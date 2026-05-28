/-
  TypeScript/Elaborator.lean

  Interprets TypeScript function definitions as RustM computations.

  Design decisions:
  · Variable bindings are `Env = List (String × TSValue)` — an association
    list.  Most-recent binding wins, giving correct `const` shadowing.
  · TypeScript `number` is modelled as `Int` for exact formal reasoning.
    Full IEEE 754 floating-point semantics are acknowledged but deferred.
  · `return e` carries its value directly in `TSSignal.return_`, avoiding
    the LLBC-style "locals[0] = return slot" convention.
  · Fuel bounds loops exactly as in Translation/Elaborator.lean.
  · `throw` / uncaught exceptions become `rpanic (.explicit msg)`.

  This file is the TypeScript analogue of Translation/Elaborator.lean.
  Both produce `RustM Unit _` and are satisfied against the SAME
  `ProgramSpec` — the paper's key unification claim.
-/

import LeanPlVerify.TypeScript.AST
import LeanPlVerify.Foundation.Monad

namespace LeanPlVerify.TypeScript

open LeanPlVerify

-- ── Runtime value ────────────────────────────────────────────────────────────

/--
  Dynamically-typed runtime value for the TypeScript interpreter.
  `number` is modelled as `Int` (integer subset of IEEE 754 double);
  full floating-point semantics are future work.
-/
inductive TSValue : Type where
  | num    (n : Int)                          : TSValue
  | bool_  (b : Bool)                         : TSValue
  | str    (s : String)                       : TSValue
  | null_                                     : TSValue
  | undef_                                    : TSValue
  | array  (vs : List TSValue)                : TSValue
  | obj    (fields : List (String × TSValue)) : TSValue
  deriving Repr

-- ── Variable environment ─────────────────────────────────────────────────────

/--
  Variable environment: positional list of values.
  Index 0 = first parameter (or most recently bound `const`).
  Kernel-transparent: `env[idx]?` reduces by `List.getElem?` without
  going through `@[extern]` string equality.
-/
abbrev Env : Type := List TSValue

/-- The TypeScript elaboration monad. -/
abbrev TSM (α : Type) := RustM Env α

-- ── Literal evaluation ────────────────────────────────────────────────────────

def evalLit : TSLit → TSValue
  | .num  n     => .num n
  | .bool b     => .bool_ b
  | .str  s     => .str s
  | .null_      => .null_
  | .undefined_ => .undef_

-- ── Binary operator evaluation ────────────────────────────────────────────────

def evalBinOp (op : String) (lv rv : TSValue) : Except PanicReason TSValue :=
  match op, lv, rv with
  | "+",   .num a,   .num b   => Except.ok (.num (a + b))
  | "-",   .num a,   .num b   => Except.ok (.num (a - b))
  | "*",   .num a,   .num b   => Except.ok (.num (a * b))
  | "/",   .num a,   .num b   =>
      if b = 0 then Except.error .divisionByZero
      else Except.ok (.num (a / b))
  | "%",   .num a,   .num b   =>
      if b = 0 then Except.error .divisionByZero
      else Except.ok (.num (a % b))
  | "===", .num a,   .num b   => Except.ok (.bool_ (a == b))
  | "!==", .num a,   .num b   => Except.ok (.bool_ (a != b))
  | "<",   .num a,   .num b   => Except.ok (.bool_ (decide (a < b)))
  | "<=",  .num a,   .num b   => Except.ok (.bool_ (decide (a ≤ b)))
  | ">",   .num a,   .num b   => Except.ok (.bool_ (decide (a > b)))
  | ">=",  .num a,   .num b   => Except.ok (.bool_ (decide (a ≥ b)))
  | "===", .bool_ a, .bool_ b => Except.ok (.bool_ (a == b))
  | "!==", .bool_ a, .bool_ b => Except.ok (.bool_ (a != b))
  | "&&",  .bool_ a, .bool_ b => Except.ok (.bool_ (a && b))
  | "||",  .bool_ a, .bool_ b => Except.ok (.bool_ (a || b))
  | "===", .str a,   .str b   => Except.ok (.bool_ (a == b))
  | "!==", .str a,   .str b   => Except.ok (.bool_ (a != b))
  | "+",   .str a,   .str b   => Except.ok (.str (a ++ b))
  | _, _, _ =>
      Except.error (.explicit s!"type error in binary op '{op}'")

-- ── Expression evaluation ─────────────────────────────────────────────────────

/--
  Evaluate a TypeScript expression given an environment.
  Expressions are pure (read-only on the environment).
  Uses explicit `match` on `Except` (no `do`/`Except.bind`) so that
  `simp only [evalExpr]` fully reduces closed and symbolic terms —
  the same design principle as `evalRValuePure` in Translation/Elaborator.lean.
-/
def evalExpr (env : Env) : TSExpr → Except PanicReason TSValue
  | .lit l    => Except.ok (evalLit l)
  | .var idx  =>
      match env[idx]? with
      | some v => Except.ok v
      | none   => Except.error (.explicit s!"variable index {idx} out of range")
  | .unOp "!" e =>
      match evalExpr env e with
      | Except.error err => Except.error err
      | Except.ok v =>
          match v with
          | .bool_ b => Except.ok (.bool_ !b)
          | _        => Except.error (.explicit "type error in '!'")
  | .unOp "-" e =>
      match evalExpr env e with
      | Except.error err => Except.error err
      | Except.ok v =>
          match v with
          | .num n => Except.ok (.num (-n))
          | _      => Except.error (.explicit "type error in unary '-'")
  | .unOp op _ =>
      Except.error (.explicit s!"unsupported unary op '{op}'")
  | .binOp op l r =>
      match evalExpr env l with
      | Except.error err => Except.error err
      | Except.ok lv =>
          match evalExpr env r with
          | Except.error err => Except.error err
          | Except.ok rv     => evalBinOp op lv rv
  | .ite c t f =>
      match evalExpr env c with
      | Except.error err          => Except.error err
      | Except.ok (.bool_ true)   => evalExpr env t
      | Except.ok (.bool_ false)  => evalExpr env f
      | Except.ok _               => Except.error (.explicit "non-boolean in ternary condition")
  | .call _ _ =>
      Except.error (.explicit "cross-function calls not yet supported")
  | .index arr ix =>
      match evalExpr env arr with
      | Except.error err => Except.error err
      | Except.ok av =>
          match evalExpr env ix with
          | Except.error err => Except.error err
          | Except.ok iv =>
              match av, iv with
              | .array vs, .num n =>
                  let i := n.toNat
                  if h : i < vs.length then Except.ok (vs[i]'h)
                  else Except.error (.indexOutOfBounds i vs.length)
              | _, _ => Except.error (.explicit "type error in array index")
  | .member obj field =>
      match evalExpr env obj with
      | Except.error err => Except.error err
      | Except.ok v =>
          match v with
          | .obj fs =>
              match fs.find? (fun p => p.1 == field) with
              | some (_, fv) => Except.ok fv
              | none         => Except.ok .undef_
          | _ => Except.error (.explicit s!"member access on non-object for '{field}'")
  | .arrow _ _ =>
      Except.error (.explicit "arrow functions not yet supported")
  | .typeof e =>
      match evalExpr env e with
      | Except.error err => Except.error err
      | Except.ok v =>
          let t : String := match v with
            | .num _   => "number"
            | .bool_ _ => "boolean"
            | .str _   => "string"
            | .null_   => "object"    -- JS: typeof null === "object"
            | .undef_  => "undefined"
            | .array _ => "object"
            | .obj _   => "object"
          Except.ok (.str t)

-- ── Control-flow signals ──────────────────────────────────────────────────────

/-- Control-flow outcome of executing a TypeScript statement. -/
inductive TSSignal : Type where
  | next              : TSSignal
  | return_ (v : TSValue) : TSSignal
  | break_            : TSSignal

-- ── Statement evaluation ──────────────────────────────────────────────────────

/--
  `evalStmt n s` executes statement `s` with fuel `n`, threading `Env`
  state through the `TSM` monad.  New `const` bindings extend the environment
  for the continuation only (lexical scope).  All recursive calls use `n`
  from pattern `n+1`, giving structural recursion on `Nat`.
-/
def evalStmt : Nat → TSStmt → TSM TSSignal
  | 0, _ => rpanic (.explicit "evalStmt: out of fuel")
  | _+1, .skip       => fun env => Except.ok (.next, env)
  | _+1, .throw_ msg => rpanic (.explicit msg)
  | _+1, .return_ e  => fun env =>
      match evalExpr env e with
      | Except.ok v    => Except.ok (.return_ v, env)
      | Except.error e => Except.error e
  | n+1, .const _ _ e k => fun env =>
      match evalExpr env e with
      | Except.error e => Except.error e
      | Except.ok v    => evalStmt n k (v :: env)   -- push to front; idx 0 = this binding
  | n+1, .set_ idx e k => fun env =>
      match evalExpr env e with
      | Except.error e => Except.error e
      | Except.ok v    => evalStmt n k (env.set idx v)
  | n+1, .ite cond thenB elseB => fun env =>
      match evalExpr env cond with
      | Except.error e            => Except.error e
      | Except.ok (.bool_ true)   => evalStmt n thenB env
      | Except.ok (.bool_ false)  => evalStmt n elseB env
      | Except.ok _               => Except.error (.explicit "non-boolean condition in if")
  | n+1, .seq s1 s2 => fun env =>
      match evalStmt n s1 env with
      | Except.error e            => Except.error e
      | Except.ok (.next, env')   => evalStmt n s2 env'
      | Except.ok (other, env')   => Except.ok (other, env')
  | n+1, .while_ cond body => fun env =>
      match evalExpr env cond with
      | Except.error e             => Except.error e
      | Except.ok (.bool_ false)   => Except.ok (.next, env)
      | Except.ok (.bool_ true)    =>
          match evalStmt n body env with
          | Except.error e               => Except.error e
          | Except.ok (.break_,   env')  => Except.ok (.next, env')
          | Except.ok (.return_ v, env') => Except.ok (.return_ v, env')
          | Except.ok (.next,     env')  => evalStmt n (.while_ cond body) env'
      | Except.ok _ => Except.error (.explicit "non-boolean while condition")

-- ── Public entry point ────────────────────────────────────────────────────────

/--
  Evaluate a TypeScript function, returning a `RustM Unit TSValue`.
  Parameters are bound by name from the `args` list (left-to-right).

  Example:
  ```lean
  evalTSFun tsAddFun 100 [.num 3, .num 4] at () |= .pureOutput (· = .num 7)
  ```
-/
def evalTSFun (f : TSFunDef) (fuel : Nat) (args : List TSValue) : RustM Unit TSValue :=
  fun _ =>
    -- Parameters are positional: args[0] = first param, args[1] = second param, etc.
    -- Kernel-transparent: no String equality in the environment lookup path.
    let initEnv : Env := args
    match evalStmt fuel f.body initEnv with
    | Except.error e              => Except.error e
    | Except.ok (.return_ v, _)  => Except.ok (v, ())
    | Except.ok (.next,     _)   => Except.error (.explicit "function fell off end without return")
    | Except.ok (.break_,   _)   => Except.error (.explicit "break outside loop")

end LeanPlVerify.TypeScript
