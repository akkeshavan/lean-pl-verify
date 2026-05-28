/-
  Translation/Elaborator.lean

  Interprets LLBC function definitions as RustM computations.

  Design:
  · Local variable store is `List Value` indexed by VarId (= Nat).
    `List` keeps all reduction steps kernel-transparent, so execution
    equations can be proved by `rfl` — no `sorry`.
  · The core evaluator `evalStmtFuel` is a pure function with STRUCTURAL
    recursion on `Nat`.  Every recursive call uses `n` from the `n+1`
    pattern, so the kernel can reduce closed terms directly.
  · Cross-function calls are handled inside `evalStmtFuel` by pattern-
    matching on the `FunEnv` — no `mutual` block needed.
  · The callee executes in a fresh local store; the caller's store is
    passed unchanged.
  · The public API `evalFun` wraps the result in `RustM Unit Value` for
    use with `ProgramSpec` and the `|=` satisfaction relation.
-/

import LeanPlVerify.Translation.LLBC
import LeanPlVerify.Foundation.Monad

namespace LeanPlVerify.LLBC

open LeanPlVerify

-- ── Value type ────────────────────────────────────────────────────────────────

/-- Dynamically-typed runtime value for the LLBC interpreter. -/
inductive Value : Type where
  | int    (n : Int)                         : Value
  | uint   (n : Nat)                         : Value
  | bool_  (b : Bool)                        : Value
  | unit                                     : Value
  | some_  (v : Value)                       : Value
  | none_                                    : Value
  | tuple  (vs : List Value)                 : Value
  | adt    (tag : Nat) (fields : List Value) : Value
  deriving Repr

-- ── Local variable state ──────────────────────────────────────────────────────

/-- Mutable local variable store, indexed by VarId (= Nat).
    `List` makes all reduction steps kernel-transparent. -/
abbrev Locals : Type := List Value

/-- Function environment for cross-function calls. -/
abbrev FunEnv : Type := List LLBCFunDef

-- ── Locals initialisation ─────────────────────────────────────────────────────

/-- Build a callee's initial locals: all `.unit`, then install argument values.
    Params are assumed to have valid indices (< locals.length) by construction;
    `List.set` is a no-op when the index is out of range, so the bound check is
    omitted here to keep the function kernel-transparent (Nat.blt is @[extern]). -/
def buildLocals (f : LLBCFunDef) (args : List Value) : Locals :=
  let base : Locals := List.replicate f.locals.length Value.unit
  List.foldl
    (fun acc (pair : VarId × Value) => acc.set pair.1 pair.2)
    base
    (List.zipWith (fun (lv : LLBCVar) v => (lv.id, v)) f.params args)

-- ── Literal evaluation ────────────────────────────────────────────────────────

def evalLit : LLBCLit → Value
  | .bool  b   => .bool_ b
  | .int   n _ => .int n
  | .uint  n _ => .uint n
  | .str   _   => .unit
  | .char  _   => .unit
  | .unit      => .unit

-- ── Literal matching ──────────────────────────────────────────────────────────

def litMatchesValue : LLBCLit → Value → Bool
  | .bool  b,   .bool_ c  => b == c
  | .int   n _, .int m    => n == m
  | .uint  n _, .uint m   => n == m
  | .unit,      .unit     => true
  | _,          _         => false

-- ── Pure place / operand / rvalue evaluation ─────────────────────────────────

/-- Read a place — pure, takes and returns locals unchanged. -/
def evalPlacePure : LLBCPlace → Locals → Except PanicReason Value
  | .var id,      s => match s[id]? with
      | some v => Except.ok v
      | none   => Except.error (.explicit s!"var {id} out of range")
  | .deref p,     s => evalPlacePure p s
  | .field p idx, s =>
      match evalPlacePure p s with
      | Except.error e => Except.error e
      | Except.ok v =>
          match v with
          | .tuple fs =>
              if h : idx < fs.length then Except.ok (fs[idx]'h)
              else Except.error (.explicit s!"field {idx} out of range")
          | .adt _ fs =>
              if h : idx < fs.length then Except.ok (fs[idx]'h)
              else Except.error (.explicit s!"field {idx} out of range")
          | _ => Except.error (.explicit "field access on non-struct value")
  | .index p iVar, s =>
      match evalPlacePure p s, s[iVar]? with
      | Except.ok (.tuple fs), some (.uint n) =>
          if h : n < fs.length then Except.ok (fs[n]'h)
          else Except.error (.indexOutOfBounds n fs.length)
      | Except.error e, _ => Except.error e
      | _, _ => Except.error (.explicit "index on non-array or non-uint index")
  | .downcast p _, s => evalPlacePure p s

/-- Write to a place — returns updated locals.
    The bounds check is omitted: `List.set` is a no-op for out-of-range indices
    (kernel-transparent), while `id < s.length` uses `Nat.blt` (`@[extern]`)
    which would block kernel reduction needed for `rfl` proofs. -/
def writePlacePure : LLBCPlace → Value → Locals → Except PanicReason Locals
  | .var id, v, s => Except.ok (s.set id v)
  | _, _, _ => Except.error (.explicit "write to non-var place (unsupported)")

/-- Evaluate an operand — pure read. -/
def evalOperandPure : LLBCOperand → Locals → Except PanicReason Value
  | .copy p,  s => evalPlacePure p s
  | .move_ p, s => evalPlacePure p s
  | .const l, _ => Except.ok (evalLit l)

/-- Evaluate a list of operands — pure. -/
def evalOperandsPure (ops : List LLBCOperand) (s : Locals) : Except PanicReason (List Value) :=
  ops.mapM (fun op => evalOperandPure op s)

/-- Evaluate a binary operation — pure. -/
def evalBinOpPure (op : BinOp) (lv rv : Value) : Except PanicReason Value :=
  match op, lv, rv with
  | .add, .int a, .int b =>
      let v := a + b
      if IntBounds.minI32 ≤ v ∧ v ≤ IntBounds.maxI32 then Except.ok (.int v)
      else Except.error .arithmeticOverflow
  | .sub, .int a, .int b =>
      let v := a - b
      if IntBounds.minI32 ≤ v ∧ v ≤ IntBounds.maxI32 then Except.ok (.int v)
      else Except.error .arithmeticOverflow
  | .mul, .int a, .int b =>
      let v := a * b
      if IntBounds.minI32 ≤ v ∧ v ≤ IntBounds.maxI32 then Except.ok (.int v)
      else Except.error .arithmeticOverflow
  | .div, .int a, .int b =>
      if b = 0 then Except.error .divisionByZero
      else Except.ok (.int (a / b))
  | .rem, .int a, .int b =>
      if b = 0 then Except.error .divisionByZero else Except.ok (.int (a % b))
  | .add, .uint a, .uint b => Except.ok (.uint (a + b))
  | .sub, .uint a, .uint b => Except.ok (.uint (a - b))
  | .mul, .uint a, .uint b => Except.ok (.uint (a * b))
  | .div, .uint a, .uint b =>
      if b = 0 then Except.error .divisionByZero else Except.ok (.uint (a / b))
  | .rem, .uint a, .uint b =>
      if b = 0 then Except.error .divisionByZero else Except.ok (.uint (a % b))
  | .eq,  .int a, .int b  => Except.ok (.bool_ (a == b))
  | .ne,  .int a, .int b  => Except.ok (.bool_ (a != b))
  | .lt,  .int a, .int b  => Except.ok (.bool_ (decide (a < b)))
  | .le,  .int a, .int b  => Except.ok (.bool_ (decide (a ≤ b)))
  | .gt,  .int a, .int b  => Except.ok (.bool_ (decide (a > b)))
  | .ge,  .int a, .int b  => Except.ok (.bool_ (decide (a ≥ b)))
  | .eq,  .uint a, .uint b => Except.ok (.bool_ (a == b))
  | .ne,  .uint a, .uint b => Except.ok (.bool_ (a != b))
  | .lt,  .uint a, .uint b => Except.ok (.bool_ (decide (a < b)))
  | .le,  .uint a, .uint b => Except.ok (.bool_ (decide (a ≤ b)))
  | .gt,  .uint a, .uint b => Except.ok (.bool_ (decide (a > b)))
  | .ge,  .uint a, .uint b => Except.ok (.bool_ (decide (a ≥ b)))
  | .and, .bool_ a, .bool_ b => Except.ok (.bool_ (a && b))
  | .or,  .bool_ a, .bool_ b => Except.ok (.bool_ (a || b))
  | .bitAnd, .bool_ a, .bool_ b => Except.ok (.bool_ (a && b))
  | .bitOr,  .bool_ a, .bool_ b => Except.ok (.bool_ (a || b))
  | .bitXor, .bool_ a, .bool_ b => Except.ok (.bool_ (a ^^ b))
  | .bitAnd, .uint a, .uint b => Except.ok (.uint (a &&& b))
  | .bitOr,  .uint a, .uint b => Except.ok (.uint (a ||| b))
  | .bitXor, .uint a, .uint b => Except.ok (.uint (a ^^^ b))
  | _, _, _ => Except.error (.explicit "type mismatch in binary operation")

/-- Evaluate an r-value — pure.
    Uses explicit `match` on `Except` (no `do`/`Except.bind`) so that
    `simp only [evalRValuePure]` can fully reduce the expression. -/
def evalRValuePure : LLBCRValue → Locals → Except PanicReason Value
  | .use op,       s => evalOperandPure op s
  | .ref p _,      s => evalPlacePure p s
  | .binOp op l r, s =>
      match evalOperandPure l s with
      | Except.error e => Except.error e
      | Except.ok lv   =>
          match evalOperandPure r s with
          | Except.error e => Except.error e
          | Except.ok rv   => evalBinOpPure op lv rv
  | .unOp op x, s =>
      match evalOperandPure x s with
      | Except.error e => Except.error e
      | Except.ok v    =>
          match op, v with
          | .not, .bool_ b => Except.ok (.bool_ !b)
          | .neg, .int  n  => Except.ok (.int (-n))
          | .cast _, _     => Except.ok v
          | _, _           => Except.error (.explicit "type mismatch in unary op")
  | .aggregate _ fs, s =>
      match fs.mapM (fun op => evalOperandPure op s) with
      | Except.error e => Except.error e
      | Except.ok vs   => Except.ok (.tuple vs)
  | .discriminant p, s =>
      match evalPlacePure p s with
      | Except.error e => Except.error e
      | Except.ok v    =>
          match v with
          | .adt tag _ => Except.ok (.uint tag)
          | _          => Except.error (.explicit "discriminant of non-ADT value")

-- ── Signal ────────────────────────────────────────────────────────────────────

/-- Control-flow outcome of executing a statement. -/
inductive Signal : Type where
  | next    : Signal
  | break_  : Signal
  | return_ : Signal
  deriving DecidableEq, Repr

-- ── Core evaluator (structural recursion on Nat) ──────────────────────────────

/-
  `evalStmtFuel env n s locals` executes statement `s` with fuel `n`,
  threading the local store explicitly.

  Structural recursion on `n`: every recursive call uses the `n` bound by
  the `n+1` pattern (strictly smaller), so the Lean kernel can reduce
  closed terms by computation — enabling `rfl` proofs without `sorry`.

  Cross-function calls are inlined: the callee body is run with `n` fuel
  in a fresh locals list; the caller's locals are unaffected.
-/
def evalStmtFuel (env : FunEnv) : Nat → LLBCStmt → Locals → Except PanicReason (Signal × Locals)
  | 0, _, _       => Except.error (.explicit "evalStmtFuel: out of fuel")
  | _+1, .skip,      s => Except.ok (.next,    s)
  | _+1, .return_,   s => Except.ok (.return_, s)
  | _+1, .break_,    s => Except.ok (.break_,  s)
  | _+1, .continue_, s => Except.ok (.next,    s)
  | _+1, .panic msg, _ => Except.error (.explicit msg)
  | n+1, .assign dst rv k, s =>
      match evalRValuePure rv s with
      | Except.error e => Except.error e
      | Except.ok v    =>
          match writePlacePure dst v s with
          | Except.error e => Except.error e
          | Except.ok s'   => evalStmtFuel env n k s'
  | n+1, .seq s1 s2, s =>
      match evalStmtFuel env n s1 s with
      | Except.error e          => Except.error e
      | Except.ok (.next, s')   => evalStmtFuel env n s2 s'
      | Except.ok (other, s')   => Except.ok (other, s')
  | n+1, .ite cond thenB elseB, s =>
      match evalOperandPure cond s with
      | Except.error e           => Except.error e
      | Except.ok (.bool_ true)  => evalStmtFuel env n thenB s
      | Except.ok (.bool_ false) => evalStmtFuel env n elseB s
      | Except.ok _              => Except.error (.explicit "non-boolean condition in ite")
  | n+1, .loop body, s =>
      match evalStmtFuel env n body s with
      | Except.error e            => Except.error e
      | Except.ok (.next,    s')  => evalStmtFuel env n (.loop body) s'
      | Except.ok (.break_,  s')  => Except.ok (.next, s')
      | Except.ok (.return_, s')  => Except.ok (.return_, s')
  | n+1, .call dst fname argOps k, s =>
      match evalOperandsPure argOps s with
      | Except.error e   => Except.error e
      | Except.ok args   =>
          match env.find? (fun f => f.name == fname) with
          | none   => Except.error (.explicit s!"unknown function '{fname}'")
          | some f =>
              match evalStmtFuel env n f.body (buildLocals f args) with
              | Except.error e              => Except.error e
              | Except.ok (_, calleeLocals) =>
                  match calleeLocals[0]? with
                  | none   => Except.error (.explicit s!"evalStmtFuel: no return slot in '{fname}'")
                  | some v =>
                      match writePlacePure dst v s with
                      | Except.error e => Except.error e
                      | Except.ok s'   => evalStmtFuel env n k s'
  | n+1, .switchInt op arms default_, s =>
      match evalOperandPure op s with
      | Except.error e => Except.error e
      | Except.ok v    =>
          match arms.find? (fun pair => litMatchesValue pair.1 v) with
          | some pair => evalStmtFuel env n pair.2 s
          | none      => evalStmtFuel env n default_ s

-- ── Public entry point ────────────────────────────────────────────────────────

/-- Run an LLBC function body, returning value from locals[0] on success. -/
def evalFunBody (env : FunEnv) (f : LLBCFunDef) (fuel : Nat) (args : List Value) :
    Except PanicReason Value :=
  let initLocals := buildLocals f args
  match evalStmtFuel env fuel f.body initLocals with
  | Except.error e => Except.error e
  | Except.ok (_, finalLocals) =>
      match finalLocals[0]? with
      | some v => Except.ok v
      | none   => Except.error (.explicit "evalFunBody: no return slot")

/--
  Evaluate an LLBC function, returning a `RustM Unit Value` suitable for
  use with `ProgramSpec` and the `|=` satisfaction relation.

  The `env` parameter lists additional callees; `f` is automatically included
  so self-recursive calls work.

  Example:
  ```lean
  evalFun [] addFun 100 [.int 3, .int 4] at () |= .pureOutput (· = .int 7)
  ```
-/
def evalFun (env : FunEnv) (f : LLBCFunDef) (fuel : Nat)
    (args : List Value) : RustM Unit Value := fun _ =>
  match evalFunBody (f :: env) f fuel args with
  | Except.error e   => Except.error e
  | Except.ok v      => Except.ok (v, ())

-- ── Convenience: ElabM as RustM Locals for spec compatibility ────────────────

/-- Elaboration monad (kept for compatibility with Spec modules). -/
abbrev ElabM (α : Type) := RustM Locals α

-- ── LLBCVar constructor helpers ───────────────────────────────────────────────

/-- Build a named parameter variable (for `LLBCFunDef.params` / `locals`). -/
def mkParam (id : Nat) (ty : LLBCTy) (name : String) : LLBCVar :=
  ⟨id, ty, some name⟩

/-- Build an unnamed local variable (for `LLBCFunDef.locals`). -/
def mkLocal (id : Nat) (ty : LLBCTy) : LLBCVar :=
  ⟨id, ty, none⟩

end LeanPlVerify.LLBC
