/-
  TypeScript/AST.lean

  Lean 4 representation of a typed TypeScript AST subset.

  Pipeline:
    TypeScript source (.ts)
      → tsc type-checker (produces typed AST)
      → ts-morph / TypeScript compiler API (exports AST as JSON)
      → This module (JSON → Lean AST)
      → Elaborator (Lean AST → RustM Unit α)  ← same monad as Rust!
      → ProgramSpec + kernel-checked proofs

  Scope (Phase 1): pure TypeScript functions only.
    - No this, no class mutation, no closures over mutable captures
    - Return type must be expressible as a Lean type
    - Types: number, boolean, string, undefined, null, union, record

  The key insight: pure TypeScript functions and pure Rust functions share
  the same Lean embedding (RustM Unit α). The specification language
  (ProgramSpec) is IDENTICAL. This is the unification claim of the paper.
-/

namespace LeanPlVerify.TypeScript

-- ── TypeScript types ────────────────────────────────────────────────────────

/--
  A subset of TypeScript types expressible in the verifier.
  TypeScript's structural type system maps to Lean's `Type`.
-/
inductive TSTy : Type where
  | number                        : TSTy   -- IEEE 754 double (modelled as ℚ or ℝ)
  | boolean                       : TSTy   -- true | false
  | string                        : TSTy   -- string literals
  | undefined_                    : TSTy   -- undefined
  | null_                         : TSTy   -- null
  | void_                         : TSTy   -- return-type void
  | never_                        : TSTy   -- unreachable
  | union (a b : TSTy)            : TSTy   -- A | B
  | opt   (inner : TSTy)          : TSTy   -- T | undefined  (optional param)
  | tuple (fields : List TSTy)    : TSTy   -- [A, B, C]
  | array (elem : TSTy)           : TSTy   -- T[]
  | record (key val : TSTy)       : TSTy   -- Record<K,V>
  | named  (name : String)        : TSTy   -- interface / type alias
  deriving Repr

-- ── Literals ───────────────────────────────────────────────────────────────

inductive TSLit : Type where
  | num  (n : Int)     : TSLit   -- integer subset of IEEE 754 double
  | bool (b : Bool)    : TSLit
  | str  (s : String)  : TSLit
  | null_              : TSLit
  | undefined_         : TSLit
  deriving Repr

-- ── Expressions ────────────────────────────────────────────────────────────

/--
  TypeScript expression AST (pure subset).
  Side-effecting expressions (console.log, fetch, etc.) are excluded.
-/
inductive TSExpr : Type where
  | lit    (l : TSLit)                             : TSExpr
  /-- De Bruijn index: 0 = first param, 1 = second param, etc.
      Local `const` bindings push to the front, shifting outer indices by 1. -/
  | var    (idx : Nat)                             : TSExpr
  | binOp  (op : String) (l r : TSExpr)            : TSExpr
  | unOp   (op : String) (e : TSExpr)              : TSExpr
  | call   (fn : String) (args : List TSExpr)      : TSExpr
  | ite    (cond thenE elseE : TSExpr)             : TSExpr
  | index  (arr idx : TSExpr)                      : TSExpr
  | member (obj : TSExpr) (field : String)         : TSExpr
  | arrow  (params : List String) (body : TSExpr)  : TSExpr
  | typeof (e : TSExpr)                            : TSExpr
  deriving Repr

-- ── Statements ─────────────────────────────────────────────────────────────

inductive TSStmt : Type where
  | skip                                                      : TSStmt
  | return_ (e : TSExpr)                                      : TSStmt
  | const   (name : String) (ty : Option TSTy) (e : TSExpr)
            (k : TSStmt)                                      : TSStmt
  /-- Mutable update: `env[idx] := eval(e)`, then continue with `k`. -/
  | set_    (idx : Nat) (e : TSExpr) (k : TSStmt)            : TSStmt
  | ite     (cond : TSExpr) (thenB elseB : TSStmt)           : TSStmt
  | while_  (cond : TSExpr) (body : TSStmt)                  : TSStmt
  | throw_  (msg : String)                                    : TSStmt
  | seq     (s1 s2 : TSStmt)                                  : TSStmt
  deriving Repr

-- ── Function definitions ────────────────────────────────────────────────────

/-- A TypeScript parameter (name + type annotation). -/
structure TSParam where
  name     : String
  ty       : TSTy
  optional : Bool   -- whether the param is `param?: T`
  deriving Repr

/-- A TypeScript function definition (pure subset). -/
structure TSFunDef where
  name    : String
  params  : List TSParam
  retTy   : TSTy
  body    : TSStmt
  async_  : Bool     -- async functions → Promise; out of scope for Phase 1
  deriving Repr

end LeanPlVerify.TypeScript
