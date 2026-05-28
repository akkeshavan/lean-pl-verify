/-
  Translation/LLBC.lean

  Lean 4 representation of the Low-Level Borrow Calculus (LLBC) AST.

  LLBC is the structured IR produced by Charon from Rust MIR:
    rustc → MIR → Charon → ULLBC → LLBC

  Unlike MIR's control-flow graph, LLBC is structured:
    - Loops, if/else, and sequences are explicit constructs
    - Pattern matching is simplified
    - Move / copy / borrow operations are explicit

  This module defines the AST; the Elaborator module translates LLBC → RustM.

  Reference: "Charon: An Analysis Framework for Rust" (AeneasVerif/charon)
             arXiv:2410.18042
-/

namespace LeanPlVerify.LLBC

-- ── Identifiers ────────────────────────────────────────────────────────────

abbrev VarId  : Type := Nat     -- local variable index
abbrev AdtId  : Type := String  -- ADT (struct/enum) name
abbrev FunId  : Type := String  -- function name
abbrev FieldIdx : Type := Nat   -- struct field index

-- ── Integer kinds ──────────────────────────────────────────────────────────

inductive IntTy : Type where
  | I8 | I16 | I32 | I64 | I128 | Isize
  deriving DecidableEq, Repr

inductive UintTy : Type where
  | U8 | U16 | U32 | U64 | U128 | Usize
  deriving DecidableEq, Repr

inductive Mutability : Type where
  | Mut    -- &mut T
  | Shared -- &T (immutable borrow)
  deriving DecidableEq, Repr

-- ── Type system ────────────────────────────────────────────────────────────

/--
  LLBC type language.
  Corresponds to Rust types after monomorphisation and lifetime erasure
  (lifetimes are tracked separately for the borrow model).
-/
inductive LLBCTy : Type where
  | bool_                                       : LLBCTy
  | int    (ty : IntTy)                         : LLBCTy
  | uint   (ty : UintTy)                        : LLBCTy
  | str_                                        : LLBCTy
  | char_                                       : LLBCTy
  | tuple  (fields : List LLBCTy)               : LLBCTy
  | ref    (inner : LLBCTy) (m : Mutability)    : LLBCTy
  | adt    (name : AdtId)   (args : List LLBCTy): LLBCTy
  | array  (elem : LLBCTy)  (len : Nat)         : LLBCTy
  | slice  (elem : LLBCTy)                      : LLBCTy
  | rawPtr (inner : LLBCTy) (m : Mutability)    : LLBCTy  -- unsafe only
  | never                                       : LLBCTy   -- Rust `!`
  deriving Repr

-- ── Literal values ─────────────────────────────────────────────────────────

inductive LLBCLit : Type where
  | bool  (b : Bool)                   : LLBCLit
  | int   (n : Int)   (ty : IntTy)     : LLBCLit
  | uint  (n : Nat)   (ty : UintTy)    : LLBCLit
  | str   (s : String)                 : LLBCLit
  | char  (c : Char)                   : LLBCLit
  | unit                               : LLBCLit
  deriving Repr

-- ── Binary operators ───────────────────────────────────────────────────────

inductive BinOp : Type where
  -- Arithmetic
  | add | sub | mul | div | rem
  -- Bitwise
  | bitAnd | bitOr | bitXor | shl | shr
  -- Comparison
  | eq | ne | lt | le | gt | ge
  -- Lazy logical (sugar; desugared to if in full LLBC)
  | and | or
  deriving DecidableEq, Repr

-- ── Unary operators ────────────────────────────────────────────────────────

inductive UnOp : Type where
  | not               -- boolean not / bitwise not
  | neg               -- arithmetic negation
  | cast (ty : LLBCTy) -- type cast (target type recorded but not compared)
  deriving Repr
-- Note: DecidableEq not derived — UnOp.cast carries LLBCTy which is recursive.

-- ── Places ────────────────────────────────────────────────────────────────
-- A place is a path into a value: local variable, dereference, field, index.
-- After borrow-checking, all places are valid; no null dereferences possible.

inductive LLBCPlace : Type where
  | var   (id  : VarId)                        : LLBCPlace
  | deref (p   : LLBCPlace)                    : LLBCPlace
  | field (p   : LLBCPlace) (idx : FieldIdx)   : LLBCPlace
  | index (p   : LLBCPlace) (i   : VarId)      : LLBCPlace
  | downcast (p : LLBCPlace) (variant : Nat)   : LLBCPlace
  deriving Repr

-- ── Operands ───────────────────────────────────────────────────────────────

/--
  An operand is a value consumed during computation.
    · Copy  — value is copied (T : Copy)
    · Move  — value is moved out (ownership transferred)
    · Const — a literal constant
-/
inductive LLBCOperand : Type where
  | copy  (p : LLBCPlace)  : LLBCOperand
  | move_ (p : LLBCPlace)  : LLBCOperand
  | const (l : LLBCLit)    : LLBCOperand
  deriving Repr

-- ── R-values ───────────────────────────────────────────────────────────────

/-- Right-hand side of an LLBC assignment. -/
inductive LLBCRValue : Type where
  | use        (op : LLBCOperand)                         : LLBCRValue
  | ref        (p  : LLBCPlace)     (m : Mutability)      : LLBCRValue
  | binOp      (op : BinOp)         (l r : LLBCOperand)   : LLBCRValue
  | unOp       (op : UnOp)          (x : LLBCOperand)     : LLBCRValue
  | aggregate  (kind : AdtId)       (flds : List LLBCOperand) : LLBCRValue
  | discriminant (p : LLBCPlace)                          : LLBCRValue
  deriving Repr

-- ── Statements ─────────────────────────────────────────────────────────────

/--
  LLBC statement language — structured control flow.

  Unlike MIR's CFG, LLBC has explicit:
    · `ite`      — if-then-else
    · `loop`     — unbounded loop (may not terminate; handled with fuel)
    · `break_`   — break out of the innermost loop
    · `seq`      — sequential composition
    · `panic`    — unconditional abort

  This structure maps cleanly to monadic Lean code via the Elaborator.
-/
inductive LLBCStmt : Type where
  | skip                                                        : LLBCStmt
  | assign  (dst : LLBCPlace) (rv  : LLBCRValue) (k : LLBCStmt) : LLBCStmt
  | call    (dst : LLBCPlace) (f   : FunId)
            (args : List LLBCOperand)              (k : LLBCStmt) : LLBCStmt
  | ite     (cond  : LLBCOperand)
            (thenB : LLBCStmt) (elseB : LLBCStmt)               : LLBCStmt
  | loop    (body  : LLBCStmt)                                  : LLBCStmt
  | break_                                                      : LLBCStmt
  | continue_                                                   : LLBCStmt
  | return_                                                     : LLBCStmt
  | panic   (msg   : String)                                    : LLBCStmt
  | seq     (s1 s2 : LLBCStmt)                                  : LLBCStmt
  | switchInt (op  : LLBCOperand)
              (arms : List (LLBCLit × LLBCStmt))
              (default_ : LLBCStmt)                             : LLBCStmt
  deriving Repr

-- ── Variable declarations ──────────────────────────────────────────────────

/-- A local variable in an LLBC function body. -/
structure LLBCVar where
  id   : VarId
  ty   : LLBCTy
  name : Option String   -- debug name (None for compiler-generated temps)
  deriving Repr

-- ── Function definitions ────────────────────────────────────────────────────

/--
  A complete LLBC function definition.
  `params` are the named input parameters (a subset of `locals`).
  `body` is the structured statement — LLBC guarantees single-entry,
  structured exit via `return_`.
-/
structure LLBCFunDef where
  name    : FunId
  params  : List LLBCVar     -- function parameters (in order)
  locals  : List LLBCVar     -- all locals (params + temps + return slot)
  retTy   : LLBCTy
  body    : LLBCStmt
  deriving Repr

-- ── Simple accessor helpers ────────────────────────────────────────────────

def LLBCFunDef.paramCount (f : LLBCFunDef) : Nat := f.params.length

def LLBCFunDef.localCount (f : LLBCFunDef) : Nat := f.locals.length

end LeanPlVerify.LLBC
