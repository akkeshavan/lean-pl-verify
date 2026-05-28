/-
  Foundation/Monad.lean

  The RustM execution monad: models safe Rust function semantics.

  A Rust function that:
    · reads / writes local variables  → modelled as StateT σ  (σ = var store)
    · may panic                       → modelled as Except PanicReason

  RustM σ α  :=  σ → Except PanicReason (α × σ)

  Sequential Rust statements become monadic binds (>>=).
  `panic!()` becomes `throw`.
  `let mut x = v` / `x = v` become `get` / `set` / `modify`.

  Pure functions (no mutable state) use σ = Unit:
    RustM Unit α  ≅  Except PanicReason α
-/

import LeanPlVerify.Foundation.Types

namespace LeanPlVerify

-- ── Core monad ─────────────────────────────────────────────────────────────

/--
  The Rust execution monad.
    σ : local variable state (a record type per function)
    α : return type
-/
abbrev RustM (σ α : Type) : Type := StateT σ (Except PanicReason) α

-- ── Primitive operations ───────────────────────────────────────────────────

/-- Model `panic!(reason)` — immediately terminates with a panic. -/
def rpanic {σ α : Type} (r : PanicReason) : RustM σ α :=
  fun _ => Except.error r

/-- Model a checked division: panics on divide-by-zero. -/
def rdiv {σ : Type} (x y : I32) : RustM σ I32 :=
  if y = 0 then rpanic .divisionByZero
  else pure (x / y)

/-- Model integer addition with overflow check. -/
def raddChecked {σ : Type} (x y : I32) : RustM σ I32 :=
  let v := x + y
  if IntBounds.minI32 ≤ v ∧ v ≤ IntBounds.maxI32 then pure v
  else rpanic .arithmeticOverflow

/-- Model a bounds-checked array index. -/
def rindex {σ α : Type} (arr : List α) (i : Nat) : RustM σ α :=
  if h : i < arr.length then pure (arr[i]'h)
  else rpanic (.indexOutOfBounds i arr.length)

-- ── Running computations ───────────────────────────────────────────────────

/-- Execute a RustM computation from an initial state. -/
def runRustM {σ α : Type} (m : RustM σ α) (init : σ) : Except PanicReason (α × σ) :=
  m init

/-- Extract the return value if the computation succeeds. -/
def evalRustM {σ α : Type} (m : RustM σ α) (init : σ) : Option α :=
  match m init with
  | Except.ok (v, _) => some v
  | Except.error _   => none

-- ── Observation predicates (used in specs) ─────────────────────────────────

/-- The computation does not panic from initial state `init`. -/
def doesNotPanic {σ α : Type} (m : RustM σ α) (init : σ) : Prop :=
  ∃ v s', m init = Except.ok (v, s')

/-- The computation returns a specific value from initial state `init`. -/
def returnsValue {σ α : Type} (m : RustM σ α) (init : σ) (expected : α) : Prop :=
  ∃ s', m init = Except.ok (expected, s')

/-- The computation returns a value satisfying predicate P. -/
def returnsValueSat {σ α : Type} (m : RustM σ α) (init : σ) (P : α → Prop) : Prop :=
  ∃ v s', m init = Except.ok (v, s') ∧ P v

-- ── Composition lemmas ─────────────────────────────────────────────────────

theorem bind_ok {σ α β : Type}
    {m : RustM σ α} {f : α → RustM σ β} {init : σ} {v : α} {s' : σ} {r : β} {s'' : σ}
    (hm : m init = Except.ok (v, s'))
    (hf : f v s' = Except.ok (r, s'')) :
    (m >>= f) init = Except.ok (r, s'') := by
  change m init >>= (fun p => f p.1 p.2) = _
  rw [hm]
  exact hf

theorem pure_ok {σ α : Type} {v : α} {init : σ} :
    (pure v : RustM σ α) init = Except.ok (v, init) := rfl

end LeanPlVerify
