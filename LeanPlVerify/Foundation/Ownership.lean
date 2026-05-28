/-
  Foundation/Ownership.lean

  Models Rust's mutable borrow semantics in a purely functional style
  using the Forward-Backward (FB) paradigm.

  Reference: Ho et al., "Aeneas: Rust Verification by Functional Translation"
             ICFP 2022 — Section 3: Mutable borrows

  Key insight: A Rust function returning `&'a mut T` is split into:
    forward  fn : inputs → T            (reads the borrowed value)
    backward fn : inputs → T → inputs   (propagates mutation back)

  This eliminates heap models, pointer arithmetic, and frame conditions.
  Mutable reference semantics become pure mathematical equations.
-/

import LeanPlVerify.Foundation.Types
import LeanPlVerify.Foundation.Monad

namespace LeanPlVerify

-- ── Forward-Backward pair ──────────────────────────────────────────────────

/--
  A FBPair captures the semantics of a Rust function that returns a mutable
  reference into one of its arguments.

    · fwd   : computes the initial value of the returned reference
    · bwd   : given the updated reference value at end-of-lifetime,
              propagates the change back to the original inputs
-/
structure FBPair (Input Output : Type) where
  fwd : Input → Output
  bwd : Input → Output → Input

/-- Consistency axiom: if the reference is never modified, backward = identity. -/
def FBPair.identity_law {I O : Type} (fb : FBPair I O) : Prop :=
  ∀ (inp : I), fb.bwd inp (fb.fwd inp) = inp

-- ── Canonical example: `choose` ────────────────────────────────────────────
-- Rust: fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T
--       { if b { x } else { y } }

namespace Choose

/-- Forward function: returns the selected value. -/
def fwd (b : Bool) (x y : α) : α :=
  if b then x else y

/-- Backward function: propagates the updated value back to x or y. -/
def bwd (b : Bool) (x y : α) (updated : α) : α × α :=
  if b then (updated, y) else (x, updated)

/-- Correctness: if b = true, fwd returns x. -/
theorem fwd_true (x y : α) : fwd true x y = x := by simp [fwd]

/-- Correctness: if b = false, fwd returns y. -/
theorem fwd_false (x y : α) : fwd false x y = y := by simp [fwd]

/-- Identity law for b = true: bwd(inp, fwd(inp)) = inp. -/
theorem identity_true (x y : α) : bwd true x y (fwd true x y) = (x, y) := by
  simp [fwd, bwd]

/-- Identity law for b = false: bwd(inp, fwd(inp)) = inp. -/
theorem identity_false (x y : α) : bwd false x y (fwd false x y) = (x, y) := by
  simp [fwd, bwd]

end Choose

-- ── Mutable reference model ────────────────────────────────────────────────

/--
  `MutBorrow α` represents a borrowed `&mut T` value together with the
  "back" continuation that must be called at end-of-lifetime.

  This is a shallow model: in full Aeneas the continuation is threaded
  through the monadic translation automatically.
-/
structure MutBorrow (α : Type) where
  value : α
  -- In a complete translation, `back` would be a backward function.
  -- We expose it here for pedagogical purposes.

/-- Dereference: read the borrowed value. -/
def MutBorrow.deref {α : Type} (b : MutBorrow α) : α := b.value

/-- Write through the borrow. -/
def MutBorrow.write {α : Type} (b : MutBorrow α) (v : α) : MutBorrow α :=
  { b with value := v }

-- ── Lifetime tracking (simplified) ────────────────────────────────────────
-- Full lifetime tracking requires a more elaborate translation.
-- This module gives the conceptual vocabulary; elaboration handles the rest.

/-- A lifetime identifier (corresponds to Rust lifetime parameters 'a, 'b …). -/
abbrev Lifetime := Nat

end LeanPlVerify
