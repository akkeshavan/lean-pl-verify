/-
  Spec/Examples.lean

  First kernel-checked theorems for lean-pl-verify.

  These play the same role as the 25 theorems in lean-qverify:
  they demonstrate the framework is sound and usable on concrete programs.

  Programs verified here:
    E1  — pure addition:     fn add(x: i32, y: i32) -> i32 { x + y }
    E2  — identity:          fn id<T>(x: T) -> T { x }
    E3  — safe division:     fn safe_div(x y: i32) -> Option<i32>
    E4  — bounded increment: fn inc(x: i32) -> i32 { x + 1 }  (may overflow)
    E5  — max function:      fn max(a b: i32) -> i32
    E6  — absolute value:    fn abs(x: i32) -> i32
    E7  — choose fwd/bwd:    identity laws for the mutable-borrow example
-/

import Mathlib.Tactic
import LeanPlVerify.Spec.Satisfies
import LeanPlVerify.Foundation.Ownership

namespace LeanPlVerify.Examples

open LeanPlVerify

-- ── E1: Pure addition ───────────────────────────────────────────────────────
-- Rust: fn add(x: i32, y: i32) -> i32 { x + y }
-- No mutable state → use Unit.

def rustAdd (x y : I32) : RustM Unit I32 :=
  pure (x + y)

theorem E1_add_output (x y : I32) :
    rustAdd x y at () |= .pureOutput (fun v => v = x + y) := by
  simp [rustAdd, ProgramSpec.satisfies, pure_ok]

theorem E1_add_nocrash (x y : I32) :
    rustAdd x y at () |= .nocrash :=
  sat_pureOutput_nocrash (E1_add_output x y)

-- ── E2: Identity function ───────────────────────────────────────────────────
-- Rust: fn id<T>(x: T) -> T { x }

def rustId {T : Type} (x : T) : RustM Unit T :=
  pure x

theorem E2_id_output {T : Type} (x : T) :
    rustId x at () |= .pureOutput (· = x) :=
  sat_pure

-- ── E3: Safe division (returns None on divide-by-zero) ─────────────────────
-- Rust: fn safe_div(x: i32, y: i32) -> Option<i32>
--         { if y == 0 { None } else { Some(x / y) } }

def rustSafeDiv (x y : I32) : RustM Unit (Option I32) :=
  pure (if y = 0 then none else some (x / y))

theorem E3_safeDiv_zero (x : I32) :
    rustSafeDiv x 0 at () |= .pureOutput (· = none) := by
  simp [rustSafeDiv, ProgramSpec.satisfies, pure_ok]

theorem E3_safeDiv_nonzero (x y : I32) (hy : y ≠ 0) :
    rustSafeDiv x y at () |= .pureOutput (· = some (x / y)) := by
  simp [rustSafeDiv, ProgramSpec.satisfies, pure_ok, hy]

theorem E3_safeDiv_nocrash (x y : I32) :
    rustSafeDiv x y at () |= .nocrash :=
  ⟨_, _, pure_ok⟩

-- ── E4: Increment with overflow check ─────────────────────────────────────
-- Rust: fn inc(x: i32) -> i32 { x + 1 }
-- Panics on overflow; proven safe when x + 1 is in i32 range.

def rustInc (x : I32) : RustM Unit I32 :=
  raddChecked x 1

theorem E4_inc_safe (x : I32) (hx : IntBounds.minI32 ≤ x + 1 ∧ x + 1 ≤ IntBounds.maxI32) :
    rustInc x at () |= .pureOutput (· = x + 1) := by
  simp only [rustInc, raddChecked, ProgramSpec.satisfies]
  refine ⟨x + 1, (), ?_, rfl⟩
  rw [if_pos hx, pure_ok]

-- ── E5: Max function ────────────────────────────────────────────────────────
-- Rust: fn max(a: i32, b: i32) -> i32 { if a >= b { a } else { b } }

def rustMax (a b : I32) : RustM Unit I32 :=
  pure (if a ≥ b then a else b)

theorem E5_max_ge (a b : I32) (h : a ≥ b) :
    rustMax a b at () |= .pureOutput (· = a) := by
  simp only [rustMax, ProgramSpec.satisfies, pure_ok]
  exact ⟨a, (), by simp [h], rfl⟩

theorem E5_max_lt (a b : I32) (h : a < b) :
    rustMax a b at () |= .pureOutput (· = b) := by
  simp only [rustMax, ProgramSpec.satisfies, pure_ok]
  have hlt : ¬(a ≥ b) := not_le.mpr h
  rw [if_neg hlt]
  exact ⟨b, (), rfl, rfl⟩

theorem E5_max_ge_both (a b : I32) :
    rustMax a b at () |= .pureOutput (fun v => v ≥ a ∧ v ≥ b) := by
  simp only [rustMax, ProgramSpec.satisfies, pure_ok]
  split_ifs with h
  · exact ⟨a, (), rfl, le_refl a, h⟩
  · exact ⟨b, (), rfl, le_of_lt (not_le.mp h), le_refl b⟩

-- ── E6: Absolute value ─────────────────────────────────────────────────────
-- Rust: fn abs(x: i32) -> i32 { if x >= 0 { x } else { -x } }
-- Note: for Lean's unbounded Int, abs never overflows (unlike Rust i32).

def rustAbs (x : I32) : RustM Unit I32 :=
  pure (if x ≥ 0 then x else -x)

theorem E6_abs_nonneg (x : I32) (hx : x ≥ 0) :
    rustAbs x at () |= .pureOutput (· = x) := by
  simp only [rustAbs, ProgramSpec.satisfies, pure_ok]
  exact ⟨x, (), by simp [hx], rfl⟩

theorem E6_abs_neg (x : I32) (hx : x < 0) :
    rustAbs x at () |= .pureOutput (· = -x) := by
  simp only [rustAbs, ProgramSpec.satisfies, pure_ok]
  have hn : ¬(x ≥ 0) := not_le.mpr hx
  rw [if_neg hn]
  exact ⟨-x, (), rfl, rfl⟩

theorem E6_abs_nonneg_result (x : I32) :
    rustAbs x at () |= .pureOutput (fun v => v ≥ 0) := by
  simp only [rustAbs, ProgramSpec.satisfies, pure_ok]
  split_ifs with h
  · exact ⟨x, (), rfl, h⟩
  · exact ⟨-x, (), rfl, neg_nonneg.mpr (le_of_lt (not_le.mp h))⟩

-- ── E7 / E8: Forward-backward (choose) identity laws ───────────────────────
-- These re-export the proofs from Foundation.Ownership as named theorems.

theorem E7_choose_identity_true (α : Type) (x y : α) :
    Choose.bwd true x y (Choose.fwd true x y) = (x, y) :=
  Choose.identity_true x y

theorem E8_choose_identity_false (α : Type) (x y : α) :
    Choose.bwd false x y (Choose.fwd false x y) = (x, y) :=
  Choose.identity_false x y

/-
  Theorem inventory (analogous to lean-qverify Table 1):

  | # | Function       | Property                    | Proof method       |
  |---|----------------|-----------------------------|---------------------|
  | E1| add            | returns x + y               | pure_ok + simp      |
  | E1| add            | no panic                    | derived             |
  | E2| id             | returns input               | sat_pure            |
  | E3| safe_div(x,0)  | returns None                | simp                |
  | E3| safe_div(x,y≠0)| returns Some(x/y)           | simp                |
  | E3| safe_div       | no panic                    | pure_ok             |
  | E4| inc            | returns x+1 (in-range)      | raddChecked+simp    |
  | E5| max(a≥b)       | returns a                   | simp                |
  | E5| max(a<b)       | returns b                   | not_le + simp       |
  | E5| max            | result ≥ both inputs        | split_ifs + linarith|
  | E6| abs(x≥0)       | returns x                   | simp                |
  | E6| abs(x<0)       | returns -x                  | not_le + simp       |
  | E6| abs            | result ≥ 0                  | split_ifs + linarith|
  | E7| choose_bwd/true| identity law                | Choose.identity     |
  | E8| choose_bwd/fls | identity law                | Choose.identity     |
-/

#check @E1_add_output
#check @E2_id_output
#check @E3_safeDiv_zero
#check @E3_safeDiv_nonzero
#check @E4_inc_safe
#check @E5_max_ge_both
#check @E6_abs_nonneg_result
#check @E7_choose_identity_true
#check @E8_choose_identity_false

end LeanPlVerify.Examples
