/-
  Tactic/Examples.lean

  Demonstrates the `llbc_verify` family of tactics on the standard benchmark
  functions.  Every theorem here replaces a manual simp+rfl proof with a
  one-liner tactic call.  This is the evaluation section's "proof automation"
  claim: adding a new verified function takes ≤3 lines.
-/

import LeanPlVerify.Tactic.VerifyFun
import LeanPlVerify.Translation.ElabSpec  -- for function definitions

namespace LeanPlVerify.Tactic.Demo

open LeanPlVerify LeanPlVerify.LLBC LeanPlVerify.LLBC.Spec
     LeanPlVerify.Tactic

-- ── Pure functions (rfl, no branching) ───────────────────────────────────────

theorem demo_return42 :
    evalFun [] return42Fun 10 [] at () |= .pureOutput (· = .int 42) := by
  llbc_verify return42Fun

theorem demo_id (x : Int) :
    evalFun [] idFun 10 [.int x] at () |= .pureOutput (· = .int x) := by
  llbc_verify idFun

theorem demo_neg (x : Int) :
    evalFun [] negFun 10 [.int x] at () |= .pureOutput (· = .int (-x)) := by
  llbc_verify negFun

-- ── Overflow-checked arithmetic (Prop-if) ────────────────────────────────────

theorem demo_add (x y : Int) (h : IntBounds.minI32 ≤ x + y ∧ x + y ≤ IntBounds.maxI32) :
    evalFun [] addFun 10 [.int x, .int y] at () |= .pureOutput (· = .int (x + y)) := by
  llbc_verify_prop addFun h

theorem demo_sub (x y : Int) (h : IntBounds.minI32 ≤ x - y ∧ x - y ≤ IntBounds.maxI32) :
    evalFun [] subFun 10 [.int x, .int y] at () |= .pureOutput (· = .int (x - y)) := by
  llbc_verify_prop subFun h

theorem demo_mul (x y : Int) (h : IntBounds.minI32 ≤ x * y ∧ x * y ≤ IntBounds.maxI32) :
    evalFun [] mulFun 10 [.int x, .int y] at () |= .pureOutput (· = .int (x * y)) := by
  llbc_verify_prop mulFun h

-- ── Conditional functions (decide-based branching) ────────────────────────────

theorem demo_max_ge (a b : Int) (h : a ≥ b) :
    evalFun [] maxFun 10 [.int a, .int b] at () |= .pureOutput (· = .int a) := by
  llbc_verify_cond maxFun (decide_eq_true h)

theorem demo_max_lt (a b : Int) (h : a < b) :
    evalFun [] maxFun 10 [.int a, .int b] at () |= .pureOutput (· = .int b) := by
  llbc_verify_cond maxFun (decide_eq_false (not_le.mpr h))

theorem demo_min_le (a b : Int) (h : a ≤ b) :
    evalFun [] minFun 10 [.int a, .int b] at () |= .pureOutput (· = .int a) := by
  llbc_verify_cond minFun (decide_eq_true h)

theorem demo_min_gt (a b : Int) (h : a > b) :
    evalFun [] minFun 10 [.int a, .int b] at () |= .pureOutput (· = .int b) := by
  llbc_verify_cond minFun (decide_eq_false (not_le.mpr h))

theorem demo_abs_nonneg (x : Int) (h : x ≥ 0) :
    evalFun [] absFun 10 [.int x] at () |= .pureOutput (· = .int x) := by
  llbc_verify_cond absFun (decide_eq_true h)

theorem demo_abs_neg (x : Int) (h : x < 0) :
    evalFun [] absFun 10 [.int x] at () |= .pureOutput (· = .int (-x)) := by
  llbc_verify_cond absFun (decide_eq_false (not_le.mpr h))

-- ── Loop ground instances ─────────────────────────────────────────────────────

theorem demo_sumTo_five :
    evalFun [] sumToFun 1000 [.int 5] at () |= .pureOutput (· = .int 10) := by
  llbc_verify_loop (.int 10)

theorem demo_fact_five :
    evalFun [] factFun 10000 [.int 5] at () |= .pureOutput (· = .int 120) := by
  llbc_verify_loop (.int 120)

theorem demo_fib_ten :
    evalFun [] fibFun 1000 [.int 10] at () |= .pureOutput (· = .int 55) := by
  llbc_verify_loop (.int 55)

-- ── Cross-function ground instance ────────────────────────────────────────────

theorem demo_square_five :
    evalFun [mulFun] squareFun 10 [.int 5] at () |= .pureOutput (· = .int 25) := by
  llbc_verify_loop (.int 25)

-- ── Summary ───────────────────────────────────────────────────────────────────
/-
  Every theorem above is proved by a ONE-LINE tactic call.
  No manual unfolding, no hand-crafted simp sets per theorem.

  Tactic  | Use case                    | Proof size
  --------|-----------------------------|-----------
  llbc_verify f        | Pure / identity function  | 1 line
  llbc_verify_prop f h | Arithmetic with overflow  | 1 line
  llbc_verify_cond f d | Conditional / comparison  | 1 line
  llbc_verify_loop v   | Loop ground instance      | 1 line
-/

end LeanPlVerify.Tactic.Demo
