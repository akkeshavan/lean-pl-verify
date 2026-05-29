/-
  Translation/ArithUtilsSpec.lean

  Verification of arithmetic utility functions extracted from the
  `arith-utils-verify` crate (examples/arith-utils-crate/).

  These functions are analogous to std::u32 stable API (since Rust 1.73):
    div_ceil    — ceiling division:  ⌈a/b⌉
    abs_diff    — unsigned absolute difference:  |a − b|
    midpoint    — overflow-safe floor midpoint:  ⌊(a+b)/2⌋
    is_pow2     — power-of-two test:  n > 0 ∧ (n & (n−1) = 0)

  All proofs use the kernel evaluator (rfl), matching the LLBC bodies
  against the expected outputs exactly.

  Theorem count: 15, sorry count: 0.
  Labels: AU1–AU15.
-/

import Mathlib.Tactic
import LeanPlVerify.Translation.ArithUtilsDefs
import LeanPlVerify.Spec.Satisfies

namespace LeanPlVerify.LLBC.ArithUtilsSpec

open LeanPlVerify LeanPlVerify.LLBC LeanPlVerify.LLBC.Charon

macro "arith_simp" args:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals,
              evalRValuePure, evalBinOpPure, evalOperandPure, evalPlacePure,
              writePlacePure, evalLit,
              List.replicate, List.foldl, List.zipWith, List.set, List.find?,
              beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
              List.length_cons, List.length_nil,
              Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, $args,*])

-- ════════════════════════════════════════════════════════════════════════════
-- AU1–AU4: div_ceil — ceiling division ⌈a/b⌉
-- ════════════════════════════════════════════════════════════════════════════

/-- AU1 (ground): div_ceil(7, 2) = 4   (odd dividend, rounds up). -/
theorem arith_div_ceil_7_2 :
    evalFun [] DivCeilFun 100 [.uint 7, .uint 2] at () |= .pureOutput (· = .uint 4) :=
  ⟨.uint 4, (), rfl, rfl⟩

/-- AU2 (ground): div_ceil(8, 2) = 4   (exact division, no rounding). -/
theorem arith_div_ceil_8_2 :
    evalFun [] DivCeilFun 100 [.uint 8, .uint 2] at () |= .pureOutput (· = .uint 4) :=
  ⟨.uint 4, (), rfl, rfl⟩

/-- AU3 (ground): div_ceil(10, 3) = 4   (10 % 3 = 1, rounds up). -/
theorem arith_div_ceil_10_3 :
    evalFun [] DivCeilFun 100 [.uint 10, .uint 3] at () |= .pureOutput (· = .uint 4) :=
  ⟨.uint 4, (), rfl, rfl⟩

/-- AU4 (ground): div_ceil(9, 3) = 3   (exact division). -/
theorem arith_div_ceil_9_3 :
    evalFun [] DivCeilFun 100 [.uint 9, .uint 3] at () |= .pureOutput (· = .uint 3) :=
  ⟨.uint 3, (), rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- AU5–AU7: abs_diff — unsigned absolute difference |a − b|
-- ════════════════════════════════════════════════════════════════════════════

/-- AU5 (ground): abs_diff(7, 3) = 4   (a > b branch). -/
theorem arith_abs_diff_7_3 :
    evalFun [] AbsDiffFun 60 [.uint 7, .uint 3] at () |= .pureOutput (· = .uint 4) :=
  ⟨.uint 4, (), rfl, rfl⟩

/-- AU6 (ground): abs_diff(3, 7) = 4   (b > a branch). -/
theorem arith_abs_diff_3_7 :
    evalFun [] AbsDiffFun 60 [.uint 3, .uint 7] at () |= .pureOutput (· = .uint 4) :=
  ⟨.uint 4, (), rfl, rfl⟩

/-- AU7 (ground): abs_diff(5, 5) = 0   (equal inputs). -/
theorem arith_abs_diff_5_5 :
    evalFun [] AbsDiffFun 60 [.uint 5, .uint 5] at () |= .pureOutput (· = .uint 0) :=
  ⟨.uint 0, (), rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- AU8–AU10: midpoint — overflow-safe floor midpoint ⌊(a+b)/2⌋  (ground instances)
-- ════════════════════════════════════════════════════════════════════════════

/-- AU8 (ground): midpoint(0, 8) = 4   (simple even case). -/
theorem arith_midpoint_0_8 :
    evalFun [] MidpointFun 60 [.uint 0, .uint 8] at () |= .pureOutput (· = .uint 4) :=
  ⟨.uint 4, (), rfl, rfl⟩

/-- AU9 (ground): midpoint(3, 7) = 5   (floor of 5.0). -/
theorem arith_midpoint_3_7 :
    evalFun [] MidpointFun 60 [.uint 3, .uint 7] at () |= .pureOutput (· = .uint 5) :=
  ⟨.uint 5, (), rfl, rfl⟩

/-- AU10 (ground): midpoint(3, 5) = 4   (odd inputs, carry bit contributes). -/
theorem arith_midpoint_3_5 :
    evalFun [] MidpointFun 60 [.uint 3, .uint 5] at () |= .pureOutput (· = .uint 4) :=
  ⟨.uint 4, (), rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- AU11–AU15: is_pow2 — power-of-two test: n > 0 ∧ (n & (n−1) = 0)
-- ════════════════════════════════════════════════════════════════════════════

/-- AU11 (ground): is_pow2(0) = false   (zero is not a power of two). -/
theorem arith_is_pow2_zero :
    evalFun [] IsPow2Fun 40 [.uint 0] at () |= .pureOutput (· = .bool_ false) :=
  ⟨.bool_ false, (), rfl, rfl⟩

/-- AU12 (ground): is_pow2(1) = true   (2^0 = 1). -/
theorem arith_is_pow2_one :
    evalFun [] IsPow2Fun 40 [.uint 1] at () |= .pureOutput (· = .bool_ true) :=
  ⟨.bool_ true, (), rfl, rfl⟩

/-- AU13 (ground): is_pow2(2) = true   (2^1 = 2). -/
theorem arith_is_pow2_two :
    evalFun [] IsPow2Fun 40 [.uint 2] at () |= .pureOutput (· = .bool_ true) :=
  ⟨.bool_ true, (), rfl, rfl⟩

/-- AU14 (ground): is_pow2(3) = false   (3 is not a power of two). -/
theorem arith_is_pow2_three :
    evalFun [] IsPow2Fun 40 [.uint 3] at () |= .pureOutput (· = .bool_ false) :=
  ⟨.bool_ false, (), rfl, rfl⟩

/-- AU15 (ground): is_pow2(8) = true   (2^3 = 8). -/
theorem arith_is_pow2_eight :
    evalFun [] IsPow2Fun 40 [.uint 8] at () |= .pureOutput (· = .bool_ true) :=
  ⟨.bool_ true, (), rfl, rfl⟩

end LeanPlVerify.LLBC.ArithUtilsSpec
