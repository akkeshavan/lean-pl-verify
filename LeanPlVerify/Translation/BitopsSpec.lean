/-
  Translation/BitopsSpec.lean

  Verification of bitflags-style set operations extracted from the
  `bitops-verify` crate (examples/bitops-crate/).

  These functions implement the core operations that the `bitflags` v2 macro
  generates for each flags type:
    bf_is_empty    — test for empty set
    bf_contains    — subset containment check
    bf_intersects  — non-empty intersection check
    bf_union       — bitwise OR  (set union)
    bf_intersection — bitwise AND (set intersection)
    bf_symmetric_diff — bitwise XOR (symmetric difference)

  All six functions are pure, straight-line, and operate on u32 values.
  Every proof is by rfl: the Lean kernel evaluates the LLBC body symbolically
  and matches the stated output exactly.

  Theorem count: 15, sorry count: 0.
  Labels: BO1–BO15.
-/

import Mathlib.Tactic
import LeanPlVerify.Translation.BitopsDefs
import LeanPlVerify.Spec.Satisfies

namespace LeanPlVerify.LLBC.BitopsSpec

open LeanPlVerify LeanPlVerify.LLBC LeanPlVerify.LLBC.Charon

macro "bitops_simp" args:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals,
              evalRValuePure, evalBinOpPure, evalOperandPure, evalPlacePure,
              writePlacePure, evalLit,
              List.replicate, List.foldl, List.zipWith, List.set, List.find?,
              beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
              List.length_cons, List.length_nil,
              Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, $args,*])

-- ════════════════════════════════════════════════════════════════════════════
-- BO1–BO2: bf_is_empty
-- ════════════════════════════════════════════════════════════════════════════

/-- BO1 (symbolic): bf_is_empty returns (n == 0) for all n. -/
theorem bitops_is_empty_symbolic (n : Nat) :
    evalFun [] BfIsEmptyFun 10 [.uint n] at () |=
      .pureOutput (· = .bool_ (n == 0)) :=
  ⟨.bool_ (n == 0), (), rfl, rfl⟩

/-- BO2 (ground): bf_is_empty(0) = true; bf_is_empty(7) = false. -/
theorem bitops_is_empty_zero :
    evalFun [] BfIsEmptyFun 10 [.uint 0] at () |= .pureOutput (· = .bool_ true) :=
  ⟨.bool_ true, (), rfl, rfl⟩

theorem bitops_is_empty_nonzero :
    evalFun [] BfIsEmptyFun 10 [.uint 7] at () |= .pureOutput (· = .bool_ false) :=
  ⟨.bool_ false, (), rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- BO3–BO4: bf_union
-- ════════════════════════════════════════════════════════════════════════════

/-- BO3 (symbolic): bf_union(a, b) = a ||| b for all a b. -/
theorem bitops_union_symbolic (a b : Nat) :
    evalFun [] BfUnionFun 10 [.uint a, .uint b] at () |=
      .pureOutput (· = .uint (a ||| b)) :=
  ⟨.uint (a ||| b), (), rfl, rfl⟩

/-- BO4 (ground): bf_union(3, 5) = 7   (011 | 101 = 111). -/
theorem bitops_union_ground :
    evalFun [] BfUnionFun 10 [.uint 3, .uint 5] at () |= .pureOutput (· = .uint 7) :=
  ⟨.uint 7, (), rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- BO5–BO6: bf_intersection
-- ════════════════════════════════════════════════════════════════════════════

/-- BO5 (symbolic): bf_intersection(a, b) = a &&& b for all a b. -/
theorem bitops_intersection_symbolic (a b : Nat) :
    evalFun [] BfIntersectionFun 10 [.uint a, .uint b] at () |=
      .pureOutput (· = .uint (a &&& b)) :=
  ⟨.uint (a &&& b), (), rfl, rfl⟩

/-- BO6 (ground): bf_intersection(6, 3) = 2   (110 & 011 = 010). -/
theorem bitops_intersection_ground :
    evalFun [] BfIntersectionFun 10 [.uint 6, .uint 3] at () |= .pureOutput (· = .uint 2) :=
  ⟨.uint 2, (), rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- BO7–BO8: bf_symmetric_diff
-- ════════════════════════════════════════════════════════════════════════════

/-- BO7 (symbolic): bf_symmetric_diff(a, b) = a ^^^ b for all a b. -/
theorem bitops_symmetric_diff_symbolic (a b : Nat) :
    evalFun [] BfSymmetricDiffFun 10 [.uint a, .uint b] at () |=
      .pureOutput (· = .uint (a ^^^ b)) :=
  ⟨.uint (a ^^^ b), (), rfl, rfl⟩

/-- BO8 (ground): bf_symmetric_diff(6, 3) = 5   (110 ^ 011 = 101). -/
theorem bitops_symmetric_diff_ground :
    evalFun [] BfSymmetricDiffFun 10 [.uint 6, .uint 3] at () |= .pureOutput (· = .uint 5) :=
  ⟨.uint 5, (), rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- BO9–BO10: bf_contains
-- ════════════════════════════════════════════════════════════════════════════

/-- BO9 (symbolic): bf_contains(flags, other) = (flags &&& other == other). -/
theorem bitops_contains_symbolic (flags other : Nat) :
    evalFun [] BfContainsFun 10 [.uint flags, .uint other] at () |=
      .pureOutput (· = .bool_ (flags &&& other == other)) :=
  ⟨.bool_ (flags &&& other == other), (), rfl, rfl⟩

/-- BO10a (ground): bf_contains(7, 5) = true   (111 & 101 = 101). -/
theorem bitops_contains_true :
    evalFun [] BfContainsFun 10 [.uint 7, .uint 5] at () |= .pureOutput (· = .bool_ true) :=
  ⟨.bool_ true, (), rfl, rfl⟩

/-- BO10b (ground): bf_contains(3, 5) = false   (011 & 101 = 001 ≠ 101). -/
theorem bitops_contains_false :
    evalFun [] BfContainsFun 10 [.uint 3, .uint 5] at () |= .pureOutput (· = .bool_ false) :=
  ⟨.bool_ false, (), rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- BO11–BO12: bf_intersects
-- ════════════════════════════════════════════════════════════════════════════

/-- BO11 (symbolic): bf_intersects(a, b) = (a &&& b ≠ 0). -/
theorem bitops_intersects_symbolic (a b : Nat) :
    evalFun [] BfIntersectsFun 10 [.uint a, .uint b] at () |=
      .pureOutput (· = .bool_ (a &&& b != 0)) :=
  ⟨.bool_ (a &&& b != 0), (), rfl, rfl⟩

/-- BO12a: bf_intersects(6, 3) = true   (110 & 011 = 010 ≠ 0). -/
theorem bitops_intersects_true :
    evalFun [] BfIntersectsFun 10 [.uint 6, .uint 3] at () |= .pureOutput (· = .bool_ true) :=
  ⟨.bool_ true, (), rfl, rfl⟩

/-- BO12b: bf_intersects(8, 3) = false   (1000 & 0011 = 0). -/
theorem bitops_intersects_false :
    evalFun [] BfIntersectsFun 10 [.uint 8, .uint 3] at () |= .pureOutput (· = .bool_ false) :=
  ⟨.bool_ false, (), rfl, rfl⟩

end LeanPlVerify.LLBC.BitopsSpec
