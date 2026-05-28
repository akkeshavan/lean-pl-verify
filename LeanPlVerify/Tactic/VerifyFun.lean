/-
  Tactic/VerifyFun.lean

  Proof automation for LLBC verification theorems.

  Tactics provided:
  · `llbc_verify f`          — pure / rfl provable (id, neg, return42, ground loops)
  · `llbc_verify_loop v`     — ground loop with explicit output value v
  · `llbc_verify_cond f dh`  — decide-based branch (max, min, abs, clamp)
  · `llbc_verify_prop f h`   — Prop-if overflow check (add, sub, mul)
-/

import LeanPlVerify.Translation.Elaborator
import LeanPlVerify.Spec.Satisfies
import Mathlib.Tactic

namespace LeanPlVerify.Tactic

open LeanPlVerify LeanPlVerify.LLBC

-- ── llbc_verify: pure / rfl provable ─────────────────────────────────────────

/-- `llbc_verify f` proves `evalFun env f fuel args |= .pureOutput P` when
    the result follows by kernel reduction alone (no symbolic branching). -/
macro "llbc_verify" f:term : tactic =>
  `(tactic| (first | exact ⟨_, (), rfl, rfl⟩ |
      (refine ⟨_, (), ?_, rfl⟩;
       simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals,
         evalRValuePure, evalBinOpPure, evalOperandPure, evalPlacePure,
         writePlacePure, evalLit, evalOperandsPure, List.mapM, List.mapM.loop,
         List.replicate, List.foldl, List.zipWith, List.set, List.find?,
         beq_self_eq_true, List.getElem_cons_succ, List.getElem_cons_zero,
         getElem?_pos, List.length_cons, List.length_nil,
         Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, mkParam, mkLocal, $f:term])))

-- ── llbc_verify_loop: ground loop with explicit output ────────────────────────

/-- `llbc_verify_loop v` proves a ground loop instance;
    provide the expected output value `v`. -/
macro "llbc_verify_loop" v:term : tactic =>
  `(tactic| exact ⟨$v:term, (), rfl, rfl⟩)

-- ── llbc_verify_cond: decide-based conditional ────────────────────────────────

/-- `llbc_verify_cond f dh` proves goals that branch on `decide P`.
    `f` = function name; `dh` = `decide_eq_true h` or `decide_eq_false ...` -/
syntax "llbc_verify_cond" ident term : tactic

macro_rules
  | `(tactic| llbc_verify_cond $f:ident $dh:term) =>
    `(tactic| (first | exact ⟨_, (), rfl, rfl⟩ |
        (refine ⟨_, (), ?_, rfl⟩;
         simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals,
           evalRValuePure, evalBinOpPure, evalOperandPure, evalPlacePure,
           writePlacePure, evalLit, evalOperandsPure, List.mapM, List.mapM.loop,
           List.replicate, List.foldl, List.zipWith, List.set, List.find?,
           beq_self_eq_true, List.getElem_cons_succ, List.getElem_cons_zero,
           getElem?_pos, List.length_cons, List.length_nil,
           Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, mkParam, mkLocal,
           $f:ident, $dh:term])))

-- ── llbc_verify_prop: Prop-if overflow / bounds check ────────────────────────

/-- `llbc_verify_prop f h` proves goals with `if minI32 ≤ v ∧ v ≤ maxI32 then ...`
    overflow checks (add, sub, mul). `f` = function name; `h` proves the bounds. -/
syntax "llbc_verify_prop" ident term : tactic

macro_rules
  | `(tactic| llbc_verify_prop $f:ident $h:term) =>
    `(tactic| (first | exact ⟨_, (), rfl, rfl⟩ |
        (refine ⟨_, (), ?_, rfl⟩;
         simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals,
           evalRValuePure, evalBinOpPure, evalOperandPure, evalPlacePure,
           writePlacePure, evalLit, evalOperandsPure, List.mapM, List.mapM.loop,
           List.replicate, List.foldl, List.zipWith, List.set, List.find?,
           beq_self_eq_true, List.getElem_cons_succ, List.getElem_cons_zero,
           getElem?_pos, List.length_cons, List.length_nil,
           Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, mkParam, mkLocal, $f:ident];
         rw [if_pos $h:term]; rfl)))

end LeanPlVerify.Tactic
