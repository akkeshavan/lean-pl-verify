/-
  Translation/LoopInvariant.lean

  Inductive loop invariant: sumTo(n) = n*(n-1)/2  for all n ≥ 0.
-/

import Mathlib.Tactic
import LeanPlVerify.Translation.ElabSpec

namespace LeanPlVerify.LLBC.Spec

open LeanPlVerify LeanPlVerify.LLBC

-- ════════════════════════════════════════════════════════════════════════════
-- §1  sumRange
-- ════════════════════════════════════════════════════════════════════════════

def sumRange (i n : Int) : Int :=
  if i < n then i + sumRange (i + 1) n else 0
termination_by (n - i).toNat
decreasing_by omega

-- Use conv_lhs to avoid unfolding the RHS occurrence of sumRange
theorem sumRange_base {i n : Int} (h : ¬(i < n)) : sumRange i n = 0 := by
  conv_lhs => unfold sumRange
  exact if_neg h

theorem sumRange_step {i n : Int} (h : i < n) :
    sumRange i n = i + sumRange (i + 1) n := by
  conv_lhs => unfold sumRange
  exact if_pos h

/-- 2 * Σ(j=i..i+k-1) = k*(2i+k-1). No Int division; proved by Nat induction. -/
private theorem sumRange_double (k : Nat) (i : Int) :
    2 * sumRange i (i + ↑k) = ↑k * (2 * i + ↑k - 1) := by
  induction k generalizing i with
  | zero =>
    simp only [Nat.cast_zero, add_zero, zero_mul, mul_zero,
               sumRange_base (lt_irrefl i)]
  | succ k ih =>
    have hlt : i < i + (↑(k + 1) : Int) := by push_cast; omega
    rw [sumRange_step hlt]
    have key : sumRange (i + 1) (i + ↑(k + 1)) =
               sumRange (i + 1) ((i + 1) + ↑k) := by
      congr 1; push_cast; ring
    rw [key]
    have h2 : 2 * sumRange (i + 1) ((i + 1) + ↑k) = ↑k * (2 * (i + 1) + ↑k - 1) :=
      ih (i + 1)
    push_cast
    nlinarith [h2]

theorem sumRange_gaussSum (k : Nat) :
    sumRange 0 (↑k : Int) = ↑k * (↑k - 1) / 2 := by
  have h := sumRange_double k 0
  simp only [mul_zero, zero_add] at h
  omega

theorem sumRange_eq_gaussSum {n : Int} (hn : 0 ≤ n) :
    sumRange 0 n = n * (n - 1) / 2 := by
  lift n to Nat using hn; exact_mod_cast sumRange_gaussSum n

-- Helper lemmas for List.getElem? reduction (getElem?_pos needs side-condition
-- discharge that fails in simp only; these hold by kernel computation = rfl)
private theorem getElem?_cons_zero' (a : α) (l : List α) : (a :: l)[0]? = some a := rfl
private theorem getElem?_cons_succ' (a : α) (l : List α) (n : Nat) :
    (a :: l)[n + 1]? = l[n]? := rfl

-- ════════════════════════════════════════════════════════════════════════════
-- §2  Loop body and step lemmas
-- ════════════════════════════════════════════════════════════════════════════

-- locals: [0]=ret [1]=n [2]=acc [3]=i [4]=cond [5]=tmp
-- Not private: simp needs to unfold this definition
def sumToBody : LLBCStmt :=
  .assign (.var 4) (.binOp .lt (.copy (.var 3)) (.copy (.var 1)))
 (.ite (.copy (.var 4))
    (.assign (.var 5) (.binOp .add (.copy (.var 2)) (.copy (.var 3)))
    (.assign (.var 2) (.use (.copy (.var 5)))
    (.assign (.var 5) (.binOp .add (.copy (.var 3)) (.const (.int 1 .I32)))
    (.assign (.var 3) (.use (.copy (.var 5)))
     .skip))))
    .break_)

/-- One true iteration: acc += i, i += 1.  Needs ≥ 7 fuel. -/
theorem sumTo_body_true (env : FunEnv) (n acc i : Int) (c4 c5 : Value)
    (h    : i < n)
    (hov1 : IntBounds.minI32 ≤ acc + i ∧ acc + i ≤ IntBounds.maxI32)
    (hov2 : IntBounds.minI32 ≤ i + 1 ∧ i + 1 ≤ IntBounds.maxI32)
    (fuel : Nat) (hf : 7 ≤ fuel) :
    evalStmtFuel env fuel sumToBody
      [.unit, .int n, .int acc, .int i, c4, c5] =
    .ok (.next, [.unit, .int n, .int (acc + i), .int (i + 1),
                 .bool_ true, .int (i + 1)]) := by
  -- Use f + 7 (not 7 + f) so Nat.add recurses correctly for simp's n+1 matching
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 7 := ⟨fuel - 7, by omega⟩
  have hdt : decide (i < n) = true := decide_eq_true h
  -- simp only does zeta-reduction, so if_pos hov1/hov2 can match the
  -- `if IntBounds.minI32 ≤ v ∧ v ≤ IntBounds.maxI32` from evalBinOpPure .add
  simp only [sumToBody, evalStmtFuel, evalRValuePure, evalBinOpPure,
    evalOperandPure, evalPlacePure, writePlacePure, evalLit,
    List.set, getElem?_cons_zero', getElem?_cons_succ',
    hdt, if_pos hov1, if_pos hov2]

/-- One false iteration: body breaks, loop returns .next.  Needs ≥ 3 fuel. -/
theorem sumTo_body_false (env : FunEnv) (n acc i : Int) (c4 c5 : Value)
    (h    : ¬(i < n))
    (fuel : Nat) (hf : 3 ≤ fuel) :
    evalStmtFuel env fuel sumToBody
      [.unit, .int n, .int acc, .int i, c4, c5] =
    .ok (.break_, [.unit, .int n, .int acc, .int i, .bool_ false, c5]) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 3 := ⟨fuel - 3, by omega⟩
  have hdf : decide (i < n) = false := decide_eq_false h
  simp only [sumToBody, evalStmtFuel, evalRValuePure, evalBinOpPure,
    evalOperandPure, evalPlacePure, writePlacePure, evalLit,
    List.set, getElem?_cons_zero', getElem?_cons_succ', hdf]

-- ════════════════════════════════════════════════════════════════════════════
-- §3  Overflow condition
-- ════════════════════════════════════════════════════════════════════════════

def SumToOv (n acc i : Int) : Prop :=
  ∀ j : Int, i ≤ j → j < n →
    (IntBounds.minI32 ≤ acc + sumRange i j + j ∧
     acc + sumRange i j + j ≤ IntBounds.maxI32) ∧
    (IntBounds.minI32 ≤ j + 1 ∧ j + 1 ≤ IntBounds.maxI32)

/-- At j = i, sumRange i i = 0, so bounds collapse to acc + i. -/
private theorem SumToOv_self {n acc i : Int} (hlt : i < n) (hov : SumToOv n acc i) :
    (IntBounds.minI32 ≤ acc + i ∧ acc + i ≤ IntBounds.maxI32) ∧
    (IntBounds.minI32 ≤ i + 1 ∧ i + 1 ≤ IntBounds.maxI32) := by
  have h := hov i (le_refl i) hlt
  simp only [sumRange_base (lt_irrefl i), add_zero] at h
  exact h

theorem SumToOv_step {n acc i : Int} (hi : 0 ≤ i) (hlt : i < n)
    (hov : SumToOv n acc i) : SumToOv n (acc + i) (i + 1) := by
  intro j hj hjn
  have hj_gt : i < j := by omega
  have hs := hov j (by omega) hjn
  have hsr : (acc + i) + sumRange (i + 1) j = acc + sumRange i j := by
    rw [sumRange_step hj_gt]; ring
  exact ⟨⟨by linarith [hs.1.1, hsr], by linarith [hs.1.2, hsr]⟩, hs.2⟩

-- ════════════════════════════════════════════════════════════════════════════
-- §4  Loop invariant
-- ════════════════════════════════════════════════════════════════════════════

/-- After k iterations from state (acc, i), the loop terminates with
    slot[2] = acc + sumRange i n, slot[3] = n. -/
theorem sumTo_loop_correct (k : Nat) (env : FunEnv)
    (n acc i : Int) (c4 c5 : Value)
    (heq  : (n - i).toNat = k)
    (hi   : 0 ≤ i) (hin : i ≤ n)
    (hov  : SumToOv n acc i)
    (fuel : Nat) (hfuel : k + 8 ≤ fuel) :
    ∃ s4 s5 : Value,
    evalStmtFuel env fuel (.loop sumToBody)
      [.unit, .int n, .int acc, .int i, c4, c5] =
    .ok (.next, [.unit, .int n, .int (acc + sumRange i n), .int n, s4, s5]) := by
  induction k generalizing n acc i c4 c5 fuel with
  | zero =>
    have hieqn : i = n := le_antisymm hin (by omega)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨.bool_ false, c5, ?_⟩
    -- Simplify the RHS first
    rw [hieqn, sumRange_base (lt_irrefl n), add_zero]
    -- Now prove the loop evaluates to .next
    have hbody := sumTo_body_false env n acc n c4 c5 (lt_irrefl n) f (by omega)
    simp only [evalStmtFuel, hbody]
  | succ k' ih =>
    have hlt : i < n := by omega
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨hov1, hov2⟩ := SumToOv_self hlt hov
    have hbody_true := sumTo_body_true env n acc i c4 c5 hlt hov1 hov2 f (by omega)
    simp only [evalStmtFuel, hbody_true]
    obtain ⟨s4', s5', hloop⟩ :=
      ih n (acc + i) (i + 1) (.bool_ true) (.int (i + 1))
        (by omega) (by omega) hlt (SumToOv_step hi hlt hov) f (by omega)
    refine ⟨s4', s5', ?_⟩
    rw [hloop]
    have key : (acc + i) + sumRange (i + 1) n = acc + sumRange i n := by
      rw [sumRange_step hlt]; ring
    rw [key]

-- ════════════════════════════════════════════════════════════════════════════
-- §5  Main theorem
-- ════════════════════════════════════════════════════════════════════════════

def SumToSafe (n : Int) : Prop :=
  0 ≤ n ∧ n ≤ IntBounds.maxI32 ∧ n * (n - 1) / 2 ≤ IntBounds.maxI32

theorem sumToSafe_implies_ov (n : Int) (hsafe : SumToSafe n) : SumToOv n 0 0 := by
  obtain ⟨hn, hn_max, hgauss⟩ := hsafe
  intro j hj hjn
  -- hstep: sumRange 0 j + j = sumRange 0 (j+1)
  -- proved via sumRange_double to avoid peeling off wrong term
  have hstep : sumRange 0 j + j = sumRange 0 (j + 1) := by
    have hd1 : 2 * sumRange 0 j = j * (j - 1) := by
      have h := sumRange_double j.toNat 0
      simp only [mul_zero, zero_add] at h
      rwa [Int.toNat_of_nonneg hj] at h
    have hd2 : 2 * sumRange 0 (j + 1) = (j + 1) * j := by
      have h := sumRange_double (j + 1).toNat 0
      simp only [mul_zero, zero_add] at h
      rw [Int.toNat_of_nonneg (by omega : (0 : Int) ≤ j + 1),
          show (j + 1 - 1 : Int) = j from by omega] at h
      exact h
    linarith [show j * (j - 1) + 2 * j = (j + 1) * j from by ring]
  -- 2 * sumRange 0 (j+1) = (j+1)*j
  have h2j : 2 * sumRange 0 (j + 1) = (j + 1) * j := by
    have h := sumRange_double (j + 1).toNat 0
    simp only [mul_zero, zero_add] at h
    rw [Int.toNat_of_nonneg (by omega : (0 : Int) ≤ j + 1),
        show (j + 1 - 1 : Int) = j from by omega] at h
    exact h
  -- 2 * sumRange 0 n = n*(n-1)
  have h2n : 2 * sumRange 0 n = n * (n - 1) := by
    have h := sumRange_double n.toNat 0
    simp only [mul_zero, zero_add] at h
    rwa [Int.toNat_of_nonneg hn] at h
  -- monotonicity: (j+1)*j ≤ n*(n-1) since j+1 ≤ n and j ≤ n-1
  have hjn1 : (j + 1) * j ≤ n * (n - 1) := by
    nlinarith [show (j + 1 : Int) ≤ n from by omega]
  have hle : sumRange 0 (j + 1) ≤ sumRange 0 n := by linarith
  have hnn : 0 ≤ sumRange 0 (j + 1) := by linarith [show 0 ≤ (j + 1) * j from by nlinarith]
  have hmin : IntBounds.minI32 ≤ (0 : Int) := by norm_num [IntBounds.minI32]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · linarith  -- minI32 ≤ 0 + sumRange 0 j + j
  · linarith [sumRange_eq_gaussSum hn]  -- 0 + sumRange 0 j + j ≤ maxI32
  · exact ⟨by linarith, by linarith⟩  -- minI32 ≤ j+1 ∧ j+1 ≤ maxI32

theorem sumTo_correct (n : Int) (hsafe : SumToSafe n) :
    evalFun [] sumToFun (n.toNat + 12) [.int n] at () |=
      .pureOutput (· = .int (n * (n - 1) / 2)) := by
  have hov := sumToSafe_implies_ov n hsafe
  obtain ⟨hn, _, _⟩ := hsafe
  obtain ⟨s4, s5, hloop⟩ :=
    sumTo_loop_correct n.toNat (sumToFun :: []) n 0 0 .unit .unit
      (by omega) (by omega) hn hov (n.toNat + 9) (by omega)
  have hgauss : sumRange 0 n = n * (n - 1) / 2 := sumRange_eq_gaussSum hn
  refine ⟨.int (n * (n - 1) / 2), (), ?_, rfl⟩
  -- Reduce prefix assigns + .seq step (3 fuel) by rfl — no .loop unfolding
  have hpre : evalStmtFuel (sumToFun :: []) (n.toNat + 12) sumToFun.body
      (buildLocals sumToFun [.int n]) =
      (match evalStmtFuel (sumToFun :: []) (n.toNat + 9) (.loop sumToBody)
          [.unit, .int n, .int 0, .int 0, .unit, .unit] with
       | .error e => .error e
       | .ok (.next, s') => evalStmtFuel (sumToFun :: []) (n.toNat + 9)
           (.assign (.var 0) (.use (.copy (.var 2))) .return_) s'
       | .ok (other, s') => .ok (other, s')) := rfl
  -- Apply hpre then hloop (iota-reduces the match); then handle post-loop
  simp only [evalFun, evalFunBody, hpre, hloop]
  simp only [evalStmtFuel, evalRValuePure, evalOperandPure, evalPlacePure,
    writePlacePure, List.set, getElem?_cons_zero', getElem?_cons_succ',
    zero_add, hgauss]

end LeanPlVerify.LLBC.Spec
