/-
  Translation/FactInvariant.lean

  Inductive loop invariant: fact(n) = n!  for 0 ≤ n ≤ 12.

  Mirrors LoopInvariant.lean; demonstrates the methodology generalises
  from sumTo to factorial with minimal changes:
    · prodRange replaces sumRange
    · FactOv replaces SumToOv
    · body lemmas and induction structure are identical in shape

  Sorry count: 0
-/

import Mathlib.Tactic
import LeanPlVerify.Translation.ElabSpec

namespace LeanPlVerify.LLBC.Spec

open LeanPlVerify LeanPlVerify.LLBC

-- ════════════════════════════════════════════════════════════════════════════
-- §1  prodRange — product from i to n inclusive
-- ════════════════════════════════════════════════════════════════════════════

def prodRange (i n : Int) : Int :=
  if i ≤ n then i * prodRange (i + 1) n else 1
termination_by (n - i + 1).toNat
decreasing_by omega

theorem prodRange_base {i n : Int} (h : ¬(i ≤ n)) : prodRange i n = 1 := by
  conv_lhs => unfold prodRange; exact if_neg h

theorem prodRange_step {i n : Int} (h : i ≤ n) :
    prodRange i n = i * prodRange (i + 1) n := by
  conv_lhs => unfold prodRange; exact if_pos h

/-- Right peel: the last factor of a product range can be extracted.
    prodRange i (i + k) = prodRange i (i + k - 1) * (i + k) -/
private theorem prodRange_right_peel (k : Nat) (i : Int) (hi : 0 < i) :
    prodRange i (i + ↑k) = prodRange i (i + ↑k - 1) * (i + ↑k) := by
  induction k generalizing i with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    rw [prodRange_step (le_refl i), prodRange_base (by omega : ¬(i + 1 ≤ i)), mul_one,
        prodRange_base (by omega : ¬(i ≤ i - 1)), one_mul]
  | succ k' ih =>
    rw [show i + ↑(k' + 1) - 1 = i + ↑k' from by push_cast; ring,
        show i + ↑(k' + 1) = i + ↑k' + 1 from by push_cast; ring,
        prodRange_step (by push_cast; linarith [Nat.zero_le k'] : i ≤ i + ↑k' + 1),
        prodRange_step (by push_cast; linarith [Nat.zero_le k'] : i ≤ i + ↑k')]
    have h' : prodRange (i + 1) (i + ↑k' + 1) = prodRange (i + 1) (i + ↑k') * (i + ↑k' + 1) := by
      convert ih (i + 1) (by linarith) using 2 <;> ring
    rw [h']; ring_nf

/-- prodRange 1 k = k!  — standard induction on k (via right-peel lemma). -/
private theorem prodRange_factorial (k : Nat) :
    prodRange 1 (↑k : Int) = ↑k.factorial := by
  induction k with
  | zero => simp [prodRange_base (by norm_num : ¬((1 : Int) ≤ 0))]
  | succ k' ih =>
    rw [Nat.factorial_succ]
    push_cast
    rw [← ih]
    -- Goal: prodRange 1 (↑k' + 1 : Int) = (↑k' + 1) * prodRange 1 (↑k' : Int)
    have h := prodRange_right_peel k' 1 (by norm_num)
    simp only [show (1 : Int) + ↑k' - 1 = ↑k' from by ring,
               show (1 : Int) + ↑k' = ↑k' + 1 from by ring] at h
    -- h : prodRange 1 (↑k' + 1) = prodRange 1 (↑k') * (↑k' + 1)
    rw [h]; ring

theorem prodRange_factorialInt {n : Int} (hn : 0 ≤ n) :
    prodRange 1 n = ↑n.toNat.factorial := by
  lift n to Nat using hn; exact_mod_cast prodRange_factorial n

-- ════════════════════════════════════════════════════════════════════════════
-- §2  Loop body and step lemmas
-- ════════════════════════════════════════════════════════════════════════════

-- locals: [0]=ret [1]=n [2]=acc [3]=i [4]=cond [5]=tmp
-- Matches factFun.body's loop body (from ElabSpec.lean)
def factBody : LLBCStmt :=
  .assign (.var 4) (.binOp .le (.copy (.var 3)) (.copy (.var 1)))
 (.ite (.copy (.var 4))
    (.assign (.var 5) (.binOp .mul (.copy (.var 2)) (.copy (.var 3)))
    (.assign (.var 2) (.use (.copy (.var 5)))
    (.assign (.var 5) (.binOp .add (.copy (.var 3)) (.const (.int 1 .I32)))
    (.assign (.var 3) (.use (.copy (.var 5)))
     .skip))))
    .break_)

private theorem getElem?_cons_zero'' (a : α) (l : List α) : (a :: l)[0]? = some a := rfl
private theorem getElem?_cons_succ'' (a : α) (l : List α) (n : Nat) :
    (a :: l)[n + 1]? = l[n]? := rfl

/-- True iteration: acc *= i, i += 1.  Needs ≥ 7 fuel. -/
theorem fact_body_true (env : FunEnv) (n acc i : Int) (c4 c5 : Value)
    (h    : i ≤ n)
    (hov1 : IntBounds.minI32 ≤ acc * i ∧ acc * i ≤ IntBounds.maxI32)
    (hov2 : IntBounds.minI32 ≤ i + 1 ∧ i + 1 ≤ IntBounds.maxI32)
    (fuel : Nat) (hf : 7 ≤ fuel) :
    evalStmtFuel env fuel factBody
      [.unit, .int n, .int acc, .int i, c4, c5] =
    .ok (.next, [.unit, .int n, .int (acc * i), .int (i + 1),
                 .bool_ true, .int (i + 1)]) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 7 := ⟨fuel - 7, by omega⟩
  have hdt : decide (i ≤ n) = true := decide_eq_true h
  simp only [factBody, evalStmtFuel, evalRValuePure, evalBinOpPure,
    evalOperandPure, evalPlacePure, writePlacePure, evalLit,
    List.set, getElem?_cons_zero'', getElem?_cons_succ'',
    hdt, if_pos hov1, if_pos hov2]

/-- False iteration: condition fails, loop breaks.  Needs ≥ 3 fuel. -/
theorem fact_body_false (env : FunEnv) (n acc i : Int) (c4 c5 : Value)
    (h    : ¬(i ≤ n))
    (fuel : Nat) (hf : 3 ≤ fuel) :
    evalStmtFuel env fuel factBody
      [.unit, .int n, .int acc, .int i, c4, c5] =
    .ok (.break_, [.unit, .int n, .int acc, .int i, .bool_ false, c5]) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 3 := ⟨fuel - 3, by omega⟩
  have hdf : decide (i ≤ n) = false := decide_eq_false h
  simp only [factBody, evalStmtFuel, evalRValuePure, evalBinOpPure,
    evalOperandPure, evalPlacePure, writePlacePure, evalLit,
    List.set, getElem?_cons_zero'', getElem?_cons_succ'', hdf]

-- ════════════════════════════════════════════════════════════════════════════
-- §3  Overflow condition
-- ════════════════════════════════════════════════════════════════════════════

/-- At every iteration j ∈ [i, n], the running product acc * prodRange i j
    stays in I32 bounds, and j+1 is also in bounds. -/
def FactOv (n acc i : Int) : Prop :=
  ∀ j : Int, i ≤ j → j ≤ n →
    (IntBounds.minI32 ≤ acc * prodRange i j ∧
     acc * prodRange i j ≤ IntBounds.maxI32) ∧
    (IntBounds.minI32 ≤ j + 1 ∧ j + 1 ≤ IntBounds.maxI32)

/-- At j = i, prodRange i i = i, so the bound collapses to acc * i. -/
private theorem FactOv_self {n acc i : Int} (hlt : i ≤ n) (hov : FactOv n acc i) :
    (IntBounds.minI32 ≤ acc * i ∧ acc * i ≤ IntBounds.maxI32) ∧
    (IntBounds.minI32 ≤ i + 1 ∧ i + 1 ≤ IntBounds.maxI32) := by
  have h := hov i (le_refl i) hlt
  have hprod : prodRange i i = i := by
    rw [prodRange_step (le_refl i), prodRange_base (by omega : ¬(i + 1 ≤ i)), mul_one]
  rw [hprod] at h
  exact h

theorem FactOv_step {n acc i : Int} (hi : 0 ≤ i) (hlt : i ≤ n)
    (hov : FactOv n acc i) : FactOv n (acc * i) (i + 1) := by
  intro j hj hjn
  -- j ≥ i since j ≥ i+1 > i
  have hj_ge : i ≤ j := by omega
  have hs := hov j hj_ge hjn
  -- (acc * i) * prodRange (i+1) j = acc * prodRange i j
  have hpr : (acc * i) * prodRange (i + 1) j = acc * prodRange i j := by
    rw [prodRange_step hj_ge]; ring
  exact ⟨⟨by linarith [hs.1.1, hpr], by linarith [hs.1.2, hpr]⟩, hs.2⟩

-- ════════════════════════════════════════════════════════════════════════════
-- §4  Loop invariant
-- ════════════════════════════════════════════════════════════════════════════

/-- After k iterations from (acc, i), the loop terminates with
    acc * prodRange i n in slot[2] and n+1 in slot[3]. -/
theorem fact_loop_correct (k : Nat) (env : FunEnv)
    (n acc i : Int) (c4 c5 : Value)
    (heq  : (n - i + 1).toNat = k)
    (hi   : 0 ≤ i) (hin : i ≤ n + 1)
    (hov  : FactOv n acc i)
    (fuel : Nat) (hfuel : k + 8 ≤ fuel) :
    ∃ s4 s5 : Value,
    evalStmtFuel env fuel (.loop factBody)
      [.unit, .int n, .int acc, .int i, c4, c5] =
    .ok (.next, [.unit, .int n, .int (acc * prodRange i n), .int (n + 1), s4, s5]) := by
  induction k generalizing n acc i c4 c5 fuel with
  | zero =>
    -- i = n + 1; prodRange (n+1) n = 1; acc * 1 = acc
    have hin1 : i = n + 1 := by omega
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨.bool_ false, c5, ?_⟩
    rw [hin1, prodRange_base (by omega : ¬(n + 1 ≤ n)), mul_one]
    have hbody := fact_body_false env n acc (n + 1) c4 c5 (by omega) f (by omega)
    simp only [evalStmtFuel, hbody]
  | succ k' ih =>
    have hlt : i ≤ n := by omega
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨hov1, hov2⟩ := FactOv_self hlt hov
    have hbody_true := fact_body_true env n acc i c4 c5 hlt hov1 hov2 f (by omega)
    simp only [evalStmtFuel, hbody_true]
    obtain ⟨s4', s5', hloop⟩ :=
      ih n (acc * i) (i + 1) (.bool_ true) (.int (i + 1))
        (by omega) (by omega) (by omega) (FactOv_step hi hlt hov) f (by omega)
    refine ⟨s4', s5', ?_⟩
    rw [hloop]
    -- (acc * i) * prodRange (i+1) n = acc * prodRange i n
    have key : (acc * i) * prodRange (i + 1) n = acc * prodRange i n := by
      rw [prodRange_step (by omega : i ≤ n)]; ring
    rw [key]

-- ════════════════════════════════════════════════════════════════════════════
-- §5  Main theorem
-- ════════════════════════════════════════════════════════════════════════════

/-- fact is safe for 0 ≤ n ≤ 12 (since 12! = 479001600 < maxI32). -/
def FactSafe (n : Int) : Prop :=
  0 ≤ n ∧ n ≤ 12

/-- Overflow condition holds for safe inputs (all intermediate j! ≤ 12! < maxI32). -/
theorem factSafe_implies_ov (n : Int) (hsafe : FactSafe n) : FactOv n 1 1 := by
  obtain ⟨hn, hn12⟩ := hsafe
  intro j hj hjn
  have hj12  : j ≤ 12 := le_trans hjn hn12
  have hj0   : 0 ≤ j  := by linarith
  have hjnat : j.toNat ≤ 12 := by omega
  -- prodRange 1 j = j!
  have hprod : prodRange 1 j = ↑j.toNat.factorial := prodRange_factorialInt hj0
  -- j! ≤ 12! = 479001600 < maxI32 = 2147483647
  have hfact_le : j.toNat.factorial ≤ 479001600 := by
    have : j.toNat ≤ 12 := hjnat
    interval_cases j.toNat <;> norm_num
  have hfact_int : (↑j.toNat.factorial : Int) ≤ 479001600 := by exact_mod_cast hfact_le
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- minI32 ≤ 1 * prodRange 1 j
    rw [one_mul, hprod]
    have : (0 : Int) ≤ ↑j.toNat.factorial := Int.ofNat_nonneg _
    simp only [IntBounds.minI32]; linarith
  · -- 1 * prodRange 1 j ≤ maxI32
    rw [one_mul, hprod]
    simp only [IntBounds.maxI32]; linarith
  · -- minI32 ≤ j + 1 ∧ j + 1 ≤ maxI32
    exact ⟨by simp only [IntBounds.minI32]; linarith,
           by simp only [IntBounds.maxI32]; linarith⟩

theorem fact_correct (n : Int) (hsafe : FactSafe n) :
    evalFun [] factFun (n.toNat + 12) [.int n] at () |=
      .pureOutput (· = .int ↑n.toNat.factorial) := by
  have hov := factSafe_implies_ov n hsafe
  obtain ⟨hn, _⟩ := hsafe
  obtain ⟨s4, s5, hloop⟩ :=
    fact_loop_correct n.toNat (factFun :: []) n 1 1 .unit .unit
      (by omega) (by omega) (by omega) hov (n.toNat + 9) (by omega)
  have hfact : prodRange 1 n = ↑n.toNat.factorial := prodRange_factorialInt hn
  refine ⟨.int ↑n.toNat.factorial, (), ?_, rfl⟩
  -- Reduce prefix assigns + .seq (same fuel arithmetic as sumTo_correct)
  have hpre : evalStmtFuel (factFun :: []) (n.toNat + 12) factFun.body
      (buildLocals factFun [.int n]) =
      (match evalStmtFuel (factFun :: []) (n.toNat + 9) (.loop factBody)
          [.unit, .int n, .int 1, .int 1, .unit, .unit] with
       | .error e => .error e
       | .ok (.next, s') => evalStmtFuel (factFun :: []) (n.toNat + 9)
           (.assign (.var 0) (.use (.copy (.var 2))) .return_) s'
       | .ok (other, s') => .ok (other, s')) := rfl
  simp only [evalFun, evalFunBody, hpre, hloop]
  simp only [evalStmtFuel, evalRValuePure, evalOperandPure, evalPlacePure,
    writePlacePure, List.set, getElem?_cons_zero'', getElem?_cons_succ'',
    one_mul, hfact]

end LeanPlVerify.LLBC.Spec
