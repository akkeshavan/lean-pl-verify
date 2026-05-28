/-
  Translation/FibInvariant.lean

  Inductive loop invariant: fib(n) = Nat.fib n  for 0 ≤ n ≤ 45.

  Structure mirrors LoopInvariant.lean and FactInvariant.lean.
  Key difference from sumTo/fact: the invariant tracks TWO accumulators
  (a = F(k), b = F(k+1)) simultaneously.

  Mathlib lemma used: Nat.fib_add_two : Nat.fib (n+2) = Nat.fib n + Nat.fib (n+1)

  Sorry count: 0
    · fibSafe_implies_ov uses `native_decide` for the ground fact Nat.fib 46 ≤ maxI32.
      native_decide is not sorry — it is verified by Lean's native code compiler.
      All other proofs are kernel-checked.
-/

import Mathlib.Tactic
import LeanPlVerify.Translation.ElabSpec

namespace LeanPlVerify.LLBC.Spec

open LeanPlVerify LeanPlVerify.LLBC

-- Helper lemmas for List.getElem? reduction (same pattern as LoopInvariant.lean)
private theorem getElem?_cons_zero_fib (a : α) (l : List α) : (a :: l)[0]? = some a := rfl
private theorem getElem?_cons_succ_fib (a : α) (l : List α) (n : Nat) :
    (a :: l)[n + 1]? = l[n]? := rfl

-- ════════════════════════════════════════════════════════════════════════════
-- §1  Loop body and step lemmas
-- ════════════════════════════════════════════════════════════════════════════

/-
  locals: [0]=ret [1]=n [2]=a [3]=b [4]=i [5]=t [6]=cond [7]=tmp
  Matches fibFun.body's loop body (from ElabSpec.lean).

  One true iteration:
    t   = b          (save old b)
    tmp = a + b      (compute next fib)
    b   = tmp        (b := a+b)
    a   = t          (a := old b)
    tmp = i + 1
    i   = tmp
-/
def fibBody : LLBCStmt :=
  .assign (.var 6) (.binOp .lt (.copy (.var 4)) (.copy (.var 1)))
 (.ite (.copy (.var 6))
    (.assign (.var 5) (.use (.copy (.var 3)))
    (.assign (.var 7) (.binOp .add (.copy (.var 2)) (.copy (.var 3)))
    (.assign (.var 3) (.use (.copy (.var 7)))
    (.assign (.var 2) (.use (.copy (.var 5)))
    (.assign (.var 7) (.binOp .add (.copy (.var 4)) (.const (.int 1 .I32)))
    (.assign (.var 4) (.use (.copy (.var 7)))
     .skip))))))
    .break_)

/-- True iteration: a := b, b := a+b, i := i+1.  Needs ≥ 9 fuel. -/
theorem fib_body_true (env : FunEnv) (n a b i : Int) (c5 c6 c7 : Value)
    (h    : i < n)
    (hov1 : IntBounds.minI32 ≤ a + b ∧ a + b ≤ IntBounds.maxI32)
    (hov2 : IntBounds.minI32 ≤ i + 1 ∧ i + 1 ≤ IntBounds.maxI32)
    (fuel : Nat) (hf : 9 ≤ fuel) :
    evalStmtFuel env fuel fibBody
      [.unit, .int n, .int a, .int b, .int i, c5, c6, c7] =
    .ok (.next, [.unit, .int n, .int b, .int (a + b), .int (i + 1),
                 .int b, .bool_ true, .int (i + 1)]) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 9 := ⟨fuel - 9, by omega⟩
  have hdt : decide (i < n) = true := decide_eq_true h
  simp only [fibBody, evalStmtFuel, evalRValuePure, evalBinOpPure,
    evalOperandPure, evalPlacePure, writePlacePure, evalLit,
    List.set, getElem?_cons_zero_fib, getElem?_cons_succ_fib,
    hdt, if_pos hov1, if_pos hov2]

/-- False iteration: condition fails, loop breaks.  Needs ≥ 3 fuel. -/
theorem fib_body_false (env : FunEnv) (n a b i : Int) (c5 c6 c7 : Value)
    (h    : ¬(i < n))
    (fuel : Nat) (hf : 3 ≤ fuel) :
    evalStmtFuel env fuel fibBody
      [.unit, .int n, .int a, .int b, .int i, c5, c6, c7] =
    .ok (.break_, [.unit, .int n, .int a, .int b, .int i, c5, .bool_ false, c7]) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 3 := ⟨fuel - 3, by omega⟩
  have hdf : decide (i < n) = false := decide_eq_false h
  simp only [fibBody, evalStmtFuel, evalRValuePure, evalBinOpPure,
    evalOperandPure, evalPlacePure, writePlacePure, evalLit,
    List.set, getElem?_cons_zero_fib, getElem?_cons_succ_fib, hdf]

-- ════════════════════════════════════════════════════════════════════════════
-- §2  Overflow condition
-- ════════════════════════════════════════════════════════════════════════════

/-- At every iteration j ∈ [i, n), F(j) + F(j+1) stays in I32 bounds
    and j+1 is in bounds.
    Parametric in i (the current loop counter), not in a and b directly,
    since the invariant pins a = F(i), b = F(i+1). -/
def FibOv (n i : Int) : Prop :=
  ∀ j : Int, i ≤ j → j < n →
    (IntBounds.minI32 ≤ (↑(Nat.fib j.toNat) : Int) + ↑(Nat.fib (j.toNat + 1)) ∧
     (↑(Nat.fib j.toNat) : Int) + ↑(Nat.fib (j.toNat + 1)) ≤ IntBounds.maxI32) ∧
    (IntBounds.minI32 ≤ j + 1 ∧ j + 1 ≤ IntBounds.maxI32)

/-- At j = i, the overflow condition gives us bounds on F(i) + F(i+1) directly. -/
private theorem FibOv_self {n i : Int} (hlt : i < n) (hov : FibOv n i) :
    (IntBounds.minI32 ≤ (↑(Nat.fib i.toNat) : Int) + ↑(Nat.fib (i.toNat + 1)) ∧
     (↑(Nat.fib i.toNat) : Int) + ↑(Nat.fib (i.toNat + 1)) ≤ IntBounds.maxI32) ∧
    (IntBounds.minI32 ≤ i + 1 ∧ i + 1 ≤ IntBounds.maxI32) :=
  hov i (le_refl i) hlt

/-- The overflow condition is monotone in i: if it holds from i, it holds from i+1. -/
theorem FibOv_step {n i : Int} (_ : i < n) (hov : FibOv n i) : FibOv n (i + 1) := by
  intro j hj hjn
  exact hov j (by omega) hjn

-- ════════════════════════════════════════════════════════════════════════════
-- §3  Loop invariant
-- ════════════════════════════════════════════════════════════════════════════

/-- After k iterations from state (a = F(i), b = F(i+1), i), the loop terminates with
    slot[2] = F(n) and slot[3] = F(n+1) and slot[4] = n. -/
theorem fib_loop_correct (k : Nat) (env : FunEnv)
    (n a b i : Int) (c5 c6 c7 : Value)
    (heq   : (n - i).toNat = k)
    (hi    : 0 ≤ i) (hin : i ≤ n)
    (hinvA : a = ↑(Nat.fib i.toNat))
    (hinvB : b = ↑(Nat.fib (i.toNat + 1)))
    (hov   : FibOv n i)
    (fuel  : Nat) (hfuel : k + 10 ≤ fuel) :
    ∃ s5 s6 s7 : Value,
    evalStmtFuel env fuel (.loop fibBody)
      [.unit, .int n, .int a, .int b, .int i, c5, c6, c7] =
    .ok (.next, [.unit, .int n, .int ↑(Nat.fib n.toNat),
                 .int ↑(Nat.fib (n.toNat + 1)), .int n, s5, s6, s7]) := by
  induction k generalizing n a b i c5 c6 c7 fuel with
  | zero =>
    -- i = n; prodRange is empty; result is (a, b) = (F(n), F(n+1))
    have hieqn : i = n := le_antisymm hin (by omega)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨c5, .bool_ false, c7, ?_⟩
    rw [hieqn] at hinvA hinvB ⊢
    rw [← hinvA, ← hinvB]
    have hbody := fib_body_false env n a b n c5 c6 c7 (lt_irrefl n) f (by omega)
    simp only [evalStmtFuel, hbody]
  | succ k' ih =>
    have hlt : i < n := by omega
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    -- Overflow bounds at j = i
    obtain ⟨hov_sum, hov_succ⟩ := FibOv_self hlt hov
    -- Restate in terms of a and b
    rw [← hinvA, ← hinvB] at hov_sum
    have hbody := fib_body_true env n a b i c5 c6 c7 hlt hov_sum hov_succ f (by omega)
    simp only [evalStmtFuel, hbody]
    -- Connect new state to Fibonacci values at i+1
    have hi1 : (i + 1).toNat = i.toNat + 1 := by omega
    -- new a = old b = F(i+1) = F((i+1).toNat)
    have hinvA' : b = ↑(Nat.fib (i + 1).toNat) := by
      rw [hi1]; exact hinvB
    -- new b = old a + old b = F(i) + F(i+1) = F(i+2) = F((i+1).toNat + 1)
    have hinvB' : a + b = ↑(Nat.fib ((i + 1).toNat + 1)) := by
      rw [hinvA, hinvB, hi1,
          show i.toNat + 1 + 1 = i.toNat + 2 from by omega,
          ← Nat.cast_add, ← Nat.fib_add_two]
    obtain ⟨s5', s6', s7', hloop⟩ :=
      ih n b (a + b) (i + 1) (.int b) (.bool_ true) (.int (i + 1))
        (by omega) (by omega) (by linarith)
        hinvA' hinvB' (FibOv_step hlt hov) f (by omega)
    exact ⟨s5', s6', s7', hloop⟩

-- ════════════════════════════════════════════════════════════════════════════
-- §4  Main theorem
-- ════════════════════════════════════════════════════════════════════════════

/-- fib is safe for 0 ≤ n ≤ 45.
    F(46) = 1836311903 < maxI32, so F(j+2) ≤ F(46) < maxI32 for j ≤ 44 (j < n ≤ 45). -/
def FibSafe (n : Int) : Prop :=
  0 ≤ n ∧ n ≤ 45

/-- The overflow condition holds for safe inputs. -/
theorem fibSafe_implies_ov (n : Int) (hsafe : FibSafe n) : FibOv n 0 := by
  obtain ⟨hn, hn45⟩ := hsafe
  intro j hj hjn
  have hj0 : 0 ≤ j := by linarith
  -- j < n ≤ 45 so j ≤ 44 so j+2 ≤ 46
  have hjnat2 : j.toNat + 2 ≤ 46 := by omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- lower bound: Fib ≥ 0, so minI32 ≤ 0 ≤ F(j) + F(j+1)
    have h1 : (0 : Int) ≤ ↑(Nat.fib j.toNat) := Int.ofNat_nonneg _
    have h2 : (0 : Int) ≤ ↑(Nat.fib (j.toNat + 1)) := Int.ofNat_nonneg _
    norm_num [IntBounds.minI32]; linarith
  · -- upper bound: F(j)+F(j+1) = F(j+2) ≤ F(46) = 1836311903 < maxI32
    have hstep : Nat.fib j.toNat + Nat.fib (j.toNat + 1) = Nat.fib (j.toNat + 2) := by
      rw [← Nat.fib_add_two]
    have hmono : Nat.fib (j.toNat + 2) ≤ Nat.fib 46 := Nat.fib_mono hjnat2
    -- Nat.fib 46 = 1836311903 — verified by native_decide (efficient native evaluation)
    have hfib46 : Nat.fib 46 = 1836311903 := by native_decide
    have hle_nat : Nat.fib (j.toNat + 2) ≤ 1836311903 := hfib46 ▸ hmono
    have hle_int : (Nat.fib (j.toNat + 2) : Int) ≤ 1836311903 := by exact_mod_cast hle_nat
    have hsum : (↑(Nat.fib j.toNat) : Int) + ↑(Nat.fib (j.toNat + 1)) =
                ↑(Nat.fib (j.toNat + 2)) := by exact_mod_cast hstep
    norm_num [IntBounds.maxI32]; linarith
  · -- i+1 bounds: j+1 ≤ 45 ≤ maxI32
    exact ⟨by norm_num [IntBounds.minI32]; linarith,
           by norm_num [IntBounds.maxI32]; linarith⟩

theorem fib_correct (n : Int) (hsafe : FibSafe n) :
    evalFun [] fibFun (n.toNat + 14) [.int n] at () |=
      .pureOutput (· = .int ↑(Nat.fib n.toNat)) := by
  have hov := fibSafe_implies_ov n hsafe
  obtain ⟨hn, _⟩ := hsafe
  -- Initial invariant: a = F(0) = 0, b = F(1) = 1
  have hfib0 : (Nat.fib 0 : Int) = 0 := by simp [Nat.fib]
  have hfib1 : (Nat.fib 1 : Int) = 1 := by simp [Nat.fib]
  obtain ⟨s5, s6, s7, hloop⟩ :=
    fib_loop_correct n.toNat (fibFun :: []) n 0 1 0 .unit .unit .unit
      (by omega) (by omega) hn
      (by simp [hfib0]) (by simp [hfib1])
      hov (n.toNat + 10) (by omega)
  refine ⟨.int ↑(Nat.fib n.toNat), (), ?_, rfl⟩
  -- hpre: reduce 3 prefix assigns + .seq (4 fuel) by kernel computation (rfl)
  -- leaving the loop with n.toNat+10 fuel
  have hpre : evalStmtFuel (fibFun :: []) (n.toNat + 14) fibFun.body
      (buildLocals fibFun [.int n]) =
      (match evalStmtFuel (fibFun :: []) (n.toNat + 10) (.loop fibBody)
          [.unit, .int n, .int 0, .int 1, .int 0, .unit, .unit, .unit] with
       | .error e => .error e
       | .ok (.next, s') => evalStmtFuel (fibFun :: []) (n.toNat + 10)
           (.assign (.var 0) (.use (.copy (.var 2))) .return_) s'
       | .ok (other, s') => .ok (other, s')) := rfl
  simp only [evalFun, evalFunBody, hpre, hloop]
  simp only [evalStmtFuel, evalRValuePure, evalOperandPure, evalPlacePure,
    writePlacePure, List.set,
    getElem?_cons_zero_fib, getElem?_cons_succ_fib]

end LeanPlVerify.LLBC.Spec
