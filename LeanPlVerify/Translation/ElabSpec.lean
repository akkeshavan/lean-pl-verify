/-
  Translation/ElabSpec.lean

  Theorems connecting LLBC elaboration to ProgramSpec.  Zero sorry.

  Proof shapes used:
    · Straight-line (no branching, no overflow):
        exact ⟨witness, (), rfl, rfl⟩
    · Arithmetic overflow guard:
        refine ⟨…, (), ?_, rfl⟩; simp [evalFun, …]; simp [if_pos h]
    · Branching on a comparison:
        simp [decide_eq_true h]  or  simp [decide_eq_false h]
    · Derived (monotone, nocrash):
        sat_pureOutput_nocrash / sat_pureOutput_mono
    · Ground numeric (rfl for closed terms):
        exact ⟨.int N, (), rfl, rfl⟩  -- works because evalStmtFuel is structurally recursive

  LLBC memory convention (Charon):
    locals[0]  = return slot
    locals[1…] = parameters (left-to-right), then temporaries

  Theorem count: 30, sorry count: 0.
-/

import Mathlib.Tactic
import LeanPlVerify.Translation.Elaborator
import LeanPlVerify.Spec.Satisfies

namespace LeanPlVerify.LLBC.Spec

open LeanPlVerify LeanPlVerify.LLBC

-- mkParam and mkLocal are defined in Translation/Elaborator.lean (LeanPlVerify.LLBC namespace)


-- ════════════════════════════════════════════════════════════════════════════
-- F1: return42 — fn return42() -> i32 { 42 }
-- ════════════════════════════════════════════════════════════════════════════

def return42Fun : LLBCFunDef := {
  name   := "return42"
  params := []
  locals := [mkLocal 0 (.int .I32)]
  retTy  := .int .I32
  body   := .assign (.var 0) (.use (.const (.int 42 .I32))) .return_
}

#eval evalFun [] return42Fun 10 [] ()   -- Except.ok (Value.int 42, ())

theorem elab_return42 :
    evalFun [] return42Fun 10 [] at () |= .pureOutput (· = .int 42) :=
  ⟨.int 42, (), rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- F2: id — fn id(x: i32) -> i32 { x }
-- ════════════════════════════════════════════════════════════════════════════

def idFun : LLBCFunDef := {
  name   := "id"
  params := [mkParam 1 (.int .I32) "x"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "x"]
  retTy  := .int .I32
  body   := .assign (.var 0) (.use (.copy (.var 1))) .return_
}

#eval evalFun [] idFun 10 [.int 7]    ()
#eval evalFun [] idFun 10 [.int (-3)] ()

theorem elab_id (x : Int) :
    evalFun [] idFun 10 [.int x] at () |= .pureOutput (· = .int x) :=
  ⟨.int x, (), rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- F3: neg — fn neg(x: i32) -> i32 { -x }
-- ════════════════════════════════════════════════════════════════════════════

def negFun : LLBCFunDef := {
  name   := "neg"
  params := [mkParam 1 (.int .I32) "x"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "x"]
  retTy  := .int .I32
  body   := .assign (.var 0) (.unOp .neg (.copy (.var 1))) .return_
}

#eval evalFun [] negFun 10 [.int 5]    ()
#eval evalFun [] negFun 10 [.int (-3)] ()

theorem elab_neg (x : Int) :
    evalFun [] negFun 10 [.int x] at () |= .pureOutput (· = .int (-x)) :=
  ⟨.int (-x), (), rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- F4: add — fn add(x: i32, y: i32) -> i32 { x + y }
-- ════════════════════════════════════════════════════════════════════════════

def addFun : LLBCFunDef := {
  name   := "add"
  params := [mkParam 1 (.int .I32) "x", mkParam 2 (.int .I32) "y"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "x",
             mkParam 2 (.int .I32) "y", mkLocal 3 (.int .I32)]
  retTy  := .int .I32
  body   :=
    .assign (.var 3) (.binOp .add (.copy (.var 1)) (.copy (.var 2)))
   (.assign (.var 0) (.use (.copy (.var 3)))
    .return_)
}

#eval evalFun [] addFun 10 [.int 3, .int 4]    ()
#eval evalFun [] addFun 10 [.int (-1), .int 1] ()

theorem elab_add (x y : Int)
    (h : IntBounds.minI32 ≤ x + y ∧ x + y ≤ IntBounds.maxI32) :
    evalFun [] addFun 10 [.int x, .int y] at () |= .pureOutput (· = .int (x + y)) := by
  refine ⟨.int (x + y), (), ?_, rfl⟩
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, addFun, mkParam, mkLocal]
  rw [if_pos h]
  rfl

/-- Derived: `add` never panics when sum is in i32 range. -/
theorem elab_add_nocrash (x y : Int)
    (h : IntBounds.minI32 ≤ x + y ∧ x + y ≤ IntBounds.maxI32) :
    evalFun [] addFun 10 [.int x, .int y] at () |= .nocrash :=
  sat_pureOutput_nocrash (elab_add x y h)

-- ════════════════════════════════════════════════════════════════════════════
-- F5: sub — fn sub(x: i32, y: i32) -> i32 { x - y }
-- ════════════════════════════════════════════════════════════════════════════

def subFun : LLBCFunDef := {
  name   := "sub"
  params := [mkParam 1 (.int .I32) "x", mkParam 2 (.int .I32) "y"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "x",
             mkParam 2 (.int .I32) "y", mkLocal 3 (.int .I32)]
  retTy  := .int .I32
  body   :=
    .assign (.var 3) (.binOp .sub (.copy (.var 1)) (.copy (.var 2)))
   (.assign (.var 0) (.use (.copy (.var 3)))
    .return_)
}

#eval evalFun [] subFun 10 [.int 7, .int 3] ()

theorem elab_sub (x y : Int)
    (h : IntBounds.minI32 ≤ x - y ∧ x - y ≤ IntBounds.maxI32) :
    evalFun [] subFun 10 [.int x, .int y] at () |= .pureOutput (· = .int (x - y)) := by
  refine ⟨.int (x - y), (), ?_, rfl⟩
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, subFun, mkParam, mkLocal]
  rw [if_pos h]
  rfl

-- ════════════════════════════════════════════════════════════════════════════
-- F6: max — fn max(a: i32, b: i32) -> i32 { if a >= b { a } else { b } }
-- ════════════════════════════════════════════════════════════════════════════

def maxFun : LLBCFunDef := {
  name   := "max"
  params := [mkParam 1 (.int .I32) "a", mkParam 2 (.int .I32) "b"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "a",
             mkParam 2 (.int .I32) "b", mkLocal 3 .bool_]
  retTy  := .int .I32
  body   :=
    .assign (.var 3) (.binOp .ge (.copy (.var 1)) (.copy (.var 2)))
   (.ite (.copy (.var 3))
      (.assign (.var 0) (.use (.copy (.var 1))) .return_)
      (.assign (.var 0) (.use (.copy (.var 2))) .return_))
}

#eval evalFun [] maxFun 10 [.int 5, .int 3] ()
#eval evalFun [] maxFun 10 [.int 2, .int 7] ()
#eval evalFun [] maxFun 10 [.int 4, .int 4] ()


theorem elab_max_ge (a b : Int) (h : a ≥ b) :
    evalFun [] maxFun 10 [.int a, .int b] at () |= .pureOutput (· = .int a) := by
  refine ⟨.int a, (), ?_, rfl⟩
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, maxFun, mkParam, mkLocal, decide_eq_true h]

theorem elab_max_lt (a b : Int) (h : a < b) :
    evalFun [] maxFun 10 [.int a, .int b] at () |= .pureOutput (· = .int b) := by
  refine ⟨.int b, (), ?_, rfl⟩
  have hf : decide (a ≥ b) = false := decide_eq_false (not_le.mpr h)
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, maxFun, mkParam, mkLocal, hf]

/-- Derived (kernel-checked): `max` returns one of its two inputs. -/
theorem elab_max_either (a b : Int) :
    evalFun [] maxFun 10 [.int a, .int b] at () |=
      .pureOutput (fun v => v = .int a ∨ v = .int b) := by
  rcases Classical.em (a ≥ b) with h | h
  · exact sat_pureOutput_mono (fun _ hv => Or.inl hv) (elab_max_ge a b h)
  · exact sat_pureOutput_mono (fun _ hv => Or.inr hv) (elab_max_lt a b (not_le.mp h))

/-- Derived (kernel-checked): `max` result dominates both inputs. -/
theorem elab_max_ge_both (a b : Int) :
    evalFun [] maxFun 10 [.int a, .int b] at () |=
      .pureOutput (fun v => ∃ n : Int, v = .int n ∧ n ≥ a ∧ n ≥ b) := by
  rcases Classical.em (a ≥ b) with h | h
  · exact sat_pureOutput_mono (fun v hv => ⟨a, hv, le_refl a, h⟩) (elab_max_ge a b h)
  · exact sat_pureOutput_mono
        (fun v hv => ⟨b, hv, le_of_lt (not_le.mp h), le_refl b⟩)
        (elab_max_lt a b (not_le.mp h))

-- ════════════════════════════════════════════════════════════════════════════
-- F7: abs — fn abs(x: i32) -> i32 { if x >= 0 { x } else { -x } }
-- ════════════════════════════════════════════════════════════════════════════

def absFun : LLBCFunDef := {
  name   := "abs"
  params := [mkParam 1 (.int .I32) "x"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "x", mkLocal 2 .bool_]
  retTy  := .int .I32
  body   :=
    .assign (.var 2) (.binOp .ge (.copy (.var 1)) (.const (.int 0 .I32)))
   (.ite (.copy (.var 2))
      (.assign (.var 0) (.use (.copy (.var 1))) .return_)
      (.assign (.var 0) (.unOp .neg (.copy (.var 1))) .return_))
}

#eval evalFun [] absFun 10 [.int 5]    ()
#eval evalFun [] absFun 10 [.int (-3)] ()
#eval evalFun [] absFun 10 [.int 0]    ()

theorem elab_abs_nonneg (x : Int) (h : x ≥ 0) :
    evalFun [] absFun 10 [.int x] at () |= .pureOutput (· = .int x) := by
  refine ⟨.int x, (), ?_, rfl⟩
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, absFun, mkParam, mkLocal, decide_eq_true h]

theorem elab_abs_neg (x : Int) (h : x < 0) :
    evalFun [] absFun 10 [.int x] at () |= .pureOutput (· = .int (-x)) := by
  refine ⟨.int (-x), (), ?_, rfl⟩
  have hf : decide (x ≥ 0) = false := decide_eq_false (not_le.mpr h)
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, absFun, mkParam, mkLocal, hf]

/-- Derived (kernel-checked): `abs` result is always ≥ 0. -/
theorem elab_abs_nonneg_result (x : Int) :
    evalFun [] absFun 10 [.int x] at () |= .pureOutput (fun v => ∃ n : Int, v = .int n ∧ n ≥ 0) := by
  rcases Classical.em (x ≥ 0) with h | h
  · exact sat_pureOutput_mono (fun v hv => ⟨x, hv, h⟩) (elab_abs_nonneg x h)
  · exact sat_pureOutput_mono
        (fun v hv => ⟨-x, hv, neg_nonneg.mpr (le_of_lt (not_le.mp h))⟩)
        (elab_abs_neg x (not_le.mp h))

-- ════════════════════════════════════════════════════════════════════════════
-- F8: is_zero — fn is_zero(x: i32) -> bool { x == 0 }
-- ════════════════════════════════════════════════════════════════════════════

def isZeroFun : LLBCFunDef := {
  name   := "is_zero"
  params := [mkParam 1 (.int .I32) "x"]
  locals := [mkLocal 0 .bool_, mkParam 1 (.int .I32) "x"]
  retTy  := .bool_
  body   :=
    .assign (.var 0) (.binOp .eq (.copy (.var 1)) (.const (.int 0 .I32)))
    .return_
}

#eval evalFun [] isZeroFun 10 [.int 0] ()
#eval evalFun [] isZeroFun 10 [.int 5] ()

theorem elab_isZero_zero :
    evalFun [] isZeroFun 10 [.int 0] at () |= .pureOutput (· = .bool_ true) :=
  ⟨.bool_ true, (), rfl, rfl⟩

theorem elab_isZero_nonzero (x : Int) (hx : x ≠ 0) :
    evalFun [] isZeroFun 10 [.int x] at () |= .pureOutput (· = .bool_ false) := by
  refine ⟨.bool_ false, (), ?_, rfl⟩
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, isZeroFun, mkParam, mkLocal]
  simp [show (x == (0 : Int)) = false from by simpa using hx]

-- ════════════════════════════════════════════════════════════════════════════
-- F9: not_gate — fn not_gate(b: bool) -> bool { !b }
-- ════════════════════════════════════════════════════════════════════════════

def notGateFun : LLBCFunDef := {
  name   := "not_gate"
  params := [mkParam 1 .bool_ "b"]
  locals := [mkLocal 0 .bool_, mkParam 1 .bool_ "b"]
  retTy  := .bool_
  body   := .assign (.var 0) (.unOp .not (.copy (.var 1))) .return_
}

theorem elab_not_gate (b : Bool) :
    evalFun [] notGateFun 10 [.bool_ b] at () |= .pureOutput (· = .bool_ !b) :=
  ⟨.bool_ !b, (), rfl, rfl⟩

/-- Derived: double negation is identity. -/
theorem elab_not_involution (b : Bool) :
    evalFun [] notGateFun 10 [.bool_ b] at () |=
      .pureOutput (fun v => evalFun [] notGateFun 10 [v] at () |=
                              .pureOutput (· = .bool_ b)) :=
  sat_pureOutput_mono
    (fun v hv => by subst hv; cases b <;> exact ⟨_, (), rfl, rfl⟩)
    (elab_not_gate b)

-- ════════════════════════════════════════════════════════════════════════════
-- F10: clamp — fn clamp(x: i32, lo: i32, hi: i32) -> i32
--              { if x < lo { lo } else if x > hi { hi } else { x } }
-- ════════════════════════════════════════════════════════════════════════════

def clampFun : LLBCFunDef := {
  name   := "clamp"
  params := [mkParam 1 (.int .I32) "x", mkParam 2 (.int .I32) "lo",
             mkParam 3 (.int .I32) "hi"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "x",
             mkParam 2 (.int .I32) "lo", mkParam 3 (.int .I32) "hi",
             mkLocal 4 .bool_]
  retTy  := .int .I32
  body   :=
    -- if x < lo:
    .assign (.var 4) (.binOp .lt (.copy (.var 1)) (.copy (.var 2)))
   (.ite (.copy (.var 4))
      (.assign (.var 0) (.use (.copy (.var 2))) .return_)  -- return lo
      -- else if x > hi:
     (.assign (.var 4) (.binOp .gt (.copy (.var 1)) (.copy (.var 3)))
      (.ite (.copy (.var 4))
         (.assign (.var 0) (.use (.copy (.var 3))) .return_)  -- return hi
         (.assign (.var 0) (.use (.copy (.var 1))) .return_))))  -- return x
}

#eval evalFun [] clampFun 10 [.int 3, .int 1, .int 5]   ()   -- 3
#eval evalFun [] clampFun 10 [.int (-2), .int 1, .int 5] ()  -- 1
#eval evalFun [] clampFun 10 [.int 7, .int 1, .int 5]   ()   -- 5

theorem elab_clamp_mid (x lo hi : Int) (h1 : lo ≤ x) (h2 : x ≤ hi) :
    evalFun [] clampFun 10 [.int x, .int lo, .int hi] at () |= .pureOutput (· = .int x) := by
  refine ⟨.int x, (), ?_, rfl⟩
  have hlt : decide (x < lo) = false := decide_eq_false (not_lt.mpr h1)
  have hgt : decide (x > hi) = false := decide_eq_false (not_lt.mpr h2)
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, clampFun, mkParam, mkLocal, hlt, hgt]

theorem elab_clamp_lo (x lo hi : Int) (h : x < lo) :
    evalFun [] clampFun 10 [.int x, .int lo, .int hi] at () |= .pureOutput (· = .int lo) := by
  refine ⟨.int lo, (), ?_, rfl⟩
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, clampFun, mkParam, mkLocal, decide_eq_true h]

theorem elab_clamp_hi (x lo hi : Int) (h1 : lo ≤ x) (h2 : hi < x) :
    evalFun [] clampFun 10 [.int x, .int lo, .int hi] at () |= .pureOutput (· = .int hi) := by
  refine ⟨.int hi, (), ?_, rfl⟩
  have hlt : decide (x < lo) = false := decide_eq_false (not_lt.mpr h1)
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add, clampFun, mkParam, mkLocal, hlt, decide_eq_true h2]

/-- Derived (kernel-checked): clamp result is always in [lo, hi]. -/
theorem elab_clamp_inrange (x lo hi : Int) (h : lo ≤ hi) :
    evalFun [] clampFun 10 [.int x, .int lo, .int hi] at () |=
      .pureOutput (fun v => ∃ n : Int, v = .int n ∧ lo ≤ n ∧ n ≤ hi) := by
  rcases lt_trichotomy x lo with hlt | heq | hgt
  · exact sat_pureOutput_mono (fun v hv => ⟨lo, hv, le_refl lo, h⟩)
        (elab_clamp_lo x lo hi hlt)
  · rw [heq]
    exact sat_pureOutput_mono (fun v hv => ⟨lo, hv, le_refl lo, h⟩)
        (elab_clamp_mid lo lo hi (le_refl lo) h)
  · rcases Classical.em (x ≤ hi) with hle | hlt
    · exact sat_pureOutput_mono (fun v hv => ⟨x, hv, le_of_lt hgt, hle⟩)
          (elab_clamp_mid x lo hi (le_of_lt hgt) hle)
    · exact sat_pureOutput_mono (fun v hv => ⟨hi, hv, h, le_refl hi⟩)
          (elab_clamp_hi x lo hi (le_of_lt hgt) (not_le.mp hlt))

-- ════════════════════════════════════════════════════════════════════════════
-- F11: sum_to — while loop: Σ(0..n-1)
-- ════════════════════════════════════════════════════════════════════════════
/-
  Rust:  fn sum_to(n: i32) -> i32 { let mut s=0; let mut i=0;
          while i < n { s += i; i += 1; } s }
  locals: [ret, n, s, i, cond, tmp]
-/
def sumToFun : LLBCFunDef := {
  name   := "sum_to"
  params := [mkParam 1 (.int .I32) "n"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "n",
             mkLocal 2 (.int .I32), mkLocal 3 (.int .I32),
             mkLocal 4 .bool_,      mkLocal 5 (.int .I32)]
  retTy  := .int .I32
  body   :=
    .assign (.var 2) (.use (.const (.int 0 .I32)))
   (.assign (.var 3) (.use (.const (.int 0 .I32)))
   (.seq
     (.loop
       (.assign (.var 4) (.binOp .lt (.copy (.var 3)) (.copy (.var 1)))
       (.ite (.copy (.var 4))
          (.assign (.var 5) (.binOp .add (.copy (.var 2)) (.copy (.var 3)))
          (.assign (.var 2) (.use (.copy (.var 5)))
          (.assign (.var 5) (.binOp .add (.copy (.var 3)) (.const (.int 1 .I32)))
          (.assign (.var 3) (.use (.copy (.var 5)))
           .skip))))
          .break_)))
     (.assign (.var 0) (.use (.copy (.var 2)))
      .return_)))
}

#eval evalFun [] sumToFun 1000 [.int 5]  ()   -- 10
#eval evalFun [] sumToFun 1000 [.int 10] ()   -- 45
#eval evalFun [] sumToFun 1000 [.int 0]  ()   -- 0

-- Ground instances verified by rfl (kernel computes the loop)
theorem elab_sumTo_zero :
    evalFun [] sumToFun 1000 [.int 0] at () |= .pureOutput (· = .int 0) :=
  ⟨.int 0, (), rfl, rfl⟩

theorem elab_sumTo_one :
    evalFun [] sumToFun 1000 [.int 1] at () |= .pureOutput (· = .int 0) :=
  ⟨.int 0, (), rfl, rfl⟩

theorem elab_sumTo_five :
    evalFun [] sumToFun 1000 [.int 5] at () |= .pureOutput (· = .int 10) :=
  ⟨.int 10, (), rfl, rfl⟩

theorem elab_sumTo_ten :
    evalFun [] sumToFun 1000 [.int 10] at () |= .pureOutput (· = .int 45) :=
  ⟨.int 45, (), rfl, rfl⟩

/-- Derived: sum_to is crash-free for n=0 and n=10. -/
theorem elab_sumTo_nocrash_zero  : evalFun [] sumToFun 1000 [.int 0]  at () |= .nocrash :=
  sat_pureOutput_nocrash elab_sumTo_zero
theorem elab_sumTo_nocrash_ten   : evalFun [] sumToFun 1000 [.int 10] at () |= .nocrash :=
  sat_pureOutput_nocrash elab_sumTo_ten

-- ════════════════════════════════════════════════════════════════════════════
-- F12: factorial — while loop
-- ════════════════════════════════════════════════════════════════════════════

def factFun : LLBCFunDef := {
  name   := "fact"
  params := [mkParam 1 (.int .I32) "n"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "n",
             mkLocal 2 (.int .I32), mkLocal 3 (.int .I32),
             mkLocal 4 .bool_,      mkLocal 5 (.int .I32)]
  retTy  := .int .I32
  body   :=
    .assign (.var 2) (.use (.const (.int 1 .I32)))
   (.assign (.var 3) (.use (.const (.int 1 .I32)))
   (.seq
     (.loop
       (.assign (.var 4) (.binOp .le (.copy (.var 3)) (.copy (.var 1)))
       (.ite (.copy (.var 4))
          (.assign (.var 5) (.binOp .mul (.copy (.var 2)) (.copy (.var 3)))
          (.assign (.var 2) (.use (.copy (.var 5)))
          (.assign (.var 5) (.binOp .add (.copy (.var 3)) (.const (.int 1 .I32)))
          (.assign (.var 3) (.use (.copy (.var 5)))
           .skip))))
          .break_)))
   (.assign (.var 0) (.use (.copy (.var 2)))
    .return_)))
}

#eval evalFun [] factFun 10000 [.int 0]  ()    -- 1
#eval evalFun [] factFun 10000 [.int 5]  ()    -- 120
#eval evalFun [] factFun 10000 [.int 10] ()    -- 3628800

theorem elab_fact_zero :
    evalFun [] factFun 10000 [.int 0] at () |= .pureOutput (· = .int 1) :=
  ⟨.int 1, (), rfl, rfl⟩

theorem elab_fact_one :
    evalFun [] factFun 10000 [.int 1] at () |= .pureOutput (· = .int 1) :=
  ⟨.int 1, (), rfl, rfl⟩

theorem elab_fact_five :
    evalFun [] factFun 10000 [.int 5] at () |= .pureOutput (· = .int 120) :=
  ⟨.int 120, (), rfl, rfl⟩

theorem elab_fact_ten :
    evalFun [] factFun 10000 [.int 10] at () |= .pureOutput (· = .int 3628800) :=
  ⟨.int 3628800, (), rfl, rfl⟩

theorem elab_fact_nocrash_five :
    evalFun [] factFun 10000 [.int 5] at () |= .nocrash :=
  sat_pureOutput_nocrash elab_fact_five

-- ════════════════════════════════════════════════════════════════════════════
-- F13: mul — fn mul(x: i32, y: i32) -> i32 { x * y }
-- ════════════════════════════════════════════════════════════════════════════

def mulFun : LLBCFunDef := {
  name   := "mul"
  params := [mkParam 1 (.int .I32) "x", mkParam 2 (.int .I32) "y"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "x",
             mkParam 2 (.int .I32) "y", mkLocal 3 (.int .I32)]
  retTy  := .int .I32
  body   :=
    .assign (.var 3) (.binOp .mul (.copy (.var 1)) (.copy (.var 2)))
   (.assign (.var 0) (.use (.copy (.var 3)))
    .return_)
}

#eval evalFun [] mulFun 10 [.int 6, .int 7]    ()   -- 42
#eval evalFun [] mulFun 10 [.int (-3), .int 4] ()   -- -12

theorem elab_mul (x y : Int)
    (h : IntBounds.minI32 ≤ x * y ∧ x * y ≤ IntBounds.maxI32) :
    evalFun [] mulFun 10 [.int x, .int y] at () |= .pureOutput (· = .int (x * y)) := by
  refine ⟨.int (x * y), (), ?_, rfl⟩
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add,
             mulFun, mkParam, mkLocal]
  rw [if_pos h]
  rfl

/-- Derived: mul never panics when product is in i32 range. -/
theorem elab_mul_nocrash (x y : Int)
    (h : IntBounds.minI32 ≤ x * y ∧ x * y ≤ IntBounds.maxI32) :
    evalFun [] mulFun 10 [.int x, .int y] at () |= .nocrash :=
  sat_pureOutput_nocrash (elab_mul x y h)

-- ════════════════════════════════════════════════════════════════════════════
-- F14: min — fn min(a: i32, b: i32) -> i32 { if a <= b { a } else { b } }
-- ════════════════════════════════════════════════════════════════════════════

def minFun : LLBCFunDef := {
  name   := "min"
  params := [mkParam 1 (.int .I32) "a", mkParam 2 (.int .I32) "b"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "a",
             mkParam 2 (.int .I32) "b", mkLocal 3 .bool_]
  retTy  := .int .I32
  body   :=
    .assign (.var 3) (.binOp .le (.copy (.var 1)) (.copy (.var 2)))
   (.ite (.copy (.var 3))
      (.assign (.var 0) (.use (.copy (.var 1))) .return_)
      (.assign (.var 0) (.use (.copy (.var 2))) .return_))
}

#eval evalFun [] minFun 10 [.int 3, .int 7] ()   -- 3
#eval evalFun [] minFun 10 [.int 9, .int 2] ()   -- 2
#eval evalFun [] minFun 10 [.int 5, .int 5] ()   -- 5

theorem elab_min_le (a b : Int) (h : a ≤ b) :
    evalFun [] minFun 10 [.int a, .int b] at () |= .pureOutput (· = .int a) := by
  refine ⟨.int a, (), ?_, rfl⟩
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add,
             minFun, mkParam, mkLocal, decide_eq_true h]

theorem elab_min_gt (a b : Int) (h : a > b) :
    evalFun [] minFun 10 [.int a, .int b] at () |= .pureOutput (· = .int b) := by
  refine ⟨.int b, (), ?_, rfl⟩
  have hf : decide (a ≤ b) = false := decide_eq_false (not_le.mpr h)
  simp only [evalFun, evalFunBody, evalStmtFuel, buildLocals, evalRValuePure,
             evalBinOpPure, evalOperandPure, evalPlacePure, writePlacePure, evalLit,
             List.replicate, List.foldl, List.zipWith, List.set, List.find?,
             beq_self_eq_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
             List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.zero_add,
             minFun, mkParam, mkLocal, hf]

/-- Derived (kernel-checked): min returns one of its two inputs. -/
theorem elab_min_either (a b : Int) :
    evalFun [] minFun 10 [.int a, .int b] at () |=
      .pureOutput (fun v => v = .int a ∨ v = .int b) := by
  rcases Classical.em (a ≤ b) with h | h
  · exact sat_pureOutput_mono (fun _ hv => Or.inl hv) (elab_min_le a b h)
  · exact sat_pureOutput_mono (fun _ hv => Or.inr hv) (elab_min_gt a b (not_le.mp h))

/-- Derived (kernel-checked): min result is ≤ both inputs. -/
theorem elab_min_le_both (a b : Int) :
    evalFun [] minFun 10 [.int a, .int b] at () |=
      .pureOutput (fun v => ∃ n : Int, v = .int n ∧ n ≤ a ∧ n ≤ b) := by
  rcases Classical.em (a ≤ b) with h | h
  · exact sat_pureOutput_mono (fun v hv => ⟨a, hv, le_refl a, h⟩) (elab_min_le a b h)
  · exact sat_pureOutput_mono
        (fun v hv => ⟨b, hv, le_of_lt (not_le.mp h), le_refl b⟩)
        (elab_min_gt a b (not_le.mp h))

-- ════════════════════════════════════════════════════════════════════════════
-- F15: square — cross-function call: fn square(x: i32) -> i32 { mul(x, x) }
-- ════════════════════════════════════════════════════════════════════════════

def squareFun : LLBCFunDef := {
  name   := "square"
  params := [mkParam 1 (.int .I32) "x"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "x"]
  retTy  := .int .I32
  body   := .call (.var 0) "mul" [.copy (.var 1), .copy (.var 1)] .return_
}

-- mulFun must be in the FunEnv for cross-function call resolution
#eval evalFun [mulFun] squareFun 10 [.int 5]    ()   -- 25
#eval evalFun [mulFun] squareFun 10 [.int (-4)] ()   -- 16
#eval evalFun [mulFun] squareFun 10 [.int 0]    ()   -- 0

-- Ground instances: kernel computes through the cross-function call by rfl
theorem elab_square_zero :
    evalFun [mulFun] squareFun 10 [.int 0] at () |= .pureOutput (· = .int 0) :=
  ⟨.int 0, (), rfl, rfl⟩

theorem elab_square_five :
    evalFun [mulFun] squareFun 10 [.int 5] at () |= .pureOutput (· = .int 25) :=
  ⟨.int 25, (), rfl, rfl⟩

theorem elab_square_neg4 :
    evalFun [mulFun] squareFun 10 [.int (-4)] at () |= .pureOutput (· = .int 16) :=
  ⟨.int 16, (), rfl, rfl⟩

/-- Derived: square(5) result is non-negative. -/
theorem elab_square_five_nonneg :
    evalFun [mulFun] squareFun 10 [.int 5] at () |=
      .pureOutput (fun v => ∃ n : Int, v = .int n ∧ n ≥ 0) :=
  sat_pureOutput_mono (fun v hv => ⟨25, hv, by norm_num⟩) elab_square_five

-- ════════════════════════════════════════════════════════════════════════════
-- F16: fib — fn fib(n: i32) -> i32 (iterative Fibonacci)
--   a=0, b=1; loop i<n: (a,b) := (b, a+b); i++; return a
-- ════════════════════════════════════════════════════════════════════════════
/-
  locals: ret(0), n(1), a(2), b(3), i(4), t(5), cond(6), tmp(7)
-/

def fibFun : LLBCFunDef := {
  name   := "fib"
  params := [mkParam 1 (.int .I32) "n"]
  locals := [mkLocal 0 (.int .I32), mkParam 1 (.int .I32) "n",
             mkLocal 2 (.int .I32), mkLocal 3 (.int .I32),
             mkLocal 4 (.int .I32), mkLocal 5 (.int .I32),
             mkLocal 6 .bool_,      mkLocal 7 (.int .I32)]
  retTy  := .int .I32
  body   :=
    .assign (.var 2) (.use (.const (.int 0 .I32)))
   (.assign (.var 3) (.use (.const (.int 1 .I32)))
   (.assign (.var 4) (.use (.const (.int 0 .I32)))
   (.seq
     (.loop
       (.assign (.var 6) (.binOp .lt (.copy (.var 4)) (.copy (.var 1)))
       (.ite (.copy (.var 6))
          (.assign (.var 5) (.use (.copy (.var 3)))              -- t = b
          (.assign (.var 7) (.binOp .add (.copy (.var 2)) (.copy (.var 3)))  -- tmp = a+b
          (.assign (.var 3) (.use (.copy (.var 7)))              -- b = tmp
          (.assign (.var 2) (.use (.copy (.var 5)))              -- a = t
          (.assign (.var 7) (.binOp .add (.copy (.var 4)) (.const (.int 1 .I32)))
          (.assign (.var 4) (.use (.copy (.var 7)))              -- i++
           .skip))))))
          .break_)))
     (.assign (.var 0) (.use (.copy (.var 2)))
      .return_))))
}

#eval evalFun [] fibFun 1000 [.int 0]  ()   -- 0
#eval evalFun [] fibFun 1000 [.int 1]  ()   -- 1
#eval evalFun [] fibFun 1000 [.int 5]  ()   -- 5
#eval evalFun [] fibFun 1000 [.int 10] ()   -- 55

-- Ground instances (kernel computes the loop by rfl)
theorem elab_fib_zero :
    evalFun [] fibFun 1000 [.int 0] at () |= .pureOutput (· = .int 0) :=
  ⟨.int 0, (), rfl, rfl⟩

theorem elab_fib_one :
    evalFun [] fibFun 1000 [.int 1] at () |= .pureOutput (· = .int 1) :=
  ⟨.int 1, (), rfl, rfl⟩

theorem elab_fib_two :
    evalFun [] fibFun 1000 [.int 2] at () |= .pureOutput (· = .int 1) :=
  ⟨.int 1, (), rfl, rfl⟩

theorem elab_fib_five :
    evalFun [] fibFun 1000 [.int 5] at () |= .pureOutput (· = .int 5) :=
  ⟨.int 5, (), rfl, rfl⟩

theorem elab_fib_ten :
    evalFun [] fibFun 1000 [.int 10] at () |= .pureOutput (· = .int 55) :=
  ⟨.int 55, (), rfl, rfl⟩

/-- Derived: fib is crash-free at n=10. -/
theorem elab_fib_nocrash_ten :
    evalFun [] fibFun 1000 [.int 10] at () |= .nocrash :=
  sat_pureOutput_nocrash elab_fib_ten

-- ════════════════════════════════════════════════════════════════════════════
-- Theorem inventory  (50 theorems, 0 sorry)
-- ════════════════════════════════════════════════════════════════════════════
/-
  | #   | Function      | Property                    | Method           |
  |-----|---------------|-----------------------------|------------------|
  | F1  | return42      | = 42                        | rfl ✓            |
  | F2  | id            | = x                         | rfl ✓            |
  | F3  | neg           | = -x                        | rfl ✓            |
  | F4  | add           | = x+y (in range)            | simp+rw(if) ✓   |
  | F4  | add           | nocrash                     | derived ✓        |
  | F5  | sub           | = x-y (in range)            | simp+rw(if) ✓   |
  | F6  | max(a≥b)      | = a                         | simp+decide ✓    |
  | F6  | max(a<b)      | = b                         | simp+decide ✓    |
  | F6  | max           | ∈ {a,b}                     | Classical.em ✓   |
  | F6  | max           | ≥ both                      | Classical.em ✓   |
  | F7  | abs(x≥0)      | = x                         | simp+decide ✓    |
  | F7  | abs(x<0)      | = -x                        | simp+decide ✓    |
  | F7  | abs           | ≥ 0                         | Classical.em ✓   |
  | F8  | is_zero(0)    | = true                      | rfl ✓            |
  | F8  | is_zero(x≠0)  | = false                     | simp ✓           |
  | F9  | not_gate      | = !b                        | rfl ✓            |
  | F9  | not_not       | double-neg                  | derived ✓        |
  | F10 | clamp(mid)    | = x                         | simp+decide ✓    |
  | F10 | clamp(lo)     | = lo                        | simp+decide ✓    |
  | F10 | clamp(hi)     | = hi                        | simp+decide ✓    |
  | F10 | clamp         | in [lo,hi]                  | Classical.em ✓   |
  | F11 | sum_to(0)     | = 0                         | rfl ✓            |
  | F11 | sum_to(1)     | = 0                         | rfl ✓            |
  | F11 | sum_to(5)     | = 10                        | rfl ✓            |
  | F11 | sum_to(10)    | = 45                        | rfl ✓            |
  | F11 | sum_to(0,10)  | nocrash                     | derived ✓        |
  | F12 | fact(0)       | = 1                         | rfl ✓            |
  | F12 | fact(1)       | = 1                         | rfl ✓            |
  | F12 | fact(5)       | = 120                       | rfl ✓            |
  | F12 | fact(10)      | = 3628800                   | rfl ✓            |
  | F12 | fact(5)       | nocrash                     | derived ✓        |

  All 30 theorems are kernel-checked.  Zero sorry.
-/

#check @elab_return42
#check @elab_id
#check @elab_neg
#check @elab_add
#check @elab_add_nocrash
#check @elab_max_ge
#check @elab_max_lt
#check @elab_max_either
#check @elab_max_ge_both
#check @elab_abs_nonneg
#check @elab_abs_neg
#check @elab_abs_nonneg_result
#check @elab_isZero_zero
#check @elab_isZero_nonzero
#check @elab_not_gate
#check @elab_not_involution
#check @elab_clamp_mid
#check @elab_clamp_lo
#check @elab_clamp_hi
#check @elab_clamp_inrange
#check @elab_sumTo_five
#check @elab_sumTo_ten
#check @elab_fact_five
#check @elab_fact_ten

end LeanPlVerify.LLBC.Spec
