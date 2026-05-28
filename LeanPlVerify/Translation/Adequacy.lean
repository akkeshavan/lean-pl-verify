/-
  Translation/Adequacy.lean

  Soundness of the fuel-based LLBC interpreter with respect to the
  relational big-step semantics in Semantics.lean.

  Main theorem (§7):
    evalStmtFuel_sound :
      evalStmtFuel env n stmt s = Except.ok (sig, s') →
      EvalStmt env stmt s sig s'

  All theorems fully proved — 0 sorry.
-/

import Mathlib.Tactic
import LeanPlVerify.Translation.Semantics

namespace LeanPlVerify.LLBC.Adequacy

open LeanPlVerify LeanPlVerify.LLBC LeanPlVerify.LLBC.Sem

-- ── §1  Place soundness ────────────────────────────────────────────────────────

theorem evalPlacePure_sound {s : Locals} {p : LLBCPlace} {v : Value}
    (h : evalPlacePure p s = Except.ok v) : EvalPlace s p v := by
  induction p generalizing v with
  | var id =>
    simp only [evalPlacePure] at h
    rcases hid : s[id]? with _ | val
    · simp [hid] at h
    · simp only [hid, Except.ok.injEq] at h
      exact EvalPlace.var (h ▸ hid)
  | deref p ih =>
    simp only [evalPlacePure] at h
    exact EvalPlace.deref (ih h)
  | field p idx ih =>
    simp only [evalPlacePure] at h
    rcases heval : evalPlacePure p s with _ | pv
    · simp [heval] at h
    · cases pv with
      | tuple fs =>
        simp only [heval] at h
        by_cases hlt : idx < fs.length
        · simp only [dif_pos hlt, Except.ok.injEq] at h
          exact EvalPlace.field_tuple (ih heval) (h ▸ List.getElem?_eq_getElem hlt)
        · simp [dif_neg hlt] at h
      | adt tag fs =>
        simp only [heval] at h
        by_cases hlt : idx < fs.length
        · simp only [dif_pos hlt, Except.ok.injEq] at h
          exact EvalPlace.field_adt (ih heval) (h ▸ List.getElem?_eq_getElem hlt)
        · simp [dif_neg hlt] at h
      | _ => simp [heval] at h
  | index p iVar ih =>
    simp only [evalPlacePure] at h
    split at h
    · -- Except.ok (.tuple fs), some (.uint n)
      rename_i fs n heval hidx
      split at h
      · rename_i hlt
        simp only [Except.ok.injEq] at h
        exact EvalPlace.index_ok (ih heval) hidx (h ▸ List.getElem?_eq_getElem hlt)
      · simp at h  -- out of bounds
    · simp at h  -- error arm
    · simp at h  -- catchall (non-tuple or non-uint)
  | downcast p _ ih =>
    simp only [evalPlacePure] at h
    exact EvalPlace.downcast (ih h)

-- ── §2  Operand soundness ──────────────────────────────────────────────────────

theorem evalOperandPure_sound {s : Locals} {op : LLBCOperand} {v : Value}
    (h : evalOperandPure op s = Except.ok v) : EvalOperand s op v := by
  cases op with
  | copy p  => exact EvalOperand.copy  (evalPlacePure_sound h)
  | move_ p => exact EvalOperand.move_ (evalPlacePure_sound h)
  | const l =>
    simp only [evalOperandPure, Except.ok.injEq] at h
    exact h ▸ EvalOperand.const

-- ── §3  mapM soundness (helper) ────────────────────────────────────────────────

/-- `mapM evalOperandPure` success implies pointwise `EvalOperand`. -/
theorem evalOperandsPure_sound {s : Locals} {ops : List LLBCOperand} {vs : List Value}
    (h : ops.mapM (fun op => evalOperandPure op s) = Except.ok vs) :
    List.Forall₂ (EvalOperand s) ops vs := by
  induction ops generalizing vs with
  | nil =>
    simp only [List.mapM_nil] at h
    change (Except.ok [] : Except PanicReason (List Value)) = Except.ok vs at h
    exact (Except.ok.inj h).symm ▸ List.Forall₂.nil
  | cons op ops ih =>
    rcases hop : evalOperandPure op s with _ | v
    · -- head operand fails
      rw [List.mapM_cons, hop] at h
      change (Except.error _ : Except PanicReason (List Value)) = Except.ok vs at h
      simp at h
    · rcases hops : ops.mapM (fun op => evalOperandPure op s) with _ | vs'
      · -- tail mapM fails
        rw [List.mapM_cons, hop, hops] at h
        change (Except.error _ : Except PanicReason (List Value)) = Except.ok vs at h
        simp at h
      · -- both succeed
        rw [List.mapM_cons, hop, hops] at h
        change (Except.ok (v :: vs') : Except PanicReason (List Value)) = Except.ok vs at h
        exact (Except.ok.inj h).symm ▸ List.Forall₂.cons (evalOperandPure_sound hop) (ih hops)

-- ── §4  BinOp bridge ──────────────────────────────────────────────────────────

theorem evalBinOpPure_to_sem {op : BinOp} {lv rv v : Value}
    (h : evalBinOpPure op lv rv = Except.ok v) :
    evalBinOpSem op lv rv = some v := by
  simp only [evalBinOpSem, h]

-- ── §5  RValue soundness ───────────────────────────────────────────────────────

theorem evalRValuePure_sound {s : Locals} {rv : LLBCRValue} {v : Value}
    (h : evalRValuePure rv s = Except.ok v) : EvalRValue s rv v := by
  cases rv with
  | use op => exact EvalRValue.use (evalOperandPure_sound h)
  | ref p m =>
    cases m with
    | Mut    => exact EvalRValue.ref       (evalPlacePure_sound h)
    | Shared => exact EvalRValue.ref_shared (evalPlacePure_sound h)
  | binOp op l r =>
    simp only [evalRValuePure] at h
    rcases hl : evalOperandPure l s with _ | lv
    · simp [hl] at h
    · rcases hr : evalOperandPure r s with _ | rv
      · simp [hl, hr] at h
      · simp only [hl, hr] at h
        exact EvalRValue.binOp (evalOperandPure_sound hl) (evalOperandPure_sound hr)
          (evalBinOpPure_to_sem h)
  | unOp op x =>
    simp only [evalRValuePure] at h
    rcases hx : evalOperandPure x s with _ | xv
    · simp [hx] at h
    · simp only [hx] at h
      cases op with
      | not =>
        cases xv with
        | bool_ b =>
          simp only [Except.ok.injEq] at h
          exact h ▸ EvalRValue.unOp_not (evalOperandPure_sound hx)
        | _ => simp at h
      | neg =>
        cases xv with
        | int n =>
          simp only [Except.ok.injEq] at h
          exact h ▸ EvalRValue.unOp_neg (evalOperandPure_sound hx)
        | _ => simp at h
      | cast ty =>
        simp only [Except.ok.injEq] at h
        exact h ▸ EvalRValue.unOp_cast (evalOperandPure_sound hx)
  | aggregate kind flds =>
    simp only [evalRValuePure] at h
    rcases hmap : flds.mapM (fun op => evalOperandPure op s) with _ | vs
    · simp [hmap] at h
    · simp only [hmap, Except.ok.injEq] at h
      exact h ▸ EvalRValue.aggregate (evalOperandsPure_sound hmap)
  | discriminant p =>
    simp only [evalRValuePure] at h
    rcases hp : evalPlacePure p s with _ | pv
    · simp [hp] at h
    · simp only [hp] at h
      cases pv with
      | adt tag fields =>
        simp only [Except.ok.injEq] at h
        exact h ▸ EvalRValue.discriminant (evalPlacePure_sound hp)
      | _ => simp at h

-- ── §6  Write soundness ────────────────────────────────────────────────────────

theorem writePlacePure_sound {s : Locals} {dst : LLBCPlace} {v : Value} {s' : Locals}
    (h : writePlacePure dst v s = Except.ok s') : EvalWrite s dst v s' := by
  cases dst with
  | var id =>
    simp only [writePlacePure, Except.ok.injEq] at h
    exact h ▸ EvalWrite.var
  | _ => simp [writePlacePure] at h

-- ── §7  Statement soundness ────────────────────────────────────────────────────

/-- Helper: extract a value from an `Except.ok` hypothesis. -/
private theorem except_ok_inj {α ε} {a b : α} {h : Except.ok a = (Except.ok b : Except ε α)} :
    a = b := Except.ok.inj h

theorem evalStmtFuel_sound (env : FunEnv) :
    ∀ (n : Nat) (stmt : LLBCStmt) (s : Locals) (sig : Signal) (s' : Locals),
    evalStmtFuel env n stmt s = Except.ok (sig, s') →
    EvalStmt env stmt s sig s' := by
  intro n
  induction n with
  | zero => intros; simp [evalStmtFuel] at *
  | succ n ih =>
    intro stmt s sig s' h
    match stmt with
    | .skip =>
      simp only [evalStmtFuel, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact EvalStmt.skip
    | .return_ =>
      simp only [evalStmtFuel, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact EvalStmt.return_
    | .break_ =>
      simp only [evalStmtFuel, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact EvalStmt.break_
    | .continue_ =>
      simp only [evalStmtFuel, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact EvalStmt.continue_
    | .panic _ =>
      simp [evalStmtFuel] at h
    | .assign dst rv k =>
      simp only [evalStmtFuel] at h
      rcases hrv : evalRValuePure rv s with _ | v
      · simp [hrv] at h
      · rcases hw : writePlacePure dst v s with _ | s_new
        · simp [hrv, hw] at h
        · simp only [hrv, hw] at h
          exact EvalStmt.assign (evalRValuePure_sound hrv) (writePlacePure_sound hw)
            (ih k s_new sig s' h)
    | .seq s1 s2 =>
      simp only [evalStmtFuel] at h
      rcases hs1 : evalStmtFuel env n s1 s with _ | ⟨sig1, s_mid⟩
      · simp [hs1] at h
      · simp only [hs1] at h
        cases sig1 with
        | next =>
          exact EvalStmt.seq_next (ih s1 s .next s_mid hs1) (ih s2 s_mid sig s' h)
        | break_ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact EvalStmt.seq_abort (ih s1 s .break_ s_mid hs1) (by decide)
        | return_ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact EvalStmt.seq_abort (ih s1 s .return_ s_mid hs1) (by decide)
    | .ite cond thenB elseB =>
      simp only [evalStmtFuel] at h
      rcases hcond : evalOperandPure cond s with _ | cv
      · simp [hcond] at h
      · simp only [hcond] at h
        cases cv with
        | bool_ b =>
          cases b with
          | true  =>
            exact EvalStmt.ite_true  (evalOperandPure_sound hcond) (ih thenB s sig s' h)
          | false =>
            exact EvalStmt.ite_false (evalOperandPure_sound hcond) (ih elseB s sig s' h)
        | _ => simp at h
    | .loop body =>
      simp only [evalStmtFuel] at h
      rcases hbody : evalStmtFuel env n body s with _ | ⟨sig1, s_mid⟩
      · simp [hbody] at h
      · simp only [hbody] at h
        cases sig1 with
        | break_ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact EvalStmt.loop_break (ih body s .break_ s_mid hbody)
        | return_ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact EvalStmt.loop_return (ih body s .return_ s_mid hbody)
        | next =>
          exact EvalStmt.loop_cont (ih body s .next s_mid hbody)
            (ih (.loop body) s_mid sig s' h)
    | .switchInt op arms default_ =>
      simp only [evalStmtFuel] at h
      -- Use split at h throughout to avoid lambda alpha-renaming issues
      rcases hop : evalOperandPure op s with _ | v
      · simp [hop] at h
      · simp only [hop] at h
        split at h
        · -- arms.find? ... = some (lit, arm)
          rename_i pair harms
          obtain ⟨lit, arm⟩ := pair
          exact EvalStmt.switch_match (evalOperandPure_sound hop) harms (ih arm s sig s' h)
        · -- arms.find? ... = none
          rename_i harms
          exact EvalStmt.switch_default (evalOperandPure_sound hop) harms
            (ih default_ s sig s' h)
    | .call dst fname argOps k =>
      -- Use split at h for each nested match to avoid substitution failures
      simp only [evalStmtFuel] at h
      split at h
      · simp at h  -- argOps.mapM = error
      · rename_i args hargs
        split at h
        · simp at h  -- env.find? = none
        · rename_i f hf
          split at h
          · simp at h  -- evalStmtFuel callee = error
          · rename_i sig_c s_c hcallee
            split at h
            · simp at h  -- s_c[0]? = none
            · rename_i v hret
              split at h
              · simp at h  -- writePlacePure = error
              · rename_i s_new hw
                exact EvalStmt.call (evalOperandsPure_sound hargs) hf
                  (ih f.body (buildLocals f args) sig_c s_c hcallee)
                  hret (writePlacePure_sound hw) (ih k s_new sig s' h)

-- ── §8  Fuel monotonicity ──────────────────────────────────────────────────────

/-- If fuel `n` suffices, then fuel `n+1` also suffices. -/
lemma evalStmtFuel_mono_one (env : FunEnv) :
    ∀ (n : Nat) (stmt : LLBCStmt) (s : Locals) (r : Signal × Locals),
    evalStmtFuel env n stmt s = Except.ok r →
    evalStmtFuel env (n + 1) stmt s = Except.ok r := by
  intro n; induction n with
  | zero => intros; simp [evalStmtFuel] at *
  | succ n ih =>
    intro stmt s r h
    match stmt with
    | .skip | .return_ | .break_ | .continue_ => exact h
    | .panic _ => simp [evalStmtFuel] at h
    | .assign dst rv k =>
      simp only [evalStmtFuel] at h ⊢
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i s' _
          exact ih k s' r h
    | .seq s1 s2 =>
      simp only [evalStmtFuel] at h ⊢
      rcases hs1 : evalStmtFuel env n s1 s with _ | ⟨sig1, s_mid⟩
      · simp [hs1] at h
      · cases sig1 with
        | next =>
          simp only [hs1] at h
          simp only [ih s1 s (.next, s_mid) hs1]
          exact ih s2 s_mid r h
        | break_ =>
          simp only [hs1] at h
          simp only [ih s1 s (.break_, s_mid) hs1]
          exact h
        | return_ =>
          simp only [hs1] at h
          simp only [ih s1 s (.return_, s_mid) hs1]
          exact h
    | .ite cond thenB elseB =>
      simp only [evalStmtFuel] at h ⊢
      rcases hcond : evalOperandPure cond s with _ | cv
      · simp [hcond] at h
      · simp only [hcond] at h ⊢
        cases cv with
        | bool_ b =>
          cases b with
          | true  => exact ih thenB s r h
          | false => exact ih elseB s r h
        | _ => simp at h
    | .loop body =>
      simp only [evalStmtFuel] at h ⊢
      rcases hbody : evalStmtFuel env n body s with _ | ⟨sig, s_mid⟩
      · simp [hbody] at h
      · cases sig with
        | next =>
          simp only [hbody] at h
          simp only [ih body s (.next, s_mid) hbody]
          exact ih (.loop body) s_mid r h
        | break_ =>
          simp only [hbody] at h
          simp only [ih body s (.break_, s_mid) hbody]
          exact h
        | return_ =>
          simp only [hbody] at h
          simp only [ih body s (.return_, s_mid) hbody]
          exact h
    | .switchInt op arms default_ =>
      simp only [evalStmtFuel] at h ⊢
      rcases hop : evalOperandPure op s with _ | v
      · simp [hop] at h
      · simp only [hop] at h ⊢
        rcases harms : arms.find? (fun pair => litMatchesValue pair.1 v) with _ | ⟨lit, arm⟩
        · simp only [harms] at h ⊢; exact ih default_ s r h
        · simp only [harms] at h ⊢; exact ih arm s r h
    | .call dst fname argOps k =>
      simp only [evalStmtFuel] at h ⊢
      rcases hargs : evalOperandsPure argOps s with _ | args
      · simp [hargs] at h
      · simp only [hargs] at h ⊢
        rcases hf : env.find? (fun f => f.name == fname) with _ | f
        · simp [hf] at h
        · simp only [hf] at h ⊢
          rcases hcallee : evalStmtFuel env n f.body (buildLocals f args) with _ | ⟨sig_c, s_c⟩
          · simp [hcallee] at h
          · simp only [hcallee] at h
            simp only [ih f.body (buildLocals f args) (sig_c, s_c) hcallee]
            rcases hret : s_c[0]? with _ | v
            · simp [hret] at h
            · simp only [hret] at h ⊢
              rcases hw : writePlacePure dst v s with _ | s_new
              · simp [hw] at h
              · simp only [hw] at h ⊢
                exact ih k s_new r h

/-- Monotonicity: fuel can always be increased. -/
lemma evalStmtFuel_mono (env : FunEnv) {n m : Nat} (hnm : n ≤ m) :
    ∀ (stmt : LLBCStmt) (s : Locals) (r : Signal × Locals),
    evalStmtFuel env n stmt s = Except.ok r →
    evalStmtFuel env m stmt s = Except.ok r := by
  intro stmt s r hr
  induction hnm with
  | refl => exact hr
  | @step k _ ih => exact evalStmtFuel_mono_one env k stmt s r ih

-- ── §9a  Sub-evaluator completeness ───────────────────────────────────────────

-- Note: for `induction h with`, each case binds: raw fields first, then IHs last.
theorem evalPlacePure_complete {s : Locals} {p : LLBCPlace} {v : Value}
    (h : EvalPlace s p v) : evalPlacePure p s = Except.ok v := by
  induction h with
  | var hid => simp only [evalPlacePure, hid]
  | deref _ ih => exact ih
  | field_tuple _ hidx ih =>
    simp only [evalPlacePure, ih]
    obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hidx
    rw [dif_pos hlt, hval]
  | field_adt _ hidx ih =>
    simp only [evalPlacePure, ih]
    obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hidx
    rw [dif_pos hlt, hval]
  | index_ok _ hidx hfs ih =>
    simp only [evalPlacePure, ih, hidx]
    obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hfs
    rw [dif_pos hlt, hval]
  | downcast _ ih => exact ih

theorem evalOperandPure_complete {s : Locals} {op : LLBCOperand} {v : Value}
    (h : EvalOperand s op v) : evalOperandPure op s = Except.ok v := by
  cases h with
  | copy  hp => exact evalPlacePure_complete hp
  | move_ hp => exact evalPlacePure_complete hp
  | const    => rfl

private theorem evalBinOpSem_to_pure' {op : BinOp} {lv rv v : Value}
    (h : evalBinOpSem op lv rv = some v) : evalBinOpPure op lv rv = Except.ok v := by
  simp only [evalBinOpSem] at h
  split at h
  · rename_i v' hpure; exact (Option.some.inj h) ▸ hpure
  · simp at h

theorem evalOperandsPure_complete {s : Locals} {ops : List LLBCOperand} {vs : List Value}
    (h : List.Forall₂ (EvalOperand s) ops vs) :
    ops.mapM (fun op => evalOperandPure op s) = Except.ok vs := by
  induction h with
  | nil => rfl
  | cons hop _ ih =>
    simp only [List.mapM_cons, evalOperandPure_complete hop, ih]; rfl

theorem evalRValuePure_complete {s : Locals} {rv : LLBCRValue} {v : Value}
    (h : EvalRValue s rv v) : evalRValuePure rv s = Except.ok v := by
  cases h with
  | use hop => exact evalOperandPure_complete hop
  | ref hp  => exact evalPlacePure_complete hp
  | ref_shared hp => exact evalPlacePure_complete hp
  | binOp hl hr hbinop =>
    simp only [evalRValuePure, evalOperandPure_complete hl, evalOperandPure_complete hr]
    exact evalBinOpSem_to_pure' hbinop
  | unOp_not hop => simp only [evalRValuePure, evalOperandPure_complete hop]
  | unOp_neg hop => simp only [evalRValuePure, evalOperandPure_complete hop]
  | unOp_cast hop => simp only [evalRValuePure, evalOperandPure_complete hop]
  | aggregate hflds => simp only [evalRValuePure, evalOperandsPure_complete hflds]
  | discriminant hp => simp only [evalRValuePure, evalPlacePure_complete hp]

theorem writePlacePure_complete {s : Locals} {dst : LLBCPlace} {v : Value} {s' : Locals}
    (h : EvalWrite s dst v s') : writePlacePure dst v s = Except.ok s' := by
  cases h with
  | var => rfl

-- ── §9  Completeness ───────────────────────────────────────────────────────────

theorem evalStmtFuel_complete (env : FunEnv) (stmt : LLBCStmt)
    (s : Locals) (sig : Signal) (s' : Locals)
    (hd : EvalStmt env stmt s sig s') :
    ∃ n : Nat, evalStmtFuel env n stmt s = Except.ok (sig, s') := by
  induction hd with
  -- Base cases: fuel = 1
  | skip     => exact ⟨1, rfl⟩
  | return_  => exact ⟨1, rfl⟩
  | break_   => exact ⟨1, rfl⟩
  | continue_ => exact ⟨1, rfl⟩
  -- assign: fuel = n_k + 1  (raw fields first, IH last)
  | assign hrv hw _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp only [evalStmtFuel,
      evalRValuePure_complete hrv, writePlacePure_complete hw, hn]⟩
  -- seq_next: fuel = max n1 n2 + 1
  | seq_next _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, ?_⟩
    have h1' := evalStmtFuel_mono env (Nat.le_max_left  n1 n2) _ _ _ h1
    have h2' := evalStmtFuel_mono env (Nat.le_max_right n1 n2) _ _ _ h2
    simp only [evalStmtFuel, h1', h2']
  -- seq_abort: fuel = n1 + 1 (simp closes via catch-all third arm)
  | seq_abort _ hne ih1 =>
    obtain ⟨n, hn⟩ := ih1
    exact ⟨n + 1, by simp only [evalStmtFuel, hn]⟩
  -- ite_true / ite_false: fuel = n + 1
  | ite_true hcond _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by
      simp only [evalStmtFuel, evalOperandPure_complete hcond, hn]⟩
  | ite_false hcond _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by
      simp only [evalStmtFuel, evalOperandPure_complete hcond, hn]⟩
  -- loop_break / loop_return: fuel = n_body + 1
  | loop_break _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp only [evalStmtFuel, hn]⟩
  | loop_return _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp only [evalStmtFuel, hn]⟩
  -- loop_cont: fuel = max n_body n_loop + 1
  | loop_cont _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, ?_⟩
    have h1' := evalStmtFuel_mono env (Nat.le_max_left  n1 n2) _ _ _ h1
    have h2' := evalStmtFuel_mono env (Nat.le_max_right n1 n2) _ _ _ h2
    simp only [evalStmtFuel, h1', h2']
  -- switch_match / switch_default: fuel = n + 1
  | switch_match hop harms _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by
      simp only [evalStmtFuel, evalOperandPure_complete hop, harms, hn]⟩
  | switch_default hop harms _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by
      simp only [evalStmtFuel, evalOperandPure_complete hop, harms, hn]⟩
  -- call: fuel = max n_callee n_k + 1
  | call hargs hf _ hret hw _ ih_callee ih_k =>
    obtain ⟨n1, h1⟩ := ih_callee
    obtain ⟨n2, h2⟩ := ih_k
    refine ⟨max n1 n2 + 1, ?_⟩
    have h1' := evalStmtFuel_mono env (Nat.le_max_left  n1 n2) _ _ _ h1
    have h2' := evalStmtFuel_mono env (Nat.le_max_right n1 n2) _ _ _ h2
    simp only [evalStmtFuel, evalOperandsPure, evalOperandsPure_complete hargs, hf, h1', hret,
      writePlacePure_complete hw, h2']

-- ── §10  Top-level corollary ──────────────────────────────────────────────────

theorem evalFunBody_sound (env : FunEnv) (f : LLBCFunDef)
    (fuel : Nat) (args : List Value) (v : Value)
    (h : evalFunBody (f :: env) f fuel args = Except.ok v) :
    EvalFun env f args v := by
  simp only [evalFunBody] at h
  rcases hrun : evalStmtFuel (f :: env) fuel f.body (buildLocals f args) with _ | ⟨sig, fl⟩
  · simp [hrun] at h
  · simp only [hrun] at h
    rcases hv : fl[0]? with _ | val
    · simp [hv] at h
    · simp only [hv, Except.ok.injEq] at h
      exact ⟨fl, sig,
        evalStmtFuel_sound (f :: env) fuel f.body (buildLocals f args) sig fl hrun,
        h ▸ hv⟩

end LeanPlVerify.LLBC.Adequacy
