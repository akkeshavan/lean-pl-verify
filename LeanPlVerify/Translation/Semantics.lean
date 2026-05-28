/-
  Translation/Semantics.lean

  Relational big-step operational semantics for the LLBC interpreter.

  This module defines the GROUND TRUTH for what LLBC programs mean,
  independently of the fuel-based interpreter in Translation/Elaborator.lean.

  All runtime types (Value, Locals, FunEnv, Signal) are shared with the
  elaborator — no duplicate definitions.

  Structure:
    · EvalPlace   — big-step for place reads
    · EvalOperand — big-step for operand reads
    · EvalRValue  — big-step for r-value evaluation
    · EvalWrite   — big-step for place writes
    · EvalStmt    — big-step for statement execution
    · EvalFun     — top-level function evaluation

  These inductive relations are the semantic specification against which
  the interpreter is proved sound (Elaborator → Semantics) in Adequacy.lean.

  Design notes:
  · All runtime types are imported from Elaborator.lean — single source of truth.
  · Panics are modelled by *absence* of a derivation.
  · Loops are handled by loop_cont / loop_break / loop_return rules so the
    relation stays inductive (no coinduction needed).
  · EvalWrite covers only `.var` writes, matching `writePlacePure`.
  · `evalBinOpSem` wraps `evalBinOpPure` (Option vs Except), keeping the
    relational spec independent of error representation.
  · Switch arms use `litMatchesValue` (same predicate as the interpreter)
    for a transparent adequacy proof.
-/

import Mathlib.Tactic
import LeanPlVerify.Translation.Elaborator

namespace LeanPlVerify.LLBC.Sem

open LeanPlVerify LeanPlVerify.LLBC

-- ── Binary operation (Option-valued, for relational spec) ─────────────────────

/-- Option-returning binary-operation semantics.
    `evalBinOpSem op lv rv = some v`  iff  `evalBinOpPure op lv rv = Except.ok v`.
    This wrapping isolates the relational spec from the `Except` error type. -/
def evalBinOpSem (op : BinOp) (lv rv : Value) : Option Value :=
  match evalBinOpPure op lv rv with
  | Except.ok v    => some v
  | Except.error _ => none

-- ── Place evaluation (big-step relation) ──────────────────────────────────────

/-- `EvalPlace s p v` : reading place `p` in locals `s` yields value `v`. -/
inductive EvalPlace (s : Locals) : LLBCPlace → Value → Prop where
  | var {id v} :
      s[id]? = some v →
      EvalPlace s (.var id) v
  | deref {p v} :
      EvalPlace s p v →
      EvalPlace s (.deref p) v
  | field_tuple {p idx fs v} :
      EvalPlace s p (.tuple fs) →
      fs[idx]? = some v →
      EvalPlace s (.field p idx) v
  | field_adt {p idx tag fs v} :
      EvalPlace s p (.adt tag fs) →
      fs[idx]? = some v →
      EvalPlace s (.field p idx) v
  | index_ok {p iVar fs n v} :
      EvalPlace s p (.tuple fs) →
      s[iVar]? = some (.uint n) →
      fs[n]? = some v →
      EvalPlace s (.index p iVar) v
  | downcast {p variant v} :
      EvalPlace s p v →
      EvalPlace s (.downcast p variant) v

-- ── Operand evaluation ────────────────────────────────────────────────────────

/-- `EvalOperand s op v` : operand `op` in locals `s` yields value `v`. -/
inductive EvalOperand (s : Locals) : LLBCOperand → Value → Prop where
  | copy  {p v} : EvalPlace s p v → EvalOperand s (.copy p) v
  | move_ {p v} : EvalPlace s p v → EvalOperand s (.move_ p) v
  | const {l}   : EvalOperand s (.const l) (evalLit l)

-- ── R-value evaluation ────────────────────────────────────────────────────────

/-- `EvalRValue s rv v` : r-value `rv` in locals `s` evaluates to value `v`. -/
inductive EvalRValue (s : Locals) : LLBCRValue → Value → Prop where
  | use {op v} :
      EvalOperand s op v →
      EvalRValue s (.use op) v
  | ref {p v} :
      EvalPlace s p v →
      EvalRValue s (.ref p .Mut) v
  | ref_shared {p v} :
      EvalPlace s p v →
      EvalRValue s (.ref p .Shared) v
  | binOp {op l r lv rv v} :
      EvalOperand s l lv →
      EvalOperand s r rv →
      evalBinOpSem op lv rv = some v →
      EvalRValue s (.binOp op l r) v
  | unOp_not {x b} :
      EvalOperand s x (.bool_ b) →
      EvalRValue s (.unOp .not x) (.bool_ !b)
  | unOp_neg {x n} :
      EvalOperand s x (.int n) →
      EvalRValue s (.unOp .neg x) (.int (-n))
  | unOp_cast {ty x v} :
      EvalOperand s x v →
      EvalRValue s (.unOp (.cast ty) x) v
  | aggregate {kind flds vs} :
      List.Forall₂ (EvalOperand s) flds vs →
      EvalRValue s (.aggregate kind flds) (.tuple vs)
  | discriminant {p tag fields} :
      EvalPlace s p (.adt tag fields) →
      EvalRValue s (.discriminant p) (.uint tag)

-- ── Write evaluation ──────────────────────────────────────────────────────────

/-- `EvalWrite s dst v s'` : writing value `v` to place `dst` in locals `s`
    produces updated locals `s'`.
    Currently only variable writes are modelled, matching `writePlacePure`. -/
inductive EvalWrite (s : Locals) : LLBCPlace → Value → Locals → Prop where
  | var {id v} :
      EvalWrite s (.var id) v (s.set id v)

-- ── Statement evaluation (big-step relation) ──────────────────────────────────

/--
  `EvalStmt env stmt s sig s'` :
  executing `stmt` in environment `env` starting from locals `s`
  terminates with signal `sig` and final locals `s'`.

  Panics are modelled by *absence* of a derivation (no rule for `.panic`).
  Loops are structurally finite via loop_break / loop_return / loop_cont.
-/
inductive EvalStmt (env : FunEnv) : LLBCStmt → Locals → Signal → Locals → Prop where

  | skip {s} :
      EvalStmt env .skip s .next s

  | return_ {s} :
      EvalStmt env .return_ s .return_ s

  | break_ {s} :
      EvalStmt env .break_ s .break_ s

  | continue_ {s} :
      EvalStmt env .continue_ s .next s

  | assign {dst rv k v s s' sig s''} :
      EvalRValue s rv v →
      EvalWrite s dst v s' →
      EvalStmt env k s' sig s'' →
      EvalStmt env (.assign dst rv k) s sig s''

  | seq_next {s1 s2 s s' sig s''} :
      EvalStmt env s1 s .next s' →
      EvalStmt env s2 s' sig s'' →
      EvalStmt env (.seq s1 s2) s sig s''

  | seq_abort {s1 s2 s sig s'} :
      EvalStmt env s1 s sig s' →
      sig ≠ .next →
      EvalStmt env (.seq s1 s2) s sig s'

  | ite_true {cond thenB elseB s sig s'} :
      EvalOperand s cond (.bool_ true) →
      EvalStmt env thenB s sig s' →
      EvalStmt env (.ite cond thenB elseB) s sig s'

  | ite_false {cond thenB elseB s sig s'} :
      EvalOperand s cond (.bool_ false) →
      EvalStmt env elseB s sig s' →
      EvalStmt env (.ite cond thenB elseB) s sig s'

  | loop_break {body s s'} :
      EvalStmt env body s .break_ s' →
      EvalStmt env (.loop body) s .next s'

  | loop_return {body s s'} :
      EvalStmt env body s .return_ s' →
      EvalStmt env (.loop body) s .return_ s'

  | loop_cont {body s s' sig s''} :
      EvalStmt env body s .next s' →
      EvalStmt env (.loop body) s' sig s'' →
      EvalStmt env (.loop body) s sig s''

  | switch_match {op arms default_ s v lit arm sig s'} :
      EvalOperand s op v →
      arms.find? (fun p => litMatchesValue p.1 v) = some (lit, arm) →
      EvalStmt env arm s sig s' →
      EvalStmt env (.switchInt op arms default_) s sig s'

  | switch_default {op arms default_ s v sig s'} :
      EvalOperand s op v →
      arms.find? (fun p => litMatchesValue p.1 v) = none →
      EvalStmt env default_ s sig s' →
      EvalStmt env (.switchInt op arms default_) s sig s'

  | call {dst fname argOps k args f sig_callee v s s_callee s' sig s''} :
      List.Forall₂ (EvalOperand s) argOps args →
      env.find? (fun f => f.name == fname) = some f →
      EvalStmt env f.body (buildLocals f args) sig_callee s_callee →
      s_callee[0]? = some v →
      EvalWrite s dst v s' →
      EvalStmt env k s' sig s'' →
      EvalStmt env (.call dst fname argOps k) s sig s''

-- ── Top-level function evaluation ────────────────────────────────────────────

/--
  `EvalFun env f args v` : calling function `f` (in environment `env`) with
  arguments `args` terminates with return value `v` (read from locals[0]).
-/
def EvalFun (env : FunEnv) (f : LLBCFunDef) (args : List Value) (v : Value) : Prop :=
  ∃ s' sig,
    EvalStmt (f :: env) f.body (buildLocals f args) sig s' ∧
    s'[0]? = some v

end LeanPlVerify.LLBC.Sem
