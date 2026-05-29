/-
  Spec/Satisfies.lean

  Lemmas about the satisfaction relation for ProgramSpec.

  These lemmas are the "tactic library" for the verifier:
  they reduce proof goals about |= to simpler goals about
  the underlying Lean terms.
-/

import LeanPlVerify.Spec.ProgramSpec

namespace LeanPlVerify

-- ── Basic satisfaction lemmas ───────────────────────────────────────────────

/-- If `m` returns `v` from `init`, then it satisfies `pureOutput (· = v)`. -/
theorem sat_pureOutput_eq {σ α : Type} {m : RustM σ α} {init : σ}
    {v : α} {s' : σ}
    (h : m init = Except.ok (v, s')) :
    m at init |= .pureOutput (· = v) :=
  ⟨v, s', h, rfl⟩

/-- pureOutput is monotone: if P → Q, sat pureOutput P → sat pureOutput Q. -/
theorem sat_pureOutput_mono {σ α : Type} {m : RustM σ α} {init : σ}
    {P Q : α → Prop}
    (hPQ : ∀ v, P v → Q v)
    (h   : m at init |= .pureOutput P) :
    m at init |= .pureOutput Q := by
  obtain ⟨v, s', hok, hP⟩ := h
  exact ⟨v, s', hok, hPQ v hP⟩

/-- pureOutput implies nocrash. -/
theorem sat_pureOutput_nocrash {σ α : Type} {m : RustM σ α} {init : σ}
    {P : α → Prop}
    (h : m at init |= .pureOutput P) :
    m at init |= .nocrash := by
  obtain ⟨v, s', hok, _⟩ := h
  exact ⟨v, s', hok⟩

/-- `both` intro: prove each spec separately. -/
theorem sat_both_intro {σ α : Type} {m : RustM σ α} {init : σ}
    {s1 s2 : ProgramSpec σ α}
    (h1 : m at init |= s1) (h2 : m at init |= s2) :
    m at init |= .both s1 s2 :=
  ⟨h1, h2⟩

/-- `both` elim left. -/
theorem sat_both_left {σ α : Type} {m : RustM σ α} {init : σ}
    {s1 s2 : ProgramSpec σ α}
    (h : m at init |= .both s1 s2) :
    m at init |= s1 := h.1

/-- `both` elim right. -/
theorem sat_both_right {σ α : Type} {m : RustM σ α} {init : σ}
    {s1 s2 : ProgramSpec σ α}
    (h : m at init |= .both s1 s2) :
    m at init |= s2 := h.2

/-- Every computation satisfies `terminates`. -/
@[simp]
theorem sat_terminates {σ α : Type} {m : RustM σ α} {init : σ} :
    m at init |= .terminates :=
  trivial

/-- `withFuel` is transparent: satisfies inner spec. -/
theorem sat_withFuel {σ α : Type} {m : RustM σ α} {init : σ}
    {n : Nat} {s : ProgramSpec σ α}
    (h : m at init |= .withFuel n s) :
    m at init |= s := h

/-- `precond` intro: if P holds on init, prove inner spec. -/
theorem sat_precond_intro {σ α : Type} {m : RustM σ α} {init : σ}
    {P : σ → Prop} {s : ProgramSpec σ α}
    (_hp : P init)
    (h  : m at init |= s) :
    m at init |= .precond P s :=
  fun _ => h

-- ── pure computation lemmas ─────────────────────────────────────────────────

/-- `pure v` always satisfies `pureOutput (· = v)`. -/
@[simp]
theorem sat_pure {σ α : Type} {v : α} {init : σ} :
    (pure v : RustM σ α) at init |= .pureOutput (· = v) :=
  ⟨v, init, pure_ok, rfl⟩

/-- `pure v` satisfies `nocrash`. -/
@[simp]
theorem sat_pure_nocrash {σ α : Type} {v : α} {init : σ} :
    (pure v : RustM σ α) at init |= .nocrash :=
  ⟨v, init, pure_ok⟩

-- ── rpanic lemmas ────────────────────────────────────────────────────────────

/-- `rpanic` never satisfies `nocrash`. -/
theorem not_sat_panic_nocrash {σ α : Type} {r : PanicReason} {init : σ} :
    ¬ (rpanic r : RustM σ α) at init |= .nocrash := by
  intro ⟨_, _, h⟩
  simp [rpanic] at h

/-- `rpanic` never satisfies `pureOutput`. -/
theorem not_sat_panic_pureOutput {σ α : Type} {r : PanicReason} {init : σ}
    {P : α → Prop} :
    ¬ (rpanic r : RustM σ α) at init |= .pureOutput P := by
  intro ⟨_, _, h, _⟩
  simp [rpanic] at h

-- ── Sequential composition ──────────────────────────────────────────────────

-- Helper: (m >>= f) init reduces to f v s' when m init = Except.ok (v, s')
private theorem bind_eval {σ α β : Type}
    {m : RustM σ α} {f : α → RustM σ β} {init : σ} {v : α} {s' : σ}
    (hm : m init = Except.ok (v, s')) :
    (m >>= f) init = f v s' := by
  change m init >>= (fun p => f p.1 p.2) = _; rw [hm]; rfl

/-- Sequential composition for `pureOutput` specs. -/
theorem sat_bind_pureOutput {σ α β : Type}
    {m : RustM σ α} {f : α → RustM σ β}
    {init : σ} {v : α} {s' : σ} {P : β → Prop}
    (hm : m init = Except.ok (v, s'))
    (hf : f v at s' |= .pureOutput P) :
    (m >>= f) at init |= .pureOutput P := by
  obtain ⟨r, s'', hr, hP⟩ := hf
  exact ⟨r, s'', (bind_eval hm).trans hr, hP⟩

/-- Sequential composition for `nocrash` specs. -/
theorem sat_bind_nocrash {σ α β : Type}
    {m : RustM σ α} {f : α → RustM σ β}
    {init : σ} {v : α} {s' : σ}
    (hm : m init = Except.ok (v, s'))
    (hf : f v at s' |= .nocrash) :
    (m >>= f) at init |= .nocrash := by
  obtain ⟨r, s'', hr⟩ := hf
  exact ⟨r, s'', (bind_eval hm).trans hr⟩

/-- Sequential composition for `postcond` specs. -/
theorem sat_bind_postcond {σ α β : Type}
    {m : RustM σ α} {f : α → RustM σ β}
    {init : σ} {v : α} {s' : σ} {P : β → σ → Prop}
    (hm : m init = Except.ok (v, s'))
    (hf : f v at s' |= .postcond P) :
    (m >>= f) at init |= .postcond P := by
  obtain ⟨r, s'', hr, hP⟩ := hf
  exact ⟨r, s'', (bind_eval hm).trans hr, hP⟩

-- ── terminatesIn ────────────────────────────────────────────────────────────

/-- A computation satisfying `pureOutput P` also satisfies `terminatesIn n`
    for any declared fuel bound n. -/
theorem sat_terminatesIn_of_pureOutput {σ α : Type} {m : RustM σ α} {init : σ}
    {n : Nat} {P : α → Prop}
    (h : m at init |= .pureOutput P) :
    m at init |= .terminatesIn n := by
  obtain ⟨v, s', hok, _⟩ := h
  exact ⟨v, s', hok⟩

/-- A computation satisfying `nocrash` also satisfies `terminatesIn n`. -/
theorem sat_terminatesIn_of_nocrash {σ α : Type} {m : RustM σ α} {init : σ}
    {n : Nat}
    (h : m at init |= .nocrash) :
    m at init |= .terminatesIn n := h

-- ── agreesWith ──────────────────────────────────────────────────────────────

/-- Introduction rule: if both computations succeed and outputs are related by R,
    `agreesWith` holds. -/
theorem agreesWith_intro {σ α β : Type} {m1 : RustM σ α} {m2 : RustM σ β} {init : σ}
    {R : α → β → Prop} {v1 : α} {v2 : β} {s1' s2' : σ}
    (h1 : m1 init = Except.ok (v1, s1'))
    (h2 : m2 init = Except.ok (v2, s2'))
    (hR : R v1 v2) :
    ProgramSpec.agreesWith m1 m2 R init :=
  ⟨v1, s1', v2, s2', h1, h2, hR⟩

/-- If m1 agreesWith m2, then m1 does not crash. -/
theorem agreesWith_nocrash_left {σ α β : Type} {m1 : RustM σ α} {m2 : RustM σ β} {init : σ}
    {R : α → β → Prop}
    (h : ProgramSpec.agreesWith m1 m2 R init) :
    m1 at init |= .nocrash := by
  obtain ⟨v1, s1', _, _, h1, _, _⟩ := h
  exact ⟨v1, s1', h1⟩

/-- agreesWith follows from two independent pureOutput proofs sharing a common value. -/
theorem agreesWith_of_pureOutput {σ α β : Type} {m1 : RustM σ α} {m2 : RustM σ β}
    {init : σ} {R : α → β → Prop}
    (h1 : m1 at init |= .pureOutput (fun v1 => ∃ v2, R v1 v2 ∧ m2 init = Except.ok (v2, init)))
    : ProgramSpec.agreesWith m1 m2 R init := by
  obtain ⟨v1, s1', hok1, v2, hR, hok2⟩ := h1
  exact ⟨v1, s1', v2, init, hok1, hok2, hR⟩

end LeanPlVerify
