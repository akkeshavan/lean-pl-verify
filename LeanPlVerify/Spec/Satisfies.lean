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

end LeanPlVerify
