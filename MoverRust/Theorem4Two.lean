/-
  MoverRust / Theorem4Two — two-thread configurations and the reduction
  commutation primitives

  Toward Theorem 4 (Reduction) for a **two-thread** pool: this file sets
  up a concrete two-thread configuration and re-packages the `istep`-level
  commuting lemmas (Theorem4.lean) as commutations of the two-thread step
  relation.  Working with a fixed configuration makes "the other thread"
  concrete, so these come out clean (no list bookkeeping), and they are
  the swap rules the full trace-assembly induction would use.

  A configuration pairs the two threads' (phase, statement) with the
  shared store.  Thread `b : Bool` (`false = 0`, `true = 1`) steps via
  `Step F M b`; `CStep` is the preemptive union, `NStep` the cooperative
  version (a thread may step only when the *other* is parked).

  Provided here, all fully proved:
  ▸ `Cfg`, `Step`, `CStep`, `NStep`, `Wrong`, and step destructors;
  ▸ `right_comm_01` / `right_comm_10` — Lemma 7 at the two-thread level;
  ▸ `left_comm_01`  / `left_comm_10`  — Lemma 8 at the two-thread level.

  What remains for the full theorem is the trace induction that threads
  these swaps through an arbitrary interleaving (paper claim (1)), plus
  the post-commit-completion step (Lemma 9 of `Postcommit.lean` + an
  iterated diamond).  See the repository README.
-/
import MoverRust.Postcommit

namespace MoverRust
open Effect

/-- A two-thread instrumented configuration. -/
structure Cfg : Type where
  p0 : Effect
  s0 : Stmt
  p1 : Effect
  s1 : Stmt
  st : Store

namespace Cfg

/-- The `Tid` of thread `b`. -/
def tid (b : Bool) : Tid := if b then 1 else 0

theorem tid_ne : Cfg.tid false ≠ Cfg.tid true := by decide
theorem tid_ne' : Cfg.tid true ≠ Cfg.tid false := by decide

/-- Thread `b`'s (phase, statement). -/
def th (c : Cfg) (b : Bool) : Effect × Stmt := if b then (c.p1, c.s1) else (c.p0, c.s0)

/-- Thread `b` takes one instrumented step (the other thread's
    `(phase, statement)` is unchanged; only that thread and the store move). -/
def Step (F : FnTable) (M : MSpec) (b : Bool) (c c' : Cfg) : Prop :=
  ∃ p' s', istep F M (tid b) (c.th b).1 (c.th b).2 c.st p' s' c'.st ∧
    (bif b then c'.p1 = p' ∧ c'.s1 = s' ∧ c'.p0 = c.p0 ∧ c'.s0 = c.s0
     else c'.p0 = p' ∧ c'.s0 = s' ∧ c'.p1 = c.p1 ∧ c'.s1 = c.s1)

/-- Preemptive step: either thread. -/
def CStep (F : FnTable) (M : MSpec) (c c' : Cfg) : Prop := ∃ b, Step F M b c c'

/-- Thread `b` is parked (yielding / done / failed). -/
def ParkedB (c : Cfg) (b : Bool) : Prop := Parked (c.th b).2

/-- Cooperative step: thread `b` steps while the *other* is parked. -/
def NStep (F : FnTable) (M : MSpec) (c c' : Cfg) : Prop :=
  ∃ b, Step F M b c c' ∧ ParkedB c (!b)

/-- The configuration is wrong (some thread is about to run `wrong`). -/
def Wrong (c : Cfg) : Prop := IsWrong c.s0 ∨ IsWrong c.s1

theorem nstep_cstep {F M c c'} (h : NStep F M c c') : CStep F M c c' :=
  ⟨h.choose, h.choose_spec.1⟩

/-- `c` goes wrong under a given step relation. -/
def GoesWrong (Step : Cfg → Cfg → Prop) (c : Cfg) : Prop :=
  ∃ c', Multi Step c c' ∧ Wrong c'

/-! ### Basic destructuring of a step -/

/-- A `false`-step touches only thread 0 and the store. -/
theorem step_false {F M c c'} (h : Step F M false c c') :
    ∃ p' s', istep F M 0 c.p0 c.s0 c.st p' s' c'.st ∧
      c'.p0 = p' ∧ c'.s0 = s' ∧ c'.p1 = c.p1 ∧ c'.s1 = c.s1 := by
  obtain ⟨p', s', hstep, hfields⟩ := h
  simp only [th, tid] at hstep
  simp only [cond_false] at hfields
  exact ⟨p', s', hstep, hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2⟩

/-- A `true`-step touches only thread 1 and the store. -/
theorem step_true {F M c c'} (h : Step F M true c c') :
    ∃ p' s', istep F M 1 c.p1 c.s1 c.st p' s' c'.st ∧
      c'.p1 = p' ∧ c'.s1 = s' ∧ c'.p0 = c.p0 ∧ c'.s0 = c.s0 := by
  obtain ⟨p', s', hstep, hfields⟩ := h
  simp only [th, tid] at hstep
  simp only [cond_true] at hfields
  exact ⟨p', s', hstep, hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2⟩

/-- Build a `false`-step from an `istep` of thread 0. -/
theorem mk_step_false {F M} {c : Cfg} {p' s' σ'}
    (h : istep F M 0 c.p0 c.s0 c.st p' s' σ') :
    Step F M false c { c with p0 := p', s0 := s', st := σ' } :=
  ⟨p', s', by simpa [th, tid] using h, by simp [cond_false]⟩

theorem mk_step_true {F M} {c : Cfg} {p' s' σ'}
    (h : istep F M 1 c.p1 c.s1 c.st p' s' σ') :
    Step F M true c { c with p1 := p', s1 := s', st := σ' } :=
  ⟨p', s', by simpa [th, tid] using h, by simp [cond_true]⟩

/-! ### Two-thread commutation (from the `istep`-level lemmas) -/

/-- Right-commutation, `0`-then-`1`: a right-mover step of thread 0
    (ending in phase `R`, non-wrong) commutes right past a following
    non-wrong step of thread 1. -/
theorem right_comm_01 {F M} (hval : Valid M) {c c₁ c₂ : Cfg}
    (h1 : Step F M false c c₁) (hR : c₁.p0 = .R) (hnw0 : ¬ IsWrong c₁.s0)
    (h2 : Step F M true c₁ c₂) (hnw1 : ¬ IsWrong c₂.s1) :
    ∃ c₃, Step F M true c c₃ ∧ Step F M false c₃ c₂ := by
  obtain ⟨p0', s0', hi0, hp0, hs0, hp1e, hs1e⟩ := step_false h1
  obtain ⟨p1', s1', hi1, hp1, hs1, hp0e, hs0e⟩ := step_true h2
  have hpiR : p0' = .R := hp0 ▸ hR
  have hnwi : ¬ IsWrong s0' := hs0 ▸ hnw0
  have hnwj : ¬ IsWrong s1' := hs1 ▸ hnw1
  have hi1' : istep F M 1 c.p1 c.s1 c₁.st p1' s1' c₂.st := by
    rw [hp1e, hs1e] at hi1; exact hi1
  obtain ⟨σ₃, hj', hi'⟩ :=
    istep_right_comm hval (by decide) hi0 hpiR hnwi hi1' hnwj
  refine ⟨{ c with p1 := p1', s1 := s1', st := σ₃ }, mk_step_true hj',
    p0', s0', by simpa [th, tid] using hi', ?_⟩
  exact ⟨hp0e.trans hp0, hs0e.trans hs0, hp1, hs1⟩

/-- Right-commutation, `1`-then-`0` (mirror). -/
theorem right_comm_10 {F M} (hval : Valid M) {c c₁ c₂ : Cfg}
    (h1 : Step F M true c c₁) (hR : c₁.p1 = .R) (hnw1 : ¬ IsWrong c₁.s1)
    (h2 : Step F M false c₁ c₂) (hnw0 : ¬ IsWrong c₂.s0) :
    ∃ c₃, Step F M false c c₃ ∧ Step F M true c₃ c₂ := by
  obtain ⟨p1', s1', hi1, hp1, hs1, hp0e, hs0e⟩ := step_true h1
  obtain ⟨p0', s0', hi0, hp0, hs0, hp1e, hs1e⟩ := step_false h2
  have hpiR : p1' = .R := hp1 ▸ hR
  have hnwi : ¬ IsWrong s1' := hs1 ▸ hnw1
  have hnwj : ¬ IsWrong s0' := hs0 ▸ hnw0
  have hi0' : istep F M 0 c.p0 c.s0 c₁.st p0' s0' c₂.st := by
    rw [hp0e, hs0e] at hi0; exact hi0
  obtain ⟨σ₃, hj', hi'⟩ :=
    istep_right_comm hval (by decide) hi1 hpiR hnwi hi0' hnwj
  refine ⟨{ c with p0 := p0', s0 := s0', st := σ₃ }, mk_step_false hj',
    p1', s1', by simpa [th, tid] using hi', ?_⟩
  exact ⟨hp1e.trans hp1, hs1e.trans hs1, hp0, hs0⟩

/-- Left-commutation, `1`-then-`0`: a left-mover step of thread 0 (from
    post-commit phase `N`, non-wrong) commutes left past a *preceding*
    non-wrong step of thread 1. -/
theorem left_comm_01 {F M} (hval : Valid M) {c c₁ c₂ : Cfg}
    (h1 : Step F M true c c₁) (hnw1 : ¬ IsWrong c₁.s1)
    (h2 : Step F M false c₁ c₂) (hN : c.p0 = .N) (hnw0 : ¬ IsWrong c₂.s0) :
    ∃ c₃, Step F M false c c₃ ∧ Step F M true c₃ c₂ := by
  obtain ⟨p1', s1', hi1, hp1, hs1, hp0e, hs0e⟩ := step_true h1
  obtain ⟨p0', s0', hi0, hp0, hs0, hp1e, hs1e⟩ := step_false h2
  have hnwj : ¬ IsWrong s1' := hs1 ▸ hnw1
  have hnwi : ¬ IsWrong s0' := hs0 ▸ hnw0
  have hi0' : istep F M 0 c.p0 c.s0 c₁.st p0' s0' c₂.st := by
    rw [hp0e, hs0e] at hi0; exact hi0
  obtain ⟨σ₃, hi', hj'⟩ := istep_left_comm hval (by decide) hi1 hnwj hi0' hN hnwi
  refine ⟨{ c with p0 := p0', s0 := s0', st := σ₃ }, mk_step_false hi',
    p1', s1', by simpa [th, tid] using hj', ?_⟩
  exact ⟨hp1e.trans hp1, hs1e.trans hs1, hp0, hs0⟩

/-- Left-commutation, `0`-then-`1` (mirror). -/
theorem left_comm_10 {F M} (hval : Valid M) {c c₁ c₂ : Cfg}
    (h1 : Step F M false c c₁) (hnw0 : ¬ IsWrong c₁.s0)
    (h2 : Step F M true c₁ c₂) (hN : c.p1 = .N) (hnw1 : ¬ IsWrong c₂.s1) :
    ∃ c₃, Step F M true c c₃ ∧ Step F M false c₃ c₂ := by
  obtain ⟨p0', s0', hi0, hp0, hs0, hp1e, hs1e⟩ := step_false h1
  obtain ⟨p1', s1', hi1, hp1, hs1, hp0e, hs0e⟩ := step_true h2
  have hnwj : ¬ IsWrong s0' := hs0 ▸ hnw0
  have hnwi : ¬ IsWrong s1' := hs1 ▸ hnw1
  have hi1' : istep F M 1 c.p1 c.s1 c₁.st p1' s1' c₂.st := by
    rw [hp1e, hs1e] at hi1; exact hi1
  obtain ⟨σ₃, hi', hj'⟩ := istep_left_comm hval (by decide) hi0 hnwj hi1' hN hnwi
  refine ⟨{ c with p1 := p1', s1 := s1', st := σ₃ }, mk_step_true hi',
    p0', s0', by simpa [th, tid] using hj', ?_⟩
  exact ⟨hp0e.trans hp0, hs0e.trans hs0, hp1, hs1⟩

end Cfg
end MoverRust
