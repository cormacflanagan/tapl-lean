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
  ▸ `left_comm_01`  / `left_comm_10`  — Lemma 8 at the two-thread level;
  ▸ `cfg_diamond`      — Lemma 10 at the two-thread level;
  ▸ `iterated_diamond` — Lemma 11 (Iterative Diamond), by which thread
    0's post-commit completion merges into a concurrent thread-1 run;
  ▸ `iterated_rcomm`   — thread 0's whole pre-commit run defers past a
    following thread-1 run (the multi-step Right Commutativity engine
    that claim (1) uses to right-commute a Pre block).

  With Lemma 9 (`Postcommit.lean`) this is the *complete lemma toolkit*
  of the paper's Appendix B.1, together with its two multi-step engines.
  What remains for the full theorem is the two trace inductions built on
  top of them: claim (1), decomposing a preemptive trace as `Post*·Pre*`,
  and claim (2), completing the last incomplete post-commit block — plus
  the two-thread typing invariant (`⊢ Π`) that claim (2) carries to
  invoke Lemma 9.  See the README.
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
    ∃ c₃, Step F M true c c₃ ∧ Step F M false c₃ c₂ ∧ c₃.s1 = c₂.s1 := by
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
    ⟨p0', s0', by simpa [th, tid] using hi', ?_⟩, hs1.symm⟩
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

/-! ### The diamond and its iteration (for merging a post-commit tail)

These lift Lemma 10 to the two-thread configuration and iterate it, so
that thread 0's post-commit completion (a run of left-mover steps) can
be merged into a concurrent run of thread 1 — exactly the merge claim (2)
performs with Lemma 9's termination trace. -/

/-- Lemma 10 at the two-thread level: with thread 0 post-commit, two
    steps from a common `c` (thread 0 left-mover, thread 1 anything)
    close a diamond. -/
theorem cfg_diamond {F M} (hval : Valid M) {c c₀ c₁ : Cfg} (hN : c.p0 = .N)
    (h0 : Step F M false c c₀) (hnw0 : ¬ IsWrong c₀.s0)
    (h1 : Step F M true c c₁) (hnw1 : ¬ IsWrong c₁.s1) :
    ∃ c', Step F M false c₁ c' ∧ Step F M true c₀ c' ∧
      c'.s0 = c₀.s0 ∧ c'.s1 = c₁.s1 ∧ c'.p0 = c₀.p0 := by
  obtain ⟨p0', s0', hi0, hp0, hs0, hp1e0, hs1e0⟩ := step_false h0
  obtain ⟨p1', s1', hi1, hp1, hs1, hp0e1, hs0e1⟩ := step_true h1
  have hnwi : ¬ IsWrong s1' := hs1 ▸ hnw1
  have hnwj : ¬ IsWrong s0' := hs0 ▸ hnw0
  -- diamond with j = 0 (post-commit), i = 1
  obtain ⟨σ₃, hj', hi'⟩ :=
    istep_diamond hval (by decide) hi1 hnwi hi0 hN hnwj
  refine ⟨{ c₁ with p0 := p0', s0 := s0', st := σ₃ }, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨p0', s0', ?_, ?_⟩
    · simp only [th, tid]; rw [hp0e1, hs0e1]; exact hj'
    · simp [cond_false]
  · refine ⟨p1', s1', ?_, ?_⟩
    · simp only [th, tid]
      rw [(⟨hp1e0, hs1e0⟩ : c₀.p1 = c.p1 ∧ c₀.s1 = c.s1).1,
        (⟨hp1e0, hs1e0⟩ : c₀.p1 = c.p1 ∧ c₀.s1 = c.s1).2]; exact hi'
    · simp only [cond_true]; exact ⟨hp1, hs1, hp0.symm, hs0.symm⟩
  · show s0' = c₀.s0; exact hs0.symm
  · rfl
  · show p0' = c₀.p0; exact hp0.symm

/-- A thread-1 step leaves thread 0's `(phase, statement)` untouched. -/
theorem step_true_pres0 {F M c c'} (h : Step F M true c c') :
    c'.p0 = c.p0 ∧ c'.s0 = c.s0 := by
  obtain ⟨_, _, _, _, _, hp0e, hs0e⟩ := step_true h; exact ⟨hp0e, hs0e⟩

/-- `L0` — one post-commit left-mover step of thread 0 (phase `N`,
    non-wrong result); `T1` — one non-wrong step of thread 1. -/
def L0 (F : FnTable) (M : MSpec) (a b : Cfg) : Prop :=
  Step F M false a b ∧ a.p0 = .N ∧ ¬ IsWrong b.s0
def T1 (F : FnTable) (M : MSpec) (a b : Cfg) : Prop :=
  Step F M true a b ∧ ¬ IsWrong b.s1

/-- Diamond of one thread-0 post-commit step against a whole thread-1
    run. -/
theorem diamond_0_multi1 {F M} (hval : Valid M) {c cB : Cfg}
    (h1s : Multi (T1 F M) c cB) :
    ∀ c₀, L0 F M c c₀ → ∃ c', Multi (T1 F M) c₀ c' ∧ L0 F M cB c' := by
  induction h1s with
  | refl => intro c₀ h0; exact ⟨c₀, .refl _, h0⟩
  | @head c c₁ cB ht1 _ ih =>
      intro c₀ h0
      obtain ⟨hstep1, hnw1⟩ := ht1
      obtain ⟨hstep0, hN, hnw0⟩ := h0
      obtain ⟨c'', hs0', hs1', hs0eq, hs1eq, _⟩ :=
        cfg_diamond hval hN hstep0 hnw0 hstep1 hnw1
      have hL0' : L0 F M c₁ c'' :=
        ⟨hs0', (step_true_pres0 hstep1).1.trans hN, hs0eq ▸ hnw0⟩
      obtain ⟨c', hmulti, hLB⟩ := ih c'' hL0'
      exact ⟨c', .head ⟨hs1', hs1eq ▸ hnw1⟩ hmulti, hLB⟩

/-- **Lemma 11 (Iterative Diamond).**  Thread 0's post-commit run and a
    concurrent thread-1 run, both from `c`, merge to a common
    configuration — the merge that folds Lemma 9's termination trace into
    the main trace. -/
theorem iterated_diamond {F M} (hval : Valid M) {c cA : Cfg}
    (h0s : Multi (L0 F M) c cA) :
    ∀ cB, Multi (T1 F M) c cB →
      ∃ c', Multi (T1 F M) cA c' ∧ Multi (L0 F M) cB c' := by
  induction h0s with
  | refl => intro cB h1s; exact ⟨cB, h1s, .refl _⟩
  | @head c c₁ cA hl0 _ ih =>
      intro cB h1s
      obtain ⟨c'', hmultiT, hL0B⟩ := diamond_0_multi1 hval h1s c₁ hl0
      obtain ⟨c', hT1A, hL0'⟩ := ih c'' hmultiT
      exact ⟨c', hT1A, .head hL0B hL0'⟩

/-! ### Iterated right-commutation (deferring one thread past the other)

A pre-commit (right-mover) step of thread 0 commutes to the right of a
whole thread-1 run; iterating, thread 0's entire pre-commit run defers
past thread 1's run.  This is the engine claim (1) uses to right-commute
a Pre block over the other thread's steps. -/

/-- `RS0` — one pre-commit right-mover step of thread 0 (ending phase
    `R`, non-wrong). -/
def RS0 (F : FnTable) (M : MSpec) (a b : Cfg) : Prop :=
  Step F M false a b ∧ b.p0 = .R ∧ ¬ IsWrong b.s0

/-- One thread-0 right-mover step defers past a whole thread-1 run. -/
theorem rcomm_0_multi1 {F M} (hval : Valid M) {c₀ cB : Cfg}
    (h1s : Multi (T1 F M) c₀ cB) :
    ∀ c, RS0 F M c c₀ → ∃ c', Multi (T1 F M) c c' ∧ RS0 F M c' cB := by
  induction h1s with
  | refl => intro c h0; exact ⟨c, .refl _, h0⟩
  | @head c₀ c₁ cB ht1 _ ih =>
      intro c h0
      obtain ⟨hstep0, hR, hnw0⟩ := h0
      obtain ⟨hstep1, hnw1⟩ := ht1
      obtain ⟨c₃, hT, hF, hs1eq⟩ := right_comm_01 hval hstep0 hR hnw0 hstep1 hnw1
      -- the deferred thread-0 step still ends in phase R, non-wrong
      have hpres := step_true_pres0 hstep1
      have hR₁ : c₁.p0 = .R := hpres.1.trans hR
      have hnw₁ : ¬ IsWrong c₁.s0 := hpres.2 ▸ hnw0
      have hT1' : T1 F M c c₃ := ⟨hT, hs1eq ▸ hnw1⟩
      obtain ⟨c', hmulti, hRB⟩ := ih c₃ ⟨hF, hR₁, hnw₁⟩
      exact ⟨c', .head hT1' hmulti, hRB⟩

/-- Thread 0's whole pre-commit run defers past a following thread-1 run:
    `[0-run][1-run]` reorders to `[1-run][0-run]`. -/
theorem iterated_rcomm {F M} (hval : Valid M) {c cA : Cfg}
    (h0s : Multi (RS0 F M) c cA) :
    ∀ cB, Multi (T1 F M) cA cB →
      ∃ c', Multi (T1 F M) c c' ∧ Multi (RS0 F M) c' cB := by
  induction h0s with
  | refl => intro cB h1s; exact ⟨cB, h1s, .refl _⟩
  | @head c c₁ cA hr0 _ ih =>
      intro cB h1s
      obtain ⟨c'', h1c₁, h0rest⟩ := ih cB h1s
      obtain ⟨c', h1c, hr0'⟩ := rcomm_0_multi1 hval h1c₁ c hr0
      exact ⟨c', h1c, .head hr0' h0rest⟩

end Cfg
end MoverRust

