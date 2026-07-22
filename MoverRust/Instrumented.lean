/-
  MoverRust / Instrumented — the instrumented semantics (paper Fig. 10)

  The instrumented semantics extends each thread with a *phase*
  `p ∈ {R, N}` — the DFA state of its current reducible sequence
  (`R` = pre-commit, `N` = post-commit).  Each action composes its
  mover effect onto the phase; if the result is `E` the thread steps to
  `wrong` instead (the code is not reducible, or an access violates the
  mover specification).  `yield` resets the phase to `R`.

  Two schedulers:

  ▸ preemptive  (`ipstep`)  — any thread steps at any time;
  ▸ non-preemptive (`npstep`) — a thread may step only when every
    other thread is parked (at a yield / terminated / failed), i.e.
    context switches happen only at yields.

  `Theorem 3 (Simulation)`: the instrumented preemptive semantics
  simulates the standard semantics, going wrong at least as often.
-/
import MoverRust.Logic

namespace MoverRust

/-- One instrumented step of thread `t`:
    `istep F M t p s σ p' s' σ'`  is the paper's  `p·s·σ →t p'·s'·σ'`. -/
inductive istep (F : FnTable) (M : MSpec) (t : Tid) :
    Effect → Stmt → Store → Effect → Stmt → Store → Prop where
  | seqSkip {p σ} (s₂ : Stmt) :
      istep F M t p (.seq .skip s₂) σ p s₂ σ
  | seqCong {p s₁ σ p' s₁' σ'} (s₂ : Stmt) :
      istep F M t p s₁ σ p' s₁' σ' →
      istep F M t p (.seq s₁ s₂) σ p' (.seq s₁' s₂) σ'
  | yld {p σ} : istep F M t p .yld σ .R .skip σ
  | act {p A σ σ'} :
      den A t σ σ' →
      p.seq (M A t σ) ≠ .E →
      istep F M t p (.act A) σ (p.seq (M A t σ)) .skip σ'
  | actWrong {p A σ} :
      p.seq (M A t σ) = .E →
      istep F M t p (.act A) σ p .wrong σ
  | iteS {p : Effect} {C : Cond} {b σ σ'} (s₁ s₂ : Stmt) :
      den (condA C b) t σ σ' →
      p.seq (M (condA C b) t σ) ≠ .E →
      istep F M t p (.ite C s₁ s₂) σ (p.seq (M (condA C b) t σ))
        (if b then s₁ else s₂) σ'
  | iteWrong {p : Effect} {C : Cond} {b σ σ'} (s₁ s₂ : Stmt) :
      den (condA C b) t σ σ' →
      p.seq (M (condA C b) t σ) = .E →
      istep F M t p (.ite C s₁ s₂) σ p .wrong σ
  | wloopUnfold {p σ} (C : Cond) (s : Stmt) :
      istep F M t p (.wloop C s) σ p (.ite C (.seq s (.wloop C s)) .skip) σ
  | call {p f body σ} :
      F f = some body →
      istep F M t p (.call f) σ p body σ

/-- Instrumented states `Π = p₁·s₁ .. pₙ·sₙ · σ`. -/
structure IState : Type where
  ths : List (Effect × Stmt)
  store : Store

/-- Preemptive scheduling of the instrumented semantics. -/
inductive ipstep (F : FnTable) (M : MSpec) : IState → IState → Prop where
  | mk {ths σ σ' p s p' s'} (t : Tid) :
      ths.get? t = some (p, s) →
      istep F M t p s σ p' s' σ' →
      ipstep F M ⟨ths, σ⟩ ⟨ths.set t (p', s'), σ'⟩

/-- Non-preemptive scheduling: only the single unparked thread may
    run; context switches happen at yields. -/
inductive npstep (F : FnTable) (M : MSpec) : IState → IState → Prop where
  | mk {ths σ σ' p s p' s'} (t : Tid) :
      ths.get? t = some (p, s) →
      istep F M t p s σ p' s' σ' →
      (∀ u pr, u ≠ t → ths.get? u = some pr → Parked pr.2) →
      npstep F M ⟨ths, σ⟩ ⟨ths.set t (p', s'), σ'⟩

/-- A non-preemptive step is a preemptive step. -/
theorem npstep.toIpstep {F M c c'} (h : npstep F M c c') : ipstep F M c c' := by
  cases h with
  | mk t hget hstep _ => exact .mk t hget hstep

/-- Some thread has failed. -/
def IStateWrong (c : IState) : Prop := ∃ pr ∈ c.ths, IsWrong pr.2

def IGoesWrong (F : FnTable) (M : MSpec) (c : IState) : Prop :=
  ∃ c', Multi (ipstep F M) c c' ∧ IStateWrong c'

def NGoesWrong (F : FnTable) (M : MSpec) (c : IState) : Prop :=
  ∃ c', Multi (npstep F M) c c' ∧ IStateWrong c'

/-! ### Simulation (Theorem 3) -/

/-- `Σ ∼ Π`: same statements, same store, any phases. -/
def SimRel (st : State) (c : IState) : Prop :=
  c.ths.map Prod.snd = st.threads ∧ c.store = st.store

/-- Thread-local simulation: every standard step is matched by an
    instrumented step — either faithfully, or by going wrong. -/
theorem step_sim {F t s σ s' σ'} (M : MSpec) (h : step F t s σ s' σ') :
    ∀ p, (∃ p', istep F M t p s σ p' s' σ') ∨
         (∃ s'', istep F M t p s σ p s'' σ ∧ IsWrong s'') := by
  induction h with
  | seqSkip s₂ σ => exact fun p => .inl ⟨p, .seqSkip s₂⟩
  | seqCong s₂ _ ih =>
      intro p
      cases ih p with
      | inl h' => exact .inl ⟨h'.choose, .seqCong s₂ h'.choose_spec⟩
      | inr h' =>
          obtain ⟨s'', hstep, hw⟩ := h'
          exact .inr ⟨.seq s'' s₂, .seqCong s₂ hstep, .seq s₂ hw⟩
  | yld σ => exact fun p => .inl ⟨.R, .yld⟩
  | act hden =>
      intro p
      rename_i A σ σ'
      by_cases hE : p.seq (M A t σ) = .E
      · exact .inr ⟨.wrong, .actWrong hE, .wrong⟩
      · exact .inl ⟨_, .act hden hE⟩
  | iteS s₁ s₂ hden =>
      intro p
      rename_i C b σ σ'
      by_cases hE : p.seq (M (condA C b) t σ) = .E
      · exact .inr ⟨.wrong, .iteWrong s₁ s₂ hden hE, .wrong⟩
      · exact .inl ⟨_, .iteS s₁ s₂ hden hE⟩
  | wloopUnfold C s σ => exact fun p => .inl ⟨p, .wloopUnfold C s⟩
  | call hf => exact fun p => .inl ⟨p, .call hf⟩

/-- Map/set bookkeeping for pools. -/
theorem list_map_set {α β : Type _} (f : α → β) :
    ∀ (l : List α) (n : Nat) (a : α), (l.set n a).map f = (l.map f).set n (f a)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | x :: l, n + 1, a => congrArg (f x :: ·) (list_map_set f l n a)

/-- Theorem 3 (Simulation), one step: if `Σ ∼ Π` and `Σ → Σ'` then
    `Π → Π'` with `Σ' ∼ Π'`, or `Π'` wrong. -/
theorem sim_step {F M st st' c} (h : pstep F st st') (hsim : SimRel st c) :
    ∃ c', ipstep F M c c' ∧ (SimRel st' c' ∨ IStateWrong c') := by
  obtain ⟨ths, σi⟩ := c
  cases h with
  | mk t hget hstep =>
    rename_i ss σ σ' s s'
    obtain ⟨hths, hσ⟩ := hsim
    simp only at hths hσ
    subst hσ
    rw [← hths, List.get?_map] at hget
    cases hg : ths.get? t with
    | none => rw [hg] at hget; cases hget
    | some pr =>
      rw [hg] at hget
      obtain ⟨p, s₀⟩ := pr
      simp only [Option.map_some'] at hget
      cases hget
      cases step_sim M hstep p with
      | inl h' =>
          obtain ⟨p', hi⟩ := h'
          refine ⟨⟨ths.set t (p', s'), σ'⟩, .mk t hg hi, .inl ⟨?_, rfl⟩⟩
          simp only [list_map_set, hths]
      | inr h' =>
          obtain ⟨s'', hi, hw⟩ := h'
          refine ⟨⟨ths.set t (p, s''), σi⟩, .mk t hg hi, .inr ?_⟩
          exact ⟨(p, s''), List.get?_mem (get?_set_self (get?_lt hg)), hw⟩

end MoverRust
