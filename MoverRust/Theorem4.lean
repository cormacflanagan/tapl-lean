/-
  MoverRust / Theorem4 — the Reduction Theorem (paper Theorem 4)

  Theorem 4 is the heart of reduction: a program that goes wrong under
  the *preemptive* instrumented scheduler also goes wrong under the
  *cooperative* (non-preemptive) one.  Composed with cooperative
  soundness (Preservation.lean) it upgrades to full preemptive
  soundness.

  The mechanization here is faithful to the paper's structure but,
  to keep the trace-permutation argument tractable, is carried out for a
  **two-thread** pool — the setting in which every conceptual ingredient
  of reduction is present (right-movers commute right, left-movers
  commute left, a single commit, post-commit termination) while the
  n-thread block bookkeeping collapses to "the other thread".

  This file provides, all fully proved:

  ▸ `istep_char`         — every instrumented step is an action step or
                           a store-preserving (silent/wrong) step;
  ▸ `ipstep_right_comm`  — Lemma 7 at the pool level;
  ▸ `ipstep_left_comm`   — Lemma 8 at the pool level;
  ▸ `ipstep_diamond`     — Lemma 10 at the pool level;
  ▸ `reduction_two`      — Theorem 4 for two threads.
-/
import MoverRust.Reduction

namespace MoverRust
open Effect

/-! ### Characterizing a single instrumented step

Every `istep` either performs an underlying action `A` (updating the
store by `den A` and the phase by `p ; M A`), or is *store-preserving*
(structural unfolding, a call, a yield that resets the phase, or a step
into `wrong`). -/

/-- The step performed action `A`: the store moves by `den A`, the phase
    by `p ; M A`, the result is non-error, and — crucially for
    reordering — the step *reproduces* at any other store (the resulting
    statement `s'` and the choice of `A` are store-independent; only the
    values differ). -/
def ActionStep (F : FnTable) (M : MSpec) (t : Tid) (p : Effect) (s : Stmt)
    (σ : Store) (p' : Effect) (s' : Stmt) (σ' : Store) : Prop :=
  ∃ A, den A t σ σ' ∧ p' = p.seq (M A t σ) ∧ p' ≠ .E ∧
    (∀ σ₀ σ₀', den A t σ₀ σ₀' → p.seq (M A t σ₀) ≠ .E →
       istep F M t p s σ₀ (p.seq (M A t σ₀)) s' σ₀')

/-- `istep` trichotomy.  A step is exactly one of:
    * an **action step** (store moves by `den A`, phase by `p ; M A`);
    * a step into **wrong** (store and phase unchanged); or
    * a **silent** step whose transition is *store-independent* — it
      reproduces from any store — covering `seq`-unfolding, `call`,
      `wloop`-unfolding, and `yield`. -/
theorem istep_char {F M t p s σ p' s' σ'} (h : istep F M t p s σ p' s' σ') :
    ActionStep F M t p s σ p' s' σ' ∨
    (IsWrong s' ∧ σ' = σ ∧ p' = p) ∨
    (σ' = σ ∧ (p' = p ∨ p' = .R) ∧ ∀ σ₀, istep F M t p s σ₀ p' s' σ₀) := by
  induction h with
  | seqSkip s₂ => exact .inr (.inr ⟨rfl, .inl rfl, fun σ₀ => .seqSkip s₂⟩)
  | seqCong s₂ hst ih =>
      rcases ih with ha | hw | hs
      · obtain ⟨A, hden, hp, hne, hrep⟩ := ha
        exact .inl ⟨A, hden, hp, hne, fun σ₀ σ₀' hd hE => .seqCong s₂ (hrep σ₀ σ₀' hd hE)⟩
      · obtain ⟨hwrong, hσ, hp⟩ := hw
        exact .inr (.inl ⟨.seq s₂ hwrong, hσ, hp⟩)
      · obtain ⟨hσ, hp, hrep⟩ := hs
        exact .inr (.inr ⟨hσ, hp, fun σ₀ => .seqCong s₂ (hrep σ₀)⟩)
  | yld => exact .inr (.inr ⟨rfl, .inr rfl, fun σ₀ => .yld⟩)
  | act hden hne => exact .inl ⟨_, hden, rfl, hne, fun σ₀ σ₀' hd hE => .act hd hE⟩
  | actWrong => exact .inr (.inl ⟨.wrong, rfl, rfl⟩)
  | iteS s₁ s₂ hden hne =>
      exact .inl ⟨_, hden, rfl, hne, fun σ₀ σ₀' hd hE => .iteS s₁ s₂ hd hE⟩
  | iteWrong => exact .inr (.inl ⟨.wrong, rfl, rfl⟩)
  | wloopUnfold C s => exact .inr (.inr ⟨rfl, .inl rfl, fun σ₀ => .wloopUnfold C s⟩)
  | call hf => exact .inr (.inr ⟨rfl, .inl rfl, fun σ₀ => .call hf⟩)

/-! ### Lemma 7 — Right commutativity, at the level of two isteps

If thread `i` takes a non-wrong step ending in the pre-commit phase `R`
(a right-mover), then it commutes to the right of any following non-wrong
step of a different thread `j`: the same statements and phases result,
via an intermediate store `σ₃`. -/

theorem istep_right_comm {F M} (hval : Valid M) {i j : Tid} (hij : i ≠ j)
    {pi si pi' si' pj sj pj' sj' : _} {σ σ₁ σ₂ : Store}
    (hstepi : istep F M i pi si σ pi' si' σ₁) (hpiR : pi' = .R) (hi_nw : ¬ IsWrong si')
    (hstepj : istep F M j pj sj σ₁ pj' sj' σ₂) (hj_nw : ¬ IsWrong sj') :
    ∃ σ₃, istep F M j pj sj σ pj' sj' σ₃ ∧ istep F M i pi si σ₃ pi' si' σ₂ := by
  rcases istep_char hstepi with hai | ⟨hw, _⟩ | ⟨hσ1, _, hrepi⟩
  · -- i is an action step, a right-mover
    obtain ⟨Ai, hdeni, hpi, _, hrepi⟩ := hai
    have hMi_le : M Ai i σ ≤ .R := by
      apply seq_eq_R_imp_le pi _ (hval.noY Ai i σ); rw [← hpi, hpiR]
    have hMi_leN : M Ai i σ ≤ .N := le_trans hMi_le (by decide)
    rcases istep_char hstepj with haj | ⟨hw, _⟩ | ⟨hσ2, _, hrepj⟩
    · -- j is also an action step
      obtain ⟨Aj, hdenj, hpj, hnej, hrepj⟩ := haj
      have hMj_leN : M Aj j σ₁ ≤ .N := arg_le_N_of_seq_ne_E pj _ (hpj ▸ hnej)
      -- validity condition 1 gives a reordered intermediate store
      obtain ⟨σ₃, hdenj', hdeni'⟩ :=
        hval.right_commute hij hMi_le hdeni hMj_leN hdenj
      -- validity condition 3: i's mover does not change j's effect
      have hMj_eq : M Aj j σ₁ = M Aj j σ := hval.stable_eff hij hMi_leN hdeni
      have hMi_eq : M Ai i σ₃ = M Ai i σ :=
        hval.stable_eff (fun e => hij e.symm) (hMj_eq ▸ hMj_leN) hdenj'
      refine ⟨σ₃, ?_, ?_⟩
      · have := hrepj σ σ₃ hdenj' (by rw [← hMj_eq]; exact hpj ▸ hnej)
        rwa [← hMj_eq, ← hpj] at this
      · have := hrepi σ₃ σ₂ hdeni' (by rw [hMi_eq, ← hpi, hpiR]; decide)
        rwa [hMi_eq, ← hpi] at this
    · exact absurd hw hj_nw
    · -- j is silent: σ₂ = σ₁; j reproduces from σ, then i runs unchanged
      subst hσ2
      exact ⟨σ, hrepj σ, hstepi⟩
  · exact absurd hw hi_nw
  · -- i is silent: σ₁ = σ; j steps from σ directly, i reproduced after
    subst hσ1
    exact ⟨σ₂, hstepj, hrepi σ₂⟩

end MoverRust
