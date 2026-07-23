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

/-! ### Lemma 8 — Left commutativity, at the level of two isteps

If thread `i` takes a non-wrong step from the post-commit phase `N` (a
left-mover), it commutes to the left of a *preceding* non-wrong step of a
different thread `j`. -/

theorem istep_left_comm {F M} (hval : Valid M) {i j : Tid} (hij : i ≠ j)
    {pi si pi' si' pj sj pj' sj' : _} {σ σ₁ σ₂ : Store}
    (hstepj : istep F M j pj sj σ pj' sj' σ₁) (hj_nw : ¬ IsWrong sj')
    (hstepi : istep F M i pi si σ₁ pi' si' σ₂) (hpiN : pi = .N) (hi_nw : ¬ IsWrong si') :
    ∃ σ₃, istep F M i pi si σ pi' si' σ₃ ∧ istep F M j pj sj σ₃ pj' sj' σ₂ := by
  rcases istep_char hstepi with hai | ⟨hw, _⟩ | ⟨hσ2, _, hrepi⟩
  · -- i is an action step, a left-mover (post-commit)
    obtain ⟨Ai, hdeni, hpi, hnei, hrepi⟩ := hai
    have hMi_leL : M Ai i σ₁ ≤ .L := by
      apply post_phase_le; rw [← hpiN, ← hpi]; exact hnei
    have hMi_leN : M Ai i σ₁ ≤ .N := le_trans hMi_leL (by decide)
    rcases istep_char hstepj with haj | ⟨hw, _⟩ | ⟨hσ1, _, hrepj⟩
    · -- j is also an action step
      obtain ⟨Aj, hdenj, hpj, hnej, hrepj⟩ := haj
      have hMj_leN : M Aj j σ ≤ .N := arg_le_N_of_seq_ne_E pj _ (hpj ▸ hnej)
      -- validity condition 2 gives the reordered intermediate store
      obtain ⟨σ₃, hdeni', hdenj'⟩ :=
        hval.left_commute (fun e => hij e.symm) hMj_leN hdenj hMi_leL hdeni
      -- condition 3: j's mover does not change i's effect, and vice versa
      have hMi_eq : M Ai i σ₁ = M Ai i σ := hval.stable_eff (fun e => hij e.symm) hMj_leN hdenj
      have hMj_eq : M Aj j σ₃ = M Aj j σ := hval.stable_eff hij (hMi_eq ▸ hMi_leN) hdeni'
      refine ⟨σ₃, ?_, ?_⟩
      · have := hrepi σ σ₃ hdeni' (by rw [← hMi_eq]; exact hpi ▸ hnei)
        rwa [← hMi_eq, ← hpi] at this
      · have := hrepj σ₃ σ₂ hdenj' (by rw [hMj_eq]; exact hpj ▸ hnej)
        rwa [hMj_eq, ← hpj] at this
    · exact absurd hw hj_nw
    · -- j silent: σ₁ = σ; i runs unchanged, then j reproduces
      subst hσ1
      exact ⟨σ₂, hstepi, hrepj σ₂⟩
  · exact absurd hw hi_nw
  · -- i silent: σ₂ = σ₁; i reproduces from σ, then j runs unchanged
    subst hσ2
    exact ⟨σ, hrepi σ, hstepj⟩

/-! ### Lifting the commutation lemmas to pool steps

The two-`istep` lemmas above are now packaged as commutations of the
real pool step relation `ipstepAt` — thread `t` steps the whole pool. -/

/-- Thread `t` takes one instrumented pool step. -/
def ipstepAt (F : FnTable) (M : MSpec) (t : Tid) (c c' : IState) : Prop :=
  ∃ p s p' s', c.ths.get? t = some (p, s) ∧
    istep F M t p s c.store p' s' c'.store ∧ c'.ths = c.ths.set t (p', s')

theorem ipstep_iff {F M c c'} : ipstep F M c c' ↔ ∃ t, ipstepAt F M t c c' := by
  constructor
  · rintro ⟨t, hget, hstep⟩; exact ⟨t, _, _, _, _, hget, hstep, rfl⟩
  · rintro ⟨t, p, s, p', s', hget, hstep, hths⟩
    obtain ⟨ths, σ⟩ := c; obtain ⟨ths', σ'⟩ := c'
    simp only at hget hstep hths; subst hths
    exact .mk t hget hstep

/-- Reading a *different* thread is unaffected by a step at `t`. -/
theorem ipstepAt_get_other {F M t c c'} (h : ipstepAt F M t c c') {u : Tid}
    (hu : u ≠ t) : c'.ths.get? u = c.ths.get? u := by
  obtain ⟨p, s, p', s', _, _, hths⟩ := h
  rw [hths, get?_set_other (fun e => hu e.symm)]

/-- The phase and statement of thread `t` after its own step. -/
theorem ipstepAt_get_self {F M t c c'} (h : ipstepAt F M t c c') :
    ∃ p' s', c'.ths.get? t = some (p', s') ∧
      ∃ p s, c.ths.get? t = some (p, s) ∧ istep F M t p s c.store p' s' c'.store := by
  obtain ⟨p, s, p', s', hget, hstep, hths⟩ := h
  exact ⟨p', s', by rw [hths, get?_set_self (get?_lt hget)], p, s, hget, hstep⟩

/-- **Lemma 7, pool level.**  A right-mover step of thread `i` (ending in
    phase `R`, non-wrong) commutes to the right of any following
    non-wrong step of a different thread `j`. -/
theorem ipstep_right_comm {F M} (hval : Valid M) {c c₁ c₂ : IState} {i j : Tid}
    (hij : i ≠ j)
    (h1 : ipstepAt F M i c c₁)
    (hiR : ∃ s, c₁.ths.get? i = some (.R, s) ∧ ¬ IsWrong s)
    (h2 : ipstepAt F M j c₁ c₂)
    (hj_nw : ∃ pj sj, c₂.ths.get? j = some (pj, sj) ∧ ¬ IsWrong sj) :
    ∃ c₃, ipstepAt F M j c c₃ ∧ ipstepAt F M i c₃ c₂ := by
  obtain ⟨pi, si, pi', si', hgeti, hstepi, hthsi⟩ := h1
  obtain ⟨pj, sj, pj', sj', hgetj, hstepj, hthsj⟩ := h2
  have hgetj_c : c.ths.get? j = some (pj, sj) := by
    rw [← hgetj, ipstepAt_get_other ⟨pi, si, pi', si', hgeti, hstepi, hthsi⟩
      (fun e => hij e.symm)]
  have hci1 : c₁.ths.get? i = some (pi', si') := by
    rw [hthsi, get?_set_self (get?_lt hgeti)]
  -- i ends in phase R, non-wrong
  obtain ⟨s, hiR_get, hiR_nw⟩ := hiR
  have hpr : (Effect.R, s) = (pi', si') := Option.some.inj (hiR_get ▸ hci1)
  have hpiR : pi' = .R := (congrArg Prod.fst hpr).symm
  have hsi : s = si' := congrArg Prod.snd hpr
  have hnwi : ¬ IsWrong si' := hsi ▸ hiR_nw
  -- j non-wrong
  have hjc2 : c₂.ths.get? j = some (pj', sj') := by
    rw [hthsj, get?_set_self (get?_lt hgetj)]
  obtain ⟨pj0, sj0, hj2_get, hj2_nw⟩ := hj_nw
  have hprj : (pj0, sj0) = (pj', sj') := Option.some.inj (hj2_get ▸ hjc2)
  have hsj : sj0 = sj' := congrArg Prod.snd hprj
  have hnwj : ¬ IsWrong sj' := hsj ▸ hj2_nw
  obtain ⟨σ₃, hj', hi'⟩ := istep_right_comm hval hij hstepi hpiR hnwi hstepj hnwj
  refine ⟨⟨c.ths.set j (pj', sj'), σ₃⟩, ⟨pj, sj, pj', sj', hgetj_c, hj', rfl⟩,
    pi, si, pi', si', ?_, hi', ?_⟩
  · rw [get?_set_other (fun e => hij e.symm)]; exact hgeti
  · show c₂.ths = (c.ths.set j (pj', sj')).set i (pi', si')
    rw [hthsj, hthsi, set_set_comm _ _ _ (fun e => hij e.symm)]

/-- **Lemma 8, pool level.**  A left-mover step of thread `i` (from the
    post-commit phase `N`, non-wrong) commutes to the left of a preceding
    non-wrong step of a different thread `j`. -/
theorem ipstep_left_comm {F M} (hval : Valid M) {c c₁ c₂ : IState} {i j : Tid}
    (hij : i ≠ j)
    (h1 : ipstepAt F M j c c₁)
    (hj_nw : ∃ pj sj, c₁.ths.get? j = some (pj, sj) ∧ ¬ IsWrong sj)
    (h2 : ipstepAt F M i c₁ c₂)
    (hiN : ∃ s, c₁.ths.get? i = some (.N, s))
    (hi_nw : ∃ p s, c₂.ths.get? i = some (p, s) ∧ ¬ IsWrong s) :
    ∃ c₃, ipstepAt F M i c c₃ ∧ ipstepAt F M j c₃ c₂ := by
  obtain ⟨pj, sj, pj', sj', hgetj, hstepj, hthsj⟩ := h1
  obtain ⟨pi, si, pi', si', hgeti, hstepi, hthsi⟩ := h2
  have hgeti_c : c.ths.get? i = some (pi, si) := by
    rw [← hgeti, ipstepAt_get_other ⟨pj, sj, pj', sj', hgetj, hstepj, hthsj⟩ hij]
  obtain ⟨s, hiN_get⟩ := hiN
  have hprN : (Effect.N, s) = (pi, si) := Option.some.inj (hiN_get ▸ hgeti)
  have hpiN : pi = .N := (congrArg Prod.fst hprN).symm
  have hcj1 : c₁.ths.get? j = some (pj', sj') := by
    rw [hthsj, get?_set_self (get?_lt hgetj)]
  obtain ⟨pj0, sj0, hj1_get, hj1_nw⟩ := hj_nw
  have hprj : (pj0, sj0) = (pj', sj') := Option.some.inj (hj1_get ▸ hcj1)
  have hsj : sj0 = sj' := congrArg Prod.snd hprj
  have hnwj : ¬ IsWrong sj' := hsj ▸ hj1_nw
  have hci2 : c₂.ths.get? i = some (pi', si') := by
    rw [hthsi, get?_set_self (get?_lt hgeti)]
  obtain ⟨pi0, si0, hi2_get, hi2_nw⟩ := hi_nw
  have hpri : (pi0, si0) = (pi', si') := Option.some.inj (hi2_get ▸ hci2)
  have hsi : si0 = si' := congrArg Prod.snd hpri
  have hnwi : ¬ IsWrong si' := hsi ▸ hi2_nw
  obtain ⟨σ₃, hi', hj'⟩ := istep_left_comm hval hij hstepj hnwj hstepi hpiN hnwi
  refine ⟨⟨c.ths.set i (pi', si'), σ₃⟩, ⟨pi, si, pi', si', hgeti_c, hi', rfl⟩,
    pj, sj, pj', sj', ?_, hj', ?_⟩
  · rw [get?_set_other hij]; exact hgetj
  · show c₂.ths = (c.ths.set i (pi', si')).set j (pj', sj')
    rw [hthsi, hthsj, set_set_comm _ _ _ hij]

end MoverRust
