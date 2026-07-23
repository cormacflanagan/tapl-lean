/-
  MoverRust / Preservation — Theorems 5 and 6, and cooperative soundness

  ▸ `publish_yielding`, `stabilize_*` — Lemma 15 (Yield Stabilization):
    a parked thread's precondition can absorb interference `R*`.
  ▸ `istep_preserve` — Lemma 14 (Preservation for Redexes), by
    induction on the instrumented step.
  ▸ `IStateOK` — the [I-state] judgment `⊢ Π` (paper Figure 10).
  ▸ `npstep_preserve` — Theorem 5 (Preservation), including Lemma 17
    (Context Switch).
  ▸ `istateok_not_wrong` — Theorem 6 (Verified States Are Not Wrong).
  ▸ `cooperative_soundness` — verified states never go wrong under the
    non-preemptive scheduler.
-/
import MoverRust.Meta

namespace MoverRust

open Effect

/-! ### Publication and stabilization at yields (Lemma 15) -/

/-- At a yield, the current reducible sequence is already published to
    the guarantee. -/
theorem publish_at {D M R G s P Q e} (hy : AtYield s) (h : Judg D M R G s P Q e) :
    ∀ t a b, P t a b → G t a b := by
  induction hy generalizing P Q e with
  | yld => exact (inv_yld h).1
  | seq s₂ _ ih =>
      obtain ⟨Q₁, e₁, e₂, h₁, _, _⟩ := inv_seq h
      exact ih h₁

theorem publish_yielding {D M R G s P Q e} (hy : Yielding s)
    (h : Judg D M R G s P Q e) (hQG : ∀ t a b, Q t a b → G t a b) :
    ∀ t a b, P t a b → G t a b := by
  cases hy with
  | inl hat => exact publish_at hat h
  | inr hskip =>
      subst hskip
      exact fun t a b hp => hQG t a b ((inv_skip h).1 t a b hp)

/-- A thread parked at a yield can have its precondition stabilized by
    `R*`, keeping its postcondition and effect. -/
theorem stabilize_at {D M R G s P Q e} (hy : AtYield s) (h : Judg D M R G s P Q e)
    (hGrefl : ∀ t σ, G t σ σ) : Judg D M R G s (yieldP P R) Q e := by
  induction hy generalizing P Q e with
  | yld =>
      obtain ⟨hPG, himp⟩ := inv_yld h
      have hy' : Judg D M R G .yld (yieldP P R) (yieldP (yieldP P R) R) .Y :=
        .yieldJ (fun t a b hp => by rw [hp.1]; exact hGrefl t a)
      exact .conseq (PImp.refl _) (PImp.trans yieldP_yieldP himp)
        (RImp.refl _) (RImp.refl _) (Y_le _) hy'
  | seq s₂ _ ih =>
      obtain ⟨Q₁, e₁, e₂, h₁, h₂, hle⟩ := inv_seq h
      exact .conseq (PImp.refl _) (PImp.refl _) (RImp.refl _) (RImp.refl _)
        hle (.seqJ (ih h₁) h₂)

/-- Stabilization for any parked thread (yield or terminated). -/
theorem stabilize_yielding {D M R G s P Q e} (hy : Yielding s)
    (h : Judg D M R G s P Q e) (hQG : ∀ t a b, Q t a b → G t a b)
    (hGrefl : ∀ t σ, G t σ σ) :
    ∃ Q', Judg D M R G s (yieldP P R) Q' e ∧ ∀ t a b, Q' t a b → G t a b := by
  cases hy with
  | inl hat => exact ⟨Q, stabilize_at hat h hGrefl, hQG⟩
  | inr hskip =>
      subst hskip
      obtain ⟨_, hBe⟩ := inv_skip h
      refine ⟨yieldP P R,
        .conseq (PImp.refl _) (PImp.refl _) (RImp.refl _) (RImp.refl _) hBe
          (Judg.skip (P := yieldP P R)), ?_⟩
      rintro t a b ⟨heq, _⟩
      rw [heq]
      exact hGrefl t a

/-! ### Preservation for one thread step (Lemma 14) -/

/-- Preservation for a single instrumented step of one thread.

    Outcome (left): an ordinary step — the reducible sequence
    continues, the store moves to `σ'`, and the combined phase+future
    effect only shrinks.

    Outcome (right): a yield — the store is unchanged, the finished
    sequence `(σ₀, σ)` is published to `G`, and a fresh sequence starts
    at `σ` with phase `R`. -/
theorem istep_preserve {D : Decls} {M R G t p s σ p' s' σ' P Q e σ₀}
    (hval : Valid M) (hD : DeclsOK D M)
    (hstep : istep D.fns M t p s σ p' s' σ')
    (hj : Judg D M R G s P Q e)
    (hP : P t σ₀ σ)
    (hp : p = .R ∨ p = .N)
    (hpe : p.seq e ≠ .E) :
    (p' = .R ∨ p' = .N) ∧
    ((∃ P' e', Judg D M R G s' P' Q e' ∧ P' t σ₀ σ' ∧ p'.seq e' ≤ p.seq e) ∨
     (σ' = σ ∧ p' = .R ∧ G t σ₀ σ ∧
       ∃ P' e', Judg D M R G s' P' Q e' ∧ P' t σ σ ∧ p'.seq e' ≤ p.seq e)) := by
  induction hstep generalizing P Q e with
  | seqSkip s₂ =>
      obtain ⟨Q₁, e₁, e₂, h₁, h₂, hle⟩ := inv_seq hj
      obtain ⟨hPQ₁, hBe₁⟩ := inv_skip h₁
      refine ⟨hp, .inl ⟨Q₁, e₂, h₂, hPQ₁ _ _ _ hP, ?_⟩⟩
      exact seq_mono_right _ (le_trans (le_seq_of_B_le e₂ hBe₁) hle)
  | seqCong s₂ hstep' ih =>
      obtain ⟨Q₁, e₁, e₂, h₁, h₂, hle⟩ := inv_seq hj
      have hpe' : p.seq (e₁.seq e₂) ≠ .E :=
        seq_ne_E_mono (le_refl p) hle hpe
      have hpe₁ : p.seq e₁ ≠ .E := seq_seq_ne_E_left _ _ _ hpe'
      obtain ⟨hph', hrest⟩ := ih h₁ hP hpe₁
      refine ⟨hph', ?_⟩
      cases hrest with
      | inl h' =>
          obtain ⟨P', e₁', hj', hP', hb⟩ := h'
          exact .inl ⟨P', e₁'.seq e₂, .seqJ hj' h₂, hP',
            seq_bound_lemma e₂ hb hle⟩
      | inr h' =>
          obtain ⟨hσ, hpR, hG, P', e₁', hj', hP', hb⟩ := h'
          exact .inr ⟨hσ, hpR, hG, P', e₁'.seq e₂, .seqJ hj' h₂, hP',
            seq_bound_lemma e₂ hb hle⟩
  | yld =>
      obtain ⟨hPG, himp⟩ := inv_yld hj
      refine ⟨.inl rfl, .inr ⟨rfl, rfl, hPG _ _ _ hP, yieldP P R, .B,
        .conseq (PImp.refl _) himp (RImp.refl _) (RImp.refl _) (le_refl _)
          (Judg.skip (P := yieldP P R)),
        ⟨rfl, _, ⟨σ₀, hP⟩, Multi.refl _⟩, ?_⟩⟩
      rw [seq_B_right]
      exact phase_R_le _ _ hp hpe
  | act hden hne =>
      obtain ⟨e₀, hbound, htot, himp, hle⟩ := inv_act hj
      have hMle := hbound _ _ _ hP
      refine ⟨phase_step _ _ hp (hval.noY _ _ _) hne, .inl
        ⟨pseq P _, .B,
         .conseq (PImp.refl _) himp (RImp.refl _) (RImp.refl _) (le_refl _)
           (Judg.skip (P := pseq P _)),
         ⟨_, hP, hden⟩, ?_⟩⟩
      rw [seq_B_right]
      exact le_trans (seq_mono_right _ hMle) (seq_mono_right _ hle)
  | actWrong hE =>
      obtain ⟨e₀, hbound, htot, himp, hle⟩ := inv_act hj
      have hMle := hbound _ _ _ hP
      have hne : p.seq _ ≠ .E :=
        le_ne_E _ _ (le_trans (seq_mono_right _ hMle) (seq_mono_right _ hle)) hpe
      exact absurd hE hne
  | iteS s₁ s₂ hden hne =>
      rename_i C b σA σ'A
      obtain ⟨m₁, m₂, e₁, e₂, hb₁, hb₂, h₁, h₂, hle⟩ := inv_ite hj
      refine ⟨phase_step _ _ hp (hval.noY _ _ _) hne, .inl ?_⟩
      cases b with
      | true =>
          rw [if_pos rfl]
          exact ⟨pseq P (condA C true), e₁, h₁, ⟨_, hP, hden⟩,
            branch_bound (hb₁ _ _ _ hP) (le_trans (le_join_left _ _) hle)⟩
      | false =>
          rw [if_neg Bool.false_ne_true]
          exact ⟨pseq P (condA C false), e₂, h₂, ⟨_, hP, hden⟩,
            branch_bound (hb₂ _ _ _ hP) (le_trans (le_join_right _ _) hle)⟩
  | iteWrong s₁ s₂ hden hE =>
      rename_i C b σA σ'A
      obtain ⟨m₁, m₂, e₁, e₂, hb₁, hb₂, h₁, h₂, hle⟩ := inv_ite hj
      exfalso
      cases b with
      | true =>
          have h1 : p.seq (m₁.seq e₁) ≠ .E :=
            seq_ne_E_mono (le_refl p) (le_trans (le_join_left _ _) hle) hpe
          have h2 : (p.seq m₁).seq e₁ ≠ .E := by
            rw [Effect.seq_assoc]; exact h1
          have h3 : p.seq m₁ ≠ .E := by
            intro hEq
            rw [hEq] at h2
            exact h2 rfl
          exact le_ne_E _ _ (seq_mono_right _ (hb₁ _ _ _ hP)) h3 hE
      | false =>
          have h1 : p.seq (m₂.seq e₂) ≠ .E :=
            seq_ne_E_mono (le_refl p) (le_trans (le_join_right _ _) hle) hpe
          have h2 : (p.seq m₂).seq e₂ ≠ .E := by
            rw [Effect.seq_assoc]; exact h1
          have h3 : p.seq m₂ ≠ .E := by
            intro hEq
            rw [hEq] at h2
            exact h2 rfl
          exact le_ne_E _ _ (seq_mono_right _ (hb₂ _ _ _ hP)) h3 hE
  | wloopUnfold C s₀ =>
      obtain ⟨Pinv, m₁, m₂, e₁, hPi, hb₁, hb₂, hbody, hnl, hpost, hle⟩ :=
        inv_wloop hj
      have hwl : Judg D M R G (.wloop C s₀) Pinv Q ((m₁.seq e₁).star.seq m₂) :=
        .conseq (PImp.refl _) hpost (RImp.refl _) (RImp.refl _) (le_refl _)
          (.wloopJ hb₁ hb₂ hbody hnl)
      have hbranch₁ : Judg D M R G (.seq s₀ (.wloop C s₀))
          (pseq Pinv (condA C true)) Q (e₁.seq ((m₁.seq e₁).star.seq m₂)) :=
        .seqJ hbody hwl
      have hbranch₂ : Judg D M R G .skip (pseq Pinv (condA C false)) Q .B :=
        .conseq (PImp.refl _) hpost (RImp.refl _) (RImp.refl _) (le_refl _)
          (Judg.skip (P := pseq Pinv (condA C false)))
      exact ⟨hp, .inl ⟨Pinv, _, .iteJ hb₁ hb₂ hbranch₁ hbranch₂,
        hPi _ _ _ hP,
        le_trans (seq_mono_right _ (wloop_unfold_le _ _ _ hnl))
          (seq_mono_right _ hle)⟩⟩
  | call hf =>
      rename_i f body σA
      have hDf : ∃ sp, D f = some (sp, body) := by
        simp only [Decls.fns, Option.map_eq_some'] at hf
        obtain ⟨pr, hpr, hpr2⟩ := hf
        exact ⟨pr.1, by rw [hpr]; cases pr; cases hpr2; rfl⟩
      obtain ⟨sp, hDf⟩ := hDf
      cases inv_call hj with
      | inl hc =>
          obtain ⟨e₀, S, Qf, body', hDf', hS, himp, hle⟩ := hc
          rw [hDf] at hDf'
          injection hDf' with h'
          injection h' with hsp hbody
          subst hsp
          subst hbody
          cases hD f _ _ hDf with
          | atomic hcf hbj =>
              have hpre := prefix_lemma hbj hcf (RImp.refl _) P R G
              refine ⟨hp, .inl ⟨P, e₀,
                .conseq (P' := pcomp P (Two S)) ?_ himp (RImp.refl _)
                  (RImp.refl _) (le_refl _) hpre,
                hP, seq_mono_right _ hle⟩⟩
              exact fun t' a b hp' => ⟨b, hp', rfl, hS t' a b hp'⟩
      | inr hc =>
          obtain ⟨Rf, Gf, S, T, body', hDf', hRf, hGf, hpre, hpost, hle⟩ := hc
          rw [hDf] at hDf'
          injection hDf' with h'
          injection h' with hsp hbody
          subst hsp
          subst hbody
          cases hD f _ _ hDf with
          | nonatomic hbj =>
              exact ⟨hp, .inl ⟨P, e,
                .conseq hpre hpost hRf hGf hle hbj, hP, le_refl _⟩⟩

/-! ### The [I-state] judgment `⊢ Π` -/

/-- Per-thread invariant of a verified instrumented state: `act` is the
    (at most one) unparked thread, `σ₀` the store at the start of its
    current reducible sequence — which is also the last store the other
    (parked) threads have observed.  (If `act` is out of range — e.g.
    an empty pool — no sequence is in flight and `σ₀` is the current
    store.) -/
def ThreadsInv (D : Decls) (M : MSpec) (R G : Rel) (act : Tid) (σ₀ : Store)
    (ths : List (Effect × Stmt)) (σ : Store) : Prop :=
  (ths.get? act = none → σ₀ = σ) ∧
  ∀ i p s, ths.get? i = some (p, s) →
    ∃ P Q e, Judg D M R G s P Q e ∧ p.seq e ≠ .E ∧ (p = .R ∨ p = .N) ∧
      (∀ t a b, Q t a b → G t a b) ∧
      (i = act → P i σ₀ σ) ∧
      (i ≠ act → Yielding s ∧ ∃ σp, P i σp σ₀)

/-- `⊢ Π` (paper Figure 10, [I-state]). -/
structure IStateOK (D : Decls) (M : MSpec) (R G : Rel) (c : IState) : Prop where
  fnsOK : DeclsOK D M
  valid : Valid M
  Grefl : ∀ t σ, G t σ σ
  compat : ∀ t u, t ≠ u → ∀ a b, G t a b → R u a b
  inv : ∃ act σ₀, ThreadsInv D M R G act σ₀ c.ths c.store

/-! ### Theorem 6: verified states are not wrong -/

theorem atYield_not_wrong {s : Stmt} (hy : AtYield s) : ¬ IsWrong s := by
  induction hy with
  | yld => intro hw; cases hw
  | seq s₂ _ ih => intro hw; cases hw with | seq _ hw' => exact ih hw'

theorem yielding_not_wrong {s : Stmt} (hy : Yielding s) : ¬ IsWrong s := by
  cases hy with
  | inl hat => exact atYield_not_wrong hat
  | inr hskip => subst hskip; intro hw; cases hw

theorem istateok_not_wrong {D M R G c} (hok : IStateOK D M R G c) :
    ¬ IStateWrong c := by
  rintro ⟨⟨p, s⟩, hmem, hw⟩
  obtain ⟨act, σ₀, _, hinv⟩ := hok.inv
  obtain ⟨i, hget⟩ := List.get?_of_mem hmem
  obtain ⟨P, Q, e, hj, _, _, _, hact, hother⟩ := hinv i p s hget
  by_cases hi : i = act
  · exact judg_wrong_empty hw hj i σ₀ c.store (hact hi)
  · exact yielding_not_wrong (hother hi).1 hw

/-! ### Theorem 5: preservation (with Lemma 17, Context Switch) -/

/-- Lemma 17 (Context Switch): when the active thread is parked, the
    invariant can be re-based at the current store with any thread as
    the new active thread. -/
theorem context_switch {D M R G act σ₀ ths σ}
    (hGrefl : ∀ t σ', G t σ' σ')
    (hcompat : ∀ t u, t ≠ u → ∀ a b, G t a b → R u a b)
    (hinv : ThreadsInv D M R G act σ₀ ths σ)
    (hpark : ∀ p s, ths.get? act = some (p, s) → Yielding s)
    (u : Tid) :
    ThreadsInv D M R G u σ ths σ := by
  obtain ⟨hbase, hinv⟩ := hinv
  -- the finished sequence σ₀ → σ of the old active thread is visible
  -- to every other thread's rely (or the store never moved at all)
  have hR : ∀ i, i ≠ act → RStar R i σ₀ σ := by
    intro i hi
    cases hg : ths.get? act with
    | none => rw [hbase hg]; exact Multi.refl σ
    | some pr =>
        obtain ⟨P, Q, e, hj, _, _, hQG, hact, _⟩ := hinv act pr.1 pr.2 hg
        have hG : G act σ₀ σ :=
          publish_yielding (hpark pr.1 pr.2 hg) hj hQG act σ₀ σ (hact rfl)
        exact Multi.head (hcompat act i (fun h => hi h.symm) σ₀ σ hG) (Multi.refl σ)
  refine ⟨fun _ => rfl, ?_⟩
  intro i p s hget
  obtain ⟨P, Q, e, hj, hpe, hph, hQG, hact, hother⟩ := hinv i p s hget
  have hyi : Yielding s := by
    by_cases hi : i = act
    · subst hi; exact hpark p s hget
    · exact (hother hi).1
  obtain ⟨Q', hj', hQ'G⟩ := stabilize_yielding hyi hj hQG hGrefl
  have hstab : yieldP P R i σ σ := by
    by_cases hi : i = act
    · subst hi; exact ⟨rfl, σ, ⟨σ₀, hact rfl⟩, Multi.refl σ⟩
    · obtain ⟨_, σp, hPp⟩ := hother hi
      exact ⟨rfl, σ₀, ⟨σp, hPp⟩, hR i hi⟩
  exact ⟨yieldP P R, Q', e, hj', hpe, hph, hQ'G,
    fun _ => hstab, fun _ => ⟨hyi, σ, hstab⟩⟩

/-- Theorem 5 (Preservation): `⊢ Π` is preserved by non-preemptive steps. -/
theorem npstep_preserve {D : Decls} {M R G c c'} (hok : IStateOK D M R G c)
    (hstep : npstep D.fns M c c') : IStateOK D M R G c' := by
  obtain ⟨act, σ₀, hbase, hinv⟩ := hok.inv
  cases hstep with
  | mk t hget histep hpark =>
    rename_i ths σ σ' p s p' s'
    -- re-base the invariant so that `t` is the active thread
    have huni : ∃ σ₀', ThreadsInv D M R G t σ₀' ths σ := by
      by_cases ht : t = act
      · exact ⟨σ₀, ht ▸ ⟨hbase, hinv⟩⟩
      · refine ⟨σ, context_switch hok.Grefl hok.compat ⟨hbase, hinv⟩ ?_ t⟩
        intro pa sa hga
        have hparked : Parked sa :=
          hpark act (pa, sa) (fun h => ht h.symm) hga
        obtain ⟨P, Q, e, hj, _, _, _, hact, _⟩ := hinv act pa sa hga
        cases hparked with
        | inl hat => exact Or.inl hat
        | inr h' =>
            cases h' with
            | inl hskip => exact Or.inr hskip
            | inr hw =>
                exact absurd (hact rfl) (judg_wrong_empty hw hj act σ₀ σ)
    obtain ⟨σ₀', hbase', hinv'⟩ := huni
    obtain ⟨P, Q, e, hj, hpe, hph, hQG, hact', _⟩ := hinv' t p s hget
    have hPt : P t σ₀' σ := hact' rfl
    obtain ⟨hph', hout⟩ :=
      istep_preserve hok.valid hok.fnsOK histep hj hPt hph hpe
    have hlt : t < ths.length := get?_lt hget
    refine ⟨hok.fnsOK, hok.valid, hok.Grefl, hok.compat, ?_⟩
    cases hout with
    | inl hA =>
        obtain ⟨P', e', hj', hP', hb⟩ := hA
        refine ⟨t, σ₀', ?_, ?_⟩
        · intro h
          rw [get?_set_self hlt] at h
          exact Option.noConfusion h
        · intro i pi si hgeti
          by_cases hi : i = t
          · subst hi
            rw [get?_set_self hlt] at hgeti
            cases hgeti
            exact ⟨P', Q, e', hj', le_ne_E _ _ hb hpe, hph', hQG,
              fun _ => hP', fun hne => absurd rfl hne⟩
          · rw [get?_set_other (fun h => hi h.symm)] at hgeti
            obtain ⟨Pi, Qi, ei, hji, hpei, hphi, hQiG, _, hotheri⟩ :=
              hinv' i pi si hgeti
            exact ⟨Pi, Qi, ei, hji, hpei, hphi, hQiG,
              fun h => absurd h hi, fun _ => hotheri hi⟩
    | inr hB =>
        obtain ⟨hσ, hpR, hGpub, P', e', hj', hP', hb⟩ := hB
        subst hσ
        refine ⟨t, σ', ?_, ?_⟩
        · intro h
          rw [get?_set_self hlt] at h
        · intro i pi si hgeti
          by_cases hi : i = t
          · subst hi
            rw [get?_set_self hlt] at hgeti
            cases hgeti
            exact ⟨P', Q, e', hj', le_ne_E _ _ hb hpe, hph', hQG,
              fun _ => hP', fun hne => absurd rfl hne⟩
          · rw [get?_set_other (fun h => hi h.symm)] at hgeti
            obtain ⟨Pi, Qi, ei, hji, hpei, hphi, hQiG, _, hotheri⟩ :=
              hinv' i pi si hgeti
            obtain ⟨hyi, σp, hPpi⟩ := hotheri hi
            obtain ⟨Qi', hji', hQi'G⟩ :=
              stabilize_yielding hyi hji hQiG hok.Grefl
            have hstab : yieldP Pi R i σ' σ' :=
              ⟨rfl, σ₀', ⟨σp, hPpi⟩,
               Multi.head (hok.compat t i (fun h => hi h.symm) σ₀' σ' hGpub)
                 (Multi.refl σ')⟩
            exact ⟨yieldP Pi R, Qi', ei, hji', hpei, hphi, hQi'G,
              fun h => absurd h hi, fun _ => ⟨hyi, σ', hstab⟩⟩

/-- Preservation along any non-preemptive execution. -/
theorem npmulti_preserve {D : Decls} {M R G c c'} (hok : IStateOK D M R G c)
    (hsteps : Multi (npstep D.fns M) c c') : IStateOK D M R G c' := by
  induction hsteps with
  | refl => exact hok
  | head hstep _ ih => exact ih (npstep_preserve hok hstep)

/-- Soundness for the cooperative (non-preemptive) scheduler: verified
    states never go wrong. -/
theorem cooperative_soundness {D : Decls} {M R G c} (hok : IStateOK D M R G c) :
    ¬ NGoesWrong D.fns M c := by
  rintro ⟨c', hsteps, hwrong⟩
  exact istateok_not_wrong (npmulti_preserve hok hsteps) hwrong

end MoverRust
