/-
  MoverRust / Meta — inversion and structural lemmas for the judgment

  These play the role of the paper's Lemma 12 (Evaluation Context) and
  Lemma 13 (Consequence): with a structural small-step semantics, what
  is needed is inversion of `Judg` modulo [M-conseq] for each statement
  form, plus:

  ▸ Lemma 16 (Prefix) — an atomic function body verified under the
    empty rely/guarantee can be spliced into any calling context;
  ▸ `judg_wrong_empty` — a thread whose redex is `wrong` has an
    unsatisfiable precondition (the core of Theorem 6).
-/
import MoverRust.Instrumented

namespace MoverRust

open Effect

/-! ### Predicate calculus -/

theorem PImp.refl (P : Pred) : PImp P P := fun _ _ _ h => h

theorem PImp.trans {P Q R : Pred} (h₁ : PImp P Q) (h₂ : PImp Q R) : PImp P R :=
  fun t a b h => h₂ t a b (h₁ t a b h)

theorem RImp.refl (R : Rel) : RImp R R := fun _ _ _ h => h

theorem RImp.trans {R S T : Rel} (h₁ : RImp R S) (h₂ : RImp S T) : RImp R T :=
  fun t a b h => h₂ t a b (h₁ t a b h)

theorem pseq_mono {P P' : Pred} (A : Act) (h : PImp P P') :
    PImp (pseq P A) (pseq P' A) := by
  rintro t a b ⟨σ, hP, hden⟩; exact ⟨σ, h _ _ _ hP, hden⟩

theorem pcomp_mono {P P' Q Q' : Pred} (h₁ : PImp P P') (h₂ : PImp Q Q') :
    PImp (pcomp P Q) (pcomp P' Q') := by
  rintro t a b ⟨σ, hP, hQ⟩; exact ⟨σ, h₁ _ _ _ hP, h₂ _ _ _ hQ⟩

theorem pcomp_pseq (Pc P : Pred) (A : Act) :
    PImp (pcomp Pc (pseq P A)) (pseq (pcomp Pc P) A) := by
  rintro t a b ⟨σ, hPc, σ', hP, hden⟩; exact ⟨σ', ⟨σ, hPc, hP⟩, hden⟩

theorem pseq_pcomp (Pc P : Pred) (A : Act) :
    PImp (pseq (pcomp Pc P) A) (pcomp Pc (pseq P A)) := by
  rintro t a b ⟨σ', ⟨σ, hPc, hP⟩, hden⟩; exact ⟨σ, hPc, σ', hP, hden⟩

theorem RStar.trans {R : Rel} {t : Tid} {a b c : Store} :
    RStar R t a b → RStar R t b c → RStar R t a c := Multi.trans

theorem RStar.mono {R R' : Rel} (h : RImp R R') {t a b} :
    RStar R t a b → RStar R' t a b := by
  intro hs
  induction hs with
  | refl => exact .refl _
  | head hstep _ ih => exact .head (h _ _ _ hstep) ih

theorem yieldP_mono {P P' : Pred} {R R' : Rel} (hP : PImp P P') (hR : RImp R R') :
    PImp (yieldP P R) (yieldP P' R') := by
  rintro t a b ⟨rfl, σ, ⟨σ₀, hPh⟩, hst⟩
  exact ⟨rfl, σ, ⟨σ₀, hP _ _ _ hPh⟩, RStar.mono hR hst⟩

/-- Stabilizing twice adds nothing (star transitivity). -/
theorem yieldP_yieldP {P : Pred} {R : Rel} :
    PImp (yieldP (yieldP P R) R) (yieldP P R) := by
  rintro t a b ⟨rfl, σ, ⟨σ₀, rfl, σ₁, hP, hst₁⟩, hst₂⟩
  exact ⟨rfl, σ₁, hP, RStar.trans hst₁ hst₂⟩

/-! ### Inversion lemmas (Lemmas 12–13, structurally) -/

theorem inv_skip {D M R G P Q e} (h : Judg D M R G .skip P Q e) :
    PImp P Q ∧ .B ≤ e := by
  generalize hs : Stmt.skip = s at h
  revert hs
  induction h with
  | skip => exact fun _ => ⟨PImp.refl _, Effect.le_refl _⟩
  | conseq hP hQ hR hG he _ ih =>
      intro hs
      obtain ⟨h₁, h₂⟩ := ih hs
      exact ⟨PImp.trans hP (PImp.trans h₁ hQ), Effect.le_trans h₂ he⟩
  | _ => intro hs; cases hs

theorem inv_wrong {D M R G P Q e} (h : Judg D M R G .wrong P Q e) :
    PImp P pFalse := by
  generalize hs : Stmt.wrong = s at h
  revert hs
  induction h with
  | wrong => exact fun _ => PImp.refl _
  | conseq hP _ _ _ _ _ ih => exact fun hs => PImp.trans hP (ih hs)
  | _ => intro hs; cases hs

theorem inv_act {D M R G A P Q e} (h : Judg D M R G (.act A) P Q e) :
    ∃ e', (∀ t σ₀ σ, P t σ₀ σ → M A t σ ≤ e') ∧ (e' ≤ .L → total A) ∧
      PImp (pseq P A) Q ∧ e' ≤ e := by
  generalize hs : Stmt.act A = s at h
  revert hs
  induction h with
  | act hbound htot =>
      intro hs
      cases hs
      exact ⟨_, hbound, htot, PImp.refl _, Effect.le_refl _⟩
  | conseq hP hQ hR hG he _ ih =>
      intro hs
      obtain ⟨e', hb, ht, hi, hle⟩ := ih hs
      exact ⟨e', fun t a b hp => hb t a b (hP _ _ _ hp), ht,
        PImp.trans (pseq_mono _ hP) (PImp.trans hi hQ), Effect.le_trans hle he⟩
  | _ => intro hs; cases hs

theorem inv_seq {D M R G s₁ s₂ P Q e} (h : Judg D M R G (.seq s₁ s₂) P Q e) :
    ∃ Q₁ e₁ e₂, Judg D M R G s₁ P Q₁ e₁ ∧ Judg D M R G s₂ Q₁ Q e₂ ∧
      e₁.seq e₂ ≤ e := by
  generalize hs : Stmt.seq s₁ s₂ = s at h
  revert hs
  induction h with
  | seqJ h₁ h₂ =>
      intro hs
      cases hs
      exact ⟨_, _, _, h₁, h₂, Effect.le_refl _⟩
  | conseq hP hQ hR hG he _ ih =>
      intro hs
      obtain ⟨Q₁, e₁, e₂, h₁, h₂, hle⟩ := ih hs
      exact ⟨Q₁, e₁, e₂,
        .conseq hP (PImp.refl _) hR hG (Effect.le_refl _) h₁,
        .conseq (PImp.refl _) hQ hR hG (Effect.le_refl _) h₂,
        Effect.le_trans hle he⟩
  | _ => intro hs; cases hs

theorem inv_ite {D M R G C s₁ s₂ P Q e} (h : Judg D M R G (.ite C s₁ s₂) P Q e) :
    ∃ m₁ m₂ e₁ e₂,
      (∀ t σ₀ σ, P t σ₀ σ → M (condA C true) t σ ≤ m₁) ∧
      (∀ t σ₀ σ, P t σ₀ σ → M (condA C false) t σ ≤ m₂) ∧
      Judg D M R G s₁ (pseq P (condA C true)) Q e₁ ∧
      Judg D M R G s₂ (pseq P (condA C false)) Q e₂ ∧
      (m₁.seq e₁).join (m₂.seq e₂) ≤ e := by
  generalize hs : Stmt.ite C s₁ s₂ = s at h
  revert hs
  induction h with
  | iteJ hb₁ hb₂ h₁ h₂ =>
      intro hs
      cases hs
      exact ⟨_, _, _, _, hb₁, hb₂, h₁, h₂, Effect.le_refl _⟩
  | conseq hP hQ hR hG he _ ih =>
      intro hs
      obtain ⟨m₁, m₂, e₁, e₂, hb₁, hb₂, h₁, h₂, hle⟩ := ih hs
      exact ⟨m₁, m₂, e₁, e₂,
        fun t a b hp => hb₁ t a b (hP _ _ _ hp),
        fun t a b hp => hb₂ t a b (hP _ _ _ hp),
        .conseq (pseq_mono _ hP) hQ hR hG (Effect.le_refl _) h₁,
        .conseq (pseq_mono _ hP) hQ hR hG (Effect.le_refl _) h₂,
        Effect.le_trans hle he⟩
  | _ => intro hs; cases hs

theorem inv_wloop {D M R G C s₀ P Q e} (h : Judg D M R G (.wloop C s₀) P Q e) :
    ∃ Pinv m₁ m₂ e₁,
      PImp P Pinv ∧
      (∀ t σ₀ σ, Pinv t σ₀ σ → M (condA C true) t σ ≤ m₁) ∧
      (∀ t σ₀ σ, Pinv t σ₀ σ → M (condA C false) t σ ≤ m₂) ∧
      Judg D M R G s₀ (pseq Pinv (condA C true)) Pinv e₁ ∧
      ¬ (((m₁.seq e₁).star.seq m₂) ≤ .L) ∧
      PImp (pseq Pinv (condA C false)) Q ∧
      ((m₁.seq e₁).star.seq m₂) ≤ e := by
  generalize hs : Stmt.wloop C s₀ = s at h
  revert hs
  induction h with
  | wloopJ hb₁ hb₂ hbody hnl =>
      intro hs
      cases hs
      exact ⟨_, _, _, _, PImp.refl _, hb₁, hb₂, hbody, hnl,
        PImp.refl _, Effect.le_refl _⟩
  | conseq hP hQ hR hG he _ ih =>
      intro hs
      obtain ⟨Pinv, m₁, m₂, e₁, hPi, hb₁, hb₂, hbody, hnl, hpost, hle⟩ := ih hs
      exact ⟨Pinv, m₁, m₂, e₁, PImp.trans hP hPi, hb₁, hb₂,
        .conseq (PImp.refl _) (PImp.refl _) hR hG (Effect.le_refl _) hbody,
        hnl, PImp.trans hpost hQ, Effect.le_trans hle he⟩
  | _ => intro hs; cases hs

theorem inv_yld {D M R G P Q e} (h : Judg D M R G .yld P Q e) :
    (∀ t σ₀ σ, P t σ₀ σ → G t σ₀ σ) ∧ PImp (yieldP P R) Q := by
  generalize hs : Stmt.yld = s at h
  revert hs
  induction h with
  | yieldJ hPG => exact fun _ => ⟨hPG, PImp.refl _⟩
  | conseq hP hQ hR hG he _ ih =>
      intro hs
      obtain ⟨hPG, himp⟩ := ih hs
      refine ⟨fun t a b hp => hG _ _ _ (hPG t a b (hP _ _ _ hp)), ?_⟩
      exact PImp.trans (yieldP_mono hP hR) (PImp.trans himp hQ)
  | _ => intro hs; cases hs

theorem inv_call {D M R G f P Q e} (h : Judg D M R G (.call f) P Q e) :
    (∃ e' S Qf body, D f = some (.atomicSpec e' S Qf, body) ∧
      (∀ t σ₀ σ, P t σ₀ σ → S t σ) ∧ PImp (pcomp P Qf) Q ∧ e' ≤ e) ∨
    (∃ Rf Gf S T body, D f = some (.rgSpec Rf Gf S T, body) ∧
      RImp R Rf ∧ RImp Gf G ∧ PImp P (Two S) ∧ PImp (Two T) Q ∧ .R ≤ e) := by
  generalize hs : Stmt.call f = s at h
  revert hs
  induction h with
  | callAtomic hD hS =>
      intro hs
      cases hs
      exact .inl ⟨_, _, _, _, hD, hS, PImp.refl _, Effect.le_refl _⟩
  | callNonAtomic hD =>
      intro hs
      cases hs
      exact .inr ⟨_, _, _, _, _, hD, RImp.refl _, RImp.refl _,
        PImp.refl _, PImp.refl _, Effect.le_refl _⟩
  | conseq hP hQ hR hG he _ ih =>
      intro hs
      cases ih hs with
      | inl hc =>
          obtain ⟨e', S, Qf, body, hD, hS, himp, hle⟩ := hc
          exact .inl ⟨e', S, Qf, body, hD,
            fun t a b hp => hS t a b (hP _ _ _ hp),
            PImp.trans (pcomp_mono hP (PImp.refl _)) (PImp.trans himp hQ),
            Effect.le_trans hle he⟩
      | inr hc =>
          obtain ⟨Rf, Gf, S, T, body, hD, hRf, hGf, hpre, hpost, hle⟩ := hc
          exact .inr ⟨Rf, Gf, S, T, body, hD, RImp.trans hR hRf,
            RImp.trans hGf hG, PImp.trans hP hpre, PImp.trans hpost hQ,
            Effect.le_trans hle he⟩
  | _ => intro hs; cases hs

/-! ### Wrong threads have empty preconditions (Theorem 6, thread level) -/

theorem judg_wrong_empty {D M R G s P Q e} (hw : IsWrong s)
    (h : Judg D M R G s P Q e) : ∀ t σ₀ σ, ¬ P t σ₀ σ := by
  induction hw generalizing R G P Q e with
  | wrong => exact fun t σ₀ σ hp => inv_wrong h t σ₀ σ hp
  | seq s₂ _ ih =>
      obtain ⟨Q₁, e₁, e₂, h₁, _, _⟩ := inv_seq h
      exact fun t σ₀ σ hp => ih h₁ t σ₀ σ hp

/-! ### The Prefix lemma (Lemma 16)

An atomic function body — call-free, verified under the empty
rely/guarantee — can run in the middle of any reducible sequence: its
judgment can be prefixed by an arbitrary predicate `Pc` and re-hosted
under any `R`, `G`. -/

theorem prefix_lemma {D M R₀ G₀ s P₀ Q₀ e} (h : Judg D M R₀ G₀ s P₀ Q₀ e)
    (hcf : CallFree s) (hG₀ : RImp G₀ emptyRel) :
    ∀ (Pc : Pred) (R G : Rel), Judg D M R G s (pcomp Pc P₀) (pcomp Pc Q₀) e := by
  induction h with
  | skip => exact fun Pc R G => .skip
  | wrong =>
      intro Pc R G
      refine .conseq (P' := pFalse) (Q' := pFalse) ?_
        (fun t a b hf => hf.elim) (RImp.refl _) (RImp.refl _)
        (Effect.le_refl _) .wrong
      rintro t a b ⟨σ, _, hf⟩; exact hf.elim
  | act hbound htot =>
      intro Pc R G
      refine .conseq (PImp.refl _) (pseq_pcomp _ _ _) (RImp.refl _)
        (RImp.refl _) (Effect.le_refl _) ?_
      refine .act (fun t a b hp => ?_) htot
      obtain ⟨σ, _, hP⟩ := hp
      exact hbound t σ b hP
  | seqJ h₁ h₂ ih₁ ih₂ =>
      exact fun Pc R G => .seqJ (ih₁ hcf.1 hG₀ Pc R G) (ih₂ hcf.2 hG₀ Pc R G)
  | iteJ hb₁ hb₂ h₁ h₂ ih₁ ih₂ =>
      intro Pc R G
      refine .iteJ (fun t a b hp => ?_) (fun t a b hp => ?_)
        (.conseq (pseq_pcomp _ _ _) (PImp.refl _) (RImp.refl _) (RImp.refl _)
          (Effect.le_refl _) (ih₁ hcf.1 hG₀ Pc R G))
        (.conseq (pseq_pcomp _ _ _) (PImp.refl _) (RImp.refl _) (RImp.refl _)
          (Effect.le_refl _) (ih₂ hcf.2 hG₀ Pc R G))
      · obtain ⟨σ, _, hP⟩ := hp; exact hb₁ t σ b hP
      · obtain ⟨σ, _, hP⟩ := hp; exact hb₂ t σ b hP
  | wloopJ hb₁ hb₂ hbody hnl ih =>
      intro Pc R G
      refine .conseq (PImp.refl _) (pseq_pcomp _ _ _) (RImp.refl _)
        (RImp.refl _) (Effect.le_refl _) ?_
      refine .wloopJ (fun t a b hp => ?_) (fun t a b hp => ?_)
        (.conseq (pseq_pcomp _ _ _) (PImp.refl _) (RImp.refl _) (RImp.refl _)
          (Effect.le_refl _) (ih hcf hG₀ Pc R G)) hnl
      · obtain ⟨σ, _, hP⟩ := hp; exact hb₁ t σ b hP
      · obtain ⟨σ, _, hP⟩ := hp; exact hb₂ t σ b hP
  | yieldJ hPG =>
      intro Pc R G
      refine .conseq (P' := pFalse) (Q' := yieldP pFalse R) ?_ ?_
        (RImp.refl _) (RImp.refl _) (Effect.le_refl _)
        (.yieldJ (fun t a b hf => hf.elim))
      · rintro t a b ⟨σ, _, hP⟩; exact (hG₀ _ _ _ (hPG _ _ _ hP)).elim
      · rintro t a b ⟨_, σ, ⟨σ₀, hf⟩, _⟩; exact hf.elim
  | callAtomic hD hS => exact absurd hcf (fun h => h)
  | callNonAtomic hD => exact absurd hcf (fun h => h)
  | conseq hP hQ hR hG he hsub ih =>
      intro Pc R G
      exact .conseq (pcomp_mono (PImp.refl _) hP) (pcomp_mono (PImp.refl _) hQ)
        (RImp.refl _) (RImp.refl _) he
        (ih hcf (fun t a b hg => hG₀ _ _ _ (hG _ _ _ hg)) Pc R G)

end MoverRust
