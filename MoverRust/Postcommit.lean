/-
  MoverRust / Postcommit — Lemma 9 (Post-Commit Termination)

  Once a thread has committed (entered the post-commit phase `N`, running
  only left-movers), it must run to a park without blocking or diverging.
  This is the "left-movers terminate" property that lets a post-commit
  reduction sequence be merged into the main trace (paper Lemma 9).

  We prove it for **call-free** running code — procedures inlined — so
  the size metric is purely structural.  (The language keeps global and
  thread-local state, locks, `cas`, threads, conditionals, and loops;
  loops are excluded from post-commit by the [M-while] rule, not by the
  call-free restriction.)  The proof is progress + preservation, recursed
  on a structural size that each step strictly decreases.
-/
import MoverRust.Theorem4

namespace MoverRust
open Effect

/-- Structural size of a (call-free) statement, the termination metric. -/
def sizeS : Stmt → Nat
  | .skip => 0
  | .wrong => 0
  | .act _ => 1
  | .yld => 1
  | .seq s₁ s₂ => 1 + sizeS s₁ + sizeS s₂
  | .ite _ s₁ s₂ => 1 + sizeS s₁ + sizeS s₂
  | .wloop _ _ => 1
  | .call _ => 1

/-- Single-thread instrumented step (thread and function table fixed). -/
def IStepT (F : FnTable) (M : MSpec) (t : Tid) :
    (Effect × Stmt × Store) → (Effect × Stmt × Store) → Prop :=
  fun a b => istep F M t a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2

/-- A well-typed statement with a *satisfiable* precondition is not about
    to execute `wrong` (contrapositive of `judg_wrong_empty`). -/
theorem not_wrong_of_sat {D M R G s P Q e t σ₀ σ} (hj : Judg D M R G s P Q e)
    (hP : P t σ₀ σ) : ¬ IsWrong s :=
  fun hw => judg_wrong_empty hw hj t σ₀ σ hP

/-- Call-freeness is preserved by stepping. -/
theorem callfree_step {F M t p s σ p' s' σ'} (hcf : CallFree s)
    (h : istep F M t p s σ p' s' σ') : CallFree s' := by
  induction h with
  | seqSkip => exact hcf.2
  | seqCong _ _ ih => exact ⟨ih hcf.1, hcf.2⟩
  | yld => exact trivial
  | act => exact trivial
  | actWrong => exact trivial
  | iteS s₁ s₂ _ _ =>
      have h1 : CallFree s₁ := hcf.1
      have h2 : CallFree s₂ := hcf.2
      split <;> assumption
  | iteWrong => exact trivial
  | wloopUnfold => exact ⟨⟨hcf, hcf⟩, trivial⟩
  | call => exact absurd hcf (by simp [CallFree])

/-! ### Progress for post-commit code

From the post-commit phase `N`, a well-typed non-yielding statement can
take a non-wrong step (again from `N` to `N`) to a strictly smaller
statement. -/

theorem post_progress {D : Decls} {M R G s P Q e t σ σ₀} (hval : Valid M)
    (hj : Judg D M R G s P Q e) (heL : e ≤ .L) (hcf : CallFree s)
    (hP : P t σ₀ σ) :
    Yielding s ∨
      ∃ s' σ', istep D.fns M t .N s σ .N s' σ' ∧ ¬ IsWrong s' ∧ sizeS s' < sizeS s := by
  induction s generalizing P Q e σ with
  | skip => exact .inl (.inr rfl)
  | yld => exact .inl (.inl .yld)
  | wrong => exact absurd hP (inv_wrong hj t σ₀ σ)
  | act A =>
      obtain ⟨e', hbound, htot, himp, hle⟩ := inv_act hj
      have he'L : e' ≤ .L := le_trans hle heL
      obtain ⟨σ', hden⟩ := htot he'L t σ
      have hMle : M A t σ ≤ .L := le_trans (hbound t σ₀ σ hP) he'L
      have hstep : istep D.fns M t .N (.act A) σ (Effect.N.seq (M A t σ)) .skip σ' :=
        .act hden (N_seq_le_L_ne_E _ hMle)
      rw [N_seq_le_L_eq_N _ hMle (hval.noY A t σ)] at hstep
      exact .inr ⟨.skip, σ', hstep, (fun hw => nomatch hw), by simp [sizeS]⟩
  | seq s₁ s₂ ih₁ _ =>
      obtain ⟨Q₁, e₁, e₂, hj₁, hj₂, hle⟩ := inv_seq hj
      have he₁L : e₁ ≤ .L := seq_le_L_left (le_trans hle heL)
      cases ih₁ hj₁ he₁L hcf.1 hP with
      | inl hy₁ =>
          cases hy₁ with
          | inl hat₁ => exact .inl (.inl (.seq s₂ hat₁))
          | inr hsk₁ =>
              subst hsk₁
              have hQ₁ : Q₁ t σ₀ σ := (inv_skip hj₁).1 t σ₀ σ hP
              exact .inr ⟨s₂, σ, .seqSkip s₂, not_wrong_of_sat hj₂ hQ₁,
                by simp [sizeS]; omega⟩
      | inr hstep₁ =>
          obtain ⟨s₁', σ', hi₁, hnw₁, hsz₁⟩ := hstep₁
          refine .inr ⟨.seq s₁' s₂, σ', .seqCong s₂ hi₁, ?_, by simp [sizeS]; omega⟩
          intro hw; cases hw with | seq _ hw' => exact hnw₁ hw'
  | ite C s₁ s₂ _ _ =>
      obtain ⟨m₁, m₂, e₁, e₂, hb₁, hb₂, hj₁, hj₂, hle⟩ := inv_ite hj
      obtain ⟨b, σ', hden⟩ := cond_total C t σ
      have hjoinL : (m₁.seq e₁).join (m₂.seq e₂) ≤ .L := le_trans hle heL
      have hm₁L : m₁ ≤ .L := seq_le_L_left (le_trans (le_join_left _ _) hjoinL)
      have hm₂L : m₂ ≤ .L := seq_le_L_left (le_trans (le_join_right _ _) hjoinL)
      have hmle : M (condA C b) t σ ≤ .L := by
        cases b with
        | true => exact le_trans (hb₁ t σ₀ σ hP) hm₁L
        | false => exact le_trans (hb₂ t σ₀ σ hP) hm₂L
      have hstep : istep D.fns M t .N (.ite C s₁ s₂) σ
          (Effect.N.seq (M (condA C b) t σ)) (if b then s₁ else s₂) σ' :=
        .iteS s₁ s₂ hden (N_seq_le_L_ne_E _ hmle)
      rw [N_seq_le_L_eq_N _ hmle (hval.noY _ t σ)] at hstep
      have hnw : ¬ IsWrong (if b then s₁ else s₂) := by
        cases b with
        | true => rw [if_pos rfl]
                  exact not_wrong_of_sat hj₁ ⟨σ, hP, hden⟩
        | false => rw [if_neg Bool.false_ne_true]
                   exact not_wrong_of_sat hj₂ ⟨σ, hP, hden⟩
      refine .inr ⟨if b then s₁ else s₂, σ', hstep, hnw, ?_⟩
      cases b <;> simp [sizeS] <;> omega
  | wloop C s _ =>
      obtain ⟨Pinv, m₁, m₂, e₁, hPi, hb₁, hb₂, hbody, hnl, hpost, hle⟩ := inv_wloop hj
      exact absurd (le_trans hle heL) hnl
  | call f => exact absurd hcf (by simp [CallFree])

/-! ### Lemma 9 — Post-Commit Termination

A well-typed, call-free post-commit thread runs (non-preemptively, by
itself) to a yielding state. -/

theorem post_terminates {D : Decls} {M R G t σ₀} (hval : Valid M) (hD : DeclsOK D M) :
    ∀ (n : Nat) (s : Stmt), sizeS s ≤ n → ∀ σ P Q e, Judg D M R G s P Q e →
      Effect.N.seq e ≠ .E → CallFree s → P t σ₀ σ →
      ∃ s' σ', Multi (IStepT D.fns M t) (.N, s, σ) (.N, s', σ') ∧ Yielding s' := by
  intro n
  induction n with
  | zero =>
      intro s hsz σ P Q e hj hne hcf hP
      -- size 0: only skip/wrong survive; wrong is excluded, skip is yielding
      cases s with
      | skip => exact ⟨.skip, σ, .refl _, .inr rfl⟩
      | wrong => exact absurd hP (inv_wrong hj t σ₀ σ)
      | act A => simp only [sizeS] at hsz; omega
      | yld => simp only [sizeS] at hsz; omega
      | seq => simp only [sizeS] at hsz; omega
      | ite => simp only [sizeS] at hsz; omega
      | wloop => simp only [sizeS] at hsz; omega
      | call => simp only [sizeS] at hsz; omega
  | succ n ih =>
      intro s hsz σ P Q e hj hne hcf hP
      have heL : e ≤ .L := post_phase_le e hne
      cases post_progress hval hj heL hcf hP with
      | inl hy => exact ⟨s, σ, .refl _, hy⟩
      | inr hstep =>
          obtain ⟨s', σ', histep, hnw, hsz'⟩ := hstep
          -- preserve the judgment across the step
          obtain ⟨hph', hout⟩ :=
            istep_preserve hval hD histep hj hP (.inr rfl) hne
          have hpre : ∃ P' e', Judg D M R G s' P' Q e' ∧ P' t σ₀ σ' ∧
              Effect.N.seq e' ≠ .E := by
            cases hout with
            | inl h =>
                obtain ⟨P', e', hj', hP', hb⟩ := h
                exact ⟨P', e', hj', hP', Effect.le_ne_E _ _ hb hne⟩
            | inr h =>
                obtain ⟨_, hpR, _⟩ := h
                exact absurd hpR (by decide)
          obtain ⟨P', e', hj', hP', hne'⟩ := hpre
          have hcf' : CallFree s' := callfree_step hcf histep
          obtain ⟨s'', σ'', hmulti, hy⟩ :=
            ih s' (by omega) σ' P' Q e' hj' hne' hcf' hP'
          exact ⟨s'', σ'', .head
            (show IStepT D.fns M t (Effect.N, s, σ) (Effect.N, s', σ') from histep)
            hmulti, hy⟩

end MoverRust
