import Chapter06.DeBruijn

/-!
# Chapter 12: Normalization

Every well-typed program of the simply typed lambda-calculus **halts**
(TAPL theorem 12.1.6). The proof cannot be a plain induction on typing —
the `app` case needs to know more about the function than "it halts" — so
it introduces the celebrated method of **logical relations** (Tait's
method): a type-indexed predicate `R T t` combining "halts" with "maps
`R`-good arguments to `R`-good results", proved to be preserved both
forward and backward by evaluation, and then established for all
well-typed terms by a substitution-closing induction.

Following TAPL §12.1, the calculus is λ→ over an uninterpreted base type
`A`. We reuse the *untyped* terms of chapter 5 (and the substitution
algebra of chapter 6): the lambda is unannotated, so `T-Abs` guesses the
domain — harmless here, since nothing in this chapter needs uniqueness of
types.
-/

namespace Chapter12

open Chapter05 Chapter05.Term Chapter06

/-- Types: an uninterpreted base type `A` and arrows (TAPL §12.1). -/
inductive Ty : Type where
  | base
  | arrow (T₁ T₂ : Ty)
  deriving Repr, DecidableEq

/-- `T₁ ⇒ T₂` is the function type. -/
scoped infixr:60 " ⇒ " => Ty.arrow

/-- Typing contexts. -/
abbrev Ctx := List Ty

/-- The typing relation, over chapter 5's unannotated terms. -/
inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ : Ctx} {n : Nat} {T : Ty} :
      Γ.get? n = some T → HasType Γ (var n) T
  | abs {Γ : Ctx} {T₁ T₂ : Ty} {t : Term} :
      HasType (T₁ :: Γ) t T₂ → HasType Γ (ƛ t) (T₁ ⇒ T₂)
  | app {Γ : Ctx} {T₁ T₂ : Ty} {t₁ t₂ : Term} :
      HasType Γ t₁ (T₁ ⇒ T₂) → HasType Γ t₂ T₁ →
      HasType Γ (t₁ ⬝ t₂) T₂

@[inherit_doc] scoped notation:40 Γ " ⊢ " t " ∶ " T => HasType Γ t T

/-! ## Context insertion, weakening, substitution, preservation

The standard chapter-9 metatheory, for this term language (only
`var`/`abs`/`app`, so the proofs are short). -/

/-- Insert type `S` at position `c` of the context. -/
def insertAt (S : Ty) : Nat → Ctx → Ctx
  | 0, Γ => S :: Γ
  | _ + 1, [] => []
  | c + 1, T :: Γ => T :: insertAt S c Γ

theorem get?_insertAt_lt (S : Ty) :
    ∀ c Γ n, n < c → (insertAt S c Γ).get? n = Γ.get? n := by
  intro c
  induction c with
  | zero => intro Γ n h; omega
  | succ c ih =>
      intro Γ n h
      cases Γ with
      | nil => rfl
      | cons T Γ =>
          cases n with
          | zero => rfl
          | succ n => exact ih Γ n (by omega)

theorem get?_insertAt_ge (S : Ty) :
    ∀ c Γ n T, Γ.get? n = some T → c ≤ n →
      (insertAt S c Γ).get? (n + 1) = some T := by
  intro c
  induction c with
  | zero => intro Γ n T h _; exact h
  | succ c ih =>
      intro Γ n T h hc
      cases Γ with
      | nil => cases h
      | cons B Γ =>
          cases n with
          | zero => omega
          | succ n => exact ih Γ n T h (by omega)

theorem get?_insertAt_self (S : Ty) :
    ∀ c Γ T, (insertAt S c Γ).get? c = some T → T = S ∧ c ≤ Γ.length := by
  intro c
  induction c with
  | zero =>
      intro Γ T h
      cases h
      exact ⟨rfl, by omega⟩
  | succ c ih =>
      intro Γ T h
      cases Γ with
      | nil => cases h
      | cons B Γ =>
          obtain ⟨rfl, hle⟩ := ih Γ T h
          refine ⟨rfl, ?_⟩
          simp [List.length]
          omega

theorem get?_insertAt_gt (S : Ty) :
    ∀ c Γ n T, (insertAt S c Γ).get? n = some T → c < n →
      Γ.get? (n - 1) = some T := by
  intro c
  induction c with
  | zero =>
      intro Γ n T h hc
      cases n with
      | zero => omega
      | succ m => exact h
  | succ c ih =>
      intro Γ n T h hc
      cases Γ with
      | nil => cases h
      | cons B Γ =>
          cases n with
          | zero => omega
          | succ m =>
              cases m with
              | zero => omega
              | succ m' => exact ih Γ (m' + 1) T h (by omega)

/-- Weakening (shift-typing). -/
theorem weakening {Γ : Ctx} {t : Term} {T : Ty} (h : Γ ⊢ t ∶ T) :
    ∀ c S, insertAt S c Γ ⊢ shift 1 c t ∶ T := by
  induction h with
  | @var Γ n T hget =>
      intro c S
      by_cases hn : n < c
      · simp only [shift, if_pos hn]
        exact .var (by rw [get?_insertAt_lt S c Γ n hn]; exact hget)
      · simp only [shift, if_neg hn]
        exact .var (get?_insertAt_ge S c Γ n T hget (by omega))
  | abs _ ih => intro c S; exact .abs (ih (c + 1) S)
  | app _ _ ih₁ ih₂ => intro c S; exact .app (ih₁ c S) (ih₂ c S)

/-- Iterated weakening at the bottom of the context. -/
theorem shift0_typing :
    ∀ k (Γ : Ctx) (s : Term) (S : Ty), k ≤ Γ.length →
      (Γ.drop k ⊢ s ∶ S) → Γ ⊢ shift k 0 s ∶ S := by
  intro k
  induction k with
  | zero => intro Γ s S _ h; rw [shift_zero]; exact h
  | succ k ih =>
      intro Γ s S hk h
      cases Γ with
      | nil => simp at hk
      | cons B Γ =>
          have hw := weakening (ih Γ s S (by simp at hk; omega) h) 0 B
          rw [shift_merge s 1 k 0 0 (by omega) (by omega)] at hw
          have : 1 + k = k + 1 := by omega
          rw [this] at hw
          exact hw

/-- The substitution lemma. -/
theorem substitution {Δ : Ctx} {t : Term} {T : Ty} (ht : Δ ⊢ t ∶ T) :
    ∀ (Γ : Ctx) (k : Nat) (S : Ty) (s : Term),
      Δ = insertAt S k Γ → (Γ.drop k ⊢ s ∶ S) →
      Γ ⊢ subst k s t ∶ T := by
  induction ht with
  | @var Δ n T hget =>
      intro Γ k S s heq hs
      subst heq
      by_cases h₁ : n < k
      · simp only [subst, if_pos h₁]
        exact .var (by rw [← get?_insertAt_lt S k Γ n h₁]; exact hget)
      · by_cases h₂ : n = k
        · subst h₂
          obtain ⟨rfl, hle⟩ := get?_insertAt_self S n Γ T hget
          simp only [subst, if_neg h₁, if_pos rfl]
          exact shift0_typing n Γ s T hle hs
        · simp only [subst, if_neg h₁, if_neg h₂]
          exact .var (get?_insertAt_gt S k Γ n T hget (by omega))
  | @abs Δ T₁ T₂ body _ ih =>
      intro Γ k S s heq hs
      exact .abs (ih (T₁ :: Γ) (k + 1) S s (by rw [heq]; rfl) hs)
  | app _ _ ih₁ ih₂ =>
      intro Γ k S s heq hs
      exact .app (ih₁ Γ k S s heq hs) (ih₂ Γ k S s heq hs)

/-- Preservation for call-by-value evaluation. -/
theorem preservation {Γ : Ctx} {t t' : Term} {T : Ty} (hs : t ⟶ t') :
    (Γ ⊢ t ∶ T) → Γ ⊢ t' ∶ T := by
  induction hs generalizing T with
  | appAbs _ =>
      intro h
      cases h with
      | app h₁ h₂ =>
          cases h₁ with
          | abs hbody => exact substitution hbody _ 0 _ _ rfl h₂
  | app1 _ ih =>
      intro h
      cases h with
      | app h₁ h₂ => exact .app (ih h₁) h₂
  | app2 _ _ ih =>
      intro h
      cases h with
      | app h₁ h₂ => exact .app h₁ (ih h₂)

/-- Well-typed terms have their free variables bounded by the context. -/
theorem typed_closed {Γ : Ctx} {t : Term} {T : Ty} (h : Γ ⊢ t ∶ T) :
    Closed Γ.length t := by
  induction h with
  | @var Γ n T hget =>
      show n < Γ.length
      induction Γ generalizing n with
      | nil => cases hget
      | cons B Γ ih =>
          cases n with
          | zero => simp
          | succ n => have := ih hget; simp; omega
  | abs _ ih => exact ih
  | app _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

/-- Closedness is monotone in the bound. -/
theorem closed_mono : ∀ (t : Term) (m n : Nat), Closed m t → m ≤ n →
    Closed n t := by
  intro t
  induction t with
  | var k => intro m n h hle; show k < n; have : k < m := h; omega
  | abs t ih => intro m n h hle; exact ih (m + 1) (n + 1) h (by omega)
  | app t₁ t₂ ih₁ ih₂ =>
      intro m n h hle
      exact ⟨ih₁ m n h.1 hle, ih₂ m n h.2 hle⟩

/-- A closed term typed in the empty context is typed in any context. -/
theorem closed_typing_any {t : Term} {T : Ty} (h : [] ⊢ t ∶ T) :
    ∀ Γ : Ctx, Γ ⊢ t ∶ T := by
  intro Γ
  have hc : Closed 0 t := typed_closed h
  have := shift0_typing Γ.length Γ t T (by omega)
    (by rw [List.drop_length]; exact h)
  rwa [shift_closed_id t Γ.length 0 (closed_mono t 0 0 hc (by omega))] at this

/-! ## Halting and the logical relation -/

/-- A term halts if it evaluates to a value. -/
def Halts (t : Term) : Prop := ∃ v, (t ⟶* v) ∧ Value v

/-- Values halt. -/
theorem Value.halts {v : Term} (hv : Value v) : Halts v :=
  ⟨v, .refl v, hv⟩

/-- **The logical relation** `R T t` (TAPL definition 12.1.1): closed
well-typed, halting, and — at arrow type — mapping `R`-good arguments to
`R`-good results. -/
def R : Ty → Term → Prop
  | .base, t => ([] ⊢ t ∶ .base) ∧ Halts t
  | .arrow T₁ T₂, t =>
      ([] ⊢ t ∶ T₁ ⇒ T₂) ∧ Halts t ∧ ∀ s, R T₁ s → R T₂ (t ⬝ s)

/-- `R` implies halting (TAPL lemma: immediate from the definition). -/
theorem R.halts : ∀ {T t}, R T t → Halts t := by
  intro T t h
  cases T with
  | base => exact h.2
  | arrow T₁ T₂ => exact h.2.1

/-- `R` implies typability. -/
theorem R.typable : ∀ {T t}, R T t → [] ⊢ t ∶ T := by
  intro T t h
  cases T with
  | base => exact h.1
  | arrow T₁ T₂ => exact h.1

/-! ### `R` is preserved by evaluation, forward and backward
(TAPL lemma 12.1.4) -/

/-- Halting is invariant under a step (forward direction uses
determinacy). -/
theorem halts_step {t t' : Term} (hs : t ⟶ t') : Halts t ↔ Halts t' := by
  constructor
  · intro ⟨v, hmulti, hv⟩
    cases hmulti with
    | refl => exact absurd hs (hv.not_step)
    | head s rest =>
        cases Step.deterministic hs s
        exact ⟨v, rest, hv⟩
  · intro ⟨v, hmulti, hv⟩
    exact ⟨v, .head hs hmulti, hv⟩

/-- One evaluation step preserves `R`, in both directions (for terms
known to be well typed). -/
theorem R_step : ∀ (T : Ty) {t t' : Term}, ([] ⊢ t ∶ T) → (t ⟶ t') →
    (R T t ↔ R T t') := by
  intro T
  induction T with
  | base =>
      intro t t' ht hs
      constructor
      · intro ⟨_, hh⟩; exact ⟨preservation hs ht, (halts_step hs).mp hh⟩
      · intro ⟨_, hh⟩; exact ⟨ht, (halts_step hs).mpr hh⟩
  | arrow T₁ T₂ _ ih₂ =>
      intro t t' ht hs
      constructor
      · intro ⟨_, hh, happ⟩
        refine ⟨preservation hs ht, (halts_step hs).mp hh, ?_⟩
        intro s hRs
        have hts : [] ⊢ t ⬝ s ∶ T₂ := .app ht (R.typable hRs)
        exact (ih₂ hts (.app1 hs)).mp (happ s hRs)
      · intro ⟨_, hh, happ⟩
        refine ⟨ht, (halts_step hs).mpr hh, ?_⟩
        intro s hRs
        have hts : [] ⊢ t ⬝ s ∶ T₂ := .app ht (R.typable hRs)
        exact (ih₂ hts (.app1 hs)).mpr (happ s hRs)

/-- Multi-step forward preservation of `R`. -/
theorem R_multi_fwd {T : Ty} : ∀ {t t' : Term}, (t ⟶* t') → R T t →
    R T t' := by
  intro t t' hm
  induction hm with
  | refl _ => intro h; exact h
  | head s _ ih => intro h; exact ih ((R_step _ (R.typable h) s).mp h)

/-- Multi-step backward preservation of `R` (needs the typing of the
source term). -/
theorem R_multi_bwd {T : Ty} : ∀ {t t' : Term}, ([] ⊢ t ∶ T) →
    (t ⟶* t') → R T t' → R T t := by
  intro t t' ht hm
  revert ht
  induction hm with
  | refl _ => intro _ h; exact h
  | head s _ ih =>
      intro ht h
      exact (R_step _ ht s).mpr (ih (preservation s ht) h)

/-! ## Multi-substitutions -/

/-- Substitute the terms of `σ` in turn at index `k` (each entry is meant
to be closed, so the sequence acts like a simultaneous substitution for
variables `k, k+1, …`). -/
def msubstK (k : Nat) : List Term → Term → Term
  | [], t => t
  | v :: σ, t => msubstK k σ (subst k v t)

/-- Substitute for all free variables at once. -/
def msubst : List Term → Term → Term := msubstK 0

/-- All entries of a substitution are closed. -/
inductive AllClosed : List Term → Prop where
  | nil : AllClosed []
  | cons {v : Term} {σ : List Term} :
      Closed 0 v → AllClosed σ → AllClosed (v :: σ)

/-- An `R`-environment: pointwise `R`-good closed terms for a context. -/
inductive REnv : List Term → Ctx → Prop where
  | nil : REnv [] []
  | cons {v : Term} {T : Ty} {σ : List Term} {Γ : Ctx} :
      R T v → REnv σ Γ → REnv (v :: σ) (T :: Γ)

theorem REnv.allClosed {σ : List Term} {Γ : Ctx} (h : REnv σ Γ) :
    AllClosed σ := by
  induction h with
  | nil => exact .nil
  | cons hR _ ih => exact .cons (typed_closed (R.typable hR)) ih

/-- Multi-substitution does nothing to a closed term. -/
theorem msubstK_closed_id {v : Term} (hc : Closed 0 v) :
    ∀ (σ : List Term) (k : Nat), msubstK k σ v = v := by
  intro σ
  induction σ with
  | nil => intro k; rfl
  | cons w σ ih =>
      intro k
      show msubstK k σ (subst k w v) = v
      rw [subst_closed_id v w k (closed_mono v 0 k hc (by omega))]
      exact ih k

/-- Multi-substitution commutes into abstractions. -/
theorem msubstK_abs : ∀ (σ : List Term) (k : Nat) (t : Term),
    msubstK k σ (ƛ t) = ƛ (msubstK (k + 1) σ t) := by
  intro σ
  induction σ with
  | nil => intro k t; rfl
  | cons w _ ih => intro k t; exact ih k (subst (k + 1) w t)

/-- Multi-substitution distributes over application. -/
theorem msubstK_app : ∀ (σ : List Term) (k : Nat) (t₁ t₂ : Term),
    msubstK k σ (t₁ ⬝ t₂) = msubstK k σ t₁ ⬝ msubstK k σ t₂ := by
  intro σ
  induction σ with
  | nil => intro k t₁ t₂; rfl
  | cons w _ ih => intro k t₁ t₂; exact ih k _ _

/-- The key commutation: a closed β-substitution moves through a
pending multi-substitution at index 1 (using chapter 6's substitution
lemma). -/
theorem subst_msubstK {v : Term} (hv : Closed 0 v) :
    ∀ (σ : List Term), AllClosed σ → ∀ b : Term,
      subst 0 v (msubstK 1 σ b) = msubstK 0 σ (subst 0 v b) := by
  intro σ hσ
  induction hσ with
  | nil => intro b; rfl
  | @cons w σ _ _ ih =>
      intro b
      show subst 0 v (msubstK 1 σ (subst 1 w b)) =
        msubstK 0 σ (subst 0 w (subst 0 v b))
      rw [ih (subst 1 w b)]
      congr 1
      -- subst 0 v (subst 1 w b) = subst 0 w (subst 0 v b), from chapter 6
      have h := subst_subst b w v 0 0 (by omega)
      rw [subst_closed_id v w 0 hv] at h
      exact h.symm

/-- Multi-substitution preserves typing: an `R`-environment closes all the
free variables. -/
theorem msubst_typing : ∀ (σ : List Term) {Γ : Ctx} {t : Term} {T : Ty},
    (Γ ⊢ t ∶ T) → REnv σ Γ → [] ⊢ msubst σ t ∶ T := by
  intro σ
  induction σ with
  | nil =>
      intro Γ t T h henv
      cases henv
      exact h
  | cons v σ ih =>
      intro Γ t T h henv
      cases henv with
      | cons hR henv' =>
          show [] ⊢ msubstK 0 σ (subst 0 v t) ∶ T
          exact ih (substitution h _ 0 _ v rfl
            (closed_typing_any (R.typable hR) _)) henv'

/-- Multi-step congruence in argument position of an application to a
value. -/
theorem multi_app2 {f t t' : Term} (hf : Value f) (hm : t ⟶* t') :
    (f ⬝ t) ⟶* (f ⬝ t') := by
  induction hm with
  | refl _ => exact .refl _
  | head s _ ih => exact .head (.app2 hf s) ih

/-! ## The main lemma and the normalization theorem -/

/-- **TAPL lemma 12.1.5**: closing a well-typed open term with an
`R`-environment yields a term in `R`. -/
theorem main_lemma {Γ : Ctx} {t : Term} {T : Ty} (h : Γ ⊢ t ∶ T) :
    ∀ σ, REnv σ Γ → R T (msubst σ t) := by
  induction h with
  | @var Γ n T hget =>
      intro σ henv
      induction henv generalizing n with
      | nil => cases hget
      | @cons v T' σ' Γ' hR _ ih =>
          cases n with
          | zero =>
              cases hget
              show R T (msubstK 0 σ' (subst 0 v (var 0)))
              have : subst 0 v (var 0) = v := by simp [subst, shift_zero]
              rw [this,
                msubstK_closed_id (typed_closed (R.typable hR)) σ' 0]
              exact hR
          | succ n =>
              show R T (msubstK 0 σ' (subst 0 v (var (n + 1))))
              have h1 : ¬ n + 1 < 0 := by omega
              have h2 : ¬ n + 1 = 0 := by omega
              have : subst 0 v (var (n + 1)) = var n := by
                simp [subst, h1, h2]
              rw [this]
              exact ih hget
  | @abs Γ T₁ T₂ body hbody ih =>
      intro σ henv
      rw [show msubst σ (ƛ body) = msubstK 0 σ (ƛ body) from rfl,
        msubstK_abs]
      have htyp : [] ⊢ ƛ (msubstK 1 σ body) ∶ T₁ ⇒ T₂ := by
        have := msubst_typing σ (HasType.abs hbody) henv
        rwa [show msubst σ (ƛ body) = ƛ (msubstK 1 σ body) from
          msubstK_abs σ 0 body] at this
      refine ⟨htyp, Value.halts (.abs _), ?_⟩
      intro s hRs
      -- evaluate the argument to a value
      obtain ⟨v, hsv, hvval⟩ := R.halts hRs
      have hRv : R T₁ v := R_multi_fwd hsv hRs
      have hvclosed : Closed 0 v := typed_closed (R.typable hRv)
      -- the redex steps to the extended multi-substitution of the body
      have hchain : (ƛ (msubstK 1 σ body)) ⬝ s ⟶* msubst (v :: σ) body := by
        apply Multi.trans (multi_app2 (.abs _) hsv)
        apply Multi.head (Step.appAbs hvval)
        rw [show msubst (v :: σ) body = msubstK 0 σ (subst 0 v body)
          from rfl, ← subst_msubstK hvclosed σ henv.allClosed body]
        exact .refl _
      have hR' : R T₂ (msubst (v :: σ) body) :=
        ih (v :: σ) (.cons hRv henv)
      exact R_multi_bwd (.app htyp (R.typable hRs)) hchain hR'
  | @app Γ T₁ T₂ t₁ t₂ _ _ ih₁ ih₂ =>
      intro σ henv
      rw [show msubst σ (t₁ ⬝ t₂) = msubstK 0 σ (t₁ ⬝ t₂) from rfl,
        msubstK_app]
      obtain ⟨_, _, happ⟩ := ih₁ σ henv
      exact happ _ (ih₂ σ henv)

/-- **Theorem 12.1.6 (Normalization)**: every closed well-typed term
halts. -/
theorem normalization {t : Term} {T : Ty} (h : [] ⊢ t ∶ T) : Halts t := by
  have := main_lemma h [] .nil
  exact R.halts this

/-! ## Examples -/

/-- The identity at base type, `λx. x ∶ A ⇒ A`. -/
example : [] ⊢ (ƛ #0) ∶ .base ⇒ .base := .abs (.var rfl)

/-- Chapter 5's Church booleans are typable here, e.g.
`tru ∶ A ⇒ A ⇒ A`, hence halt — as does every well-typed term. -/
example : [] ⊢ tru ∶ .base ⇒ .base ⇒ .base := .abs (.abs (.var rfl))

example : Halts ((ƛ #0) ⬝ (ƛ #0)) :=
  normalization (.app (.abs (.var rfl)) (.abs (T₁ := Ty.base) (.var rfl)))

/-- `omega` from chapter 5 diverges — so by `normalization` (contrapositive)
it cannot be well typed, at any type. -/
theorem omega_not_typable (T : Ty) : ¬ ([] ⊢ Chapter05.omega ∶ T) := by
  intro h
  obtain ⟨v, hmulti, hv⟩ := normalization h
  -- omega only ever steps to itself, so it never reaches a value
  have aux : ∀ s u, (s ⟶* u) → s = Chapter05.omega →
      u = Chapter05.omega := by
    intro s u hm
    induction hm with
    | refl _ => intro heq; exact heq
    | head st _ ih =>
        intro heq
        subst heq
        have homega : Chapter05.omega ⟶ Chapter05.omega := .appAbs (.abs _)
        cases Step.deterministic st homega
        exact ih rfl
  have hveq := aux _ _ hmulti rfl
  subst hveq
  cases hv

end Chapter12
