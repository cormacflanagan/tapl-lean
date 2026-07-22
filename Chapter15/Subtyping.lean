/-!
# Chapter 15: Subtyping

λ→ with booleans and pairs, extended with a maximal type `Top` and the
subsumption rule `T-Sub`: a term of a subtype may be used wherever a
supertype is expected. Function types are contravariant in their domain
and covariant in their codomain; products are covariant.

Because of subsumption, typing derivations are no longer syntax-directed,
so the metatheory needs *inversion lemmas for the subtype relation*
(TAPL lemma 15.3.2) and *inversion of typing modulo subtyping*
(lemma 15.3.3) before preservation and progress go through.

TAPL's records (with width, depth, and permutation subtyping) are
represented here by their binary special case, products; see the README.
-/

namespace Chapter15

/-- Types: `Top`, `Bool`, functions, products (TAPL figure 15-1). -/
inductive Ty : Type where
  | top
  | bool
  | arrow (T₁ T₂ : Ty)
  | prod (T₁ T₂ : Ty)
  deriving Repr, DecidableEq

/-- `T₁ ⇒ T₂` is the function type. -/
scoped infixr:60 " ⇒ " => Ty.arrow
/-- `T₁ ⊗ T₂` is the product type. -/
scoped infixl:65 " ⊗ " => Ty.prod

/-- The subtype relation `S <: T` (TAPL figure 15-1, plus the product rule
of §15.2). -/
inductive Sub : Ty → Ty → Prop where
  | refl (T : Ty) : Sub T T                                    -- S-Refl
  | trans {S U T : Ty} : Sub S U → Sub U T → Sub S T           -- S-Trans
  | top (S : Ty) : Sub S .top                                  -- S-Top
  | arrow {S₁ S₂ T₁ T₂ : Ty} :
      Sub T₁ S₁ → Sub S₂ T₂ → Sub (S₁ ⇒ S₂) (T₁ ⇒ T₂)          -- S-Arrow
  | prod {S₁ S₂ T₁ T₂ : Ty} :
      Sub S₁ T₁ → Sub S₂ T₂ → Sub (S₁ ⊗ S₂) (T₁ ⊗ T₂)          -- S-Prod

@[inherit_doc] scoped infix:45 " <: " => Sub

/-- Terms: λ→ with booleans and pairs, as in chapters 9 and 11. -/
inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | tru
  | fls
  | ite (t₁ t₂ t₃ : Term)
  | pair (t₁ t₂ : Term)
  | fst (t : Term)
  | snd (t : Term)
  deriving Repr, DecidableEq

namespace Term

/-- Shift the variables of `t` that are `≥ c` up by `d`. -/
def shift (d c : Nat) : Term → Term
  | var n => if n < c then var n else var (n + d)
  | abs T t => abs T (shift d (c + 1) t)
  | app t₁ t₂ => app (shift d c t₁) (shift d c t₂)
  | tru => tru
  | fls => fls
  | ite t₁ t₂ t₃ => ite (shift d c t₁) (shift d c t₂) (shift d c t₃)
  | pair t₁ t₂ => pair (shift d c t₁) (shift d c t₂)
  | fst t => fst (shift d c t)
  | snd t => snd (shift d c t)

/-- Beta-substitution `[k ↦ s] t` (substitute and decrement). -/
def subst (k : Nat) (s : Term) : Term → Term
  | var n =>
      if n < k then var n
      else if n = k then shift k 0 s
      else var (n - 1)
  | abs T t => abs T (subst (k + 1) s t)
  | app t₁ t₂ => app (subst k s t₁) (subst k s t₂)
  | tru => tru
  | fls => fls
  | ite t₁ t₂ t₃ => ite (subst k s t₁) (subst k s t₂) (subst k s t₃)
  | pair t₁ t₂ => pair (subst k s t₁) (subst k s t₂)
  | fst t => fst (subst k s t)
  | snd t => snd (subst k s t)

/-- Shifting by zero is the identity. -/
theorem shift_zero : ∀ (t : Term) (c : Nat), shift 0 c t = t := by
  intro t
  induction t with
  | var n => intro c; by_cases h : n < c <;> simp [shift, h]
  | tru | fls => intro c; rfl
  | abs T t ih | fst t ih | snd t ih => intro c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ | pair t₁ t₂ ih₁ ih₂ => intro c; simp [shift, ih₁, ih₂]
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ => intro c; simp [shift, ih₁, ih₂, ih₃]

/-- Successive one-place shifts accumulate. -/
theorem shift_succ : ∀ (t : Term) (k c : Nat),
    shift 1 c (shift k c t) = shift (k + 1) c t := by
  intro t
  induction t with
  | var n =>
      intro k c
      by_cases h : n < c
      · simp [shift, h]
      · have h' : ¬ n + k < c := by omega
        simp [shift, h, h']
        omega
  | tru | fls => intro k c; rfl
  | abs T t ih | fst t ih | snd t ih => intro k c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ | pair t₁ t₂ ih₁ ih₂ => intro k c; simp [shift, ih₁, ih₂]
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ => intro k c; simp [shift, ih₁, ih₂, ih₃]

end Term

open Term

/-- Values. -/
inductive Value : Term → Prop where
  | abs (T : Ty) (t : Term) : Value (abs T t)
  | tru : Value tru
  | fls : Value fls
  | pair {v₁ v₂ : Term} : Value v₁ → Value v₂ → Value (pair v₁ v₂)

/-- Call-by-value single-step evaluation (as in chapters 9 and 11 —
subtyping changes only the statics, not the dynamics). -/
inductive Step : Term → Term → Prop where
  | appAbs {T : Ty} {t v : Term} :
      Value v → Step (app (abs T t) v) (subst 0 v t)
  | app1 {t₁ t₁' t₂ : Term} :
      Step t₁ t₁' → Step (app t₁ t₂) (app t₁' t₂)
  | app2 {v t t' : Term} :
      Value v → Step t t' → Step (app v t) (app v t')
  | ifTrue {t₂ t₃ : Term} : Step (ite tru t₂ t₃) t₂
  | ifFalse {t₂ t₃ : Term} : Step (ite fls t₂ t₃) t₃
  | ifCong {t₁ t₁' t₂ t₃ : Term} :
      Step t₁ t₁' → Step (ite t₁ t₂ t₃) (ite t₁' t₂ t₃)
  | pairBeta1 {v₁ v₂ : Term} :
      Value v₁ → Value v₂ → Step (fst (pair v₁ v₂)) v₁
  | pairBeta2 {v₁ v₂ : Term} :
      Value v₁ → Value v₂ → Step (snd (pair v₁ v₂)) v₂
  | fstCong {t t' : Term} : Step t t' → Step (fst t) (fst t')
  | sndCong {t t' : Term} : Step t t' → Step (snd t) (snd t')
  | pair1 {t₁ t₁' t₂ : Term} :
      Step t₁ t₁' → Step (pair t₁ t₂) (pair t₁' t₂)
  | pair2 {v t t' : Term} :
      Value v → Step t t' → Step (pair v t) (pair v t')

@[inherit_doc] scoped infix:50 " ⟶ " => Step

/-- Multi-step evaluation. -/
inductive MultiStep : Term → Term → Prop where
  | refl (t : Term) : MultiStep t t
  | head {t t' t'' : Term} : Step t t' → MultiStep t' t'' → MultiStep t t''

@[inherit_doc] scoped infix:50 " ⟶* " => MultiStep

/-! ## Typing with subsumption -/

/-- Typing contexts. -/
abbrev Ctx := List Ty

/-- The typing relation, now with the subsumption rule `T-Sub`
(TAPL figure 15-1). -/
inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ : Ctx} {n : Nat} {T : Ty} :
      Γ.get? n = some T → HasType Γ (var n) T
  | abs {Γ : Ctx} {T₁ T₂ : Ty} {t : Term} :
      HasType (T₁ :: Γ) t T₂ → HasType Γ (abs T₁ t) (T₁ ⇒ T₂)
  | app {Γ : Ctx} {T₁ T₂ : Ty} {t₁ t₂ : Term} :
      HasType Γ t₁ (T₁ ⇒ T₂) → HasType Γ t₂ T₁ →
      HasType Γ (app t₁ t₂) T₂
  | tru {Γ : Ctx} : HasType Γ tru .bool
  | fls {Γ : Ctx} : HasType Γ fls .bool
  | ite {Γ : Ctx} {t₁ t₂ t₃ : Term} {T : Ty} :
      HasType Γ t₁ .bool → HasType Γ t₂ T → HasType Γ t₃ T →
      HasType Γ (ite t₁ t₂ t₃) T
  | pair {Γ : Ctx} {t₁ t₂ : Term} {T₁ T₂ : Ty} :
      HasType Γ t₁ T₁ → HasType Γ t₂ T₂ →
      HasType Γ (pair t₁ t₂) (T₁ ⊗ T₂)
  | fst {Γ : Ctx} {t : Term} {T₁ T₂ : Ty} :
      HasType Γ t (T₁ ⊗ T₂) → HasType Γ (fst t) T₁
  | snd {Γ : Ctx} {t : Term} {T₁ T₂ : Ty} :
      HasType Γ t (T₁ ⊗ T₂) → HasType Γ (snd t) T₂
  | sub {Γ : Ctx} {t : Term} {S T : Ty} :                      -- T-Sub
      HasType Γ t S → (S <: T) → HasType Γ t T

@[inherit_doc] scoped notation:40 Γ " ⊢ " t " ∶ " T => HasType Γ t T

/-! ## Inversion of the subtype relation (TAPL lemma 15.3.2) -/

/-- The only subtype of `Bool` is `Bool`. -/
theorem Sub.bool_inv {S T : Ty} (h : S <: T) : T = .bool → S = .bool := by
  induction h with
  | refl _ => intro h; exact h
  | trans _ _ ih₁ ih₂ => intro h; exact ih₁ (ih₂ h)
  | top _ => intro h; cases h
  | arrow _ _ _ _ => intro h; cases h
  | prod _ _ _ _ => intro h; cases h

/-- Subtypes of an arrow type are arrow types, contravariantly on the left
and covariantly on the right. -/
theorem Sub.arrow_inv {S T : Ty} (h : S <: T) :
    ∀ T₁ T₂, T = T₁ ⇒ T₂ →
      ∃ S₁ S₂, S = S₁ ⇒ S₂ ∧ (T₁ <: S₁) ∧ (S₂ <: T₂) := by
  induction h with
  | refl T =>
      intro T₁ T₂ heq
      exact ⟨T₁, T₂, heq, .refl T₁, .refl T₂⟩
  | trans _ _ ih₁ ih₂ =>
      intro T₁ T₂ heq
      obtain ⟨U₁, U₂, rfl, hU₁, hU₂⟩ := ih₂ T₁ T₂ heq
      obtain ⟨S₁, S₂, rfl, hS₁, hS₂⟩ := ih₁ U₁ U₂ rfl
      exact ⟨S₁, S₂, rfl, .trans hU₁ hS₁, .trans hS₂ hU₂⟩
  | top _ => intro T₁ T₂ heq; cases heq
  | @arrow S₁ S₂ U₁ U₂ h₁ h₂ _ _ =>
      intro T₁ T₂ heq
      cases heq
      exact ⟨S₁, S₂, rfl, h₁, h₂⟩
  | prod _ _ _ _ => intro T₁ T₂ heq; cases heq

/-- Subtypes of a product type are product types, componentwise. -/
theorem Sub.prod_inv {S T : Ty} (h : S <: T) :
    ∀ T₁ T₂, T = T₁ ⊗ T₂ →
      ∃ S₁ S₂, S = S₁ ⊗ S₂ ∧ (S₁ <: T₁) ∧ (S₂ <: T₂) := by
  induction h with
  | refl T =>
      intro T₁ T₂ heq
      exact ⟨T₁, T₂, heq, .refl T₁, .refl T₂⟩
  | trans _ _ ih₁ ih₂ =>
      intro T₁ T₂ heq
      obtain ⟨U₁, U₂, rfl, hU₁, hU₂⟩ := ih₂ T₁ T₂ heq
      obtain ⟨S₁, S₂, rfl, hS₁, hS₂⟩ := ih₁ U₁ U₂ rfl
      exact ⟨S₁, S₂, rfl, .trans hS₁ hU₁, .trans hS₂ hU₂⟩
  | top _ => intro T₁ T₂ heq; cases heq
  | arrow _ _ _ _ => intro T₁ T₂ heq; cases heq
  | @prod S₁ S₂ U₁ U₂ h₁ h₂ _ _ =>
      intro T₁ T₂ heq
      cases heq
      exact ⟨S₁, S₂, rfl, h₁, h₂⟩

/-! ## Inversion of typing modulo subtyping (TAPL lemma 15.3.3) -/

/-- If `λx:S₁. body` has a type below `T₁ ⇒ T₂`, then `T₁ <: S₁` and the
body has type `T₂` under `S₁`. -/
theorem abs_inv {Γ : Ctx} {S₁ : Ty} {body : Term} {T : Ty}
    (h : Γ ⊢ abs S₁ body ∶ T) :
    ∀ {T₁ T₂}, (T <: T₁ ⇒ T₂) →
      (T₁ <: S₁) ∧ ((S₁ :: Γ) ⊢ body ∶ T₂) := by
  generalize ht : Term.abs S₁ body = t' at h
  induction h with
  | abs hbody =>
      cases ht
      intro T₁ T₂ hsub
      obtain ⟨S₁', S₂', heq, h₁, h₂⟩ := hsub.arrow_inv _ _ rfl
      cases heq
      exact ⟨h₁, .sub hbody h₂⟩
  | sub _ hsub' ih =>
      subst ht
      intro T₁ T₂ hsub
      exact ih rfl (.trans hsub' hsub)
  | var _ => cases ht
  | app _ _ _ _ => cases ht
  | tru => cases ht
  | fls => cases ht
  | ite _ _ _ _ _ _ => cases ht
  | pair _ _ _ _ => cases ht
  | fst _ _ => cases ht
  | snd _ _ => cases ht

/-- If `pair t₁ t₂` has a type below `T₁ ⊗ T₂`, its components have types
`T₁` and `T₂`. -/
theorem pair_inv {Γ : Ctx} {t₁ t₂ : Term} {T : Ty}
    (h : Γ ⊢ pair t₁ t₂ ∶ T) :
    ∀ {T₁ T₂}, (T <: T₁ ⊗ T₂) → (Γ ⊢ t₁ ∶ T₁) ∧ (Γ ⊢ t₂ ∶ T₂) := by
  generalize ht : Term.pair t₁ t₂ = t' at h
  induction h with
  | pair h₁ h₂ =>
      cases ht
      intro T₁ T₂ hsub
      obtain ⟨S₁, S₂, heq, hs₁, hs₂⟩ := hsub.prod_inv _ _ rfl
      cases heq
      exact ⟨.sub h₁ hs₁, .sub h₂ hs₂⟩
  | sub _ hsub' ih =>
      subst ht
      intro T₁ T₂ hsub
      exact ih rfl (.trans hsub' hsub)
  | var _ => cases ht
  | abs _ => cases ht
  | app _ _ _ _ => cases ht
  | tru => cases ht
  | fls => cases ht
  | ite _ _ _ _ _ _ => cases ht
  | fst _ _ => cases ht
  | snd _ _ => cases ht

/-! ## Context insertion, weakening, substitution (as in chapter 9) -/

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

/-- Weakening (shift-typing); the `T-Sub` case is immediate. -/
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
  | tru => intro c S; exact .tru
  | fls => intro c S; exact .fls
  | ite _ _ _ ih₁ ih₂ ih₃ =>
      intro c S; exact .ite (ih₁ c S) (ih₂ c S) (ih₃ c S)
  | pair _ _ ih₁ ih₂ => intro c S; exact .pair (ih₁ c S) (ih₂ c S)
  | fst _ ih => intro c S; exact .fst (ih c S)
  | snd _ ih => intro c S; exact .snd (ih c S)
  | sub _ hsub ih => intro c S; exact .sub (ih c S) hsub

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
          rw [shift_succ] at hw
          exact hw

/-- The substitution lemma, by induction on the typing derivation of `t`
(with the context constrained by an equation, so subsumption is a one-line
case). -/
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
  | tru => intro Γ k S s _ _; exact .tru
  | fls => intro Γ k S s _ _; exact .fls
  | ite _ _ _ ih₁ ih₂ ih₃ =>
      intro Γ k S s heq hs
      exact .ite (ih₁ Γ k S s heq hs) (ih₂ Γ k S s heq hs)
        (ih₃ Γ k S s heq hs)
  | pair _ _ ih₁ ih₂ =>
      intro Γ k S s heq hs
      exact .pair (ih₁ Γ k S s heq hs) (ih₂ Γ k S s heq hs)
  | fst _ ih =>
      intro Γ k S s heq hs
      exact .fst (ih Γ k S s heq hs)
  | snd _ ih =>
      intro Γ k S s heq hs
      exact .snd (ih Γ k S s heq hs)
  | sub _ hsub ih =>
      intro Γ k S s heq hs
      exact .sub (ih Γ k S s heq hs) hsub

/-! ## Preservation and progress -/

/-- **Preservation (TAPL theorem 15.3.5)**, by induction on the typing
derivation; the `E-AppAbs` and pair-projection cases use the inversion
lemmas above. -/
theorem preservation {Γ : Ctx} {t : Term} {T : Ty} (h : Γ ⊢ t ∶ T) :
    ∀ t', (t ⟶ t') → Γ ⊢ t' ∶ T := by
  induction h with
  | var _ => intro t' hs; cases hs
  | abs _ => intro t' hs; cases hs
  | tru => intro t' hs; cases hs
  | fls => intro t' hs; cases hs
  | @app Γ T₁ T₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      intro t' hs
      cases hs with
      | appAbs hv =>
          obtain ⟨hsub, hbody⟩ := abs_inv h₁ (.refl _)
          exact substitution hbody Γ 0 _ _ rfl (.sub h₂ hsub)
      | app1 hstep => exact .app (ih₁ _ hstep) h₂
      | app2 _ hstep => exact .app h₁ (ih₂ _ hstep)
  | ite h₁ h₂ h₃ ih₁ _ _ =>
      intro t' hs
      cases hs with
      | ifTrue => exact h₂
      | ifFalse => exact h₃
      | ifCong hstep => exact .ite (ih₁ _ hstep) h₂ h₃
  | pair h₁ h₂ ih₁ ih₂ =>
      intro t' hs
      cases hs with
      | pair1 hstep => exact .pair (ih₁ _ hstep) h₂
      | pair2 _ hstep => exact .pair h₁ (ih₂ _ hstep)
  | fst h ih =>
      intro t' hs
      cases hs with
      | pairBeta1 hv₁ hv₂ => exact (pair_inv h (.refl _)).1
      | fstCong hstep => exact .fst (ih _ hstep)
  | snd h ih =>
      intro t' hs
      cases hs with
      | pairBeta2 hv₁ hv₂ => exact (pair_inv h (.refl _)).2
      | sndCong hstep => exact .snd (ih _ hstep)
  | sub _ hsub ih =>
      intro t' hs
      exact .sub (ih _ hs) hsub

/-- Canonical forms at arrow type: values below an arrow type are
abstractions (TAPL lemma 15.3.6). -/
theorem canonical_arrow {Γ : Ctx} {v : Term} {T : Ty}
    (h : Γ ⊢ v ∶ T) :
    Value v → ∀ {T₁ T₂}, T = T₁ ⇒ T₂ → ∃ S body, v = abs S body := by
  induction h with
  | var _ => intro hv; cases hv
  | abs _ => intro _ T₁ T₂ _; exact ⟨_, _, rfl⟩
  | app _ _ _ _ => intro hv; cases hv
  | tru => intro _ T₁ T₂ heq; cases heq
  | fls => intro _ T₁ T₂ heq; cases heq
  | ite _ _ _ _ _ _ => intro hv; cases hv
  | pair _ _ _ _ => intro _ T₁ T₂ heq; cases heq
  | fst _ _ => intro hv; cases hv
  | snd _ _ => intro hv; cases hv
  | sub _ hsub ih =>
      intro hv T₁ T₂ heq
      subst heq
      obtain ⟨S₁, S₂, rfl, _, _⟩ := hsub.arrow_inv _ _ rfl
      exact ih hv rfl

/-- Canonical forms at `Bool` (TAPL lemma 15.3.6). -/
theorem canonical_bool {Γ : Ctx} {v : Term} {T : Ty}
    (h : Γ ⊢ v ∶ T) :
    Value v → T = .bool → v = tru ∨ v = fls := by
  induction h with
  | var _ => intro hv; cases hv
  | abs _ => intro _ heq; cases heq
  | app _ _ _ _ => intro hv; cases hv
  | tru => intro _ _; exact .inl rfl
  | fls => intro _ _; exact .inr rfl
  | ite _ _ _ _ _ _ => intro hv; cases hv
  | pair _ _ _ _ => intro _ heq; cases heq
  | fst _ _ => intro hv; cases hv
  | snd _ _ => intro hv; cases hv
  | sub _ hsub ih =>
      intro hv heq
      subst heq
      exact ih hv (hsub.bool_inv rfl)

/-- Canonical forms at product type: values below a product type are
pairs of values. -/
theorem canonical_prod {Γ : Ctx} {v : Term} {T : Ty}
    (h : Γ ⊢ v ∶ T) :
    Value v → ∀ {T₁ T₂}, T = T₁ ⊗ T₂ →
      ∃ v₁ v₂, v = pair v₁ v₂ ∧ Value v₁ ∧ Value v₂ := by
  induction h with
  | var _ => intro hv; cases hv
  | abs _ => intro _ T₁ T₂ heq; cases heq
  | app _ _ _ _ => intro hv; cases hv
  | tru => intro _ T₁ T₂ heq; cases heq
  | fls => intro _ T₁ T₂ heq; cases heq
  | ite _ _ _ _ _ _ => intro hv; cases hv
  | pair _ _ _ _ =>
      intro hv T₁ T₂ _
      cases hv with
      | pair hv₁ hv₂ => exact ⟨_, _, rfl, hv₁, hv₂⟩
  | fst _ _ => intro hv; cases hv
  | snd _ _ => intro hv; cases hv
  | sub _ hsub ih =>
      intro hv T₁ T₂ heq
      subst heq
      obtain ⟨S₁, S₂, rfl, _, _⟩ := hsub.prod_inv _ _ rfl
      exact ih hv rfl

/-- Progress, auxiliary version with a context equation. -/
theorem progress' {Γ : Ctx} {t : Term} {T : Ty} (h : Γ ⊢ t ∶ T) :
    Γ = [] → Value t ∨ ∃ t', t ⟶ t' := by
  induction h with
  | @var Γ n T hget =>
      intro heq
      subst heq
      simp [List.get?] at hget
  | abs _ _ => intro _; exact .inl (.abs _ _)
  | @app Γ T₁ T₂ t₁ t₂ h₁ _ ih₁ ih₂ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv₁ | ⟨t₁', hs⟩
      · rcases ih₂ rfl with hv₂ | ⟨t₂', hs⟩
        · obtain ⟨S, body, rfl⟩ := canonical_arrow h₁ hv₁ rfl
          exact .inr ⟨_, .appAbs hv₂⟩
        · exact .inr ⟨_, .app2 hv₁ hs⟩
      · exact .inr ⟨_, .app1 hs⟩
  | tru => intro _; exact .inl .tru
  | fls => intro _; exact .inl .fls
  | ite h₁ _ _ ih₁ _ _ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv₁ | ⟨t₁', hs⟩
      · rcases canonical_bool h₁ hv₁ rfl with rfl | rfl
        · exact .inr ⟨_, .ifTrue⟩
        · exact .inr ⟨_, .ifFalse⟩
      · exact .inr ⟨_, .ifCong hs⟩
  | pair _ _ ih₁ ih₂ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv₁ | ⟨t₁', hs⟩
      · rcases ih₂ rfl with hv₂ | ⟨t₂', hs⟩
        · exact .inl (.pair hv₁ hv₂)
        · exact .inr ⟨_, .pair2 hv₁ hs⟩
      · exact .inr ⟨_, .pair1 hs⟩
  | fst h ih =>
      intro heq
      subst heq
      rcases ih rfl with hv | ⟨t', hs⟩
      · obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := canonical_prod h hv rfl
        exact .inr ⟨_, .pairBeta1 hv₁ hv₂⟩
      · exact .inr ⟨_, .fstCong hs⟩
  | snd h ih =>
      intro heq
      subst heq
      rcases ih rfl with hv | ⟨t', hs⟩
      · obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := canonical_prod h hv rfl
        exact .inr ⟨_, .pairBeta2 hv₁ hv₂⟩
      · exact .inr ⟨_, .sndCong hs⟩
  | sub _ _ ih => exact ih

/-- **Progress (TAPL theorem 15.3.7)**. -/
theorem progress {t : Term} {T : Ty} (h : [] ⊢ t ∶ T) :
    Value t ∨ ∃ t', t ⟶ t' :=
  progress' h rfl

/-! ## Examples -/

/-- `Bool ⊗ Bool <: Top` — everything is below `Top`. -/
example : (Ty.bool ⊗ Ty.bool) <: .top := .top _

/-- Depth subtyping through a product: `Bool ⊗ Bool <: Top ⊗ Bool`. -/
example : (Ty.bool ⊗ Ty.bool) <: (Ty.top ⊗ Ty.bool) :=
  .prod (.top _) (.refl _)

/-- Contravariance: a function accepting `Top` may be used where one
accepting only `Bool` is expected: `Top ⇒ Bool <: Bool ⇒ Bool`. -/
example : (Ty.top ⇒ Ty.bool) <: (Ty.bool ⇒ Ty.bool) :=
  .arrow (.top _) (.refl _)

/-- The identity on `Top` applied to a boolean — accepted via subsumption,
and it evaluates to that boolean. -/
def idTop : Term := abs .top (var 0)

example : [] ⊢ app idTop tru ∶ .top :=
  .app (.abs (.var rfl)) (.sub .tru (.top _))

example : app idTop tru ⟶* tru :=
  .head (.appAbs .tru) (.refl _)

/-- A pair used at a supertype: `{true, false} ∶ Top ⊗ Bool`. -/
example : [] ⊢ pair tru fls ∶ (Ty.top ⊗ Ty.bool) :=
  .sub (.pair .tru .fls) (.prod (.top _) (.refl _))

end Chapter15
