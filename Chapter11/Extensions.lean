/-!
# Chapter 11: Simple Extensions

λ→ from chapter 9 extended with the most important of chapter 11's simple
extensions: the `Unit` type, `let`-bindings, pairs (products), and sums —
each with its values, evaluation rules, and typing rules, and the full
progress/preservation metatheory redone for the extended language.

Ascription, records/variants (generalizing pairs/sums), and the other
extensions of the chapter follow exactly the same patterns; see the README
for the correspondence.
-/

namespace Chapter11

/-- Types (TAPL figures 11-2, 11-4, 11-5, 11-9). -/
inductive Ty : Type where
  | unit
  | bool
  | arrow (T₁ T₂ : Ty)
  | prod (T₁ T₂ : Ty)
  | sum (T₁ T₂ : Ty)
  deriving Repr, DecidableEq

/-- `T₁ ⇒ T₂` is the function type. -/
scoped infixr:60 " ⇒ " => Ty.arrow
/-- `T₁ ⊗ T₂` is the product type `T₁ × T₂`. -/
scoped infixl:65 " ⊗ " => Ty.prod
/-- `T₁ ⊕ T₂` is the sum type `T₁ + T₂`. -/
scoped infixl:64 " ⊕ " => Ty.sum

/-- Terms. Binding constructs (`abs`, `letE`, the two `case` branches)
bind de Bruijn index 0 of their body. `inl`/`inr` carry their full sum
type as an ascription, as in TAPL's `inl t as T`. -/
inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | tru
  | fls
  | ite (t₁ t₂ t₃ : Term)
  | unit
  | letE (t₁ t₂ : Term)          -- let x = t₁ in t₂
  | pair (t₁ t₂ : Term)          -- {t₁, t₂}
  | fst (t : Term)               -- t.1
  | snd (t : Term)               -- t.2
  | inl (T : Ty) (t : Term)      -- inl t as T
  | inr (T : Ty) (t : Term)      -- inr t as T
  | case (t t₁ t₂ : Term)        -- case t of inl x ⇒ t₁ | inr y ⇒ t₂
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
  | unit => unit
  | letE t₁ t₂ => letE (shift d c t₁) (shift d (c + 1) t₂)
  | pair t₁ t₂ => pair (shift d c t₁) (shift d c t₂)
  | fst t => fst (shift d c t)
  | snd t => snd (shift d c t)
  | inl T t => inl T (shift d c t)
  | inr T t => inr T (shift d c t)
  | case t t₁ t₂ =>
      case (shift d c t) (shift d (c + 1) t₁) (shift d (c + 1) t₂)

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
  | unit => unit
  | letE t₁ t₂ => letE (subst k s t₁) (subst (k + 1) s t₂)
  | pair t₁ t₂ => pair (subst k s t₁) (subst k s t₂)
  | fst t => fst (subst k s t)
  | snd t => snd (subst k s t)
  | inl T t => inl T (subst k s t)
  | inr T t => inr T (subst k s t)
  | case t t₁ t₂ =>
      case (subst k s t) (subst (k + 1) s t₁) (subst (k + 1) s t₂)

/-- Shifting by zero is the identity. -/
theorem shift_zero : ∀ (t : Term) (c : Nat), shift 0 c t = t := by
  intro t
  induction t with
  | var n => intro c; by_cases h : n < c <;> simp [shift, h]
  | tru | fls | unit => intro c; rfl
  | abs T t ih => intro c; simp [shift, ih]
  | fst t ih | snd t ih | inl T t ih | inr T t ih => intro c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ | letE t₁ t₂ ih₁ ih₂ | pair t₁ t₂ ih₁ ih₂ =>
      intro c; simp [shift, ih₁, ih₂]
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ | case t t₁ t₂ ih₁ ih₂ ih₃ =>
      intro c; simp [shift, ih₁, ih₂, ih₃]

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
  | tru | fls | unit => intro k c; rfl
  | abs T t ih => intro k c; simp [shift, ih]
  | fst t ih | snd t ih | inl T t ih | inr T t ih => intro k c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ | letE t₁ t₂ ih₁ ih₂ | pair t₁ t₂ ih₁ ih₂ =>
      intro k c; simp [shift, ih₁, ih₂]
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ | case t t₁ t₂ ih₁ ih₂ ih₃ =>
      intro k c; simp [shift, ih₁, ih₂, ih₃]

end Term

open Term

/-- Values: abstractions, the constants, and pairs/injections of values. -/
inductive Value : Term → Prop where
  | abs (T : Ty) (t : Term) : Value (abs T t)
  | tru : Value tru
  | fls : Value fls
  | unit : Value unit
  | pair {v₁ v₂ : Term} : Value v₁ → Value v₂ → Value (pair v₁ v₂)
  | inl {v : Term} (T : Ty) : Value v → Value (inl T v)
  | inr {v : Term} (T : Ty) : Value v → Value (inr T v)

/-- Call-by-value single-step evaluation (TAPL figures 11-1 … 11-9). -/
inductive Step : Term → Term → Prop where
  -- λ→ core
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
  -- let (fig. 11-4)
  | letV {v t : Term} : Value v → Step (letE v t) (subst 0 v t)
  | letCong {t₁ t₁' t₂ : Term} :
      Step t₁ t₁' → Step (letE t₁ t₂) (letE t₁' t₂)
  -- pairs (fig. 11-5)
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
  -- sums (fig. 11-9)
  | caseInl {T : Ty} {v t₁ t₂ : Term} :
      Value v → Step (case (inl T v) t₁ t₂) (subst 0 v t₁)
  | caseInr {T : Ty} {v t₁ t₂ : Term} :
      Value v → Step (case (inr T v) t₁ t₂) (subst 0 v t₂)
  | caseCong {t t' t₁ t₂ : Term} :
      Step t t' → Step (case t t₁ t₂) (case t' t₁ t₂)
  | inlCong {T : Ty} {t t' : Term} :
      Step t t' → Step (inl T t) (inl T t')
  | inrCong {T : Ty} {t t' : Term} :
      Step t t' → Step (inr T t) (inr T t')

@[inherit_doc] scoped infix:50 " ⟶ " => Step

/-- Multi-step evaluation. -/
inductive MultiStep : Term → Term → Prop where
  | refl (t : Term) : MultiStep t t
  | head {t t' t'' : Term} : Step t t' → MultiStep t' t'' → MultiStep t t''

@[inherit_doc] scoped infix:50 " ⟶* " => MultiStep

/-! ## Typing -/

/-- Typing contexts. -/
abbrev Ctx := List Ty

/-- The typing relation for the extended language. -/
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
  | unit {Γ : Ctx} : HasType Γ unit .unit                     -- T-Unit
  | letE {Γ : Ctx} {t₁ t₂ : Term} {T₁ T₂ : Ty} :              -- T-Let
      HasType Γ t₁ T₁ → HasType (T₁ :: Γ) t₂ T₂ →
      HasType Γ (letE t₁ t₂) T₂
  | pair {Γ : Ctx} {t₁ t₂ : Term} {T₁ T₂ : Ty} :              -- T-Pair
      HasType Γ t₁ T₁ → HasType Γ t₂ T₂ →
      HasType Γ (pair t₁ t₂) (T₁ ⊗ T₂)
  | fst {Γ : Ctx} {t : Term} {T₁ T₂ : Ty} :                   -- T-Proj1
      HasType Γ t (T₁ ⊗ T₂) → HasType Γ (fst t) T₁
  | snd {Γ : Ctx} {t : Term} {T₁ T₂ : Ty} :                   -- T-Proj2
      HasType Γ t (T₁ ⊗ T₂) → HasType Γ (snd t) T₂
  | inl {Γ : Ctx} {t : Term} {T₁ T₂ : Ty} :                   -- T-Inl
      HasType Γ t T₁ → HasType Γ (inl (T₁ ⊕ T₂) t) (T₁ ⊕ T₂)
  | inr {Γ : Ctx} {t : Term} {T₁ T₂ : Ty} :                   -- T-Inr
      HasType Γ t T₂ → HasType Γ (inr (T₁ ⊕ T₂) t) (T₁ ⊕ T₂)
  | case {Γ : Ctx} {t t₁ t₂ : Term} {T₁ T₂ T : Ty} :          -- T-Case
      HasType Γ t (T₁ ⊕ T₂) →
      HasType (T₁ :: Γ) t₁ T → HasType (T₂ :: Γ) t₂ T →
      HasType Γ (case t t₁ t₂) T

@[inherit_doc] scoped notation:40 Γ " ⊢ " t " ∶ " T => HasType Γ t T

/-! ## Context insertion (as in chapter 9) -/

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

/-! ## Weakening and substitution -/

/-- Weakening (shift-typing), extended to the new constructs. -/
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
  | unit => intro c S; exact .unit
  | letE _ _ ih₁ ih₂ => intro c S; exact .letE (ih₁ c S) (ih₂ (c + 1) S)
  | pair _ _ ih₁ ih₂ => intro c S; exact .pair (ih₁ c S) (ih₂ c S)
  | fst _ ih => intro c S; exact .fst (ih c S)
  | snd _ ih => intro c S; exact .snd (ih c S)
  | inl _ ih => intro c S; exact .inl (ih c S)
  | inr _ ih => intro c S; exact .inr (ih c S)
  | case _ _ _ ih ih₁ ih₂ =>
      intro c S; exact .case (ih c S) (ih₁ (c + 1) S) (ih₂ (c + 1) S)

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

/-- The substitution lemma for the extended language. -/
theorem substitution :
    ∀ (t : Term) (Γ : Ctx) (k : Nat) (S T : Ty) (s : Term),
      (insertAt S k Γ ⊢ t ∶ T) → (Γ.drop k ⊢ s ∶ S) →
      Γ ⊢ subst k s t ∶ T := by
  intro t
  induction t with
  | var n =>
      intro Γ k S T s ht hs
      cases ht with
      | var hget =>
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
  | abs B t ih =>
      intro Γ k S T s ht hs
      cases ht with
      | abs ht' => exact .abs (ih (B :: Γ) (k + 1) S _ s ht' hs)
  | app t₁ t₂ ih₁ ih₂ =>
      intro Γ k S T s ht hs
      cases ht with
      | app h₁ h₂ =>
          exact .app (ih₁ Γ k S _ s h₁ hs) (ih₂ Γ k S _ s h₂ hs)
  | tru => intro Γ k S T s ht _; cases ht; exact .tru
  | fls => intro Γ k S T s ht _; cases ht; exact .fls
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
      intro Γ k S T s ht hs
      cases ht with
      | ite h₁ h₂ h₃ =>
          exact .ite (ih₁ Γ k S _ s h₁ hs) (ih₂ Γ k S _ s h₂ hs)
            (ih₃ Γ k S _ s h₃ hs)
  | unit => intro Γ k S T s ht _; cases ht; exact .unit
  | letE t₁ t₂ ih₁ ih₂ =>
      intro Γ k S T s ht hs
      cases ht with
      | letE h₁ h₂ =>
          exact .letE (ih₁ Γ k S _ s h₁ hs) (ih₂ (_ :: Γ) (k + 1) S _ s h₂ hs)
  | pair t₁ t₂ ih₁ ih₂ =>
      intro Γ k S T s ht hs
      cases ht with
      | pair h₁ h₂ =>
          exact .pair (ih₁ Γ k S _ s h₁ hs) (ih₂ Γ k S _ s h₂ hs)
  | fst t ih =>
      intro Γ k S T s ht hs
      cases ht with
      | fst h => exact .fst (ih Γ k S _ s h hs)
  | snd t ih =>
      intro Γ k S T s ht hs
      cases ht with
      | snd h => exact .snd (ih Γ k S _ s h hs)
  | inl B t ih =>
      intro Γ k S T s ht hs
      cases ht with
      | inl h => exact .inl (ih Γ k S _ s h hs)
  | inr B t ih =>
      intro Γ k S T s ht hs
      cases ht with
      | inr h => exact .inr (ih Γ k S _ s h hs)
  | case t t₁ t₂ ih ih₁ ih₂ =>
      intro Γ k S T s ht hs
      cases ht with
      | case h h₁ h₂ =>
          exact .case (ih Γ k S _ s h hs) (ih₁ (_ :: Γ) (k + 1) S _ s h₁ hs)
            (ih₂ (_ :: Γ) (k + 1) S _ s h₂ hs)

/-! ## Preservation and progress -/

/-- **Preservation** for the extended language. -/
theorem preservation {Γ : Ctx} {t t' : Term} {T : Ty} (hs : t ⟶ t') :
    (Γ ⊢ t ∶ T) → Γ ⊢ t' ∶ T := by
  induction hs generalizing T with
  | appAbs _ =>
      intro h
      cases h with
      | app h₁ h₂ =>
          cases h₁ with
          | abs hbody => exact substitution _ _ 0 _ T _ hbody h₂
  | app1 _ ih =>
      intro h
      cases h with
      | app h₁ h₂ => exact .app (ih h₁) h₂
  | app2 _ _ ih =>
      intro h
      cases h with
      | app h₁ h₂ => exact .app h₁ (ih h₂)
  | ifTrue =>
      intro h
      cases h with
      | ite _ h₂ _ => exact h₂
  | ifFalse =>
      intro h
      cases h with
      | ite _ _ h₃ => exact h₃
  | ifCong _ ih =>
      intro h
      cases h with
      | ite h₁ h₂ h₃ => exact .ite (ih h₁) h₂ h₃
  | letV _ =>
      intro h
      cases h with
      | letE h₁ h₂ => exact substitution _ _ 0 _ T _ h₂ h₁
  | letCong _ ih =>
      intro h
      cases h with
      | letE h₁ h₂ => exact .letE (ih h₁) h₂
  | pairBeta1 _ _ =>
      intro h
      cases h with
      | fst hp =>
          cases hp with
          | pair h₁ _ => exact h₁
  | pairBeta2 _ _ =>
      intro h
      cases h with
      | snd hp =>
          cases hp with
          | pair _ h₂ => exact h₂
  | fstCong _ ih =>
      intro h
      cases h with
      | fst hp => exact .fst (ih hp)
  | sndCong _ ih =>
      intro h
      cases h with
      | snd hp => exact .snd (ih hp)
  | pair1 _ ih =>
      intro h
      cases h with
      | pair h₁ h₂ => exact .pair (ih h₁) h₂
  | pair2 _ _ ih =>
      intro h
      cases h with
      | pair h₁ h₂ => exact .pair h₁ (ih h₂)
  | caseInl _ =>
      intro h
      cases h with
      | case hsum h₁ h₂ =>
          cases hsum with
          | inl hv => exact substitution _ _ 0 _ T _ h₁ hv
  | caseInr _ =>
      intro h
      cases h with
      | case hsum h₁ h₂ =>
          cases hsum with
          | inr hv => exact substitution _ _ 0 _ T _ h₂ hv
  | caseCong _ ih =>
      intro h
      cases h with
      | case hsum h₁ h₂ => exact .case (ih hsum) h₁ h₂
  | inlCong _ ih =>
      intro h
      cases h with
      | inl h' => exact .inl (ih h')
  | inrCong _ ih =>
      intro h
      cases h with
      | inr h' => exact .inr (ih h')

/-- Progress, auxiliary version with a context equation. -/
theorem progress' {Γ : Ctx} {t : Term} {T : Ty} (h : Γ ⊢ t ∶ T) :
    Γ = [] → Value t ∨ ∃ t', t ⟶ t' := by
  induction h with
  | @var Γ n T hget =>
      intro heq
      subst heq
      simp [List.get?] at hget
  | abs _ _ => intro _; exact .inl (.abs _ _)
  | app h₁ _ ih₁ ih₂ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv₁ | ⟨t₁', hs⟩
      · rcases ih₂ rfl with hv₂ | ⟨t₂', hs⟩
        · cases hv₁ with
          | abs T t => exact .inr ⟨_, .appAbs hv₂⟩
          | tru | fls | unit => cases h₁
          | pair _ _ => cases h₁
          | inl _ _ => cases h₁
          | inr _ _ => cases h₁
        · exact .inr ⟨_, .app2 hv₁ hs⟩
      · exact .inr ⟨_, .app1 hs⟩
  | tru => intro _; exact .inl .tru
  | fls => intro _; exact .inl .fls
  | ite h₁ _ _ ih₁ _ _ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv₁ | ⟨t₁', hs⟩
      · cases hv₁ with
        | tru => exact .inr ⟨_, .ifTrue⟩
        | fls => exact .inr ⟨_, .ifFalse⟩
        | abs T t => cases h₁
        | unit => cases h₁
        | pair _ _ => cases h₁
        | inl _ _ => cases h₁
        | inr _ _ => cases h₁
      · exact .inr ⟨_, .ifCong hs⟩
  | unit => intro _; exact .inl .unit
  | letE _ _ ih₁ _ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv₁ | ⟨t₁', hs⟩
      · exact .inr ⟨_, .letV hv₁⟩
      · exact .inr ⟨_, .letCong hs⟩
  | pair _ _ ih₁ ih₂ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv₁ | ⟨t₁', hs⟩
      · rcases ih₂ rfl with hv₂ | ⟨t₂', hs⟩
        · exact .inl (.pair hv₁ hv₂)
        · exact .inr ⟨_, .pair2 hv₁ hs⟩
      · exact .inr ⟨_, .pair1 hs⟩
  | @fst Γ t T₁ T₂ h ih =>
      intro heq
      subst heq
      rcases ih rfl with hv | ⟨t', hs⟩
      · cases hv with
        | pair hv₁ hv₂ => exact .inr ⟨_, .pairBeta1 hv₁ hv₂⟩
        | abs T t => cases h
        | tru | fls | unit => cases h
        | inl _ _ => cases h
        | inr _ _ => cases h
      · exact .inr ⟨_, .fstCong hs⟩
  | @snd Γ t T₁ T₂ h ih =>
      intro heq
      subst heq
      rcases ih rfl with hv | ⟨t', hs⟩
      · cases hv with
        | pair hv₁ hv₂ => exact .inr ⟨_, .pairBeta2 hv₁ hv₂⟩
        | abs T t => cases h
        | tru | fls | unit => cases h
        | inl _ _ => cases h
        | inr _ _ => cases h
      · exact .inr ⟨_, .sndCong hs⟩
  | inl _ ih =>
      intro heq
      subst heq
      rcases ih rfl with hv | ⟨t', hs⟩
      · exact .inl (.inl _ hv)
      · exact .inr ⟨_, .inlCong hs⟩
  | inr _ ih =>
      intro heq
      subst heq
      rcases ih rfl with hv | ⟨t', hs⟩
      · exact .inl (.inr _ hv)
      · exact .inr ⟨_, .inrCong hs⟩
  | @case Γ t t₁ t₂ T₁ T₂ T h _ _ ih _ _ =>
      intro heq
      subst heq
      rcases ih rfl with hv | ⟨t', hs⟩
      · cases hv with
        | inl _ hv => exact .inr ⟨_, .caseInl hv⟩
        | inr _ hv => exact .inr ⟨_, .caseInr hv⟩
        | abs T t => cases h
        | tru | fls | unit => cases h
        | pair _ _ => cases h
      · exact .inr ⟨_, .caseCong hs⟩

/-- **Progress** for the extended language. -/
theorem progress {t : Term} {T : Ty} (h : [] ⊢ t ∶ T) :
    Value t ∨ ∃ t', t ⟶ t' :=
  progress' h rfl

/-! ## Type safety -/

/-- A term is a normal form if it cannot step. -/
def NormalForm (t : Term) : Prop := ¬ ∃ t', t ⟶ t'

theorem preservation_multi {t t' : Term} {T : Ty} (h : [] ⊢ t ∶ T)
    (hs : t ⟶* t') : [] ⊢ t' ∶ T := by
  induction hs with
  | refl _ => exact h
  | head s _ ih => exact ih (preservation s h)

/-- Type safety for the extended language. -/
theorem safety {t t' : Term} {T : Ty} (h : [] ⊢ t ∶ T) (hs : t ⟶* t')
    (hn : NormalForm t') : Value t' := by
  rcases progress (preservation_multi h hs) with hv | hstep
  · exact hv
  · exact absurd hstep hn

/-! ## Examples -/

/-- `swap : Bool ⊗ Unit ⇒ Unit ⊗ Bool`, `λp. {p.2, p.1}`. -/
def swapTerm : Term := abs (.bool ⊗ .unit) (pair (snd (var 0)) (fst (var 0)))

example : [] ⊢ swapTerm ∶ (.bool ⊗ .unit) ⇒ (.unit ⊗ .bool) :=
  .abs (.pair (.snd (.var rfl)) (.fst (.var rfl)))

/-- `swap {true, unit}` evaluates to `{unit, true}`. -/
example : app swapTerm (pair tru unit) ⟶* pair unit tru :=
  .head (.appAbs (.pair .tru .unit))
    (.head (.pair1 (.pairBeta2 .tru .unit))
      (.head (.pair2 .unit (.pairBeta1 .tru .unit))
        (.refl _)))

/-- `let x = fst {true, unit} in if x then unit else unit ∶ Unit`. -/
example : [] ⊢ letE (fst (pair tru unit)) (ite (var 0) unit unit) ∶ .unit :=
  .letE (.fst (.pair .tru .unit)) (.ite (.var rfl) .unit .unit)

/-- An option-like use of sums: `getOrElse ∶ Bool ⊕ Unit ⇒ Bool` returning
the payload of `inl` and `false` for `inr`. -/
def getOrElse : Term :=
  abs (.bool ⊕ .unit) (case (var 0) (var 0) fls)

example : [] ⊢ getOrElse ∶ (.bool ⊕ .unit) ⇒ .bool :=
  .abs (.case (.var rfl) (.var rfl) .fls)

/-- `getOrElse (inl true) ⟶* true`. -/
example : app getOrElse (inl (.bool ⊕ .unit) tru) ⟶* tru :=
  .head (.appAbs (.inl _ .tru)) (.head (.caseInl .tru) (.refl _))

/-- `getOrElse (inr unit) ⟶* false`. -/
example : app getOrElse (inr (.bool ⊕ .unit) unit) ⟶* fls :=
  .head (.appAbs (.inr _ .unit)) (.head (.caseInr .unit) (.refl _))

end Chapter11
