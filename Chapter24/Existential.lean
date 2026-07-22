/-!
# Chapter 24: Existential Types

System F from chapter 23 extended with existential types `{∃X, T}` and
their introduction/elimination forms `{*U, t} as T` (`pack`) and
`let {X, x} = t₁ in t₂` (`unpack`) — the type-theoretic account of
**abstract data types**: a package hides a witness type `U` behind an
abstract name `X` (TAPL figure 24-1).

The whole two-level de Bruijn infrastructure of chapter 23 is carried
over; `unpack` is the interesting new binder, binding a *type* variable
and a *term* variable at once.
-/

namespace Chapter24

/-- Types: System F plus existentials (`exi T` is `{∃X, T}`, binding
type-variable 0 of `T`). -/
inductive Ty : Type where
  | var (n : Nat)
  | arrow (T₁ T₂ : Ty)
  | all (T : Ty)
  | exi (T : Ty)
  deriving Repr, DecidableEq

/-- `T₁ ⇒ T₂` is the function type. -/
scoped infixr:60 " ⇒ " => Ty.arrow

namespace Ty

/-- Shift type variables `≥ c` up by `d`. -/
def tshift (d c : Nat) : Ty → Ty
  | var n => if n < c then var n else var (n + d)
  | arrow T₁ T₂ => arrow (tshift d c T₁) (tshift d c T₂)
  | all T => all (tshift d (c + 1) T)
  | exi T => exi (tshift d (c + 1) T)

/-- Type-level substitution `[k ↦ S] T` (substitute and decrement). -/
def tsubst (k : Nat) (S : Ty) : Ty → Ty
  | var n =>
      if n < k then var n
      else if n = k then tshift k 0 S
      else var (n - 1)
  | arrow T₁ T₂ => arrow (tsubst k S T₁) (tsubst k S T₂)
  | all T => all (tsubst (k + 1) S T)
  | exi T => exi (tsubst (k + 1) S T)

/-! ### The de Bruijn algebra for types (as in chapters 6 and 23) -/

theorem tshift_zero (T : Ty) : ∀ c, tshift 0 c T = T := by
  induction T with
  | var n => intro c; by_cases h : n < c <;> simp [tshift, h]
  | arrow T₁ T₂ ih₁ ih₂ => intro c; simp [tshift, ih₁, ih₂]
  | all T ih | exi T ih => intro c; simp [tshift, ih]

theorem tshift_merge (T : Ty) :
    ∀ d d' c c', c ≤ c' → c' ≤ c + d' →
      tshift d c' (tshift d' c T) = tshift (d + d') c T := by
  induction T with
  | var n =>
      intro d d' c c' h₁ h₂
      by_cases h : n < c
      · have h' : n < c' := by omega
        simp [tshift, h, h']
      · have h' : ¬ n + d' < c' := by omega
        simp [tshift, h, h']
        omega
  | arrow T₁ T₂ ih₁ ih₂ =>
      intro d d' c c' h₁ h₂
      simp only [tshift]
      rw [ih₁ d d' c c' h₁ h₂, ih₂ d d' c c' h₁ h₂]
  | all T ih | exi T ih =>
      intro d d' c c' h₁ h₂
      simp only [tshift]
      rw [ih d d' (c + 1) (c' + 1) (by omega) (by omega)]

theorem tshift_comm (T : Ty) :
    ∀ d d' c c', c' ≤ c →
      tshift d' c' (tshift d c T) = tshift d (c + d') (tshift d' c' T) := by
  induction T with
  | var n =>
      intro d d' c c' h
      by_cases h₁ : n < c'
      · have h₂ : n < c := by omega
        have h₃ : n < c + d' := by omega
        simp [tshift, h₁, h₂, h₃]
      · by_cases h₂ : n < c
        · have h₃ : n + d' < c + d' := by omega
          simp [tshift, h₁, h₂, h₃]
        · have h₃ : ¬ n + d < c' := by omega
          have h₄ : ¬ n + d' < c + d' := by omega
          simp [tshift, h₁, h₂, h₃, h₄]
          omega
  | arrow T₁ T₂ ih₁ ih₂ =>
      intro d d' c c' h
      simp only [tshift]
      rw [ih₁ d d' c c' h, ih₂ d d' c c' h]
  | all T ih | exi T ih =>
      intro d d' c c' h
      simp only [tshift]
      rw [ih d d' (c + 1) (c' + 1) (by omega)]
      have : c + 1 + d' = c + d' + 1 := by omega
      rw [this]

theorem tsubst_tshift_cancel (T : Ty) :
    ∀ S k d c, c ≤ k → k < c + d + 1 →
      tsubst k S (tshift (d + 1) c T) = tshift d c T := by
  induction T with
  | var n =>
      intro S k d c h₁ h₂
      by_cases h : n < c
      · have h' : n < k := by omega
        simp [tshift, tsubst, h, h']
      · have h₃ : ¬ n + (d + 1) < k := by omega
        have h₄ : ¬ n + (d + 1) = k := by omega
        simp [tshift, tsubst, h, h₃, h₄]
        omega
  | arrow T₁ T₂ ih₁ ih₂ =>
      intro S k d c h₁ h₂
      simp only [tshift, tsubst]
      rw [ih₁ S k d c h₁ h₂, ih₂ S k d c h₁ h₂]
  | all T ih | exi T ih =>
      intro S k d c h₁ h₂
      simp only [tshift, tsubst]
      rw [ih S (k + 1) d (c + 1) (by omega) (by omega)]

/-- The `k = 0, d = 0` corner of the cancellation law, used to collapse
contexts and types after eliminating a type binder. -/
theorem tsubst_tshift_cancel0 (T S : Ty) :
    tsubst 0 S (tshift 1 0 T) = T := by
  have := tsubst_tshift_cancel T S 0 0 0 (by omega) (by omega)
  simpa [tshift_zero] using this

theorem tshift_tsubst_dist (T : Ty) :
    ∀ S d c k,
      tshift d (c + k) (tsubst k S T) =
        tsubst k (tshift d c S) (tshift d (c + k + 1) T) := by
  induction T with
  | var n =>
      intro S d c k
      by_cases h₁ : n < k
      · have h₂ : n < c + k := by omega
        have h₃ : n < c + k + 1 := by omega
        simp [tshift, tsubst, h₁, h₂, h₃]
      · by_cases h₂ : n = k
        · subst h₂
          have h₃ : n < c + n + 1 := by omega
          simp [tshift, tsubst, h₃, Nat.lt_irrefl]
          rw [← tshift_comm S d n c 0 (by omega)]
        · by_cases h₃ : n < c + k + 1
          · have h₄ : n - 1 < c + k := by omega
            simp [tshift, tsubst, h₁, h₂, h₃, h₄]
          · have h₄ : ¬ n - 1 < c + k := by omega
            have h₅ : ¬ n + d < k := by omega
            have h₆ : ¬ n + d = k := by omega
            simp [tshift, tsubst, h₁, h₂, h₃, h₄, h₅, h₆]
            omega
  | arrow T₁ T₂ ih₁ ih₂ =>
      intro S d c k
      simp only [tshift, tsubst]
      rw [ih₁ S d c k, ih₂ S d c k]
  | all T ih | exi T ih =>
      intro S d c k
      simp only [tshift, tsubst]
      have h1 : c + k + 1 = c + (k + 1) := by omega
      rw [h1, ih S d c (k + 1)]

theorem tsubst_tshift_dist (T : Ty) :
    ∀ S d c k, c + d ≤ k →
      tsubst k S (tshift d c T) = tshift d c (tsubst (k - d) S T) := by
  induction T with
  | var n =>
      intro S d c k h
      by_cases h₁ : n < c
      · have h₂ : n < k := by omega
        have h₃ : n < k - d := by omega
        simp [tshift, tsubst, h₁, h₂, h₃]
      · by_cases h₂ : n + d < k
        · have h₃ : n < k - d := by omega
          simp [tshift, tsubst, h₁, h₂, h₃]
        · by_cases h₃ : n + d = k
          · have h₄ : n = k - d := by omega
            subst h₄
            have hk : k - d + d = k := by omega
            simp [tshift, tsubst, h₁, hk, Nat.lt_irrefl]
            rw [tshift_merge S d (k - d) 0 c (by omega) (by omega)]
            have : d + (k - d) = k := by omega
            rw [this]
          · have h₄ : ¬ n < k - d := by omega
            have h₅ : ¬ n = k - d := by omega
            have h₆ : ¬ n - 1 < c := by omega
            simp [tshift, tsubst, h₁, h₂, h₃, h₄, h₅, h₆]
            omega
  | arrow T₁ T₂ ih₁ ih₂ =>
      intro S d c k h
      simp only [tshift, tsubst]
      rw [ih₁ S d c k h, ih₂ S d c k h]
  | all T ih | exi T ih =>
      intro S d c k h
      simp only [tshift, tsubst]
      rw [ih S d (c + 1) (k + 1) (by omega)]
      have : k + 1 - d = k - d + 1 := by omega
      rw [this]

theorem tsubst_tsubst (T : Ty) :
    ∀ S U j k, j ≤ k →
      tsubst k S (tsubst j U T) =
        tsubst j (tsubst (k - j) S U) (tsubst (k + 1) S T) := by
  induction T with
  | var n =>
      intro S U j k h
      by_cases h₁ : n < j
      · have h₂ : n < k := by omega
        have h₃ : n < k + 1 := by omega
        simp [tsubst, h₁, h₂, h₃]
      · by_cases h₂ : n = j
        · subst h₂
          have h₃ : n < k + 1 := by omega
          simp [tsubst, h₁, h₃, Nat.lt_irrefl]
          rw [tsubst_tshift_dist U S n 0 k (by omega)]
        · by_cases h₃ : n < k + 1
          · have h₄ : n - 1 < k := by omega
            simp [tsubst, h₁, h₂, h₃, h₄]
          · by_cases h₄ : n = k + 1
            · subst h₄
              have h₅ : ¬ k + 1 - 1 < k := by omega
              have h₆ : k + 1 - 1 = k := by omega
              simp [tsubst, h₁, h₂, h₃, h₅, h₆, Nat.lt_irrefl]
              rw [tsubst_tshift_cancel S _ j k 0 (by omega) (by omega)]
            · have h₅ : ¬ n - 1 < k := by omega
              have h₆ : ¬ n - 1 = k := by omega
              have h₇ : ¬ n - 1 < j := by omega
              have h₈ : ¬ n - 1 = j := by omega
              simp [tsubst, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  | arrow T₁ T₂ ih₁ ih₂ =>
      intro S U j k h
      simp only [tsubst]
      rw [ih₁ S U j k h, ih₂ S U j k h]
  | all T ih | exi T ih =>
      intro S U j k h
      simp only [tsubst]
      rw [ih S U (j + 1) (k + 1) (by omega)]
      have : k + 1 - (j + 1) = k - j := by omega
      rw [this]

end Ty

open Ty

/-- Terms: System F plus `pack U t T` (`{*U, t} as T`) and `unpack t₁ t₂`
(`let {X, x} = t₁ in t₂`, binding type-variable 0 *and* term-variable 0
of `t₂`). -/
inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | tabs (t : Term)
  | tapp (t : Term) (T : Ty)
  | pack (U : Ty) (t : Term) (T : Ty)
  | unpack (t₁ t₂ : Term)
  deriving Repr, DecidableEq

namespace Term

/-- Shift the *term* variables of `t` that are `≥ c` up by `d`. -/
def shift (d c : Nat) : Term → Term
  | var n => if n < c then var n else var (n + d)
  | abs T t => abs T (shift d (c + 1) t)
  | app t₁ t₂ => app (shift d c t₁) (shift d c t₂)
  | tabs t => tabs (shift d c t)
  | tapp t T => tapp (shift d c t) T
  | pack U t T => pack U (shift d c t) T
  | unpack t₁ t₂ => unpack (shift d c t₁) (shift d (c + 1) t₂)

/-- Shift the *type* variables of `t` that are `≥ c` up by `d`. -/
def tshiftT (d c : Nat) : Term → Term
  | var n => var n
  | abs T t => abs (tshift d c T) (tshiftT d c t)
  | app t₁ t₂ => app (tshiftT d c t₁) (tshiftT d c t₂)
  | tabs t => tabs (tshiftT d (c + 1) t)
  | tapp t T => tapp (tshiftT d c t) (tshift d c T)
  | pack U t T => pack (tshift d c U) (tshiftT d c t) (tshift d c T)
  | unpack t₁ t₂ => unpack (tshiftT d c t₁) (tshiftT d (c + 1) t₂)

/-- Term-level substitution `[k ↦ s] t`; crossing a type binder (`tabs`
or `unpack`) type-shifts the substituted term. -/
def subst (k : Nat) (s : Term) : Term → Term
  | var n =>
      if n < k then var n
      else if n = k then shift k 0 s
      else var (n - 1)
  | abs T t => abs T (subst (k + 1) s t)
  | app t₁ t₂ => app (subst k s t₁) (subst k s t₂)
  | tabs t => tabs (subst k (tshiftT 1 0 s) t)
  | tapp t T => tapp (subst k s t) T
  | pack U t T => pack U (subst k s t) T
  | unpack t₁ t₂ => unpack (subst k s t₁) (subst (k + 1) (tshiftT 1 0 s) t₂)

/-- Type substitution in a term. -/
def tsubstT (k : Nat) (S : Ty) : Term → Term
  | var n => var n
  | abs T t => abs (tsubst k S T) (tsubstT k S t)
  | app t₁ t₂ => app (tsubstT k S t₁) (tsubstT k S t₂)
  | tabs t => tabs (tsubstT (k + 1) S t)
  | tapp t T => tapp (tsubstT k S t) (tsubst k S T)
  | pack U t T => pack (tsubst k S U) (tsubstT k S t) (tsubst k S T)
  | unpack t₁ t₂ => unpack (tsubstT k S t₁) (tsubstT (k + 1) S t₂)

/-- Term-shifting by zero is the identity. -/
theorem shift_zero : ∀ (t : Term) (c : Nat), shift 0 c t = t := by
  intro t
  induction t with
  | var n => intro c; by_cases h : n < c <;> simp [shift, h]
  | abs T t ih | tabs t ih | tapp t T ih => intro c; simp [shift, ih]
  | pack U t T ih => intro c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ | unpack t₁ t₂ ih₁ ih₂ =>
      intro c; simp [shift, ih₁, ih₂]

/-- Successive one-place term shifts accumulate. -/
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
  | abs T t ih | tabs t ih | tapp t T ih => intro k c; simp [shift, ih]
  | pack U t T ih => intro k c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ | unpack t₁ t₂ ih₁ ih₂ =>
      intro k c; simp [shift, ih₁, ih₂]

end Term

open Term

/-- Values: the two abstractions and packed values. -/
inductive Value : Term → Prop where
  | abs (T : Ty) (t : Term) : Value (abs T t)
  | tabs (t : Term) : Value (tabs t)
  | pack {v : Term} (U T : Ty) : Value v → Value (pack U v T)

/-- Call-by-value single-step evaluation (TAPL figure 24-1). Unpacking a
package substitutes the hidden witness type and the packed value into the
body. -/
inductive Step : Term → Term → Prop where
  | appAbs {T : Ty} {t v : Term} :
      Value v → Step (app (abs T t) v) (subst 0 v t)
  | app1 {t₁ t₁' t₂ : Term} :
      Step t₁ t₁' → Step (app t₁ t₂) (app t₁' t₂)
  | app2 {v t t' : Term} :
      Value v → Step t t' → Step (app v t) (app v t')
  | tappTabs {t : Term} {S : Ty} :
      Step (tapp (tabs t) S) (tsubstT 0 S t)
  | tappCong {t t' : Term} {S : Ty} :
      Step t t' → Step (tapp t S) (tapp t' S)
  | unpackPack {U T : Ty} {v t₂ : Term} :                     -- E-UnpackPack
      Value v →
      Step (unpack (pack U v T) t₂) (subst 0 v (tsubstT 0 U t₂))
  | packCong {U T : Ty} {t t' : Term} :                       -- E-Pack
      Step t t' → Step (pack U t T) (pack U t' T)
  | unpackCong {t₁ t₁' t₂ : Term} :                           -- E-Unpack
      Step t₁ t₁' → Step (unpack t₁ t₂) (unpack t₁' t₂)

@[inherit_doc] scoped infix:50 " ⟶ " => Step

/-- Multi-step evaluation. -/
inductive MultiStep : Term → Term → Prop where
  | refl (t : Term) : MultiStep t t
  | head {t t' t'' : Term} : Step t t' → MultiStep t' t'' → MultiStep t t''

@[inherit_doc] scoped infix:50 " ⟶* " => MultiStep

/-! ## Typing -/

/-- Typing contexts (term bindings only; type binders shift the context,
as in chapter 23). -/
abbrev Ctx := List Ty

/-- The typing relation (TAPL figure 24-1). In `T-Unpack`, the body is
typed under the abstract type binder (context shifted, bound type on top)
and its type `tshift 1 0 T₂` cannot mention the abstract variable — the
scoping side-condition of the named presentation. -/
inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ : Ctx} {n : Nat} {T : Ty} :
      Γ.get? n = some T → HasType Γ (var n) T
  | abs {Γ : Ctx} {T₁ T₂ : Ty} {t : Term} :
      HasType (T₁ :: Γ) t T₂ → HasType Γ (abs T₁ t) (T₁ ⇒ T₂)
  | app {Γ : Ctx} {T₁ T₂ : Ty} {t₁ t₂ : Term} :
      HasType Γ t₁ (T₁ ⇒ T₂) → HasType Γ t₂ T₁ →
      HasType Γ (app t₁ t₂) T₂
  | tabs {Γ : Ctx} {t : Term} {T : Ty} :
      HasType (Γ.map (tshift 1 0)) t T →
      HasType Γ (tabs t) (.all T)
  | tapp {Γ : Ctx} {t : Term} {T S : Ty} :
      HasType Γ t (.all T) →
      HasType Γ (tapp t S) (tsubst 0 S T)
  | pack {Γ : Ctx} {U T₂ : Ty} {t : Term} :                   -- T-Pack
      HasType Γ t (tsubst 0 U T₂) →
      HasType Γ (pack U t (.exi T₂)) (.exi T₂)
  | unpack {Γ : Ctx} {T₁₂ T₂ : Ty} {t₁ t₂ : Term} :           -- T-Unpack
      HasType Γ t₁ (.exi T₁₂) →
      HasType (T₁₂ :: Γ.map (tshift 1 0)) t₂ (tshift 1 0 T₂) →
      HasType Γ (unpack t₁ t₂) T₂

@[inherit_doc] scoped notation:40 Γ " ⊢ " t " ∶ " T => HasType Γ t T

/-! ## List lemmas (as in chapter 23) -/

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

/-- `map` commutes with `insertAt`. -/
theorem map_insertAt (f : Ty → Ty) (S : Ty) :
    ∀ c Γ, (insertAt S c Γ).map f = insertAt (f S) c (Γ.map f) := by
  intro c
  induction c with
  | zero => intro Γ; rfl
  | succ c ih =>
      intro Γ
      cases Γ with
      | nil => rfl
      | cons T Γ => simp [insertAt, List.map, ih Γ]

/-- `map` commutes with `drop`. -/
theorem map_drop (f : Ty → Ty) :
    ∀ (k : Nat) (Γ : Ctx), (Γ.map f).drop k = (Γ.drop k).map f := by
  intro k
  induction k with
  | zero => intro Γ; rfl
  | succ k ih =>
      intro Γ
      cases Γ with
      | nil => rfl
      | cons T Γ => exact ih Γ

/-- Pointwise-equal functions map lists equally. -/
theorem map_ext (f g : Ty → Ty) (h : ∀ X, f X = g X) :
    ∀ Γ : Ctx, Γ.map f = Γ.map g := by
  intro Γ
  induction Γ with
  | nil => rfl
  | cons T Γ ih => simp only [List.map, h T, ih]

/-- Lookup in a mapped context. -/
theorem get?_map (f : Ty → Ty) :
    ∀ (Γ : Ctx) (n : Nat) (T : Ty),
      Γ.get? n = some T → (Γ.map f).get? n = some (f T) := by
  intro Γ
  induction Γ with
  | nil => intro n T h; cases h
  | cons B Γ ih =>
      intro n T h
      cases n with
      | zero => cases h; rfl
      | succ n => exact ih n T h

/-- Substituting into a freshly-shifted context is the identity. -/
theorem map_tsubst_tshift_cancel (S : Ty) :
    ∀ Γ : Ctx, (Γ.map (tshift 1 0)).map (tsubst 0 S) = Γ := by
  intro Γ
  induction Γ with
  | nil => rfl
  | cons T Γ ih =>
      simp only [List.map]
      rw [ih, tsubst_tshift_cancel0]

/-! ## Weakening lemmas -/

/-- **Term weakening**. -/
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
  | tabs _ ih =>
      intro c S
      apply HasType.tabs
      rw [map_insertAt]
      exact ih c (tshift 1 0 S)
  | tapp _ ih => intro c S; exact .tapp (ih c S)
  | pack _ ih => intro c S; exact .pack (ih c S)
  | unpack _ _ ih₁ ih₂ =>
      intro c S
      apply HasType.unpack (ih₁ c S)
      rw [map_insertAt]
      exact ih₂ (c + 1) (tshift 1 0 S)

/-- **Type weakening**. -/
theorem tweakening {Γ : Ctx} {t : Term} {T : Ty} (h : Γ ⊢ t ∶ T) :
    ∀ c, Γ.map (tshift 1 c) ⊢ tshiftT 1 c t ∶ tshift 1 c T := by
  induction h with
  | var hget => intro c; exact .var (get?_map _ _ _ _ hget)
  | abs _ ih => intro c; exact .abs (ih c)
  | app _ _ ih₁ ih₂ => intro c; exact .app (ih₁ c) (ih₂ c)
  | @tabs Γ t T _ ih =>
      intro c
      apply HasType.tabs
      have hih := ih (c + 1)
      rw [List.map_map] at hih ⊢
      have hmap : Γ.map (tshift 1 (c + 1) ∘ tshift 1 0) =
          Γ.map (tshift 1 0 ∘ tshift 1 c) :=
        map_ext _ _
          (fun X => by
            simp only [Function.comp]
            exact (tshift_comm X 1 1 c 0 (by omega)).symm) Γ
      rw [hmap] at hih
      exact hih
  | @tapp Γ t T S _ ih =>
      intro c
      have h' := HasType.tapp (S := tshift 1 c S) (ih c)
      have : tsubst 0 (tshift 1 c S) (tshift 1 (c + 1) T) =
          tshift 1 c (tsubst 0 S T) := by
        have := tshift_tsubst_dist T S 1 c 0
        simpa using this.symm
      rw [this] at h'
      exact h'
  | @pack Γ U T₂ t _ ih =>
      intro c
      apply HasType.pack
      have := ih c
      have heq : tshift 1 c (tsubst 0 U T₂) =
          tsubst 0 (tshift 1 c U) (tshift 1 (c + 1) T₂) := by
        have := tshift_tsubst_dist T₂ U 1 c 0
        simpa using this
      rw [heq] at this
      exact this
  | @unpack Γ T₁₂ T₂ t₁ t₂ _ _ ih₁ ih₂ =>
      intro c
      apply HasType.unpack (ih₁ c)
      have hih := ih₂ (c + 1)
      simp only [List.map] at hih
      rw [List.map_map] at hih
      have hmap : Γ.map (tshift 1 (c + 1) ∘ tshift 1 0) =
          Γ.map (tshift 1 0 ∘ tshift 1 c) :=
        map_ext _ _
          (fun X => by
            simp only [Function.comp]
            exact (tshift_comm X 1 1 c 0 (by omega)).symm) Γ
      rw [hmap] at hih
      have hty : tshift 1 (c + 1) (tshift 1 0 T₂) =
          tshift 1 0 (tshift 1 c T₂) :=
        (tshift_comm T₂ 1 1 c 0 (by omega)).symm
      rw [hty] at hih
      rw [List.map_map]
      exact hih

/-- Iterated term weakening at the bottom of the context. -/
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

/-! ## The two substitution lemmas -/

/-- **Term-substitution lemma**. -/
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
  | tabs _ ih =>
      intro Γ k S s heq hs
      apply HasType.tabs
      apply ih (Γ.map (tshift 1 0)) k (tshift 1 0 S) (tshiftT 1 0 s)
      · rw [heq, map_insertAt]
      · rw [map_drop]
        exact tweakening hs 0
  | tapp _ ih =>
      intro Γ k S s heq hs
      exact .tapp (ih Γ k S s heq hs)
  | pack _ ih =>
      intro Γ k S s heq hs
      exact .pack (ih Γ k S s heq hs)
  | @unpack Δ T₁₂ T₂ t₁ t₂ _ _ ih₁ ih₂ =>
      intro Γ k S s heq hs
      apply HasType.unpack (ih₁ Γ k S s heq hs)
      apply ih₂ (T₁₂ :: Γ.map (tshift 1 0)) (k + 1) (tshift 1 0 S)
        (tshiftT 1 0 s)
      · rw [heq, map_insertAt]
        rfl
      · show (Γ.map (tshift 1 0)).drop k ⊢ tshiftT 1 0 s ∶ tshift 1 0 S
        rw [map_drop]
        exact tweakening hs 0

/-- **Type-substitution lemma**. -/
theorem tsubstitution {Δ : Ctx} {t : Term} {T : Ty} (ht : Δ ⊢ t ∶ T) :
    ∀ (k : Nat) (S : Ty),
      Δ.map (tsubst k S) ⊢ tsubstT k S t ∶ tsubst k S T := by
  induction ht with
  | var hget => intro k S; exact .var (get?_map _ _ _ _ hget)
  | abs _ ih => intro k S; exact .abs (ih k S)
  | app _ _ ih₁ ih₂ => intro k S; exact .app (ih₁ k S) (ih₂ k S)
  | @tabs Δ t T _ ih =>
      intro k S
      apply HasType.tabs
      have hih := ih (k + 1) S
      rw [List.map_map] at hih ⊢
      have hmap : Δ.map (tsubst (k + 1) S ∘ tshift 1 0) =
          Δ.map (tshift 1 0 ∘ tsubst k S) :=
        map_ext _ _
          (fun X => by
            simp only [Function.comp]
            exact tsubst_tshift_dist X S 1 0 (k + 1) (by omega)) Δ
      rw [hmap] at hih
      exact hih
  | @tapp Δ t T S₂ _ ih =>
      intro k S
      have h' := HasType.tapp (S := tsubst k S S₂) (ih k S)
      have : tsubst 0 (tsubst k S S₂) (tsubst (k + 1) S T) =
          tsubst k S (tsubst 0 S₂ T) := by
        have := tsubst_tsubst T S S₂ 0 k (by omega)
        simpa using this.symm
      rw [this] at h'
      exact h'
  | @pack Δ U T₂ t _ ih =>
      intro k S
      apply HasType.pack
      have := ih k S
      have heq : tsubst k S (tsubst 0 U T₂) =
          tsubst 0 (tsubst k S U) (tsubst (k + 1) S T₂) := by
        have := tsubst_tsubst T₂ S U 0 k (by omega)
        simpa using this
      rw [heq] at this
      exact this
  | @unpack Δ T₁₂ T₂ t₁ t₂ _ _ ih₁ ih₂ =>
      intro k S
      apply HasType.unpack (ih₁ k S)
      have hih := ih₂ (k + 1) S
      simp only [List.map] at hih
      rw [List.map_map] at hih
      have hmap : Δ.map (tsubst (k + 1) S ∘ tshift 1 0) =
          Δ.map (tshift 1 0 ∘ tsubst k S) :=
        map_ext _ _
          (fun X => by
            simp only [Function.comp]
            exact tsubst_tshift_dist X S 1 0 (k + 1) (by omega)) Δ
      rw [hmap] at hih
      have hty : tsubst (k + 1) S (tshift 1 0 T₂) =
          tshift 1 0 (tsubst k S T₂) :=
        tsubst_tshift_dist T₂ S 1 0 (k + 1) (by omega)
      rw [hty] at hih
      rw [List.map_map]
      exact hih

/-! ## Preservation and progress -/

/-- **Preservation**. In the `E-UnpackPack` case the type-substitution
lemma eliminates the abstract type, the context collapses, and the
term-substitution lemma installs the packed value. -/
theorem preservation {Γ : Ctx} {t : Term} {T : Ty} (h : Γ ⊢ t ∶ T) :
    ∀ t', (t ⟶ t') → Γ ⊢ t' ∶ T := by
  induction h with
  | var _ => intro t' hs; cases hs
  | abs _ => intro t' hs; cases hs
  | app h₁ h₂ ih₁ ih₂ =>
      intro t' hs
      cases hs with
      | appAbs hv =>
          cases h₁ with
          | abs hbody => exact substitution hbody _ 0 _ _ rfl h₂
      | app1 hstep => exact .app (ih₁ _ hstep) h₂
      | app2 _ hstep => exact .app h₁ (ih₂ _ hstep)
  | tabs _ _ => intro t' hs; cases hs
  | @tapp Γ t T S h ih =>
      intro t' hs
      cases hs with
      | tappTabs =>
          cases h with
          | tabs hbody =>
              have := tsubstitution hbody 0 S
              rw [map_tsubst_tshift_cancel] at this
              exact this
      | tappCong hstep => exact .tapp (ih _ hstep)
  | pack _ ih =>
      intro t' hs
      cases hs with
      | packCong hstep => exact .pack (ih _ hstep)
  | @unpack Γ T₁₂ T₂ t₁ t₂ h₁ hbody ih₁ _ =>
      intro t' hs
      cases hs with
      | @unpackPack U _ v _ hv =>
          cases h₁ with
          | pack hv' =>
              have hb := tsubstitution hbody 0 U
              simp only [List.map] at hb
              rw [map_tsubst_tshift_cancel, tsubst_tshift_cancel0] at hb
              exact substitution hb Γ 0 _ v rfl hv'
      | unpackCong hstep => exact .unpack (ih₁ _ hstep) hbody

/-- Canonical forms at arrow, universal, and existential type. -/
theorem canonical_arrow {v : Term} {T₁ T₂ : Ty} (hv : Value v)
    (h : [] ⊢ v ∶ T₁ ⇒ T₂) : ∃ S body, v = abs S body := by
  cases hv with
  | abs T t => exact ⟨_, _, rfl⟩
  | tabs t => cases h
  | pack _ _ _ => cases h

theorem canonical_all {v : Term} {T : Ty} (hv : Value v)
    (h : [] ⊢ v ∶ .all T) : ∃ body, v = tabs body := by
  cases hv with
  | abs T t => cases h
  | tabs t => exact ⟨_, rfl⟩
  | pack _ _ _ => cases h

theorem canonical_exi {v : Term} {T : Ty} (hv : Value v)
    (h : [] ⊢ v ∶ .exi T) :
    ∃ U v', v = pack U v' (.exi T) ∧ Value v' := by
  cases hv with
  | abs T t => cases h
  | tabs t => cases h
  | pack U T' hv' =>
      cases h with
      | pack _ => exact ⟨_, _, rfl, hv'⟩

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
        · obtain ⟨S, body, rfl⟩ := canonical_arrow hv₁ h₁
          exact .inr ⟨_, .appAbs hv₂⟩
        · exact .inr ⟨_, .app2 hv₁ hs⟩
      · exact .inr ⟨_, .app1 hs⟩
  | tabs _ _ => intro _; exact .inl (.tabs _)
  | tapp h ih =>
      intro heq
      subst heq
      rcases ih rfl with hv | ⟨t', hs⟩
      · obtain ⟨body, rfl⟩ := canonical_all hv h
        exact .inr ⟨_, .tappTabs⟩
      · exact .inr ⟨_, .tappCong hs⟩
  | pack _ ih =>
      intro heq
      subst heq
      rcases ih rfl with hv | ⟨t', hs⟩
      · exact .inl (.pack _ _ hv)
      · exact .inr ⟨_, .packCong hs⟩
  | unpack h₁ _ ih₁ _ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv | ⟨t₁', hs⟩
      · obtain ⟨U, v', rfl, hv'⟩ := canonical_exi hv h₁
        exact .inr ⟨_, .unpackPack hv'⟩
      · exact .inr ⟨_, .unpackCong hs⟩

/-- **Progress**. -/
theorem progress {t : Term} {T : Ty} (h : [] ⊢ t ∶ T) :
    Value t ∨ ∃ t', t ⟶ t' :=
  progress' h rfl

/-! ## Examples (TAPL §24.1–24.2)

The pure calculus has no records or numbers, so TAPL's counter-ADT
example cannot be transliterated directly; the examples below show the
same mechanisms — hiding a witness type, using the abstract name inside
the body, and the package being opaque from outside. -/

/-- `IdTy = ∀X. X → X` and the polymorphic identity, from chapter 23. -/
def IdTy : Ty := .all (.var 0 ⇒ .var 0)
def idF : Term := tabs (abs (.var 0) (var 0))

/-- A package hiding the witness type `IdTy` behind the interface
`{∃Y, Y}`: `p = {*IdTy, id} as {∃Y, Y}`. -/
def p : Term := pack IdTy idF (.exi (.var 0))

theorem p_type : [] ⊢ p ∶ .exi (.var 0) := by
  apply HasType.pack
  show HasType [] idF (tsubst 0 IdTy (.var 0))
  have : tsubst 0 IdTy (Ty.var 0) = IdTy := by decide
  rw [this]
  exact .tabs (.abs (.var rfl))

/-- Clients cannot see through the abstraction, but they can *repack*:
`let {Y, x} = p in ({*Y, x} as {∃Y, Y})` has the same existential type … -/
def repack : Term := unpack p (pack (.var 0) (var 0) (.exi (.var 0)))

theorem repack_type : [] ⊢ repack ∶ .exi (.var 0) := by
  apply HasType.unpack p_type
  show HasType [Ty.var 0] (pack (.var 0) (var 0) (.exi (.var 0)))
      (tshift 1 0 (.exi (.var 0)))
  have : tshift 1 0 (Ty.exi (.var 0)) = Ty.exi (.var 0) := by decide
  rw [this]
  apply HasType.pack
  show HasType [Ty.var 0] (var 0) (tsubst 0 (.var 0) (.var 0))
  have : tsubst 0 (Ty.var 0) (Ty.var 0) = Ty.var 0 := by decide
  rw [this]
  exact .var rfl

/-- … and evaluates back to the original package. -/
theorem repack_evals : repack ⟶* p := by
  apply MultiStep.head (.unpackPack (.tabs _))
  show MultiStep (subst 0 idF (tsubstT 0 IdTy
      (pack (.var 0) (var 0) (.exi (.var 0))))) p
  have : subst 0 idF (tsubstT 0 IdTy
      (pack (.var 0) (var 0) (.exi (.var 0)))) = p := by decide
  rw [this]
  exact .refl _

end Chapter24
