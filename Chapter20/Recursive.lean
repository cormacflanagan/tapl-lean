/-!
# Chapter 20: Recursive Types

Iso-recursive types: μ-types together with the explicit coercions
`fold [μX.T]` and `unfold [μX.T]` between a recursive type and its one-step
unfolding (TAPL figure 20-1). Types now contain a binder (`μ`), so they get
their own de Bruijn indices and substitution.

The payoff example is TAPL §20.1's: with `D = μX. X → X` the untyped
lambda-calculus embeds into the typed language, and a **well-typed divergent
term** exists — recursive types trade away strong normalization.
-/

namespace Chapter20

/-- Types: type variables (de Bruijn), `Bool`, arrows, and recursive types
`μX.T` (`mu T` binds type-variable 0 of `T`). -/
inductive Ty : Type where
  | var (n : Nat)
  | bool
  | arrow (T₁ T₂ : Ty)
  | mu (T : Ty)
  deriving Repr, DecidableEq

/-- `T₁ ⇒ T₂` is the function type. -/
scoped infixr:60 " ⇒ " => Ty.arrow

namespace Ty

/-- Shift type variables `≥ c` up by `d`. -/
def tshift (d c : Nat) : Ty → Ty
  | var n => if n < c then var n else var (n + d)
  | bool => bool
  | arrow T₁ T₂ => arrow (tshift d c T₁) (tshift d c T₂)
  | mu T => mu (tshift d (c + 1) T)

/-- Type-level substitution `[k ↦ S] T` (substitute and decrement). -/
def tsubst (k : Nat) (S : Ty) : Ty → Ty
  | var n =>
      if n < k then var n
      else if n = k then tshift k 0 S
      else var (n - 1)
  | bool => bool
  | arrow T₁ T₂ => arrow (tsubst k S T₁) (tsubst k S T₂)
  | mu T => mu (tsubst (k + 1) S T)

/-- One-step unfolding of `μX.T`: substitute the whole recursive type for
`X` in the body, `[X ↦ μX.T] T`. -/
def unfoldMu (T : Ty) : Ty := tsubst 0 (mu T) T

end Ty

/-- Terms: λ→ with booleans plus the two coercions. The `Ty` argument of
`fold`/`unfold` is the μ-type annotation, as in `fold [μX.T] t`. -/
inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | tru
  | fls
  | ite (t₁ t₂ t₃ : Term)
  | fold (T : Ty) (t : Term)
  | unfold (T : Ty) (t : Term)
  deriving Repr, DecidableEq

namespace Term

/-- Shift the (term) variables of `t` that are `≥ c` up by `d`. -/
def shift (d c : Nat) : Term → Term
  | var n => if n < c then var n else var (n + d)
  | abs T t => abs T (shift d (c + 1) t)
  | app t₁ t₂ => app (shift d c t₁) (shift d c t₂)
  | tru => tru
  | fls => fls
  | ite t₁ t₂ t₃ => ite (shift d c t₁) (shift d c t₂) (shift d c t₃)
  | fold T t => fold T (shift d c t)
  | unfold T t => unfold T (shift d c t)

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
  | fold T t => fold T (subst k s t)
  | unfold T t => unfold T (subst k s t)

/-- Shifting by zero is the identity. -/
theorem shift_zero : ∀ (t : Term) (c : Nat), shift 0 c t = t := by
  intro t
  induction t with
  | var n => intro c; by_cases h : n < c <;> simp [shift, h]
  | tru | fls => intro c; rfl
  | abs T t ih | fold T t ih | unfold T t ih => intro c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ => intro c; simp [shift, ih₁, ih₂]
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
  | abs T t ih | fold T t ih | unfold T t ih => intro k c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ => intro k c; simp [shift, ih₁, ih₂]
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ => intro k c; simp [shift, ih₁, ih₂, ih₃]

end Term

open Term

/-- Values: a `fold` of a value is a value (a folded package awaiting an
`unfold`). -/
inductive Value : Term → Prop where
  | abs (T : Ty) (t : Term) : Value (abs T t)
  | tru : Value tru
  | fls : Value fls
  | fold {v : Term} (T : Ty) : Value v → Value (fold T v)

/-- Call-by-value single-step evaluation (TAPL figure 20-1). -/
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
  | unfoldFold {S T : Ty} {v : Term} :                       -- E-UnfldFld
      Value v → Step (unfold S (fold T v)) v
  | foldCong {T : Ty} {t t' : Term} :                        -- E-Fld
      Step t t' → Step (fold T t) (fold T t')
  | unfoldCong {T : Ty} {t t' : Term} :                      -- E-Unfld
      Step t t' → Step (unfold T t) (unfold T t')

@[inherit_doc] scoped infix:50 " ⟶ " => Step

/-- Multi-step evaluation. -/
inductive MultiStep : Term → Term → Prop where
  | refl (t : Term) : MultiStep t t
  | head {t t' t'' : Term} : Step t t' → MultiStep t' t'' → MultiStep t t''

@[inherit_doc] scoped infix:50 " ⟶* " => MultiStep

/-! ## Typing -/

/-- Typing contexts. -/
abbrev Ctx := List Ty

/-- The typing relation, with the iso-recursive rules `T-Fld`/`T-Unfld`. -/
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
  | fold {Γ : Ctx} {T : Ty} {t : Term} :                     -- T-Fld
      HasType Γ t (Ty.unfoldMu T) →
      HasType Γ (fold (Ty.mu T) t) (Ty.mu T)
  | unfold {Γ : Ctx} {T : Ty} {t : Term} :                   -- T-Unfld
      HasType Γ t (Ty.mu T) →
      HasType Γ (unfold (Ty.mu T) t) (Ty.unfoldMu T)

@[inherit_doc] scoped notation:40 Γ " ⊢ " t " ∶ " T => HasType Γ t T

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
  | tru => intro c S; exact .tru
  | fls => intro c S; exact .fls
  | ite _ _ _ ih₁ ih₂ ih₃ =>
      intro c S; exact .ite (ih₁ c S) (ih₂ c S) (ih₃ c S)
  | fold _ ih => intro c S; exact .fold (ih c S)
  | unfold _ ih => intro c S; exact .unfold (ih c S)

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
  | tru => intro Γ k S s _ _; exact .tru
  | fls => intro Γ k S s _ _; exact .fls
  | ite _ _ _ ih₁ ih₂ ih₃ =>
      intro Γ k S s heq hs
      exact .ite (ih₁ Γ k S s heq hs) (ih₂ Γ k S s heq hs)
        (ih₃ Γ k S s heq hs)
  | fold _ ih =>
      intro Γ k S s heq hs
      exact .fold (ih Γ k S s heq hs)
  | unfold _ ih =>
      intro Γ k S s heq hs
      exact .unfold (ih Γ k S s heq hs)

/-! ## Preservation and progress -/

/-- **Preservation**. The `E-UnfldFld` case is where fold and unfold
annotations meet: typing forces them to agree. -/
theorem preservation {Γ : Ctx} {t : Term} {T : Ty} (h : Γ ⊢ t ∶ T) :
    ∀ t', (t ⟶ t') → Γ ⊢ t' ∶ T := by
  induction h with
  | var _ => intro t' hs; cases hs
  | abs _ => intro t' hs; cases hs
  | tru => intro t' hs; cases hs
  | fls => intro t' hs; cases hs
  | app h₁ h₂ ih₁ ih₂ =>
      intro t' hs
      cases hs with
      | appAbs hv =>
          cases h₁ with
          | abs hbody => exact substitution hbody _ 0 _ _ rfl h₂
      | app1 hstep => exact .app (ih₁ _ hstep) h₂
      | app2 _ hstep => exact .app h₁ (ih₂ _ hstep)
  | ite h₁ h₂ h₃ ih₁ _ _ =>
      intro t' hs
      cases hs with
      | ifTrue => exact h₂
      | ifFalse => exact h₃
      | ifCong hstep => exact .ite (ih₁ _ hstep) h₂ h₃
  | fold _ ih =>
      intro t' hs
      cases hs with
      | foldCong hstep => exact .fold (ih _ hstep)
  | unfold h ih =>
      intro t' hs
      cases hs with
      | unfoldFold hv =>
          cases h with
          | fold hv' => exact hv'
      | unfoldCong hstep => exact .unfold (ih _ hstep)

/-- Canonical forms at a recursive type: a closed value of type `μX.T` is
a `fold`ed value with matching annotation. -/
theorem canonical_mu {v : Term} {T : Ty} (hv : Value v)
    (h : [] ⊢ v ∶ .mu T) :
    ∃ v', v = fold (.mu T) v' ∧ Value v' := by
  cases hv with
  | abs T t => cases h
  | tru => cases h
  | fls => cases h
  | fold _ hv' =>
      cases h with
      | fold _ => exact ⟨_, rfl, hv'⟩

/-- Canonical forms at arrow type. -/
theorem canonical_arrow {v : Term} {T₁ T₂ : Ty} (hv : Value v)
    (h : [] ⊢ v ∶ T₁ ⇒ T₂) : ∃ S body, v = abs S body := by
  cases hv with
  | abs T t => exact ⟨_, _, rfl⟩
  | tru => cases h
  | fls => cases h
  | fold _ _ => cases h

/-- Canonical forms at `Bool`. -/
theorem canonical_bool {v : Term} (hv : Value v)
    (h : [] ⊢ v ∶ .bool) : v = tru ∨ v = fls := by
  cases hv with
  | abs T t => cases h
  | tru => exact .inl rfl
  | fls => exact .inr rfl
  | fold _ _ => cases h

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
  | tru => intro _; exact .inl .tru
  | fls => intro _; exact .inl .fls
  | ite h₁ _ _ ih₁ _ _ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv₁ | ⟨t₁', hs⟩
      · rcases canonical_bool hv₁ h₁ with rfl | rfl
        · exact .inr ⟨_, .ifTrue⟩
        · exact .inr ⟨_, .ifFalse⟩
      · exact .inr ⟨_, .ifCong hs⟩
  | fold _ ih =>
      intro heq
      subst heq
      rcases ih rfl with hv | ⟨t', hs⟩
      · exact .inl (.fold _ hv)
      · exact .inr ⟨_, .foldCong hs⟩
  | unfold h ih =>
      intro heq
      subst heq
      rcases ih rfl with hv | ⟨t', hs⟩
      · obtain ⟨v', rfl, hv'⟩ := canonical_mu hv h
        exact .inr ⟨_, .unfoldFold hv'⟩
      · exact .inr ⟨_, .unfoldCong hs⟩

/-- **Progress**. -/
theorem progress {t : Term} {T : Ty} (h : [] ⊢ t ∶ T) :
    Value t ∨ ∃ t', t ⟶ t' :=
  progress' h rfl

/-! ## Example: well-typed divergence (TAPL §20.1)

With `D = μX. X → X`, `unfold [D]` turns a `D` into a `D → D`, so a term
of type `D` can be applied to itself. The whole untyped lambda-calculus
embeds this way — and in particular `Ω` becomes well typed. -/

/-- `D = μX. X → X`. -/
def D : Ty := .mu (.arrow (.var 0) (.var 0))

/-- `unfold [μX.X→X] (X → X) = D ⇒ D`. -/
example : Ty.unfoldMu (.arrow (.var 0) (.var 0)) = (D ⇒ D) := by decide

/-- `selfApp = λx:D. (unfold [D] x) x ∶ D ⇒ D`. -/
def selfApp : Term := abs D (app (unfold D (var 0)) (var 0))

example : [] ⊢ selfApp ∶ (D ⇒ D) :=
  .abs (.app (.unfold (.var rfl)) (.var rfl))

/-- The well-typed `Ω`: `selfApp (fold [D] selfApp)` has a type! -/
def omegaTyped : Term := app selfApp (fold D selfApp)

theorem omegaTyped_wellTyped : [] ⊢ omegaTyped ∶ D :=
  .app (.abs (.app (.unfold (.var rfl)) (.var rfl)))
    (.fold (.abs (.app (.unfold (.var rfl)) (.var rfl))))

/-- ... and it diverges: `Ω` steps back to itself in two steps, so a
well-typed term can run forever. (Progress + preservation still hold —
safety means "never stuck", not "always terminating".) -/
theorem omegaTyped_loops : omegaTyped ⟶ app (unfold D (fold D selfApp)) (fold D selfApp) ∧
    app (unfold D (fold D selfApp)) (fold D selfApp) ⟶ omegaTyped := by
  constructor
  · exact .appAbs (.fold _ (.abs _ _))
  · exact .app1 (.unfoldFold (.abs _ _))

end Chapter20
