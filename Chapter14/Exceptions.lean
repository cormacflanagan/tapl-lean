/-!
# Chapter 14: Exceptions

λ→ with booleans, extended with runtime errors and their handlers
(TAPL figures 14-1 and 14-2): a constant `error` that aborts the
computation by propagating through every evaluation context, and
`try t₁ with t₂`, which runs `t₂` if `t₁` aborts.

Two notable wrinkles compared to earlier chapters:
* `error` has **every** type (`T-Error`), so uniqueness of types is lost —
  deliberately, so that an error can occur in any position;
* the progress theorem changes shape: a closed well-typed term is a value,
  is `error`, or steps.

TAPL §14.3's exceptions *carrying values* (`raise t`) add an exception
payload type but no new proof ideas; see the README.
-/

namespace Chapter14

/-- Types: `Bool` and functions, as in chapter 9. -/
inductive Ty : Type where
  | bool
  | arrow (T₁ T₂ : Ty)
  deriving Repr, DecidableEq

/-- `T₁ ⇒ T₂` is the function type. -/
scoped infixr:60 " ⇒ " => Ty.arrow

/-- Terms: chapter 9's λ→ plus `error` and `tryE t₁ t₂` (= `try t₁ with
t₂`; no binder — `t₂` is the alternative computation). -/
inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | tru
  | fls
  | ite (t₁ t₂ t₃ : Term)
  | error
  | tryE (t₁ t₂ : Term)
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
  | error => error
  | tryE t₁ t₂ => tryE (shift d c t₁) (shift d c t₂)

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
  | error => error
  | tryE t₁ t₂ => tryE (subst k s t₁) (subst k s t₂)

/-- Shifting by zero is the identity. -/
theorem shift_zero : ∀ (t : Term) (c : Nat), shift 0 c t = t := by
  intro t
  induction t with
  | var n => intro c; by_cases h : n < c <;> simp [shift, h]
  | tru | fls | error => intro c; rfl
  | abs T t ih => intro c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ | tryE t₁ t₂ ih₁ ih₂ => intro c; simp [shift, ih₁, ih₂]
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
  | tru | fls | error => intro k c; rfl
  | abs T t ih => intro k c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ | tryE t₁ t₂ ih₁ ih₂ => intro k c; simp [shift, ih₁, ih₂]
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ => intro k c; simp [shift, ih₁, ih₂, ih₃]

end Term

open Term

/-- Values: `error` is *not* a value — it is an aborted computation. -/
inductive Value : Term → Prop where
  | abs (T : Ty) (t : Term) : Value (abs T t)
  | tru : Value tru
  | fls : Value fls

/-- Call-by-value single-step evaluation with error propagation and
handling (TAPL figures 14-1 and 14-2). -/
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
  | appErr1 {t₂ : Term} : Step (app error t₂) error       -- E-AppErr1
  | appErr2 {v : Term} : Value v → Step (app v error) error -- E-AppErr2
  | ifErr {t₂ t₃ : Term} : Step (ite error t₂ t₃) error   -- error in guard
  | tryV {v t₂ : Term} : Value v → Step (tryE v t₂) v     -- E-TryV
  | tryErr {t₂ : Term} : Step (tryE error t₂) t₂          -- E-TryError
  | tryCong {t₁ t₁' t₂ : Term} :
      Step t₁ t₁' → Step (tryE t₁ t₂) (tryE t₁' t₂)       -- E-Try

@[inherit_doc] scoped infix:50 " ⟶ " => Step

/-- Multi-step evaluation. -/
inductive MultiStep : Term → Term → Prop where
  | refl (t : Term) : MultiStep t t
  | head {t t' t'' : Term} : Step t t' → MultiStep t' t'' → MultiStep t t''

@[inherit_doc] scoped infix:50 " ⟶* " => MultiStep

/-! ## Typing -/

/-- Typing contexts. -/
abbrev Ctx := List Ty

/-- The typing relation. `T-Error` gives `error` *any* type — the price is
uniqueness of types, the gain is that errors can occur anywhere. -/
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
  | error {Γ : Ctx} {T : Ty} : HasType Γ error T           -- T-Error
  | tryE {Γ : Ctx} {t₁ t₂ : Term} {T : Ty} :               -- T-Try
      HasType Γ t₁ T → HasType Γ t₂ T →
      HasType Γ (tryE t₁ t₂) T

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
  | error => intro c S; exact .error
  | tryE _ _ ih₁ ih₂ => intro c S; exact .tryE (ih₁ c S) (ih₂ c S)

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
  | error => intro Γ k S s _ _; exact .error
  | tryE _ _ ih₁ ih₂ =>
      intro Γ k S s heq hs
      exact .tryE (ih₁ Γ k S s heq hs) (ih₂ Γ k S s heq hs)

/-! ## Preservation and progress -/

/-- **Preservation**: the error rules produce `error`, which has every
type; `E-TryV`/`E-TryError` return one of the two equi-typed branches. -/
theorem preservation {Γ : Ctx} {t : Term} {T : Ty} (h : Γ ⊢ t ∶ T) :
    ∀ t', (t ⟶ t') → Γ ⊢ t' ∶ T := by
  induction h with
  | var _ => intro t' hs; cases hs
  | abs _ => intro t' hs; cases hs
  | tru => intro t' hs; cases hs
  | fls => intro t' hs; cases hs
  | error => intro t' hs; cases hs
  | app h₁ h₂ ih₁ ih₂ =>
      intro t' hs
      cases hs with
      | appAbs hv =>
          cases h₁ with
          | abs hbody => exact substitution hbody _ 0 _ _ rfl h₂
      | app1 hstep => exact .app (ih₁ _ hstep) h₂
      | app2 _ hstep => exact .app h₁ (ih₂ _ hstep)
      | appErr1 => exact .error
      | appErr2 _ => exact .error
  | ite h₁ h₂ h₃ ih₁ _ _ =>
      intro t' hs
      cases hs with
      | ifTrue => exact h₂
      | ifFalse => exact h₃
      | ifCong hstep => exact .ite (ih₁ _ hstep) h₂ h₃
      | ifErr => exact .error
  | tryE h₁ h₂ ih₁ _ =>
      intro t' hs
      cases hs with
      | tryV _ => exact h₁
      | tryErr => exact h₂
      | tryCong hstep => exact .tryE (ih₁ _ hstep) h₂

/-- Canonical forms at arrow type (`error` is not a value, so the lemma
survives `T-Error`). -/
theorem canonical_arrow {v : Term} {T₁ T₂ : Ty} (hv : Value v)
    (h : [] ⊢ v ∶ T₁ ⇒ T₂) : ∃ S body, v = abs S body := by
  cases hv with
  | abs T t => exact ⟨_, _, rfl⟩
  | tru => cases h
  | fls => cases h

/-- Canonical forms at `Bool`. -/
theorem canonical_bool {v : Term} (hv : Value v)
    (h : [] ⊢ v ∶ .bool) : v = tru ∨ v = fls := by
  cases hv with
  | abs T t => cases h
  | tru => exact .inl rfl
  | fls => exact .inr rfl

/-- Progress, auxiliary version with a context equation. -/
theorem progress' {Γ : Ctx} {t : Term} {T : Ty} (h : Γ ⊢ t ∶ T) :
    Γ = [] → Value t ∨ t = error ∨ ∃ t', t ⟶ t' := by
  induction h with
  | @var Γ n T hget =>
      intro heq
      subst heq
      simp [List.get?] at hget
  | abs _ _ => intro _; exact .inl (.abs _ _)
  | tru => intro _; exact .inl .tru
  | fls => intro _; exact .inl .fls
  | error => intro _; exact .inr (.inl rfl)
  | app h₁ _ ih₁ ih₂ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv₁ | rfl | ⟨t₁', hs⟩
      · rcases ih₂ rfl with hv₂ | rfl | ⟨t₂', hs⟩
        · obtain ⟨S, body, rfl⟩ := canonical_arrow hv₁ h₁
          exact .inr (.inr ⟨_, .appAbs hv₂⟩)
        · exact .inr (.inr ⟨_, .appErr2 hv₁⟩)
        · exact .inr (.inr ⟨_, .app2 hv₁ hs⟩)
      · exact .inr (.inr ⟨_, .appErr1⟩)
      · exact .inr (.inr ⟨_, .app1 hs⟩)
  | ite h₁ _ _ ih₁ _ _ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv₁ | rfl | ⟨t₁', hs⟩
      · rcases canonical_bool hv₁ h₁ with rfl | rfl
        · exact .inr (.inr ⟨_, .ifTrue⟩)
        · exact .inr (.inr ⟨_, .ifFalse⟩)
      · exact .inr (.inr ⟨_, .ifErr⟩)
      · exact .inr (.inr ⟨_, .ifCong hs⟩)
  | tryE _ _ ih₁ _ =>
      intro heq
      subst heq
      rcases ih₁ rfl with hv₁ | rfl | ⟨t₁', hs⟩
      · exact .inr (.inr ⟨_, .tryV hv₁⟩)
      · exact .inr (.inr ⟨_, .tryErr⟩)
      · exact .inr (.inr ⟨_, .tryCong hs⟩)

/-- **Progress (theorem 14.1.2, extended)**: a closed well-typed term is
a value, is `error`, or can take a step. -/
theorem progress {t : Term} {T : Ty} (h : [] ⊢ t ∶ T) :
    Value t ∨ t = error ∨ ∃ t', t ⟶ t' :=
  progress' h rfl

/-! ## Examples -/

/-- Boolean negation, from chapter 9. -/
def notTerm : Term := abs .bool (ite (var 0) fls tru)

/-- An error in argument position aborts the whole application … -/
example : app notTerm error ⟶* error :=
  .head (.appErr2 (.abs _ _)) (.refl _)

/-- … unless a `try` catches it:
`try (not error) with true ⟶* true`. -/
example : tryE (app notTerm error) tru ⟶* tru :=
  .head (.tryCong (.appErr2 (.abs _ _))) (.head .tryErr (.refl _))

/-- When the body finishes normally, the handler is discarded:
`try (not false) with false ⟶* true`. -/
example : tryE (app notTerm fls) fls ⟶* tru :=
  .head (.tryCong (.appAbs .fls))
    (.head (.tryCong .ifFalse) (.head (.tryV .tru) (.refl _)))

/-- `error` really does have every type. -/
example (T : Ty) : [] ⊢ error ∶ T := .error

/-- So uniqueness of types fails, by design: `error` is both a boolean
and a function. -/
example : ([] ⊢ error ∶ .bool) ∧ ([] ⊢ error ∶ .bool ⇒ .bool) :=
  ⟨.error, .error⟩

end Chapter14
