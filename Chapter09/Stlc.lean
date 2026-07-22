/-!
# Chapter 9: Simply Typed Lambda-Calculus

The simply typed lambda-calculus λ→ over the base type `Bool`
(TAPL figure 9-1): function types, typing contexts, the typing relation,
and its metatheory — weakening, the substitution lemma, preservation,
progress, and uniqueness of types.

The chapter is self-contained (it does not import the untyped calculus of
chapters 5–7) because the syntax changes: abstractions are now annotated,
`λx:T. t`, and the boolean constants and conditional are included.
-/

namespace Chapter09

/-- Types: `Bool` and function types (TAPL fig. 9-1 plus 8-1). -/
inductive Ty : Type where
  | bool
  | arrow (T₁ T₂ : Ty)
  deriving Repr, DecidableEq

/-- `T₁ ⇒ T₂` is the type of functions from `T₁` to `T₂`. -/
scoped infixr:60 " ⇒ " => Ty.arrow

/-- Terms of λ→ with booleans, in de Bruijn representation. The
abstraction carries its domain type: `abs T t` is `λx:T. t`. -/
inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | tru
  | fls
  | ite (t₁ t₂ t₃ : Term)
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

/-- Beta-substitution `[k ↦ s] t` (substitute and decrement, as in
chapter 5). -/
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

/-- Shifting by zero is the identity. -/
theorem shift_zero : ∀ (t : Term) (c : Nat), shift 0 c t = t := by
  intro t
  induction t with
  | var n => intro c; by_cases h : n < c <;> simp [shift, h]
  | abs T t ih => intro c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ => intro c; simp [shift, ih₁, ih₂]
  | tru => intro c; rfl
  | fls => intro c; rfl
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
  | abs T t ih => intro k c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ => intro k c; simp [shift, ih₁, ih₂]
  | tru => intro k c; rfl
  | fls => intro k c; rfl
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ => intro k c; simp [shift, ih₁, ih₂, ih₃]

end Term

open Term

/-- Values: abstractions and the boolean constants (TAPL fig. 9-1). -/
inductive Value : Term → Prop where
  | abs (T : Ty) (t : Term) : Value (abs T t)
  | tru : Value tru
  | fls : Value fls

/-- Call-by-value single-step evaluation (TAPL fig. 9-1 plus the boolean
rules of fig. 8-1). -/
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

@[inherit_doc] scoped infix:50 " ⟶ " => Step

/-- Multi-step evaluation. -/
inductive MultiStep : Term → Term → Prop where
  | refl (t : Term) : MultiStep t t
  | head {t t' t'' : Term} : Step t t' → MultiStep t' t'' → MultiStep t t''

@[inherit_doc] scoped infix:50 " ⟶* " => MultiStep

/-! ## Typing -/

/-- A typing context is a list of types; de Bruijn variable `n` is looked
up at position `n`, so the head of the list is the innermost binding. -/
abbrev Ctx := List Ty

/-- The typing relation `Γ ⊢ t ∶ T` (TAPL fig. 9-1). -/
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

@[inherit_doc] scoped notation:40 Γ " ⊢ " t " ∶ " T => HasType Γ t T

/-- **Theorem 9.3.3 (Uniqueness of types)**. -/
theorem HasType.unique {Γ : Ctx} {t : Term} {T₁ T₂ : Ty}
    (h₁ : Γ ⊢ t ∶ T₁) (h₂ : Γ ⊢ t ∶ T₂) : T₁ = T₂ := by
  induction h₁ generalizing T₂ with
  | var hget => cases h₂ with
    | var hget' => rw [hget] at hget'; cases hget'; rfl
  | abs _ ih => cases h₂ with
    | abs h' => rw [ih h']
  | app _ _ ih₁ _ => cases h₂ with
    | app h₁' h₂' => cases ih₁ h₁'; rfl
  | tru => cases h₂; rfl
  | fls => cases h₂; rfl
  | ite _ _ _ _ ih₂ _ => cases h₂ with
    | ite _ h₂' _ => exact ih₂ h₂'

/-! ## Context manipulation: insertion and its lookup laws -/

/-- Insert type `S` at position `c` of the context (identity if `c` is past
the end). This is the context operation matching a `shift 1 c`. -/
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

/-- **Weakening (shift-typing)**: inserting a binding at position `c` of
the context leaves the term well typed after shifting its variables at
cutoff `c`. -/
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
  | abs _ ih =>
      intro c S
      exact .abs (ih (c + 1) S)
  | app _ _ ih₁ ih₂ =>
      intro c S
      exact .app (ih₁ c S) (ih₂ c S)
  | tru => intro c S; exact .tru
  | fls => intro c S; exact .fls
  | ite _ _ _ ih₁ ih₂ ih₃ =>
      intro c S
      exact .ite (ih₁ c S) (ih₂ c S) (ih₃ c S)

/-- Iterated weakening at the bottom of the context: a term typed in
`Γ.drop k` can be shifted by `k` to live in `Γ`. -/
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

/-- **The substitution lemma (TAPL lemma 9.3.8)**: substituting a term of
type `S` for a variable of type `S` preserves typing. Stated for a
variable at arbitrary depth `k`; preservation uses `k = 0`. -/
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
      | abs ht' =>
          exact .abs (ih (B :: Γ) (k + 1) S _ s ht' hs)
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

/-! ## Preservation and progress -/

/-- **Theorem 9.3.9 (Preservation)**: types are preserved by evaluation. -/
theorem preservation {Γ : Ctx} {t t' : Term} {T : Ty} (hs : t ⟶ t') :
    (Γ ⊢ t ∶ T) → Γ ⊢ t' ∶ T := by
  induction hs generalizing T with
  | appAbs _ =>
      intro h
      cases h with
      | app h₁ h₂ =>
          cases h₁ with
          | abs hbody => exact substitution _ Γ 0 _ T _ hbody h₂
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

/-- **Theorem 9.3.5 (Progress)**: a closed well-typed term is a value or
can take a step. (Auxiliary version with a context equation, so that the
induction goes through.) -/
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
          | tru => cases h₁
          | fls => cases h₁
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
      · exact .inr ⟨_, .ifCong hs⟩

/-- **Theorem 9.3.5 (Progress)**. -/
theorem progress {t : Term} {T : Ty} (h : [] ⊢ t ∶ T) :
    Value t ∨ ∃ t', t ⟶ t' :=
  progress' h rfl

/-! ## Type safety -/

/-- A term is a normal form if it cannot step. -/
def NormalForm (t : Term) : Prop := ¬ ∃ t', t ⟶ t'

/-- Types are preserved along multi-step evaluation. -/
theorem preservation_multi {t t' : Term} {T : Ty} (h : [] ⊢ t ∶ T)
    (hs : t ⟶* t') : [] ⊢ t' ∶ T := by
  induction hs with
  | refl _ => exact h
  | head s _ ih => exact ih (preservation s h)

/-- **Type safety**: a closed well-typed term never gets stuck — every
normal form it reaches is a value. -/
theorem safety {t t' : Term} {T : Ty} (h : [] ⊢ t ∶ T) (hs : t ⟶* t')
    (hn : NormalForm t') : Value t' := by
  rcases progress (preservation_multi h hs) with hv | hstep
  · exact hv
  · exact absurd hstep hn

/-! ## Examples -/

/-- Boolean negation, `λb:Bool. if b then false else true`. -/
def notTerm : Term := abs .bool (ite (var 0) fls tru)

/-- `⊢ not ∶ Bool → Bool` -/
example : [] ⊢ notTerm ∶ .bool ⇒ .bool :=
  .abs (.ite (.var rfl) .fls .tru)

/-- `not true` evaluates to `false`. -/
example : app notTerm tru ⟶* fls :=
  .head (.appAbs .tru) (.head .ifTrue (.refl _))

/-- Function composition on `Bool`:
`λf:Bool→Bool. λg:Bool→Bool. λx:Bool. g (f x)`. -/
def composeTerm : Term :=
  abs (.bool ⇒ .bool) (abs (.bool ⇒ .bool) (abs .bool
    (app (var 1) (app (var 2) (var 0)))))

example : [] ⊢ composeTerm ∶
    (.bool ⇒ .bool) ⇒ (.bool ⇒ .bool) ⇒ .bool ⇒ .bool :=
  .abs (.abs (.abs (.app (.var rfl) (.app (.var rfl) (.var rfl)))))

/-- Self-application `λx:Bool. x x` is not typable — in λ→ no term may be
applied to itself, whatever annotation we pick. -/
example (T : Ty) : ¬ ([] ⊢ abs .bool (app (var 0) (var 0)) ∶ T) := by
  intro h
  cases h with
  | abs h =>
      cases h with
      | app h₁ h₂ =>
          cases h₁ with
          | var hget => cases hget

/-- No type is its own domain: `T ⇒ U ≠ T` (structural induction). -/
theorem arrow_ne : ∀ (T U : Ty), T ⇒ U ≠ T := by
  intro T
  induction T with
  | bool => intro U h; cases h
  | arrow T₁ T₂ ih₁ _ =>
      intro U h
      injection h with h₁ _
      exact ih₁ T₂ h₁

/-- The untyped `omega` has no counterpart in λ→: `λx:T. x x` is untypable
for every annotation `T`, because both lookups hit the same context slot,
forcing `T = T ⇒ T₂`. -/
theorem no_self_app (T R : Ty) :
    ¬ ([] ⊢ abs T (app (var 0) (var 0)) ∶ R) := by
  intro h
  cases h with
  | abs h =>
      cases h with
      | app h₁ h₂ =>
          cases h₁ with
          | var hget₁ =>
              cases h₂ with
              | var hget₂ =>
                  simp [List.get?] at hget₁ hget₂
                  subst hget₂
                  exact arrow_ne T _ hget₁.symm

end Chapter09
