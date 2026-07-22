/-!
# Chapter 3: Untyped Arithmetic Expressions

The language of booleans and natural numbers from TAPL chapter 3:
syntax, small-step evaluation, and its basic metatheory (determinacy of
evaluation, values vs. normal forms, termination of evaluation).
-/

namespace Chapter03

/-- Terms of the arithmetic language (TAPL figure 3-1 and 3-2). -/
inductive Term : Type where
  | tru                          -- constant true
  | fls                          -- constant false
  | ite (t₁ t₂ t₃ : Term)        -- conditional: if t₁ then t₂ else t₃
  | zero                         -- constant zero
  | succ (t : Term)              -- successor
  | pred (t : Term)              -- predecessor
  | iszero (t : Term)            -- zero test
  deriving Repr, DecidableEq

open Term

/-- Numeric values: `0`, `succ 0`, `succ (succ 0)`, ... (TAPL fig. 3-2). -/
inductive NValue : Term → Prop where
  | zero : NValue zero
  | succ {t : Term} : NValue t → NValue (succ t)

/-- Values — possible final results of evaluation: the booleans and the
numeric values. -/
inductive Value : Term → Prop where
  | tru : Value tru
  | fls : Value fls
  | num {t : Term} : NValue t → Value t

/-- The single-step evaluation relation `t ⟶ t'` (TAPL fig. 3-1, 3-2). -/
inductive Step : Term → Term → Prop where
  | ifTrue {t₂ t₃ : Term} :
      Step (ite tru t₂ t₃) t₂
  | ifFalse {t₂ t₃ : Term} :
      Step (ite fls t₂ t₃) t₃
  | ifCong {t₁ t₁' t₂ t₃ : Term} :
      Step t₁ t₁' → Step (ite t₁ t₂ t₃) (ite t₁' t₂ t₃)
  | succCong {t t' : Term} :
      Step t t' → Step (succ t) (succ t')
  | predZero :
      Step (pred zero) zero
  | predSucc {t : Term} :
      NValue t → Step (pred (succ t)) t
  | predCong {t t' : Term} :
      Step t t' → Step (pred t) (pred t')
  | iszeroZero :
      Step (iszero zero) tru
  | iszeroSucc {t : Term} :
      NValue t → Step (iszero (succ t)) fls
  | iszeroCong {t t' : Term} :
      Step t t' → Step (iszero t) (iszero t')

@[inherit_doc] scoped infix:50 " ⟶ " => Step

/-- Multi-step evaluation: the reflexive–transitive closure of `⟶`. -/
inductive MultiStep : Term → Term → Prop where
  | refl (t : Term) : MultiStep t t
  | head {t t' t'' : Term} : Step t t' → MultiStep t' t'' → MultiStep t t''

@[inherit_doc] scoped infix:50 " ⟶* " => MultiStep

namespace MultiStep

/-- A single step is a multi-step. -/
theorem single {t t' : Term} (h : t ⟶ t') : t ⟶* t' :=
  .head h (.refl t')

/-- Multi-step evaluation is transitive. -/
theorem trans {t t' t'' : Term} (h₁ : t ⟶* t') (h₂ : t' ⟶* t'') : t ⟶* t'' := by
  induction h₁ with
  | refl _ => exact h₂
  | head s _ ih => exact .head s (ih h₂)

end MultiStep

/-- A term is a normal form if no evaluation rule applies to it
(TAPL definition 3.5.6). -/
def NormalForm (t : Term) : Prop := ¬ ∃ t', t ⟶ t'

/-- Numeric values do not step. -/
theorem NValue.not_step {t t' : Term} (hv : NValue t) : ¬ t ⟶ t' := by
  induction hv generalizing t' with
  | zero => intro h; cases h
  | succ _ ih =>
      intro hs
      cases hs with
      | succCong hs' => exact ih hs'

/-- **Theorem 3.5.7**: every value is a normal form. -/
theorem Value.normalForm {t : Term} (hv : Value t) : NormalForm t := by
  intro ⟨t', hstep⟩
  cases hv with
  | tru => cases hstep
  | fls => cases hstep
  | num hn => exact hn.not_step hstep

/-- **Theorem 3.5.4 (Determinacy)**: a term steps to at most one term. -/
theorem Step.deterministic {t t₁ t₂ : Term} (h₁ : t ⟶ t₁) (h₂ : t ⟶ t₂) :
    t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | ifTrue => cases h₂ with
    | ifTrue => rfl
    | ifCong h => cases h
  | ifFalse => cases h₂ with
    | ifFalse => rfl
    | ifCong h => cases h
  | ifCong h ih => cases h₂ with
    | ifTrue => cases h
    | ifFalse => cases h
    | ifCong h' => rw [ih h']
  | succCong _ ih => cases h₂ with
    | succCong h' => rw [ih h']
  | predZero => cases h₂ with
    | predZero => rfl
    | predCong h => cases h
  | predSucc hn => cases h₂ with
    | predSucc _ => rfl
    | predCong h => exact absurd h (NValue.succ hn).not_step
  | predCong h ih => cases h₂ with
    | predZero => cases h
    | predSucc hn => exact absurd h (NValue.succ hn).not_step
    | predCong h' => rw [ih h']
  | iszeroZero => cases h₂ with
    | iszeroZero => rfl
    | iszeroCong h => cases h
  | iszeroSucc hn => cases h₂ with
    | iszeroSucc _ => rfl
    | iszeroCong h => exact absurd h (NValue.succ hn).not_step
  | iszeroCong h ih => cases h₂ with
    | iszeroZero => cases h
    | iszeroSucc hn => exact absurd h (NValue.succ hn).not_step
    | iszeroCong h' => rw [ih h']

/-- **Corollary 3.5.11 (Uniqueness of normal forms)**: if `t` evaluates to
normal forms `u₁` and `u₂`, then `u₁ = u₂`. -/
theorem MultiStep.normalForm_unique {t u₁ u₂ : Term}
    (h₁ : t ⟶* u₁) (n₁ : NormalForm u₁)
    (h₂ : t ⟶* u₂) (n₂ : NormalForm u₂) : u₁ = u₂ := by
  induction h₁ with
  | refl t => cases h₂ with
    | refl => rfl
    | head s _ => exact absurd ⟨_, s⟩ n₁
  | head s _ ih =>
    cases h₂ with
    | refl => exact absurd ⟨_, s⟩ n₂
    | head s' h₂' => exact ih n₁ (s.deterministic s' ▸ h₂')

/-- Size of a term (number of constructors), used as a termination measure. -/
def Term.size : Term → Nat
  | tru | fls | zero => 1
  | ite t₁ t₂ t₃ => t₁.size + t₂.size + t₃.size + 1
  | succ t | pred t | iszero t => t.size + 1

/-- Every evaluation step strictly decreases the size of the term. -/
theorem Step.size_lt {t t' : Term} (h : t ⟶ t') : t'.size < t.size := by
  induction h with
  | ifTrue => simp [Term.size]; omega
  | ifFalse => simp [Term.size]; omega
  | ifCong _ ih => simp [Term.size]; omega
  | succCong _ ih => simp [Term.size]; omega
  | predZero => simp [Term.size]
  | predSucc _ => simp [Term.size]; omega
  | predCong _ ih => simp [Term.size]; omega
  | iszeroZero => simp [Term.size]
  | iszeroSucc _ => simp [Term.size]; omega
  | iszeroCong _ ih => simp [Term.size]; omega

/-- **Theorem 3.5.12 (Termination)**: every term evaluates to some normal
form. The proof is by strong induction on the size of the term, since each
step strictly decreases size. -/
theorem MultiStep.exists_normalForm (t : Term) :
    ∃ u, (t ⟶* u) ∧ NormalForm u := by
  by_cases h : ∃ t', t ⟶ t'
  · obtain ⟨t', ht'⟩ := h
    have : t'.size < t.size := ht'.size_lt
    obtain ⟨u, hu, hnf⟩ := exists_normalForm t'
    exact ⟨u, .head ht' hu, hnf⟩
  · exact ⟨t, .refl t, h⟩
termination_by t.size

/-! ## Stuck terms

Not every normal form is a value: evaluation can get *stuck*, which is how
this untyped language models runtime errors (TAPL §3.5). -/

/-- A term is stuck if it is a normal form but not a value (TAPL
exercise 3.5.16). -/
def Stuck (t : Term) : Prop := NormalForm t ∧ ¬ Value t

/-- `succ true` is stuck: applying a numeric operator to a boolean is a
runtime error. -/
example : Stuck (succ tru) := by
  constructor
  · intro ⟨t', h⟩
    cases h with
    | succCong h => cases h
  · intro hv
    cases hv with
    | num hn => cases hn with
      | succ hn => cases hn

/-! ## Big-step evaluation (exercise 3.5.17) -/

/-- Big-step ("natural") evaluation `t ⇓ v` (TAPL exercise 3.5.17). -/
inductive BigStep : Term → Term → Prop where
  | value {v : Term} : Value v → BigStep v v
  | iteTrue {t₁ t₂ t₃ v : Term} :
      BigStep t₁ tru → BigStep t₂ v → BigStep (ite t₁ t₂ t₃) v
  | iteFalse {t₁ t₂ t₃ v : Term} :
      BigStep t₁ fls → BigStep t₃ v → BigStep (ite t₁ t₂ t₃) v
  | succ {t v : Term} :
      NValue v → BigStep t v → BigStep (succ t) (succ v)
  | predZero {t : Term} :
      BigStep t zero → BigStep (pred t) zero
  | predSucc {t v : Term} :
      NValue v → BigStep t (succ v) → BigStep (pred t) v
  | iszeroZero {t : Term} :
      BigStep t zero → BigStep (iszero t) tru
  | iszeroSucc {t v : Term} :
      NValue v → BigStep t (succ v) → BigStep (iszero t) fls

@[inherit_doc] scoped infix:50 " ⇓ " => BigStep

/-- Big-step results are values. -/
theorem BigStep.value_right {t v : Term} (h : t ⇓ v) : Value v := by
  induction h with
  | value hv => exact hv
  | iteTrue _ _ _ ih => exact ih
  | iteFalse _ _ _ ih => exact ih
  | succ hn _ _ => exact .num (.succ hn)
  | predZero _ _ => exact .num .zero
  | predSucc hn _ _ => exact .num hn
  | iszeroZero _ _ => exact .tru
  | iszeroSucc _ _ _ => exact .fls

/-- Big-step evaluation of a value yields that value back. -/
theorem BigStep.eq_of_value {t v : Term} (hv : Value t) (h : t ⇓ v) : v = t := by
  induction h with
  | value _ => rfl
  | iteTrue _ _ _ _ | iteFalse _ _ _ _ | predZero _ _ | predSucc _ _ _
  | iszeroZero _ _ | iszeroSucc _ _ _ =>
      cases hv with | num hn => cases hn
  | succ _ _ ih =>
      cases hv with
      | num hnv => cases hnv with
        | succ hnv => rw [ih (.num hnv)]

/-- Multi-step congruence for `ite`. -/
theorem MultiStep.ite_cong {t₁ t₁' t₂ t₃ : Term} (h : t₁ ⟶* t₁') :
    ite t₁ t₂ t₃ ⟶* ite t₁' t₂ t₃ := by
  induction h with
  | refl _ => exact .refl _
  | head s _ ih => exact .head (.ifCong s) ih

/-- Multi-step congruence for `succ`. -/
theorem MultiStep.succ_cong {t t' : Term} (h : t ⟶* t') :
    succ t ⟶* succ t' := by
  induction h with
  | refl _ => exact .refl _
  | head s _ ih => exact .head (.succCong s) ih

/-- Multi-step congruence for `pred`. -/
theorem MultiStep.pred_cong {t t' : Term} (h : t ⟶* t') :
    pred t ⟶* pred t' := by
  induction h with
  | refl _ => exact .refl _
  | head s _ ih => exact .head (.predCong s) ih

/-- Multi-step congruence for `iszero`. -/
theorem MultiStep.iszero_cong {t t' : Term} (h : t ⟶* t') :
    iszero t ⟶* iszero t' := by
  induction h with
  | refl _ => exact .refl _
  | head s _ ih => exact .head (.iszeroCong s) ih

/-- Big-step evaluation implies multi-step evaluation (one half of
exercise 3.5.17). -/
theorem BigStep.toMultiStep {t v : Term} (h : t ⇓ v) : t ⟶* v := by
  induction h with
  | value _ => exact .refl _
  | iteTrue _ _ ih₁ ih₂ =>
      exact (MultiStep.ite_cong ih₁).trans (.head .ifTrue ih₂)
  | iteFalse _ _ ih₁ ih₂ =>
      exact (MultiStep.ite_cong ih₁).trans (.head .ifFalse ih₂)
  | succ _ _ ih => exact MultiStep.succ_cong ih
  | predZero _ ih =>
      exact (MultiStep.pred_cong ih).trans (.head .predZero (.refl _))
  | predSucc hn _ ih =>
      exact (MultiStep.pred_cong ih).trans (.head (.predSucc hn) (.refl _))
  | iszeroZero _ ih =>
      exact (MultiStep.iszero_cong ih).trans (.head .iszeroZero (.refl _))
  | iszeroSucc hn _ ih =>
      exact (MultiStep.iszero_cong ih).trans (.head (.iszeroSucc hn) (.refl _))

/-- A small step preserves the big-step result: if `t ⟶ t'` and `t' ⇓ v`
then `t ⇓ v`. -/
theorem BigStep.expand {t t' v : Term} (hs : t ⟶ t') (h : t' ⇓ v) : t ⇓ v := by
  induction hs generalizing v with
  | ifTrue => exact .iteTrue (.value .tru) h
  | ifFalse => exact .iteFalse (.value .fls) h
  | ifCong _ ih =>
      cases h with
      | value hv => cases hv with | num hn => cases hn
      | iteTrue h₁ h₂ => exact .iteTrue (ih h₁) h₂
      | iteFalse h₁ h₂ => exact .iteFalse (ih h₁) h₂
  | succCong _ ih =>
      cases h with
      | value hv =>
          cases hv with
          | num hn =>
            cases hn with
            | succ hn => exact .succ hn (ih (.value (.num hn)))
      | succ hn h => exact .succ hn (ih h)
  | predZero => cases h with
      | value hv => exact .predZero (.value (.num .zero))
  | predSucc hn =>
      cases h.eq_of_value (.num hn)
      exact .predSucc hn (.value (.num (.succ hn)))
  | predCong _ ih =>
      cases h with
      | value hv => cases hv with | num hn => cases hn
      | predZero h => exact .predZero (ih h)
      | predSucc hn h => exact .predSucc hn (ih h)
  | iszeroZero => cases h with
      | value hv => exact .iszeroZero (.value (.num .zero))
  | iszeroSucc hn => cases h with
      | value hv => exact .iszeroSucc hn (.value (.num (.succ hn)))
  | iszeroCong _ ih =>
      cases h with
      | value hv => cases hv with | num hn => cases hn
      | iszeroZero h => exact .iszeroZero (ih h)
      | iszeroSucc hn h => exact .iszeroSucc hn (ih h)

/-- Multi-step evaluation to a value implies big-step evaluation (the other
half of exercise 3.5.17). -/
theorem MultiStep.toBigStep {t v : Term} (h : t ⟶* v) (hv : Value v) :
    t ⇓ v := by
  induction h with
  | refl _ => exact .value hv
  | head s _ ih => exact .expand s (ih hv)

/-- **Exercise 3.5.17**: small-step and big-step evaluation agree. -/
theorem bigStep_iff_multiStep {t v : Term} (hv : Value v) :
    t ⇓ v ↔ t ⟶* v :=
  ⟨BigStep.toMultiStep, fun h => h.toBigStep hv⟩

/-! ## Examples -/

/-- `if false then false else true ⟶ true` -/
example : ite fls fls tru ⟶ tru := .ifFalse

/-- `if iszero (pred (succ 0)) then 0 else succ 0` evaluates to `0`. -/
example : ite (iszero (pred (succ zero))) zero (succ zero) ⟶* zero :=
  .head (.ifCong (.iszeroCong (.predSucc .zero)))
    (.head (.ifCong .iszeroZero)
      (.head .ifTrue (.refl _)))

/-- `pred (succ (pred 0))` big-steps to `0`. -/
example : pred (succ (pred zero)) ⇓ zero :=
  .predSucc .zero (.succ .zero (.predZero (.value (.num .zero))))

end Chapter03
