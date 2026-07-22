import Chapter03.Arith

/-!
# Chapter 8: Typed Arithmetic Expressions

The first type system of the book, for the arithmetic language of
chapter 3: two types (`Bool` and `Nat`), a typing relation, and the two
theorems whose pattern recurs through the rest of the book — **progress**
("a well-typed term is not stuck now") and **preservation** ("evaluation
keeps terms well typed") — combining into type safety ("well-typed programs
never get stuck").
-/

namespace Chapter08

open Chapter03 Chapter03.Term

/-- The types: `Bool` and `Nat` (TAPL figure 8-1, 8-2). -/
inductive Ty : Type where
  | bool
  | nat
  deriving Repr, DecidableEq

/-- The typing relation `t ∶ T` (TAPL figures 8-1 and 8-2). -/
inductive HasType : Term → Ty → Prop where
  | tru : HasType tru .bool
  | fls : HasType fls .bool
  | ite {t₁ t₂ t₃ : Term} {T : Ty} :
      HasType t₁ .bool → HasType t₂ T → HasType t₃ T →
      HasType (ite t₁ t₂ t₃) T
  | zero : HasType zero .nat
  | succ {t : Term} : HasType t .nat → HasType (succ t) .nat
  | pred {t : Term} : HasType t .nat → HasType (pred t) .nat
  | iszero {t : Term} : HasType t .nat → HasType (iszero t) .bool

@[inherit_doc] scoped infix:40 " ∶ " => HasType

/-! ## Inversion and uniqueness (TAPL lemmas 8.2.2, 8.2.4) -/

/-- Inversion, sample clause: a well-typed `succ` has type `Nat`, and so
does its argument. (The other clauses are equally immediate by `cases`.) -/
theorem inversion_succ {t : Term} {R : Ty} (h : succ t ∶ R) :
    R = .nat ∧ t ∶ .nat := by
  cases h with
  | succ h => exact ⟨rfl, h⟩

/-- Inversion, sample clause for `ite`. -/
theorem inversion_ite {t₁ t₂ t₃ : Term} {R : Ty} (h : ite t₁ t₂ t₃ ∶ R) :
    t₁ ∶ .bool ∧ t₂ ∶ R ∧ t₃ ∶ R := by
  cases h with
  | ite h₁ h₂ h₃ => exact ⟨h₁, h₂, h₃⟩

/-- **Theorem 8.2.4 (Uniqueness of types)**: each term has at most one
type. -/
theorem HasType.unique {t : Term} {T₁ T₂ : Ty}
    (h₁ : t ∶ T₁) (h₂ : t ∶ T₂) : T₁ = T₂ := by
  induction h₁ generalizing T₂ with
  | tru => cases h₂; rfl
  | fls => cases h₂; rfl
  | ite _ _ _ _ ih₂ _ => cases h₂ with
    | ite _ h₂' _ => exact ih₂ h₂'
  | zero => cases h₂; rfl
  | succ _ _ => cases h₂; rfl
  | pred _ _ => cases h₂; rfl
  | iszero _ _ => cases h₂; rfl

/-! ## Canonical forms (TAPL lemma 8.3.1) -/

/-- A boolean-typed value is `tru` or `fls`. -/
theorem canonical_bool {v : Term} (hv : Value v) (ht : v ∶ .bool) :
    v = tru ∨ v = fls := by
  cases hv with
  | tru => exact .inl rfl
  | fls => exact .inr rfl
  | num hn => cases hn <;> cases ht

/-- A `Nat`-typed value is a numeric value. -/
theorem canonical_nat {v : Term} (hv : Value v) (ht : v ∶ .nat) :
    NValue v := by
  cases hv with
  | tru => cases ht
  | fls => cases ht
  | num hn => exact hn

/-! ## Progress and preservation (TAPL theorems 8.3.2, 8.3.3) -/

/-- **Theorem 8.3.2 (Progress)**: a well-typed term is a value or can take
a step of evaluation. -/
theorem progress {t : Term} {T : Ty} (h : t ∶ T) :
    Value t ∨ ∃ t', t ⟶ t' := by
  induction h with
  | tru => exact .inl .tru
  | fls => exact .inl .fls
  | zero => exact .inl (.num .zero)
  | ite h₁ _ _ ih₁ _ _ =>
      rcases ih₁ with hv | ⟨t₁', hs⟩
      · rcases canonical_bool hv h₁ with rfl | rfl
        · exact .inr ⟨_, .ifTrue⟩
        · exact .inr ⟨_, .ifFalse⟩
      · exact .inr ⟨_, .ifCong hs⟩
  | succ h ih =>
      rcases ih with hv | ⟨t', hs⟩
      · exact .inl (.num (.succ (canonical_nat hv h)))
      · exact .inr ⟨_, .succCong hs⟩
  | pred h ih =>
      rcases ih with hv | ⟨t', hs⟩
      · cases canonical_nat hv h with
        | zero => exact .inr ⟨_, .predZero⟩
        | succ hn => exact .inr ⟨_, .predSucc hn⟩
      · exact .inr ⟨_, .predCong hs⟩
  | iszero h ih =>
      rcases ih with hv | ⟨t', hs⟩
      · cases canonical_nat hv h with
        | zero => exact .inr ⟨_, .iszeroZero⟩
        | succ hn => exact .inr ⟨_, .iszeroSucc hn⟩
      · exact .inr ⟨_, .iszeroCong hs⟩

/-- **Theorem 8.3.3 (Preservation)**: types are preserved by evaluation. -/
theorem preservation {t t' : Term} {T : Ty} (h : t ∶ T) (hs : t ⟶ t') :
    t' ∶ T := by
  induction hs generalizing T with
  | ifTrue => cases h with
    | ite _ h₂ _ => exact h₂
  | ifFalse => cases h with
    | ite _ _ h₃ => exact h₃
  | ifCong _ ih => cases h with
    | ite h₁ h₂ h₃ => exact .ite (ih h₁) h₂ h₃
  | succCong _ ih => cases h with
    | succ h => exact .succ (ih h)
  | predZero => cases h with
    | pred h => exact h
  | predSucc _ => cases h with
    | pred h => cases h with
      | succ h => exact h
  | predCong _ ih => cases h with
    | pred h => exact .pred (ih h)
  | iszeroZero => cases h with
    | iszero _ => exact .tru
  | iszeroSucc _ => cases h with
    | iszero _ => exact .fls
  | iszeroCong _ ih => cases h with
    | iszero h => exact .iszero (ih h)

/-! ## Type safety -/

/-- Types are preserved by multi-step evaluation. -/
theorem preservation_multi {t t' : Term} {T : Ty} (h : t ∶ T)
    (hs : t ⟶* t') : t' ∶ T := by
  induction hs with
  | refl _ => exact h
  | head s _ ih => exact ih (preservation h s)

/-- **Type safety**: a well-typed term never reaches a stuck state — every
reachable normal form is a value. -/
theorem safety {t t' : Term} {T : Ty} (h : t ∶ T) (hs : t ⟶* t') :
    ¬ Stuck t' := by
  intro ⟨hnf, hnv⟩
  rcases progress (preservation_multi h hs) with hv | hstep
  · exact hnv hv
  · exact hnf hstep

/-! ## Examples -/

/-- A typing derivation:
`if iszero 0 then 0 else succ 0 ∶ Nat`. -/
example : ite (iszero zero) zero (succ zero) ∶ .nat :=
  .ite (.iszero .zero) .zero (.succ .zero)

/-- `succ tru` — the stuck term of chapter 3 — is not typable, at any
type: the type system rejects exactly the sort of term that would get
stuck. -/
example (T : Ty) : ¬ (succ tru ∶ T) := by
  intro h
  cases h with
  | succ h => cases h

/-- `if tru then 0 else fls` is not typable: both branches of a
conditional must have the same type, even when the guard is constant. -/
example (T : Ty) : ¬ (ite tru zero fls ∶ T) := by
  intro h
  cases h with
  | ite _ h₂ h₃ =>
      cases h₂
      cases h₃

end Chapter08
