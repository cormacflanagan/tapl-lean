import Chapter09.Stlc

/-!
# Chapter 10: An ML Implementation of Simple Types

TAPL chapter 10 implements a typechecker for λ→ in OCaml. Here it is a
Lean function `typeof : Ctx → Term → Option Ty` — again with the upgrade
that we *prove* it sound and complete for the typing relation of
chapter 9, so `typeof` is a decision procedure for typability.
-/

namespace Chapter10

open Chapter09 Chapter09.Term

/-- The typechecking algorithm, mirroring TAPL's `typeof`: `none` plays
the role of the OCaml version's type-error exceptions. -/
def typeof (Γ : Ctx) : Term → Option Ty
  | .var n => Γ.get? n
  | .abs T t => (typeof (T :: Γ) t).map (T ⇒ ·)
  | .app t₁ t₂ =>
      match typeof Γ t₁, typeof Γ t₂ with
      | some (.arrow T₁ T₂), some T₁' => if T₁ = T₁' then some T₂ else none
      | _, _ => none
  | .tru => some .bool
  | .fls => some .bool
  | .ite t₁ t₂ t₃ =>
      match typeof Γ t₁, typeof Γ t₂, typeof Γ t₃ with
      | some .bool, some T₂, some T₃ => if T₂ = T₃ then some T₂ else none
      | _, _, _ => none

/-- `typeof` is complete: every derivable typing is computed. -/
theorem typeof_complete {Γ : Ctx} {t : Term} {T : Ty}
    (h : Γ ⊢ t ∶ T) : typeof Γ t = some T := by
  induction h with
  | var hget => exact hget
  | abs _ ih => simp [typeof, ih]
  | app _ _ ih₁ ih₂ => simp [typeof, ih₁, ih₂]
  | tru => rfl
  | fls => rfl
  | ite _ _ _ ih₁ ih₂ ih₃ => simp [typeof, ih₁, ih₂, ih₃]

/-- `typeof` is sound: every computed type is derivable. -/
theorem typeof_sound : ∀ {t : Term} {Γ : Ctx} {T : Ty},
    typeof Γ t = some T → Γ ⊢ t ∶ T := by
  intro t
  induction t with
  | var n =>
      intro Γ T h
      exact .var h
  | abs S t ih =>
      intro Γ T h
      rw [show typeof Γ (.abs S t) = (typeof (S :: Γ) t).map (S ⇒ ·) from rfl,
          Option.map_eq_some'] at h
      obtain ⟨T₂, hT₂, rfl⟩ := h
      exact .abs (ih hT₂)
  | app t₁ t₂ ih₁ ih₂ =>
      intro Γ T h
      rw [show typeof Γ (.app t₁ t₂) =
            match typeof Γ t₁, typeof Γ t₂ with
            | some (.arrow T₁ T₂), some T₁' =>
                if T₁ = T₁' then some T₂ else none
            | _, _ => none from rfl] at h
      cases h₁ : typeof Γ t₁ with
      | none => rw [h₁] at h; cases h
      | some S =>
          cases S with
          | bool => rw [h₁] at h; cases h₂ : typeof Γ t₂ <;> rw [h₂] at h <;> cases h
          | arrow T₁ T₂ =>
              rw [h₁] at h
              cases h₂ : typeof Γ t₂ with
              | none => rw [h₂] at h; cases h
              | some T₁' =>
                  rw [h₂] at h
                  by_cases heq : T₁ = T₁'
                  · subst heq
                    simp at h
                    subst h
                    exact .app (ih₁ h₁) (ih₂ h₂)
                  · simp [heq] at h
  | tru => intro Γ T h; cases h; exact .tru
  | fls => intro Γ T h; cases h; exact .fls
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
      intro Γ T h
      rw [show typeof Γ (.ite t₁ t₂ t₃) =
            match typeof Γ t₁, typeof Γ t₂, typeof Γ t₃ with
            | some .bool, some T₂, some T₃ =>
                if T₂ = T₃ then some T₂ else none
            | _, _, _ => none from rfl] at h
      cases h₁ : typeof Γ t₁ with
      | none => rw [h₁] at h; cases h
      | some S =>
          cases S with
          | arrow _ _ =>
              rw [h₁] at h
              cases h₂ : typeof Γ t₂ <;> rw [h₂] at h <;>
                cases h₃ : typeof Γ t₃ <;> rw [h₃] at h <;> cases h
          | bool =>
              rw [h₁] at h
              cases h₂ : typeof Γ t₂ with
              | none =>
                  rw [h₂] at h
                  cases h₃ : typeof Γ t₃ <;> rw [h₃] at h <;> cases h
              | some T₂ =>
                  rw [h₂] at h
                  cases h₃ : typeof Γ t₃ with
                  | none => rw [h₃] at h; cases h
                  | some T₃ =>
                      rw [h₃] at h
                      by_cases heq : T₂ = T₃
                      · subst heq
                        simp at h
                        subst h
                        exact .ite (ih₁ h₁) (ih₂ h₂) (ih₃ h₃)
                      · simp [heq] at h

/-- `typeof` decides the typing relation. -/
theorem typeof_correct {Γ : Ctx} {t : Term} {T : Ty} :
    typeof Γ t = some T ↔ (Γ ⊢ t ∶ T) :=
  ⟨typeof_sound, typeof_complete⟩

/-- Typability is decidable: a term is typable iff `typeof` succeeds. -/
theorem typable_iff {Γ : Ctx} {t : Term} :
    (∃ T, Γ ⊢ t ∶ T) ↔ (typeof Γ t).isSome := by
  constructor
  · intro ⟨T, h⟩
    rw [typeof_complete h]
    rfl
  · intro h
    cases hT : typeof Γ t with
    | none => rw [hT] at h; cases h
    | some T => exact ⟨T, typeof_sound hT⟩

/-! ## Examples: running the typechecker -/

/-- `typeof` computes the type of boolean negation. -/
example : typeof [] notTerm = some (.bool ⇒ .bool) := by decide

/-- ... and of composition at `Bool`. -/
example : typeof [] composeTerm =
    some ((.bool ⇒ .bool) ⇒ (.bool ⇒ .bool) ⇒ .bool ⇒ .bool) := by decide

/-- The typechecker rejects self-application... -/
example : typeof [] (.abs .bool (.app (.var 0) (.var 0))) = none := by decide

/-- ... an argument-type mismatch... -/
example : typeof [] (.app notTerm (.abs .bool (.var 0))) = none := by decide

/-- ... and branches of different types. -/
example : typeof [] (.ite .tru .tru notTerm) = none := by decide

/-- Open terms typecheck under a context. With `f` the innermost binding
(position 0) and `x` at position 1, `f x` is `app (var 0) (var 1)`:
`f : Bool ⇒ Bool, x : Bool ⊢ f x ∶ Bool`. -/
example : typeof [.bool ⇒ .bool, .bool] (.app (.var 0) (.var 1)) =
    some .bool := by decide

/-- Applying the variables the wrong way round is rejected. -/
example : typeof [.bool ⇒ .bool, .bool] (.app (.var 1) (.var 0)) = none := by
  decide

end Chapter10
