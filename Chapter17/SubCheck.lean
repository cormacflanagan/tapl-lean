import Chapter16.AlgorithmicSub

/-!
# Chapter 17: An ML Implementation of Subtyping

TAPL chapter 17 implements the algorithmic subtype relation of chapter 16
as an OCaml function. Ours is the Lean function `subtype : Ty → Ty → Bool`
below — proved to decide exactly the (declarative) subtype relation of
chapter 15, which makes subtyping **decidable** and lets `decide` settle
subtyping questions inside the kernel.

The recursion swaps its arguments at contravariant positions, so it is not
structural in either argument; we bound it by fuel (the combined size of
the two types suffices), keeping the function kernel-computable.
-/

namespace Chapter17

open Chapter15 (Ty Sub)
open Chapter15.Ty
open scoped Chapter15
open Chapter16

/-- Size of a type (number of constructors): enough fuel for `subtypeF`. -/
def size : Ty → Nat
  | .top => 1
  | .bool => 1
  | .arrow T₁ T₂ => size T₁ + size T₂ + 1
  | .prod T₁ T₂ => size T₁ + size T₂ + 1

/-- Every type has at least one constructor. -/
theorem size_pos : ∀ T : Ty, 0 < size T := by
  intro T
  cases T <;> simp [size]

/-- The fuel-bounded subtype checker, one clause per algorithmic rule
(TAPL fig. 17-2 style); `false` when the fuel runs out. -/
def subtypeF : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, S, T =>
      match S, T with
      | _, .top => true
      | .bool, .bool => true
      | .arrow S₁ S₂, .arrow T₁ T₂ =>
          subtypeF fuel T₁ S₁ && subtypeF fuel S₂ T₂
      | .prod S₁ S₂, .prod T₁ T₂ =>
          subtypeF fuel S₁ T₁ && subtypeF fuel S₂ T₂
      | _, _ => false

/-- The subtype checker: run `subtypeF` with sufficient fuel. -/
def subtype (S T : Ty) : Bool := subtypeF (size S + size T) S T

/-- `subtypeF` is sound whatever the fuel: `true` answers are correct. -/
theorem subtypeF_sound :
    ∀ (fuel : Nat) (S T : Ty), subtypeF fuel S T = true → SubA S T := by
  intro fuel
  induction fuel with
  | zero => intro S T h; simp [subtypeF] at h
  | succ fuel ih =>
      intro S T h
      cases T with
      | top => exact .top S
      | bool =>
          cases S with
          | bool => exact .bool
          | top => simp [subtypeF] at h
          | arrow _ _ => simp [subtypeF] at h
          | prod _ _ => simp [subtypeF] at h
      | arrow T₁ T₂ =>
          cases S with
          | top => simp [subtypeF] at h
          | bool => simp [subtypeF] at h
          | prod _ _ => simp [subtypeF] at h
          | arrow S₁ S₂ =>
              simp [subtypeF] at h
              exact .arrow (ih T₁ S₁ h.1) (ih S₂ T₂ h.2)
      | prod T₁ T₂ =>
          cases S with
          | top => simp [subtypeF] at h
          | bool => simp [subtypeF] at h
          | arrow _ _ => simp [subtypeF] at h
          | prod S₁ S₂ =>
              simp [subtypeF] at h
              exact .prod (ih S₁ T₁ h.1) (ih S₂ T₂ h.2)

/-- `subtypeF` is complete once the fuel covers the combined size. -/
theorem subtypeF_complete {S T : Ty} (h : SubA S T) :
    ∀ fuel, size S + size T ≤ fuel → subtypeF fuel S T = true := by
  induction h with
  | top S =>
      intro fuel hf
      cases fuel with
      | zero => simp [size] at hf
      | succ fuel => cases S <;> simp [subtypeF]
  | bool =>
      intro fuel hf
      cases fuel with
      | zero => simp [size] at hf
      | succ fuel => simp [subtypeF]
  | @arrow S₁ S₂ T₁ T₂ _ _ ih₁ ih₂ =>
      intro fuel hf
      cases fuel with
      | zero => simp [size] at hf; omega
      | succ fuel =>
          simp [size] at hf
          simp [subtypeF, ih₁ fuel (by omega), ih₂ fuel (by omega)]
  | @prod S₁ S₂ T₁ T₂ _ _ ih₁ ih₂ =>
      intro fuel hf
      cases fuel with
      | zero => simp [size] at hf; omega
      | succ fuel =>
          simp [size] at hf
          simp [subtypeF, ih₁ fuel (by omega), ih₂ fuel (by omega)]

/-- **Correctness**: the checker decides the declarative subtype relation
of chapter 15. -/
theorem subtype_iff {S T : Ty} : subtype S T = true ↔ Sub S T := by
  constructor
  · intro h
    exact (subtypeF_sound _ S T h).toSub
  · intro h
    exact subtypeF_complete (Sub.toSubA h) _ (Nat.le_refl _)

/-- Subtyping is decidable. -/
instance : ∀ S T : Ty, Decidable (Sub S T) := fun S T =>
  decidable_of_iff (subtype S T = true) subtype_iff

/-! ## Examples: deciding subtyping inside the kernel -/

example : Sub (Ty.top ⇒ Ty.bool) (Ty.bool ⇒ Ty.bool) := by decide

example : Sub ((Ty.bool ⇒ Ty.bool) ⊗ Ty.bool) .top := by decide

/-- Contravariance twice flips back to covariance. -/
example : Sub ((Ty.bool ⇒ Ty.bool) ⇒ Ty.bool) ((Ty.top ⇒ Ty.bool) ⇒ Ty.top) := by
  decide

/-- Non-subtypings are refuted just as mechanically. -/
example : ¬ Sub (Ty.bool ⇒ Ty.bool) (Ty.top ⇒ Ty.bool) := by decide
example : ¬ Sub Ty.top Ty.bool := by decide
example : ¬ Sub (Ty.top ⊗ Ty.bool) (Ty.bool ⇒ Ty.top) := by decide

end Chapter17
