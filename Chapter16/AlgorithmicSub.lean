import Chapter15.Subtyping

/-!
# Chapter 16: Metatheory of Subtyping

The declarative subtype relation of chapter 15 is not an algorithm: the
`S-Refl` and `S-Trans` rules are not syntax-directed (`S-Trans` would
require *guessing* a middle type). This chapter develops the standard
remedy: an **algorithmic** subtype relation with one rule per pair of
type constructors, and proofs that reflexivity and transitivity are
*admissible* for it, making it equivalent to the declarative system
(TAPL §16.1, lemmas 16.1.2–16.1.6, theorem 16.1.5).

Chapter 17 turns the algorithmic relation into an executable checker.
-/

namespace Chapter16

open Chapter15 (Ty Sub)
open Chapter15.Ty
open scoped Chapter15

/-- The algorithmic subtype relation `↦ S <: T` (TAPL fig. 16-1, with the
product rule): exactly one rule per pair of head constructors, no
reflexivity, no transitivity. -/
inductive SubA : Ty → Ty → Prop where
  | top (S : Ty) : SubA S .top                               -- SA-Top
  | bool : SubA .bool .bool                                  -- SA-Bool
  | arrow {S₁ S₂ T₁ T₂ : Ty} :
      SubA T₁ S₁ → SubA S₂ T₂ →
      SubA (.arrow S₁ S₂) (.arrow T₁ T₂)                     -- SA-Arrow
  | prod {S₁ S₂ T₁ T₂ : Ty} :
      SubA S₁ T₁ → SubA S₂ T₂ →
      SubA (.prod S₁ S₂) (.prod T₁ T₂)                       -- SA-Prod

/-- **Lemma 16.1.2 (Reflexivity is admissible)**. -/
theorem SubA.refl : ∀ T : Ty, SubA T T := by
  intro T
  induction T with
  | top => exact .top _
  | bool => exact .bool
  | arrow T₁ T₂ ih₁ ih₂ => exact .arrow ih₁ ih₂
  | prod T₁ T₂ ih₁ ih₂ => exact .prod ih₁ ih₂

/-- **Lemma 16.1.6 (Transitivity is admissible)**, by induction on the
middle type. -/
theorem SubA.trans : ∀ (U S T : Ty), SubA S U → SubA U T → SubA S T := by
  intro U
  induction U with
  | top =>
      intro S T _ h₂
      cases h₂ with
      | top => exact .top _
  | bool =>
      intro S T h₁ h₂
      cases h₁ with
      | bool => exact h₂
  | arrow U₁ U₂ ih₁ ih₂ =>
      intro S T h₁ h₂
      cases h₂ with
      | top => exact .top _
      | arrow h₂a h₂b =>
          cases h₁ with
          | arrow h₁a h₁b =>
              exact .arrow (ih₁ _ _ h₂a h₁a) (ih₂ _ _ h₁b h₂b)
  | prod U₁ U₂ ih₁ ih₂ =>
      intro S T h₁ h₂
      cases h₂ with
      | top => exact .top _
      | prod h₂a h₂b =>
          cases h₁ with
          | prod h₁a h₁b =>
              exact .prod (ih₁ _ _ h₁a h₂a) (ih₂ _ _ h₁b h₂b)

/-- The algorithmic relation is sound for the declarative one. -/
theorem SubA.toSub {S T : Ty} (h : SubA S T) : Sub S T := by
  induction h with
  | top _ => exact .top _
  | bool => exact .refl _
  | arrow _ _ ih₁ ih₂ => exact .arrow ih₁ ih₂
  | prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂

/-- … and complete: `S-Refl` and `S-Trans` are eliminated by their
admissibility lemmas. -/
theorem Sub.toSubA {S T : Ty} (h : Sub S T) : SubA S T := by
  induction h with
  | refl T => exact SubA.refl T
  | trans _ _ ih₁ ih₂ => exact SubA.trans _ _ _ ih₁ ih₂
  | top _ => exact .top _
  | arrow _ _ ih₁ ih₂ => exact .arrow ih₁ ih₂
  | prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂

/-- **Theorem 16.1.5 (Equivalence)**: the declarative and algorithmic
subtype relations coincide. -/
theorem subA_iff_sub {S T : Ty} : SubA S T ↔ Sub S T :=
  ⟨SubA.toSub, Sub.toSubA⟩

/-! ## Examples

The algorithmic derivations of chapter 15's example subtypings — now
unique and mechanical. -/

example : SubA (Ty.bool ⊗ Ty.bool) .top := .top _

example : SubA (Ty.bool ⊗ Ty.bool) (Ty.top ⊗ Ty.bool) :=
  .prod (.top _) .bool

example : SubA (Ty.top ⇒ Ty.bool) (Ty.bool ⇒ Ty.bool) :=
  .arrow (.top _) .bool

/-- A transitivity chain the algorithmic system reaches directly:
`(Top ⇒ Bool) ⊗ Bool <: (Bool ⇒ Bool) ⊗ Top`. -/
example : SubA ((Ty.top ⇒ Ty.bool) ⊗ Ty.bool) ((Ty.bool ⇒ Ty.bool) ⊗ Ty.top) :=
  .prod (.arrow (.top _) .bool) (.top _)

end Chapter16
