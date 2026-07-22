# Chapter 17 — An ML Implementation of Subtyping

TAPL chapter 17 implements the algorithmic subtype relation of
[chapter 16](../Chapter16/) as an OCaml function. Ours is the Lean function
`subtype : Ty → Ty → Bool` in [`SubCheck.lean`](SubCheck.lean) — proved to
decide exactly the declarative subtype relation of chapter 15, which makes
subtyping **decidable** and lets `decide` settle subtyping questions
inside the kernel.

## The checker

The recursion swaps its arguments at contravariant positions, so it is not
structural in either argument; it is bounded by fuel, for which the
combined size of the two types suffices (this also keeps the function
kernel-computable, which a well-founded-recursion definition would not be):

```lean
def size : Ty → Nat
  | .top => 1
  | .bool => 1
  | .arrow T₁ T₂ => size T₁ + size T₂ + 1
  | .prod T₁ T₂ => size T₁ + size T₂ + 1

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

def subtype (S T : Ty) : Bool := subtypeF (size S + size T) S T
```

## Correctness and decidability

```lean
theorem size_pos : ∀ T : Ty, 0 < size T
theorem subtypeF_sound (h : subtypeF fuel S T = true) : SubA S T
theorem subtypeF_complete (h : SubA S T) :
    ∀ fuel, size S + size T ≤ fuel → subtypeF fuel S T = true

-- the checker decides chapter 15's declarative relation
theorem subtype_iff : subtype S T = true ↔ Sub S T

instance : ∀ S T : Ty, Decidable (Sub S T)
```

Soundness holds for *any* fuel (a `true` answer is always right);
completeness needs enough fuel, and `size S + size T` always is.

## Examples

With the `Decidable` instance, the kernel settles subtyping by `decide` —
both positively and negatively:

```lean
example : Sub (Ty.top ⇒ Ty.bool) (Ty.bool ⇒ Ty.bool) := by decide
example : Sub ((Ty.bool ⇒ Ty.bool) ⊗ Ty.bool) .top := by decide
example : Sub ((Ty.bool ⇒ Ty.bool) ⇒ Ty.bool) ((Ty.top ⇒ Ty.bool) ⇒ Ty.top) := by decide

example : ¬ Sub (Ty.bool ⇒ Ty.bool) (Ty.top ⇒ Ty.bool) := by decide
example : ¬ Sub Ty.top Ty.bool := by decide
example : ¬ Sub (Ty.top ⊗ Ty.bool) (Ty.bool ⇒ Ty.top) := by decide
```
