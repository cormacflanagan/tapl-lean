# Chapter 16 — Metatheory of Subtyping

The declarative subtype relation of [chapter 15](../Chapter15/) is not an
algorithm: `S-Refl` and `S-Trans` are not syntax-directed (`S-Trans` would
require *guessing* a middle type). This chapter develops the standard
remedy: an **algorithmic** subtype relation with exactly one rule per pair
of type constructors, and proofs that reflexivity and transitivity are
*admissible* for it — making it equivalent to the declarative system
(TAPL §16.1). [Chapter 17](../Chapter17/) turns it into an executable
checker.

All code lives in [`AlgorithmicSub.lean`](AlgorithmicSub.lean), reusing
chapter 15's `Ty` and declarative `Sub`.

> **Scope.** TAPL chapter 16 also covers algorithmic *typing* with minimal
> types (§16.2) and the join/meet operations needed to type `if` under
> subtyping (§16.3). For this language joins and meets always exist (with
> `Top` as the fallback join of incompatible types); the minimal-typing
> development adds bookkeeping but no new ideas beyond the inversion
> machinery already proved in chapter 15, and is omitted here.

## The algorithmic relation

```lean
inductive SubA : Ty → Ty → Prop where
  | top (S : Ty) : SubA S .top                        -- SA-Top
  | bool : SubA .bool .bool                           -- SA-Bool
  | arrow : SubA T₁ S₁ → SubA S₂ T₂ →
            SubA (.arrow S₁ S₂) (.arrow T₁ T₂)        -- SA-Arrow
  | prod  : SubA S₁ T₁ → SubA S₂ T₂ →
            SubA (.prod S₁ S₂) (.prod T₁ T₂)          -- SA-Prod
```

No reflexivity, no transitivity — at most one rule applies to any pair of
types, so derivations are unique and mechanical.

## Admissibility and equivalence

```lean
-- Lemma 16.1.2: reflexivity is admissible
theorem SubA.refl : ∀ T : Ty, SubA T T

-- Lemma 16.1.6: transitivity is admissible (induction on the middle type)
theorem SubA.trans : ∀ (U S T : Ty), SubA S U → SubA U T → SubA S T

-- soundness and completeness
theorem SubA.toSub (h : SubA S T) : Sub S T
theorem Sub.toSubA (h : Sub S T) : SubA S T

-- Theorem 16.1.5: the two relations coincide
theorem subA_iff_sub : SubA S T ↔ Sub S T
```

The transitivity proof is the interesting one: it goes by structural
induction on the **middle type** `U`, with the contravariant twist that in
the arrow case the two induction hypotheses are used with their arguments
swapped.

## Examples

Chapter 15's example subtypings, now with unique algorithmic derivations:

```lean
example : SubA (Ty.bool ⊗ Ty.bool) .top
example : SubA (Ty.bool ⊗ Ty.bool) (Ty.top ⊗ Ty.bool)
example : SubA (Ty.top ⇒ Ty.bool) (Ty.bool ⇒ Ty.bool)
example : SubA ((Ty.top ⇒ Ty.bool) ⊗ Ty.bool) ((Ty.bool ⇒ Ty.bool) ⊗ Ty.top)
```
