# Chapter 15 — Subtyping

λ→ with booleans and pairs, extended with a maximal type **`Top`** and the
**subsumption rule**: a term of a subtype may be used wherever a supertype
is expected. Arrows are **contravariant** in their domain and covariant in
their codomain; products are covariant in both components.

All code lives in [`Subtyping.lean`](Subtyping.lean).

> **Records.** TAPL presents record subtyping (width, depth, permutation).
> Products are the binary, positional special case — depth subtyping is
> `S-Prod` below; width/permutation are about labels and add bookkeeping
> but no new proof ideas, so this formalization uses products.

## The subtype relation

```lean
inductive Ty : Type where
  | top
  | bool
  | arrow (T₁ T₂ : Ty)      -- T₁ ⇒ T₂
  | prod (T₁ T₂ : Ty)       -- T₁ ⊗ T₂

inductive Sub : Ty → Ty → Prop where
  | refl (T : Ty) : Sub T T                                 -- S-Refl
  | trans : Sub S U → Sub U T → Sub S T                     -- S-Trans
  | top (S : Ty) : Sub S .top                               -- S-Top
  | arrow : Sub T₁ S₁ → Sub S₂ T₂ →
            Sub (S₁ ⇒ S₂) (T₁ ⇒ T₂)                          -- S-Arrow (contra/co)
  | prod : Sub S₁ T₁ → Sub S₂ T₂ →
           Sub (S₁ ⊗ S₂) (T₁ ⊗ T₂)                           -- S-Prod

infix:45 " <: " => Sub
```

## Typing with subsumption

Terms, values and evaluation are exactly those of chapters 9/11 (subtyping
changes only the statics). The typing relation gains one rule:

```lean
| sub : HasType Γ t S → (S <: T) → HasType Γ t T             -- T-Sub
```

## Inversion of the subtype relation (lemma 15.3.2)

`T-Sub` destroys syntax-directedness, so the metatheory first needs to
know what subtypes of each type constructor look like:

```lean
theorem Sub.bool_inv  (h : S <: T) : T = .bool → S = .bool

theorem Sub.arrow_inv (h : S <: T) :
    ∀ T₁ T₂, T = T₁ ⇒ T₂ →
      ∃ S₁ S₂, S = S₁ ⇒ S₂ ∧ (T₁ <: S₁) ∧ (S₂ <: T₂)

theorem Sub.prod_inv (h : S <: T) :
    ∀ T₁ T₂, T = T₁ ⊗ T₂ →
      ∃ S₁ S₂, S = S₁ ⊗ S₂ ∧ (S₁ <: T₁) ∧ (S₂ <: T₂)
```

## Inversion of typing modulo subtyping (lemma 15.3.3)

```lean
theorem abs_inv (h : Γ ⊢ abs S₁ body ∶ T) :
    ∀ {T₁ T₂}, (T <: T₁ ⇒ T₂) → (T₁ <: S₁) ∧ ((S₁ :: Γ) ⊢ body ∶ T₂)

theorem pair_inv (h : Γ ⊢ pair t₁ t₂ ∶ T) :
    ∀ {T₁ T₂}, (T <: T₁ ⊗ T₂) → (Γ ⊢ t₁ ∶ T₁) ∧ (Γ ⊢ t₂ ∶ T₂)
```

## Metatheory

Weakening and substitution go through as in chapter 9 (subsumption adds a
one-line case to each); the substitution lemma is stated by induction on
the typing derivation with a context equation:

```lean
theorem weakening (h : Γ ⊢ t ∶ T) : ∀ c S, insertAt S c Γ ⊢ shift 1 c t ∶ T

theorem substitution (ht : Δ ⊢ t ∶ T) :
    ∀ Γ k S s, Δ = insertAt S k Γ → (Γ.drop k ⊢ s ∶ S) →
      Γ ⊢ subst k s t ∶ T
```

Canonical forms (lemma 15.3.6) now require chasing subsumption chains
through the subtype-inversion lemmas:

```lean
theorem canonical_arrow (h : Γ ⊢ v ∶ T) :
    Value v → T = T₁ ⇒ T₂ → ∃ S body, v = abs S body
theorem canonical_bool (h : Γ ⊢ v ∶ T) :
    Value v → T = .bool → v = tru ∨ v = fls
theorem canonical_prod (h : Γ ⊢ v ∶ T) :
    Value v → T = T₁ ⊗ T₂ → ∃ v₁ v₂, v = pair v₁ v₂ ∧ Value v₁ ∧ Value v₂
```

And the main theorems (15.3.5, 15.3.7):

```lean
theorem preservation (h : Γ ⊢ t ∶ T) : ∀ t', (t ⟶ t') → Γ ⊢ t' ∶ T
theorem progress (h : [] ⊢ t ∶ T) : Value t ∨ ∃ t', t ⟶ t'
```

## Examples

```lean
example : (Ty.bool ⊗ Ty.bool) <: .top                      -- everything <: Top
example : (Ty.bool ⊗ Ty.bool) <: (Ty.top ⊗ Ty.bool)        -- depth subtyping
example : (Ty.top ⇒ Ty.bool) <: (Ty.bool ⇒ Ty.bool)        -- contravariance

def idTop : Term := abs .top (var 0)                       -- λx:Top. x

example : [] ⊢ app idTop tru ∶ .top     -- accepted via subsumption
example : app idTop tru ⟶* tru

example : [] ⊢ pair tru fls ∶ (Ty.top ⊗ Ty.bool)   -- a pair at a supertype
```
