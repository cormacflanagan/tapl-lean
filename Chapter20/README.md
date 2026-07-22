# Chapter 20 — Recursive Types

**Iso-recursive types**: μ-types together with the explicit coercions
`fold [μX.T]` and `unfold [μX.T]` between a recursive type and its one-step
unfolding (TAPL figure 20-1). Types now contain a binder, so they get their
own de Bruijn indices and their own substitution operation.

The payoff is TAPL §20.1's famous example: with `D = μX. X → X` the untyped
lambda-calculus embeds into the typed language and a **well-typed divergent
term** exists — recursive types trade away normalization while keeping type
safety.

All code lives in [`Recursive.lean`](Recursive.lean).

> **Equi vs. iso.** TAPL discusses two treatments: *equi-recursive* (μX.T
> is definitionally equal to its unfolding) and *iso-recursive* (they are
> merely isomorphic, with explicit `fold`/`unfold` witnesses). We formalize
> the iso-recursive system, which is the one with straightforward syntactic
> metatheory (and the one real languages like ML and Rust implement via
> datatype constructors).

## Types, with their own binder

```lean
inductive Ty : Type where
  | var (n : Nat)           -- type variable (de Bruijn)
  | bool
  | arrow (T₁ T₂ : Ty)      -- T₁ ⇒ T₂
  | mu (T : Ty)             -- μX.T   (binds type-variable 0 of T)

def tshift (d c : Nat) : Ty → Ty          -- shift type variables ≥ c by d
  | var n => if n < c then var n else var (n + d)
  | bool => bool
  | arrow T₁ T₂ => arrow (tshift d c T₁) (tshift d c T₂)
  | mu T => mu (tshift d (c + 1) T)

def tsubst (k : Nat) (S : Ty) : Ty → Ty   -- [k ↦ S]T, substitute-and-decrement
  | var n =>
      if n < k then var n
      else if n = k then tshift k 0 S
      else var (n - 1)
  | bool => bool
  | arrow T₁ T₂ => arrow (tsubst k S T₁) (tsubst k S T₂)
  | mu T => mu (tsubst (k + 1) S T)

def unfoldMu (T : Ty) : Ty := tsubst 0 (mu T) T    -- [X ↦ μX.T] T
```

## Terms, values, evaluation

Terms are λ→ with booleans plus the two coercions `fold T t` / `unfold T t`.
A `fold` of a value is a value; `unfold` cancels `fold`:

```lean
inductive Value : Term → Prop where
  | abs (T : Ty) (t : Term) : Value (abs T t)
  | tru : Value tru
  | fls : Value fls
  | fold (T : Ty) : Value v → Value (fold T v)

-- new evaluation rules
| unfoldFold : Value v → Step (unfold S (fold T v)) v      -- E-UnfldFld
| foldCong   : Step t t' → Step (fold T t) (fold T t')     -- E-Fld
| unfoldCong : Step t t' → Step (unfold T t) (unfold T t') -- E-Unfld
```

## Typing

```lean
| fold   : HasType Γ t (unfoldMu T) →
           HasType Γ (fold (mu T) t) (mu T)                -- T-Fld
| unfold : HasType Γ t (mu T) →
           HasType Γ (unfold (mu T) t) (unfoldMu T)        -- T-Unfld
```

## Metatheory

Weakening and the substitution lemma are as in chapter 9 (the coercions
bind no term variables, so they add only congruence cases); in the
`E-UnfldFld` case of preservation, the typing rules force the `fold` and
`unfold` annotations to agree:

```lean
theorem weakening (h : Γ ⊢ t ∶ T) : ∀ c S, insertAt S c Γ ⊢ shift 1 c t ∶ T
theorem substitution (ht : Δ ⊢ t ∶ T) :
    ∀ Γ k S s, Δ = insertAt S k Γ → (Γ.drop k ⊢ s ∶ S) → Γ ⊢ subst k s t ∶ T

theorem canonical_mu (hv : Value v) (h : [] ⊢ v ∶ .mu T) :
    ∃ v', v = fold (.mu T) v' ∧ Value v'

theorem preservation (h : Γ ⊢ t ∶ T) : ∀ t', (t ⟶ t') → Γ ⊢ t' ∶ T
theorem progress (h : [] ⊢ t ∶ T) : Value t ∨ ∃ t', t ⟶ t'
```

## Example: well-typed divergence (§20.1)

`unfold [D]` turns a `D = μX. X → X` into a `D ⇒ D`, so a term of type `D`
can be applied to itself — chapter 9's `no_self_app` impossibility is
gone, by design:

```lean
def D : Ty := .mu (.arrow (.var 0) (.var 0))

example : Ty.unfoldMu (.arrow (.var 0) (.var 0)) = (D ⇒ D)

def selfApp : Term := abs D (app (unfold D (var 0)) (var 0))
example : [] ⊢ selfApp ∶ (D ⇒ D)

def omegaTyped : Term := app selfApp (fold D selfApp)
theorem omegaTyped_wellTyped : [] ⊢ omegaTyped ∶ D
```

and it runs forever — `Ω` steps back to itself in two steps:

```lean
theorem omegaTyped_loops :
    omegaTyped ⟶ app (unfold D (fold D selfApp)) (fold D selfApp) ∧
    app (unfold D (fold D selfApp)) (fold D selfApp) ⟶ omegaTyped
```

Progress and preservation still hold: type safety means "never stuck",
not "always terminating".
