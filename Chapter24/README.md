# Chapter 24 — Existential Types

System F from [chapter 23](../Chapter23/) extended with **existential
types** `{∃X, T}` and their introduction/elimination forms
`{*U, t} as T` (**pack**) and `let {X, x} = t₁ in t₂` (**unpack**) — the
type-theoretic account of *abstract data types*: a package hides a witness
type `U` behind an abstract name `X` (TAPL figure 24-1).

All code lives in [`Existential.lean`](Existential.lean). The whole
two-level de Bruijn infrastructure of chapter 23 carries over (the seven
type-level laws now also cover `exi`); `unpack` is the interesting new
binder, binding a *type* variable and a *term* variable at once.

## Syntax

```lean
inductive Ty : Type where
  | var (n : Nat)
  | arrow (T₁ T₂ : Ty)
  | all (T : Ty)
  | exi (T : Ty)           -- {∃X, T}  (binds type-variable 0 of T)

inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | tabs (t : Term)
  | tapp (t : Term) (T : Ty)
  | pack (U : Ty) (t : Term) (T : Ty)   -- {*U, t} as T
  | unpack (t₁ t₂ : Term)  -- let {X, x} = t₁ in t₂ (binds ty-var 0 and tm-var 0 of t₂)
```

The four shift/substitution operations extend homomorphically; the two
binder-crossing subtleties are in `unpack`:

```lean
-- term substitution crosses BOTH binders of unpack's body:
| unpack t₁ t₂ => unpack (subst k s t₁) (subst (k + 1) (tshiftT 1 0 s) t₂)

-- type substitution in a term crosses its type binder:
| unpack t₁ t₂ => unpack (tsubstT k S t₁) (tsubstT (k + 1) S t₂)
```

## Evaluation

A `pack` of a value is a value. Unpacking a package substitutes the hidden
witness type and the packed value into the body:

```lean
| pack (U T : Ty) : Value v → Value (pack U v T)

| unpackPack : Value v →
    Step (unpack (pack U v T) t₂) (subst 0 v (tsubstT 0 U t₂))  -- E-UnpackPack
| packCong   : Step t t' → Step (pack U t T) (pack U t' T)      -- E-Pack
| unpackCong : Step t₁ t₁' → Step (unpack t₁ t₂) (unpack t₁' t₂) -- E-Unpack
```

## Typing

```lean
| pack : HasType Γ t (tsubst 0 U T₂) →
         HasType Γ (pack U t (.exi T₂)) (.exi T₂)               -- T-Pack

| unpack : HasType Γ t₁ (.exi T₁₂) →
           HasType (T₁₂ :: Γ.map (tshift 1 0)) t₂ (tshift 1 0 T₂) →
           HasType Γ (unpack t₁ t₂) T₂                          -- T-Unpack
```

In `T-Unpack` the body is typed under the abstract type binder (context
shifted, bound type on top), and its result type is `tshift 1 0 T₂` — a
type that *cannot mention* the abstract variable. This is the de Bruijn
rendering of the named presentation's side condition "X not free in T₂",
the essence of abstraction: nothing about the witness type escapes.

## Metatheory

The same lemma suite as chapter 23, each extended with `pack`/`unpack`
cases (`unpack` combines the `abs` and `tabs` cases of each proof):

```lean
theorem weakening (h : Γ ⊢ t ∶ T) : ∀ c S, insertAt S c Γ ⊢ shift 1 c t ∶ T
theorem tweakening (h : Γ ⊢ t ∶ T) :
    ∀ c, Γ.map (tshift 1 c) ⊢ tshiftT 1 c t ∶ tshift 1 c T
theorem substitution (ht : Δ ⊢ t ∶ T) :
    ∀ Γ k S s, Δ = insertAt S k Γ → (Γ.drop k ⊢ s ∶ S) → Γ ⊢ subst k s t ∶ T
theorem tsubstitution (ht : Δ ⊢ t ∶ T) :
    ∀ k S, Δ.map (tsubst k S) ⊢ tsubstT k S t ∶ tsubst k S T

theorem canonical_exi (hv : Value v) (h : [] ⊢ v ∶ .exi T) :
    ∃ U v', v = pack U v' (.exi T) ∧ Value v'

theorem preservation (h : Γ ⊢ t ∶ T) : ∀ t', (t ⟶ t') → Γ ⊢ t' ∶ T
theorem progress (h : [] ⊢ t ∶ T) : Value t ∨ ∃ t', t ⟶ t'
```

In the `E-UnpackPack` case of preservation, `tsubstitution` eliminates the
abstract type, the shifted context collapses
(`(Γ.map (tshift 1 0)).map (tsubst 0 S) = Γ`), and `substitution` installs
the packed value — landing exactly on `T-Pack`'s premise.

## Examples

The pure calculus has no records or numbers, so TAPL's counter-ADT example
can't be transliterated directly; the examples show the same mechanisms:

```lean
def p : Term := pack IdTy idF (.exi (.var 0))   -- {*(∀X.X→X), id} as {∃Y, Y}
theorem p_type : [] ⊢ p ∶ .exi (.var 0)

-- a client can use the abstract value only abstractly, e.g. repack it:
def repack : Term := unpack p (pack (.var 0) (var 0) (.exi (.var 0)))
theorem repack_type : [] ⊢ repack ∶ .exi (.var 0)
theorem repack_evals : repack ⟶* p
```
