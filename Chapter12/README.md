# Chapter 12 — Normalization

Every well-typed program of the simply typed lambda-calculus **halts**
(TAPL theorem 12.1.6). This cannot be proved by a plain induction on
typing — the application case needs to know more about the function than
"it halts" — so the chapter introduces the celebrated method of **logical
relations** (Tait's method).

All code lives in [`Normalization.lean`](Normalization.lean). Following
TAPL §12.1 the calculus is λ→ over an uninterpreted base type `A`; we
reuse the *untyped* terms of [chapter 5](../Chapter05/) and the
substitution algebra of [chapter 6](../Chapter06/) (the lambda is
unannotated, so `T-Abs` guesses its domain — harmless, since nothing here
needs uniqueness of types).

## The system

```lean
inductive Ty : Type where
  | base                 -- the uninterpreted base type A
  | arrow (T₁ T₂ : Ty)   -- T₁ ⇒ T₂

inductive HasType : Ctx → Term → Ty → Prop where
  | var : Γ.get? n = some T → HasType Γ (var n) T
  | abs : HasType (T₁ :: Γ) t T₂ → HasType Γ (ƛ t) (T₁ ⇒ T₂)
  | app : HasType Γ t₁ (T₁ ⇒ T₂) → HasType Γ t₂ T₁ → HasType Γ (t₁ ⬝ t₂) T₂
```

The chapter-9 metatheory (weakening, substitution, preservation) is
re-proved for this typing relation, plus two closure facts:

```lean
theorem typed_closed (h : Γ ⊢ t ∶ T) : Closed Γ.length t
theorem closed_typing_any (h : [] ⊢ t ∶ T) : ∀ Γ, Γ ⊢ t ∶ T
```

## The logical relation

```lean
def Halts (t : Term) : Prop := ∃ v, (t ⟶* v) ∧ Value v

def R : Ty → Term → Prop
  | .base, t => ([] ⊢ t ∶ .base) ∧ Halts t
  | .arrow T₁ T₂, t =>
      ([] ⊢ t ∶ T₁ ⇒ T₂) ∧ Halts t ∧ ∀ s, R T₁ s → R T₂ (t ⬝ s)

theorem R.halts (h : R T t) : Halts t
theorem R.typable (h : R T t) : [] ⊢ t ∶ T
```

`R` is preserved by evaluation in **both** directions (TAPL lemma 12.1.4;
the forward direction of `halts_step` uses determinacy of evaluation):

```lean
theorem halts_step (hs : t ⟶ t') : Halts t ↔ Halts t'
theorem R_step (ht : [] ⊢ t ∶ T) (hs : t ⟶ t') : R T t ↔ R T t'
theorem R_multi_fwd (hm : t ⟶* t') : R T t → R T t'
theorem R_multi_bwd (ht : [] ⊢ t ∶ T) (hm : t ⟶* t') : R T t' → R T t
```

## Multi-substitutions and the main lemma

Open terms are handled by closing them with an environment of `R`-good
terms. `msubstK k σ` applies the (closed) entries of `σ` one after another
at index `k`:

```lean
def msubstK (k : Nat) : List Term → Term → Term
  | [], t => t
  | v :: σ, t => msubstK k σ (subst k v t)

def msubst : List Term → Term → Term := msubstK 0

inductive REnv : List Term → Ctx → Prop where
  | nil : REnv [] []
  | cons : R T v → REnv σ Γ → REnv (v :: σ) (T :: Γ)
```

Its calculus (`msubstK_abs`, `msubstK_app`, `msubstK_closed_id`, and the
key commutation `subst_msubstK`, an instance of chapter 6's `subst_subst`)
supports the **main lemma** (TAPL 12.1.5), proved by induction on typing:

```lean
theorem msubst_typing : (Γ ⊢ t ∶ T) → REnv σ Γ → [] ⊢ msubst σ t ∶ T

theorem main_lemma (h : Γ ⊢ t ∶ T) :
    ∀ σ, REnv σ Γ → R T (msubst σ t)
```

In the `abs` case, the argument `s` is first evaluated to a value `v`
(possible because `R T₁ s` includes halting), `R` is transported forward
to `v` and backward along the β-step — exactly where call-by-value and
the two directions of lemma 12.1.4 earn their keep.

## The theorem

```lean
theorem normalization (h : [] ⊢ t ∶ T) : Halts t
```

## Examples

```lean
example : [] ⊢ (ƛ #0) ∶ .base ⇒ .base
example : [] ⊢ tru ∶ .base ⇒ .base ⇒ .base    -- chapter 5's Church true
example : Halts ((ƛ #0) ⬝ (ƛ #0))

-- contrapositive: the divergent omega cannot be well typed at any type
theorem omega_not_typable (T : Ty) : ¬ ([] ⊢ Chapter05.omega ∶ T)
```
