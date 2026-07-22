# Chapter 23 — Universal Types (System F)

Pure **System F** (TAPL figure 23-1): the polymorphic lambda-calculus with
type abstraction `ΛX.t` and type application `t [T]`, with its full
metatheory — the term- *and* type-substitution lemmas, **preservation**,
and **progress**.

All code lives in [`SystemF.lean`](SystemF.lean).

## Two binders, two index spaces

Both terms and types now bind variables, so both carry de Bruijn indices,
in separate name-spaces: term variables count enclosing `λ`s; type
variables count enclosing `Λ`s (in terms) and `∀`s (in types).

```lean
inductive Ty : Type where
  | var (n : Nat)          -- type variable
  | arrow (T₁ T₂ : Ty)     -- T₁ ⇒ T₂
  | all (T : Ty)           -- ∀X.T  (binds type-variable 0 of T)

inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | tabs (t : Term)        -- ΛX.t  (binds type-variable 0 of t)
  | tapp (t : Term) (T : Ty)  -- t [T]
```

Four operations act on this syntax; the key subtlety is that term-level
substitution must *type-shift* the substituted term when crossing a `Λ`:

```lean
def tshift (d c : Nat) : Ty → Ty         -- shift type vars in a type
def tsubst (k : Nat) (S : Ty) : Ty → Ty  -- [k ↦ S]T (substitute-and-decrement)

def shift (d c : Nat) : Term → Term      -- shift term vars in a term
def tshiftT (d c : Nat) : Term → Term    -- shift type vars in a term

def subst (k : Nat) (s : Term) : Term → Term    -- term substitution
  ...
  | tabs t => tabs (subst k (tshiftT 1 0 s) t)  -- ← shift s across the Λ
  ...

def tsubstT (k : Nat) (S : Ty) : Term → Term    -- type substitution in a term
```

The type level satisfies the same seven de Bruijn laws proved for terms in
chapter 6 (`tshift_zero`, `tshift_merge`, `tshift_comm`,
`tsubst_tshift_cancel`, `tshift_tsubst_dist`, `tsubst_tshift_dist`,
`tsubst_tsubst`) — ported verbatim, and doing exactly the same work in the
metatheory below.

## Evaluation

Values are the two abstraction forms; type application β-reduces on `Λ`:

```lean
inductive Value : Term → Prop where
  | abs (T : Ty) (t : Term) : Value (abs T t)
  | tabs (t : Term) : Value (tabs t)

| tappTabs : Step (tapp (tabs t) S) (tsubstT 0 S t)   -- E-TappTabs
| tappCong : Step t t' → Step (tapp t S) (tapp t' S)  -- E-Tapp
```

## Typing

The context is a list of types for term variables. There is no entry for
type variables: crossing a `Λ` instead **shifts the whole context**, which
replaces the named presentation's freshness side-conditions:

```lean
inductive HasType : Ctx → Term → Ty → Prop where
  | var  : Γ.get? n = some T → HasType Γ (var n) T
  | abs  : HasType (T₁ :: Γ) t T₂ → HasType Γ (abs T₁ t) (T₁ ⇒ T₂)
  | app  : HasType Γ t₁ (T₁ ⇒ T₂) → HasType Γ t₂ T₁ → HasType Γ (app t₁ t₂) T₂
  | tabs : HasType (Γ.map (tshift 1 0)) t T →
           HasType Γ (tabs t) (.all T)                     -- T-TAbs
  | tapp : HasType Γ t (.all T) →
           HasType Γ (tapp t S) (tsubst 0 S T)             -- T-TApp
```

## Metatheory

Two weakening lemmas (one per binder kind) and two substitution lemmas:

```lean
theorem weakening (h : Γ ⊢ t ∶ T) :          -- term weakening
    ∀ c S, insertAt S c Γ ⊢ shift 1 c t ∶ T

theorem tweakening (h : Γ ⊢ t ∶ T) :         -- type weakening
    ∀ c, Γ.map (tshift 1 c) ⊢ tshiftT 1 c t ∶ tshift 1 c T

theorem substitution (ht : Δ ⊢ t ∶ T) :      -- term substitution
    ∀ Γ k S s, Δ = insertAt S k Γ → (Γ.drop k ⊢ s ∶ S) →
      Γ ⊢ subst k s t ∶ T

theorem tsubstitution (ht : Δ ⊢ t ∶ T) :     -- type substitution
    ∀ k S, Δ.map (tsubst k S) ⊢ tsubstT k S t ∶ tsubst k S T
```

and then the main theorems (23.5.1, 23.5.2):

```lean
theorem preservation (h : Γ ⊢ t ∶ T) : ∀ t', (t ⟶ t') → Γ ⊢ t' ∶ T
theorem progress (h : [] ⊢ t ∶ T) : Value t ∨ ∃ t', t ⟶ t'
```

(The `E-TappTabs` case of preservation composes `tsubstitution` with the
context collapse `(Γ.map (tshift 1 0)).map (tsubst 0 S) = Γ`.)

## Examples (TAPL §23.4)

```lean
def idF : Term := tabs (abs (.var 0) (var 0))       -- ΛX. λx:X. x
def IdTy : Ty := .all (.var 0 ⇒ .var 0)             -- ∀X. X → X
theorem idF_type : [] ⊢ idF ∶ IdTy

def double : Term :=                                -- ΛX. λf:X→X. λa:X. f (f a)
  tabs (abs (.var 0 ⇒ .var 0) (abs (.var 0) (app (var 1) (app (var 1) (var 0)))))
theorem double_type : [] ⊢ double ∶ .all ((.var 0 ⇒ .var 0) ⇒ .var 0 ⇒ .var 0)

-- instantiation computes with tsubst:
example : [] ⊢ tapp idF IdTy ∶ (IdTy ⇒ IdTy)

-- self-application, impossible in λ→ (chapter 9), is typable here:
example : [] ⊢ app (tapp idF IdTy) idF ∶ IdTy
example : app (tapp idF IdTy) idF ⟶* idF

-- Church booleans, typed:
def CBool : Ty := .all (.var 0 ⇒ .var 0 ⇒ .var 0)
theorem truF_type : [] ⊢ truF ∶ CBool
theorem flsF_type : [] ⊢ flsF ∶ CBool
```
