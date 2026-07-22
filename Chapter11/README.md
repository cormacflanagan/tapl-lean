# Chapter 11 — Simple Extensions

λ→ from [chapter 9](../Chapter09/) extended with the most important of the
chapter's "simple extensions": the **`Unit`** type, **`let`**-bindings,
**pairs** (products), and **sums** — with the full progress/preservation
metatheory redone for the extended language.

All code lives in [`Extensions.lean`](Extensions.lean).

> **Coverage.** TAPL chapter 11 also treats ascription (`t as T`), records
> and variants (the n-ary, labeled forms of pairs and sums), general
> recursion (`fix`), and lists. Records/variants add no new proof ideas
> over pairs/sums (only labeled lookup in place of two projections);
> `fix` and lists appear in TAPL again in later chapters. Derived forms
> like sequencing (`t₁; t₂ ≡ (λx:Unit. t₂) t₁`) and wildcards are
> definable abbreviations.

## Types and terms

```lean
inductive Ty : Type where
  | unit
  | bool
  | arrow (T₁ T₂ : Ty)      -- T₁ ⇒ T₂
  | prod (T₁ T₂ : Ty)       -- T₁ ⊗ T₂
  | sum (T₁ T₂ : Ty)        -- T₁ ⊕ T₂

inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | tru
  | fls
  | ite (t₁ t₂ t₃ : Term)
  | unit
  | letE (t₁ t₂ : Term)          -- let x = t₁ in t₂   (t₂ binds index 0)
  | pair (t₁ t₂ : Term)          -- {t₁, t₂}
  | fst (t : Term)
  | snd (t : Term)
  | inl (T : Ty) (t : Term)      -- inl t as T  (T = full sum type)
  | inr (T : Ty) (t : Term)      -- inr t as T
  | case (t t₁ t₂ : Term)        -- case t of inl x ⇒ t₁ | inr y ⇒ t₂
```

`shift` and `subst` extend chapter 9's homomorphically; `letE` and the two
`case` branches are binders (cutoff `c + 1`), and the same laws
`shift_zero`, `shift_succ` hold.

## Values and evaluation

```lean
inductive Value : Term → Prop where
  | abs (T : Ty) (t : Term) : Value (abs T t)
  | tru : Value tru
  | fls : Value fls
  | unit : Value unit
  | pair : Value v₁ → Value v₂ → Value (pair v₁ v₂)
  | inl (T : Ty) : Value v → Value (inl T v)
  | inr (T : Ty) : Value v → Value (inr T v)
```

New evaluation rules beyond the λ→/boolean core (each with the congruence
rules fixing left-to-right call-by-value order):

```lean
| letV      : Value v → Step (letE v t) (subst 0 v t)              -- E-LetV
| pairBeta1 : Value v₁ → Value v₂ → Step (fst (pair v₁ v₂)) v₁     -- E-PairBeta1
| pairBeta2 : Value v₁ → Value v₂ → Step (snd (pair v₁ v₂)) v₂     -- E-PairBeta2
| caseInl   : Value v → Step (case (inl T v) t₁ t₂) (subst 0 v t₁) -- E-CaseInl
| caseInr   : Value v → Step (case (inr T v) t₁ t₂) (subst 0 v t₂) -- E-CaseInr
```

## Typing

New rules (TAPL figures 11-2, 11-4, 11-5, 11-9):

```lean
| unit : HasType Γ unit .unit                                       -- T-Unit
| letE : HasType Γ t₁ T₁ → HasType (T₁ :: Γ) t₂ T₂ →
         HasType Γ (letE t₁ t₂) T₂                                  -- T-Let
| pair : HasType Γ t₁ T₁ → HasType Γ t₂ T₂ →
         HasType Γ (pair t₁ t₂) (T₁ ⊗ T₂)                           -- T-Pair
| fst  : HasType Γ t (T₁ ⊗ T₂) → HasType Γ (fst t) T₁               -- T-Proj1
| snd  : HasType Γ t (T₁ ⊗ T₂) → HasType Γ (snd t) T₂               -- T-Proj2
| inl  : HasType Γ t T₁ → HasType Γ (inl (T₁ ⊕ T₂) t) (T₁ ⊕ T₂)     -- T-Inl
| inr  : HasType Γ t T₂ → HasType Γ (inr (T₁ ⊕ T₂) t) (T₁ ⊕ T₂)     -- T-Inr
| case : HasType Γ t (T₁ ⊕ T₂) →
         HasType (T₁ :: Γ) t₁ T → HasType (T₂ :: Γ) t₂ T →
         HasType Γ (case t t₁ t₂) T                                 -- T-Case
```

Note the sum annotations: without `inl t as T`, a term `inl v` would have
*every* type `T₁ ⊕ T₂` with matching left side, destroying uniqueness of
types — TAPL §11.9's motivation for the ascription.

## Metatheory

Same statements as chapter 9, extended proofs (weakening and substitution
must now also track the `let` and `case` binders):

```lean
theorem weakening (h : Γ ⊢ t ∶ T) : ∀ c S, insertAt S c Γ ⊢ shift 1 c t ∶ T
theorem substitution :
    (insertAt S k Γ ⊢ t ∶ T) → (Γ.drop k ⊢ s ∶ S) → Γ ⊢ subst k s t ∶ T

theorem preservation (hs : t ⟶ t') : (Γ ⊢ t ∶ T) → Γ ⊢ t' ∶ T
theorem progress (h : [] ⊢ t ∶ T) : Value t ∨ ∃ t', t ⟶ t'
theorem safety (h : [] ⊢ t ∶ T) (hs : t ⟶* t') (hn : NormalForm t') : Value t'
```

## Examples

```lean
def swapTerm : Term := abs (.bool ⊗ .unit) (pair (snd (var 0)) (fst (var 0)))

example : [] ⊢ swapTerm ∶ (.bool ⊗ .unit) ⇒ (.unit ⊗ .bool)
example : app swapTerm (pair tru unit) ⟶* pair unit tru

example : [] ⊢ letE (fst (pair tru unit)) (ite (var 0) unit unit) ∶ .unit

def getOrElse : Term :=            -- Bool ⊕ Unit ⇒ Bool, "Option.getD false"
  abs (.bool ⊕ .unit) (case (var 0) (var 0) fls)

example : [] ⊢ getOrElse ∶ (.bool ⊕ .unit) ⇒ .bool
example : app getOrElse (inl (.bool ⊕ .unit) tru) ⟶* tru
example : app getOrElse (inr (.bool ⊕ .unit) unit) ⟶* fls
```
