# Chapter 8 — Typed Arithmetic Expressions

The first type system of the book, over the arithmetic language of
[chapter 3](../Chapter03/): two types, a typing relation, and the two
theorems whose pattern recurs throughout the rest of TAPL — **progress**
and **preservation** — combined into **type safety**: *well-typed programs
never get stuck*.

All code lives in [`TypedArith.lean`](TypedArith.lean), importing the
terms and semantics of chapter 3.

## Types and the typing relation

```lean
inductive Ty : Type where
  | bool
  | nat
```

The typing relation `t ∶ T` (TAPL figures 8-1 and 8-2 — the language has
no variables yet, so there is no context):

```lean
inductive HasType : Term → Ty → Prop where
  | tru    : HasType tru .bool                                    -- T-True
  | fls    : HasType fls .bool                                    -- T-False
  | ite    : HasType t₁ .bool → HasType t₂ T → HasType t₃ T →
             HasType (ite t₁ t₂ t₃) T                             -- T-If
  | zero   : HasType zero .nat                                    -- T-Zero
  | succ   : HasType t .nat → HasType (succ t) .nat               -- T-Succ
  | pred   : HasType t .nat → HasType (pred t) .nat               -- T-Pred
  | iszero : HasType t .nat → HasType (iszero t) .bool            -- T-IsZero

infix:40 " ∶ " => HasType
```

## Inversion and uniqueness

Each syntactic form is typed by exactly one rule, so typing derivations
can be inverted (TAPL lemma 8.2.2 — two sample clauses; the rest are just
as immediate by `cases`), and types are unique (theorem 8.2.4):

```lean
theorem inversion_succ (h : succ t ∶ R) : R = .nat ∧ t ∶ .nat
theorem inversion_ite (h : ite t₁ t₂ t₃ ∶ R) : t₁ ∶ .bool ∧ t₂ ∶ R ∧ t₃ ∶ R

theorem HasType.unique (h₁ : t ∶ T₁) (h₂ : t ∶ T₂) : T₁ = T₂
```

## Canonical forms (lemma 8.3.1)

What do *values* of each type look like? These little lemmas drive the
interesting cases of progress:

```lean
theorem canonical_bool (hv : Value v) (ht : v ∶ .bool) : v = tru ∨ v = fls
theorem canonical_nat (hv : Value v) (ht : v ∶ .nat) : NValue v
```

## Progress and preservation

```lean
-- Theorem 8.3.2: a well-typed term is a value or can take a step
theorem progress (h : t ∶ T) : Value t ∨ ∃ t', t ⟶ t'

-- Theorem 8.3.3: evaluation preserves types
theorem preservation (h : t ∶ T) (hs : t ⟶ t') : t' ∶ T
```

Progress is proved by induction on the typing derivation, using canonical
forms when a subterm is a value; preservation by induction on the
evaluation step, inverting the typing derivation in each case.

## Type safety

Chaining preservation along a multi-step reduction and applying progress
at the end shows that no stuck term (chapter 3's `Stuck`: a normal form
that is not a value) is ever reachable from a well-typed term:

```lean
theorem preservation_multi (h : t ∶ T) (hs : t ⟶* t') : t' ∶ T

theorem safety (h : t ∶ T) (hs : t ⟶* t') : ¬ Stuck t'
```

## Examples

```lean
-- a typing derivation
example : ite (iszero zero) zero (succ zero) ∶ .nat

-- chapter 3's stuck term is exactly what the type system rejects
example (T : Ty) : ¬ (succ tru ∶ T)

-- conservativity: both branches must agree, even under a constant guard
example (T : Ty) : ¬ (ite tru zero fls ∶ T)
```

The last example shows the type system is *conservative*: it rejects some
terms that would in fact evaluate safely — the price of a decidable static
analysis.
