# Chapter 3 — Untyped Arithmetic Expressions

This chapter formalizes the first real language of TAPL: a tiny untyped language
of **booleans and natural numbers**. Despite its size it is rich enough to
introduce all the central concepts of operational semantics: terms, values,
a small-step evaluation relation, normal forms, stuck terms (the semantic
notion of a runtime error), and the basic metatheory — determinacy of
evaluation, uniqueness of normal forms, and termination.

All code lives in [`Arith.lean`](Arith.lean). Every definition below is shown
in full; theorems are shown as statements only (see the Lean file for the
machine-checked proofs).

## Syntax

Terms are booleans, a conditional, and Peano-style numbers with `succ`,
`pred` and a zero test (TAPL figures 3-1 and 3-2):

```lean
inductive Term : Type where
  | tru                          -- constant true
  | fls                          -- constant false
  | ite (t₁ t₂ t₃ : Term)        -- conditional: if t₁ then t₂ else t₃
  | zero                         -- constant zero
  | succ (t : Term)              -- successor
  | pred (t : Term)              -- predecessor
  | iszero (t : Term)            -- zero test
```

(`true`, `false`, `if` are Lean keywords, hence the spellings `tru`, `fls`,
`ite`.)

## Values

A *value* is a term that is a possible final result of evaluation. Numeric
values are singled out because the evaluation rules for `pred` and `iszero`
need to refer to them:

```lean
inductive NValue : Term → Prop where
  | zero : NValue zero
  | succ {t : Term} : NValue t → NValue (succ t)

inductive Value : Term → Prop where
  | tru : Value tru
  | fls : Value fls
  | num {t : Term} : NValue t → Value t
```

## Small-step evaluation

The one-step evaluation relation `t ⟶ t'`. The first rule in each group is a
*computation* rule; the `…Cong` rules are *congruence* rules that fix the
(call-by-value, leftmost-outermost) evaluation order:

```lean
inductive Step : Term → Term → Prop where
  | ifTrue     : Step (ite tru t₂ t₃) t₂
  | ifFalse    : Step (ite fls t₂ t₃) t₃
  | ifCong     : Step t₁ t₁' → Step (ite t₁ t₂ t₃) (ite t₁' t₂ t₃)
  | succCong   : Step t t' → Step (succ t) (succ t')
  | predZero   : Step (pred zero) zero
  | predSucc   : NValue t → Step (pred (succ t)) t
  | predCong   : Step t t' → Step (pred t) (pred t')
  | iszeroZero : Step (iszero zero) tru
  | iszeroSucc : NValue t → Step (iszero (succ t)) fls
  | iszeroCong : Step t t' → Step (iszero t) (iszero t')

infix:50 " ⟶ " => Step
```

Multi-step evaluation `⟶*` is the reflexive–transitive closure:

```lean
inductive MultiStep : Term → Term → Prop where
  | refl (t : Term) : MultiStep t t
  | head : Step t t' → MultiStep t' t'' → MultiStep t t''

infix:50 " ⟶* " => MultiStep
```

with the expected closure properties:

```lean
theorem MultiStep.single (h : t ⟶ t') : t ⟶* t'
theorem MultiStep.trans (h₁ : t ⟶* t') (h₂ : t' ⟶* t'') : t ⟶* t''
```

## Normal forms and determinacy

A *normal form* is a term that cannot take a step:

```lean
def NormalForm (t : Term) : Prop := ¬ ∃ t', t ⟶ t'
```

The central metatheoretic results of the chapter:

```lean
-- values never step
theorem NValue.not_step (hv : NValue t) : ¬ t ⟶ t'

-- Theorem 3.5.7: every value is a normal form
theorem Value.normalForm (hv : Value t) : NormalForm t

-- Theorem 3.5.4 (determinacy of one-step evaluation)
theorem Step.deterministic (h₁ : t ⟶ t₁) (h₂ : t ⟶ t₂) : t₁ = t₂

-- Corollary 3.5.11 (uniqueness of normal forms)
theorem MultiStep.normalForm_unique
    (h₁ : t ⟶* u₁) (n₁ : NormalForm u₁)
    (h₂ : t ⟶* u₂) (n₂ : NormalForm u₂) : u₁ = u₂
```

## Termination of evaluation

Every step strictly shrinks the term, measured by the number of constructors,
so evaluation always reaches a normal form (Theorem 3.5.12):

```lean
def Term.size : Term → Nat
  | tru | fls | zero => 1
  | ite t₁ t₂ t₃ => t₁.size + t₂.size + t₃.size + 1
  | succ t | pred t | iszero t => t.size + 1

theorem Step.size_lt (h : t ⟶ t') : t'.size < t.size

theorem MultiStep.exists_normalForm (t : Term) :
    ∃ u, (t ⟶* u) ∧ NormalForm u
```

## Stuck terms

The converse of theorem 3.5.7 fails: some normal forms are not values. Such
terms are *stuck* — they model runtime errors. Type systems (starting in
chapter 8) exist precisely to rule these out statically:

```lean
def Stuck (t : Term) : Prop := NormalForm t ∧ ¬ Value t

example : Stuck (succ tru)   -- applying succ to a boolean is a runtime error
```

## Big-step evaluation (exercise 3.5.17)

The chapter's main exercise: define "natural" (big-step) evaluation `t ⇓ v`
and show it agrees with small-step evaluation.

```lean
inductive BigStep : Term → Term → Prop where
  | value      : Value v → BigStep v v
  | iteTrue    : BigStep t₁ tru → BigStep t₂ v → BigStep (ite t₁ t₂ t₃) v
  | iteFalse   : BigStep t₁ fls → BigStep t₃ v → BigStep (ite t₁ t₂ t₃) v
  | succ       : NValue v → BigStep t v → BigStep (succ t) (succ v)
  | predZero   : BigStep t zero → BigStep (pred t) zero
  | predSucc   : NValue v → BigStep t (succ v) → BigStep (pred t) v
  | iszeroZero : BigStep t zero → BigStep (iszero t) tru
  | iszeroSucc : NValue v → BigStep t (succ v) → BigStep (iszero t) fls

infix:50 " ⇓ " => BigStep
```

Key lemmas and the equivalence:

```lean
theorem BigStep.value_right (h : t ⇓ v) : Value v
theorem BigStep.eq_of_value (hv : Value t) (h : t ⇓ v) : v = t
theorem BigStep.toMultiStep (h : t ⇓ v) : t ⟶* v
theorem BigStep.expand (hs : t ⟶ t') (h : t' ⇓ v) : t ⇓ v
theorem MultiStep.toBigStep (h : t ⟶* v) (hv : Value v) : t ⇓ v

-- Exercise 3.5.17: the two semantics agree
theorem bigStep_iff_multiStep (hv : Value v) : t ⇓ v ↔ t ⟶* v
```

## Examples

```lean
example : ite fls fls tru ⟶ tru

example : ite (iszero (pred (succ zero))) zero (succ zero) ⟶* zero

example : pred (succ (pred zero)) ⇓ zero
```
