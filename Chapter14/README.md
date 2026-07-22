# Chapter 14 — Exceptions

λ→ with booleans, extended with **runtime errors** and **handlers**
(TAPL figures 14-1 and 14-2): a constant `error` that aborts the
computation by propagating through every evaluation context, and
`try t₁ with t₂`, which runs `t₂` if `t₁` aborts.

All code lives in [`Exceptions.lean`](Exceptions.lean).

> **Exceptions with values.** TAPL §14.3 refines `error` to `raise t`,
> carrying a payload of a fixed exception type `T_exn` (a variant type in
> full generality); the handler then binds the payload. The evaluation and
> typing rules are the evident refinements and add no new proof ideas, so
> this formalization sticks to figures 14-1/14-2.

## Syntax, values, evaluation

```lean
inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | tru
  | fls
  | ite (t₁ t₂ t₃ : Term)
  | error                   -- aborted computation
  | tryE (t₁ t₂ : Term)     -- try t₁ with t₂   (t₂ = alternative, no binder)
```

`error` is **not** a value — values are the results of successful
computations. Instead, `error` propagates out of every evaluation
position, and `try` stops it:

```lean
| appErr1 : Step (app error t₂) error              -- E-AppErr1
| appErr2 : Value v → Step (app v error) error     -- E-AppErr2
| ifErr   : Step (ite error t₂ t₃) error           -- error in the guard
| tryV    : Value v → Step (tryE v t₂) v           -- E-TryV
| tryErr  : Step (tryE error t₂) t₂                -- E-TryError
| tryCong : Step t₁ t₁' → Step (tryE t₁ t₂) (tryE t₁' t₂)  -- E-Try
```

## Typing

```lean
| error : HasType Γ error T                                -- T-Error
| tryE  : HasType Γ t₁ T → HasType Γ t₂ T →
          HasType Γ (tryE t₁ t₂) T                         -- T-Try
```

`T-Error` gives `error` **every** type, so it can occur in any position;
the deliberate price is uniqueness of types:

```lean
example (T : Ty) : [] ⊢ error ∶ T
example : ([] ⊢ error ∶ .bool) ∧ ([] ⊢ error ∶ .bool ⇒ .bool)
```

## Metatheory

Weakening and the substitution lemma are as in chapter 9 (`error`/`tryE`
add only trivial cases). Preservation is unchanged in shape; **progress
changes shape** — an aborted computation is a third legitimate outcome:

```lean
theorem preservation (h : Γ ⊢ t ∶ T) : ∀ t', (t ⟶ t') → Γ ⊢ t' ∶ T

-- Theorem 14.1.2 (extended with try):
theorem progress (h : [] ⊢ t ∶ T) :
    Value t ∨ t = error ∨ ∃ t', t ⟶ t'
```

The canonical-forms lemmas survive `T-Error` untouched, because `error`
is not a value.

## Examples

```lean
def notTerm : Term := abs .bool (ite (var 0) fls tru)

example : app notTerm error ⟶* error                -- errors propagate…
example : tryE (app notTerm error) tru ⟶* tru       -- …until caught
example : tryE (app notTerm fls) fls ⟶* tru         -- normal result: handler dropped
```
