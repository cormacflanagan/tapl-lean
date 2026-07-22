# Chapter 10 — An ML Implementation of Simple Types

TAPL chapter 10 implements a typechecker for λ→ in OCaml. Ours is the Lean
function `typeof` in [`TypeCheck.lean`](TypeCheck.lean) — verified sound
and complete against chapter 9's typing relation, which makes it a
**decision procedure** for typability of λ→.

## The typechecker

`Option` plays the role of the OCaml version's type-error exceptions:

```lean
def typeof (Γ : Ctx) : Term → Option Ty
  | .var n => Γ.get? n
  | .abs T t => (typeof (T :: Γ) t).map (T ⇒ ·)
  | .app t₁ t₂ =>
      match typeof Γ t₁, typeof Γ t₂ with
      | some (.arrow T₁ T₂), some T₁' => if T₁ = T₁' then some T₂ else none
      | _, _ => none
  | .tru => some .bool
  | .fls => some .bool
  | .ite t₁ t₂ t₃ =>
      match typeof Γ t₁, typeof Γ t₂, typeof Γ t₃ with
      | some .bool, some T₂, some T₃ => if T₂ = T₃ then some T₂ else none
      | _, _, _ => none
```

## Correctness

```lean
theorem typeof_complete (h : Γ ⊢ t ∶ T) : typeof Γ t = some T
theorem typeof_sound (h : typeof Γ t = some T) : Γ ⊢ t ∶ T

theorem typeof_correct : typeof Γ t = some T ↔ (Γ ⊢ t ∶ T)
theorem typable_iff : (∃ T, Γ ⊢ t ∶ T) ↔ (typeof Γ t).isSome
```

Completeness is a one-line-per-case induction on the typing derivation
(the algorithm is syntax-directed); soundness follows the structure of the
`match` in each defining equation.

Together with uniqueness of types (theorem 9.3.3), `typeof` computes *the*
type of a term whenever one exists.

## Examples

The typechecker runs inside the kernel (`by decide`):

```lean
example : typeof [] notTerm = some (.bool ⇒ .bool)
example : typeof [] composeTerm =
    some ((.bool ⇒ .bool) ⇒ (.bool ⇒ .bool) ⇒ .bool ⇒ .bool)

-- rejections
example : typeof [] (.abs .bool (.app (.var 0) (.var 0))) = none  -- self-app
example : typeof [] (.app notTerm (.abs .bool (.var 0))) = none   -- arg mismatch
example : typeof [] (.ite .tru .tru notTerm) = none               -- branch mismatch

-- open terms typecheck under a context (de Bruijn: position 0 is innermost)
example : typeof [.bool ⇒ .bool, .bool] (.app (.var 0) (.var 1)) = some .bool
example : typeof [.bool ⇒ .bool, .bool] (.app (.var 1) (.var 0)) = none
```
