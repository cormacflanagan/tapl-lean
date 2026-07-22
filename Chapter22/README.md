# Chapter 22 — Type Reconstruction

Typechecking λ→ terms whose annotations may contain **type variables**:
**constraint-based typing** (TAPL figure 22-1) generates a set of
equations between types, and **unification** (figure 22-2 — the
Hindley/Milner/Robinson algorithm) solves them, computing a *principal*
(most general) solution.

All code lives in [`Reconstruction.lean`](Reconstruction.lean).

## Types, substitutions

```lean
inductive Ty : Type where
  | var (n : Nat)          -- type variable Xₙ
  | bool
  | arrow (T₁ T₂ : Ty)

def occurs (n : Nat) : Ty → Bool          -- the occurs check
def subst1 (n : Nat) (S : Ty) : Ty → Ty   -- [n ↦ S]

abbrev Subst := List (Nat × Ty)           -- (n,T) :: σ  is  σ ∘ [n ↦ T]
def applyS : Subst → Ty → Ty

abbrev Constr := Ty × Ty
def Unifies (σ : Subst) (C : List Constr) : Prop :=
  ∀ p ∈ C, applyS σ p.1 = applyS σ p.2
```

## Unification (fig. 22-2)

Written with explicit fuel — which keeps the function kernel-computable
(so the examples run by `decide`) and sidesteps the standard-but-tangential
lexicographic termination argument:

```lean
def unifyF : Nat → List Constr → Option Subst
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, (S, T) :: rest =>
      match S, T with
      | .bool, .bool => unifyF fuel rest
      | .arrow S₁ S₂, .arrow T₁ T₂ =>
          unifyF fuel ((S₁, T₁) :: (S₂, T₂) :: rest)
      | .var n, T =>
          if T = .var n then unifyF fuel rest
          else if occurs n T then none
          else (unifyF fuel (substC n T rest)).map ((n, T) :: ·)
      | S, .var n =>
          if occurs n S then none
          else (unifyF fuel (substC n S rest)).map ((n, S) :: ·)
      | _, _ => none
```

The two theorems, holding for **every successful run** whatever the fuel:

```lean
-- soundness: the answer solves the constraints
theorem unify_sound : unifyF fuel C = some σ → Unifies σ C

-- principality (the heart of TAPL theorem 22.4.5): every unifier
-- factors through the answer — unifyF computes a most general unifier
theorem unify_principal :
    unifyF fuel C = some σ → ∀ τ, Unifies τ C →
      ∃ ρ, ∀ T, applyS τ T = applyS ρ (applyS σ T)
```

The principality proof needs no termination measure: it follows the
algorithm's recursion, with the key step `applyS_subst1_eq` (a unifier of
`Xₙ ≐ T` cannot see the substitution `[n ↦ T]`).

## Constraint generation (fig. 22-1) and reconstruction

`gen` threads a fresh-variable counter through the term (the functional
form of the `CT-…` rules); `reconstruct` composes it with the unifier:

```lean
def gen (Γ : Ctx) : Term → Nat → Option (Ty × List Constr × Nat)
def substTerm (σ : Subst) : Term → Term   -- apply σ to annotations

def reconstruct (fuel : Nat) (t : Term) : Option (Subst × Ty) :=
  match gen [] t 0 with
  | some (T, C, _) => (unifyF fuel C).map (fun σ => (σ, T))
  | none => none
```

with soundness (TAPL theorem 22.3.5's soundness direction), and its
composition with `unify_sound`:

```lean
theorem gen_sound :
    gen Γ t k = some (T, C, k') → ∀ σ, Unifies σ C →
      HasType (Γ.map (applyS σ)) (substTerm σ t) (applyS σ T)

theorem reconstruct_sound :
    reconstruct fuel t = some (σ, T) →
      HasType [] (substTerm σ t) (applyS σ T)
```

> **Not proved here** (see the file header): completeness of `unifyF` on
> unsolvable inputs (a `none` answer might also mean exhausted fuel — the
> closed-form fuel bound is the lexicographic termination argument), and
> the freshness bookkeeping needed for constraint-generation
> *completeness* (every typing of an instance arises from a solution).
> `gen`'s counter only tracks its own fresh variables, so soundness — which
> holds for arbitrary annotations — is the honest statement.

## Examples (running inside the kernel)

```lean
-- λx:X₀. x  — no constraints, principal-shaped type X₀ ⇒ X₀
example : reconstruct 10 (.abs (.var 0) (.var 0)) = some ([], .var 0 ⇒ .var 0)

-- (λx:X₅. x) true — solves X₅ ⇒ X₅ ≐ Bool ⇒ X₀
example : reconstruct 10 (.app (.abs (.var 5) (.var 0)) .tru) =
    some ([(5, .bool), (0, .bool)], .var 0)

-- λx:X₀. if x then false else x — the guard forces X₀ = Bool
example : (reconstruct 10 (.abs (.var 0) (.ite (.var 0) .fls (.var 0)))).map
    (fun p => applyS p.1 p.2) = some (Ty.bool ⇒ Ty.bool)

-- λx:X₀. x x — the occurs check fires: X₀ ≐ X₀ ⇒ X₁ has no finite solution
example : reconstruct 10 (.abs (.var 0) (.app (.var 0) (.var 0))) = none

-- if true then (λx:X₀.x) else true — a clash X₀ ⇒ X₀ ≐ Bool
example : reconstruct 10 (.ite .tru (.abs (.var 0) (.var 0)) .tru) = none
```
