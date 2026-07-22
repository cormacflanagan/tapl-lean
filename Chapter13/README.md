# Chapter 13 — References

λ→ with `Unit`, extended with ML-style **mutable references**: allocation
`ref t`, dereferencing `!t`, and assignment `t₁ := t₂` (TAPL figure 13-1).

Evaluation now acts on *configurations* `(t, μ)` where `μ` is a **store**,
and typing acquires a **store typing** `St`. Preservation takes its famous
chapter-13 shape: the store typing may *grow* during evaluation, so the
theorem existentially quantifies over an extension of `St`.

All code lives in [`References.lean`](References.lean).

## Syntax and stores

```lean
inductive Ty : Type where
  | unit
  | arrow (T₁ T₂ : Ty)
  | ref (T : Ty)

inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | unit
  | loc (l : Nat)           -- store location (runtime only)
  | ref (t : Term)
  | deref (t : Term)        -- !t
  | assign (t₁ t₂ : Term)   -- t₁ := t₂

abbrev Store := List Term   -- loc l refers to position l
```

Values are abstractions, `unit`, and locations.

## Evaluation of configurations

`Step t μ t' μ'` is `(t, μ) ⟶ (t', μ')`. Besides the usual λ→ rules
(threading `μ` through), the store is touched by three rules:

```lean
| refV     : Value v → Step (ref v) μ (loc μ.length) (μ ++ [v])   -- E-RefV
| derefLoc : μ.get? l = some v → Step (deref (loc l)) μ v μ       -- E-DerefLoc
| assign   : Value v → l < μ.length →
             Step (assign (loc l) v) μ unit (μ.set l v)           -- E-Assign
```

## Typing with store typings

```lean
abbrev StoreTy := List Ty

| loc    : St.get? l = some T → HasType Γ St (loc l) (.ref T)     -- T-Loc
| ref    : HasType Γ St t T → HasType Γ St (ref t) (.ref T)       -- T-Ref
| deref  : HasType Γ St t (.ref T) → HasType Γ St (deref t) T     -- T-Deref
| assign : HasType Γ St t₁ (.ref T) → HasType Γ St t₂ T →
           HasType Γ St (assign t₁ t₂) .unit                      -- T-Assign
```

A store realizes a store typing when the sizes agree and every cell holds
a closed term of the assigned type (definition 13.5.1); store typings only
ever grow by appending:

```lean
def StoreWf (St : StoreTy) (μ : Store) : Prop :=
  μ.length = St.length ∧
  ∀ l T, St.get? l = some T → ∃ v, μ.get? l = some v ∧ HasType [] St v T

def Extends (St' St : StoreTy) : Prop := ∃ ext, St' = St ++ ext
```

## Metatheory

Weakening and substitution are chapter 9's, with `St` threaded through.
The chapter-specific lemmas:

```lean
-- Lemma 13.5.4: typing survives store-typing extension
theorem storety_weakening (h : HasType Γ St t T) :
    ∀ St', Extends St' St → HasType Γ St' t T

-- allocation and update preserve store well-typedness
theorem storeWf_extend (hwf : StoreWf St μ) (hv : HasType [] St v T) :
    StoreWf (St ++ [T]) (μ ++ [v])
theorem storeWf_update (hwf : StoreWf St μ) (hget : St.get? l = some T)
    (hv : HasType [] St v T) : StoreWf St (μ.set l v)
```

The main theorems (13.5.3 and 13.5.7) — note the `∃ St'` in preservation:

```lean
theorem preservation (h : HasType [] St t T) :
    ∀ t' μ μ', StoreWf St μ → Step t μ t' μ' →
      ∃ St', Extends St' St ∧ HasType [] St' t' T ∧ StoreWf St' μ'

theorem canonical_ref (hv : Value v) (h : HasType [] St v (.ref T)) :
    ∃ l, v = loc l ∧ St.get? l = some T

theorem progress (h : HasType [] St t T) (hwf : StoreWf St μ) :
    Value t ∨ ∃ t' μ', Step t μ t' μ'
```

## Examples

```lean
example : Step (ref unit) [] (loc 0) [unit]              -- allocation
example : Step (deref (loc 0)) [unit] unit [unit]        -- read
example : Step (assign (loc 0) unit) [unit] unit [unit]  -- write

example : HasType [] [Ty.unit] (deref (loc 0)) .unit
example : HasType [] [] (abs (.ref .unit) (assign (var 0) unit))
    (.ref .unit ⇒ .unit)
example : StoreWf [] []
```
