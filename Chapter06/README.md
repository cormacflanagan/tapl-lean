# Chapter 6 — Nameless Representation of Terms

Chapter 5 already *used* de Bruijn indices; this chapter studies them.
It develops the algebra of the two fundamental operations on nameless
terms — **shifting** and **substitution** — proving the commutation laws
that make de Bruijn representation work, introduces TAPL's notion of an
***n*-term** (definition 6.1.2), and shows that reduction never creates
free variables.

All code lives in [`DeBruijn.lean`](DeBruijn.lean), which imports the
definitions of chapter 5:

```lean
def shift (d c : Nat) : Term → Term          -- add d to variables ≥ c
  | var n => if n < c then var n else var (n + d)
  | abs t => abs (shift d (c + 1) t)
  | app t₁ t₂ => app (shift d c t₁) (shift d c t₂)

def subst (k : Nat) (s : Term) : Term → Term -- [k ↦ s]t, decrementing above k
  | var n =>
      if n < k then var n
      else if n = k then shift k 0 s
      else var (n - 1)
  | abs t => abs (subst (k + 1) s t)
  | app t₁ t₂ => app (subst k s t₁) (subst k s t₂)
```

> **What is not here.** TAPL §6.1 defines `removenames`/`restorenames`,
> translating between named and nameless syntax relative to a naming
> context Γ. Since this development never introduces named syntax, those
> functions have no counterpart; the naming context survives only as the
> *bound* `n` in the `n`-term predicate `Closed n` below.

## Shifting laws

```lean
-- shifting by zero is the identity
theorem shift_zero (t : Term) : ∀ c, shift 0 c t = t

-- two shifts merge into one when the second lands in the gap made by the first
theorem shift_merge (t : Term) :
    ∀ d d' c c', c ≤ c' → c' ≤ c + d' →
      shift d c' (shift d' c t) = shift (d + d') c t

-- shifts at independent cutoffs commute
theorem shift_comm (t : Term) :
    ∀ d d' c c', c' ≤ c →
      shift d' c' (shift d c t) = shift d (c + d') (shift d' c' t)
```

## Substitution laws

The four laws below are the entire "arithmetic" one ever needs about
substitution; every metatheoretic proof about de Bruijn calculi (e.g. the
substitution cases of the preservation proofs in chapters 9–23) reduces to
them. They correspond to TAPL exercise 6.2.8, adapted to the fused
substitution operation.

```lean
-- substituting for a variable just created by a shift cancels one unit of it
theorem subst_shift_cancel (t : Term) :
    ∀ s k d c, c ≤ k → k < c + d + 1 →
      subst k s (shift (d + 1) c t) = shift d c t

-- shifting distributes over substitution
theorem shift_subst_dist (t : Term) :
    ∀ s d c k,
      shift d (c + k) (subst k s t) =
        subst k (shift d c s) (shift d (c + k + 1) t)

-- substitution passes under a shift with a lower cutoff
theorem subst_shift_dist (t : Term) :
    ∀ s d c k, c + d ≤ k →
      subst k s (shift d c t) = shift d c (subst (k - d) s t)

-- the substitution lemma: two substitutions commute
theorem subst_subst (t : Term) :
    ∀ s u j k, j ≤ k →
      subst k s (subst j u t) =
        subst j (subst (k - j) s u) (subst (k + 1) s t)
```

## *n*-terms and closedness

TAPL definition 6.1.2: an *n-term* is a term all of whose free variables
are drawn from `{0, …, n−1}`. A *0-term* is closed:

```lean
def Closed (n : Nat) : Term → Prop
  | var m => m < n
  | abs t => Closed (n + 1) t
  | app t₁ t₂ => Closed n t₁ ∧ Closed n t₂
```

How shifting and substitution interact with the free-variable bound:

```lean
-- shifting above every free variable does nothing
theorem shift_closed_id (t : Term) : ∀ d c, Closed c t → shift d c t = t

-- shifting an n-term by d yields an (n+d)-term
theorem Closed.shift (t : Term) :
    ∀ n d c, Closed n t → Closed (n + d) (shift d c t)

-- substituting for an absent variable does nothing
theorem subst_closed_id (t : Term) : ∀ s k, Closed k t → subst k s t = t

-- substitution consumes one free variable
theorem Closed.subst (t : Term) :
    ∀ s n k, Closed n s → Closed (n + k + 1) t →
      Closed (n + k) (subst k s t)
```

## Reduction preserves closedness

Free variables never appear out of nowhere during reduction — in
particular, evaluating a closed program only ever produces closed terms:

```lean
theorem FullBeta.closed (h : t ⟶β t') : ∀ n, Closed n t → Closed n t'
theorem Step.closed (h : t ⟶ t') (hc : Closed n t) : Closed n t'
```

## Examples

TAPL exercise 6.2.2 (shifting), computed by `decide`:

```lean
example : shift 2 0 (ƛ ƛ #1 ⬝ (#0 ⬝ #2)) = ƛ ƛ #1 ⬝ (#0 ⬝ #4)
example : shift 2 0 (ƛ #0 ⬝ #1 ⬝ (ƛ #0 ⬝ #1 ⬝ #2)) = ƛ #0 ⬝ #3 ⬝ (ƛ #0 ⬝ #1 ⬝ #4)
```

Substitution shifts the substituted term as it moves under binders, and
`ω` is closed:

```lean
example : subst 0 (#1) (#0 ⬝ (ƛ ƛ #2)) = #1 ⬝ (ƛ ƛ #3)
example : Closed 0 omega
```
