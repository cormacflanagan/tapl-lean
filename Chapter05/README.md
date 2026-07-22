# Chapter 5 — The Untyped Lambda-Calculus

This chapter formalizes the pure untyped lambda-calculus: its syntax, the
call-by-value operational semantics of TAPL figure 5-3, full β-reduction,
and the classic **Church encodings** of booleans, pairs, and numerals —
with the encoded programs actually *run* inside Lean by an executable,
verified normalizer.

> **A note on names.** TAPL chapter 5 uses named variables (`λx. x y`) and
> defines substitution up to α-conversion; the nameless *de Bruijn*
> representation only appears in chapter 6. Mechanized metatheory is far
> easier with de Bruijn indices, so this formalization adopts them from the
> start: `var n` refers to the `n`-th enclosing binder. Chapter 6 then
> studies the shifting/substitution operations in their own right.

All code lives in [`Lambda.lean`](Lambda.lean).

## Syntax

```lean
inductive Term : Type where
  | var (n : Nat)         -- de Bruijn index
  | abs (t : Term)        -- λ-abstraction (binds index 0 of its body)
  | app (t₁ t₂ : Term)    -- application

prefix:max "#"  => Term.var    -- #n
prefix:65  "ƛ " => Term.abs    -- ƛ t
infixl:70  " ⬝ " => Term.app   -- t ⬝ s
```

So the named term `λx. λy. x y` is written `ƛ ƛ #1 ⬝ #0`.

## Shifting and substitution

β-reduction needs *shifting* (renumbering free variables when a term is
moved under a binder) and *substitution*. `subst k s t` fuses TAPL's
`↑⁻¹([0 ↦ ↑¹s] t)` into one traversal: it replaces variable `k` by `s`
(shifted into place) and decrements the variables above `k`:

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

## Call-by-value evaluation (TAPL figure 5-3)

Values are the λ-abstractions. The three rules evaluate the function
position, then the argument, then perform β on a value argument:

```lean
inductive Value : Term → Prop where
  | abs (t : Term) : Value (ƛ t)

inductive Step : Term → Term → Prop where
  | appAbs : Value v → Step ((ƛ t) ⬝ v) (subst 0 v t)   -- E-AppAbs
  | app1   : Step t₁ t₁' → Step (t₁ ⬝ t₂) (t₁' ⬝ t₂)     -- E-App1
  | app2   : Value v → Step t t' → Step (v ⬝ t) (v ⬝ t') -- E-App2

infix:50 " ⟶ " => Step
```

Multi-step reduction is defined once, generically, as the
reflexive–transitive closure of any relation:

```lean
inductive Multi (R : Term → Term → Prop) : Term → Term → Prop where
  | refl (t : Term) : Multi R t t
  | head : R t t' → Multi R t' t'' → Multi R t t''

infix:50 " ⟶* " => Multi Step

theorem Multi.single (h : R t t') : Multi R t t'
theorem Multi.trans (h₁ : Multi R t t') (h₂ : Multi R t' t'') : Multi R t t''
```

Basic metatheory of the evaluation strategy:

```lean
theorem Value.not_step (hv : Value v) : ¬ v ⟶ t
theorem Step.deterministic (h₁ : t ⟶ t₁) (h₂ : t ⟶ t₂) : t₁ = t₂
```

## Full β-reduction

Full β-reduction (TAPL §5.3) may contract any redex anywhere — including
under binders — and is therefore non-deterministic:

```lean
inductive FullBeta : Term → Term → Prop where
  | beta    : FullBeta ((ƛ t) ⬝ s) (subst 0 s t)
  | absCong : FullBeta t t' → FullBeta (ƛ t) (ƛ t')
  | app1    : FullBeta t₁ t₁' → FullBeta (t₁ ⬝ t₂) (t₁' ⬝ t₂)
  | app2    : FullBeta t₂ t₂' → FullBeta (t₁ ⬝ t₂) (t₁ ⬝ t₂')

infix:50 " ⟶β "  => FullBeta
infix:50 " ⟶β* " => Multi FullBeta

theorem Step.toFullBeta (h : t ⟶ t') : t ⟶β t'
```

## An executable, verified normalizer

To *run* lambda-terms we implement the normal-order (leftmost-outermost)
strategy as a function, plus a fuel-bounded iterator:

```lean
def nreduce : Term → Option Term            -- one normal-order step
  | var _ => none
  | abs t => (nreduce t).map abs
  | app (abs t) s => some (subst 0 s t)
  | app (var n) t₂ => (nreduce t₂).map (app (var n))
  | app (app s₁ s₂) t₂ =>
      match nreduce (app s₁ s₂) with
      | some t₁' => some (app t₁' t₂)
      | none => (nreduce t₂).map (app (app s₁ s₂))

def normalize (fuel : Nat) (t : Term) : Option Term :=
  match fuel with
  | 0 => none
  | fuel + 1 => match nreduce t with
    | none => some t
    | some t' => normalize fuel t'

def BetaNormal (t : Term) : Prop := ¬ ∃ t', t ⟶β t'
```

and prove it correct with respect to the reduction relation:

```lean
theorem nreduce_sound (h : nreduce t = some t') : t ⟶β t'
theorem nreduce_none_normal (h : nreduce t = none) : BetaNormal t
theorem normalize_sound (h : normalize fuel t = some u) :
    (t ⟶β* u) ∧ BetaNormal u
```

## Church encodings (TAPL §5.2)

```lean
def id'  : Term := ƛ #0                       -- λx. x
def tru  : Term := ƛ ƛ #1                     -- λt.λf. t
def fls  : Term := ƛ ƛ #0                     -- λt.λf. f
def test : Term := ƛ ƛ ƛ #2 ⬝ #1 ⬝ #0         -- λl.λm.λn. l m n
def and' : Term := ƛ ƛ #1 ⬝ #0 ⬝ fls          -- λb.λc. b c fls
def or'  : Term := ƛ ƛ #1 ⬝ tru ⬝ #0          -- λb.λc. b tru c
def not' : Term := ƛ #0 ⬝ fls ⬝ tru           -- λb. b fls tru
def pair : Term := ƛ ƛ ƛ #0 ⬝ #2 ⬝ #1         -- λf.λs.λb. b f s
def fst' : Term := ƛ #0 ⬝ tru                 -- λp. p tru
def snd' : Term := ƛ #0 ⬝ fls                 -- λp. p fls

def church (n : Nat) : Term :=                -- λs.λz. sⁿ z
  ƛ ƛ go n
where go : Nat → Term
  | 0 => #0
  | n + 1 => #1 ⬝ go n

def scc   : Term := ƛ ƛ ƛ #1 ⬝ (#2 ⬝ #1 ⬝ #0)      -- λn.λs.λz. s (n s z)
def plus  : Term := ƛ ƛ ƛ ƛ #3 ⬝ #1 ⬝ (#2 ⬝ #1 ⬝ #0) -- λm.λn.λs.λz. m s (n s z)
def times : Term := ƛ ƛ #1 ⬝ (plus ⬝ #0) ⬝ church 0 -- λm.λn. m (plus n) c₀
def iszro : Term := ƛ #0 ⬝ (ƛ fls) ⬝ tru           -- λm. m (λx. fls) tru
def omega : Term := (ƛ #0 ⬝ #0) ⬝ (ƛ #0 ⬝ #0)      -- (λx. x x)(λx. x x)
```

## Examples

Hand-written call-by-value reduction sequences:

```lean
example : id' ⬝ (id' ⬝ id') ⟶* id'
example : and' ⬝ tru ⬝ fls ⟶* fls
example : omega ⟶ omega          -- omega steps to itself: divergence
```

Church arithmetic verified by *running* the normalizer inside the kernel
(`normalize_sound` connects each of these to a genuine `⟶β*` derivation):

```lean
example : normalize 100 (scc ⬝ church 0) = some (church 1)
example : normalize 100 (plus ⬝ church 1 ⬝ church 1) = some (church 2)
example : normalize 100 (times ⬝ church 2 ⬝ church 3) = some (church 6)
example : normalize 100 (not' ⬝ (and' ⬝ tru ⬝ (not' ⬝ fls))) = some fls
example : normalize 100 (iszro ⬝ church 0) = some tru
example : normalize 100 (fst' ⬝ (pair ⬝ tru ⬝ fls)) = some tru
example : normalize 100 omega = none   -- no normal form: fuel runs out
```
