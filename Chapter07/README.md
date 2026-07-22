# Chapter 7 — An ML Implementation of the Lambda-Calculus

TAPL chapter 7 turns the call-by-value semantics of chapter 5 into an OCaml
program. Our "ML implementation" is a Lean function — with one important
upgrade over OCaml: the evaluator comes with machine-checked proofs that it
computes **exactly** the evaluation relation of chapter 5.

All code lives in [`Eval.lean`](Eval.lean), building on chapters 5 and 6.

## The value test

```lean
def isValue : Term → Bool
  | abs _ => true
  | _ => false

theorem isValue_iff : isValue t = true ↔ Value t
theorem isValue_false_of_step (h : t ⟶ t') : isValue t = false
```

## Single-step evaluation as a function

TAPL's `eval1` raises `NoRuleApplies`; ours returns `Option`:

```lean
def eval1 : Term → Option Term
  | app (abs t) t₂ =>
      if isValue t₂ then some (subst 0 t₂ t)        -- E-AppAbs
      else (eval1 t₂).map (app (abs t))             -- E-App2
  | app t₁ t₂ => (eval1 t₁).map (fun t₁' => app t₁' t₂)  -- E-App1
  | _ => none
```

The function agrees with the relation `⟶` in both directions, so `none`
answers characterize normal forms exactly:

```lean
theorem eval1_sound (h : eval1 t = some t') : t ⟶ t'
theorem eval1_complete (h : t ⟶ t') : eval1 t = some t'

def NormalForm (t : Term) : Prop := ¬ ∃ t', t ⟶ t'

theorem eval1_none_iff : eval1 t = none ↔ NormalForm t
```

## Progress, untyped version

When can the evaluator get stuck? Never on a closed term, until it reaches
a value — the untyped shadow of chapter 8's progress theorem:

```lean
theorem progress (hc : Closed 0 t) : Value t ∨ ∃ t', t ⟶ t'
theorem closed_normal_value (hc : Closed 0 t) (hn : NormalForm t) : Value t
```

## The evaluation loop

TAPL's `eval` iterates `eval1` until no rule applies; since Lean functions
are total, the loop is bounded by fuel (`some u` = normal form `u` reached):

```lean
def eval (fuel : Nat) (t : Term) : Option Term :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match eval1 t with
      | none => some t
      | some t' => eval fuel t'

theorem eval_sound (h : eval fuel t = some u) : (t ⟶* u) ∧ NormalForm u
theorem eval_closed_value (hc : Closed 0 t) (h : eval fuel t = some u) : Value u
```

## Examples

The evaluator actually runs inside the kernel (`by decide`):

```lean
example : eval1 (id' ⬝ id') = some id'
example : eval 10 (id' ⬝ (id' ⬝ id')) = some id'
example : eval 100 (not' ⬝ (and' ⬝ tru ⬝ (not' ⬝ fls))) = some fls
example : eval 100 (fst' ⬝ (pair ⬝ tru ⬝ fls)) = some tru
example : eval 100 omega = none        -- fuel runs out: divergence
example : eval1 (#0) = none ∧ ¬ Value (#0)   -- an open term is stuck
```
