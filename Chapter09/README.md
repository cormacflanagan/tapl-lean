# Chapter 9 — Simply Typed Lambda-Calculus

The heart of the book: **λ→**, the simply typed lambda-calculus over the
base type `Bool`, with typing contexts, the typing relation, and the full
metatheory — weakening, the substitution lemma, **preservation**,
**progress**, and uniqueness of types.

All code lives in [`Stlc.lean`](Stlc.lean). The chapter is self-contained:
the syntax differs from chapters 5–7 (abstractions are annotated,
`λx:T. t`, and booleans are built in), so terms, shifting, and substitution
are defined afresh.

## Types and terms

```lean
inductive Ty : Type where
  | bool
  | arrow (T₁ T₂ : Ty)

infixr:60 " ⇒ " => Ty.arrow

inductive Term : Type where
  | var (n : Nat)          -- de Bruijn index
  | abs (T : Ty) (t : Term)  -- λx:T. t
  | app (t₁ t₂ : Term)
  | tru
  | fls
  | ite (t₁ t₂ t₃ : Term)
```

Shifting and substitution extend chapter 5's definitions homomorphically
to the new constructors (`shift d c`, `subst k s`), with the same
arithmetic laws (`shift_zero`, `shift_succ`).

## Evaluation

Call-by-value, as in figure 9-1 (booleans from figure 8-1):

```lean
inductive Value : Term → Prop where
  | abs (T : Ty) (t : Term) : Value (abs T t)
  | tru : Value tru
  | fls : Value fls

inductive Step : Term → Term → Prop where
  | appAbs  : Value v → Step (app (abs T t) v) (subst 0 v t)
  | app1    : Step t₁ t₁' → Step (app t₁ t₂) (app t₁' t₂)
  | app2    : Value v → Step t t' → Step (app v t) (app v t')
  | ifTrue  : Step (ite tru t₂ t₃) t₂
  | ifFalse : Step (ite fls t₂ t₃) t₃
  | ifCong  : Step t₁ t₁' → Step (ite t₁ t₂ t₃) (ite t₁' t₂ t₃)

infix:50 " ⟶ "  => Step
infix:50 " ⟶* " => MultiStep     -- reflexive-transitive closure
```

## Typing

A context is a list of types; de Bruijn variable `n` is looked up at
position `n` (head = innermost binding). This is TAPL figure 9-1:

```lean
abbrev Ctx := List Ty

inductive HasType : Ctx → Term → Ty → Prop where
  | var : Γ.get? n = some T → HasType Γ (var n) T             -- T-Var
  | abs : HasType (T₁ :: Γ) t T₂ →
          HasType Γ (abs T₁ t) (T₁ ⇒ T₂)                       -- T-Abs
  | app : HasType Γ t₁ (T₁ ⇒ T₂) → HasType Γ t₂ T₁ →
          HasType Γ (app t₁ t₂) T₂                             -- T-App
  | tru : HasType Γ tru .bool
  | fls : HasType Γ fls .bool
  | ite : HasType Γ t₁ .bool → HasType Γ t₂ T → HasType Γ t₃ T →
          HasType Γ (ite t₁ t₂ t₃) T

notation:40 Γ " ⊢ " t " ∶ " T => HasType Γ t T

-- Theorem 9.3.3
theorem HasType.unique (h₁ : Γ ⊢ t ∶ T₁) (h₂ : Γ ⊢ t ∶ T₂) : T₁ = T₂
```

## Weakening and the substitution lemma

In de Bruijn style, TAPL's permutation/weakening lemmas (9.3.6, 9.3.7)
become one *shift-typing* lemma about inserting a binding at position `c`
of the context:

```lean
def insertAt (S : Ty) : Nat → Ctx → Ctx      -- insert S at position c
  | 0, Γ => S :: Γ
  | _ + 1, [] => []
  | c + 1, T :: Γ => T :: insertAt S c Γ

theorem weakening (h : Γ ⊢ t ∶ T) :
    ∀ c S, insertAt S c Γ ⊢ shift 1 c t ∶ T

theorem shift0_typing :          -- iterated weakening at the bottom
    k ≤ Γ.length → (Γ.drop k ⊢ s ∶ S) → Γ ⊢ shift k 0 s ∶ S
```

(supported by four lookup laws `get?_insertAt_lt/ge/self/gt` relating
`insertAt` and `List.get?`). The **substitution lemma** (TAPL 9.3.8) then
goes through by induction on the term:

```lean
theorem substitution :
    (insertAt S k Γ ⊢ t ∶ T) → (Γ.drop k ⊢ s ∶ S) →
    Γ ⊢ subst k s t ∶ T
```

## Preservation, progress, safety

```lean
-- Theorem 9.3.9
theorem preservation (hs : t ⟶ t') : (Γ ⊢ t ∶ T) → Γ ⊢ t' ∶ T

-- Theorem 9.3.5
theorem progress (h : [] ⊢ t ∶ T) : Value t ∨ ∃ t', t ⟶ t'

-- safety = progress + preservation
theorem preservation_multi (h : [] ⊢ t ∶ T) (hs : t ⟶* t') : [] ⊢ t' ∶ T
theorem safety (h : [] ⊢ t ∶ T) (hs : t ⟶* t') (hn : NormalForm t') : Value t'
```

## Examples

```lean
def notTerm : Term := abs .bool (ite (var 0) fls tru)   -- λb:Bool. if b then fls else tru

example : [] ⊢ notTerm ∶ .bool ⇒ .bool
example : app notTerm tru ⟶* fls

def composeTerm : Term :=   -- λf.λg.λx. g (f x), at type Bool
  abs (.bool ⇒ .bool) (abs (.bool ⇒ .bool) (abs .bool
    (app (var 1) (app (var 2) (var 0)))))

example : [] ⊢ composeTerm ∶ (.bool ⇒ .bool) ⇒ (.bool ⇒ .bool) ⇒ .bool ⇒ .bool
```

And the punchline of simple typing — self-application (hence `omega`, hence
divergence) is unwritable:

```lean
theorem arrow_ne (T U : Ty) : T ⇒ U ≠ T
theorem no_self_app (T R : Ty) : ¬ ([] ⊢ abs T (app (var 0) (var 0)) ∶ R)
```
