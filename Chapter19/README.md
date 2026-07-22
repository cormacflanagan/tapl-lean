# Chapter 19 — Featherweight Java

**Featherweight Java (FJ)**: the minimal core of Java — classes with
fields, inheritance, methods, object creation, and casts — small enough
for a complete metatheory (TAPL figures 19-1 … 19-4).

All code lives in [`FJ.lean`](FJ.lean). FJ differs pleasantly from the
lambda-calculi elsewhere in this repo: terms contain **no binders**
(method parameters are bound only at the method-table level), so
substitution is plain simultaneous replacement of named variables, with no
capture or shifting. The price is elsewhere: constructors and methods are
n-ary, so terms are a **mutual inductive** with argument lists, and every
function and proof over them is mutual too.

## Syntax and the class table

```lean
mutual
inductive Term : Type where
  | var (x : Name)                              -- x
  | fld (t : Term) (f : Name)                   -- t.f
  | invk (t : Term) (m : Name) (ts : TermList)  -- t.m(t̄)
  | new (C : Name) (ts : TermList)              -- new C(t̄)
  | cast (C : Name) (t : Term)                  -- (C) t
inductive TermList : Type where
  | nil
  | cons (t : Term) (ts : TermList)
end

structure MethodDef (Term : Type) where        -- B m(B̄ x̄) { return body; }
  name : Name
  params : List (Name × Name)
  ret : Name
  body : Term

structure ClassDef where                        -- class C extends D {…}
  superclass : Name
  fields : List (Name × Name)
  methods : List (MethodDef Term)

abbrev ClassTable := List (Name × ClassDef)
```

Substitution is capture-free by construction:

```lean
def substT (σ : List (Name × Term)) : Term → Term    -- and substL, mutually
```

## Subtyping and the inheritance-walking relations

`fields`, `mtype`, `mbody` are **inductive relations** (so no
well-foundedness conditions on the class table are needed to define them):

```lean
inductive Sub : Name → Name → Prop            -- refl, trans, extends edges
inductive HasFields : Name → List (Name × Name) → Prop  -- fields(C), super first
inductive MType : Name → Name → List Name → Name → Prop -- mtype(m, C) = B̄ → B
inductive MBody : Name → Name → List Name → Term → Prop -- mbody(m, C) = (x̄, t)
```

## Evaluation and typing

Call-by-value order (receiver, then arguments left to right); the three
computation rules (TAPL fig. 19-3):

```lean
| projNew : HasFields CT C fs → lookupIdx fs f = some (i, Ci) →
    args.toList.get? i = some v → isValueL args = true →
    Step (.fld (.new C args) f) v                          -- E-ProjNew
| invkNew : MBody CT m C xs body → isValueL vs → isValueL us →
    Step (.invk (.new C vs) m us)
      (substT (("this", .new C vs) :: List.zip xs us.toList) body)
| castNew : Sub CT C D → isValueL vs →
    Step (.cast D (.new C vs)) (.new C vs)                 -- E-CastNew
```

Typing (fig. 19-4) is syntax-directed; subtyping enters only at argument
positions (`ArgsTyped`). The three cast rules (`T-UCast`/`T-DCast`/
`T-SCast`) are **merged into one liberal rule** `cast : HasType Γ t D →
HasType Γ (cast C t) C` — TAPL splits them only to flag "stupid" casts,
and the merged system satisfies the same preservation theorem.

## Well-formed class tables

The semantic content of TAPL's `CT OK` judgment, as the metatheory needs
it, is bundled as a record and assumed where required:

```lean
structure CTOk : Prop where
  obj_none : CT.lookup "Object" = none
  mtype_sub : Sub CT C D → MType CT m D Bs B → MType CT m C Bs B  -- overrides
  method_typing : MBody CT m C xs body → MType CT m C Bs B →
    ∃ C₀ E, Sub CT C C₀ ∧
      HasType CT (("this", C₀) :: List.zip xs Bs) body E ∧ Sub CT E B
```

Everything else TAPL derives from `CT OK` is **proved** here:
`fields_det` (determinism), `fields_sub` (a subclass's fields extend its
superclass's, positions preserved), `mbody_mtype_length`, `mtype_mbody`.

## Metatheory

```lean
-- weakening and the substitution lemma (both mutual over Term/TermList)
theorem weaken_t : HasType CT Δ t C → HasType CT (Δ ++ Γ) t C
theorem subst_t (hok : CTOk CT) :
    HasType CT (Δ ++ Γ) t C → SubstOk CT Γ σ Δ →
    ∃ C', HasType CT Γ (substT σ t) C' ∧ Sub CT C' C

-- Theorem 19.5.1: a step refines the type
theorem preservation (hok : CTOk CT) (hs : Step CT t t')
    (h : HasType CT Γ t C) : ∃ C', HasType CT Γ t' C' ∧ Sub CT C' C

-- Theorem 19.5.2 (cast-free form): failing downcasts are the only stuck states
theorem progress (hok : CTOk CT) (h : HasType CT [] t C)
    (hcf : castFreeT t = true) : isValueT t = true ∨ ∃ t', Step CT t t'
```

Note the `∃ C', … ∧ C' <: C` in both the substitution lemma and
preservation: in FJ, evaluation can *refine* types (a method can return a
subclass of its declared type) — this is where `fields_sub` and the
override condition earn their keep.

## Example: the `Pair` class (TAPL §19.1)

```java
class A extends Object {}
class B extends Object {}
class Pair extends Object {
  Object fst; Object snd;
  Pair setfst(Object newfst) { return new Pair(newfst, this.snd); }
}
```

encoded as a concrete `exCT : ClassTable`, with machine-checked
derivations:

```lean
theorem fieldsPair : HasFields exCT "Pair" [("fst","Object"), ("snd","Object")]
theorem subA : Sub exCT "A" "Object"
theorem tyNewPair : HasType exCT [] newPair "Pair"
theorem mtySetfst : MType exCT "setfst" "Pair" ["Object"] "Pair"

example : Step exCT (.fld newPair "snd") newB              -- projection runs
example : HasType exCT [] (.invk newPair "setfst" (.cons newB .nil)) "Pair"
example : ∃ t', Step exCT (.invk newPair "setfst" (.cons newB .nil)) t'
example : Step exCT (.cast "Object" newA) newA             -- upcast runs
example : HasType exCT [] (.cast "B" newA) "B"             -- downcast typechecks…
-- …but (B)(new A()) is stuck: FJ's model of a ClassCastException.
```
