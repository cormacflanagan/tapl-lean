# MoverRust — mover logic for a multithreaded Rust subset, in Lean 4

A Lean formalization of **mover logic** — Flanagan & Freund's concurrent
program logic that combines rely-guarantee reasoning with Lipton's theory
of reduction — applied to a small multithreaded Rust-flavored language.

> Cormac Flanagan and Stephen N. Freund.
> *Mover Logic: A Concurrent Program Logic for Reduction and
> Rely-Guarantee Reasoning.* ECOOP 2024.
> (The extended version is in [`../mover-rust/`](../mover-rust/).)

Mover logic was designed to emit verification conditions for an **SMT
solver**. The experiment here is to emit them as **Lean propositions**
instead: every proof obligation is discharged by the Lean kernel, so the
solver leaves the trusted base entirely. This directory carries that idea
through a complete, machine-checked development: a concurrent operational
semantics, the logic and its soundness theorem, and a worked example
whose `add` procedure is proved to satisfy its specification.

The whole library builds with **zero `sorry`s** and no `native_decide`;
the one component that is *tested rather than proved* is the surface-syntax
parser, for the reason explained under [The parser](#the-parser) below.

## What is mover logic, in one paragraph

In a multithreaded program, a function's behavior can be observed by other
threads at every intermediate step, so rely-guarantee (RG) logic forces
each postcondition to be *stabilized* against interference — which
entangles library specifications with client invariants. Mover logic fixes
this using **reduction**: it classifies each action by how it *commutes*
with steps of other threads — **right-mover** (`R`), **left-mover** (`L`),
**both-mover** (`B`), **non-mover** (`N`) — and checks that the code
between two `yield` points is *reducible*, i.e. its movers match the
pattern `R* [N] L*`. A reducible block behaves as if it ran atomically, so
it can be given a precise, client-independent pre/postcondition, with the
rely assumption applied only at `yield`s.

## The files

| File | Contents |
|---|---|
| [`Effects.lean`](Effects.lean) | the effect lattice `Y ⊑ B ⊑ R,L ⊑ N ⊑ E`, sequential composition, join and closure — **validated against a reducibility DFA** by `decide` |
| [`Lang.lean`](Lang.lean) | the language: stores, expressions, actions (`acquire`/`release`/`cas`/read/write/local), statements, and an interleaving thread-pool semantics |
| [`Logic.lean`](Logic.lean) | mover specifications and their **validity** (Definition 1); the judgment `R;G ⊢ s : P → Q · e`; atomic/non-atomic function specs; verified states |
| [`Instrumented.lean`](Instrumented.lean) | the phase-instrumented semantics (Fig. 10), preemptive and non-preemptive schedulers, and the one-step **Simulation** theorem |
| [`Meta.lean`](Meta.lean) | inversion lemmas for the judgment, and the **Prefix lemma** (atomic bodies splice into any context) |
| [`Preservation.lean`](Preservation.lean) | **Preservation** (Thm 5), *verified-states-are-not-wrong* (Thm 6), and **cooperative soundness** |
| [`Reduction.lean`](Reduction.lean) | multi-step **Simulation** (Thm 3), and the action-level commuting lemmas derived from validity |
| [`Theorem4.lean`](Theorem4.lean) | the **step trichotomy** and the pool-level **commuting lemmas** (Lemmas 7, 8, 10) — the technical core of the Reduction Theorem |
| [`Postcommit.lean`](Postcommit.lean) | **Lemma 9** (Post-Commit Termination): a committed, call-free thread runs to a park (progress + preservation on a structural metric) |
| [`Examples.lean`](Examples.lean) | the counter/lock library: `add` **satisfies its spec**, plus the mover-spec **validity mechanism** |
| [`Parser.lean`](Parser.lean) | a recursive-descent parser from Rust-flavored source to the verified AST |

## The effect algebra (`Effects.lean`)

Reducibility of a code sequence is decided by a three-state DFA
(pre-commit → post-commit → error) that accepts exactly `R* [N] L*`
between yields. Each effect denotes a transition function of that DFA. We
*define* `⊑`, sequential composition `;`, join `⊔` and closure `*` by the
paper's tables and then **prove they agree with the DFA semantics**, so
the tables are not trusted:

```lean
theorem le_iff_run : ∀ a b, le a b = true ↔ ∀ p, (run a p).le (run b p) = true  -- by decide
theorem seq_run    : ∀ a b p, run (seq a b) p = run b (run a p)                 -- by decide
```

## The language (`Lang.lean`)

Shared **stores** map variables — globals `g n` and per-thread locals
`l t n` (the paper's `r_tid` encoding) — to integers. Actions denote
store relations indexed by the acting thread:

```lean
inductive Act
  | lact (r : Nat) (e : Exp)      -- r := e            (locals only)
  | readg (r : Nat) (x : Nat)     -- r := x            (global read)
  | writeg (x : Nat) (e : Exp)    -- x := e            (global write)
  | acquire (m : Nat)             -- blocks until m = 0, then m := t+1
  | release (m : Nat)             -- m := 0
  | casT (x : Nat) (e₁ e₂ : Exp)  -- successful compare-and-set
  | assume (e : Exp) (b : Bool)   -- a pure test
  | idA                           -- no-op (a failing cas)

inductive Stmt
  | skip | wrong | act (A : Act) | seq | ite (C) (s₁ s₂) | wloop (C) (s)
  | call (f : Nat) | yld
```

Execution is a **preemptive interleaving** of a thread pool
`s₁ .. sₙ · σ`; a state is *wrong* if any thread reaches `wrong`
(`assert e` desugars to `if e then skip else wrong`). The goal of the
logic is to prove no reachable state is wrong.

## The logic (`Logic.lean`)

A **mover specification** `M : Act → Tid → Store → Effect` classifies each
action in each store. It is **valid** (Definition 1) when every claim it
makes is true — right-movers commute later, left-movers commute earlier,
and a mover of one thread cannot change or disable another thread's step:

```lean
structure Valid (M : MSpec) : Prop where
  right_commute : … M A₁ t σ ≤ .R → … M A₂ u σ' ≤ .N → … ∃ σ''', …
  left_commute  : … M A₁ t σ ≤ .N → … M A₂ u σ' ≤ .L → … ∃ σ''', …
  stable_eff    : … M A₁ t σ ≤ .N → den A₁ t σ σ' → M A₂ u σ' = M A₂ u σ
  left_enabled  : …
```

The central judgment is the paper's `R;G ⊢ s : P → Q · e`:

```lean
inductive Judg (D : Decls) (M : MSpec) : Rel → Rel → Stmt → Pred → Pred → Effect → Prop
```

with rules `M-skip`, `M-wrong`, `M-action`, `M-seq`, `M-if`, `M-while`,
`M-yield`, `M-call-atomic`, `M-call-non-atomic`, and `M-conseq` — each an
extension of a Hoare rule tracking a reduction effect. `P` and `Q` are
two-store predicates relating the store at the start of the current
reducible sequence (`\old`) to the current store. Function specifications
come in two flavors:

```lean
inductive FnSpec
  | atomicSpec (e : Effect) (S : Pred1) (Q : Pred)   -- reducible, unstabilized post
  | rgSpec (R G : Rel) (S T : Pred1)                 -- may yield; carries its own R, G
```

## Soundness

The soundness argument follows the paper's five-step structure. The
instrumented semantics ([`Instrumented.lean`](Instrumented.lean)) tags
each thread with its DFA **phase** and steps to `wrong` whenever an action
violates the mover spec or breaks reducibility. Two schedulers — the
preemptive `ipstep` and the cooperative `npstep` (which context-switches
only at yields) — share this instrumented step relation.

```lean
-- Theorem 3 (Simulation): the instrumented machine matches the standard
-- one, going wrong at least as often.
theorem sim_multi … :
  (∃ c', Multi (ipstep F M) c c' ∧ SimRel st' c') ∨ IGoesWrong F M c

-- Theorem 5 (Preservation) for the cooperative scheduler
theorem npstep_preserve (hok : IStateOK D M R G c) (h : npstep D.fns M c c') :
  IStateOK D M R G c'

-- Theorem 6: a verified state is never wrong
theorem istateok_not_wrong (hok : IStateOK D M R G c) : ¬ IStateWrong c

-- Cooperative soundness: verified programs do not go wrong under the
-- yield-to-yield scheduler the logic reasons about
theorem cooperative_soundness (hok : IStateOK D M R G c) : ¬ NGoesWrong D.fns M c
```

`Preservation.lean`'s `istep_preserve` is the technical core: preservation
for a single instrumented step, by induction over the step relation with
all statement forms — the mover effect of each action composes onto the
phase and the invariant is re-established, using the **Prefix lemma**
(`Meta.lean`) at atomic calls and yield **stabilization** at yields.

### The Reduction Theorem (Theorem 4): commuting lemmas

The heart of Theorem 4 is that the four validity conditions are exactly
the commutations that let a preemptive trace be rearranged into a
cooperative one. [`Theorem4.lean`](Theorem4.lean) mechanizes these
**commuting lemmas** — Lemmas 7, 8, and 10 of the paper's Appendix B.1 —
at the level of the real pool step relation `ipstep`, all fully proved:

```lean
-- Lemma 7 (Right Commutativity): a right-mover step of thread i (ending
-- in the pre-commit phase R) commutes right past a following step of j.
theorem ipstep_right_comm (hval : Valid M) (hij : i ≠ j)
    (h1 : ipstepAt F M i c c₁) (hiR : … i ends in phase R, non-wrong …)
    (h2 : ipstepAt F M j c₁ c₂) (hj_nw : …) :
    ∃ c₃, ipstepAt F M j c c₃ ∧ ipstepAt F M i c₃ c₂

-- Lemma 8 (Left Commutativity) and Lemma 10 (Diamond) likewise.
theorem ipstep_left_comm …      theorem istep_diamond …
```

They rest on a **step trichotomy** (`istep_char`): every instrumented
step either performs an action (store moving by `den A`, phase by
`p ; M A`, and *reproducible at any store*), steps into `wrong`, or is a
store-independent silent step. The action–action cases invoke the
`Valid` conditions; the silent cases commute because they do not touch
the store.

**Lemma 9 (Post-Commit Termination)** is mechanized in
[`Postcommit.lean`](Postcommit.lean): a committed thread (post-commit
phase `N`), running call-free code, always runs to a park — proved by
progress + preservation on a structural size metric that each step
strictly decreases. Loops cannot appear in post-commit (the [M-while]
rule forbids it), which is what makes the metric bounded.

```lean
theorem post_terminates (hval : Valid M) (hD : DeclsOK D M) :
    ∀ n s, sizeS s ≤ n → ∀ σ P Q e, Judg D M R G s P Q e →
      Effect.N.seq e ≠ .E → CallFree s → P t σ₀ σ →
      ∃ s' σ', Multi (IStepT D.fns M t) (.N, s, σ) (.N, s', σ') ∧ Yielding s'
```

**What remains for the full theorem.**  With Lemmas 7–10 (commutation)
and Lemma 9 (post-commit termination) all mechanized, the paper assembles
Theorem 4 by a global trace induction proving `Π →* Π' ⇒ (Π,Π') ∈
Post*·Pre*` — a bubble-sort of the preemptive trace into cooperative
blocks using the four commutations as swap rules — then discharges the
last incomplete block with Lemma 9. That trace-combinatorial assembly,
which would connect to full preemptive soundness via
`cooperative_soundness`, is the remaining step; every lemma it rests on
is mechanized here.

## The worked example (`Examples.lean`)

The paper's running example: a counter `x` protected by a lock `m`, with
an atomic `add` procedure.

```
atomic  ensures x == \old(x) + arg
add() {
  acquire(m);       // R    right-mover
  r = x;            // B    both-mover (lock held)
  x = r + arg;      // B
  release(m);       // L    left-mover
}                   // R;B;B;L = N  ⇒ one commit ⇒ atomic
```

Two theorems, both discharged by the Lean kernel — the obligations a
reduction verifier would send to an SMT backend:

```lean
-- 1. Code satisfies its spec: add's body is reducible with a single
--    commit (effect N, hence atomic) and establishes x == \old(x) + arg.
theorem addBody_spec (D) :
    Judg D Mex emptyRel emptyRel addBody (Two addPre) addPost .N

theorem addFn_ok (D) : FnOK D Mex (.atomicSpec .N addPre addPost) addBody

-- 2. Mover-spec validity mechanism: lock exclusivity makes conflicting
--    cross-thread accesses errors, and disjoint steps commute (frame).
theorem den_frame_foreign (hut : u ≠ t) (hd : den A u σ σ') :
    den A u (upd σ (.l t r) k) (upd σ' (.l t r) k)

theorem valid_acq_vs_local (hut : u ≠ t)
    (h1 : den aAcq t σ σ') (h2 : den (.lact r₂ e) u σ' σ'') :
    ∃ τ, den (.lact r₂ e) u σ τ ∧ den aAcq t τ σ''
```

`den_frame_foreign` proves the "non-conflicting steps commute" half of
validity once and for all (any action frames through a foreign local
update); `valid_acq_vs_local` is a representative validity obligation from
Definition 1 discharged in full. Proving `Valid Mex` for *every* pair of
actions is a finite obligation of the same two mechanisms
(lock-exclusivity + framing); the representative instance and the general
frame lemma are what is mechanized here.

## The parser

[`Parser.lean`](Parser.lean) is a hand-written tokenizer + recursive
descent parser from Rust-flavored source to the verified `Stmt` AST:

```
acquire(m); r = x; x = r + arg; release(m);
if (e) { s } else { s }      while (e) { s }      assert(e);
```

Identifiers are resolved to global/local indices through a caller-supplied
environment, mirroring how a real front-end lowers names to MIR locals.
Expressions read only locals; globals are touched through explicit
read/write actions, matching the semantics.

The parser is **executable and tested**, not kernel-proved: its tokenizer
uses `String` primitives that the Lean kernel does not reduce, so the
`#guard` commands (which run at compile time and fail the build on a wrong
parse) play the role of a test suite. This mirrors reality — a compiler's
parser is trusted/tested, and verification begins at the AST. Everything
downstream of the AST here *is* kernel-checked:

```lean
#guard parseBlock counterEnv 100
  "acquire(m); r = x; x = r + arg; release(m);"
  = some ( … the exact AST proved atomic in Examples.lean … )
```

## Building

```sh
lake build MoverRust
```

Requires Lean 4 `v4.10.0` (see `../lean-toolchain`). No Mathlib.
