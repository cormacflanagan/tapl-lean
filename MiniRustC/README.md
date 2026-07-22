# MiniRustC — a verified compiler in miniature

A working model of the "verified Rust compiler" architecture at
demonstration scale, in one kernel-checked Lean file:
[`Compiler.lean`](Compiler.lean).

```
MiniRust source ──check──▶ (rejected, or accepted with mut-context Γ)
      │
      │  compileS               theorem compileS_correct:
      ▼                         source ⇓ σ'  ⇒  machine runs to σ'
stack-machine code ──MSteps──▶  same final store, for every program
```

The pieces mirror the real project shape: front-end static checks as a
*filter* with their own soundness theorem (the borrow checker's role), a
verified translation to a small machine (the CompCert-style core), and a
trusted base reduced to the Lean kernel plus the machine model.

## The source language

MiniRust-flavored: numbered locals introduced in declaration order by
`let` / `let mut` (as rustc numbers MIR locals), assignment, sequencing,
`if`, `while`, over integer expressions:

```lean
inductive Stmt : Type where
  | skip
  | decl (n : Nat) (mutb : Bool) (e : Expr)   -- let x_n = e / let mut x_n = e
  | assign (n : Nat) (e : Expr)               -- x_n = e
  | seq (s₁ s₂ : Stmt)
  | ite (c : Expr) (s₁ s₂ : Stmt)
  | wloop (c : Expr) (s : Stmt)               -- while c { s }

inductive BigStep : Stmt → Store → Store → Prop   -- ⟨s, σ⟩ ⇓ σ'
```

## The static checker, with a soundness theorem

`check Γ s` enforces scope (declare before use, `let` declares the next
local, no declarations escape `if`/`while` bodies) and **Rust's
mutability discipline** (only `mut` locals may be assigned). Its
soundness theorem is the semantic content of `let` vs `let mut`:

```lean
def check (Γ : List Bool) : Stmt → Option (List Bool)

theorem check_extends : check Γ s = some Γ' → ∃ ext, Γ' = Γ ++ ext

-- in a checked program, immutable locals never change
theorem immut_sound (hb : BigStep s σ σ') :
    check Γ s = some Γ' → ∀ n, Γ.get? n = some false → σ' n = σ n
```

## The machine and the compiler

A stack machine with absolute jumps (`konst/load/store/addI/mulI/lessI/
eqI/jmp/jz`), configurations `(pc, stack, store)`, small-step `MStep` and
its closure `MSteps`. The compiler places code at an absolute `base` so
jump targets are computed, not patched:

```lean
def compileE : Expr → List Instr          -- position-independent
def compileS : Stmt → Nat → List Instr    -- code intended for position base
```

`contains P base c` ("program `P` has code `c` at `base`") lets each
induction case reason about its own fragment inside the whole program —
the miniature of a compiler-verification simulation invariant.

## The theorems

```lean
-- expressions: compiled code pushes the value, changes nothing else
theorem compileE_correct :
    contains P base (compileE e) →
    MSteps P base stk σ (base + (compileE e).length) (eval σ e :: stk) σ

-- SEMANTIC PRESERVATION: whatever the source semantics computes,
-- the compiled code computes — for every program
theorem compileS_correct (hb : BigStep s σ σ') :
    contains P base (compileS s base) →
    MSteps P base stk σ (base + (compileS s base).length) stk σ'
```

The `while` case is the essential one: the loop compiles to
`⟨guard⟩; jz end; ⟨body⟩; jmp base`, and the proof follows the big-step
derivation — guard, conditional jump, body (IH), back-jump, and the
*outer* induction hypothesis for the remaining iterations.

## End to end

The example program (`3!` by loop):

```rust
let mut x = 3;        // local 0
let mut acc = 1;      // local 1
while 0 < x { acc = acc * x; x = x + (-1); }
```

```lean
example : check [] prog = some [true, true]        -- accepted
example : check [] progNoMut = none                -- rejected: assign to non-mut
example : check [] (.assign 0 (.int 1)) = none     -- rejected: out of scope

theorem prog_evals : ∃ σ', BigStep prog σ0 σ' ∧ σ' 1 = 6

-- the compiled machine code provably computes acc = 6
theorem progCode_runs : ∃ σ',
    MSteps progCode 0 [] σ0 progCode.length [] σ' ∧ σ' 1 = 6
```

## What the real project adds

Scaling this to an actual verified Rust compiler (see the discussion in
the repo README) means: MIR instead of this toy source; a formal semantics
for it (the genuine open problem — MiniRust/a-mir-formality territory); a
register machine with calling conventions instead of a stack toy;
optimization passes each with this same simulation-proof shape; and
RustBelt-style borrow-checker soundness replacing `immut_sound`. None of
those change the *architecture* demonstrated here — they change its size.
