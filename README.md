# Types and Programming Languages — in Lean 4

A formalization of the core chapters of Benjamin C. Pierce's *Types and
Programming Languages* (TAPL) in Lean 4, with **one chapter per
subdirectory**. Each chapter directory contains:

- one or more `.lean` files with the definitions, worked **examples**, and
  fully machine-checked **proofs** of the chapter's theorems;
- a `README.md` that walks through the chapter: every definition with its
  body, and every theorem statement — but **without proofs** (those live in
  the Lean files) — together with enough prose to read it as a standalone
  tour of the chapter.

## Chapters

| Directory | TAPL chapter | Contents |
|---|---|---|
| [`Chapter03`](Chapter03/) | 3. Untyped Arithmetic Expressions | booleans + numbers, small-step semantics, determinacy, normal forms, termination, big-step equivalence |
| [`Chapter05`](Chapter05/) | 5. The Untyped Lambda-Calculus | λ-terms (de Bruijn), full β-reduction, Church encodings |
| [`Chapter06`](Chapter06/) | 6. Nameless Representation of Terms | shifting, substitution, and their algebraic laws |
| [`Chapter07`](Chapter07/) | 7. An ML Implementation of the λ-Calculus | call-by-value evaluator, determinacy, evaluation function with fuel |
| [`Chapter08`](Chapter08/) | 8. Typed Arithmetic Expressions | typing relation, inversion, progress & preservation, type safety |
| [`Chapter09`](Chapter09/) | 9. Simply Typed Lambda-Calculus | STLC: weakening, substitution lemma, progress & preservation |
| [`Chapter10`](Chapter10/) | 10. An ML Implementation of Simple Types | executable typechecker, soundness & completeness |
| [`Chapter11`](Chapter11/) | 11. Simple Extensions | unit, let, pairs, sums — full metatheory |
| [`Chapter15`](Chapter15/) | 15. Subtyping | subtype relation, subsumption, inversion, progress & preservation |
| [`Chapter20`](Chapter20/) | 20. Recursive Types | iso-recursive types (fold/unfold), metatheory |
| [`Chapter23`](Chapter23/) | 23. Universal Types | System F, progress & preservation, Church encodings typed |

Chapters of the book that are pure prose or ML-implementation interludes
without new formal content (1, 2, 4, 12, 14, 16–19, 21, 22, 24–32) are not
formalized here; where a chapter's content is best expressed differently in
Lean (e.g. chapter 5's named terms vs. chapter 6's de Bruijn indices), the
chapter README explains the deviation.

## Conventions

- **De Bruijn indices** are used for binders throughout (introduced in the
  book in chapter 6); named syntax appears only in comments and READMEs.
- Evaluation is **call-by-value**, small-step, exactly as in the book;
  chapter 5 additionally formalizes full β-reduction.
- The formalization is **self-contained**: plain Lean 4, no Mathlib.
- Chapter files build on earlier chapters where the book does (e.g.
  chapter 7 imports the terms of chapters 5–6); each chapter's README
  restates what it needs, so the READMEs read independently.

## Building

With Lean 4 (`v4.10.0`, see `lean-toolchain`) installed:

```sh
lake build
```

Every theorem in the repository is proved — there are no `sorry`s.
