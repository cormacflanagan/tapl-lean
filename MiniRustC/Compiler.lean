/-!
# MiniRustC: a verified compiler in miniature

A working model of the "verified Rust compiler" architecture, at
demonstration scale:

* a **MiniRust-flavored source language**: numbered locals introduced by
  `let` / `let mut`, assignment, sequencing, `if` and `while`, over
  integer expressions;
* a **static checker** playing the borrow checker's role in miniature —
  scope checking plus Rust's mutability discipline — with a proved
  soundness theorem: *in checked programs, immutable locals never
  change*;
* a **stack machine** target with absolute jumps;
* a **compiler** from source to machine code, written in Lean; and
* the **semantic preservation theorem**: if the source program's big-step
  semantics takes store `σ` to `σ'`, then the compiled code, run on the
  machine, drives the same store from `σ` to `σ'` — for *every* program,
  checked by the Lean kernel.

The architecture mirrors the real project shape discussed in the README:
front-end checks as a filter with their own soundness theorem, a verified
translation to a small machine, and the trusted base reduced to the Lean
kernel plus the machine model.
-/

namespace MiniRustC

/-! ## Source language -/

/-- Stores map (numbered) locals to integers. -/
def Store := Nat → Int

/-- Update a store at one local. -/
def upd (σ : Store) (n : Nat) (v : Int) : Store :=
  fun m => if m = n then v else σ m

/-- Integer expressions over locals. Comparisons yield `1` or `0`
(condition positions treat nonzero as true). -/
inductive Expr : Type where
  | int (k : Int)
  | var (n : Nat)
  | add (e₁ e₂ : Expr)
  | mul (e₁ e₂ : Expr)
  | less (e₁ e₂ : Expr)
  | eqE (e₁ e₂ : Expr)
  deriving Repr, DecidableEq

/-- Expression evaluation. -/
def eval (σ : Store) : Expr → Int
  | .int k => k
  | .var n => σ n
  | .add e₁ e₂ => eval σ e₁ + eval σ e₂
  | .mul e₁ e₂ => eval σ e₁ * eval σ e₂
  | .less e₁ e₂ => if eval σ e₁ < eval σ e₂ then 1 else 0
  | .eqE e₁ e₂ => if eval σ e₁ = eval σ e₂ then 1 else 0

/-- Statements. `decl n mutb e` is `let x_n = e` / `let mut x_n = e`; the
static checker enforces that `n` is the next local in declaration order
(locals are numbered by a pre-pass, as rustc numbers MIR locals). -/
inductive Stmt : Type where
  | skip
  | decl (n : Nat) (mutb : Bool) (e : Expr)
  | assign (n : Nat) (e : Expr)
  | seq (s₁ s₂ : Stmt)
  | ite (c : Expr) (s₁ s₂ : Stmt)
  | wloop (c : Expr) (s : Stmt)
  deriving Repr, DecidableEq

/-- Big-step operational semantics, `⟨s, σ⟩ ⇓ σ'`. -/
inductive BigStep : Stmt → Store → Store → Prop where
  | skip {σ} : BigStep .skip σ σ
  | decl {n mutb e σ} :
      BigStep (.decl n mutb e) σ (upd σ n (eval σ e))
  | assign {n e σ} :
      BigStep (.assign n e) σ (upd σ n (eval σ e))
  | seq {s₁ s₂ σ σ₁ σ₂} :
      BigStep s₁ σ σ₁ → BigStep s₂ σ₁ σ₂ → BigStep (.seq s₁ s₂) σ σ₂
  | iteT {c s₁ s₂ σ σ'} :
      eval σ c ≠ 0 → BigStep s₁ σ σ' → BigStep (.ite c s₁ s₂) σ σ'
  | iteF {c s₁ s₂ σ σ'} :
      eval σ c = 0 → BigStep s₂ σ σ' → BigStep (.ite c s₁ s₂) σ σ'
  | whileF {c s σ} :
      eval σ c = 0 → BigStep (.wloop c s) σ σ
  | whileT {c s σ σ₁ σ₂} :
      eval σ c ≠ 0 → BigStep s σ σ₁ → BigStep (.wloop c s) σ₁ σ₂ →
      BigStep (.wloop c s) σ σ₂

/-! ## The static checker (the borrow checker's little cousin)

The context `Γ : List Bool` records, for each declared local in
declaration order, whether it is `mut`. The checker enforces:

* every local is declared before use (scope);
* `let` declares exactly the next local (`n = Γ.length`);
* only `mut` locals are assigned (Rust's mutability discipline);
* `if`/`while` bodies do not declare locals that escape (block scoping).
-/

/-- All locals of `e` are declared. -/
def exprOk (Γ : List Bool) : Expr → Bool
  | .int _ => true
  | .var n => n < Γ.length
  | .add e₁ e₂ => exprOk Γ e₁ && exprOk Γ e₂
  | .mul e₁ e₂ => exprOk Γ e₁ && exprOk Γ e₂
  | .less e₁ e₂ => exprOk Γ e₁ && exprOk Γ e₂
  | .eqE e₁ e₂ => exprOk Γ e₁ && exprOk Γ e₂

/-- The checker: `some Γ'` is the context after the statement. -/
def check (Γ : List Bool) : Stmt → Option (List Bool)
  | .skip => some Γ
  | .decl n mutb e =>
      if n = Γ.length && exprOk Γ e then some (Γ ++ [mutb]) else none
  | .assign n e =>
      match Γ.get? n with
      | some true => if exprOk Γ e then some Γ else none
      | _ => none
  | .seq s₁ s₂ =>
      match check Γ s₁ with
      | some Γ₁ => check Γ₁ s₂
      | none => none
  | .ite c s₁ s₂ =>
      if exprOk Γ c then
        match check Γ s₁, check Γ s₂ with
        | some Γ₁, some Γ₂ =>
            if Γ₁ = Γ && Γ₂ = Γ then some Γ else none
        | _, _ => none
      else none
  | .wloop c s =>
      if exprOk Γ c then
        match check Γ s with
        | some Γ' => if Γ' = Γ then some Γ else none
        | none => none
      else none

/-- Lookups below the length succeed. -/
theorem get?_lt_some {α : Type} :
    ∀ (l : List α) (n : Nat) (a : α), l.get? n = some a → n < l.length := by
  intro l
  induction l with
  | nil => intro n a h; cases h
  | cons b l ih =>
      intro n a h
      cases n with
      | zero => simp
      | succ n => have := ih n a h; simp; omega

/-- Lookup in a left factor of an append. -/
theorem get?_append_l {α : Type} :
    ∀ (l₁ l₂ : List α) (n : Nat) (a : α),
      l₁.get? n = some a → (l₁ ++ l₂).get? n = some a := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ n a h; cases h
  | cons b l₁ ih =>
      intro l₂ n a h
      cases n with
      | zero => exact h
      | succ n => exact ih l₂ n a h

/-- The checker only ever appends declarations. -/
theorem check_extends :
    ∀ (s : Stmt) (Γ Γ' : List Bool), check Γ s = some Γ' →
      ∃ ext, Γ' = Γ ++ ext := by
  intro s
  induction s with
  | skip =>
      intro Γ Γ' h
      cases h
      exact ⟨[], by simp⟩
  | decl n mutb e =>
      intro Γ Γ' h
      simp only [check] at h
      split at h
      · cases h; exact ⟨[mutb], rfl⟩
      · cases h
  | assign n e =>
      intro Γ Γ' h
      simp only [check] at h
      split at h
      · split at h
        · cases h; exact ⟨[], by simp⟩
        · cases h
      · cases h
  | seq s₁ s₂ ih₁ ih₂ =>
      intro Γ Γ' h
      simp only [check] at h
      split at h
      next Γ₁ heq₁ =>
        obtain ⟨e₁, rfl⟩ := ih₁ Γ Γ₁ heq₁
        obtain ⟨e₂, rfl⟩ := ih₂ _ Γ' h
        exact ⟨e₁ ++ e₂, by simp⟩
      next => cases h
  | ite c s₁ s₂ _ _ =>
      intro Γ Γ' h
      simp only [check] at h
      split at h
      · split at h
        next Γ₁ Γ₂ _ _ =>
          split at h
          · cases h; exact ⟨[], by simp⟩
          · cases h
        next => cases h
      · cases h
  | wloop c s _ =>
      intro Γ Γ' h
      simp only [check] at h
      split at h
      · split at h
        next Γ₀ _ =>
          split at h
          · cases h; exact ⟨[], by simp⟩
          · cases h
        next => cases h
      · cases h

/-- **Immutability soundness**: in a checked program, locals not declared
`mut` never change — the semantic content of Rust's `let` vs `let mut`. -/
theorem immut_sound {s : Stmt} {σ σ' : Store} (hb : BigStep s σ σ') :
    ∀ (Γ Γ' : List Bool), check Γ s = some Γ' →
      ∀ n, Γ.get? n = some false → σ' n = σ n := by
  induction hb with
  | skip => intro Γ Γ' _ n _; rfl
  | @decl k mutb e σ =>
      intro Γ Γ' h n hn
      simp only [check] at h
      split at h
      next hg =>
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        have hlt := get?_lt_some Γ n false hn
        have : n ≠ k := by omega
        simp [upd, this]
      next => cases h
  | @assign k e σ =>
      intro Γ Γ' h n hn
      simp only [check] at h
      split at h
      next hk =>
        have : n ≠ k := by
          intro heq
          subst heq
          rw [hn] at hk
          cases hk
        simp [upd, this]
      next => cases h
  | seq _ _ ih₁ ih₂ =>
      intro Γ Γ' h n hn
      simp only [check] at h
      split at h
      next Γ₁ heq₁ =>
        obtain ⟨ext, rfl⟩ := check_extends _ Γ Γ₁ heq₁
        rw [ih₂ _ Γ' h n (get?_append_l Γ ext n false hn),
          ih₁ Γ _ heq₁ n hn]
      next => cases h
  | iteT _ _ ih =>
      intro Γ Γ' h n hn
      simp only [check] at h
      split at h
      · split at h
        next Γ₁ Γ₂ heq₁ _ =>
          split at h
          next hg =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
            cases h
            rw [hg.1] at heq₁
            exact ih Γ Γ heq₁ n hn
          · cases h
        next => cases h
      · cases h
  | iteF _ _ ih =>
      intro Γ Γ' h n hn
      simp only [check] at h
      split at h
      · split at h
        next Γ₁ Γ₂ _ heq₂ =>
          split at h
          next hg =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
            cases h
            rw [hg.2] at heq₂
            exact ih Γ Γ heq₂ n hn
          · cases h
        next => cases h
      · cases h
  | whileF _ =>
      intro Γ Γ' _ n _; rfl
  | whileT _ _ _ ih₁ ih₂ =>
      intro Γ Γ' h n hn
      have hloop := h
      simp only [check] at h
      split at h
      · split at h
        next Γ₀ heq₀ =>
          split at h
          next hg =>
            cases h
            rw [hg] at heq₀
            rw [ih₂ Γ Γ hloop n hn, ih₁ Γ Γ heq₀ n hn]
          · cases h
        next => cases h
      · cases h

/-! ## The stack machine -/

/-- Machine instructions; jumps are absolute. Comparisons push `1`/`0`;
`jz` pops and jumps when the value is `0`. -/
inductive Instr : Type where
  | konst (k : Int)
  | load (n : Nat)
  | store (n : Nat)
  | addI
  | mulI
  | lessI
  | eqI
  | jmp (a : Nat)
  | jz (a : Nat)
  deriving Repr, DecidableEq

/-- One machine step of program `P`: configuration is
(program counter, operand stack, store). -/
inductive MStep (P : List Instr) :
    Nat → List Int → Store → Nat → List Int → Store → Prop where
  | konst {pc stk σ k} :
      P.get? pc = some (.konst k) →
      MStep P pc stk σ (pc + 1) (k :: stk) σ
  | load {pc stk σ n} :
      P.get? pc = some (.load n) →
      MStep P pc stk σ (pc + 1) (σ n :: stk) σ
  | store {pc stk σ n v} :
      P.get? pc = some (.store n) →
      MStep P pc (v :: stk) σ (pc + 1) stk (upd σ n v)
  | addI {pc stk σ a b} :
      P.get? pc = some .addI →
      MStep P pc (a :: b :: stk) σ (pc + 1) ((b + a) :: stk) σ
  | mulI {pc stk σ a b} :
      P.get? pc = some .mulI →
      MStep P pc (a :: b :: stk) σ (pc + 1) ((b * a) :: stk) σ
  | lessI {pc stk σ a b} :
      P.get? pc = some .lessI →
      MStep P pc (a :: b :: stk) σ (pc + 1)
        ((if b < a then (1 : Int) else 0) :: stk) σ
  | eqI {pc stk σ a b} :
      P.get? pc = some .eqI →
      MStep P pc (a :: b :: stk) σ (pc + 1)
        ((if b = a then (1 : Int) else 0) :: stk) σ
  | jmp {pc stk σ a} :
      P.get? pc = some (.jmp a) →
      MStep P pc stk σ a stk σ
  | jz0 {pc stk σ a} :
      P.get? pc = some (.jz a) →
      MStep P pc ((0 : Int) :: stk) σ a stk σ
  | jzS {pc stk σ a v} :
      P.get? pc = some (.jz a) → v ≠ 0 →
      MStep P pc (v :: stk) σ (pc + 1) stk σ

/-- Zero or more machine steps. -/
inductive MSteps (P : List Instr) :
    Nat → List Int → Store → Nat → List Int → Store → Prop where
  | refl (pc stk σ) : MSteps P pc stk σ pc stk σ
  | head {pc stk σ pc₁ stk₁ σ₁ pc₂ stk₂ σ₂} :
      MStep P pc stk σ pc₁ stk₁ σ₁ →
      MSteps P pc₁ stk₁ σ₁ pc₂ stk₂ σ₂ →
      MSteps P pc stk σ pc₂ stk₂ σ₂

theorem MSteps.trans {P : List Instr}
    {pc stk σ pc₁ stk₁ σ₁ pc₂ stk₂ σ₂} :
    MSteps P pc stk σ pc₁ stk₁ σ₁ →
    MSteps P pc₁ stk₁ σ₁ pc₂ stk₂ σ₂ →
    MSteps P pc stk σ pc₂ stk₂ σ₂ := by
  intro h₁ h₂
  induction h₁ with
  | refl _ _ _ => exact h₂
  | head s _ ih => exact .head s (ih h₂)

theorem MSteps.single {P : List Instr} {pc stk σ pc' stk' σ'}
    (h : MStep P pc stk σ pc' stk' σ') : MSteps P pc stk σ pc' stk' σ' :=
  .head h (.refl _ _ _)

/-! ## The compiler -/

/-- Compile an expression to stack code (position-independent: no
jumps). -/
def compileE : Expr → List Instr
  | .int k => [.konst k]
  | .var n => [.load n]
  | .add e₁ e₂ => compileE e₁ ++ compileE e₂ ++ [.addI]
  | .mul e₁ e₂ => compileE e₁ ++ compileE e₂ ++ [.mulI]
  | .less e₁ e₂ => compileE e₁ ++ compileE e₂ ++ [.lessI]
  | .eqE e₁ e₂ => compileE e₁ ++ compileE e₂ ++ [.eqI]

/-- Compile a statement to code intended to sit at absolute position
`base` (all jump targets are absolute, computed from `base`). -/
def compileS : Stmt → Nat → List Instr
  | .skip, _ => []
  | .decl n _ e, _ => compileE e ++ [.store n]
  | .assign n e, _ => compileE e ++ [.store n]
  | .seq s₁ s₂, base =>
      let c₁ := compileS s₁ base
      c₁ ++ compileS s₂ (base + c₁.length)
  | .ite c s₁ s₂, base =>
      let ce := compileE c
      let c₁ := compileS s₁ (base + ce.length + 1)
      let elseA := base + ce.length + 1 + c₁.length + 1
      let c₂ := compileS s₂ elseA
      ce ++ [.jz elseA] ++ c₁ ++ [.jmp (elseA + c₂.length)] ++ c₂
  | .wloop c s, base =>
      let ce := compileE c
      let cb := compileS s (base + ce.length + 1)
      ce ++ [.jz (base + ce.length + 1 + cb.length + 1)] ++ cb ++
        [.jmp base]

/-- `contains P base c`: program `P` has the code `c` at position
`base`. -/
def contains (P : List Instr) (base : Nat) (c : List Instr) : Prop :=
  ∀ i ins, c.get? i = some ins → P.get? (base + i) = some ins

theorem get?_append_r {α : Type} :
    ∀ (l₁ l₂ : List α) (i : Nat), (l₁ ++ l₂).get? (l₁.length + i) = l₂.get? i := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ i; simp
  | cons a l₁ ih =>
      intro l₂ i
      have h : (a :: l₁).length + i = l₁.length + i + 1 := by
        simp only [List.length_cons]
        omega
      rw [h]
      exact ih l₂ i

/-- Containment splits over appended code. -/
theorem contains_append {P : List Instr} {base : Nat} {c₁ c₂ : List Instr}
    (h : contains P base (c₁ ++ c₂)) :
    contains P base c₁ ∧ contains P (base + c₁.length) c₂ := by
  constructor
  · intro i ins hi
    exact h i ins (get?_append_l c₁ c₂ i ins hi)
  · intro i ins hi
    have h' := h (c₁.length + i) ins (by rw [get?_append_r]; exact hi)
    have : base + (c₁.length + i) = base + c₁.length + i := by omega
    rwa [this] at h'

/-- The head instruction of contained code. -/
theorem contains_head {P : List Instr} {base : Nat} {ins : Instr}
    {rest : List Instr} (h : contains P base (ins :: rest)) :
    P.get? base = some ins := by
  have := h 0 ins rfl
  simpa using this

/-- Transport containment along an equality of positions. -/
theorem contains_congr {P : List Instr} {base base' : Nat}
    {c : List Instr} (h : contains P base c) (heq : base = base') :
    contains P base' c := heq ▸ h

/-- A whole program is contained in itself at position `0`. -/
theorem contains_self (P : List Instr) : contains P 0 P := by
  intro i ins hi
  simpa using hi

/-! ## Correctness of expression compilation -/

/-- Running compiled expression code pushes the expression's value and
leaves everything else unchanged. -/
theorem compileE_correct :
    ∀ (e : Expr) (P : List Instr) (base : Nat) (stk : List Int) (σ : Store),
      contains P base (compileE e) →
      MSteps P base stk σ (base + (compileE e).length)
        (eval σ e :: stk) σ := by
  intro e
  induction e with
  | int k =>
      intro P base stk σ h
      exact .single (.konst (contains_head h))
  | var n =>
      intro P base stk σ h
      exact .single (.load (contains_head h))
  | add e₁ e₂ ih₁ ih₂ =>
      intro P base stk σ h
      rw [show compileE (Expr.add e₁ e₂) =
          (compileE e₁ ++ compileE e₂) ++ [Instr.addI] from rfl] at h
      obtain ⟨h₁₂, hop⟩ := contains_append h
      obtain ⟨h₁, h₂⟩ := contains_append h₁₂
      have s₁ := ih₁ P base stk σ h₁
      have s₂ := ih₂ P (base + (compileE e₁).length) (eval σ e₁ :: stk) σ h₂
      have hins : P.get? (base + (compileE e₁).length +
          (compileE e₂).length) = some Instr.addI := by
        have := contains_head hop
        have hlen : base + (compileE e₁ ++ compileE e₂).length =
            base + (compileE e₁).length + (compileE e₂).length := by
          simp only [List.length_append]
          omega
        rwa [hlen] at this
      have s₃ : MStep P
          (base + (compileE e₁).length + (compileE e₂).length)
          (eval σ e₂ :: eval σ e₁ :: stk) σ
          (base + (compileE e₁).length + (compileE e₂).length + 1)
          ((eval σ e₁ + eval σ e₂) :: stk) σ := .addI hins
      have hgoal : base + (compileE (Expr.add e₁ e₂)).length =
          base + (compileE e₁).length + (compileE e₂).length + 1 := by
        simp only [compileE, List.length_append, List.length_cons,
          List.length_nil]
        omega
      rw [hgoal]
      exact s₁.trans (s₂.trans (MSteps.single s₃))
  | mul e₁ e₂ ih₁ ih₂ =>
      intro P base stk σ h
      rw [show compileE (Expr.mul e₁ e₂) =
          (compileE e₁ ++ compileE e₂) ++ [Instr.mulI] from rfl] at h
      obtain ⟨h₁₂, hop⟩ := contains_append h
      obtain ⟨h₁, h₂⟩ := contains_append h₁₂
      have s₁ := ih₁ P base stk σ h₁
      have s₂ := ih₂ P (base + (compileE e₁).length) (eval σ e₁ :: stk) σ h₂
      have hins : P.get? (base + (compileE e₁).length +
          (compileE e₂).length) = some Instr.mulI := by
        have := contains_head hop
        have hlen : base + (compileE e₁ ++ compileE e₂).length =
            base + (compileE e₁).length + (compileE e₂).length := by
          simp only [List.length_append]
          omega
        rwa [hlen] at this
      have s₃ : MStep P
          (base + (compileE e₁).length + (compileE e₂).length)
          (eval σ e₂ :: eval σ e₁ :: stk) σ
          (base + (compileE e₁).length + (compileE e₂).length + 1)
          ((eval σ e₁ * eval σ e₂) :: stk) σ := .mulI hins
      have hgoal : base + (compileE (Expr.mul e₁ e₂)).length =
          base + (compileE e₁).length + (compileE e₂).length + 1 := by
        simp only [compileE, List.length_append, List.length_cons,
          List.length_nil]
        omega
      rw [hgoal]
      exact s₁.trans (s₂.trans (MSteps.single s₃))
  | less e₁ e₂ ih₁ ih₂ =>
      intro P base stk σ h
      rw [show compileE (Expr.less e₁ e₂) =
          (compileE e₁ ++ compileE e₂) ++ [Instr.lessI] from rfl] at h
      obtain ⟨h₁₂, hop⟩ := contains_append h
      obtain ⟨h₁, h₂⟩ := contains_append h₁₂
      have s₁ := ih₁ P base stk σ h₁
      have s₂ := ih₂ P (base + (compileE e₁).length) (eval σ e₁ :: stk) σ h₂
      have hins : P.get? (base + (compileE e₁).length +
          (compileE e₂).length) = some Instr.lessI := by
        have := contains_head hop
        have hlen : base + (compileE e₁ ++ compileE e₂).length =
            base + (compileE e₁).length + (compileE e₂).length := by
          simp only [List.length_append]
          omega
        rwa [hlen] at this
      have s₃ : MStep P
          (base + (compileE e₁).length + (compileE e₂).length)
          (eval σ e₂ :: eval σ e₁ :: stk) σ
          (base + (compileE e₁).length + (compileE e₂).length + 1)
          ((if eval σ e₁ < eval σ e₂ then (1 : Int) else 0) :: stk) σ := .lessI hins
      have hgoal : base + (compileE (Expr.less e₁ e₂)).length =
          base + (compileE e₁).length + (compileE e₂).length + 1 := by
        simp only [compileE, List.length_append, List.length_cons,
          List.length_nil]
        omega
      rw [hgoal]
      exact s₁.trans (s₂.trans (MSteps.single s₃))
  | eqE e₁ e₂ ih₁ ih₂ =>
      intro P base stk σ h
      rw [show compileE (Expr.eqE e₁ e₂) =
          (compileE e₁ ++ compileE e₂) ++ [Instr.eqI] from rfl] at h
      obtain ⟨h₁₂, hop⟩ := contains_append h
      obtain ⟨h₁, h₂⟩ := contains_append h₁₂
      have s₁ := ih₁ P base stk σ h₁
      have s₂ := ih₂ P (base + (compileE e₁).length) (eval σ e₁ :: stk) σ h₂
      have hins : P.get? (base + (compileE e₁).length +
          (compileE e₂).length) = some Instr.eqI := by
        have := contains_head hop
        have hlen : base + (compileE e₁ ++ compileE e₂).length =
            base + (compileE e₁).length + (compileE e₂).length := by
          simp only [List.length_append]
          omega
        rwa [hlen] at this
      have s₃ : MStep P
          (base + (compileE e₁).length + (compileE e₂).length)
          (eval σ e₂ :: eval σ e₁ :: stk) σ
          (base + (compileE e₁).length + (compileE e₂).length + 1)
          ((if eval σ e₁ = eval σ e₂ then (1 : Int) else 0) :: stk) σ := .eqI hins
      have hgoal : base + (compileE (Expr.eqE e₁ e₂)).length =
          base + (compileE e₁).length + (compileE e₂).length + 1 := by
        simp only [compileE, List.length_append, List.length_cons,
          List.length_nil]
        omega
      rw [hgoal]
      exact s₁.trans (s₂.trans (MSteps.single s₃))


/-! ## Correctness of statement compilation -/

/-- **Semantic preservation**: if `⟨s, σ⟩ ⇓ σ'` then the compiled code for
`s`, located at `base` inside any program `P`, drives the machine from
`(base, stk, σ)` to `(base + |code|, stk, σ')`. -/
theorem compileS_correct {s : Stmt} {σ σ' : Store} (hb : BigStep s σ σ') :
    ∀ (P : List Instr) (base : Nat) (stk : List Int),
      contains P base (compileS s base) →
      MSteps P base stk σ (base + (compileS s base).length) stk σ' := by
  induction hb with
  | skip =>
      intro P base stk _
      have : base + (compileS .skip base).length = base := by
        simp [compileS]
      rw [this]
      exact .refl _ _ _
  | @decl n mutb e σ =>
      intro P base stk h
      rw [show compileS (.decl n mutb e) base =
          compileE e ++ [.store n] from rfl] at h
      obtain ⟨he, hst⟩ := contains_append h
      have s1 := compileE_correct e P base stk σ he
      have s2 : MStep P (base + (compileE e).length) (eval σ e :: stk) σ
          (base + (compileE e).length + 1) stk (upd σ n (eval σ e)) :=
        .store (contains_head hst)
      have hlen : base + (compileS (.decl n mutb e) base).length =
          base + (compileE e).length + 1 := by
        simp only [compileS, List.length_append, List.length_cons,
          List.length_nil]
        omega
      rw [hlen]
      exact s1.trans (MSteps.single s2)
  | @assign n e σ =>
      intro P base stk h
      rw [show compileS (.assign n e) base =
          compileE e ++ [.store n] from rfl] at h
      obtain ⟨he, hst⟩ := contains_append h
      have s1 := compileE_correct e P base stk σ he
      have s2 : MStep P (base + (compileE e).length) (eval σ e :: stk) σ
          (base + (compileE e).length + 1) stk (upd σ n (eval σ e)) :=
        .store (contains_head hst)
      have hlen : base + (compileS (.assign n e) base).length =
          base + (compileE e).length + 1 := by
        simp only [compileS, List.length_append, List.length_cons,
          List.length_nil]
        omega
      rw [hlen]
      exact s1.trans (MSteps.single s2)
  | @seq s₁ s₂ σ σ₁ σ₂ _ _ ih₁ ih₂ =>
      intro P base stk h
      rw [show compileS (.seq s₁ s₂) base =
          compileS s₁ base ++
            compileS s₂ (base + (compileS s₁ base).length) from rfl] at h
      obtain ⟨h₁, h₂⟩ := contains_append h
      have m1 := ih₁ P base stk h₁
      have m2 := ih₂ P (base + (compileS s₁ base).length) stk h₂
      have hlen : base + (compileS (.seq s₁ s₂) base).length =
          base + (compileS s₁ base).length +
            (compileS s₂ (base + (compileS s₁ base).length)).length := by
        simp only [compileS, List.length_append]
        omega
      rw [hlen]
      exact m1.trans m2
  | @iteT c s₁ s₂ σ σ' hc _ ih =>
      intro P base stk h
      rw [show compileS (.ite c s₁ s₂) base =
          compileE c ++ [.jz (base + (compileE c).length + 1 +
              (compileS s₁ (base + (compileE c).length + 1)).length + 1)] ++
            compileS s₁ (base + (compileE c).length + 1) ++
            [.jmp (base + (compileE c).length + 1 +
              (compileS s₁ (base + (compileE c).length + 1)).length + 1 +
              (compileS s₂ (base + (compileE c).length + 1 +
                (compileS s₁ (base + (compileE c).length + 1)).length +
                1)).length)] ++
            compileS s₂ (base + (compileE c).length + 1 +
              (compileS s₁ (base + (compileE c).length + 1)).length + 1)
          from rfl] at h
      obtain ⟨hA, _⟩ := contains_append h
      obtain ⟨hB, hjmp⟩ := contains_append hA
      obtain ⟨hC, hcs1⟩ := contains_append hB
      obtain ⟨hce, hjz⟩ := contains_append hC
      have m1 := compileE_correct c P base stk σ hce
      have m2 : MStep P (base + (compileE c).length) (eval σ c :: stk) σ
          (base + (compileE c).length + 1) stk σ :=
        .jzS (contains_head hjz) hc
      have m3 := ih P (base + (compileE c).length + 1) stk
        (contains_congr hcs1 (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega))
      have m4 : MStep P
          (base + (compileE c).length + 1 +
            (compileS s₁ (base + (compileE c).length + 1)).length)
          stk σ'
          (base + (compileE c).length + 1 +
            (compileS s₁ (base + (compileE c).length + 1)).length + 1 +
            (compileS s₂ (base + (compileE c).length + 1 +
              (compileS s₁ (base + (compileE c).length + 1)).length +
              1)).length)
          stk σ' := by
        apply MStep.jmp
        exact contains_head (contains_congr hjmp (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega))
      have hlen : base + (compileS (.ite c s₁ s₂) base).length =
          base + (compileE c).length + 1 +
            (compileS s₁ (base + (compileE c).length + 1)).length + 1 +
            (compileS s₂ (base + (compileE c).length + 1 +
              (compileS s₁ (base + (compileE c).length + 1)).length +
              1)).length := by
        simp only [compileS, List.length_append, List.length_cons,
          List.length_nil]
        omega
      rw [hlen]
      exact m1.trans ((MSteps.single m2).trans
        (m3.trans (MSteps.single m4)))
  | @iteF c s₁ s₂ σ σ' hc _ ih =>
      intro P base stk h
      rw [show compileS (.ite c s₁ s₂) base =
          compileE c ++ [.jz (base + (compileE c).length + 1 +
              (compileS s₁ (base + (compileE c).length + 1)).length + 1)] ++
            compileS s₁ (base + (compileE c).length + 1) ++
            [.jmp (base + (compileE c).length + 1 +
              (compileS s₁ (base + (compileE c).length + 1)).length + 1 +
              (compileS s₂ (base + (compileE c).length + 1 +
                (compileS s₁ (base + (compileE c).length + 1)).length +
                1)).length)] ++
            compileS s₂ (base + (compileE c).length + 1 +
              (compileS s₁ (base + (compileE c).length + 1)).length + 1)
          from rfl] at h
      obtain ⟨hA, hc2⟩ := contains_append h
      obtain ⟨hB, _⟩ := contains_append hA
      obtain ⟨hC, _⟩ := contains_append hB
      obtain ⟨hce, hjz⟩ := contains_append hC
      have m1 := compileE_correct c P base stk σ hce
      have m2 : MStep P (base + (compileE c).length) (eval σ c :: stk) σ
          (base + (compileE c).length + 1 +
            (compileS s₁ (base + (compileE c).length + 1)).length + 1)
          stk σ := by
        rw [show eval σ c = 0 from hc]
        exact .jz0 (contains_head hjz)
      have m3 := ih P
        (base + (compileE c).length + 1 +
          (compileS s₁ (base + (compileE c).length + 1)).length + 1) stk
        (contains_congr hc2 (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega))
      have hlen : base + (compileS (.ite c s₁ s₂) base).length =
          base + (compileE c).length + 1 +
            (compileS s₁ (base + (compileE c).length + 1)).length + 1 +
            (compileS s₂ (base + (compileE c).length + 1 +
              (compileS s₁ (base + (compileE c).length + 1)).length +
              1)).length := by
        simp only [compileS, List.length_append, List.length_cons,
          List.length_nil]
        omega
      rw [hlen]
      exact m1.trans ((MSteps.single m2).trans m3)
  | @whileF c s σ hc =>
      intro P base stk h
      rw [show compileS (.wloop c s) base =
          compileE c ++ [.jz (base + (compileE c).length + 1 +
              (compileS s (base + (compileE c).length + 1)).length + 1)] ++
            compileS s (base + (compileE c).length + 1) ++ [.jmp base]
          from rfl] at h
      obtain ⟨hA, _⟩ := contains_append h
      obtain ⟨hB, _⟩ := contains_append hA
      obtain ⟨hce, hjz⟩ := contains_append hB
      have m1 := compileE_correct c P base stk σ hce
      have m2 : MStep P (base + (compileE c).length) (eval σ c :: stk) σ
          (base + (compileE c).length + 1 +
            (compileS s (base + (compileE c).length + 1)).length + 1)
          stk σ := by
        rw [show eval σ c = 0 from hc]
        exact .jz0 (contains_head hjz)
      have hlen : base + (compileS (.wloop c s) base).length =
          base + (compileE c).length + 1 +
            (compileS s (base + (compileE c).length + 1)).length + 1 := by
        simp only [compileS, List.length_append, List.length_cons,
          List.length_nil]
        omega
      rw [hlen]
      exact m1.trans (MSteps.single m2)
  | @whileT c s σ σ₁ σ₂ hc _ _ ih₁ ih₂ =>
      intro P base stk h
      have hfull := h
      rw [show compileS (.wloop c s) base =
          compileE c ++ [.jz (base + (compileE c).length + 1 +
              (compileS s (base + (compileE c).length + 1)).length + 1)] ++
            compileS s (base + (compileE c).length + 1) ++ [.jmp base]
          from rfl] at h
      obtain ⟨hA, hjmp⟩ := contains_append h
      obtain ⟨hB, hcs⟩ := contains_append hA
      obtain ⟨hce, hjz⟩ := contains_append hB
      have m1 := compileE_correct c P base stk σ hce
      have m2 : MStep P (base + (compileE c).length) (eval σ c :: stk) σ
          (base + (compileE c).length + 1) stk σ :=
        .jzS (contains_head hjz) hc
      have m3 := ih₁ P (base + (compileE c).length + 1) stk
        (contains_congr hcs (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega))
      have m4 : MStep P
          (base + (compileE c).length + 1 +
            (compileS s (base + (compileE c).length + 1)).length)
          stk σ₁ base stk σ₁ := by
        apply MStep.jmp
        exact contains_head (contains_congr hjmp (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega))
      have m5 := ih₂ P base stk hfull
      exact m1.trans ((MSteps.single m2).trans
        (m3.trans ((MSteps.single m4).trans m5)))

/-! ## End-to-end example

The MiniRust program

```rust
let mut x = 3;        // local 0
let mut acc = 1;      // local 1
while 0 < x {
    acc = acc * x;
    x = x + (-1);
}
```
-/

/-- The example program (locals: `x = 0`, `acc = 1`). -/
def prog : Stmt :=
  .seq (.decl 0 true (.int 3))
    (.seq (.decl 1 true (.int 1))
      (.wloop (.less (.int 0) (.var 0))
        (.seq (.assign 1 (.mul (.var 1) (.var 0)))
          (.assign 0 (.add (.var 0) (.int (-1)))))))

/-- The checker accepts it, recording two `mut` locals. -/
example : check [] prog = some [true, true] := by decide

/-- … rejects it if `acc` loses its `mut` (Rust's mutability discipline,
enforced statically) … -/
example :
    check []
      (.seq (.decl 0 true (.int 3))
        (.seq (.decl 1 false (.int 1))
          (.wloop (.less (.int 0) (.var 0))
            (.seq (.assign 1 (.mul (.var 1) (.var 0)))
              (.assign 0 (.add (.var 0) (.int (-1)))))))) = none := by
  decide

/-- … and rejects out-of-scope locals. -/
example : check [] (.assign 0 (.int 1)) = none := by decide

/-- The initial store. -/
def σ0 : Store := fun _ => 0

/-- The source program computes `3! = 6` into `acc` (an explicit big-step
derivation; the loop-guard side conditions are settled by `decide` on the
evolving store). -/
theorem prog_evals : ∃ σ', BigStep prog σ0 σ' ∧ σ' 1 = 6 := by
  refine ⟨_, .seq .decl (.seq .decl
    (.whileT (by decide) (.seq .assign .assign)
      (.whileT (by decide) (.seq .assign .assign)
        (.whileT (by decide) (.seq .assign .assign)
          (.whileF (by decide)))))), ?_⟩
  decide

/-- The compiled machine program. -/
def progCode : List Instr := compileS prog 0

/-- **End to end**: the compiled code, started on the empty stack at
`pc = 0`, halts at the end of the program having computed `acc = 6` —
obtained by instantiating the preservation theorem with the source run. -/
theorem progCode_runs : ∃ σ',
    MSteps progCode 0 [] σ0 progCode.length [] σ' ∧ σ' 1 = 6 := by
  obtain ⟨σ', hb, hv⟩ := prog_evals
  refine ⟨σ', ?_, hv⟩
  have h := compileS_correct hb progCode 0 [] (contains_self progCode)
  simpa using h

end MiniRustC
