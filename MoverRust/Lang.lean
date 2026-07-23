/-
  MoverRust / Lang — a multithreaded mini-Rust and its operational semantics

  The language instantiates the "Mover Logic Language" (MLL) of
  Flanagan & Freund (ECOOP 2024, Figure 6) with a concrete syntax of
  actions in the style of a small Rust subset:

    • global (shared) variables   `x`, including lock words
    • thread-local variables      `r` (per-thread registers; in MLL a
      local `r` of thread `t` is the store variable `r_t`)
    • primitive actions: local computation, global read/write,
      `acquire`/`release` of a lock word, and `cas`
    • statements: `skip`, `wrong` (a failed assertion), sequencing,
      `if`/`while` on conditional actions, procedure calls, `yield`
    • a thread pool `s₁ .. sₙ · σ` with preemptive interleaving

  Assertions are sugar: `assert e = if e then skip else wrong`.  The
  goal of the logic (Logic.lean) is to prove that no thread ever
  reaches `wrong`.
-/
import MoverRust.Effects

namespace MoverRust

/-- Thread identifiers.  A thread's id is its index in the pool. -/
abbrev Tid := Nat

/-- Store variables: shared globals `g n`, and thread-local `l t n`
    (the paper's `r_tid` encoding of locals — a "local" of thread `t`
    is just a store variable only `t` ever touches). -/
inductive Var : Type where
  | g (n : Nat)
  | l (t : Tid) (n : Nat)
deriving DecidableEq, Repr

/-- Shared stores. -/
def Store := Var → Int

/-- Store update. -/
def upd (σ : Store) (v : Var) (k : Int) : Store :=
  fun w => if w = v then k else σ w

@[simp] theorem upd_same (σ : Store) (v : Var) (k : Int) : upd σ v k v = k := by
  simp [upd]

@[simp] theorem upd_other (σ : Store) {v w : Var} (k : Int) (h : w ≠ v) :
    upd σ v k w = σ w := by
  simp [upd, h]

/-- Updates to distinct variables commute. -/
theorem upd_comm (σ : Store) {v w : Var} (a b : Int) (h : v ≠ w) :
    upd (upd σ v a) w b = upd (upd σ w b) v a := by
  funext u
  simp only [upd]
  by_cases hv : u = v <;> by_cases hw : u = w <;>
    simp_all [hv, hw] <;> exact absurd (hv ▸ hw ▸ rfl) h

/-- Expressions over the current thread's locals (globals are accessed
    only through explicit read/write actions, as in the paper's
    compiled examples). -/
inductive Exp : Type where
  | int (k : Int)
  | lv (n : Nat)              -- local variable n of the current thread
  | add (e₁ e₂ : Exp)
  | sub (e₁ e₂ : Exp)
  | mul (e₁ e₂ : Exp)
  | modE (e₁ e₂ : Exp)
  | less (e₁ e₂ : Exp)        -- 1 or 0
  | eq (e₁ e₂ : Exp)          -- 1 or 0
deriving DecidableEq, Repr

/-- Expression evaluation, by thread `t` in store `σ`. -/
def evalE (t : Tid) (σ : Store) : Exp → Int
  | .int k => k
  | .lv n => σ (.l t n)
  | .add e₁ e₂ => evalE t σ e₁ + evalE t σ e₂
  | .sub e₁ e₂ => evalE t σ e₁ - evalE t σ e₂
  | .mul e₁ e₂ => evalE t σ e₁ * evalE t σ e₂
  | .modE e₁ e₂ => evalE t σ e₁ % evalE t σ e₂
  | .less e₁ e₂ => if evalE t σ e₁ < evalE t σ e₂ then 1 else 0
  | .eq e₁ e₂ => if evalE t σ e₁ = evalE t σ e₂ then 1 else 0

/-- Expression evaluation depends only on the current thread's locals. -/
theorem evalE_congr_locals {t : Tid} {σ σ' : Store} (e : Exp)
    (h : ∀ n, σ (.l t n) = σ' (.l t n)) : evalE t σ e = evalE t σ' e := by
  induction e <;> simp_all [evalE]

/-- Updating a global leaves every local untouched, so it does not
    change a thread's expression values. -/
theorem evalE_upd_g {t : Tid} {σ : Store} (x : Nat) (k : Int) (e : Exp) :
    evalE t (upd σ (.g x) k) e = evalE t σ e :=
  evalE_congr_locals e (fun _ => by simp [upd])

/-- Updating another thread's local likewise. -/
theorem evalE_upd_l_other {t u : Tid} {σ : Store} (r : Nat) (k : Int) (e : Exp)
    (h : t ≠ u) : evalE t (upd σ (.l u r) k) e = evalE t σ e :=
  evalE_congr_locals e (fun n => by
    simp only [upd]; rw [if_neg]; intro hc; cases hc; exact h rfl)

/-- Primitive actions.  Each denotes a relation on stores, indexed by
    the executing thread (MLL's `A ⊆ Tid × Store × Store`).  A lock
    word holds `t+1` while thread `t` owns it, `0` when free. -/
inductive Act : Type where
  | lact (r : Nat) (e : Exp)          -- r := e            (locals only)
  | readg (r : Nat) (x : Nat)         -- r := x            (global read)
  | writeg (x : Nat) (e : Exp)        -- x := e            (global write)
  | acquire (m : Nat)                 -- blocks until m = 0, sets m := t+1
  | release (m : Nat)                 -- m := 0
  | casT (x : Nat) (e₁ e₂ : Exp)      -- succeeding cas(x, e₁, e₂)
  | assume (e : Exp) (b : Bool)       -- pure test: e ≠ 0 (b) / e = 0 (¬b)
  | idA                               -- no-op (a failing cas)
deriving DecidableEq, Repr

/-- Denotation of actions:  `den A t σ σ'`  ⇔  `(t, σ, σ') ∈ A`. -/
def den : Act → Tid → Store → Store → Prop
  | .lact r e,     t, σ, σ' => σ' = upd σ (.l t r) (evalE t σ e)
  | .readg r x,    t, σ, σ' => σ' = upd σ (.l t r) (σ (.g x))
  | .writeg x e,   t, σ, σ' => σ' = upd σ (.g x) (evalE t σ e)
  | .acquire m,    t, σ, σ' => σ (.g m) = 0 ∧ σ' = upd σ (.g m) (t + 1)
  | .release m,    _, σ, σ' => σ' = upd σ (.g m) 0
  | .casT x e₁ e₂, t, σ, σ' => σ (.g x) = evalE t σ e₁ ∧
                               σ' = upd σ (.g x) (evalE t σ e₂)
  | .assume e b,   t, σ, σ' => σ' = σ ∧ (if b then evalE t σ e ≠ 0
                                         else evalE t σ e = 0)
  | .idA,          _, σ, σ' => σ' = σ

/-- An action is total if it can step from every store (the paper's
    non-blocking requirement for left-movers). -/
def total (A : Act) : Prop := ∀ t σ, ∃ σ', den A t σ σ'

/-- Conditional actions `C = A₁ ⋄ A₂` (MLL §6): either a boolean test
    or a `cas` whose success/failure selects the branch.  The failure
    action of `cas` is `idA` — a `cas` may nondeterministically fail
    from any state, which is what makes failing `cas` a both-mover. -/
inductive Cond : Type where
  | test (e : Exp)
  | cas (x : Nat) (e₁ e₂ : Exp)
deriving DecidableEq, Repr

/-- The branch action of a conditional: `condA C true = A₁`,
    `condA C false = A₂`. -/
def condA : Cond → Bool → Act
  | .test e, b => .assume e b
  | .cas x e₁ e₂, true => .casT x e₁ e₂
  | .cas _ _ _, false => .idA

/-- `A₁ ∪ A₂` is total: conditionals never block. -/
theorem cond_total (C : Cond) (t : Tid) (σ : Store) :
    ∃ b σ', den (condA C b) t σ σ' := by
  cases C with
  | test e =>
      by_cases h : evalE t σ e = 0
      · exact ⟨false, σ, rfl, h⟩
      · exact ⟨true, σ, rfl, h⟩
  | cas x e₁ e₂ => exact ⟨false, σ, rfl⟩

/-- Statements (MLL Figure 6). -/
inductive Stmt : Type where
  | skip
  | wrong
  | act (A : Act)
  | seq (s₁ s₂ : Stmt)
  | ite (C : Cond) (s₁ s₂ : Stmt)
  | wloop (C : Cond) (s : Stmt)
  | call (f : Nat)
  | yld
deriving DecidableEq, Repr

/-- `assert e`  =  `if e then skip else wrong`. -/
def assertS (e : Exp) : Stmt := .ite (.test e) .skip .wrong

/-- Function bodies (the semantics needs only bodies; specifications
    live in Logic.lean). -/
def FnTable := Nat → Option Stmt

/-! ### Small-step semantics of one thread

We use structural congruence on the left of `;` in place of the
paper's evaluation contexts `E ::= • | E; s`. -/

/-- `step F t s σ s' σ'` — thread `t` makes one step (MLL Figure 6). -/
inductive step (F : FnTable) (t : Tid) : Stmt → Store → Stmt → Store → Prop where
  | seqSkip (s₂ : Stmt) (σ : Store) :
      step F t (.seq .skip s₂) σ s₂ σ
  | seqCong {s₁ σ s₁' σ'} (s₂ : Stmt) :
      step F t s₁ σ s₁' σ' →
      step F t (.seq s₁ s₂) σ (.seq s₁' s₂) σ'
  | yld (σ : Store) : step F t .yld σ .skip σ
  | act {A σ σ'} : den A t σ σ' → step F t (.act A) σ .skip σ'
  | iteS {C : Cond} {b σ σ'} (s₁ s₂ : Stmt) :
      den (condA C b) t σ σ' →
      step F t (.ite C s₁ s₂) σ (if b then s₁ else s₂) σ'
  | wloopUnfold (C : Cond) (s : Stmt) (σ : Store) :
      step F t (.wloop C s) σ (.ite C (.seq s (.wloop C s)) .skip) σ
  | call {f body σ} : F f = some body → step F t (.call f) σ body σ

/-! ### Redex classification -/

/-- The redex is `wrong`: the thread has failed. -/
inductive IsWrong : Stmt → Prop where
  | wrong : IsWrong .wrong
  | seq {s₁} (s₂ : Stmt) : IsWrong s₁ → IsWrong (.seq s₁ s₂)

/-- The redex is `yield`. -/
inductive AtYield : Stmt → Prop where
  | yld : AtYield .yld
  | seq {s₁} (s₂ : Stmt) : AtYield s₁ → AtYield (.seq s₁ s₂)

/-- A thread is *yielding* if it is at a yield point or has terminated
    (the paper's `N_i` also counts failed threads; see `Parked`). -/
def Yielding (s : Stmt) : Prop := AtYield s ∨ s = .skip

/-- Parked threads: yielding, terminated, or failed.  The
    non-preemptive scheduler may switch only when the active thread is
    parked. -/
def Parked (s : Stmt) : Prop := AtYield s ∨ s = .skip ∨ IsWrong s

/-- Wrong threads cannot step. -/
theorem step_not_wrong {F t s σ s' σ'} (h : step F t s σ s' σ') :
    ¬ IsWrong s := by
  induction h with
  | seqSkip => intro hw; cases hw with | seq _ hw' => cases hw'
  | seqCong _ _ ih => intro hw; cases hw with | seq _ hw' => exact ih hw'
  | yld => intro hw; cases hw
  | act => intro hw; cases hw
  | iteS => intro hw; cases hw
  | wloopUnfold => intro hw; cases hw
  | call => intro hw; cases hw

theorem IsWrong.no_step {F t s σ s' σ'} (hw : IsWrong s) :
    ¬ step F t s σ s' σ' := fun h => step_not_wrong h hw

/-- Skip cannot step. -/
theorem skip_no_step {F t σ s' σ'} : ¬ step F t .skip σ s' σ' := by
  intro h; cases h

/-! ### Thread pools -/

/-- A program state `Σ = s₁..sₙ · σ`. -/
structure State : Type where
  threads : List Stmt
  store : Store

/-- Preemptive interleaving: any thread may step at any time
    (MLL rule [E-State]).  The thread's id is its pool index. -/
inductive pstep (F : FnTable) : State → State → Prop where
  | mk {ss σ σ' s s'} (t : Tid) :
      ss.get? t = some s →
      step F t s σ s' σ' →
      pstep F ⟨ss, σ⟩ ⟨ss.set t s', σ'⟩

/-- A state is wrong if some thread has failed. -/
def StateWrong (st : State) : Prop := ∃ s ∈ st.threads, IsWrong s

/-- Reflexive–transitive closure of a relation. -/
inductive Multi {α : Type _} (R : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Multi R a a
  | head {a b c} : R a b → Multi R b c → Multi R a c

theorem Multi.tail {α : Type _} {R : α → α → Prop} {a b c : α} :
    Multi R a b → R b c → Multi R a c := by
  intro hab hbc
  induction hab with
  | refl => exact .head hbc (.refl _)
  | head h _ ih => exact .head h (ih hbc)

theorem Multi.trans {α : Type _} {R : α → α → Prop} {a b c : α} :
    Multi R a b → Multi R b c → Multi R a c := by
  intro hab hbc
  induction hab with
  | refl => exact hbc
  | head h _ ih => exact .head h (ih hbc)

/-! ### List utilities (get?/set) used throughout -/

theorem get?_lt {α : Type _} {l : List α} {n : Nat} {a : α}
    (h : l.get? n = some a) : n < l.length := by
  cases Nat.lt_or_ge n l.length with
  | inl h' => exact h'
  | inr h' => rw [List.get?_eq_none.mpr h'] at h; cases h

theorem get?_set_self {α : Type _} {l : List α} {n : Nat} {a : α}
    (h : n < l.length) : (l.set n a).get? n = some a := by
  rw [List.get?_eq_getElem?]
  exact List.getElem?_set_eq (by simpa using h)

theorem get?_set_other {α : Type _} {l : List α} {n m : Nat} {a : α}
    (h : n ≠ m) : (l.set n a).get? m = l.get? m := by
  rw [List.get?_eq_getElem?, List.get?_eq_getElem?]
  exact List.getElem?_set_ne h

/-- `Σ` goes wrong if it can reach a wrong state. -/
def GoesWrong (F : FnTable) (st : State) : Prop :=
  ∃ st', Multi (pstep F) st st' ∧ StateWrong st'

end MoverRust
