/-!
# Chapter 5: The Untyped Lambda-Calculus

Syntax and operational semantics of the pure untyped lambda-calculus:
call-by-value evaluation (TAPL figure 5-3), full beta-reduction, a
normal-order normalizer, and the classic Church encodings.

TAPL chapter 5 works with named variables and defines substitution up to
alpha-conversion; the nameless (de Bruijn) representation only appears in
chapter 6. In a proof assistant it is easiest to use de Bruijn indices from
the start, so this chapter already adopts them; chapter 6 then studies the
shifting and substitution operations in their own right.
-/

namespace Chapter05

/-- Terms of the untyped lambda-calculus, with de Bruijn indices:
`var n` refers to the `n`-th enclosing binder. -/
inductive Term : Type where
  | var (n : Nat)
  | abs (t : Term)
  | app (t₁ t₂ : Term)
  deriving Repr, DecidableEq

namespace Term

/-- `#n` is the de Bruijn variable `n`. -/
scoped prefix:max "#" => Term.var
/-- `ƛ t` is the lambda-abstraction with body `t` (binding index 0). -/
scoped prefix:65 "ƛ " => Term.abs
/-- `t ⬝ s` is application. -/
scoped infixl:70 " ⬝ " => Term.app

/-- Shift by `d` the variables of `t` that are `≥ c` ("d-place shift above
cutoff c", TAPL definition 6.2.1 — used here already because beta-reduction
needs it). -/
def shift (d c : Nat) : Term → Term
  | var n => if n < c then var n else var (n + d)
  | abs t => abs (shift d (c + 1) t)
  | app t₁ t₂ => app (shift d c t₁) (shift d c t₂)

/-- Beta-substitution `[k ↦ s] t`: replace variable `k` by `s` (shifted into
place), decrementing the free variables above `k` — this fuses TAPL's
`↑⁻¹([0 ↦ ↑¹ s] t)` into a single traversal. -/
def subst (k : Nat) (s : Term) : Term → Term
  | var n =>
      if n < k then var n
      else if n = k then shift k 0 s
      else var (n - 1)
  | abs t => abs (subst (k + 1) s t)
  | app t₁ t₂ => app (subst k s t₁) (subst k s t₂)

end Term

open Term

/-- Values: in the pure lambda-calculus every abstraction is a value
(TAPL fig. 5-3). -/
inductive Value : Term → Prop where
  | abs (t : Term) : Value (ƛ t)

/-- Call-by-value single-step evaluation (TAPL fig. 5-3): reduce the
function position, then the argument, then apply. -/
inductive Step : Term → Term → Prop where
  | appAbs {t v : Term} : Value v → Step ((ƛ t) ⬝ v) (subst 0 v t)
  | app1 {t₁ t₁' t₂ : Term} : Step t₁ t₁' → Step (t₁ ⬝ t₂) (t₁' ⬝ t₂)
  | app2 {v t t' : Term} : Value v → Step t t' → Step (v ⬝ t) (v ⬝ t')

@[inherit_doc] scoped infix:50 " ⟶ " => Step

/-- Reflexive–transitive closure of an arbitrary reduction relation. -/
inductive Multi (R : Term → Term → Prop) : Term → Term → Prop where
  | refl (t : Term) : Multi R t t
  | head {t t' t'' : Term} : R t t' → Multi R t' t'' → Multi R t t''

/-- Multi-step call-by-value evaluation. -/
scoped infix:50 " ⟶* " => Multi Step

namespace Multi

theorem single {R : Term → Term → Prop} {t t' : Term} (h : R t t') :
    Multi R t t' :=
  .head h (.refl t')

theorem trans {R : Term → Term → Prop} {t t' t'' : Term}
    (h₁ : Multi R t t') (h₂ : Multi R t' t'') : Multi R t t'' := by
  induction h₁ with
  | refl _ => exact h₂
  | head s _ ih => exact .head s (ih h₂)

end Multi

/-- Values do not step (they are final results). -/
theorem Value.not_step {v t : Term} (hv : Value v) : ¬ v ⟶ t := by
  cases hv; intro h; cases h

/-- Call-by-value evaluation is deterministic. -/
theorem Step.deterministic {t t₁ t₂ : Term} (h₁ : t ⟶ t₁) (h₂ : t ⟶ t₂) :
    t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | appAbs hv => cases h₂ with
    | appAbs _ => rfl
    | app1 h => exact absurd h (Value.abs _).not_step
    | app2 _ h => exact absurd h hv.not_step
  | app1 h ih => cases h₂ with
    | appAbs _ => exact absurd h (Value.abs _).not_step
    | app1 h' => rw [ih h']
    | app2 hv _ => exact absurd h hv.not_step
  | app2 hv h ih => cases h₂ with
    | appAbs hv' => exact absurd h hv'.not_step
    | app1 h' => exact absurd h' hv.not_step
    | app2 _ h' => rw [ih h']

/-! ## Full beta-reduction

Full beta-reduction (TAPL §5.3, exercise 5.3.6) may contract any redex,
anywhere in the term — including under binders. -/

/-- Full beta-reduction: contract any redex anywhere. -/
inductive FullBeta : Term → Term → Prop where
  | beta {t s : Term} : FullBeta ((ƛ t) ⬝ s) (subst 0 s t)
  | absCong {t t' : Term} : FullBeta t t' → FullBeta (ƛ t) (ƛ t')
  | app1 {t₁ t₁' t₂ : Term} : FullBeta t₁ t₁' → FullBeta (t₁ ⬝ t₂) (t₁' ⬝ t₂)
  | app2 {t₁ t₂ t₂' : Term} : FullBeta t₂ t₂' → FullBeta (t₁ ⬝ t₂) (t₁ ⬝ t₂')

@[inherit_doc] scoped infix:50 " ⟶β " => FullBeta
/-- Multi-step full beta-reduction. -/
scoped infix:50 " ⟶β* " => Multi FullBeta

/-- Every call-by-value step is a full-beta step. -/
theorem Step.toFullBeta {t t' : Term} (h : t ⟶ t') : t ⟶β t' := by
  induction h with
  | appAbs _ => exact .beta
  | app1 _ ih => exact .app1 ih
  | app2 _ _ ih => exact .app2 ih

/-! ## A normal-order normalizer

Because full beta-reduction is not deterministic, it is convenient to have an
executable *strategy* for it. Normal order (leftmost-outermost) reaches the
normal form whenever one exists, and lets us verify Church-encoding
computations below by `decide`/`rfl`. -/

/-- One normal-order (leftmost-outermost) reduction step, or `none` if the
term is a beta-normal form. -/
def nreduce : Term → Option Term
  | var _ => none
  | abs t => (nreduce t).map abs
  | app (abs t) s => some (subst 0 s t)
  | app (var n) t₂ => (nreduce t₂).map (app (var n))
  | app (app s₁ s₂) t₂ =>
      match nreduce (app s₁ s₂) with
      | some t₁' => some (app t₁' t₂)
      | none => (nreduce t₂).map (app (app s₁ s₂))

/-- Iterate `nreduce` for at most `fuel` steps; `some u` means the normal
form `u` was reached. -/
def normalize (fuel : Nat) (t : Term) : Option Term :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match nreduce t with
      | none => some t
      | some t' => normalize fuel t'

/-- `nreduce` is sound: it performs full-beta steps. -/
theorem nreduce_sound : ∀ {t t' : Term}, nreduce t = some t' → t ⟶β t' := by
  intro t
  induction t with
  | var n => intro t' h; simp [nreduce] at h
  | abs t ih =>
      intro t' h
      simp [nreduce, Option.map_eq_some'] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .absCong (ih hu)
  | app t₁ t₂ ih₁ ih₂ =>
      intro t' h
      cases t₁ with
      | abs t =>
          simp [nreduce] at h
          rw [← h]; exact .beta
      | var n =>
          simp [nreduce, Option.map_eq_some'] at h
          obtain ⟨u, hu, rfl⟩ := h
          exact .app2 (ih₂ hu)
      | app s₁ s₂ =>
          rw [show nreduce ((s₁ ⬝ s₂) ⬝ t₂) =
                match nreduce (s₁ ⬝ s₂) with
                | some t₁' => some (t₁' ⬝ t₂)
                | none => (nreduce t₂).map (app (s₁ ⬝ s₂)) from rfl] at h
          cases hr : nreduce (s₁ ⬝ s₂) with
          | some u =>
              rw [hr] at h
              cases h
              exact .app1 (ih₁ hr)
          | none =>
              rw [hr, Option.map_eq_some'] at h
              obtain ⟨u, hu, rfl⟩ := h
              exact .app2 (ih₂ hu)

/-- A term is a beta-normal form if no full-beta step applies. -/
def BetaNormal (t : Term) : Prop := ¬ ∃ t', t ⟶β t'

/-- `nreduce` is complete: if it finds no redex, the term is beta-normal. -/
theorem nreduce_none_normal : ∀ {t : Term}, nreduce t = none → BetaNormal t := by
  intro t
  induction t with
  | var n => intro _ ⟨t', h⟩; cases h
  | abs t ih =>
      intro h ⟨t', hstep⟩
      simp [nreduce, Option.map_eq_none'] at h
      cases hstep with
      | absCong hstep => exact ih h ⟨_, hstep⟩
  | app t₁ t₂ ih₁ ih₂ =>
      intro h ⟨t', hstep⟩
      cases t₁ with
      | abs t => simp [nreduce] at h
      | var n =>
          simp [nreduce, Option.map_eq_none'] at h
          cases hstep with
          | app1 hstep => cases hstep
          | app2 hstep => exact ih₂ h ⟨_, hstep⟩
      | app s₁ s₂ =>
          rw [show nreduce ((s₁ ⬝ s₂) ⬝ t₂) =
                match nreduce (s₁ ⬝ s₂) with
                | some t₁' => some (t₁' ⬝ t₂)
                | none => (nreduce t₂).map (app (s₁ ⬝ s₂)) from rfl] at h
          cases hr : nreduce (s₁ ⬝ s₂) with
          | some u => rw [hr] at h; cases h
          | none =>
              rw [hr, Option.map_eq_none'] at h
              cases hstep with
              | app1 hstep => exact ih₁ hr ⟨_, hstep⟩
              | app2 hstep => exact ih₂ h ⟨_, hstep⟩

/-- `normalize` is sound: a returned term is reached by full beta-reduction
and is a beta-normal form. -/
theorem normalize_sound : ∀ {fuel : Nat} {t u : Term},
    normalize fuel t = some u → (t ⟶β* u) ∧ BetaNormal u := by
  intro fuel
  induction fuel with
  | zero => intro t u h; simp [normalize] at h
  | succ fuel ih =>
      intro t u h
      rw [show normalize (fuel + 1) t =
            match nreduce t with
            | none => some t
            | some t' => normalize fuel t' from rfl] at h
      cases hr : nreduce t with
      | none =>
          rw [hr] at h; cases h
          exact ⟨.refl _, nreduce_none_normal hr⟩
      | some t' =>
          rw [hr] at h
          obtain ⟨hmulti, hnf⟩ := ih h
          exact ⟨.head (nreduce_sound hr) hmulti, hnf⟩

/-! ## Programming in the lambda-calculus: Church encodings (TAPL §5.2)

In named syntax:  `tru = λt.λf.t`, `fls = λt.λf.f`, `and = λb.λc. b c fls`,
`pair = λf.λs.λb. b f s`, `c₂ = λs.λz. s (s z)`, `plus = λm.λn.λs.λz. m s (n s z)`,
`times = λm.λn. m (plus n) c₀`, `omega = (λx. x x)(λx. x x)`. -/

/-- Identity: `λx. x`. -/
def id' : Term := ƛ #0
/-- Church true: `λt.λf. t`. -/
def tru : Term := ƛ ƛ #1
/-- Church false: `λt.λf. f`. -/
def fls : Term := ƛ ƛ #0
/-- Boolean conditional: `λl.λm.λn. l m n`. -/
def test : Term := ƛ ƛ ƛ #2 ⬝ #1 ⬝ #0
/-- Conjunction: `λb.λc. b c fls`. -/
def and' : Term := ƛ ƛ #1 ⬝ #0 ⬝ fls
/-- Disjunction: `λb.λc. b tru c`. -/
def or' : Term := ƛ ƛ #1 ⬝ tru ⬝ #0
/-- Negation: `λb. b fls tru`. -/
def not' : Term := ƛ #0 ⬝ fls ⬝ tru
/-- Pairing: `λf.λs.λb. b f s`. -/
def pair : Term := ƛ ƛ ƛ #0 ⬝ #2 ⬝ #1
/-- First projection: `λp. p tru`. -/
def fst' : Term := ƛ #0 ⬝ tru
/-- Second projection: `λp. p fls`. -/
def snd' : Term := ƛ #0 ⬝ fls

/-- Church numeral `n`: `λs.λz. sⁿ z`. -/
def church (n : Nat) : Term :=
  ƛ ƛ go n
where go : Nat → Term
  | 0 => #0
  | n + 1 => #1 ⬝ go n

/-- Successor: `λn.λs.λz. s (n s z)`. -/
def scc : Term := ƛ ƛ ƛ #1 ⬝ (#2 ⬝ #1 ⬝ #0)
/-- Addition: `λm.λn.λs.λz. m s (n s z)`. -/
def plus : Term := ƛ ƛ ƛ ƛ #3 ⬝ #1 ⬝ (#2 ⬝ #1 ⬝ #0)
/-- Multiplication: `λm.λn. m (plus n) c₀`. -/
def times : Term := ƛ ƛ #1 ⬝ (plus ⬝ #0) ⬝ church 0
/-- Zero test: `λm. m (λx. fls) tru`. -/
def iszro : Term := ƛ #0 ⬝ (ƛ fls) ⬝ tru
/-- The divergent term `omega` (TAPL §5.2): it steps to itself forever. -/
def omega : Term := (ƛ #0 ⬝ #0) ⬝ (ƛ #0 ⬝ #0)

/-! ### Examples -/

/-- `id (id id)` evaluates call-by-value to `id`. -/
example : id' ⬝ (id' ⬝ id') ⟶* id' :=
  .head (.app2 (.abs _) (.appAbs (.abs _))) (.head (.appAbs (.abs _)) (.refl _))

/-- `and tru fls ⟶* fls`, step by explicit call-by-value step. -/
example : and' ⬝ tru ⬝ fls ⟶* fls :=
  .head (.app1 (.appAbs (.abs _)))          -- (λc. tru c fls) fls
    (.head (.appAbs (.abs _))               -- tru fls fls
      (.head (.app1 (.appAbs (.abs _)))     -- (λf. fls) fls
        (.head (.appAbs (.abs _))           -- fls
          (.refl _))))

/-- `omega` steps to itself: evaluation of `omega` never terminates. -/
example : omega ⟶ omega := .appAbs (.abs _)

/-- Church-encoded computations, checked by running the normalizer
(soundness of `normalize` connects these to `⟶β*`):
`succ 0 = 1`, `1 + 1 = 2`, `2 × 3 = 6`, `not (and tru (not fls)) = fls`,
`iszero 0 = tru`, `fst (pair tru fls) = tru`. -/
example : normalize 100 (scc ⬝ church 0) = some (church 1) := by decide
example : normalize 100 (plus ⬝ church 1 ⬝ church 1) = some (church 2) := by decide
example : normalize 100 (times ⬝ church 2 ⬝ church 3) = some (church 6) := by decide
example : normalize 100 (not' ⬝ (and' ⬝ tru ⬝ (not' ⬝ fls))) = some fls := by decide
example : normalize 100 (iszro ⬝ church 0) = some tru := by decide
example : normalize 100 (fst' ⬝ (pair ⬝ tru ⬝ fls)) = some tru := by decide

/-- `omega` has no normal form — the normalizer runs out of fuel. -/
example : normalize 100 omega = none := by decide

end Chapter05
