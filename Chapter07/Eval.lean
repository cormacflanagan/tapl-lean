import Chapter06.DeBruijn

/-!
# Chapter 7: An ML Implementation of the Lambda-Calculus

TAPL chapter 7 turns the call-by-value semantics of chapter 5 into an OCaml
program. Here the "implementation" is a Lean function `eval1 : Term →
Option Term` — and unlike the OCaml version, it comes with a proof that it
computes *exactly* the one-step evaluation relation `⟶`, plus a fuel-bounded
driver `eval` whose results provably are normal forms reached by `⟶*`.

We also prove the untyped analogue of the progress theorem: a closed term is
either a value or can take a step, so the evaluator only ever "gets stuck"
on open terms or on the non-value normal forms they create.
-/

namespace Chapter07

open Chapter05 Chapter05.Term Chapter06

/-- Boolean test for values (abstractions), mirroring TAPL's `isval`. -/
def isValue : Term → Bool
  | abs _ => true
  | _ => false

/-- `isValue` decides the `Value` predicate. -/
theorem isValue_iff {t : Term} : isValue t = true ↔ Value t := by
  cases t with
  | var n => simp [isValue]; intro h; cases h
  | abs t => simp [isValue]; exact .abs t
  | app t₁ t₂ => simp [isValue]; intro h; cases h

/-- A term that steps is not a value. -/
theorem isValue_false_of_step {t t' : Term} (h : t ⟶ t') :
    isValue t = false := by
  cases ht : isValue t
  · rfl
  · exact absurd h (isValue_iff.mp ht).not_step

/-- Single-step call-by-value evaluator, mirroring TAPL's `eval1`:
`none` means no rule applies (the term is a normal form). -/
def eval1 : Term → Option Term
  | app (abs t) t₂ =>
      if isValue t₂ then some (subst 0 t₂ t)
      else (eval1 t₂).map (app (abs t))
  | app t₁ t₂ => (eval1 t₁).map (fun t₁' => app t₁' t₂)
  | _ => none

/-- `eval1` is sound: it only performs `⟶` steps. -/
theorem eval1_sound : ∀ {t t' : Term}, eval1 t = some t' → t ⟶ t' := by
  intro t
  induction t with
  | var n => intro t' h; simp [eval1] at h
  | abs t _ => intro t' h; simp [eval1] at h
  | app t₁ t₂ ih₁ ih₂ =>
      intro t' h
      cases t₁ with
      | abs t =>
          rw [show eval1 ((ƛ t) ⬝ t₂) =
                if isValue t₂ then some (subst 0 t₂ t)
                else (eval1 t₂).map (app (ƛ t)) from rfl] at h
          by_cases hv : isValue t₂
          · rw [if_pos hv] at h
            cases h
            exact .appAbs (isValue_iff.mp hv)
          · rw [if_neg hv, Option.map_eq_some'] at h
            obtain ⟨u, hu, rfl⟩ := h
            exact .app2 (.abs t) (ih₂ hu)
      | var n =>
          simp [eval1] at h
      | app s₁ s₂ =>
          rw [show eval1 ((s₁ ⬝ s₂) ⬝ t₂) =
                (eval1 (s₁ ⬝ s₂)).map (fun t₁' => t₁' ⬝ t₂) from rfl,
              Option.map_eq_some'] at h
          obtain ⟨u, hu, rfl⟩ := h
          exact .app1 (ih₁ hu)

/-- `eval1` is complete: it finds every `⟶` step. -/
theorem eval1_complete {t t' : Term} (h : t ⟶ t') : eval1 t = some t' := by
  induction h with
  | @appAbs t v hv =>
      have : isValue v = true := isValue_iff.mpr hv
      simp [eval1, this]
  | @app1 t₁ t₁' t₂ h ih =>
      cases t₁ with
      | var n => cases h
      | abs t => exact absurd h (Value.abs t).not_step
      | app s₁ s₂ =>
          rw [show eval1 ((s₁ ⬝ s₂) ⬝ t₂) =
                (eval1 (s₁ ⬝ s₂)).map (fun t₁' => t₁' ⬝ t₂) from rfl, ih]
          rfl
  | @app2 v t t'' hv h ih =>
      cases hv with
      | abs u =>
          rw [show eval1 ((ƛ u) ⬝ t) =
                if isValue t then some (subst 0 t u)
                else (eval1 t).map (app (ƛ u)) from rfl,
              if_neg (by simp [isValue_false_of_step h]), ih]
          rfl

/-- A term is a (call-by-value) normal form if no rule applies. -/
def NormalForm (t : Term) : Prop := ¬ ∃ t', t ⟶ t'

/-- `eval1` returns `none` exactly on normal forms — a direct corollary of
soundness and completeness. -/
theorem eval1_none_iff {t : Term} : eval1 t = none ↔ NormalForm t := by
  constructor
  · intro h ⟨t', hstep⟩
    rw [eval1_complete hstep] at h
    cases h
  · intro h
    cases he : eval1 t with
    | none => rfl
    | some t' => exact absurd ⟨t', eval1_sound he⟩ h

/-! ## Progress for closed terms

The untyped calculus has no preservation/progress *theorem pair* (there are
no types yet!), but the following analogue of progress explains when the
evaluator can get stuck: never on closed terms until it reaches a value. -/

/-- **Progress, untyped version**: a closed term is a value or steps. -/
theorem progress : ∀ {t : Term}, Closed 0 t → Value t ∨ ∃ t', t ⟶ t' := by
  intro t
  induction t with
  | var n => intro hc; simp [Closed] at hc; omega
  | abs t _ => intro _; exact .inl (.abs t)
  | app t₁ t₂ ih₁ ih₂ =>
      intro hc
      have hc' : Closed 0 t₁ ∧ Closed 0 t₂ := hc
      rcases ih₁ hc'.1 with hv₁ | ⟨t₁', h₁⟩
      · rcases ih₂ hc'.2 with hv₂ | ⟨t₂', h₂⟩
        · cases hv₁ with
          | abs t => exact .inr ⟨_, .appAbs hv₂⟩
        · exact .inr ⟨_, .app2 hv₁ h₂⟩
      · exact .inr ⟨_, .app1 h₁⟩

/-- Closed normal forms are values. -/
theorem closed_normal_value {t : Term} (hc : Closed 0 t)
    (hn : NormalForm t) : Value t := by
  rcases progress hc with hv | hstep
  · exact hv
  · exact absurd hstep hn

/-! ## The evaluation function

TAPL's `eval` repeatedly applies `eval1` until no rule applies. In Lean all
functions are total, so we bound the iteration with fuel; `some u` means the
normal form `u` was reached. -/

/-- Iterated evaluation with fuel, mirroring TAPL's `eval`. -/
def eval (fuel : Nat) (t : Term) : Option Term :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match eval1 t with
      | none => some t
      | some t' => eval fuel t'

/-- `eval` is sound: a returned term is a normal form reached by `⟶*`. -/
theorem eval_sound : ∀ {fuel : Nat} {t u : Term},
    eval fuel t = some u → (t ⟶* u) ∧ NormalForm u := by
  intro fuel
  induction fuel with
  | zero => intro t u h; simp [eval] at h
  | succ fuel ih =>
      intro t u h
      rw [show eval (fuel + 1) t =
            match eval1 t with
            | none => some t
            | some t' => eval fuel t' from rfl] at h
      cases he : eval1 t with
      | none =>
          rw [he] at h; cases h
          exact ⟨.refl _, eval1_none_iff.mp he⟩
      | some t' =>
          rw [he] at h
          obtain ⟨hmulti, hnf⟩ := ih h
          exact ⟨.head (eval1_sound he) hmulti, hnf⟩

/-- On closed terms, `eval` can only produce values (combine `eval_sound`,
`Step.closed`, and `closed_normal_value`). -/
theorem eval_closed_value {fuel : Nat} {t u : Term} (hc : Closed 0 t)
    (h : eval fuel t = some u) : Value u := by
  obtain ⟨hmulti, hnf⟩ := eval_sound h
  have hcu : Closed 0 u := by
    clear h hnf
    induction hmulti with
    | refl _ => exact hc
    | head s _ ih => exact ih (Step.closed s hc)
  exact closed_normal_value hcu hnf

/-! ## Examples -/

/-- One step of the evaluator on `(λ.0) (λ.0)`. -/
example : eval1 (id' ⬝ id') = some id' := by decide

/-- `id (id id)` evaluates to `id`. -/
example : eval 10 (id' ⬝ (id' ⬝ id')) = some id' := by decide

/-- Church-boolean program: `not (and tru (not fls))` runs (call-by-value!)
to `fls`. -/
example : eval 100 (not' ⬝ (and' ⬝ tru ⬝ (not' ⬝ fls))) = some fls := by decide

/-- `fst (pair tru fls)` evaluates to `tru`. -/
example : eval 100 (fst' ⬝ (pair ⬝ tru ⬝ fls)) = some tru := by decide

/-- `omega` never finishes — the fuel runs out and `eval` gives up. -/
example : eval 100 omega = none := by decide

/-- A *stuck* open term: the variable `#0` is a normal form but not a value;
the evaluator stops without producing a value. -/
example : eval1 (#0) = none ∧ ¬ Value (#0) :=
  ⟨rfl, fun h => nomatch h⟩

end Chapter07
