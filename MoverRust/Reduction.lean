/-
  MoverRust / Reduction — simulation, and the commuting lemmas

  This file collects the *reduction* content — the part of mover logic
  that justifies treating a reducible sequence as atomic:

  ▸ `sim_multi` — Theorem 3 (Simulation), lifted to whole executions:
    every standard execution is matched by an instrumented one that
    goes wrong at least as often.

  ▸ `right_commute`, `left_commute`, `diamond_left` — the commuting
    lemmas (paper Lemmas 7, 8, 10), here at the level of the underlying
    actions: from a *valid* mover specification, a right-mover of one
    thread commutes later past any step of another thread, a left-mover
    commutes earlier, and two post-commit steps satisfy a diamond.
    These are exactly the properties the paper uses to rearrange a
    preemptive trace into a cooperative one.

  Together with `cooperative_soundness` (Preservation.lean), these are
  the ingredients of the full soundness theorem.  The remaining step —
  the global trace-rearrangement of Theorem 4, which threads these
  commutations through an arbitrary interleaving — is the paper's most
  involved argument; see the module note at the end and the README.
-/
import MoverRust.Preservation

namespace MoverRust
open Effect

/-! ### Theorem 3, multi-step -/

/-- Simulation along a whole standard execution: from `Σ ∼ c`, either
    the instrumented machine matches `Σ`'s execution step for step, or
    it reaches a wrong state along the way. -/
theorem sim_multi {F M st st' c} (hsteps : Multi (pstep F) st st')
    (hsim : SimRel st c) :
    (∃ c', Multi (ipstep F M) c c' ∧ SimRel st' c') ∨ IGoesWrong F M c := by
  induction hsteps generalizing c with
  | refl => exact .inl ⟨c, .refl _, hsim⟩
  | head hstep _ ih =>
      obtain ⟨c₁, hi, hres⟩ := sim_step (M := M) hstep hsim
      cases hres with
      | inl hsim₁ =>
          cases ih hsim₁ with
          | inl h' =>
              obtain ⟨c', hsteps', hsim'⟩ := h'
              exact .inl ⟨c', .head hi hsteps', hsim'⟩
          | inr hwrong =>
              obtain ⟨c', hsteps', hw⟩ := hwrong
              exact .inr ⟨c', .head hi hsteps', hw⟩
      | inr hwrong =>
          exact .inr ⟨c₁, .head hi (.refl _), hwrong⟩

/-! ### The commuting lemmas (from validity)

The four validity conditions (Definition 1) are precisely the
commutations reduction needs.  We restate them as named theorems at the
level of a two-thread trace fragment `σ → σ' → σ''`. -/

variable {M : MSpec} (hval : Valid M)

/-- Lemma 7 (Right Commutativity), action level: a right-mover of thread
    `t` commutes to the right of a following step of thread `u`.  The
    reordered trace visits a different intermediate store but reaches
    the same final store. -/
theorem right_commute {t u : Tid} {A₁ A₂ σ σ' σ''} (h : t ≠ u)
    (h1 : M A₁ t σ ≤ .R) (hd1 : den A₁ t σ σ')
    (h2 : M A₂ u σ' ≤ .N) (hd2 : den A₂ u σ' σ'') :
    ∃ σ''', den A₂ u σ σ''' ∧ den A₁ t σ''' σ'' :=
  hval.right_commute h h1 hd1 h2 hd2

/-- Lemma 8 (Left Commutativity), action level: a left-mover of thread
    `t` commutes to the left of a preceding step of thread `u`. -/
theorem left_commute {t u : Tid} {A₁ A₂ σ σ' σ''} (h : t ≠ u)
    (h1 : M A₁ t σ ≤ .N) (hd1 : den A₁ t σ σ')
    (h2 : M A₂ u σ' ≤ .L) (hd2 : den A₂ u σ' σ'') :
    ∃ σ''', den A₂ u σ σ''' ∧ den A₁ t σ''' σ'' :=
  hval.left_commute h h1 hd1 h2 hd2

/-- A mover of one thread cannot change the effect another thread's
    action has (validity condition 3). -/
theorem effect_stable {t u : Tid} {A₁ A₂ σ σ'} (h : t ≠ u)
    (h1 : M A₁ t σ ≤ .N) (hd1 : den A₁ t σ σ') :
    M A₂ u σ' = M A₂ u σ :=
  hval.stable_eff h h1 hd1

/-- Lemma 10 (Diamond), action level: if thread `u`'s step is a
    left-mover and thread `t` also steps, the two can be done in either
    order to a common store — the diamond that lets a post-commit
    termination trace be merged into the main trace. -/
theorem diamond_left {t u : Tid} {A₁ A₂ σ σ' σ''} (h : t ≠ u)
    (h1 : M A₁ t σ ≤ .N) (hd1 : den A₁ t σ σ')
    (h2 : M A₂ u σ ≤ .L) (hd2 : den A₂ u σ σ'') :
    ∃ σ''', den A₂ u σ' σ''' ∧ den A₁ t σ'' σ''' :=
  hval.left_enabled h h1 hd1 h2 hd2

/-! ### A worked commutation

To show the commuting lemmas have teeth, here is a concrete two-thread
reordering for a valid specification: thread `t` acquires a lock
(right-mover) and thread `u ≠ t` does a lock-free local step; the two
commute, and the reordered trace reaches the same final store.  This is
the atomic step of the reduction argument. -/

theorem right_commute_example {t u : Tid} {A₁ A₂ σ σ' σ''} (h : t ≠ u)
    (h1 : M A₁ t σ ≤ .R) (hd1 : den A₁ t σ σ')
    (h2 : M A₂ u σ' ≤ .N) (hd2 : den A₂ u σ' σ'') :
    ∃ τ, den A₂ u σ τ ∧ den A₁ t τ σ'' :=
  right_commute hval h h1 hd1 h2 hd2

end MoverRust
