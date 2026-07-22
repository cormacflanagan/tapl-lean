/-
  MoverRust / Logic — mover logic: specifications, validity, proof rules

  Flanagan & Freund (ECOOP 2024), Sections 7–8.

  ▸ A *mover specification* `M : Act → Tid → Store → Effect` classifies
    each action, in each store, as a both/right/left/non-mover — or an
    error (an access outside the program's synchronization discipline).

  ▸ `Valid M` (Definition 1) says the classification is truthful:
    right movers commute later past other threads' steps, left movers
    commute earlier, movers of one thread cannot change the effect of —
    or disable a left mover of — another thread.

  ▸ The judgment `Judg D M R G s P Q e` is the paper's
    `R;G ⊢ s : P → Q · e`:  from stores satisfying `P`, statement `s`
    terminates only in stores satisfying `Q` (partial correctness),
    consists of reducible sequences separated by `yield`s, and commutes
    as effect `e`.  `P, Q` are two-store predicates relating the store
    at the start of the current reducible sequence (`\old(·)`) to the
    current store.

  One presentational deviation from the paper, chosen to make
  verification-condition generation direct: where the paper computes
  the exact join `M(A, P) = ⨆ {M(A,t,σ) | (t,_,σ) ∈ P}`, our rules take
  any upper bound (`∀ (t,_,σ) ∈ P, M A t σ ⊑ e`).  The exact join plus
  [M-conseq] recovers the paper's rules; soundness only ever needs the
  bound.
-/
import MoverRust.Lang

namespace MoverRust

/-! ### Predicates -/

/-- Two-store predicates `P ⊆ Tid × Store × Store`: `P t σ₀ σ` relates
    the store `σ₀` at the start of the current reducible sequence to
    the current store `σ`. -/
def Pred := Tid → Store → Store → Prop

/-- One-store predicates `S ⊆ Tid × Store`. -/
def Pred1 := Tid → Store → Prop

/-- Rely/guarantee relations (also `⊆ Tid × Store × Store`; for a rely,
    `t` is the thread *being interfered with*). -/
def Rel := Tid → Store → Store → Prop

/-- `Two S` — the diagonal of a one-store predicate (`\old(x) = x`). -/
def Two (S : Pred1) : Pred := fun t σ₀ σ => σ₀ = σ ∧ S t σ

/-- `Post P` — forget the old store. -/
def Post (P : Pred) : Pred1 := fun t σ => ∃ σ₀, P t σ₀ σ

/-- `P ; A` — run action `A` after `P`. -/
def pseq (P : Pred) (A : Act) : Pred :=
  fun t σ₀ σ'' => ∃ σ', P t σ₀ σ' ∧ den A t σ' σ''

/-- `P ; Q` — relational composition of two-store predicates. -/
def pcomp (P Q : Pred) : Pred :=
  fun t σ₀ σ'' => ∃ σ', P t σ₀ σ' ∧ Q t σ' σ''

/-- Iterated interference `R*` (per thread). -/
def RStar (R : Rel) (t : Tid) : Store → Store → Prop := Multi (R t)

/-- `Yield(P, R)` — the precondition after a yield: any store reachable
    from a `P`-store by interference, with `\old` reset. -/
def yieldP (P : Pred) (R : Rel) : Pred :=
  fun t σ' σ'' => σ'' = σ' ∧ ∃ σ, (∃ σ₀, P t σ₀ σ) ∧ RStar R t σ σ'

/-- The empty predicate (precondition of `wrong`). -/
def pFalse : Pred := fun _ _ _ => False

/-- The empty rely/guarantee (used for atomic function bodies). -/
def emptyRel : Rel := fun _ _ _ => False

/-- Predicate implication. -/
def PImp (P Q : Pred) : Prop := ∀ t σ₀ σ, P t σ₀ σ → Q t σ₀ σ

/-- Rely/guarantee implication. -/
def RImp (R R' : Rel) : Prop := ∀ t σ σ', R t σ σ' → R' t σ σ'

/-! ### Mover specifications and validity -/

/-- A mover specification (paper §7.2), `M(A, tid, σ) ∈ Effect \ {Y}`. -/
def MSpec := Act → Tid → Store → Effect

/-- Definition 1 (Validity).  `M` may claim only true commutativity:

    1. right movers commute to later in a trace;
    2. left movers commute to earlier in a trace;
    3. a step of one thread cannot change the effect of another
       thread's action;
    4. a step of one thread cannot disable another thread's left mover.

    Together with `noY` (actions never have the yield effect). -/
structure Valid (M : MSpec) : Prop where
  noY : ∀ A t σ, M A t σ ≠ .Y
  right_commute : ∀ {t u : Tid} {A₁ A₂ σ σ' σ''}, t ≠ u →
    M A₁ t σ ≤ .R → den A₁ t σ σ' →
    M A₂ u σ' ≤ .N → den A₂ u σ' σ'' →
    ∃ σ''', den A₂ u σ σ''' ∧ den A₁ t σ''' σ''
  left_commute : ∀ {t u : Tid} {A₁ A₂ σ σ' σ''}, t ≠ u →
    M A₁ t σ ≤ .N → den A₁ t σ σ' →
    M A₂ u σ' ≤ .L → den A₂ u σ' σ'' →
    ∃ σ''', den A₂ u σ σ''' ∧ den A₁ t σ''' σ''
  stable_eff : ∀ {t u : Tid} {A₁ A₂ σ σ'}, t ≠ u →
    M A₁ t σ ≤ .N → den A₁ t σ σ' →
    M A₂ u σ' = M A₂ u σ
  left_enabled : ∀ {t u : Tid} {A₁ A₂ σ σ' σ''}, t ≠ u →
    M A₁ t σ ≤ .N → den A₁ t σ σ' →
    M A₂ u σ ≤ .L → den A₂ u σ σ'' →
    ∃ σ''', den A₂ u σ' σ''' ∧ den A₁ t σ'' σ'''

/-! ### Function specifications -/

/-- Function specifications (paper §8.2–8.3):

    * `atomicSpec e S Q` — an atomic function: reducible (yield-free)
      body, one-store precondition `S`, two-store postcondition `Q`
      (which may mention `\old`), overall effect `e`;
    * `rgSpec R G S T` — a non-atomic function: may contain yields,
      carries its own rely `R` and guarantee `G`, one-store pre/post
      `S`, `T`. -/
inductive FnSpec : Type 1 where
  | atomicSpec (e : Effect) (S : Pred1) (Q : Pred)
  | rgSpec (R G : Rel) (S T : Pred1)

/-- Declarations: function id ↦ (specification, body). -/
def Decls := Nat → Option (FnSpec × Stmt)

/-- The bodies alone, for the operational semantics. -/
def Decls.fns (D : Decls) : FnTable := fun f => (D f).map Prod.snd

/-- Call-free statements.  We require atomic function *bodies* to be
    call-free — a simple sufficient condition for the paper's
    "atomic functions are not (directly or indirectly) recursive",
    which underpins the post-commit termination argument. -/
def CallFree : Stmt → Prop
  | .skip | .wrong | .act _ | .yld => True
  | .seq s₁ s₂ => CallFree s₁ ∧ CallFree s₂
  | .ite _ s₁ s₂ => CallFree s₁ ∧ CallFree s₂
  | .wloop _ s => CallFree s
  | .call _ => False

/-! ### The mover logic judgment (Figures 8 and 9) -/

/-- `Judg D M R G s P Q e` — the paper's `R;G ⊢ s : P → Q · e`. -/
inductive Judg (D : Decls) (M : MSpec) : Rel → Rel → Stmt → Pred → Pred → Effect → Prop where
  /-- [M-skip] -/
  | skip {R G : Rel} {P : Pred} : Judg D M R G .skip P P .B
  /-- [M-wrong] — `wrong` verifies only from the empty precondition:
      verified code never reaches it. -/
  | wrong {R G : Rel} : Judg D M R G .wrong pFalse pFalse .B
  /-- [M-action] with an upper bound `e` for `M(A, P)`. -/
  | act {R G : Rel} {A P e} :
      (∀ t σ₀ σ, P t σ₀ σ → M A t σ ≤ e) →
      (e ≤ .L → total A) →
      Judg D M R G (.act A) P (pseq P A) e
  /-- [M-seq] -/
  | seqJ {R G : Rel} {s₁ s₂ P Q₁ Q₂ e₁ e₂} :
      Judg D M R G s₁ P Q₁ e₁ →
      Judg D M R G s₂ Q₁ Q₂ e₂ →
      Judg D M R G (.seq s₁ s₂) P Q₂ (e₁.seq e₂)
  /-- [M-if]: both branches meet the same postcondition; the effect is
      the join over both paths. -/
  | iteJ {R G : Rel} {C s₁ s₂ P Q e₁ e₂ m₁ m₂} :
      (∀ t σ₀ σ, P t σ₀ σ → M (condA C true) t σ ≤ m₁) →
      (∀ t σ₀ σ, P t σ₀ σ → M (condA C false) t σ ≤ m₂) →
      Judg D M R G s₁ (pseq P (condA C true)) Q e₁ →
      Judg D M R G s₂ (pseq P (condA C false)) Q e₂ →
      Judg D M R G (.ite C s₁ s₂) P Q ((m₁.seq e₁).join (m₂.seq e₂))
  /-- [M-while]: `P` is the loop invariant; the loop cannot sit in the
      post-commit phase (`e ̸⊑ L`), since committed code must terminate. -/
  | wloopJ {R G : Rel} {C s P e₁ m₁ m₂} :
      (∀ t σ₀ σ, P t σ₀ σ → M (condA C true) t σ ≤ m₁) →
      (∀ t σ₀ σ, P t σ₀ σ → M (condA C false) t σ ≤ m₂) →
      Judg D M R G s (pseq P (condA C true)) P e₁ →
      ¬ (((m₁.seq e₁).star.seq m₂) ≤ .L) →
      Judg D M R G (.wloop C s) P (pseq P (condA C false)) ((m₁.seq e₁).star.seq m₂)
  /-- [M-yield]: the reducible sequence just ended is published to the
      guarantee; the next one starts from any store reachable by
      interference `R*`. -/
  | yieldJ {R G : Rel} {P} :
      (∀ t σ₀ σ, P t σ₀ σ → G t σ₀ σ) →
      Judg D M R G .yld P (yieldP P R) .Y
  /-- [M-call-atomic] -/
  | callAtomic {R G : Rel} {f e S Q body P} :
      D f = some (.atomicSpec e S Q, body) →
      (∀ t σ₀ σ, P t σ₀ σ → S t σ) →
      Judg D M R G (.call f) P (pcomp P Q) e
  /-- [M-call-non-atomic]: calls happen at the start of a reducible
      sequence, with the callee's own rely/guarantee. -/
  | callNonAtomic {R G : Rel} {f S T body} :
      D f = some (.rgSpec R G S T, body) →
      Judg D M R G (.call f) (Two S) (Two T) .R
  /-- [M-conseq] -/
  | conseq {R G R' G' : Rel} {s P P' Q Q' e e'} :
      PImp P P' → PImp Q' Q → RImp R R' → RImp G' G → e' ≤ e →
      Judg D M R' G' s P' Q' e' →
      Judg D M R G s P Q e

/-! ### Verified function declarations (Figure 9) -/

/-- `⊢ fn` for one declaration. -/
inductive FnOK (D : Decls) (M : MSpec) : FnSpec → Stmt → Prop where
  /-- [M-def-atomic]: body verified under the empty rely/guarantee
      (which forbids reachable yields), call-free (hence no recursion). -/
  | atomic {e S Q body} :
      CallFree body →
      Judg D M emptyRel emptyRel body (Two S) Q e →
      FnOK D M (.atomicSpec e S Q) body
  /-- [M-def-non-atomic]: the body runs from `S` to `T` through yields,
      with overall effect (at most) `R` — it ends in a yield. -/
  | nonatomic {R G S T body} :
      Judg D M R G body (Two S) (Two T) .R →
      FnOK D M (.rgSpec R G S T) body

/-- All declarations verified. -/
def DeclsOK (D : Decls) (M : MSpec) : Prop :=
  ∀ f sp body, D f = some (sp, body) → FnOK D M sp body

/-! ### Verified states ([M-state]) -/

/-- `⊢ Σ` — the top-level judgment for a thread pool (paper Figure 9):
    every declaration is verified, `M` is valid, the guarantee is
    reflexive and contained in every other thread's rely, and each
    thread verifies from a precondition holding at the current store,
    starts at a yield, and publishes its final state to `G`. -/
structure StateOK (D : Decls) (M : MSpec) (R G : Rel) (st : State) : Prop where
  fnsOK : DeclsOK D M
  valid : Valid M
  Grefl : ∀ t σ, G t σ σ
  compat : ∀ t u, t ≠ u → ∀ σ σ', G t σ σ' → R u σ σ'
  threads : ∀ i s, st.threads.get? i = some s →
    ∃ P Q e, Judg D M R G s P Q e ∧ e ≠ .E ∧
      PImp Q (fun t σ₀ σ => G t σ₀ σ) ∧
      Yielding s ∧ P i st.store st.store

end MoverRust
