/-
  MoverRust / Effects — the effect algebra of mover logic

  Flanagan & Freund, "Mover Logic: A Concurrent Program Logic for
  Reduction and Rely-Guarantee Reasoning" (ECOOP 2024), Section 7.1.

  Effects classify how code commutes with steps of concurrent threads:

    Y   yield (interference point)
    B   both-mover
    R   right-mover
    L   left-mover
    N   non-mover (atomic, single commit)
    E   error (not reducible)

  A sequence of actions is *reducible* if its effects match R* [N] L*.
  This is captured by a three-state DFA (pre-commit / post-commit /
  error); every effect denotes a transition function of that DFA, the
  order e₁ ⊑ e₂ is pointwise ("e₂ is at least as damaged"), sequential
  composition is function composition, and iteration e* is the closure
  under repetition.  We define the operations by the tables of the
  paper and then *prove by `decide`* that they agree with the DFA
  semantics — so the tables need not be trusted.
-/

namespace MoverRust

/-- Reduction effects (paper §7.1). -/
inductive Effect : Type where
  | Y  -- yield
  | B  -- both-mover
  | R  -- right-mover
  | L  -- left-mover
  | N  -- non-mover
  | E  -- error
deriving DecidableEq, Repr

/-- Universal quantification over the six effects is decidable (no Mathlib,
    so we provide the instance by hand; it makes every `∀`-lemma below a
    `decide`). -/
instance {p : Effect → Prop} [∀ e, Decidable (p e)] : Decidable (∀ e, p e) :=
  decidable_of_iff (p .Y ∧ p .B ∧ p .R ∧ p .L ∧ p .N ∧ p .E)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ e => by cases e <;> assumption,
     fun h => ⟨h _, h _, h _, h _, h _, h _⟩⟩

namespace Effect

/-- The order `⊑` derived from the DFA:  Y ⊑ B ⊑ R,L ⊑ N ⊑ E
    (R and L incomparable). -/
def le : Effect → Effect → Bool
  | .Y, _  => true
  | .B, .Y => false
  | .B, _  => true
  | .R, .R => true
  | .R, .N => true
  | .R, .E => true
  | .R, _  => false
  | .L, .L => true
  | .L, .N => true
  | .L, .E => true
  | .L, _  => false
  | .N, .N => true
  | .N, .E => true
  | .N, _  => false
  | .E, .E => true
  | .E, _  => false

instance : LE Effect := ⟨fun a b => le a b = true⟩

instance (a b : Effect) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (le a b = true))

/-- Sequential composition `e₁; e₂` (the table of §7.1). -/
def seq : Effect → Effect → Effect
  | .Y, .Y => .Y | .Y, .B => .Y | .Y, .R => .Y | .Y, .L => .L | .Y, .N => .L | .Y, .E => .E
  | .B, e  => e
  | .R, .Y => .R | .R, .B => .R | .R, .R => .R | .R, .L => .N | .R, .N => .N | .R, .E => .E
  | .L, .Y => .Y | .L, .B => .L | .L, .R => .E | .L, .L => .L | .L, .N => .E | .L, .E => .E
  | .N, .Y => .R | .N, .B => .N | .N, .R => .E | .N, .L => .N | .N, .N => .E | .N, .E => .E
  | .E, _  => .E

/-- Join (least upper bound; `R ⊔ L = N`). -/
def join (a b : Effect) : Effect :=
  if le a b then b else if le b a then a else .N

/-- Iterative closure `e*` (the table of §7.1). -/
def star : Effect → Effect
  | .Y => .Y | .B => .B | .R => .R | .L => .L | .N => .E | .E => .E

/-! ### The DFA semantics, and validation of the tables

The DFA has states pre-commit / post-commit / error.  Each effect is a
transition function; we check the tables against it. -/

/-- DFA phases: pre-commit, post-commit, error. -/
inductive Ph : Type where
  | pre | post | err
deriving DecidableEq, Repr

instance {p : Ph → Prop} [∀ x, Decidable (p x)] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .pre ∧ p .post ∧ p .err)
    ⟨fun ⟨h1, h2, h3⟩ x => by cases x <;> assumption,
     fun h => ⟨h _, h _, h _⟩⟩

/-- Phase order: `pre ⊑ post ⊑ err`. -/
def Ph.le : Ph → Ph → Bool
  | .pre, _ => true
  | .post, .pre => false
  | .post, _ => true
  | .err, .err => true
  | .err, _ => false

/-- The transition function denoted by an effect. -/
def run : Effect → Ph → Ph
  | _,  .err  => .err
  | .Y, _     => .pre
  | .B, p     => p
  | .R, .pre  => .pre
  | .R, .post => .err
  | .L, _     => .post
  | .N, .pre  => .post
  | .N, .post => .err
  | .E, _     => .err

/-- `⊑` is exactly the pointwise DFA order. -/
theorem le_iff_run : ∀ a b : Effect,
    le a b = true ↔ ∀ p, (run a p).le (run b p) = true := by decide

/-- `e₁; e₂` is exactly DFA composition. -/
theorem seq_run : ∀ (a b : Effect) (p : Ph), run (seq a b) p = run b (run a p) := by
  decide

/-! ### Order and algebra lemmas (all by `decide` over the finite type) -/

theorem le_refl : ∀ e : Effect, e ≤ e := by decide
theorem le_trans' : ∀ a b c : Effect, a ≤ b → b ≤ c → a ≤ c := by decide
theorem le_trans {a b c : Effect} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := le_trans' a b c h1 h2
theorem le_antisymm' : ∀ a b : Effect, a ≤ b → b ≤ a → a = b := by decide
theorem le_antisymm {a b : Effect} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := le_antisymm' a b h1 h2

theorem le_E : ∀ e : Effect, e ≤ .E := by decide
theorem Y_le : ∀ e : Effect, .Y ≤ e := by decide
theorem B_le_iff : ∀ e : Effect, (.B ≤ e) ↔ e ≠ .Y := by decide

theorem seq_assoc : ∀ a b c : Effect, seq (seq a b) c = seq a (seq b c) := by decide
theorem seq_B_left : ∀ e : Effect, seq .B e = e := by decide
theorem seq_B_right : ∀ e : Effect, seq e .B = e := by decide
theorem seq_E_right : ∀ e : Effect, seq e .E = .E := by decide

/-- Sequencing is monotone in both arguments. -/
theorem seq_mono' : ∀ a a' b b' : Effect, a ≤ a' → b ≤ b' → seq a b ≤ seq a' b' := by
  decide
theorem seq_mono {a a' b b' : Effect} (h1 : a ≤ a') (h2 : b ≤ b') :
    seq a b ≤ seq a' b' := seq_mono' a a' b b' h1 h2

theorem seq_mono_left {a a' : Effect} (b : Effect) (h : a ≤ a') : seq a b ≤ seq a' b :=
  seq_mono h (le_refl b)

theorem seq_mono_right (a : Effect) {b b' : Effect} (h : b ≤ b') : seq a b ≤ seq a b' :=
  seq_mono (le_refl a) h

theorem join_le_iff : ∀ a b c : Effect, (join a b ≤ c) ↔ (a ≤ c ∧ b ≤ c) := by decide
theorem le_join_left : ∀ a b : Effect, a ≤ join a b := by decide
theorem le_join_right : ∀ a b : Effect, b ≤ join a b := by decide

theorem star_mono' : ∀ a b : Effect, a ≤ b → star a ≤ star b := by decide
theorem star_mono {a b : Effect} (h : a ≤ b) : star a ≤ star b := star_mono' a b h
theorem le_star : ∀ e : Effect, e ≤ star e := by decide
theorem B_le_star : ∀ e : Effect, e ≠ .Y → .B ≤ star e := by decide
/-- Unfolding one iteration stays below the closure: `e; e* ⊑ e*`. -/
theorem seq_star_le : ∀ e : Effect, seq e (star e) ≤ star e := by decide
theorem star_seq_le : ∀ e : Effect, seq (star e) e ≤ star e := by decide

/-! ### Facts about the post-commit phase, used in the soundness proof.

Phases of the instrumented semantics are the effects `R` (pre-commit)
and `N` (post-commit); `p; e ≠ E` says the code with future effect `e`
is still reducible from phase `p`. -/

/-- If a decomposed effect `e₁; e₂` fits post-commit (`⊑ L`), so does its head. -/
theorem seq_le_L_left' : ∀ a b : Effect, seq a b ≤ .L → a ≤ .L := by decide
theorem seq_le_L_left {a b : Effect} (h : seq a b ≤ .L) : a ≤ .L := seq_le_L_left' a b h

/-- A right-mover is not post-commit material. -/
theorem R_not_le_L : ¬ (Effect.R ≤ Effect.L) := by decide

/-- From post-commit phase `N`, the remaining effect must be `⊑ L` (or the
    whole thing is an error). -/
theorem post_phase_le : ∀ e : Effect, seq .N e ≠ .E → e ≤ .L := by
  intro e; revert e; decide

theorem seq_ne_E_mono' : ∀ a a' b b' : Effect,
    a ≤ a' → b ≤ b' → seq a' b' ≠ .E → seq a b ≠ .E := by decide
theorem seq_ne_E_mono {a a' b b' : Effect} (h1 : a ≤ a') (h2 : b ≤ b')
    (h3 : seq a' b' ≠ .E) : seq a b ≠ .E := seq_ne_E_mono' a a' b b' h1 h2 h3

theorem le_ne_E : ∀ a b : Effect, a ≤ b → b ≠ .E → a ≠ .E := by decide

instance : Trans (· ≤ · : Effect → Effect → Prop)
    (· ≤ · : Effect → Effect → Prop) (· ≤ · : Effect → Effect → Prop) :=
  ⟨le_trans⟩

/-- Reachable phases are `R` or `N`; every non-error future keeps `R` below. -/
theorem phase_R_le : ∀ p e : Effect, (p = .R ∨ p = .N) → p.seq e ≠ .E →
    .R ≤ p.seq e := by decide

/-- Phases stay in `{R, N}` after composing a non-yield, non-error effect. -/
theorem phase_step : ∀ p m : Effect, (p = .R ∨ p = .N) → m ≠ .Y →
    p.seq m ≠ .E → (p.seq m = .R ∨ p.seq m = .N) := by decide

theorem seq_seq_ne_E_left : ∀ p e₁ e₂ : Effect,
    p.seq (e₁.seq e₂) ≠ .E → p.seq e₁ ≠ .E := by decide

/-- Effect inequality for one unfolding of [M-while] into [M-if]:
    `(m₁;(e₁;eW)) ⊔ (m₂;B) ⊑ eW` where `eW = (m₁;e₁)*;m₂`, given the
    rule's side condition `eW ̸⊑ L`. -/
theorem wloop_unfold_le : ∀ m₁ e₁ m₂ : Effect,
    ¬ (((m₁.seq e₁).star.seq m₂) ≤ .L) →
    ((m₁.seq (e₁.seq ((m₁.seq e₁).star.seq m₂))).join (m₂.seq .B)) ≤
      ((m₁.seq e₁).star.seq m₂) := by decide

/-- Fresh threads (phase `R`) with non-error effects are not stuck. -/
theorem R_seq_ne_E : ∀ e : Effect, e ≠ .E → Effect.R.seq e ≠ .E := by decide

/-- If a step lands in the pre-commit phase `R`, its (non-yield) effect
    was a right- or both-mover (`⊑ R`). -/
theorem seq_eq_R_imp_le : ∀ p m : Effect, m ≠ .Y → p.seq m = .R → m ≤ .R := by decide

/-- A non-error composition had a non-error (hence `⊑ N`) argument. -/
theorem arg_le_N_of_seq_ne_E : ∀ p m : Effect, p.seq m ≠ .E → m ≤ .N := by decide

/-- Composite bound used in the seq-congruence preservation case:
    from `p'; e₁' ⊑ p; e₁` and `e₁; e₂ ⊑ e` conclude
    `p'; (e₁'; e₂) ⊑ p; e`. -/
theorem seq_bound_lemma {p' e₁' p e₁ : Effect} (e₂ : Effect) {e : Effect}
    (hb : p'.seq e₁' ≤ p.seq e₁) (hle : e₁.seq e₂ ≤ e) :
    p'.seq (e₁'.seq e₂) ≤ p.seq e := by
  rw [← seq_assoc]
  exact le_trans (seq_mono_left _ hb)
    (by rw [seq_assoc]; exact seq_mono_right _ hle)

/-- Composite bound for a conditional branch: from `mM ⊑ m` and
    `m; eb ⊑ e` conclude `(p; mM); eb ⊑ p; e`. -/
theorem branch_bound {p mM m eb e : Effect} (h1 : mM ≤ m) (h2 : m.seq eb ≤ e) :
    (p.seq mM).seq eb ≤ p.seq e := by
  rw [seq_assoc]
  exact seq_mono_right _ (le_trans (seq_mono_left _ h1) h2)

theorem le_seq_of_B_le' : ∀ e₁ e₂ : Effect, .B ≤ e₁ → e₂ ≤ e₁.seq e₂ := by
  decide
theorem le_seq_of_B_le {e₁ : Effect} (e₂ : Effect) (h : .B ≤ e₁) :
    e₂ ≤ e₁.seq e₂ := le_seq_of_B_le' e₁ e₂ h

end Effect

end MoverRust
