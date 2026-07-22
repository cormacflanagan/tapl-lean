/-!
# Chapter 22: Type Reconstruction

Typechecking λ→ terms whose annotations may contain **type variables**:
constraint-based typing (TAPL figure 22-1) generates a set of equations
between types, and **unification** (figure 22-2, Hindley/Milner/Robinson)
solves them, computing a *principal* solution.

The three results proved here:
* `unify_sound` — a substitution returned by the unifier really solves
  the constraints;
* `unify_principal` (TAPL theorem 22.4.5's heart) — any other solution
  factors through the returned one: the unifier computes a **most general
  unifier**;
* `gen_sound` / `reconstruct_sound` — solutions of the generated
  constraints yield well-typed instantiations of the original term
  (theorem 22.3.5's soundness direction).

The unifier is written with explicit fuel, which keeps it kernel-
computable and sidesteps the (standard, but tangential) lexicographic
termination argument; both correctness theorems hold for every successful
run, whatever the fuel. See the README for what is deliberately not here
(completeness of `unify` on unsolvable inputs, and the freshness
bookkeeping for constraint-generation completeness).
-/

namespace Chapter22

/-- Types with type variables (numbered), `Bool`, and arrows. -/
inductive Ty : Type where
  | var (n : Nat)
  | bool
  | arrow (T₁ T₂ : Ty)
  deriving Repr, DecidableEq

/-- `T₁ ⇒ T₂` is the function type. -/
scoped infixr:60 " ⇒ " => Ty.arrow

/-- Terms: λ→ with booleans; abstractions are annotated with types that
may contain type variables. -/
inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | tru
  | fls
  | ite (t₁ t₂ t₃ : Term)
  deriving Repr, DecidableEq

/-! ## Substitutions -/

/-- Does type variable `n` occur in `T`? -/
def occurs (n : Nat) : Ty → Bool
  | .var m => m == n
  | .bool => false
  | .arrow T₁ T₂ => occurs n T₁ || occurs n T₂

/-- Substitute `S` for the single type variable `n`. -/
def subst1 (n : Nat) (S : Ty) : Ty → Ty
  | .var m => if m = n then S else .var m
  | .bool => .bool
  | .arrow T₁ T₂ => .arrow (subst1 n S T₁) (subst1 n S T₂)

/-- A substitution is a sequence of single-variable bindings, applied
left to right (so `(n, T) :: σ` is `σ ∘ [n ↦ T]`, as in TAPL's
unification algorithm). -/
abbrev Subst := List (Nat × Ty)

/-- Apply a substitution. -/
def applyS : Subst → Ty → Ty
  | [], T => T
  | (n, S) :: σ, T => applyS σ (subst1 n S T)

theorem applyS_bool : ∀ σ : Subst, applyS σ .bool = .bool := by
  intro σ
  induction σ with
  | nil => rfl
  | cons _ σ ih => simp [applyS, subst1, ih]

theorem applyS_arrow : ∀ (σ : Subst) (A B : Ty),
    applyS σ (.arrow A B) = .arrow (applyS σ A) (applyS σ B) := by
  intro σ
  induction σ with
  | nil => intro A B; rfl
  | cons p σ ih => intro A B; simp [applyS, subst1, ih]

/-- Substituting for an absent variable does nothing. -/
theorem subst1_no_occurs {n : Nat} {S : Ty} :
    ∀ {T : Ty}, occurs n T = false → subst1 n S T = T := by
  intro T
  induction T with
  | var m =>
      intro h
      simp [occurs] at h
      simp [subst1, h]
  | bool => intro _; rfl
  | arrow T₁ T₂ ih₁ ih₂ =>
      intro h
      simp [occurs] at h
      simp [subst1, ih₁ h.1, ih₂ h.2]

/-! ## Constraints and unification (TAPL fig. 22-2) -/

/-- A constraint is an equation between two types. -/
abbrev Constr := Ty × Ty

/-- Apply a single-variable substitution to a constraint set. -/
def substC (n : Nat) (S : Ty) (C : List Constr) : List Constr :=
  C.map (fun p => (subst1 n S p.1, subst1 n S p.2))

/-- `σ` solves every equation in `C`. -/
def Unifies (σ : Subst) (C : List Constr) : Prop :=
  ∀ p ∈ C, applyS σ p.1 = applyS σ p.2

/-- The unification algorithm, with fuel. On the binding cases it returns
`unify(rest[n ↦ T]) ∘ [n ↦ T]`, exactly as in TAPL fig. 22-2; `none`
means an occurs-check or clash failure — or exhausted fuel. -/
def unifyF : Nat → List Constr → Option Subst
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, (S, T) :: rest =>
      match S, T with
      | .bool, .bool => unifyF fuel rest
      | .arrow S₁ S₂, .arrow T₁ T₂ =>
          unifyF fuel ((S₁, T₁) :: (S₂, T₂) :: rest)
      | .var n, T =>
          if T = .var n then unifyF fuel rest
          else if occurs n T then none
          else (unifyF fuel (substC n T rest)).map ((n, T) :: ·)
      | S, .var n =>
          if occurs n S then none
          else (unifyF fuel (substC n S rest)).map ((n, S) :: ·)
      | _, _ => none

/-- One equal-pair step used by both binding cases: if `τ` equates
`var n` and `T`, then `subst1 n T` is invisible to `τ`. -/
theorem applyS_subst1_eq {τ : Subst} {n : Nat} {T : Ty}
    (h : applyS τ (.var n) = applyS τ T) :
    ∀ X, applyS τ (subst1 n T X) = applyS τ X := by
  intro X
  induction X with
  | var m =>
      by_cases hm : m = n
      · subst hm
        simp [subst1, h]
      · simp [subst1, hm]
  | bool => simp [subst1]
  | arrow X₁ X₂ ih₁ ih₂ =>
      simp [subst1, applyS_arrow, ih₁, ih₂]

/-- **Soundness of unification**: a returned substitution solves the
constraints. -/
theorem unify_sound :
    ∀ (fuel : Nat) (C : List Constr) (σ : Subst),
      unifyF fuel C = some σ → Unifies σ C := by
  intro fuel
  induction fuel with
  | zero => intro C σ h; simp [unifyF] at h
  | succ fuel ih =>
      intro C σ h
      match C with
      | [] => intro p hp; cases hp
      | (S, T) :: rest =>
          match S, T with
          | .bool, .bool =>
              simp only [unifyF] at h
              intro p hp
              cases hp with
              | head => rfl
              | tail _ hp => exact ih rest σ h p hp
          | .arrow S₁ S₂, .arrow T₁ T₂ =>
              simp only [unifyF] at h
              have hu := ih _ σ h
              intro p hp
              cases hp with
              | head =>
                  have h₁ := hu (S₁, T₁) (by simp)
                  have h₂ := hu (S₂, T₂) (by simp)
                  simp [applyS_arrow, h₁, h₂]
              | tail _ hp =>
                  exact hu p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
          | .var n, T =>
              simp only [unifyF] at h
              by_cases hTn : T = .var n
              · rw [if_pos hTn] at h
                subst hTn
                intro p hp
                cases hp with
                | head => rfl
                | tail _ hp => exact ih rest σ h p hp
              · rw [if_neg hTn] at h
                by_cases hocc : occurs n T
                · rw [if_pos hocc] at h; cases h
                · rw [if_neg hocc, Option.map_eq_some'] at h
                  obtain ⟨σ', hσ', rfl⟩ := h
                  have hu := ih _ σ' hσ'
                  intro p hp
                  cases hp with
                  | head =>
                      show applyS σ' (subst1 n T (.var n)) =
                        applyS σ' (subst1 n T T)
                      rw [show subst1 n T (.var n) = T from by simp [subst1],
                        subst1_no_occurs (by simpa using hocc)]
                  | tail _ hp =>
                      exact hu _ (List.mem_map_of_mem _ hp)
          | .bool, .var n =>
              simp only [unifyF] at h
              rw [if_neg (by simp [occurs])] at h
              rw [Option.map_eq_some'] at h
              obtain ⟨σ', hσ', rfl⟩ := h
              have hu := ih _ σ' hσ'
              intro p hp
              cases hp with
              | head =>
                  show applyS σ' (subst1 n .bool .bool) =
                    applyS σ' (subst1 n .bool (.var n))
                  simp [subst1]
              | tail _ hp => exact hu _ (List.mem_map_of_mem _ hp)
          | .arrow S₁ S₂, .var n =>
              simp only [unifyF] at h
              by_cases hocc : occurs n (.arrow S₁ S₂)
              · rw [if_pos hocc] at h; cases h
              · rw [if_neg hocc, Option.map_eq_some'] at h
                obtain ⟨σ', hσ', rfl⟩ := h
                have hu := ih _ σ' hσ'
                intro p hp
                cases hp with
                | head =>
                    show applyS σ' (subst1 n (.arrow S₁ S₂) (.arrow S₁ S₂)) =
                      applyS σ' (subst1 n (.arrow S₁ S₂) (.var n))
                    rw [subst1_no_occurs (by simpa using hocc),
                      show subst1 n (.arrow S₁ S₂) (.var n) = .arrow S₁ S₂
                        from by simp [subst1]]
                | tail _ hp => exact hu _ (List.mem_map_of_mem _ hp)
          | .bool, .arrow T₁ T₂ => simp [unifyF] at h
          | .arrow S₁ S₂, .bool => simp [unifyF] at h

/-- **Principality (TAPL theorem 22.4.5)**: every unifier of the
constraints factors through the substitution the algorithm returns —
`unifyF` computes a most general unifier. -/
theorem unify_principal :
    ∀ (fuel : Nat) (C : List Constr) (σ : Subst),
      unifyF fuel C = some σ → ∀ τ, Unifies τ C →
        ∃ ρ, ∀ T, applyS τ T = applyS ρ (applyS σ T) := by
  intro fuel
  induction fuel with
  | zero => intro C σ h; simp [unifyF] at h
  | succ fuel ih =>
      intro C σ h τ hτ
      match C with
      | [] =>
          simp only [unifyF] at h
          cases h
          exact ⟨τ, fun T => rfl⟩
      | (S, T) :: rest =>
          match S, T with
          | .bool, .bool =>
              simp only [unifyF] at h
              exact ih rest σ h τ (fun p hp => hτ p (by simp [hp]))
          | .arrow S₁ S₂, .arrow T₁ T₂ =>
              simp only [unifyF] at h
              apply ih _ σ h τ
              intro p hp
              cases hp with
              | head =>
                  have := hτ (.arrow S₁ S₂, .arrow T₁ T₂) (by simp)
                  simp [applyS_arrow] at this
                  exact this.1
              | tail _ hp =>
                  cases hp with
                  | head =>
                      have := hτ (.arrow S₁ S₂, .arrow T₁ T₂) (by simp)
                      simp [applyS_arrow] at this
                      exact this.2
                  | tail _ hp => exact hτ _ (List.mem_cons_of_mem _ hp)
          | .var n, T =>
              simp only [unifyF] at h
              by_cases hTn : T = .var n
              · rw [if_pos hTn] at h
                exact ih rest σ h τ (fun p hp => hτ p (by simp [hp]))
              · rw [if_neg hTn] at h
                by_cases hocc : occurs n T
                · rw [if_pos hocc] at h; cases h
                · rw [if_neg hocc, Option.map_eq_some'] at h
                  obtain ⟨σ', hσ', rfl⟩ := h
                  have hn : applyS τ (.var n) = applyS τ T :=
                    hτ (.var n, T) (by simp)
                  have hτ' : Unifies τ (substC n T rest) := by
                    intro p hp
                    simp [substC] at hp
                    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hp
                    show applyS τ (subst1 n T a) = applyS τ (subst1 n T b)
                    rw [applyS_subst1_eq hn, applyS_subst1_eq hn]
                    exact hτ (a, b) (by simp [hab])
                  obtain ⟨ρ, hρ⟩ := ih _ σ' hσ' τ hτ'
                  refine ⟨ρ, fun U => ?_⟩
                  show applyS τ U = applyS ρ (applyS σ' (subst1 n T U))
                  rw [← hρ (subst1 n T U), applyS_subst1_eq hn]
          | .bool, .var n =>
              simp only [unifyF] at h
              rw [if_neg (by simp [occurs])] at h
              rw [Option.map_eq_some'] at h
              obtain ⟨σ', hσ', rfl⟩ := h
              have hn : applyS τ (.var n) = applyS τ .bool :=
                (hτ (.bool, .var n) (by simp)).symm
              have hτ' : Unifies τ (substC n .bool rest) := by
                intro p hp
                simp [substC] at hp
                obtain ⟨⟨a, b⟩, hab, rfl⟩ := hp
                show applyS τ (subst1 n .bool a) = applyS τ (subst1 n .bool b)
                rw [applyS_subst1_eq hn, applyS_subst1_eq hn]
                exact hτ (a, b) (by simp [hab])
              obtain ⟨ρ, hρ⟩ := ih _ σ' hσ' τ hτ'
              refine ⟨ρ, fun U => ?_⟩
              show applyS τ U = applyS ρ (applyS σ' (subst1 n .bool U))
              rw [← hρ (subst1 n .bool U), applyS_subst1_eq hn]
          | .arrow S₁ S₂, .var n =>
              simp only [unifyF] at h
              by_cases hocc : occurs n (.arrow S₁ S₂)
              · rw [if_pos hocc] at h; cases h
              · rw [if_neg hocc, Option.map_eq_some'] at h
                obtain ⟨σ', hσ', rfl⟩ := h
                have hn : applyS τ (.var n) = applyS τ (.arrow S₁ S₂) :=
                  (hτ (.arrow S₁ S₂, .var n) (by simp)).symm
                have hτ' : Unifies τ (substC n (.arrow S₁ S₂) rest) := by
                  intro p hp
                  simp [substC] at hp
                  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hp
                  show applyS τ (subst1 n (.arrow S₁ S₂) a) =
                    applyS τ (subst1 n (.arrow S₁ S₂) b)
                  rw [applyS_subst1_eq hn, applyS_subst1_eq hn]
                  exact hτ (a, b) (by simp [hab])
                obtain ⟨ρ, hρ⟩ := ih _ σ' hσ' τ hτ'
                refine ⟨ρ, fun U => ?_⟩
                show applyS τ U =
                  applyS ρ (applyS σ' (subst1 n (.arrow S₁ S₂) U))
                rw [← hρ (subst1 n (.arrow S₁ S₂) U), applyS_subst1_eq hn]
          | .bool, .arrow _ _ => simp [unifyF] at h
          | .arrow _ _, .bool => simp [unifyF] at h

/-! ## Constraint generation (TAPL fig. 22-1) -/

/-- Typing contexts. -/
abbrev Ctx := List Ty

/-- Constraint generation, threading a fresh-variable counter `k`
(function form of TAPL's `CT-…` rules; `none` = unbound term variable). -/
def gen (Γ : Ctx) : Term → Nat → Option (Ty × List Constr × Nat)
  | .var n, k =>
      match Γ.get? n with
      | some T => some (T, [], k)
      | none => none
  | .abs T₁ t, k =>
      match gen (T₁ :: Γ) t k with
      | some (T₂, C, k') => some (.arrow T₁ T₂, C, k')
      | none => none
  | .app t₁ t₂, k =>
      match gen Γ t₁ k with
      | some (T₁, C₁, k₁) =>
          match gen Γ t₂ k₁ with
          | some (T₂, C₂, k₂) =>
              some (.var k₂, C₁ ++ C₂ ++ [(T₁, .arrow T₂ (.var k₂))], k₂ + 1)
          | none => none
      | none => none
  | .tru, k => some (.bool, [], k)
  | .fls, k => some (.bool, [], k)
  | .ite t₁ t₂ t₃, k =>
      match gen Γ t₁ k with
      | some (T₁, C₁, k₁) =>
          match gen Γ t₂ k₁ with
          | some (T₂, C₂, k₂) =>
              match gen Γ t₃ k₂ with
              | some (T₃, C₃, k₃) =>
                  some (T₂, C₁ ++ C₂ ++ C₃ ++ [(T₁, .bool), (T₂, T₃)], k₃)
              | none => none
          | none => none
      | none => none

/-- Apply a substitution to a term's annotations. -/
def substTerm (σ : Subst) : Term → Term
  | .var n => .var n
  | .abs T t => .abs (applyS σ T) (substTerm σ t)
  | .app t₁ t₂ => .app (substTerm σ t₁) (substTerm σ t₂)
  | .tru => .tru
  | .fls => .fls
  | .ite t₁ t₂ t₃ =>
      .ite (substTerm σ t₁) (substTerm σ t₂) (substTerm σ t₃)

/-- The (declarative) typing relation of chapter 9, over these types. -/
inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ n T} : Γ.get? n = some T → HasType Γ (.var n) T
  | abs {Γ T₁ T₂ t} :
      HasType (T₁ :: Γ) t T₂ → HasType Γ (.abs T₁ t) (T₁ ⇒ T₂)
  | app {Γ T₁ T₂ t₁ t₂} :
      HasType Γ t₁ (T₁ ⇒ T₂) → HasType Γ t₂ T₁ →
      HasType Γ (.app t₁ t₂) T₂
  | tru {Γ} : HasType Γ .tru .bool
  | fls {Γ} : HasType Γ .fls .bool
  | ite {Γ t₁ t₂ t₃ T} :
      HasType Γ t₁ .bool → HasType Γ t₂ T → HasType Γ t₃ T →
      HasType Γ (.ite t₁ t₂ t₃) T

theorem unifies_append_left {σ : Subst} {A B : List Constr}
    (h : Unifies σ (A ++ B)) : Unifies σ A :=
  fun p hp => h p (by simp [hp])

theorem unifies_append_right {σ : Subst} {A B : List Constr}
    (h : Unifies σ (A ++ B)) : Unifies σ B :=
  fun p hp => h p (by simp [hp])

theorem get?_map_ty (f : Ty → Ty) :
    ∀ (Γ : Ctx) (n : Nat) (T : Ty),
      Γ.get? n = some T → (Γ.map f).get? n = some (f T) := by
  intro Γ
  induction Γ with
  | nil => intro n T h; cases h
  | cons B Γ ih =>
      intro n T h
      cases n with
      | zero => cases h; rfl
      | succ n => exact ih n T h

/-- **Soundness of constraint typing (TAPL theorem 22.3.5, soundness
direction)**: every solution of the generated constraints turns the term
into a well-typed one. -/
theorem gen_sound :
    ∀ (t : Term) (Γ : Ctx) (k : Nat) {T : Ty} {C : List Constr} {k' : Nat},
      gen Γ t k = some (T, C, k') → ∀ σ, Unifies σ C →
        HasType (Γ.map (applyS σ)) (substTerm σ t) (applyS σ T) := by
  intro t
  induction t with
  | var n =>
      intro Γ k T C k' h σ _
      simp only [gen] at h
      cases hg : Γ.get? n with
      | none => rw [hg] at h; cases h
      | some T₀ =>
          rw [hg] at h
          cases h
          exact .var (get?_map_ty (applyS σ) Γ n _ hg)
  | abs T₁ t ih =>
      intro Γ k T C k' h σ hσ
      simp only [gen] at h
      cases hg : gen (T₁ :: Γ) t k with
      | none => rw [hg] at h; cases h
      | some r =>
          obtain ⟨T₂, C₀, k₀⟩ := r
          rw [hg] at h
          cases h
          rw [show substTerm σ (.abs T₁ t) =
            .abs (applyS σ T₁) (substTerm σ t) from rfl, applyS_arrow]
          exact .abs (ih (T₁ :: Γ) k hg σ hσ)
  | app t₁ t₂ ih₁ ih₂ =>
      intro Γ k T C k' h σ hσ
      simp only [gen] at h
      split at h
      next T₁ C₁ k₁ heq₁ =>
        split at h
        next T₂ C₂ k₂ heq₂ =>
          cases h
          have h₁ := ih₁ Γ k heq₁ σ
            (unifies_append_left (unifies_append_left hσ))
          have h₂ := ih₂ Γ k₁ heq₂ σ
            (unifies_append_right (unifies_append_left hσ))
          have heq := (unifies_append_right hσ)
            (T₁, .arrow T₂ (.var k₂)) (by simp)
          rw [applyS_arrow] at heq
          rw [heq] at h₁
          exact .app h₁ h₂
        next _ => cases h
      next _ => cases h
  | tru =>
      intro Γ k T C k' h σ _
      simp only [gen] at h
      cases h
      rw [applyS_bool]
      exact .tru
  | fls =>
      intro Γ k T C k' h σ _
      simp only [gen] at h
      cases h
      rw [applyS_bool]
      exact .fls
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
      intro Γ k T C k' h σ hσ
      simp only [gen] at h
      split at h
      next T₁ C₁ k₁ heq₁ =>
        split at h
        next T₂ C₂ k₂ heq₂ =>
          split at h
          next T₃ C₃ k₃ heq₃ =>
            cases h
            have hA := unifies_append_left hσ
            have hlast := unifies_append_right hσ
            have h₁ := ih₁ Γ k heq₁ σ
              (unifies_append_left (unifies_append_left hA))
            have h₂ := ih₂ Γ k₁ heq₂ σ
              (unifies_append_right (unifies_append_left hA))
            have h₃ := ih₃ Γ k₂ heq₃ σ (unifies_append_right hA)
            have hb := hlast (T₁, .bool) (by simp)
            rw [applyS_bool] at hb
            have h23 := hlast (T, T₃) (by simp)
            rw [hb] at h₁
            rw [← h23] at h₃
            exact .ite h₁ h₂ h₃
          next _ => cases h
        next _ => cases h
      next _ => cases h

/-! ## The reconstruction algorithm -/

/-- Generate constraints and unify: on success, a substitution and the
(pre-substitution) result type. -/
def reconstruct (fuel : Nat) (t : Term) : Option (Subst × Ty) :=
  match gen [] t 0 with
  | some (T, C, _) => (unifyF fuel C).map (fun σ => (σ, T))
  | none => none

/-- **Soundness of reconstruction**: a successful run yields a well-typed
instantiation of the term. -/
theorem reconstruct_sound {fuel : Nat} {t : Term} {σ : Subst} {T : Ty}
    (h : reconstruct fuel t = some (σ, T)) :
    HasType [] (substTerm σ t) (applyS σ T) := by
  unfold reconstruct at h
  cases hg : gen [] t 0 with
  | none => rw [hg] at h; cases h
  | some r =>
      obtain ⟨T₀, C, k⟩ := r
      rw [hg, Option.map_eq_some'] at h
      obtain ⟨σ', hσ', heq⟩ := h
      cases heq
      have := gen_sound t [] 0 hg σ (unify_sound fuel C σ hσ')
      simpa using this

/-! ## Examples (TAPL §22.2–22.4) -/

/-- `λx:X₀. x` — no constraints; its type is `X₀ ⇒ X₀`. -/
example : reconstruct 10 (.abs (.var 0) (.var 0)) =
    some ([], .var 0 ⇒ .var 0) := by decide

/-- `(λx:X₅. x) true` — unification solves `X₅ ⇒ X₅ ≐ Bool ⇒ X₀`,
binding both type variables to `Bool`; the result type instantiates to
`Bool`. -/
example : reconstruct 10 (.app (.abs (.var 5) (.var 0)) .tru) =
    some ([(5, .bool), (0, .bool)], .var 0) := by decide

example :
    applyS [(5, Ty.bool), (0, Ty.bool)] (.var 0) = .bool := by decide

/-- `λx:X₀. if x then false else x` — the guard forces `X₀ = Bool`, and
the reconstructed type instantiates to `Bool ⇒ Bool`. -/
example : (reconstruct 10
    (.abs (.var 0) (.ite (.var 0) .fls (.var 0)))).map
      (fun p => applyS p.1 p.2) = some (Ty.bool ⇒ Ty.bool) := by decide

/-- `λx:X₀. x x` — the **occurs check** fires (`X₀ ≐ X₀ ⇒ X₁` has no
finite solution): self-application is untypable, exactly as chapter 9
proved by hand. -/
example : reconstruct 10
    (.abs (.var 0) (.app (.var 0) (.var 0))) = none := by decide

/-- `if true then (λx:X₀.x) else true` — a clash `X₀ ⇒ X₀ ≐ Bool`:
no solution. -/
example : reconstruct 10
    (.ite .tru (.abs (.var 0) (.var 0)) .tru) = none := by decide

end Chapter22
