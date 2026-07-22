/-!
# Chapter 13: References

λ→ with `Unit`, extended with ML-style mutable references: allocation
`ref t`, dereferencing `!t`, and assignment `t₁ := t₂` (TAPL figure 13-1).

Evaluation now acts on *configurations* `(t, μ)` where `μ` is a **store**
(a list of terms indexed by locations), and typing acquires a **store
typing** `St` assigning a type to each location. The preservation theorem
takes its famous chapter-13 shape: the store typing may *grow* during
evaluation, so the theorem existentially quantifies over an extension of
`St` (TAPL theorem 13.5.3).
-/

namespace Chapter13

/-- Types: `Unit`, functions, and reference types (TAPL fig. 13-1). -/
inductive Ty : Type where
  | unit
  | arrow (T₁ T₂ : Ty)
  | ref (T : Ty)
  deriving Repr, DecidableEq

/-- `T₁ ⇒ T₂` is the function type. -/
scoped infixr:60 " ⇒ " => Ty.arrow

/-- Terms: λ→ with `unit`, plus locations and the three reference
operations. Locations `loc l` appear only at runtime (allocated by
evaluation), never in source programs. -/
inductive Term : Type where
  | var (n : Nat)
  | abs (T : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  | unit
  | loc (l : Nat)
  | ref (t : Term)
  | deref (t : Term)
  | assign (t₁ t₂ : Term)
  deriving Repr, DecidableEq

namespace Term

/-- Shift the variables of `t` that are `≥ c` up by `d`. -/
def shift (d c : Nat) : Term → Term
  | var n => if n < c then var n else var (n + d)
  | abs T t => abs T (shift d (c + 1) t)
  | app t₁ t₂ => app (shift d c t₁) (shift d c t₂)
  | unit => unit
  | loc l => loc l
  | ref t => ref (shift d c t)
  | deref t => deref (shift d c t)
  | assign t₁ t₂ => assign (shift d c t₁) (shift d c t₂)

/-- Beta-substitution `[k ↦ s] t` (substitute and decrement). -/
def subst (k : Nat) (s : Term) : Term → Term
  | var n =>
      if n < k then var n
      else if n = k then shift k 0 s
      else var (n - 1)
  | abs T t => abs T (subst (k + 1) s t)
  | app t₁ t₂ => app (subst k s t₁) (subst k s t₂)
  | unit => unit
  | loc l => loc l
  | ref t => ref (subst k s t)
  | deref t => deref (subst k s t)
  | assign t₁ t₂ => assign (subst k s t₁) (subst k s t₂)

/-- Shifting by zero is the identity. -/
theorem shift_zero : ∀ (t : Term) (c : Nat), shift 0 c t = t := by
  intro t
  induction t with
  | var n => intro c; by_cases h : n < c <;> simp [shift, h]
  | unit => intro c; rfl
  | loc l => intro c; rfl
  | abs T t ih | ref t ih | deref t ih => intro c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ | assign t₁ t₂ ih₁ ih₂ =>
      intro c; simp [shift, ih₁, ih₂]

/-- Successive one-place shifts accumulate. -/
theorem shift_succ : ∀ (t : Term) (k c : Nat),
    shift 1 c (shift k c t) = shift (k + 1) c t := by
  intro t
  induction t with
  | var n =>
      intro k c
      by_cases h : n < c
      · simp [shift, h]
      · have h' : ¬ n + k < c := by omega
        simp [shift, h, h']
        omega
  | unit => intro k c; rfl
  | loc l => intro k c; rfl
  | abs T t ih | ref t ih | deref t ih => intro k c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ | assign t₁ t₂ ih₁ ih₂ =>
      intro k c; simp [shift, ih₁, ih₂]

end Term

open Term

/-- A store is a list of terms; `loc l` refers to position `l`. -/
abbrev Store := List Term

/-- Values: abstractions, `unit`, and locations. -/
inductive Value : Term → Prop where
  | abs (T : Ty) (t : Term) : Value (abs T t)
  | unit : Value unit
  | loc (l : Nat) : Value (loc l)

/-- Single-step evaluation of configurations, `(t, μ) ⟶ (t', μ')`
(TAPL figure 13-1). -/
inductive Step : Term → Store → Term → Store → Prop where
  | appAbs {T : Ty} {t v : Term} {μ : Store} :
      Value v → Step (app (abs T t) v) μ (subst 0 v t) μ
  | app1 {t₁ t₁' t₂ : Term} {μ μ' : Store} :
      Step t₁ μ t₁' μ' → Step (app t₁ t₂) μ (app t₁' t₂) μ'
  | app2 {v t t' : Term} {μ μ' : Store} :
      Value v → Step t μ t' μ' → Step (app v t) μ (app v t') μ'
  | refV {v : Term} {μ : Store} :                            -- E-RefV
      Value v → Step (ref v) μ (loc μ.length) (μ ++ [v])
  | refCong {t t' : Term} {μ μ' : Store} :                   -- E-Ref
      Step t μ t' μ' → Step (ref t) μ (ref t') μ'
  | derefLoc {l : Nat} {v : Term} {μ : Store} :              -- E-DerefLoc
      μ.get? l = some v → Step (deref (loc l)) μ v μ
  | derefCong {t t' : Term} {μ μ' : Store} :                 -- E-Deref
      Step t μ t' μ' → Step (deref t) μ (deref t') μ'
  | assign {l : Nat} {v : Term} {μ : Store} :                -- E-Assign
      Value v → l < μ.length →
      Step (assign (loc l) v) μ unit (μ.set l v)
  | assign1 {t₁ t₁' t₂ : Term} {μ μ' : Store} :              -- E-Assign1
      Step t₁ μ t₁' μ' → Step (assign t₁ t₂) μ (assign t₁' t₂) μ'
  | assign2 {v t t' : Term} {μ μ' : Store} :                 -- E-Assign2
      Value v → Step t μ t' μ' → Step (assign v t) μ (assign v t') μ'

/-! ## Typing with store typings -/

/-- Typing contexts (for term variables). -/
abbrev Ctx := List Ty

/-- A store typing assigns a type to each location. -/
abbrev StoreTy := List Ty

/-- The typing relation `Γ; St ⊢ t ∶ T` (TAPL figure 13-1). -/
inductive HasType : Ctx → StoreTy → Term → Ty → Prop where
  | var {Γ : Ctx} {St : StoreTy} {n : Nat} {T : Ty} :
      Γ.get? n = some T → HasType Γ St (var n) T
  | abs {Γ : Ctx} {St : StoreTy} {T₁ T₂ : Ty} {t : Term} :
      HasType (T₁ :: Γ) St t T₂ → HasType Γ St (abs T₁ t) (T₁ ⇒ T₂)
  | app {Γ : Ctx} {St : StoreTy} {T₁ T₂ : Ty} {t₁ t₂ : Term} :
      HasType Γ St t₁ (T₁ ⇒ T₂) → HasType Γ St t₂ T₁ →
      HasType Γ St (app t₁ t₂) T₂
  | unit {Γ : Ctx} {St : StoreTy} : HasType Γ St unit .unit
  | loc {Γ : Ctx} {St : StoreTy} {l : Nat} {T : Ty} :         -- T-Loc
      St.get? l = some T → HasType Γ St (loc l) (.ref T)
  | ref {Γ : Ctx} {St : StoreTy} {t : Term} {T : Ty} :        -- T-Ref
      HasType Γ St t T → HasType Γ St (ref t) (.ref T)
  | deref {Γ : Ctx} {St : StoreTy} {t : Term} {T : Ty} :      -- T-Deref
      HasType Γ St t (.ref T) → HasType Γ St (deref t) T
  | assign {Γ : Ctx} {St : StoreTy} {t₁ t₂ : Term} {T : Ty} : -- T-Assign
      HasType Γ St t₁ (.ref T) → HasType Γ St t₂ T →
      HasType Γ St (assign t₁ t₂) .unit

/-- A store `μ` is well typed under `St` (TAPL definition 13.5.1): same
size, and each cell holds a closed term of the type `St` assigns it. -/
def StoreWf (St : StoreTy) (μ : Store) : Prop :=
  μ.length = St.length ∧
  ∀ l T, St.get? l = some T → ∃ v, μ.get? l = some v ∧ HasType [] St v T

/-- `St'` extends `St` when it appends new locations (evaluation only ever
allocates; existing cells keep their types). -/
def Extends (St' St : StoreTy) : Prop := ∃ ext, St' = St ++ ext

theorem Extends.refl (St : StoreTy) : Extends St St :=
  ⟨[], by simp⟩

/-! ## List helper lemmas -/

theorem get?_append_left {α : Type} :
    ∀ (St ext : List α) (l : Nat) (T : α),
      St.get? l = some T → (St ++ ext).get? l = some T := by
  intro St
  induction St with
  | nil => intro ext l T h; cases h
  | cons B St ih =>
      intro ext l T h
      cases l with
      | zero => exact h
      | succ l => exact ih ext l T h

theorem get?_concat_self {α : Type} :
    ∀ (St : List α) (a : α), (St ++ [a]).get? St.length = some a := by
  intro St a
  induction St with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem get?_some_lt {α : Type} :
    ∀ (St : List α) (l : Nat) (T : α), St.get? l = some T → l < St.length := by
  intro St
  induction St with
  | nil => intro l T h; cases h
  | cons B St ih =>
      intro l T h
      cases l with
      | zero => simp
      | succ l => have := ih l T h; simp; omega

theorem get?_lt_some {α : Type} :
    ∀ (St : List α) (l : Nat), l < St.length → ∃ T, St.get? l = some T := by
  intro St
  induction St with
  | nil => intro l h; simp at h; omega
  | cons B St ih =>
      intro l h
      cases l with
      | zero => exact ⟨B, rfl⟩
      | succ l => exact ih l (by simp at h; omega)

theorem get?_set_self {α : Type} :
    ∀ (μ : List α) (l : Nat) (v : α), l < μ.length →
      (μ.set l v).get? l = some v := by
  intro μ
  induction μ with
  | nil => intro l v h; simp at h; omega
  | cons a μ ih =>
      intro l v h
      cases l with
      | zero => rfl
      | succ l => exact ih l v (by simp at h; omega)

theorem get?_set_other {α : Type} :
    ∀ (μ : List α) (l l' : Nat) (v : α), l ≠ l' →
      (μ.set l v).get? l' = μ.get? l' := by
  intro μ
  induction μ with
  | nil => intro l l' _ _; simp
  | cons a μ ih =>
      intro l l' v h
      cases l with
      | zero =>
          cases l' with
          | zero => omega
          | succ l' => rfl
      | succ l =>
          cases l' with
          | zero => rfl
          | succ l' => exact ih l l' v (by omega)

/-! ## Store-typing weakening -/

/-- **Lemma 13.5.4**: typing is preserved when the store typing grows. -/
theorem storety_weakening {Γ : Ctx} {St : StoreTy} {t : Term} {T : Ty}
    (h : HasType Γ St t T) :
    ∀ St', Extends St' St → HasType Γ St' t T := by
  induction h with
  | var hget => intro St' _; exact .var hget
  | abs _ ih => intro St' hx; exact .abs (ih St' hx)
  | app _ _ ih₁ ih₂ => intro St' hx; exact .app (ih₁ St' hx) (ih₂ St' hx)
  | unit => intro St' _; exact .unit
  | loc hget =>
      intro St' hx
      obtain ⟨ext, rfl⟩ := hx
      exact .loc (get?_append_left _ _ _ _ hget)
  | ref _ ih => intro St' hx; exact .ref (ih St' hx)
  | deref _ ih => intro St' hx; exact .deref (ih St' hx)
  | assign _ _ ih₁ ih₂ => intro St' hx; exact .assign (ih₁ St' hx) (ih₂ St' hx)

/-! ## Context insertion, weakening, substitution (as in chapter 9) -/

/-- Insert type `S` at position `c` of the context. -/
def insertAt (S : Ty) : Nat → Ctx → Ctx
  | 0, Γ => S :: Γ
  | _ + 1, [] => []
  | c + 1, T :: Γ => T :: insertAt S c Γ

theorem get?_insertAt_lt (S : Ty) :
    ∀ c Γ n, n < c → (insertAt S c Γ).get? n = Γ.get? n := by
  intro c
  induction c with
  | zero => intro Γ n h; omega
  | succ c ih =>
      intro Γ n h
      cases Γ with
      | nil => rfl
      | cons T Γ =>
          cases n with
          | zero => rfl
          | succ n => exact ih Γ n (by omega)

theorem get?_insertAt_ge (S : Ty) :
    ∀ c Γ n T, Γ.get? n = some T → c ≤ n →
      (insertAt S c Γ).get? (n + 1) = some T := by
  intro c
  induction c with
  | zero => intro Γ n T h _; exact h
  | succ c ih =>
      intro Γ n T h hc
      cases Γ with
      | nil => cases h
      | cons B Γ =>
          cases n with
          | zero => omega
          | succ n => exact ih Γ n T h (by omega)

theorem get?_insertAt_self (S : Ty) :
    ∀ c Γ T, (insertAt S c Γ).get? c = some T → T = S ∧ c ≤ Γ.length := by
  intro c
  induction c with
  | zero =>
      intro Γ T h
      cases h
      exact ⟨rfl, by omega⟩
  | succ c ih =>
      intro Γ T h
      cases Γ with
      | nil => cases h
      | cons B Γ =>
          obtain ⟨rfl, hle⟩ := ih Γ T h
          refine ⟨rfl, ?_⟩
          simp [List.length]
          omega

theorem get?_insertAt_gt (S : Ty) :
    ∀ c Γ n T, (insertAt S c Γ).get? n = some T → c < n →
      Γ.get? (n - 1) = some T := by
  intro c
  induction c with
  | zero =>
      intro Γ n T h hc
      cases n with
      | zero => omega
      | succ m => exact h
  | succ c ih =>
      intro Γ n T h hc
      cases Γ with
      | nil => cases h
      | cons B Γ =>
          cases n with
          | zero => omega
          | succ m =>
              cases m with
              | zero => omega
              | succ m' => exact ih Γ (m' + 1) T h (by omega)

/-- Weakening (shift-typing) in the term context. -/
theorem weakening {Γ : Ctx} {St : StoreTy} {t : Term} {T : Ty}
    (h : HasType Γ St t T) :
    ∀ c S, HasType (insertAt S c Γ) St (shift 1 c t) T := by
  induction h with
  | @var Γ St n T hget =>
      intro c S
      by_cases hn : n < c
      · simp only [shift, if_pos hn]
        exact .var (by rw [get?_insertAt_lt S c Γ n hn]; exact hget)
      · simp only [shift, if_neg hn]
        exact .var (get?_insertAt_ge S c Γ n T hget (by omega))
  | abs _ ih => intro c S; exact .abs (ih (c + 1) S)
  | app _ _ ih₁ ih₂ => intro c S; exact .app (ih₁ c S) (ih₂ c S)
  | unit => intro c S; exact .unit
  | loc hget => intro c S; exact .loc hget
  | ref _ ih => intro c S; exact .ref (ih c S)
  | deref _ ih => intro c S; exact .deref (ih c S)
  | assign _ _ ih₁ ih₂ => intro c S; exact .assign (ih₁ c S) (ih₂ c S)

/-- Iterated weakening at the bottom of the context. -/
theorem shift0_typing :
    ∀ k (Γ : Ctx) (St : StoreTy) (s : Term) (S : Ty), k ≤ Γ.length →
      HasType (Γ.drop k) St s S → HasType Γ St (shift k 0 s) S := by
  intro k
  induction k with
  | zero => intro Γ St s S _ h; rw [shift_zero]; exact h
  | succ k ih =>
      intro Γ St s S hk h
      cases Γ with
      | nil => simp at hk
      | cons B Γ =>
          have hw := weakening (ih Γ St s S (by simp at hk; omega) h) 0 B
          rw [shift_succ] at hw
          exact hw

/-- The substitution lemma. -/
theorem substitution {Δ : Ctx} {St : StoreTy} {t : Term} {T : Ty}
    (ht : HasType Δ St t T) :
    ∀ (Γ : Ctx) (k : Nat) (S : Ty) (s : Term),
      Δ = insertAt S k Γ → HasType (Γ.drop k) St s S →
      HasType Γ St (subst k s t) T := by
  induction ht with
  | @var Δ St n T hget =>
      intro Γ k S s heq hs
      subst heq
      by_cases h₁ : n < k
      · simp only [subst, if_pos h₁]
        exact .var (by rw [← get?_insertAt_lt S k Γ n h₁]; exact hget)
      · by_cases h₂ : n = k
        · subst h₂
          obtain ⟨rfl, hle⟩ := get?_insertAt_self S n Γ T hget
          simp only [subst, if_neg h₁, if_pos rfl]
          exact shift0_typing n Γ St s T hle hs
        · simp only [subst, if_neg h₁, if_neg h₂]
          exact .var (get?_insertAt_gt S k Γ n T hget (by omega))
  | @abs Δ St T₁ T₂ body _ ih =>
      intro Γ k S s heq hs
      exact .abs (ih (T₁ :: Γ) (k + 1) S s (by rw [heq]; rfl) hs)
  | app _ _ ih₁ ih₂ =>
      intro Γ k S s heq hs
      exact .app (ih₁ Γ k S s heq hs) (ih₂ Γ k S s heq hs)
  | unit => intro Γ k S s _ _; exact .unit
  | loc hget => intro Γ k S s _ _; exact .loc hget
  | ref _ ih =>
      intro Γ k S s heq hs
      exact .ref (ih Γ k S s heq hs)
  | deref _ ih =>
      intro Γ k S s heq hs
      exact .deref (ih Γ k S s heq hs)
  | assign _ _ ih₁ ih₂ =>
      intro Γ k S s heq hs
      exact .assign (ih₁ Γ k S s heq hs) (ih₂ Γ k S s heq hs)

/-! ## Store manipulation preserves well-typedness -/

/-- Allocating a well-typed value extends a well-typed store. -/
theorem storeWf_extend {St : StoreTy} {μ : Store} {v : Term} {T : Ty}
    (hwf : StoreWf St μ) (hv : HasType [] St v T) :
    StoreWf (St ++ [T]) (μ ++ [v]) := by
  obtain ⟨hlen, hcells⟩ := hwf
  constructor
  · simp [hlen]
  · intro l T' hget
    by_cases hl : l < St.length
    · obtain ⟨T'', hT''⟩ := get?_lt_some St l hl
      obtain ⟨w, hw, hwt⟩ := hcells l T'' hT''
      have := get?_append_left St [T] l T'' hT''
      rw [this] at hget
      cases hget
      exact ⟨w, get?_append_left μ [v] l w hw,
        storety_weakening hwt _ ⟨[T], rfl⟩⟩
    · -- l is the fresh location
      have hlSt : l = St.length := by
        have := get?_some_lt (St ++ [T]) l T' hget
        simp at this
        omega
      subst hlSt
      have : (St ++ [T]).get? St.length = some T := get?_concat_self St T
      rw [this] at hget
      cases hget
      refine ⟨v, ?_, storety_weakening hv _ ⟨[T], rfl⟩⟩
      rw [← hlen]
      exact get?_concat_self μ v

/-- Updating a cell with a value of its assigned type preserves store
well-typedness. -/
theorem storeWf_update {St : StoreTy} {μ : Store} {l : Nat} {v : Term}
    {T : Ty} (hwf : StoreWf St μ) (hget : St.get? l = some T)
    (hv : HasType [] St v T) : StoreWf St (μ.set l v) := by
  obtain ⟨hlen, hcells⟩ := hwf
  constructor
  · simp [hlen]
  · intro l' T' hget'
    by_cases hl : l = l'
    · subst hl
      rw [hget] at hget'
      cases hget'
      refine ⟨v, ?_, hv⟩
      apply get?_set_self
      rw [hlen]
      exact get?_some_lt St l T hget
    · obtain ⟨w, hw, hwt⟩ := hcells l' T' hget'
      exact ⟨w, by rw [get?_set_other μ l l' v hl]; exact hw, hwt⟩

/-! ## Preservation and progress -/

/-- **Theorem 13.5.3 (Preservation)**: if a well-typed configuration
steps, the result is well typed under some *extension* of the store
typing. -/
theorem preservation {St : StoreTy} {t : Term} {T : Ty}
    (h : HasType [] St t T) :
    ∀ t' (μ μ' : Store), StoreWf St μ → Step t μ t' μ' →
      ∃ St', Extends St' St ∧ HasType [] St' t' T ∧ StoreWf St' μ' := by
  generalize hΓ : ([] : Ctx) = Γ at h
  induction h with
  | var hget => subst hΓ; intro t' μ μ' _ hs; cases hs
  | abs _ _ => intro t' μ μ' _ hs; cases hs
  | unit => intro t' μ μ' _ hs; cases hs
  | loc _ => intro t' μ μ' _ hs; cases hs
  | app h₁ h₂ ih₁ ih₂ =>
      subst hΓ
      intro t' μ μ' hwf hs
      cases hs with
      | appAbs hv =>
          cases h₁ with
          | abs hbody =>
              exact ⟨_, .refl _, substitution hbody _ 0 _ _ rfl h₂, hwf⟩
      | app1 hstep =>
          obtain ⟨St', hx, ht', hwf'⟩ := ih₁ rfl _ _ _ hwf hstep
          exact ⟨St', hx, .app ht' (storety_weakening h₂ St' hx), hwf'⟩
      | app2 _ hstep =>
          obtain ⟨St', hx, ht', hwf'⟩ := ih₂ rfl _ _ _ hwf hstep
          exact ⟨St', hx, .app (storety_weakening h₁ St' hx) ht', hwf'⟩
  | @ref Γ St t T h ih =>
      subst hΓ
      intro t' μ μ' hwf hs
      cases hs with
      | refV hv =>
          refine ⟨St ++ [T], ⟨[T], rfl⟩, ?_, storeWf_extend hwf h⟩
          apply HasType.loc
          rw [hwf.1]
          exact get?_concat_self St T
      | refCong hstep =>
          obtain ⟨St', hx, ht', hwf'⟩ := ih rfl _ _ _ hwf hstep
          exact ⟨St', hx, .ref ht', hwf'⟩
  | @deref Γ St t T h ih =>
      subst hΓ
      intro t' μ μ' hwf hs
      cases hs with
      | derefLoc hget =>
          cases h with
          | loc hgetSt =>
              obtain ⟨w, hw, hwt⟩ := hwf.2 _ _ hgetSt
              rw [hget] at hw
              cases hw
              exact ⟨St, .refl _, hwt, hwf⟩
      | derefCong hstep =>
          obtain ⟨St', hx, ht', hwf'⟩ := ih rfl _ _ _ hwf hstep
          exact ⟨St', hx, .deref ht', hwf'⟩
  | @assign Γ St t₁ t₂ T h₁ h₂ ih₁ ih₂ =>
      subst hΓ
      intro t' μ μ' hwf hs
      cases hs with
      | assign hv hlt =>
          cases h₁ with
          | loc hgetSt =>
              exact ⟨St, .refl _, .unit, storeWf_update hwf hgetSt h₂⟩
      | assign1 hstep =>
          obtain ⟨St', hx, ht', hwf'⟩ := ih₁ rfl _ _ _ hwf hstep
          exact ⟨St', hx, .assign ht' (storety_weakening h₂ St' hx), hwf'⟩
      | assign2 _ hstep =>
          obtain ⟨St', hx, ht', hwf'⟩ := ih₂ rfl _ _ _ hwf hstep
          exact ⟨St', hx, .assign (storety_weakening h₁ St' hx) ht', hwf'⟩

/-- Canonical forms at arrow, `Ref`, and `Unit` types. -/
theorem canonical_arrow {St : StoreTy} {v : Term} {T₁ T₂ : Ty}
    (hv : Value v) (h : HasType [] St v (T₁ ⇒ T₂)) :
    ∃ S body, v = abs S body := by
  cases hv with
  | abs T t => exact ⟨_, _, rfl⟩
  | unit => cases h
  | loc l => cases h

theorem canonical_ref {St : StoreTy} {v : Term} {T : Ty}
    (hv : Value v) (h : HasType [] St v (.ref T)) :
    ∃ l, v = loc l ∧ St.get? l = some T := by
  cases hv with
  | abs T t => cases h
  | unit => cases h
  | loc l =>
      cases h with
      | loc hget => exact ⟨l, rfl, hget⟩

/-- Progress, auxiliary version with a context equation. -/
theorem progress' {Γ : Ctx} {St : StoreTy} {t : Term} {T : Ty}
    (h : HasType Γ St t T) :
    Γ = [] → ∀ μ, StoreWf St μ →
      Value t ∨ ∃ t' μ', Step t μ t' μ' := by
  induction h with
  | @var Γ St n T hget =>
      intro heq _ _
      subst heq
      simp [List.get?] at hget
  | abs _ _ => intro _ _ _; exact .inl (.abs _ _)
  | unit => intro _ _ _; exact .inl .unit
  | loc _ => intro _ _ _; exact .inl (.loc _)
  | app h₁ _ ih₁ ih₂ =>
      intro heq μ hwf
      subst heq
      rcases ih₁ rfl μ hwf with hv₁ | ⟨t₁', μ', hs⟩
      · rcases ih₂ rfl μ hwf with hv₂ | ⟨t₂', μ', hs⟩
        · obtain ⟨S, body, rfl⟩ := canonical_arrow hv₁ h₁
          exact .inr ⟨_, _, .appAbs hv₂⟩
        · exact .inr ⟨_, _, .app2 hv₁ hs⟩
      · exact .inr ⟨_, _, .app1 hs⟩
  | ref _ ih =>
      intro heq μ hwf
      subst heq
      rcases ih rfl μ hwf with hv | ⟨t', μ', hs⟩
      · exact .inr ⟨_, _, .refV hv⟩
      · exact .inr ⟨_, _, .refCong hs⟩
  | deref h ih =>
      intro heq μ hwf
      subst heq
      rcases ih rfl μ hwf with hv | ⟨t', μ', hs⟩
      · obtain ⟨l, rfl, hget⟩ := canonical_ref hv h
        obtain ⟨w, hw, _⟩ := hwf.2 _ _ hget
        exact .inr ⟨_, _, .derefLoc hw⟩
      · exact .inr ⟨_, _, .derefCong hs⟩
  | assign h₁ _ ih₁ ih₂ =>
      intro heq μ hwf
      subst heq
      rcases ih₁ rfl μ hwf with hv₁ | ⟨t₁', μ', hs⟩
      · rcases ih₂ rfl μ hwf with hv₂ | ⟨t₂', μ', hs⟩
        · obtain ⟨l, rfl, hget⟩ := canonical_ref hv₁ h₁
          have hlt : l < μ.length := by
            rw [hwf.1]
            exact get?_some_lt _ _ _ hget
          exact .inr ⟨_, _, .assign hv₂ hlt⟩
        · exact .inr ⟨_, _, .assign2 hv₁ hs⟩
      · exact .inr ⟨_, _, .assign1 hs⟩

/-- **Theorem 13.5.7 (Progress)**: a closed term, well typed under a
store typing realized by a well-typed store, is a value or can step. -/
theorem progress {St : StoreTy} {t : Term} {T : Ty} {μ : Store}
    (h : HasType [] St t T) (hwf : StoreWf St μ) :
    Value t ∨ ∃ t' μ', Step t μ t' μ' :=
  progress' h rfl μ hwf

/-! ## Examples -/

/-- Allocation: `(ref unit, ∅) ⟶ (loc 0, [unit])`. -/
example : Step (ref unit) [] (loc 0) [unit] := .refV .unit

/-- Dereferencing reads the store. -/
example : Step (deref (loc 0)) [unit] unit [unit] := .derefLoc rfl

/-- Assignment writes the store. -/
example : Step (assign (loc 0) unit) [unit] unit [unit] :=
  .assign .unit (by simp)

/-- A location is typed by the store typing:
`∅; [Unit] ⊢ !(loc 0) ∶ Unit`. -/
example : HasType [] [Ty.unit] (deref (loc 0)) .unit := .deref (.loc rfl)

/-- Aliasing at the type level: `λr:Ref Unit. r := unit` is a well-typed
function on references. -/
example : HasType [] [] (abs (.ref .unit) (assign (var 0) unit))
    (.ref .unit ⇒ .unit) :=
  .abs (.assign (.var rfl) .unit)

/-- The empty store is well typed under the empty store typing. -/
example : StoreWf [] [] := by
  constructor
  · rfl
  · intro l T h; cases h

end Chapter13
