import Chapter05.Lambda

/-!
# Chapter 6: Nameless Representation of Terms

The metatheory of the de Bruijn representation introduced (for us, already
used) in chapter 5: the algebraic laws relating shifting and substitution,
the notion of an `n`-term (TAPL definition 6.1.2), and preservation of
closedness by reduction.

TAPL's `removenames`/`restorenames` translations relate named and nameless
syntax; since this development is nameless throughout, they are not
formalized (see the README).
-/

namespace Chapter06

open Chapter05 Chapter05.Term

/-! ## Shifting laws -/

/-- Shifting by zero is the identity. -/
theorem shift_zero (t : Term) : ∀ c, shift 0 c t = t := by
  induction t with
  | var n =>
      intro c
      by_cases h : n < c <;> simp [shift, h]
  | abs t ih => intro c; simp [shift, ih]
  | app t₁ t₂ ih₁ ih₂ => intro c; simp [shift, ih₁, ih₂]

/-- Merging two shifts: shifting by `d'` at cutoff `c` and then by `d` at
any cutoff `c'` inside the freshly created gap is a single shift by
`d + d'`. -/
theorem shift_merge (t : Term) :
    ∀ d d' c c', c ≤ c' → c' ≤ c + d' →
      shift d c' (shift d' c t) = shift (d + d') c t := by
  induction t with
  | var n =>
      intro d d' c c' h₁ h₂
      by_cases h : n < c
      · have h' : n < c' := by omega
        simp [shift, h, h']
      · have h' : ¬ n + d' < c' := by omega
        simp [shift, h, h']
        omega
  | abs t ih =>
      intro d d' c c' h₁ h₂
      simp only [shift]
      rw [ih d d' (c + 1) (c' + 1) (by omega) (by omega)]
  | app t₁ t₂ ih₁ ih₂ =>
      intro d d' c c' h₁ h₂
      simp only [shift]
      rw [ih₁ d d' c c' h₁ h₂, ih₂ d d' c c' h₁ h₂]

/-- Shifts at independent cutoffs commute. -/
theorem shift_comm (t : Term) :
    ∀ d d' c c', c' ≤ c →
      shift d' c' (shift d c t) = shift d (c + d') (shift d' c' t) := by
  induction t with
  | var n =>
      intro d d' c c' h
      by_cases h₁ : n < c'
      · have h₂ : n < c := by omega
        have h₃ : n < c + d' := by omega
        simp [shift, h₁, h₂, h₃]
      · by_cases h₂ : n < c
        · have h₃ : n + d' < c + d' := by omega
          simp [shift, h₁, h₂, h₃]
        · have h₃ : ¬ n + d < c' := by omega
          have h₄ : ¬ n + d' < c + d' := by omega
          simp [shift, h₁, h₂, h₃, h₄]
          omega
  | abs t ih =>
      intro d d' c c' h
      simp only [shift]
      rw [ih d d' (c + 1) (c' + 1) (by omega)]
      have : c + 1 + d' = c + d' + 1 := by omega
      rw [this]
  | app t₁ t₂ ih₁ ih₂ =>
      intro d d' c c' h
      simp only [shift]
      rw [ih₁ d d' c c' h, ih₂ d d' c c' h]

/-! ## Substitution laws -/

/-- Substituting for a variable that was just created by a (large enough)
shift cancels one unit of the shift. -/
theorem subst_shift_cancel (t : Term) :
    ∀ s k d c, c ≤ k → k < c + d + 1 →
      subst k s (shift (d + 1) c t) = shift d c t := by
  induction t with
  | var n =>
      intro s k d c h₁ h₂
      by_cases h : n < c
      · have h' : n < k := by omega
        simp [shift, subst, h, h']
      · have h₃ : ¬ n + (d + 1) < k := by omega
        have h₄ : ¬ n + (d + 1) = k := by omega
        simp [shift, subst, h, h₃, h₄]
        omega
  | abs t ih =>
      intro s k d c h₁ h₂
      simp only [shift, subst]
      rw [ih s (k + 1) d (c + 1) (by omega) (by omega)]
  | app t₁ t₂ ih₁ ih₂ =>
      intro s k d c h₁ h₂
      simp only [shift, subst]
      rw [ih₁ s k d c h₁ h₂, ih₂ s k d c h₁ h₂]

/-- Shifting distributes over substitution (TAPL exercise 6.2.8, adapted to
the fused substitution operation). -/
theorem shift_subst_dist (t : Term) :
    ∀ s d c k,
      shift d (c + k) (subst k s t) =
        subst k (shift d c s) (shift d (c + k + 1) t) := by
  induction t with
  | var n =>
      intro s d c k
      by_cases h₁ : n < k
      · have h₂ : n < c + k := by omega
        have h₃ : n < c + k + 1 := by omega
        simp [shift, subst, h₁, h₂, h₃]
      · by_cases h₂ : n = k
        · subst h₂
          have h₃ : n < c + n + 1 := by omega
          simp [shift, subst, h₃, Nat.lt_irrefl]
          rw [← shift_comm s d n c 0 (by omega)]
        · by_cases h₃ : n < c + k + 1
          · have h₄ : n - 1 < c + k := by omega
            simp [shift, subst, h₁, h₂, h₃, h₄]
          · have h₄ : ¬ n - 1 < c + k := by omega
            have h₅ : ¬ n + d < k := by omega
            have h₆ : ¬ n + d = k := by omega
            simp [shift, subst, h₁, h₂, h₃, h₄, h₅, h₆]
            omega
  | abs t ih =>
      intro s d c k
      simp only [shift, subst]
      have h1 : c + k + 1 = c + (k + 1) := by omega
      rw [h1, ih s d c (k + 1)]
  | app t₁ t₂ ih₁ ih₂ =>
      intro s d c k
      simp only [shift, subst]
      rw [ih₁ s d c k, ih₂ s d c k]

/-- Substitution passes under a shift with a lower cutoff. -/
theorem subst_shift_dist (t : Term) :
    ∀ s d c k, c + d ≤ k →
      subst k s (shift d c t) = shift d c (subst (k - d) s t) := by
  induction t with
  | var n =>
      intro s d c k h
      by_cases h₁ : n < c
      · have h₂ : n < k := by omega
        have h₃ : n < k - d := by omega
        simp [shift, subst, h₁, h₂, h₃]
      · by_cases h₂ : n + d < k
        · have h₃ : n < k - d := by omega
          simp [shift, subst, h₁, h₂, h₃]
        · by_cases h₃ : n + d = k
          · have h₄ : n = k - d := by omega
            subst h₄
            have hk : k - d + d = k := by omega
            simp [shift, subst, h₁, hk, Nat.lt_irrefl]
            rw [shift_merge s d (k - d) 0 c (by omega) (by omega)]
            have : d + (k - d) = k := by omega
            rw [this]
          · have h₄ : ¬ n < k - d := by omega
            have h₅ : ¬ n = k - d := by omega
            have h₆ : ¬ n - 1 < c := by omega
            simp [shift, subst, h₁, h₂, h₃, h₄, h₅, h₆]
            omega
  | abs t ih =>
      intro s d c k h
      simp only [shift, subst]
      rw [ih s d (c + 1) (k + 1) (by omega)]
      have : k + 1 - d = k - d + 1 := by omega
      rw [this]
  | app t₁ t₂ ih₁ ih₂ =>
      intro s d c k h
      simp only [shift, subst]
      rw [ih₁ s d c k h, ih₂ s d c k h]

/-- The substitution lemma: two substitutions commute
(the classic identity `[k ↦ s]([j ↦ u] t) = [j ↦ [k−j ↦ s]u]([k+1 ↦ s] t)`
for `j ≤ k`, cf. TAPL exercise 6.2.8). -/
theorem subst_subst (t : Term) :
    ∀ s u j k, j ≤ k →
      subst k s (subst j u t) =
        subst j (subst (k - j) s u) (subst (k + 1) s t) := by
  induction t with
  | var n =>
      intro s u j k h
      by_cases h₁ : n < j
      · have h₂ : n < k := by omega
        have h₃ : n < k + 1 := by omega
        simp [subst, h₁, h₂, h₃]
      · by_cases h₂ : n = j
        · subst h₂
          have h₃ : n < k + 1 := by omega
          simp [subst, h₁, h₃, Nat.lt_irrefl]
          rw [subst_shift_dist u s n 0 k (by omega)]
        · by_cases h₃ : n < k + 1
          · have h₄ : n - 1 < k := by omega
            simp [subst, h₁, h₂, h₃, h₄]
          · by_cases h₄ : n = k + 1
            · subst h₄
              have h₅ : ¬ k + 1 - 1 < k := by omega
              have h₆ : k + 1 - 1 = k := by omega
              simp [subst, h₁, h₂, h₃, h₅, h₆, Nat.lt_irrefl]
              rw [subst_shift_cancel s _ j k 0 (by omega) (by omega)]
            · have h₅ : ¬ n - 1 < k := by omega
              have h₆ : ¬ n - 1 = k := by omega
              have h₇ : ¬ n - 1 < j := by omega
              have h₈ : ¬ n - 1 = j := by omega
              simp [subst, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  | abs t ih =>
      intro s u j k h
      simp only [subst]
      rw [ih s u (j + 1) (k + 1) (by omega)]
      have : k + 1 - (j + 1) = k - j := by omega
      rw [this]
  | app t₁ t₂ ih₁ ih₂ =>
      intro s u j k h
      simp only [subst]
      rw [ih₁ s u j k h, ih₂ s u j k h]

/-! ## `n`-terms and closedness (TAPL definition 6.1.2) -/

/-- `Closed n t` says `t` is an *n-term*: all its free variables are `< n`.
`Closed 0 t` is the usual notion of a closed term. -/
def Closed (n : Nat) : Term → Prop
  | var m => m < n
  | abs t => Closed (n + 1) t
  | app t₁ t₂ => Closed n t₁ ∧ Closed n t₂

/-- Shifting at a cutoff above every free variable does nothing. -/
theorem shift_closed_id (t : Term) :
    ∀ d c, Closed c t → shift d c t = t := by
  induction t with
  | var n => intro d c h; simp [Closed] at h; simp [shift, h]
  | abs t ih => intro d c h; simp [Closed] at h; simp [shift, ih d (c + 1) h]
  | app t₁ t₂ ih₁ ih₂ =>
      intro d c h
      simp [Closed] at h
      simp [shift, ih₁ d c h.1, ih₂ d c h.2]

/-- Shifting an `n`-term by `d` yields an `(n+d)`-term. -/
theorem Closed.shift (t : Term) :
    ∀ n d c, Closed n t → Closed (n + d) (Term.shift d c t) := by
  induction t with
  | var m =>
      intro n d c h
      simp [Closed] at h
      by_cases h' : m < c <;> simp [Term.shift, h', Closed] <;> omega
  | abs t ih =>
      intro n d c h
      show Closed (n + d + 1) (Term.shift d (c + 1) t)
      have := ih (n + 1) d (c + 1) h
      have heq : n + 1 + d = n + d + 1 := by omega
      exact heq ▸ this
  | app t₁ t₂ ih₁ ih₂ =>
      intro n d c h
      have h' : Closed n t₁ ∧ Closed n t₂ := h
      exact ⟨ih₁ n d c h'.1, ih₂ n d c h'.2⟩

/-- Substituting for a variable that does not occur free does nothing. -/
theorem subst_closed_id (t : Term) :
    ∀ s k, Closed k t → subst k s t = t := by
  induction t with
  | var n =>
      intro s k h
      simp [Closed] at h
      simp [subst, h]
  | abs t ih => intro s k h; simp [Closed] at h; simp [subst, ih s (k + 1) h]
  | app t₁ t₂ ih₁ ih₂ =>
      intro s k h
      simp [Closed] at h
      simp [subst, ih₁ s k h.1, ih₂ s k h.2]

/-- Substituting an `n`-term into an `(n+k+1)`-term at index `k` yields an
`(n+k)`-term: substitution consumes one free variable. -/
theorem Closed.subst (t : Term) :
    ∀ s n k, Closed n s → Closed (n + k + 1) t →
      Closed (n + k) (Term.subst k s t) := by
  induction t with
  | var m =>
      intro s n k hs ht
      simp [Closed] at ht
      by_cases h₁ : m < k
      · simp [Term.subst, h₁, Closed]; omega
      · by_cases h₂ : m = k
        · subst h₂
          simp [Term.subst, h₁]
          have := Closed.shift s n m 0 hs
          rw [Nat.add_comm n m] at this
          rw [Nat.add_comm n m]
          exact this
        · simp [Term.subst, h₁, h₂, Closed]; omega
  | abs t ih =>
      intro s n k hs ht
      exact ih s n (k + 1) hs ht
  | app t₁ t₂ ih₁ ih₂ =>
      intro s n k hs ht
      have ht' : Closed (n + k + 1) t₁ ∧ Closed (n + k + 1) t₂ := ht
      exact ⟨ih₁ s n k hs ht'.1, ih₂ s n k hs ht'.2⟩

/-! ## Reduction preserves closedness -/

/-- Full beta-reduction (and hence call-by-value evaluation) maps `n`-terms
to `n`-terms: no new free variables appear during reduction. -/
theorem FullBeta.closed {t t' : Term} (h : t ⟶β t') :
    ∀ n, Closed n t → Closed n t' := by
  induction h with
  | @beta t s =>
      intro n h
      have h' : Closed (n + 1) t ∧ Closed n s := h
      exact Closed.subst t s n 0 h'.2 h'.1
  | absCong _ ih => intro n h; exact ih (n + 1) h
  | app1 _ ih =>
      intro n h
      have h' : _ ∧ _ := h
      exact ⟨ih n h'.1, h'.2⟩
  | app2 _ ih =>
      intro n h
      have h' : _ ∧ _ := h
      exact ⟨h'.1, ih n h'.2⟩

/-- Call-by-value evaluation preserves closedness. -/
theorem Step.closed {t t' : Term} (h : t ⟶ t') {n : Nat}
    (hc : Closed n t) : Closed n t' :=
  FullBeta.closed h.toFullBeta n hc

/-! ## Examples (cf. TAPL exercise 6.2.2) -/

/-- `↑²(λ.λ. 1 (0 2))  =  λ.λ. 1 (0 4)` -/
example : shift 2 0 (ƛ ƛ #1 ⬝ (#0 ⬝ #2)) = ƛ ƛ #1 ⬝ (#0 ⬝ #4) := by decide

/-- `↑²(λ. 0 1 (λ. 0 1 2))  =  λ. 0 3 (λ. 0 1 4)` -/
example : shift 2 0 (ƛ #0 ⬝ #1 ⬝ (ƛ #0 ⬝ #1 ⬝ #2)) =
    ƛ #0 ⬝ #3 ⬝ (ƛ #0 ⬝ #1 ⬝ #4) := by decide

/-- Substituting variable `0` by variable `1`: the substituted variable is
shifted as it goes under binders (`#1` becomes `#3` under two λs). -/
example : subst 0 (#1) (#0 ⬝ (ƛ ƛ #2)) = #1 ⬝ (ƛ ƛ #3) := by decide

/-- `ω` is a `0`-term (closed). -/
example : Closed 0 Chapter05.omega :=
  ⟨⟨Nat.one_pos, Nat.one_pos⟩, Nat.one_pos, Nat.one_pos⟩

end Chapter06
