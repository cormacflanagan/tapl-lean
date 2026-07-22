/-!
# Chapter 19: Featherweight Java

Featherweight Java (FJ): the minimal core of Java — classes with fields,
inheritance, methods, object creation, and casts — small enough for a
complete metatheory (TAPL figures 19-1 … 19-4).

FJ differs pleasantly from the lambda-calculi of the other chapters:
terms contain **no binders** (method parameters are bound only at the
method-table level), so substitution is plain simultaneous replacement of
named variables with no capture or shifting. The price is elsewhere:
constructors and methods are n-ary (a mutual `Term`/`TermList` syntax),
and the auxiliary functions `fields`, `mtype`, `mbody` walk the class
table's inheritance chains (here: inductive relations, so no termination
conditions are needed).

Design notes (see the README):
* the three cast typing rules (`T-UCast`, `T-DCast`, `T-SCast`) are merged
  into one liberal rule — the split exists in TAPL only to flag "stupid"
  casts, and the merged system types strictly more terms while satisfying
  the same preservation theorem;
* the properties of a *well-formed class table* that the metatheory needs
  (no `Object` entry, override consistency, well-typed method bodies) are
  bundled as the record `CTOk` and assumed where required — they are
  exactly the semantic content of TAPL's `CT OK` judgment;
* progress is proved for cast-free terms (TAPL theorem 19.5.2's honest
  core: a failing downcast is a legitimate stuck state).
-/

namespace Chapter19

/-- Class, field, method and variable names. -/
abbrev Name := String

/-- Method definition: `B m(B̄ x̄) { return body; }`. -/
structure MethodDef (Term : Type) where
  name : Name
  params : List (Name × Name)     -- (parameter, class)
  ret : Name
  body : Term

mutual
/-- Terms of FJ (mutual with argument lists, since constructors and
methods are n-ary). -/
inductive Term : Type where
  | var (x : Name)                            -- x
  | fld (t : Term) (f : Name)                 -- t.f
  | invk (t : Term) (m : Name) (ts : TermList)  -- t.m(t̄)
  | new (C : Name) (ts : TermList)            -- new C(t̄)
  | cast (C : Name) (t : Term)                -- (C) t

inductive TermList : Type where
  | nil
  | cons (t : Term) (ts : TermList)
end

/-- Convert an argument list to a `List`. -/
def TermList.toList : TermList → List Term
  | .nil => []
  | .cons t ts => t :: ts.toList

/-- Class definition: `class C extends D { C̄ f̄; … methods }` (the
constructor is determined by the fields and omitted, as in TAPL). -/
structure ClassDef where
  superclass : Name
  fields : List (Name × Name)                 -- (field, class)
  methods : List (MethodDef Term)

/-- A class table maps class names to definitions; `Object` must not
appear. -/
abbrev ClassTable := List (Name × ClassDef)

/-- Look up a method in a class body. -/
def findMethod (cd : ClassDef) (m : Name) : Option (MethodDef Term) :=
  cd.methods.find? (fun md => md.name == m)

/-- Look up a field name, returning its position and class. -/
def lookupIdx : List (Name × Name) → Name → Option (Nat × Name)
  | [], _ => none
  | (f', C) :: rest, f =>
      if f' = f then some (0, C)
      else (lookupIdx rest f).map (fun p => (p.1 + 1, p.2))

/-- Typing environments: variable name ↦ class name. -/
abbrev Env := List (Name × Name)

/-! ## Values, cast-freeness, substitution -/

mutual
/-- A value is a `new` whose arguments are values. -/
def isValueT : Term → Bool
  | .new _ args => isValueL args
  | _ => false

def isValueL : TermList → Bool
  | .nil => true
  | .cons t ts => isValueT t && isValueL ts
end

mutual
/-- Cast-free terms (for the progress theorem). -/
def castFreeT : Term → Bool
  | .var _ => true
  | .fld t _ => castFreeT t
  | .invk t _ ts => castFreeT t && castFreeL ts
  | .new _ ts => castFreeL ts
  | .cast _ _ => false

def castFreeL : TermList → Bool
  | .nil => true
  | .cons t ts => castFreeT t && castFreeL ts
end

mutual
/-- Simultaneous substitution of terms for named variables. No shifting,
no capture: FJ terms contain no binders. -/
def substT (σ : List (Name × Term)) : Term → Term
  | .var x =>
      match σ.lookup x with
      | some u => u
      | none => .var x
  | .fld t f => .fld (substT σ t) f
  | .invk t m ts => .invk (substT σ t) m (substL σ ts)
  | .new C ts => .new C (substL σ ts)
  | .cast C t => .cast C (substT σ t)

def substL (σ : List (Name × Term)) : TermList → TermList
  | .nil => .nil
  | .cons t ts => .cons (substT σ t) (substL σ ts)
end

variable (CT : ClassTable)

/-! ## Subtyping and the class-table relations -/

/-- Subtyping: reflexivity, transitivity, and `extends` edges
(TAPL fig. 19-1). -/
inductive Sub : Name → Name → Prop where
  | refl (C : Name) : Sub C C
  | trans {C D E : Name} : Sub C D → Sub D E → Sub C E
  | ext {C : Name} {cd : ClassDef} :
      CT.lookup C = some cd → Sub C cd.superclass

/-- `HasFields C fs`: the fields of `C`, superclass fields first
(TAPL's `fields(C)`, as a relation — no termination condition needed). -/
inductive HasFields : Name → List (Name × Name) → Prop where
  | obj : HasFields "Object" []
  | step {C : Name} {cd : ClassDef} {fs : List (Name × Name)} :
      CT.lookup C = some cd → HasFields cd.superclass fs →
      HasFields C (fs ++ cd.fields)

/-- `MType m C Bs B`: method `m` on class `C` has parameter classes `Bs`
and return class `B` (TAPL's `mtype`). -/
inductive MType : Name → Name → List Name → Name → Prop where
  | here {C : Name} {cd : ClassDef} {m : Name} {md : MethodDef Term} :
      CT.lookup C = some cd → findMethod cd m = some md →
      MType m C (md.params.map (·.2)) md.ret
  | super {C : Name} {cd : ClassDef} {m : Name} {Bs : List Name} {B : Name} :
      CT.lookup C = some cd → findMethod cd m = none →
      MType m cd.superclass Bs B → MType m C Bs B

/-- `MBody m C xs body`: method `m` on class `C` has parameter names `xs`
and body `body` (TAPL's `mbody`). -/
inductive MBody : Name → Name → List Name → Term → Prop where
  | here {C : Name} {cd : ClassDef} {m : Name} {md : MethodDef Term} :
      CT.lookup C = some cd → findMethod cd m = some md →
      MBody m C (md.params.map (·.1)) md.body
  | super {C : Name} {cd : ClassDef} {m : Name} {xs : List Name} {t : Term} :
      CT.lookup C = some cd → findMethod cd m = none →
      MBody m cd.superclass xs t → MBody m C xs t

/-! ## Evaluation (TAPL fig. 19-3) -/

mutual
/-- Single-step evaluation (call-by-value order: receiver, then
arguments left to right). -/
inductive Step : Term → Term → Prop where
  | projNew {C f : Name} {fs : List (Name × Name)} {i : Nat} {Ci : Name}
      {args : TermList} {v : Term} :
      HasFields CT C fs → lookupIdx fs f = some (i, Ci) →
      args.toList.get? i = some v → isValueL args = true →
      Step (.fld (.new C args) f) v                        -- E-ProjNew
  | invkNew {C m : Name} {xs : List Name} {body : Term}
      {vs us : TermList} :
      MBody CT m C xs body → isValueL vs = true → isValueL us = true →
      Step (.invk (.new C vs) m us)
        (substT (("this", .new C vs) :: List.zip xs us.toList) body)
                                                           -- E-InvkNew
  | castNew {C D : Name} {vs : TermList} :
      Sub CT C D → isValueL vs = true →
      Step (.cast D (.new C vs)) (.new C vs)               -- E-CastNew
  | fldCong {t t' : Term} {f : Name} :
      Step t t' → Step (.fld t f) (.fld t' f)              -- E-Field
  | invkRecv {t t' : Term} {m : Name} {ts : TermList} :
      Step t t' → Step (.invk t m ts) (.invk t' m ts)      -- E-Invk-Recv
  | invkArgs {t : Term} {m : Name} {ts ts' : TermList} :
      isValueT t = true → StepArgs ts ts' →
      Step (.invk t m ts) (.invk t m ts')                  -- E-Invk-Arg
  | newArgs {C : Name} {ts ts' : TermList} :
      StepArgs ts ts' → Step (.new C ts) (.new C ts')      -- E-New-Arg
  | castCong {C : Name} {t t' : Term} :
      Step t t' → Step (.cast C t) (.cast C t')            -- E-Cast

/-- One argument in a list steps (leftmost non-value first). -/
inductive StepArgs : TermList → TermList → Prop where
  | here {t t' : Term} {ts : TermList} :
      Step t t' → StepArgs (.cons t ts) (.cons t' ts)
  | there {t : Term} {ts ts' : TermList} :
      isValueT t = true → StepArgs ts ts' →
      StepArgs (.cons t ts) (.cons t ts')
end

/-! ## Typing (TAPL fig. 19-4, with the merged cast rule) -/

mutual
/-- The typing relation `Γ ⊢ t : C`. FJ typing is syntax-directed:
subtyping enters only at argument positions. -/
inductive HasType : Env → Term → Name → Prop where
  | var {Γ : Env} {x : Name} {C : Name} :
      Γ.lookup x = some C → HasType Γ (.var x) C           -- T-Var
  | fld {Γ : Env} {t : Term} {C₀ f Ci : Name}
      {fs : List (Name × Name)} {i : Nat} :
      HasType Γ t C₀ → HasFields CT C₀ fs →
      lookupIdx fs f = some (i, Ci) →
      HasType Γ (.fld t f) Ci                              -- T-Field
  | invk {Γ : Env} {t : Term} {m C₀ B : Name} {Bs : List Name}
      {ts : TermList} :
      HasType Γ t C₀ → MType CT m C₀ Bs B → ArgsTyped Γ ts Bs →
      HasType Γ (.invk t m ts) B                           -- T-Invk
  | new {Γ : Env} {C : Name} {fs : List (Name × Name)} {ts : TermList} :
      HasFields CT C fs → ArgsTyped Γ ts (fs.map (·.2)) →
      HasType Γ (.new C ts) C                              -- T-New
  | cast {Γ : Env} {t : Term} {C D : Name} :
      HasType Γ t D → HasType Γ (.cast C t) C              -- T-Cast (merged)

/-- Argument lists typed against expected classes, with subtyping. -/
inductive ArgsTyped : Env → TermList → List Name → Prop where
  | nil {Γ : Env} : ArgsTyped Γ .nil []
  | cons {Γ : Env} {t : Term} {ts : TermList} {A B : Name}
      {Bs : List Name} :
      HasType Γ t A → Sub CT A B → ArgsTyped Γ ts Bs →
      ArgsTyped Γ (.cons t ts) (B :: Bs)
end

/-- The semantic content of TAPL's `CT OK` judgment, as used by the
metatheory: no `Object` entry, override consistency, and well-typed
method bodies. -/
structure CTOk : Prop where
  obj_none : CT.lookup "Object" = none
  mtype_sub : ∀ {C D m Bs B},
    Sub CT C D → MType CT m D Bs B → MType CT m C Bs B
  method_typing : ∀ {m C xs body Bs B},
    MBody CT m C xs body → MType CT m C Bs B →
    ∃ C₀ E, Sub CT C C₀ ∧
      HasType CT (("this", C₀) :: List.zip xs Bs) body E ∧ Sub CT E B

/-! ## List and lookup lemmas -/

theorem lookupIdx_append {fs ext : List (Name × Name)} {f : Name}
    {p : Nat × Name} (h : lookupIdx fs f = some p) :
    lookupIdx (fs ++ ext) f = some p := by
  induction fs generalizing p with
  | nil => cases h
  | cons hd rest ih =>
      obtain ⟨f', C⟩ := hd
      by_cases hf : f' = f
      · simp [lookupIdx, hf] at h ⊢
        exact h
      · simp [lookupIdx, hf] at h ⊢
        obtain ⟨q, hq, hpq⟩ := h
        exact ⟨q, ih hq, hpq⟩

theorem lookupIdx_get {fs : List (Name × Name)} {f : Name} {i : Nat}
    {Ci : Name} (h : lookupIdx fs f = some (i, Ci)) :
    (fs.map (·.2)).get? i = some Ci := by
  induction fs generalizing i with
  | nil => cases h
  | cons hd rest ih =>
      obtain ⟨f', C⟩ := hd
      by_cases hf : f' = f
      · simp [lookupIdx, hf] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      · simp [lookupIdx, hf] at h
        obtain ⟨⟨j, Cj⟩, hq, hi, hC⟩ := h
        subst hi
        subst hC
        exact ih hq

theorem get?_some_of_lt {α : Type} :
    ∀ (l : List α) (i : Nat), i < l.length → ∃ a, l.get? i = some a := by
  intro l
  induction l with
  | nil => intro i h; simp at h; omega
  | cons a l ih =>
      intro i h
      cases i with
      | zero => exact ⟨a, rfl⟩
      | succ i => exact ih i (by simp at h; omega)

theorem get?_lt_length {α : Type} :
    ∀ (l : List α) (i : Nat) (a : α), l.get? i = some a → i < l.length := by
  intro l
  induction l with
  | nil => intro i a h; cases h
  | cons b l ih =>
      intro i a h
      cases i with
      | zero => simp
      | succ i => have := ih i a h; simp; omega

theorem env_lookup_append_some {Δ Γ : Env} {x : Name} {C : Name}
    (h : Δ.lookup x = some C) : (Δ ++ Γ).lookup x = some C := by
  induction Δ with
  | nil => cases h
  | cons hd Δ ih =>
      obtain ⟨y, D⟩ := hd
      by_cases hxy : x == y
      · simp [List.lookup, hxy] at h ⊢
        exact h
      · simp [List.lookup, hxy] at h ⊢
        exact ih h

theorem env_lookup_append_none {Δ Γ : Env} {x : Name}
    (h : Δ.lookup x = none) : (Δ ++ Γ).lookup x = Γ.lookup x := by
  induction Δ with
  | nil => rfl
  | cons hd Δ ih =>
      obtain ⟨y, D⟩ := hd
      by_cases hxy : x == y
      · simp [List.lookup, hxy] at h
      · simp [List.lookup, hxy] at h ⊢
        exact ih h

/-! ## Class-table lemmas -/

variable {CT : ClassTable}

/-- `fields` is deterministic (given that `Object` has no entry). -/
theorem fields_det (hobj : CT.lookup "Object" = none) :
    ∀ {C fs fs'}, HasFields CT C fs → HasFields CT C fs' → fs = fs' := by
  intro C fs fs' h₁
  induction h₁ generalizing fs' with
  | obj =>
      intro h₂
      cases h₂ with
      | obj => rfl
      | step hlook _ => rw [hobj] at hlook; cases hlook
  | step hlook _ ih =>
      intro h₂
      cases h₂ with
      | obj => rw [hobj] at hlook; cases hlook
      | step hlook' hsup' =>
          rw [hlook] at hlook'
          cases hlook'
          rw [ih hsup']

/-- Fields are preserved (as a prefix) going down the subtype order: a
subclass has all its superclass's fields, first, at the same positions. -/
theorem fields_sub :
    ∀ {C D fsD}, Sub CT C D → HasFields CT D fsD →
      ∃ ext, HasFields CT C (fsD ++ ext) := by
  intro C D fsD hsub
  induction hsub generalizing fsD with
  | refl C => intro h; exact ⟨[], by simpa using h⟩
  | trans _ _ ih₁ ih₂ =>
      intro h
      obtain ⟨ext₁, h₁⟩ := ih₂ h
      obtain ⟨ext₂, h₂⟩ := ih₁ h₁
      exact ⟨ext₁ ++ ext₂, by simpa using h₂⟩
  | ext hlook =>
      intro h
      exact ⟨_, .step hlook h⟩

/-- `mtype` and `mbody` find the same method, so parameter counts agree. -/
theorem mbody_mtype_length :
    ∀ {m C xs body Bs B}, MBody CT m C xs body → MType CT m C Bs B →
      xs.length = Bs.length := by
  intro m C xs body Bs B h₁
  induction h₁ generalizing Bs B with
  | here hlook hfind =>
      intro h₂
      cases h₂ with
      | here hlook' hfind' =>
          rw [hlook] at hlook'
          cases hlook'
          rw [hfind] at hfind'
          cases hfind'
          simp
      | super hlook' hfind' _ =>
          rw [hlook] at hlook'
          cases hlook'
          rw [hfind] at hfind'
          cases hfind'
  | super hlook hfind _ ih =>
      intro h₂
      cases h₂ with
      | here hlook' hfind' =>
          rw [hlook] at hlook'
          cases hlook'
          rw [hfind] at hfind'
          cases hfind'
      | super hlook' hfind' hsup' =>
          rw [hlook] at hlook'
          cases hlook'
          exact ih hsup'

/-- Where `mtype` is defined, `mbody` is too. -/
theorem mtype_mbody :
    ∀ {m C Bs B}, MType CT m C Bs B →
      ∃ xs body, MBody CT m C xs body := by
  intro m C Bs B h
  induction h with
  | here hlook hfind => exact ⟨_, _, .here hlook hfind⟩
  | super hlook hfind _ ih =>
      obtain ⟨xs, body, hb⟩ := ih
      exact ⟨xs, body, .super hlook hfind hb⟩

/-! ## Environment weakening -/

mutual
/-- A term typed in `Δ` is typed in `Δ ++ Γ` (every lookup that succeeded
still succeeds). -/
theorem weaken_t : ∀ (t : Term) {Δ Γ C}, HasType CT Δ t C →
    HasType CT (Δ ++ Γ) t C
  | .var x, Δ, Γ, C, h => by
      cases h with
      | var hget => exact .var (env_lookup_append_some hget)
  | .fld t f, Δ, Γ, C, h => by
      cases h with
      | fld ht hf hl => exact .fld (weaken_t t ht) hf hl
  | .invk t m ts, Δ, Γ, C, h => by
      cases h with
      | invk ht hm ha => exact .invk (weaken_t t ht) hm (weaken_l ts ha)
  | .new C₀ ts, Δ, Γ, C, h => by
      cases h with
      | new hf ha => exact .new hf (weaken_l ts ha)
  | .cast C₀ t, Δ, Γ, C, h => by
      cases h with
      | cast ht => exact .cast (weaken_t t ht)

theorem weaken_l : ∀ (ts : TermList) {Δ Γ Bs}, ArgsTyped CT Δ ts Bs →
    ArgsTyped CT (Δ ++ Γ) ts Bs
  | .nil, Δ, Γ, Bs, h => by
      cases h with
      | nil => exact .nil
  | .cons t ts, Δ, Γ, Bs, h => by
      cases h with
      | cons ht hs ha => exact .cons (weaken_t t ht) hs (weaken_l ts ha)
end

/-! ## The substitution lemma -/

/-- A substitution `σ` matches an environment `Δ`: pointwise, each term is
typed (in `Γ`) at a subclass of the declared class. -/
inductive SubstOk (CT : ClassTable) (Γ : Env) :
    List (Name × Term) → Env → Prop where
  | nil : SubstOk CT Γ [] []
  | cons {x : Name} {u : Term} {A B : Name} {σ : List (Name × Term)}
      {Δ : Env} :
      HasType CT Γ u A → Sub CT A B → SubstOk CT Γ σ Δ →
      SubstOk CT Γ ((x, u) :: σ) ((x, B) :: Δ)

theorem substOk_lookup_some {Γ : Env} {σ : List (Name × Term)} {Δ : Env}
    (h : SubstOk CT Γ σ Δ) :
    ∀ {x B}, Δ.lookup x = some B →
      ∃ u A, σ.lookup x = some u ∧ HasType CT Γ u A ∧ Sub CT A B := by
  induction h with
  | nil => intro x B hx; cases hx
  | @cons y u A B' σ' Δ' hu hsub _ ih =>
      intro x B hx
      by_cases hxy : x == y
      · simp only [List.lookup, hxy] at hx
        cases hx
        refine ⟨u, A, ?_, hu, hsub⟩
        simp only [List.lookup, hxy]
      · simp only [List.lookup, hxy] at hx
        obtain ⟨u', A', hlook, hu', hsub'⟩ := ih hx
        refine ⟨u', A', ?_, hu', hsub'⟩
        simp only [List.lookup, hxy]
        exact hlook

theorem substOk_lookup_none {Γ : Env} {σ : List (Name × Term)} {Δ : Env}
    (h : SubstOk CT Γ σ Δ) :
    ∀ {x}, Δ.lookup x = none → σ.lookup x = none := by
  induction h with
  | nil => intro x _; rfl
  | @cons y u _ B' σ' Δ' _ _ _ ih =>
      intro x hx
      by_cases hxy : x == y
      · simp only [List.lookup, hxy] at hx
      · simp only [List.lookup, hxy] at hx ⊢
        exact ih hx

/-- Build a `SubstOk` for a parameter list from typed arguments. -/
theorem substOk_zip {Γ : Env} :
    ∀ (xs : List Name) {us : TermList} {Bs : List Name},
      ArgsTyped CT Γ us Bs → xs.length = Bs.length →
      SubstOk CT Γ (List.zip xs us.toList) (List.zip xs Bs) := by
  intro xs
  induction xs with
  | nil => intro us Bs _ _; exact .nil
  | cons x xs ih =>
      intro us Bs ha hlen
      cases ha with
      | nil => simp at hlen
      | @cons t ts A B Bs' ht hs ha' =>
          have h1 : (TermList.cons t ts).toList = t :: ts.toList := by
            simp [TermList.toList]
          rw [h1, List.zip_cons_cons, List.zip_cons_cons]
          exact .cons ht hs (ih ha' (by simp at hlen; omega))

mutual
/-- **The substitution lemma** (TAPL lemma 19.5.4-style): substituting
subclass-typed terms for variables refines the type. -/
theorem subst_t (hok : CTOk CT) :
    ∀ (t : Term) {Δ Γ σ C}, HasType CT (Δ ++ Γ) t C → SubstOk CT Γ σ Δ →
      ∃ C', HasType CT Γ (substT σ t) C' ∧ Sub CT C' C
  | .var x, Δ, Γ, σ, C, h, hσ => by
      cases h with
      | var hget =>
          cases hΔ : Δ.lookup x with
          | some B =>
              rw [env_lookup_append_some hΔ] at hget
              cases hget
              obtain ⟨u, A, hu, hA, hAB⟩ := substOk_lookup_some hσ hΔ
              have hsubst : substT σ (.var x) = u := by
                simp [substT, hu]
              rw [hsubst]
              exact ⟨A, hA, hAB⟩
          | none =>
              rw [env_lookup_append_none hΔ] at hget
              have hsubst : substT σ (.var x) = .var x := by
                simp [substT, substOk_lookup_none hσ hΔ]
              rw [hsubst]
              exact ⟨C, .var hget, .refl C⟩
  | .fld t f, Δ, Γ, σ, C, h, hσ => by
      cases h with
      | fld ht hf hl =>
          obtain ⟨C₀', ht', hsub⟩ := subst_t hok t ht hσ
          obtain ⟨ext, hf'⟩ := fields_sub hsub hf
          rw [show substT σ (Term.fld t f) = .fld (substT σ t) f from by
            simp [substT]]
          exact ⟨_, .fld ht' hf' (lookupIdx_append hl), .refl _⟩
  | .invk t m ts, Δ, Γ, σ, C, h, hσ => by
      cases h with
      | invk ht hm ha =>
          obtain ⟨C₀', ht', hsub⟩ := subst_t hok t ht hσ
          rw [show substT σ (Term.invk t m ts) =
              .invk (substT σ t) m (substL σ ts) from by simp [substT]]
          exact ⟨_, .invk ht' (hok.mtype_sub hsub hm)
            (subst_l hok ts ha hσ), .refl _⟩
  | .new C₀ ts, Δ, Γ, σ, C, h, hσ => by
      cases h with
      | new hf ha =>
          rw [show substT σ (Term.new C₀ ts) = .new C₀ (substL σ ts) from by
            simp [substT]]
          exact ⟨C₀, .new hf (subst_l hok ts ha hσ), .refl C₀⟩
  | .cast C₀ t, Δ, Γ, σ, C, h, hσ => by
      cases h with
      | cast ht =>
          obtain ⟨D', ht', _⟩ := subst_t hok t ht hσ
          rw [show substT σ (Term.cast C₀ t) = .cast C₀ (substT σ t) from by
            simp [substT]]
          exact ⟨C₀, .cast ht', .refl C₀⟩

theorem subst_l (hok : CTOk CT) :
    ∀ (ts : TermList) {Δ Γ σ Bs}, ArgsTyped CT (Δ ++ Γ) ts Bs →
      SubstOk CT Γ σ Δ → ArgsTyped CT Γ (substL σ ts) Bs
  | .nil, Δ, Γ, σ, Bs, h, _ => by
      cases h with
      | nil =>
          rw [show substL σ TermList.nil = TermList.nil from by simp [substL]]
          exact .nil
  | .cons t ts, Δ, Γ, σ, Bs, h, hσ => by
      cases h with
      | cons ht hs ha =>
          obtain ⟨A', ht', hsub⟩ := subst_t hok t ht hσ
          rw [show substL σ (TermList.cons t ts) =
              .cons (substT σ t) (substL σ ts) from by simp [substL]]
          exact .cons ht' (.trans hsub hs) (subst_l hok ts ha hσ)
end

/-! ## Preservation -/

/-- Indexing into a typed argument list. -/
theorem argsTyped_get :
    ∀ (ts : TermList) {Γ Bs}, ArgsTyped CT Γ ts Bs →
      ∀ {i v B}, ts.toList.get? i = some v → Bs.get? i = some B →
        ∃ A, HasType CT Γ v A ∧ Sub CT A B
  | .nil, Γ, Bs, _ => by
      intro hv _
      rw [show TermList.nil.toList = [] from by simp [TermList.toList]] at hv
      cases hv
  | .cons t ts, Γ, Bs, h => by
      cases h with
      | @cons _ _ A B' Bs' ht hs ha =>
          intro hv hB
          rename_i i v B
          rw [show (TermList.cons t ts).toList = t :: ts.toList from by
            simp [TermList.toList]] at hv
          cases i with
          | zero =>
              cases hv
              cases hB
              exact ⟨A, ht, hs⟩
          | succ i => exact argsTyped_get ts ha hv hB

/-- Typed argument lists have the declared length. -/
theorem argsTyped_length :
    ∀ (ts : TermList) {Γ Bs}, ArgsTyped CT Γ ts Bs →
      ts.toList.length = Bs.length
  | .nil, Γ, Bs, h => by
      cases h with
      | nil =>
          rw [show TermList.nil.toList = [] from by simp [TermList.toList]]
          rfl
  | .cons t ts, Γ, Bs, h => by
      cases h with
      | cons ht hs ha =>
          rw [show (TermList.cons t ts).toList = t :: ts.toList from by
            simp [TermList.toList]]
          simp [argsTyped_length ts ha]

mutual
/-- **Preservation (TAPL theorem 19.5.1)**: a step refines the type. -/
theorem pres_t (hok : CTOk CT) :
    ∀ {t t' : Term} {Γ : Env} {C : Name}, Step CT t t' →
      HasType CT Γ t C → ∃ C', HasType CT Γ t' C' ∧ Sub CT C' C
  | _, _, _, _, .projNew hfields hlook hget _ => fun h => by
      cases h with
      | fld hrecv hf' hl' =>
          cases hrecv with
          | new hfC ha =>
              have hfs := fields_det hok.obj_none hfields hf'
              subst hfs
              rw [hl'] at hlook
              cases hlook
              have hfs2 := fields_det hok.obj_none hfC hf'
              subst hfs2
              exact argsTyped_get _ ha hget (lookupIdx_get hl')
  | _, _, Γ, _, .invkNew hbody _ _ => fun h => by
      cases h with
      | invk hrecv hm ha =>
          cases hrecv with
          | new hfC hargs =>
              obtain ⟨C₀', E, hsubC, hbodyty, hEB⟩ :=
                hok.method_typing hbody hm
              have hlen := mbody_mtype_length hbody hm
              have hσ : SubstOk CT Γ
                  (("this", Term.new _ _) :: List.zip _ (TermList.toList _))
                  (("this", C₀') :: List.zip _ _) :=
                .cons (.new hfC hargs) hsubC (substOk_zip _ ha hlen)
              have hb := weaken_t (CT := CT) _ hbodyty (Γ := Γ)
              obtain ⟨E', hE', hsub'⟩ := subst_t hok _ hb hσ
              exact ⟨E', hE', .trans hsub' hEB⟩
  | _, _, _, _, .castNew hsub _ => fun h => by
      cases h with
      | cast ht =>
          cases ht with
          | new hf ha => exact ⟨_, .new hf ha, hsub⟩
  | _, _, _, _, .fldCong hstep => fun h => by
      cases h with
      | fld hrecv hf hl =>
          obtain ⟨C₀', ht', hsub⟩ := pres_t hok hstep hrecv
          obtain ⟨ext, hf'⟩ := fields_sub hsub hf
          exact ⟨_, .fld ht' hf' (lookupIdx_append hl), .refl _⟩
  | _, _, _, _, .invkRecv hstep => fun h => by
      cases h with
      | invk hrecv hm ha =>
          obtain ⟨C₀', ht', hsub⟩ := pres_t hok hstep hrecv
          exact ⟨_, .invk ht' (hok.mtype_sub hsub hm) ha, .refl _⟩
  | _, _, _, _, .invkArgs _ hsteps => fun h => by
      cases h with
      | invk hrecv hm ha =>
          exact ⟨_, .invk hrecv hm (pres_l hok hsteps ha), .refl _⟩
  | _, _, _, _, .newArgs hsteps => fun h => by
      cases h with
      | new hf ha => exact ⟨_, .new hf (pres_l hok hsteps ha), .refl _⟩
  | _, _, _, _, .castCong hstep => fun h => by
      cases h with
      | cast ht =>
          obtain ⟨D', ht', _⟩ := pres_t hok hstep ht
          exact ⟨_, .cast ht', .refl _⟩

theorem pres_l (hok : CTOk CT) :
    ∀ {ts ts' : TermList} {Γ : Env} {Bs : List Name}, StepArgs CT ts ts' →
      ArgsTyped CT Γ ts Bs → ArgsTyped CT Γ ts' Bs
  | _, _, _, _, .here hstep => fun ha => by
      cases ha with
      | cons ht hs ha' =>
          obtain ⟨A', ht', hsub⟩ := pres_t hok hstep ht
          exact .cons ht' (.trans hsub hs) ha'
  | _, _, _, _, .there _ hsteps => fun ha => by
      cases ha with
      | cons ht hs ha' => exact .cons ht hs (pres_l hok hsteps ha')
end

/-! ## Progress (for cast-free terms) -/

/-- Values are `new` terms with value arguments. -/
theorem isValue_shape :
    ∀ (t : Term), isValueT t = true →
      ∃ C args, t = .new C args ∧ isValueL args = true := by
  intro t hv
  cases t with
  | new C args => exact ⟨C, args, rfl, by simpa [isValueT] using hv⟩
  | var x => simp [isValueT] at hv
  | fld t f => simp [isValueT] at hv
  | invk t m ts => simp [isValueT] at hv
  | cast C t => simp [isValueT] at hv

mutual
/-- **Progress (TAPL theorem 19.5.2, cast-free form)**: a closed
well-typed cast-free term is a value or steps. -/
theorem prog_t (hok : CTOk CT) :
    ∀ (t : Term) {C}, HasType CT [] t C → castFreeT t = true →
      isValueT t = true ∨ ∃ t', Step CT t t'
  | .var x, C, h, _ => by
      cases h with
      | var hget => cases hget
  | .fld t f, C, h, hcf => by
      cases h with
      | fld ht hf hl =>
          have hcf' : castFreeT t = true := by
            simpa [castFreeT] using hcf
          rcases prog_t hok t ht hcf' with hv | ⟨t', hs⟩
          · obtain ⟨C₀', args, rfl, hargsv⟩ := isValue_shape t hv
            cases ht with
            | new hfC ha =>
                have hfs := fields_det hok.obj_none hfC hf
                subst hfs
                have hi := get?_lt_length _ _ _ (lookupIdx_get hl)
                have hlen := argsTyped_length _ ha
                obtain ⟨v, hv'⟩ :=
                  get?_some_of_lt args.toList _ (by rw [hlen]; exact hi)
                exact .inr ⟨v, .projNew hf hl hv' hargsv⟩
          · exact .inr ⟨_, .fldCong hs⟩
  | .invk t m ts, C, h, hcf => by
      cases h with
      | invk ht hm ha =>
          rw [show castFreeT (.invk t m ts) =
              (castFreeT t && castFreeL ts) from by simp [castFreeT]] at hcf
          rw [Bool.and_eq_true] at hcf
          rcases prog_t hok t ht hcf.1 with hv | ⟨t', hs⟩
          · rcases prog_l hok ts ha hcf.2 with hvs | ⟨ts', hss⟩
            · obtain ⟨C₀', args, rfl, hargsv⟩ := isValue_shape t hv
              cases ht with
              | new hfC hargs =>
                  obtain ⟨xs, body, hbody⟩ := mtype_mbody hm
                  exact .inr ⟨_, .invkNew hbody hargsv hvs⟩
            · exact .inr ⟨_, .invkArgs hv hss⟩
          · exact .inr ⟨_, .invkRecv hs⟩
  | .new C₀ ts, C, h, hcf => by
      cases h with
      | new hf ha =>
          have hcf' : castFreeL ts = true := by
            simpa [castFreeT] using hcf
          rcases prog_l hok ts ha hcf' with hvs | ⟨ts', hss⟩
          · exact .inl (by simp [isValueT, hvs])
          · exact .inr ⟨_, .newArgs hss⟩
  | .cast C₀ t, _, _, hcf => by
      simp [castFreeT] at hcf

theorem prog_l (hok : CTOk CT) :
    ∀ (ts : TermList) {Bs}, ArgsTyped CT [] ts Bs →
      castFreeL ts = true →
      isValueL ts = true ∨ ∃ ts', StepArgs CT ts ts'
  | .nil, _, _, _ => .inl (by simp [isValueL])
  | .cons t ts, Bs, ha, hcf => by
      cases ha with
      | cons ht hs ha' =>
          rw [show castFreeL (.cons t ts) =
              (castFreeT t && castFreeL ts) from by simp [castFreeL]] at hcf
          rw [Bool.and_eq_true] at hcf
          rcases prog_t hok t ht hcf.1 with hv | ⟨t', hstep⟩
          · rcases prog_l hok ts ha' hcf.2 with hvs | ⟨ts', hss⟩
            · exact .inl (by simp [isValueL, hv, hvs])
            · exact .inr ⟨_, .there hv hss⟩
          · exact .inr ⟨_, .here hstep⟩
end

/-- **Preservation (TAPL theorem 19.5.1)**. -/
theorem preservation {t t' : Term} {Γ : Env} {C : Name} (hok : CTOk CT)
    (hs : Step CT t t') (h : HasType CT Γ t C) :
    ∃ C', HasType CT Γ t' C' ∧ Sub CT C' C :=
  pres_t hok hs h

/-- **Progress (TAPL theorem 19.5.2, cast-free form)**. -/
theorem progress {t : Term} {C : Name} (hok : CTOk CT)
    (h : HasType CT [] t C) (hcf : castFreeT t = true) :
    isValueT t = true ∨ ∃ t', Step CT t t' :=
  prog_t hok t h hcf

/-! ## Example: the `Pair` class table (TAPL §19.1)

```java
class A extends Object {}
class B extends Object {}
class Pair extends Object {
  Object fst; Object snd;
  Pair setfst(Object newfst) { return new Pair(newfst, this.snd); }
}
```
-/

/-- The `setfst` method of `Pair`. -/
def setfstDef : MethodDef Term :=
  ⟨"setfst", [("newfst", "Object")], "Pair",
    .new "Pair" (.cons (.var "newfst")
      (.cons (.fld (.var "this") "snd") .nil))⟩

/-- The `Pair` class. -/
def pairDef : ClassDef :=
  ⟨"Object", [("fst", "Object"), ("snd", "Object")], [setfstDef]⟩

/-- The example class table. -/
def exCT : ClassTable :=
  [ ("A", ⟨"Object", [], []⟩),
    ("B", ⟨"Object", [], []⟩),
    ("Pair", pairDef) ]

def newA : Term := .new "A" .nil
def newB : Term := .new "B" .nil
def newPair : Term := .new "Pair" (.cons newA (.cons newB .nil))

theorem fieldsA : HasFields exCT "A" [] := by
  have h : HasFields exCT "A" ([] ++ []) :=
    .step (cd := ⟨"Object", [], []⟩) rfl .obj
  simpa using h

theorem fieldsB : HasFields exCT "B" [] := by
  have h : HasFields exCT "B" ([] ++ []) :=
    .step (cd := ⟨"Object", [], []⟩) rfl .obj
  simpa using h

theorem fieldsPair :
    HasFields exCT "Pair" [("fst", "Object"), ("snd", "Object")] := by
  have h : HasFields exCT "Pair" ([] ++ pairDef.fields) :=
    .step (cd := pairDef) rfl .obj
  simpa [pairDef] using h

/-- `A <: Object` via the `extends` edge. -/
theorem subA : Sub exCT "A" "Object" := .ext (cd := ⟨"Object", [], []⟩) rfl

theorem subB : Sub exCT "B" "Object" := .ext (cd := ⟨"Object", [], []⟩) rfl

theorem tyNewA : HasType exCT [] newA "A" := .new fieldsA .nil

theorem tyNewB : HasType exCT [] newB "B" := .new fieldsB .nil

/-- `new Pair(new A(), new B()) : Pair` — the arguments are used at the
supertype `Object` of their classes. -/
theorem tyNewPair : HasType exCT [] newPair "Pair" :=
  .new fieldsPair (.cons tyNewA subA (.cons tyNewB subB .nil))

/-- Field projection: `new Pair(new A(), new B()).snd ⟶ new B()`. -/
example : Step exCT (.fld newPair "snd") newB :=
  .projNew fieldsPair rfl
    (by simp [newPair, TermList.toList])
    (by simp [newPair, newA, newB, isValueL, isValueT])

/-- ... and it is well typed, at the field's class. -/
example : HasType exCT [] (.fld newPair "snd") "Object" :=
  .fld tyNewPair fieldsPair rfl

/-- `mtype(setfst, Pair) = (Object) → Pair`. -/
theorem mtySetfst : MType exCT "setfst" "Pair" ["Object"] "Pair" := by
  have h := MType.here (m := "setfst")
    (show exCT.lookup "Pair" = some pairDef from rfl)
    (show findMethod pairDef "setfst" = some setfstDef from rfl)
  simpa [setfstDef] using h

/-- `mbody(setfst, Pair)`. -/
theorem mbSetfst : MBody exCT "setfst" "Pair" ["newfst"]
    (.new "Pair" (.cons (.var "newfst")
      (.cons (.fld (.var "this") "snd") .nil))) := by
  have h := MBody.here (m := "setfst")
    (show exCT.lookup "Pair" = some pairDef from rfl)
    (show findMethod pairDef "setfst" = some setfstDef from rfl)
  simpa [setfstDef] using h

/-- Method invocation typechecks:
`new Pair(new A(), new B()).setfst(new B()) : Pair`. -/
example : HasType exCT [] (.invk newPair "setfst" (.cons newB .nil))
    "Pair" :=
  .invk tyNewPair mtySetfst (.cons tyNewB subB .nil)

/-- ... and it steps (by `E-InvkNew`, substituting `this` and `newfst`
into the method body). -/
example : ∃ t', Step exCT (.invk newPair "setfst" (.cons newB .nil)) t' :=
  ⟨_, .invkNew mbSetfst
    (by simp [newPair, newA, newB, isValueL, isValueT])
    (by simp [newB, isValueL, isValueT])⟩

/-- Upcast: `(Object)(new A()) ⟶ new A()`. -/
example : Step exCT (.cast "Object" newA) newA :=
  .castNew subA (by simp [newA, isValueL, isValueT])

/-- A failing downcast is stuck: `(B)(new A())` is a normal form that is
not a value — FJ's model of a `ClassCastException`. -/
example : HasType exCT [] (.cast "B" newA) "B" := .cast tyNewA

end Chapter19
