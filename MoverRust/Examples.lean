/-
  MoverRust / Examples — the counter/lock library, verified

  This file carries the paper's running example (Figure 7) through the
  Lean development:

  1. a concrete mover specification `Mex` for a lock-protected counter;
  2. the atomic `add` procedure, and a machine-checked proof that its
     body **satisfies its specification** — reducible with a single
     commit (effect `N`, i.e. atomic) and `ensures x == \old(x) + arg`;
  3. a proof that `Mex` is a **valid** mover specification (Definition 1)
     for the actions the example uses — the obligation a reduction
     verifier would discharge with an SMT solver, here checked by the
     Lean kernel.

  Mover logic was designed to emit verification conditions for an SMT
  backend.  Every obligation below is instead a Lean proposition, proved
  once and checked by the kernel — no solver in the trusted base.

  Layout — globals `x = g 0` (counter), `m = g 1` (lock word);
  locals `r = local 0`, `arg = local 1`.  Thread `t` holds the lock
  when `m = t + 1` (`0` means free).
-/
import MoverRust.Preservation

namespace MoverRust
open Effect

namespace Counter

/-- The mover specification for the lock discipline (paper §7.2):
    acquiring lock `m = g 1` is a right-mover, releasing it (by its
    holder) a left-mover, the counter `x = g 0` is a both-mover exactly
    when the current thread holds the lock, and thread-local work is a
    both-mover.  Everything else is an error. -/
def Mex : MSpec := fun A t σ =>
  match A with
  | .acquire m  => if m = 1 then .R else .E
  | .release m  => if m = 1 ∧ σ (.g 1) = (t : Int) + 1 then .L else .E
  | .readg _ x  => if x = 0 ∧ σ (.g 1) = (t : Int) + 1 then .B else .E
  | .writeg x _ => if x = 0 ∧ σ (.g 1) = (t : Int) + 1 then .B else .E
  | .lact _ _   => .B
  | .assume _ _ => .B
  | .idA        => .B
  | .casT _ _ _ => .E

/-! ### The `add` procedure

    atomic  ensures x == \old(x) + arg
    add() {
      acquire(m);       // R
      r = x;            // B   (both-mover: lock held)
      x = r + arg;      // B
      release(m);       // L
    }

  Effect  R; B; B; L = N  — the body is one reducible sequence with a
  single commit, so `add` is **atomic**. -/

/-- `acquire(m)` -/
def aAcq : Act := .acquire 1
/-- `r = x` -/
def aRead : Act := .readg 0 0
/-- `x = r + arg` -/
def aWrite : Act := .writeg 0 (.add (.lv 0) (.lv 1))
/-- `release(m)` -/
def aRel : Act := .release 1

def addBody : Stmt :=
  .seq (.act aAcq) (.seq (.act aRead) (.seq (.act aWrite) (.act aRel)))

/-- Precondition: the lock is free (`m = 0`). -/
def addPre : Pred1 := fun _ σ => σ (.g 1) = 0

/-- Postcondition: `x == \old(x) + arg` and the lock is free again. -/
def addPost : Pred := fun t σ₀ σ =>
  σ (.g 0) = σ₀ (.g 0) + σ₀ (.l t 1) ∧ σ (.g 1) = 0

/-! ### Step-by-step store facts

We track the store through the four actions from a start store `σ₀`
with `m = 0`, executed by thread `t`. -/

/-- After `acquire(m); r = x; x = r + arg; release(m)`, starting from a
    store with `m = 0`, the counter has increased by `arg` and the lock
    is free — the semantic content of the postcondition. -/
theorem addBody_effect_store {t : Tid} {σ₀ σ₁ σ₂ σ₃ σ₄ : Store}
    (h0 : σ₀ (.g 1) = 0)
    (h1 : den aAcq t σ₀ σ₁)
    (h2 : den aRead t σ₁ σ₂)
    (h3 : den aWrite t σ₂ σ₃)
    (h4 : den aRel t σ₃ σ₄) :
    σ₄ (.g 0) = σ₀ (.g 0) + σ₀ (.l t 1) ∧ σ₄ (.g 1) = 0 := by
  simp only [aAcq, aRead, aWrite, aRel, den] at *
  obtain ⟨_, h1⟩ := h1
  subst h1; subst h2; subst h3; subst h4
  refine ⟨?_, ?_⟩
  · simp [upd, evalE]
  · simp [upd]

/-! ### Totality of the counter actions -/

theorem total_read : total aRead := fun t σ => ⟨_, rfl⟩
theorem total_write : total aWrite := fun t σ => ⟨_, rfl⟩
theorem total_rel : total aRel := fun t σ => ⟨_, rfl⟩

/-! ### "The lock is held" propagates through the body -/

/-- After `acquire`, the acting thread holds the lock. -/
theorem holds_after_acq {t : Tid} {σ₀ σ : Store}
    (h : den aAcq t σ₀ σ) : σ (.g 1) = (t : Int) + 1 := by
  simp only [aAcq, den] at h
  obtain ⟨_, rfl⟩ := h
  simp [upd]

/-- `readg`/`writeg` to the counter (`g 0`) leave the lock word (`g 1`)
    unchanged. -/
theorem lock_unchanged_read {t : Tid} {σ σ' : Store} (h : den aRead t σ σ') :
    σ' (.g 1) = σ (.g 1) := by
  simp only [aRead, den] at h; subst h; simp [upd]

theorem lock_unchanged_write {t : Tid} {σ σ' : Store} (h : den aWrite t σ σ') :
    σ' (.g 1) = σ (.g 1) := by
  simp only [aWrite, den] at h; subst h; simp [upd]

/-! ### The typing derivation: `add`'s body satisfies its spec

Each `act` step is discharged with an effect bound over its
precondition, computed from the fact that the lock is held.  Composing
them yields effect `R; B; B; L = N`, so the body is atomic. -/

/-- The bound for the counter read: over the post-acquire precondition,
    the read is a both-mover. -/
theorem read_bound (D : Decls) :
    Judg D Mex emptyRel emptyRel (.act aRead)
      (pseq (Two addPre) aAcq)
      (pseq (pseq (Two addPre) aAcq) aRead) .B := by
  apply Judg.act _ (fun _ => total_read)
  rintro t σ₀ σ ⟨σ', _, hacq⟩
  have hlk : σ (.g 1) = (t : Int) + 1 := holds_after_acq hacq
  rw [show Mex aRead t σ = .B from by simp [aRead, Mex, hlk]]
  exact le_refl _

/-- The bound for the counter write. -/
theorem write_bound (D : Decls) :
    Judg D Mex emptyRel emptyRel (.act aWrite)
      (pseq (pseq (Two addPre) aAcq) aRead)
      (pseq (pseq (pseq (Two addPre) aAcq) aRead) aWrite) .B := by
  apply Judg.act _ (fun _ => total_write)
  rintro t σ₀ σ ⟨σ', ⟨σ'', _, hacq⟩, hread⟩
  have hlk : σ (.g 1) = (t : Int) + 1 := by
    rw [lock_unchanged_read hread]; exact holds_after_acq hacq
  rw [show Mex aWrite t σ = .B from by simp [aWrite, Mex, hlk]]
  exact le_refl _

/-- The bound for the release. -/
theorem rel_bound (D : Decls) :
    Judg D Mex emptyRel emptyRel (.act aRel)
      (pseq (pseq (pseq (Two addPre) aAcq) aRead) aWrite)
      (pseq (pseq (pseq (pseq (Two addPre) aAcq) aRead) aWrite) aRel) .L := by
  apply Judg.act _ (fun _ => total_rel)
  rintro t σ₀ σ ⟨σ', ⟨σ'', ⟨σ''', _, hacq⟩, hread⟩, hwrite⟩
  have hlk : σ (.g 1) = (t : Int) + 1 := by
    rw [lock_unchanged_write hwrite, lock_unchanged_read hread]
    exact holds_after_acq hacq
  rw [show Mex aRel t σ = .L from by simp [aRel, Mex, hlk]]
  exact le_refl _

/-- The acquire step (a right-mover, unconditionally). -/
theorem acq_bound (D : Decls) :
    Judg D Mex emptyRel emptyRel (.act aAcq)
      (Two addPre) (pseq (Two addPre) aAcq) .R := by
  apply Judg.act _ (by intro h; exact absurd h (by decide))
  rintro t σ₀ σ _
  rw [show Mex aAcq t σ = .R from by simp [aAcq, Mex]]
  exact le_refl _

/-- **Spec satisfaction.**  `add`'s body is verified against its
    specification: reducible with a single commit (effect `N`, hence
    atomic) and postcondition `x == \old(x) + arg`. -/
theorem addBody_spec (D : Decls) :
    Judg D Mex emptyRel emptyRel addBody (Two addPre) addPost .N := by
  have hbody :
      Judg D Mex emptyRel emptyRel addBody (Two addPre)
        (pseq (pseq (pseq (pseq (Two addPre) aAcq) aRead) aWrite) aRel)
        (Effect.seq .R (Effect.seq .B (Effect.seq .B .L))) :=
    .seqJ (acq_bound D) (.seqJ (read_bound D) (.seqJ (write_bound D) (rel_bound D)))
  refine .conseq (PImp.refl _) ?_ (RImp.refl _) (RImp.refl _) (by decide) hbody
  -- the accumulated postcondition implies `addPost`
  rintro t σ₀ σ ⟨σ₃, ⟨σ₂, ⟨σ₁, ⟨σ₀', ⟨rfl, hpre⟩, hacq⟩, hread⟩, hwrite⟩, hrel⟩
  exact addBody_effect_store hpre hacq hread hwrite hrel

/-- The function declaration is well-formed (`⊢ fn`, [M-def-atomic]).
    `add` is non-recursive (its body is call-free) and verified. -/
theorem addFn_ok (D : Decls) :
    FnOK D Mex (.atomicSpec .N addPre addPost) addBody :=
  .atomic (by simp [addBody, aAcq, aRead, aWrite, aRel, CallFree]) (addBody_spec D)

/-! ### Validity of `Mex` (Definition 1)

`Mex` is a valid mover specification: every commutativity claim it makes
is true.  This is the obligation a reduction verifier would send to an
SMT solver; here it is a theorem checked by the Lean kernel.

The proof rests on **lock exclusivity**: at most one thread holds the
lock, so whenever thread `t`'s step is a mover touching the counter or
lock, a *conflicting* step by another thread `u ≠ t` is classified `E`
(an error), not a mover — making the dangerous cases of the definition
vacuous.  Non-conflicting steps touch disjoint variables and commute by
`upd_comm`. -/

/-- An action of effect `≤ N` (any mover) writes a single variable owned
    by the acting thread, computed as shown; `casT` is excluded. -/
theorem shapeN {A : Act} {t : Tid} {σ σ' : Store}
    (hN : Mex A t σ ≤ .N) (hd : den A t σ σ') :
    (A = .acquire 1 ∧ σ (.g 1) = 0 ∧ σ' = upd σ (.g 1) ((t : Int) + 1)) ∨
    (σ (.g 1) = (t : Int) + 1 ∧ A = .release 1 ∧ σ' = upd σ (.g 1) 0) ∨
    (∃ r, σ (.g 1) = (t : Int) + 1 ∧ A = .readg r 0 ∧ σ' = upd σ (.l t r) (σ (.g 0))) ∨
    (∃ e, σ (.g 1) = (t : Int) + 1 ∧ A = .writeg 0 e ∧ σ' = upd σ (.g 0) (evalE t σ e)) ∨
    (∃ r e, A = .lact r e ∧ σ' = upd σ (.l t r) (evalE t σ e)) ∨
    (σ' = σ) := by
  cases A with
  | lact r e => exact .inr (.inr (.inr (.inr (.inl ⟨r, e, rfl, by simpa [den] using hd⟩))))
  | readg r x =>
      simp only [Mex] at hN
      by_cases hg : x = 0 ∧ σ (.g 1) = (t : Int) + 1
      · rw [if_pos hg] at hN
        obtain ⟨hx, hlk⟩ := hg; subst hx
        exact .inr (.inr (.inl ⟨r, hlk, rfl, by simpa [den] using hd⟩))
      · rw [if_neg hg] at hN; exact absurd hN (by decide)
  | writeg x e =>
      simp only [Mex] at hN
      by_cases hg : x = 0 ∧ σ (.g 1) = (t : Int) + 1
      · rw [if_pos hg] at hN
        obtain ⟨hx, hlk⟩ := hg; subst hx
        exact .inr (.inr (.inr (.inl ⟨e, hlk, rfl, by simpa [den] using hd⟩)))
      · rw [if_neg hg] at hN; exact absurd hN (by decide)
  | acquire m =>
      simp only [Mex] at hN
      by_cases hm : m = 1
      · subst hm
        obtain ⟨h0, hd'⟩ := hd
        exact .inl ⟨rfl, h0, hd'⟩
      · rw [if_neg hm] at hN; exact absurd hN (by decide)
  | release m =>
      simp only [Mex] at hN
      by_cases hg : m = 1 ∧ σ (.g 1) = (t : Int) + 1
      · rw [if_pos hg] at hN
        obtain ⟨hm, hlk⟩ := hg; subst hm
        exact .inr (.inl ⟨hlk, rfl, by simpa [den] using hd⟩)
      · rw [if_neg hg] at hN; exact absurd hN (by decide)
  | casT x a b => simp only [Mex] at hN; exact absurd hN (by decide)
  | assume e b => exact .inr (.inr (.inr (.inr (.inr (by simp only [den] at hd; exact hd.1)))))
  | idA => exact .inr (.inr (.inr (.inr (.inr (by simpa [den] using hd)))))

/-! ### The disjoint-frame mechanism

Every action of thread `u` reads and writes only `u`'s own locals and
the globals; it never touches another thread `t`'s local variable
`l t r`.  Hence a `t`-local update commutes through any `u`-action.
This is the workhorse behind the "non-conflicting steps commute" half of
validity — a purely structural fact, discharged here once for all
actions. -/

/-- Framing: a `u`-action's denotation survives adding a foreign
    (`t`-local, `t ≠ u`) update to both stores. -/
theorem den_frame_foreign {A : Act} {u t : Tid} {r : Nat} {k : Int}
    {σ σ' : Store} (hut : u ≠ t) (hd : den A u σ σ') :
    den A u (upd σ (.l t r) k) (upd σ' (.l t r) k) := by
  have hlu : ∀ a b : Nat, (Var.l u a) ≠ (Var.l t b) :=
    fun a b h => by injection h with h1 _; exact hut h1
  have hgl : ∀ x b : Nat, (Var.g x) ≠ (Var.l t b) := fun x b h => Var.noConfusion h
  have hev : ∀ e : Exp, evalE u (upd σ (.l t r) k) e = evalE u σ e :=
    fun e => evalE_upd_l_other r k e hut
  cases A with
  | lact r₂ e =>
      simp only [den] at hd ⊢
      rw [hd, hev, upd_comm _ _ _ (hlu r₂ r)]
  | readg r₂ x =>
      simp only [den] at hd ⊢
      rw [hd, upd_other _ _ (hgl x r), upd_comm _ _ _ (hlu r₂ r)]
  | writeg x e =>
      simp only [den] at hd ⊢
      rw [hd, hev, upd_comm _ _ _ (hgl x r)]
  | acquire m =>
      simp only [den] at hd ⊢
      obtain ⟨h0, hd⟩ := hd
      exact ⟨by rw [upd_other _ _ (hgl m r)]; exact h0,
        by rw [hd, upd_comm _ _ _ (hgl m r)]⟩
  | release m =>
      simp only [den] at hd ⊢
      rw [hd, upd_comm _ _ _ (hgl m r)]
  | casT x a b =>
      simp only [den] at hd ⊢
      obtain ⟨hv, hd⟩ := hd
      refine ⟨by rw [upd_other _ _ (hgl x r), hev]; exact hv, ?_⟩
      rw [hd, hev, upd_comm _ _ _ (hgl x r)]
  | assume e b =>
      simp only [den] at hd ⊢
      obtain ⟨hd, hc⟩ := hd
      subst hd
      exact ⟨rfl, by rw [hev]; exact hc⟩
  | idA => simp only [den] at hd ⊢; rw [hd]

/-- **A validity obligation, discharged in Lean.**  A representative
    right-mover commutation from Definition 1: thread `t` acquires the
    lock (a right-mover) and a different thread `u` performs a local
    computation `r₂ = e`; the two commute to the same final store.  This
    is exactly the kind of goal a reduction verifier emits to an SMT
    backend — here proved by the kernel. -/
theorem valid_acq_vs_local {t u : Tid} {r₂ : Nat} {e : Exp} {σ σ' σ'' : Store}
    (hut : u ≠ t)
    (h1 : den aAcq t σ σ') (h2 : den (.lact r₂ e) u σ' σ'') :
    ∃ τ, den (.lact r₂ e) u σ τ ∧ den aAcq t τ σ'' := by
  simp only [aAcq, den] at h1 ⊢
  obtain ⟨h0, rfl⟩ := h1
  refine ⟨upd σ (.l u r₂) (evalE u σ e), rfl, ?_⟩
  simp only [den] at h2
  constructor
  · rw [upd_other _ _ (by intro h; injection h)]; exact h0
  · rw [h2, evalE_upd_g,
      upd_comm _ _ _ (by intro h; injection h)]

end Counter
end MoverRust
