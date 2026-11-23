/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Interp

/-!
# The interpreter

`IF` at `(IF, (f, (x, t)))` simulates the formula `f` at `x` with the budgets `t`; its value is the value of the run
and the budgets that are left.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Rel

variable {α β γ δ : Type*}

theorem forall₂_flatMap {R : α → β → Prop} {S : γ → δ → Prop} {l : List α} {l' : List β} {f : α → List γ}
    {g : β → List δ} (h : List.Forall₂ R l l') (hf : ∀ a ∈ l, ∀ b ∈ l', R a b → List.Forall₂ S (f a) (g b)) :
    List.Forall₂ S (l.flatMap f) (l'.flatMap g) := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    refine List.rel_append (hf _ List.mem_cons_self _ List.mem_cons_self hab) (ih fun a ha b hb =>
      hf a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))

theorem forall₂_exists {R : α → β → Prop} {l : List α} {l' : List β} (h : List.Forall₂ R l l') {a : α} (ha : a ∈ l) :
    ∃ b ∈ l', R a b := by
  induction h with
  | nil => simp at ha
  | cons hab _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

/-- `let`, for lists that correspond to other lists. -/
theorem lett_rel {e body : Fm} {x : Tree} {le : List (Run A)} (he : Ev θ e x le) {Q : List β}
    {R : Run A → β → Prop} (hR : List.Forall₂ R le Q) {Q2 : β → List γ} {R2 : Run A → γ → Prop}
    (h : ∀ s ∈ le, ∀ b ∈ Q, R s b → ∃ l2, Ev θ body s.out l2 ∧
      List.Forall₂ (fun t c => R2 ⟨s.cost + t.cost + 2, s.th * t.th, s.bill ++ t.bill, t.out⟩ c) l2 (Q2 b)) :
    ∃ l, Ev θ (lett e body) x l ∧ List.Forall₂ R2 l (Q.flatMap Q2) := by
  refine ⟨_, Ev.lett he fun s hs => ?_, forall₂_flatMap hR fun s hs b hb hsb => ?_⟩
  · obtain ⟨b, hb, hsb⟩ := forall₂_exists hR hs
    obtain ⟨l2, h2, -⟩ := h s hs b hb hsb
    exact h2.hl
  · obtain ⟨l2, h2, h3⟩ := h s hs b hb hsb
    rw [h2.evl, List.forall₂_map_left_iff]
    exact h3

end Rel

section Cases

/-- Choose by the length of the value of `b`. -/
def selF : List Fm → Fm → Fm
  | [], _ => .fail
  | c :: cs, b => .ite b (selF cs (.tl b)) c

theorem selF_ev {cs : List Fm} {b : Fm} {x o : Tree} {k : ℕ} (hb : Dt θ b x o k) {l : List (Run A)}
    (h : ∀ c, cs[o.len]? = some c → Ev θ c x l) (h0 : cs.length ≤ o.len → l = []) :
    ∃ k' ≤ cs.length * (k + cs.length + 1), Ev θ (selF cs b) x (l.map (Run.delay k')) := by
  induction cs generalizing b o k with
  | nil =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [h0 (Nat.zero_le _)]
    exact .fail x
  | cons c cs ih =>
    cases o with
    | nil =>
      refine ⟨k + 1, ?_, Ev.ite_false hb (h c rfl)⟩
      simp only [List.length_cons]
      nlinarith
    | cons a o =>
      obtain ⟨k', hk', h'⟩ := ih (b := .tl b) (o := o) hb.tl (fun c hc => h c (by simpa [len] using hc))
        (fun hl => h0 (by simp only [List.length_cons, len]; omega))
      refine ⟨k + 1 + k', ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · have := Ev.ite_true (c := c) hb (by simp) h'
        rw [List.map_map] at this
        refine Eq.mp ?_ this
        congr 1
        refine List.map_congr_left fun r _ => ?_
        simp only [Run.delay, Function.comp_apply, Run.mk.injEq, and_true]
        omega

end Cases

section Code

/-- The formula in the environment. -/
def fF (b : Fm) : Fm := .hd (.tl b)
/-- The argument in the environment. -/
def fX (b : Fm) : Fm := .hd (.tl (.tl b))
/-- The budgets in the environment. -/
def fS (b : Fm) : Fm := .tl (.tl (.tl b))
/-- The opcode. -/
def fO (b : Fm) : Fm := .hd (fF b)
/-- The arguments of the formula. -/
def fA (b : Fm) : Fm := .tl (fF b)
/-- Recursive call. -/
def rec' (b a x s : Fm) : Fm := .run (.hd b) (.cons (.hd b) (.cons a (.cons x s)))

/-- First call, with the environment kept. -/
def call1 : Fm := .cons .id (rec' .id (.hd (fA .id)) (fX .id) (fS .id))

/-- Second call, with everything kept. -/
def call2 : Fm := .cons .id (rec' (.hd .id) (.tl (fA (.hd .id))) (fX (.hd .id)) (.tl (.tl .id)))

/-- The cases of the interpreter. -/
def caseL : List Fm := [
  -- quote
  .cons (fA .id) (fS .id),
  -- id
  .cons (fX .id) (fS .id),
  -- hd
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.hd (.hd .id)) (.tl .id)),
  -- tl
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.tl (.hd .id)) (.tl .id)),
  -- cons
  lett call1 (lett call2 (.cons (.cons (.hd (.tl (.hd .id))) (.hd (.tl .id))) (.tl (.tl .id)))),
  -- ite
  lett call1 (.ite (.hd (.tl .id))
    (rec' (.hd .id) (.hd (.tl (fA (.hd .id)))) (fX (.hd .id)) (.tl (.tl .id)))
    (rec' (.hd .id) (.tl (.tl (fA (.hd .id)))) (fX (.hd .id)) (.tl (.tl .id)))),
  -- run
  lett call1 (lett call2 (rec' (.hd (.hd .id)) (.hd (.tl (.hd .id))) (.hd (.tl .id)) (.tl (.tl .id)))),
  -- guess
  .cons .guess (fS .id),
  -- fail
  .fail,
  -- theta
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.theta (.hd .id)) (.tl .id)),
  -- mul
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.quote .nil) (.run (.quote DC.code) (.cons (.quote DC.code) .id)))
  ]

/-- The interpreter. -/
def IF : Fm := selF caseL (fO .id)

/-- The environment of the interpreter. -/
def env (f x : Tree) (t : Bt) : Tree := .cons IF.code (.cons f (.cons x t.enc))

theorem Dt.fX {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fX b) y x (k + 3) :=
  .hd (.tl (.tl h))

theorem Dt.fS {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fS b) y t.enc (k + 3) :=
  .tl (.tl (.tl h))

theorem Dt.fO {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fO b) y f.hd (k + 3) :=
  .hd (.hd (.tl h))

theorem Dt.fA {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fA b) y f.tl (k + 3) :=
  .tl (.hd (.tl h))

/-- A recursive call. -/
theorem rec_ev {b a x s : Fm} {y g z : Tree} {f' x' : Tree} {t t' : Bt} {kb ka kx ks : ℕ}
    (hb : Dt θ b y (env f' x' t') kb) (ha : Dt θ a y g ka) (hx : Dt θ x y z kx) (hs : Dt θ s y t.enc ks)
    {l : List (Run A)} (h : Ev θ IF (env g z t) l) :
    Ev θ (rec' b a x s) y (l.map (Run.delay (2 * kb + ka + kx + ks + 6))) := by
  have := Ev.run_det (Dt.hd hb) (.cons (.hd hb) (.cons ha (.cons hx hs))) (l := l) (by
    show Ev θ (Fm.ofTree IF.code) _ l
    rw [Fm.ofTree_code]
    exact h)
  refine Eq.mp ?_ this
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [Run.delay, Run.mk.injEq, and_true]
  omega

/-- The runs that stay within the budgets, with what is left. -/
def simS (t : Bt) (l : List (Run A)) : List (Run A × Bt) :=
  l.filterMap fun r => (Bt.decAll r.bill t).map fun t' => (r, t')

theorem mem_simS {t : Bt} {l : List (Run A)} {q : Run A × Bt} (h : q ∈ simS t l) :
    q.1 ∈ l ∧ Bt.decAll q.1.bill t = some q.2 := by
  rw [simS, List.mem_filterMap] at h
  obtain ⟨r, hr, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨t', ht, rfl⟩ := h
  exact ⟨hr, ht⟩

theorem simS_map {t : Bt} {l : List (Run A)} {G : Run A → Run A} (h : ∀ r, (G r).bill = r.bill) :
    simS t (l.map G) = (simS t l).map fun q => (G q.1, q.2) := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [simS, List.map_cons, List.filterMap_cons, h] at ih ⊢
    cases Bt.decAll r.bill t with
    | none => exact ih
    | some t' =>
      simp only [Option.map_some, List.map_cons]
      rw [ih]

theorem simS_append {t : Bt} {l l' : List (Run A)} : simS t (l ++ l') = simS t l ++ simS t l' := by
  simp [simS]

theorem simS_flatMap {t : Bt} {la : List (Run A)} {L : Run A → List (Run A)} {G : Run A → Run A → Run A}
    (h : ∀ r s, (G r s).bill = r.bill ++ s.bill) : simS t (la.flatMap fun r => (L r).map (G r)) =
      (simS t la).flatMap fun q => (simS q.2 (L q.1)).map fun p => (G q.1 p.1, p.2) := by
  have one : ∀ (r : Run A) (l : List (Run A)), simS t (l.map (G r)) =
      ((Bt.decAll r.bill t).toList.map fun t' => (r, t')).flatMap fun q =>
        (simS q.2 l).map fun p => (G q.1 p.1, p.2) := by
    intro r l
    cases hd : Bt.decAll r.bill t with
    | none =>
      simp only [Option.toList_none, List.map_nil, List.flatMap_nil, simS, List.filterMap_map]
      rw [List.filterMap_eq_nil_iff]
      intro s _
      simp [h, Bt.decAll_append, hd]
    | some t' =>
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      induction l with
      | nil => rfl
      | cons s l ih =>
        simp only [simS, List.map_cons, List.filterMap_cons, h, Bt.decAll_append, hd, Option.bind_some] at ih ⊢
        cases Bt.decAll s.bill t' with
        | none => exact ih
        | some t'' =>
          simp only [Option.map_some, List.map_cons]
          rw [ih]
  induction la with
  | nil => rfl
  | cons r la ih =>
    rw [List.flatMap_cons, simS_append, ih, one]
    simp only [simS, List.filterMap_cons]
    cases Bt.decAll r.bill t with
    | none => simp
    | some t' => simp

end Code

end NS1
