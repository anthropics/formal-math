/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tape.Task

/-!
# Programs given by their structured runs

A series on channels is described by a family of runs: every run emits words on the channels and has a weight.
The sum of the series over all words with given projections is the sum of the weights of the runs that emit
these projections.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]

/-- The series is described by runs with emissions em and weights wt. -/
def IsRuns (P : Series F (Z × Γ)) {X : Type*} (em : X → Z → List Γ) (wt : X → F) : Prop :=
  ∀ v, ∃ R : Finset X, (∀ x, x ∈ R ↔ em x = v) ∧ hat P v = ∑ x ∈ R, wt x

/-- There is a series of dimension at most n with these runs. -/
def Runs (n : ℕ) {X : Type*} (em : X → Z → List Γ) (wt : X → F) : Prop :=
  ∃ P : Series F (Z × Γ), RatLe n P ∧ IsRuns P em wt

theorem IsRuns.exists_run {P : Series F (Z × Γ)} {X : Type*} {em : X → Z → List Γ} {wt : X → F}
    (h : IsRuns P em wt) {v : Z → List Γ} (hv : hat P v ≠ 0) : ∃ x, em x = v ∧ wt x ≠ 0 := by
  obtain ⟨R, h1, h2⟩ := h v
  rw [h2] at hv
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact ⟨x, (h1 x).1 hx, hne⟩

theorem IsRuns.of_fib {P : Series F (Z × Γ)} {X : Type*} {em : X → Z → List Γ} {wt : X → F}
    (h : IsRuns P em wt) {v : Z → List Γ} (R : Finset X) (hR : ∀ x, x ∈ R ↔ em x = v) :
    hat P v = ∑ x ∈ R, wt x := by
  obtain ⟨R', h1, h2⟩ := h v
  have : R' = R := by ext x; rw [h1, hR]
  rw [h2, this]

theorem IsRuns.mul {f g : Series F (Z × Γ)} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (hf : IsRuns f em wt) (hg : IsRuns g em' wt') :
    IsRuns (Series.mul f g) (fun (x : X × Y) z => em x.1 z ++ em' x.2 z) (fun x => wt x.1 * wt' x.2) := by
  classical
  intro v
  choose Rf hf1 hf2 using hf
  choose Rg hg1 hg2 using hg
  refine ⟨(anti v).biUnion fun p => Rf p.1 ×ˢ Rg p.2, ?_, ?_⟩
  · rintro ⟨x, y⟩
    simp only [Finset.mem_biUnion, Finset.mem_product, hf1, hg1, mem_anti]
    constructor
    · rintro ⟨p, hp, h1, h2⟩
      funext z
      rw [h1, h2, hp z]
    · intro h
      exact ⟨(em x, em' y), fun z => congrFun h z, rfl, rfl⟩
  · rw [hat_mul, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [hf2, hg2, Finset.sum_mul_sum, Finset.sum_product]
    · intro p _ q _ hpq
      rw [Function.onFun, Finset.disjoint_left]
      rintro ⟨x, y⟩ h h'
      rw [Finset.mem_product, hf1, hg1] at h h'
      exact hpq (Prod.ext (h.1.symm.trans h'.1) (h.2.symm.trans h'.2))

theorem IsRuns.sum {ι : Type*} [Fintype ι] {X : ι → Type*} {P : ι → Series F (Z × Γ)}
    {em : ∀ i, X i → Z → List Γ} {wt : ∀ i, X i → F} (h : ∀ i, IsRuns (P i) (em i) (wt i)) :
    IsRuns (∑ i, P i) (fun (x : Σ i, X i) => em x.1 x.2) (fun x => wt x.1 x.2) := by
  intro v
  choose R h1 h2 using h
  refine ⟨univ.sigma fun i => R i v, ?_, ?_⟩
  · rintro ⟨i, x⟩
    simp [h1]
  · rw [hat_sum, Finset.sum_sigma]
    exact Finset.sum_congr rfl fun i _ => h2 i v

theorem IsRuns.congr {P : Series F (Z × Γ)} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (h : IsRuns P em wt) (e : Y ≃ X)
    (h1 : ∀ y z, em (e y) z = em' y z) (h2 : ∀ y, wt (e y) = wt' y) : IsRuns P em' wt' := by
  intro v
  obtain ⟨R, g1, g2⟩ := h v
  refine ⟨R.map e.symm.toEmbedding, fun y => ?_, ?_⟩
  · simp only [Finset.mem_map_equiv, Equiv.symm_symm, g1]
    have : em (e y) = em' y := funext fun z => h1 y z
    rw [this]
  · rw [g2, Finset.sum_map]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← h2]
    simp

theorem IsRuns.one : IsRuns (Series.one : Series F (Z × Γ)) (fun (_ : Unit) _ => []) (fun _ => 1) := by
  classical
  intro v
  refine ⟨if v = fun _ => [] then {()} else ∅, ?_, ?_⟩
  · intro x
    by_cases h : v = fun _ => []
    · simp [h]
    · simp [h, Ne.symm h]
  · rw [hat_one]
    split_ifs <;> simp

/-- The star: the runs are the lists of runs. -/
theorem IsRuns.kstar {f : Series F (Z × Γ)} {X : Type*} {em : X → Z → List Γ} {wt : X → F}
    (hf : IsRuns f em wt) (hne : ∀ x, em x ≠ fun _ => []) :
    IsRuns (Series.kstar f) (fun (l : List X) z => l.flatMap fun x => em x z)
      (fun l => (l.map wt).prod) := by
  classical
  intro v
  induction hn : ∑ z, (v z).length using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    choose Rf hf1 hf2 using hf
    have hlt : ∀ p ∈ (anti v).filter (fun p => p.1 ≠ fun _ => []), ∑ z, (p.2 z).length < n := by
      intro p hp
      rw [Finset.mem_filter, mem_anti] at hp
      have e : n = ∑ z, (p.1 z).length + ∑ z, (p.2 z).length := by
        rw [← hn, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun z _ => by rw [← hp.1 z, List.length_append]
      have : 0 < ∑ z, (p.1 z).length := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        apply hp.2
        funext z
        exact List.length_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1 h0 z (Finset.mem_univ z))
      omega
    have ih' : ∀ p, ∃ R : Finset (List X), p ∈ (anti v).filter (fun p => p.1 ≠ fun _ => []) →
        (∀ l, l ∈ R ↔ (fun z => l.flatMap fun x => em x z) = p.2) ∧
        hat (Series.kstar f) p.2 = ∑ l ∈ R, (l.map wt).prod := by
      intro p
      by_cases hp : p ∈ (anti v).filter (fun p => p.1 ≠ fun _ => [])
      · obtain ⟨R, h1, h2⟩ := ih _ (hlt p hp) p.2 rfl
        exact ⟨R, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨∅, fun h => absurd h hp⟩
    choose Rs hRs using ih'
    let A := (anti v).filter (fun p => p.1 ≠ fun _ => [])
    let B : Finset (X × List X) := A.biUnion fun p => Rf p.1 ×ˢ Rs p
    have hB : ∀ x l, (x, l) ∈ B ↔ (fun z => em x z ++ l.flatMap fun x => em x z) = v := by
      intro x l
      simp only [B, Finset.mem_biUnion, Finset.mem_product]
      constructor
      · rintro ⟨p, hp, h1, h2⟩
        rw [hf1] at h1
        rw [(hRs p hp).1] at h2
        have := (mem_anti.1 (Finset.mem_filter.1 hp).1)
        funext z
        rw [← this z, h1]
        exact congrArg _ (congrFun h2 z)
      · intro h
        have hp : (em x, fun z => l.flatMap fun x => em x z) ∈ A := by
          rw [Finset.mem_filter, mem_anti]
          exact ⟨fun z => congrFun h z, hne x⟩
        exact ⟨_, hp, (hf1 _ _).2 rfl, ((hRs _ hp).1 _).2 rfl⟩
    let C : Finset (List X) := B.map ⟨fun p => p.1 :: p.2, by rintro ⟨a, b⟩ ⟨c, d⟩ h; simpa using h⟩
    have hC : ∀ l, l ∈ C ↔ l ≠ [] ∧ (fun z => l.flatMap fun x => em x z) = v := by
      intro l
      simp only [C, Finset.mem_map, Function.Embedding.coeFn_mk, Prod.exists]
      constructor
      · rintro ⟨x, l', h, rfl⟩
        exact ⟨by simp, by rw [hB] at h; exact h⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨x, l', rfl⟩ := List.exists_cons_of_ne_nil h1
        exact ⟨x, l', (hB _ _).2 (by simpa using h2), rfl⟩
    refine ⟨(if v = fun _ => [] then {[]} else ∅) ∪ C, ?_, ?_⟩
    · intro l
      rw [Finset.mem_union, hC]
      by_cases hl : l = []
      · subst hl
        by_cases h : v = fun _ => []
        · simp [h]
        · simp [h, Ne.symm h]
      · by_cases h : v = fun _ => []
        · simp [h, hl]
        · simp [h, hl]
    · rw [Finset.sum_union]
      · rw [hat_kstar]
        congr 1
        · split_ifs <;> simp
        · simp only [C, Finset.sum_map, Function.Embedding.coeFn_mk, List.map_cons, List.prod_cons]
          simp only [B]
          rw [Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun p hp => ?_
            rw [hf2, (hRs p hp).2, Finset.sum_mul_sum, Finset.sum_product]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
              (List.prod_cons (l := j.map wt) (a := wt i)).symm
          · intro p hp q hq hpq
            rw [Function.onFun, Finset.disjoint_left]
            rintro ⟨x, y⟩ h h'
            rw [Finset.mem_product, hf1] at h h'
            rw [(hRs p hp).1] at h
            rw [(hRs q hq).1] at h'
            exact hpq (Prod.ext (h.1.symm.trans h'.1) (h.2.symm.trans h'.2))
      · rw [Finset.disjoint_left]
        intro l hl hl'
        rw [hC] at hl'
        split_ifs at hl <;> simp at hl
        exact hl'.1 hl

/-- The word on the channels, channel by channel. -/
noncomputable def chanWord (w : Z → List Γ) : List (Z × Γ) :=
  (univ : Finset Z).toList.flatMap fun z => (w z).map fun a => (z, a)

theorem proj_flatMap {ι : Type*} (l : List ι) (g : ι → List (Z × Γ)) (z : Z) :
    proj (l.flatMap g) z = l.flatMap fun i => proj (g i) z := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.flatMap_cons, proj_append, ih]

theorem proj_map_mk (z z' : Z) (w : List Γ) :
    proj (w.map fun a => (z, a)) z' = if z = z' then w else [] := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons, proj_cons, ih]
    split_ifs <;> rfl

theorem flatMap_ite_eq {ι β : Type*} [DecidableEq ι] (l : List ι) (hl : l.Nodup) (i : ι) (hi : i ∈ l)
    (g : ι → List β) : (l.flatMap fun j => if j = i then g j else []) = g i := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.flatMap_cons]
    rw [List.nodup_cons] at hl
    by_cases h : a = i
    · subst h
      have : (l.flatMap fun j => if j = a then g j else []) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro j hj
        rw [if_neg]
        rintro rfl
        exact hl.1 hj
      simp [this]
    · rw [if_neg h, List.nil_append]
      exact ih hl.2 (by simpa [Ne.symm h] using hi)

theorem proj_chanWord (w : Z → List Γ) : proj (chanWord w) = w := by
  funext z
  rw [chanWord, proj_flatMap]
  have : (fun i => proj ((w i).map fun a => (i, a)) z) = fun i => if i = z then w i else [] := by
    funext i; rw [proj_map_mk]
  rw [this]
  exact flatMap_ite_eq _ (Finset.nodup_toList _) z (by simp) w

theorem length_chanWord (w : Z → List Γ) : (chanWord w).length = ∑ z, (w z).length := by
  rw [← sum_length_proj, proj_chanWord]

namespace Runs

theorem mono {n m : ℕ} {X : Type*} {em : X → Z → List Γ} {wt : X → F} (h : Runs n em wt) (hm : n ≤ m) :
    Runs m em wt := by
  obtain ⟨P, h1, h2⟩ := h
  exact ⟨P, h1.mono hm, h2⟩

theorem congr {n : ℕ} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (h : Runs n em wt) (e : Y ≃ X)
    (h1 : ∀ y z, em (e y) z = em' y z) (h2 : ∀ y, wt (e y) = wt' y) : Runs n em' wt' := by
  obtain ⟨P, g1, g2⟩ := h
  exact ⟨P, g1, g2.congr e h1 h2⟩

theorem mul {n m : ℕ} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (hf : Runs n em wt) (hg : Runs m em' wt') :
    Runs (n + m) (fun (x : X × Y) z => em x.1 z ++ em' x.2 z) (fun x => wt x.1 * wt' x.2) := by
  obtain ⟨P, g1, g2⟩ := hf
  obtain ⟨Q, g3, g4⟩ := hg
  exact ⟨_, g1.mul g3, g2.mul g4⟩

theorem sum {ι : Type*} [Fintype ι] {n : ι → ℕ} {X : ι → Type*} {em : ∀ i, X i → Z → List Γ}
    {wt : ∀ i, X i → F} (h : ∀ i, Runs (n i) (em i) (wt i)) :
    Runs (∑ i, n i) (fun (x : Σ i, X i) => em x.1 x.2) (fun x => wt x.1 x.2) := by
  choose P h1 h2 using h
  exact ⟨∑ i, P i, RatLe.sum _ _ _ fun i _ => h1 i, IsRuns.sum h2⟩

theorem add {n m : ℕ} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (hf : Runs n em wt) (hg : Runs m em' wt') :
    Runs (n + m) (Sum.elim em em') (Sum.elim wt wt') := by
  classical
  obtain ⟨P, g1, g2⟩ := hf
  obtain ⟨Q, g3, g4⟩ := hg
  refine ⟨P + Q, g1.add g3, fun v => ?_⟩
  obtain ⟨R, h1, h2⟩ := g2 v
  obtain ⟨R', h3, h4⟩ := g4 v
  refine ⟨R.disjSum R', ?_, ?_⟩
  · rintro (x | x)
    · simp [h1]
    · simp [h3]
  · rw [hat_add, h2, h4, Finset.sum_disjSum]
    simp

theorem kstar {n : ℕ} {X : Type*} {em : X → Z → List Γ} {wt : X → F} (hf : Runs n em wt)
    (hne : ∀ x, ∃ z, em x z ≠ []) :
    Runs (n + 1) (fun (l : List X) z => l.flatMap fun x => em x z) (fun l => (l.map wt).prod) := by
  obtain ⟨P, g1, g2⟩ := hf
  refine ⟨_, g1.kstar, g2.kstar fun x h => ?_⟩
  obtain ⟨z, hz⟩ := hne x
  exact hz (congrFun h z)

theorem one : Runs 1 (fun (_ : Unit) (_ : Z) => ([] : List Γ)) (fun _ => (1 : F)) :=
  ⟨_, RatLe.one, IsRuns.one⟩

/-- One of finitely many families of words, with weights. -/
theorem pick {κ : Type*} [Fintype κ] (w : κ → Z → List Γ) (c : κ → F) :
    Runs (∑ k, (2 * ∑ z, (w k z).length + 1)) w c := by
  classical
  refine ⟨Series.body (fun k => chanWord (w k)) c, ?_, fun v => ?_⟩
  · have := RatLe.body (F := F) (fun k => chanWord (w k)) c
    simpa only [length_chanWord] using this
  · refine ⟨univ.filter fun k => w k = v, by simp, ?_⟩
    rw [hat_body, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [proj_chanWord]
    by_cases h : w k = v
    · simp [h]
    · simp [h, Ne.symm h]

/-- Fixed words. -/
theorem const (w : Z → List Γ) :
    Runs (2 * ∑ z, (w z).length + 1) (fun (_ : Unit) => w) (fun _ => (1 : F)) := by
  have := pick (F := F) (fun _ : Unit => w) (fun _ => 1)
  simpa using this

/-- A sequence of choices. -/
theorem pi {k : ℕ} {n : Fin k → ℕ} {X : Fin k → Type*} {em : ∀ i, X i → Z → List Γ}
    {wt : ∀ i, X i → F} (h : ∀ i, Runs (n i) (em i) (wt i)) :
    Runs (∑ i, n i + 1) (fun (x : ∀ i, X i) z => (List.ofFn fun i => em i (x i) z).flatten)
      (fun x => ∏ i, wt i (x i)) := by
  induction k with
  | zero =>
    refine Runs.mono (n := 1) ((one (F := F) (Z := Z) (Γ := Γ)).congr
      ⟨fun _ => (), fun _ i => i.elim0, fun x => ?_, fun _ => rfl⟩ ?_ ?_) (by omega)
    · funext i; exact i.elim0
    · intro y z; simp
    · intro y; simp
  | succ k ih =>
    have h1 := (h 0).mul (ih (n := fun i => n i.succ) (X := fun i => X i.succ) (em := fun i => em i.succ)
      (wt := fun i => wt i.succ) fun i => h i.succ)
    refine (h1.congr (Fin.consEquiv X).symm ?_ ?_).mono ?_
    · intro y z
      simp [Fin.consEquiv, List.ofFn_succ, Fin.tail]
    · intro y
      simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.tail]
    · rw [Fin.sum_univ_succ]; omega

end Runs

end Nc
