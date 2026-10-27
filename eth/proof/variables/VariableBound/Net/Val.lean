/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
import VariableBound.Net.Basic
import StepMachines.Math.SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup

/-! # Step 3: the value of the network of one profile

The plain functions `netD` present the network `netDN` (StPresents). The value of the network of the
profile y is the sum, over the pairs (ξ, P) of an assignment ξ and a set P of objects whose clauses
ξ violates, such that
P belongs to the profile y, of ∏_j σ_(|Π_j|), for F times (−1)^|Π₀| (StVal). This is the sentence of
Appendix D, Step 3, of the paper: «Hence the nonzero terms are the tuples (ξ, Π₀, …, Π_r), each
once, with the values in (65)». The steps: if the settings of two
nodes belong to the profile, Ψ is 1 if they give the same marks to every object with the test {a, b}
and 0 otherwise, because the position of a string determines it (StLab); «in a nonzero term the
marks of an object agree at
all nodes that it touches, because its tests form a path», so the settings at which all weights are
nonzero and all marks agree are exactly the settings of the pairs (ξ, P); «h(j) sees |Π_j|», because
every incidence of
check j touches h(j); and every marked clause is counted in the sign by its owner alone. -/

namespace VariableBound.Net.Val

open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)

variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

/-! ### The lists of objects -/

/-- The list `tch g n D a` holds the places of the objects that touch the node a. -/
theorem mem_tch {a e : ℕ} : e ∈ tch g n D a ↔ e < (objs D).length ∧ tchB g n D a e = true := by
  simp [tch]

/-- No object occurs twice in the list of the objects that touch a. -/
theorem nodup_tch (a : ℕ) : (tch g n D a).Nodup := List.Nodup.filter _ List.nodup_range

/-- {a, b} with a < b is a test of the object e iff e touches a and b and no node between them. -/
theorem linkB_iff {e a b : ℕ} : linkB g n D e a b = true ↔
    a < b ∧ tchB g n D a e = true ∧ tchB g n D b e = true ∧ ∀ c < g, a < c → c < b → tchB g n D c e = false := by
  simp only [linkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, h3, fun c hc h5 h6 => ?_⟩
    rcases h4 c hc with (h | h) | h
    · exact absurd h5 h
    · exact absurd h6 h
    · exact h
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, fun c hc => ?_⟩
    by_cases h5 : a < c
    · by_cases h6 : c < b
      · exact Or.inr (h4 c hc h5 h6)
      · exact Or.inl (Or.inr h6)
    · exact Or.inl (Or.inl h5)

/-- The node a owns the object e iff e touches a and no smaller node. -/
theorem ownB_iff {e a : ℕ} : ownB g n D e a = true ↔ tchB g n D a e = true ∧ ∀ c < g, c < a → tchB g n D c e = false := by
  simp only [ownB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun c hc h3 => ?_⟩
    rcases h2 c hc with h | h
    · exact absurd h3 h
    · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun c hc => ?_⟩
    by_cases h3 : c < a
    · exact Or.inr (h2 c hc h3)
    · exact Or.inl h3

/-- The list `tst g n D a b i` holds the places of the objects of kind i with the test {a, b}. -/
theorem mem_tst {a b i e : ℕ} : e ∈ tst g n D a b i ↔
    e < (objs D).length ∧ (obAt D e).1 = i ∧ linkB g n D e (min a b) (max a b) = true := by
  simp [tst]

/-- No object occurs twice in the list of the objects with the test {a, b}. -/
theorem nodup_tst (a b i : ℕ) : (tst g n D a b i).Nodup := List.Nodup.filter _ List.nodup_range

/-- The objects with the test {a, b} are those with the test {b, a}. -/
theorem tst_comm (a b i : ℕ) : tst g n D a b i = tst g n D b a i := by
  simp only [tst, min_comm, max_comm]

/-- An object with the test {a, b} touches a. -/
theorem mem_tch_of_mem_tst {a b i e : ℕ} (h : e ∈ tst g n D a b i) : e ∈ tch g n D a := by
  obtain ⟨h1, _, h3⟩ := mem_tst.1 h
  obtain ⟨_, h5, h6, _⟩ := linkB_iff.1 h3
  refine mem_tch.2 ⟨h1, ?_⟩
  rcases le_total a b with hab | hab
  · rwa [min_eq_left hab] at h5
  · rwa [max_eq_left hab] at h6

/-! ### The settings of a pair (σ, P) -/

/-- The setting of the node a: the values of its variables, then the marks of the objects that touch
it. -/
def st (g n : ℕ) (D : Dat) (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) : List Bool :=
  (List.range (qv g n)).map (fun r => σ (a * qv g n + r)) ++ (tch g n D a).map fun e => decide (e ∈ P)

/-- The setting of the node a has ⌈n/g⌉ value bits and one mark bit for each object that touches a. -/
theorem length_st (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) : (st g n D σ P a).length = qv g n + (tch g n D a).length := by
  simp [st]

/-- The value bit number r < ⌈n/g⌉ of the setting of the node a is the value of the variable a·⌈n/g⌉ +
r. -/
theorem getD_st_lt (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) {r : ℕ} (h : r < qv g n) :
    (st g n D σ P a).getD r false = σ (a * qv g n + r) := by
  unfold st
  rw [List.getD_append _ _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

/-- The setting of (σ, P) at the node a marks an object e that touches a iff e is a member of P. -/
theorem mark_st (σ : ℕ → Bool) (P : Finset ℕ) {a e : ℕ} (h : e ∈ tch g n D a) :
    mark g n D a (st g n D σ P a) e = decide (e ∈ P) := by
  unfold mark st
  have h1 : (tch g n D a).idxOf e < (tch g n D a).length := List.idxOf_lt_length_iff.2 h
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, h1]

/-! ### The weight without the profile -/

/-- The value bits of variables numbered n or more are 0, and a marked object has all its literals
at a false. -/
def base (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) : Bool :=
  ((List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)) &&
    ((tch g n D a).all fun e => !(mark g n D a z e) ||
      (clOf D e).all fun l => !(l.1 / qv g n == a) || (z.getD (l.1 % qv g n) false != l.2))

/-- The number of marked objects of kind i that the node a owns, in the setting z. -/
def ownC (g n : ℕ) (D : Dat) (a i : ℕ) (z : List Bool) : ℕ :=
  ((tch g n D a).filter fun e => (obAt D e).1 == i && ownB g n D e a && mark g n D a z e).length

/-- The setting z of the node a has the numbers that the profile y prescribes. -/
def prof (g n : ℕ) (D : Dat) (y a : ℕ) (z : List Bool) : Bool :=
  ((List.range 2).all fun i => ownC g n D a i z == mu g D y a a i) &&
    ((List.range g).all fun a' => a' == a || (List.range 2).all fun i => (str g n D a a' i z).count true == mu g D y a a' i)

/-- ∏_(j : h(j) = a) σ_(q_j), times, for F only, (−1)^q, where q is the number of marked clauses
owned by a. -/
def wz (g n : ℕ) (D : Dat) (fl : Bool) (a : ℕ) (z : List Bool) : ℤ :=
  (((List.range D.2.length).filter fun j => home g j == a).map fun j => ParityChecks.sig (qj g n D a z j)).prod *
    (bif fl then (-1) ^ ownC g n D a 0 z else 1)

/-- The weight is `wz` if the setting is consistent and has the profile, and 0 otherwise. -/
theorem WD_eq (a : ℕ) (z : List Bool) :
    WD g n D y fl a z = if (base g n D a z && prof g n D y a z) = true then wz g n D fl a z else 0 := by
  unfold WD okD base prof ownC wz ownC
  simp only [Bool.and_assoc]

/-- What `prof` says: for both kinds i, the node a owns μ_(a,i) marked objects, and for every other
node a' < g the string of the marks of the objects with the test {a, a'} has μ_(a,a',i) ones. -/
theorem prof_iff {a : ℕ} {z : List Bool} : prof g n D y a z = true ↔
    (∀ i < 2, ownC g n D a i z = mu g D y a a i) ∧
      ∀ a' < g, a' ≠ a → ∀ i < 2, (str g n D a a' i z).count true = mu g D y a a' i := by
  simp only [prof, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a' ha' hne i hi => (h2 a' ha').resolve_left hne i hi⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a' ha' => ?_⟩
    by_cases hne : a' = a
    · exact Or.inl hne
    · exact Or.inr (h2 a' ha' hne)

/-! ### The network of one profile -/

/-- The weight W_a of the network of the profile y is `WD`. -/
theorem netDN_W (a : Fin g) (z : List Bool) : (netDN g (ctx g n D y fl)).W a z = WD g n D y fl a z := by
  simp [netDN, netD, ctx, rep]

/-- The factor f_(a,a')(z, θ) of the network of the profile y is 1 if θ is the label that z shows to
a', and 0 otherwise. -/
theorem netDN_f (a a' : Fin g) (z θ : List Bool) :
    (netDN g (ctx g n D y fl)).f a a' z θ = if (labD g n D y a a' z == θ) = true then 1 else 0 := by
  simp [netDN, netD, ctx, rep]

/-- The set S_a of the network of the profile y is the set of all words of ⌈n/g⌉ + (number of
objects that touch a) bits. -/
theorem netDN_S (a : Fin g) : (netDN g (ctx g n D y fl)).S a = words (qv g n + (tch g n D a).length) := by
  simp [netDN, netD, ctx, rep]

/-- μ_(a,a',i) = μ_(a',a,i). -/
theorem mu_comm (a a' i : ℕ) : mu g D y a a' i = mu g D y a' a i := by
  simp only [mu, min_comm, max_comm]

/-- c_(a,a') = c_(a',a). -/
theorem capD_comm (a a' : ℕ) : capD g n D y a a' = capD g n D y a' a := by
  unfold capD
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  rw [mu_comm, tst_comm]

/-- The labels of the pair {a, a'} in the network of the profile y are all words of c_(a,a') bits. -/
theorem netDN_lab (a a' : Fin g) : (netDN g (ctx g n D y fl)).lab a a' = words (capD g n D y a a') := by
  rcases le_total a a' with h | h
  · simp [Network.lab, netDN, netD, ctx, rep, min_eq_left h, max_eq_right h]
  · simp only [Network.lab, netDN, netD, ctx, rep, min_eq_right h, max_eq_left h, List.length_replicate]
    rw [capD_comm]

/-- The sum over all labels of length c of «A is the label and B is the label». -/
theorem sum_words_eq (c : ℕ) (A B : List Bool) :
    ∑ θ ∈ words c, (if (A == θ) = true then (1 : ℤ) else 0) * (if (B == θ) = true then 1 else 0) =
      if A = B ∧ A.length = c then 1 else 0 := by
  by_cases hA : A.length = c
  · rw [Finset.sum_eq_single A]
    · by_cases hAB : A = B
      · subst hAB; simp [hA]
      · have : ¬ B = A := fun h => hAB h.symm
        simp [hAB, this]
    · intro θ _ hne
      have : ¬ A = θ := fun h => hne h.symm
      simp [this]
    · intro h
      exact absurd (mem_words.2 hA) h
  · rw [Finset.sum_eq_zero]
    · simp [hA]
    · intro θ hθ
      have : ¬ A = θ := fun h => hA (h ▸ mem_words.1 hθ)
      simp [this]

/-- Ψ_(a,a') for two different nodes whose settings z, z' belong to the profile y: 1 if they give
the same mark to every object with the test {a, a'}, and 0 otherwise. Needs that the labels
determine the strings (StLab). -/
theorem Ψ_eq (hL : StLab) {a a' : Fin g} (hne : a ≠ a') {z z' : List Bool}
    (hz : prof g n D y a z = true) (hz' : prof g n D y a' z' = true) :
    (netDN g (ctx g n D y fl)).Ψ a a' z z' =
      if ∀ i < (2 : ℕ), str g n D a a' i z = str g n D a' a i z' then 1 else 0 := by
  unfold Network.Ψ
  rw [netDN_lab]
  simp only [netDN_f]
  rw [sum_words_eq]
  have h1 : ∀ κ < 2, (str g n D a a' κ z).count true = mu g D y a a' κ :=
    fun κ hκ => (prof_iff.1 hz).2 a' a'.2 (fun h => hne (Fin.ext h.symm)) κ hκ
  have h2 : ∀ κ < 2, (str g n D a' a κ z').count true = mu g D y a a' κ :=
    fun κ hκ => by rw [mu_comm]; exact (prof_iff.1 hz').2 a a.2 (fun h => hne (Fin.ext h)) κ hκ
  exact if_congr ⟨fun h => (hL.inj g n D y a a' z z' h1 h2).1 h.1, fun h => ⟨(hL.inj g n D y a a' z z' h1 h2).2 h, hL.len g n D y a a' z⟩⟩ rfl rfl

/-! ### The quantities of the profile at the settings of (σ, P) -/

/-- The length of a filtered list without repetitions is the number of elements of the set that it
lists. -/
theorem length_filter_eq_card {l : List ℕ} (hl : l.Nodup) (p : ℕ → Bool) (S : Finset ℕ) (h : ∀ e, (e ∈ l ∧ p e = true) ↔ e ∈ S) :
    (l.filter p).length = S.card := by
  rw [← List.toFinset_card_of_nodup (hl.filter p)]
  congr 1
  ext e
  rw [List.mem_toFinset, List.mem_filter]
  exact h e

/-- The string of the marks that the setting of (σ, P) at a gives to the objects of kind i with the
test {a, a'}: the bit of an object says whether it is a member of P. -/
theorem str_st (σ : ℕ → Bool) (P : Finset ℕ) (a a' i : ℕ) :
    str g n D a a' i (st g n D σ P a) = (tst g n D a a' i).map fun e => decide (e ∈ P) := by
  unfold str
  exact List.map_congr_left fun e he => mark_st σ P (mem_tch_of_mem_tst he)

/-- That string has as many ones as P has members of kind i with the test {a, a'}. -/
theorem count_str_st (σ : ℕ → Bool) (P : Finset ℕ) (a a' i : ℕ) :
    (str g n D a a' i (st g n D σ P a)).count true = pw g n D P a a' i := by
  rw [str_st, List.count, List.countP_map, List.countP_eq_length_filter]
  refine length_filter_eq_card (nodup_tst a a' i) _ _ fun e => ?_
  simp [and_comm]

/-- In the setting of (σ, P), for a set P of places of objects, the number of marked objects of kind
i that a owns is the number of members of P of kind i that a owns. -/
theorem ownC_st (σ : ℕ → Bool) {P : Finset ℕ} (hP : P ⊆ Finset.range (objs D).length) (a i : ℕ) :
    ownC g n D a i (st g n D σ P a) = oc g n D P a i := by
  refine length_filter_eq_card (nodup_tch a) _ _ fun e => ?_
  simp only [Bool.and_eq_true, beq_iff_eq, Finset.mem_filter]
  constructor
  · rintro ⟨he, ⟨h1, h2⟩, h3⟩
    rw [mark_st σ P he] at h3
    exact ⟨by simpa using h3, h1, h2⟩
  · rintro ⟨h3, h1, h2⟩
    have he : e ∈ tch g n D a := mem_tch.2 ⟨Finset.mem_range.1 (hP h3), (ownB_iff.1 h2).1⟩
    refine ⟨he, ⟨h1, h2⟩, ?_⟩
    rw [mark_st σ P he]
    simpa using h3

/-- «h(j) sees |Π_j|»: at the home of check j, the number of marked incidences of check j in the
setting of (σ, P) is the number of members of P that are incidences of check j, for a set P of
places of objects. -/
theorem qj_st (σ : ℕ → Bool) {P : Finset ℕ} (hP : P ⊆ Finset.range (objs D).length) (j : ℕ) :
    qj g n D (home g j) (st g n D σ P (home g j)) j = (chP D P j).card := by
  refine length_filter_eq_card (nodup_tch _) _ _ fun e => ?_
  simp only [Bool.and_eq_true, beq_iff_eq, chP, Finset.mem_filter]
  constructor
  · rintro ⟨he, ⟨h1, h2⟩, h3⟩
    rw [mark_st σ P he] at h3
    exact ⟨by simpa using h3, h1, h2⟩
  · rintro ⟨h3, h1, h2⟩
    have he : e ∈ tch g n D (home g j) := mem_tch.2 ⟨Finset.mem_range.1 (hP h3), by rw [← h2]; exact tchB_home h1⟩
    refine ⟨he, ⟨h1, h2⟩, ?_⟩
    rw [mark_st σ P he]
    simpa using h3

/-- For a set P of places of objects: the settings of (σ, P) at all nodes have the numbers of the
profile y exactly if P belongs to y. -/
theorem prof_st_iff (σ : ℕ → Bool) {P : Finset ℕ} (hP : P ⊆ Finset.range (objs D).length) :
    (∀ a : Fin g, prof g n D y a (st g n D σ P a) = true) ↔ Match g n D y P := by
  simp only [prof_iff, ownC_st σ hP, count_str_st]
  constructor
  · intro h i hi a ha
    exact ⟨(h ⟨a, ha⟩).1 i hi, fun b hb hne => (h ⟨a, ha⟩).2 b hb hne i hi⟩
  · intro h a
    exact ⟨fun i hi => (h i hi a a.2).1, fun b hb hne i hi => (h i hi a a.2).2 b hb hne⟩

/-! ### Every object has one owner -/

/-- Every object has an owner, if g > 0 and the data are well formed (WfD). -/
theorem exists_owner (hg : 0 < g) (hW : WfD k n D) {e : ℕ} (he : e < (objs D).length) : ∃ a < g, ownB g n D e a = true := by
  obtain ⟨a₀, _, h₀⟩ := exists_tch (g := g) hg hW he
  have hex : ∃ a, tchB g n D a e = true := ⟨a₀, h₀⟩
  classical
  refine ⟨Nat.find hex, tch_lt hg hW he (Nat.find_spec hex), ownB_iff.2 ⟨Nat.find_spec hex, fun c _ hc => ?_⟩⟩
  simpa using Nat.find_min hex hc

/-- An object has at most one owner among the nodes below g. -/
theorem owner_unique {e a a' : ℕ} (ha : a < g) (ha' : a' < g) (h : ownB g n D e a = true) (h' : ownB g n D e a' = true) : a = a' := by
  obtain ⟨h1, h2⟩ := ownB_iff.1 h
  obtain ⟨h3, h4⟩ := ownB_iff.1 h'
  rcases Nat.lt_trichotomy a a' with hlt | heq | hgt
  · rw [h4 a ha hlt] at h1; exact absurd h1 (by simp)
  · exact heq
  · rw [h2 a' ha' hgt] at h3; exact absurd h3 (by simp)

/-- Counting the members of P with a property p owner by owner counts each once, if g > 0, the data
are well formed (WfD) and P is a set of places of objects. -/
theorem sum_owner (hg : 0 < g) (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ Finset.range (objs D).length) (p : ℕ → Prop) [DecidablePred p] :
    ∑ a ∈ Finset.range g, (P.filter fun e => p e ∧ ownB g n D e a = true).card = (P.filter p).card := by
  rw [← card_biUnion]
  · congr 1
    ext e
    simp only [mem_biUnion, mem_range, mem_filter]
    constructor
    · rintro ⟨a, -, he, hp, -⟩; exact ⟨he, hp⟩
    · rintro ⟨he, hp⟩
      obtain ⟨a, ha, ho⟩ := exists_owner hg hW (mem_range.1 (hP he))
      exact ⟨a, ha, he, hp, ho⟩
  · intro a ha a' ha' hne
    rw [Function.onFun, disjoint_left]
    intro e h1 h2
    exact hne (owner_unique (mem_range.1 ha) (mem_range.1 ha') (mem_filter.1 h1).2.2 (mem_filter.1 h2).2.2)


/-- The weights of the nodes at the settings of (σ, P) multiply to the value of the term of P in
display (65), if g > 0, the data are well formed (WfD) and P is a set of places of objects. -/
theorem prod_wz_st (hg : 0 < g) (hw : WfD k n D) (σ : ℕ → Bool) {P : Finset ℕ}
    (hP : P ⊆ Finset.range (objs D).length) :
    ∏ a : Fin g, wz g n D fl a (st g n D σ P a) = wt D fl P := by
  unfold wz wt
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [Fin.prod_univ_eq_prod_range (fun a => (((List.range D.2.length).filter fun j => home g j == a).map
      fun j => ParityChecks.sig (qj g n D a (st g n D σ P a) j)).prod) g]
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.range D.2.length) (t := Finset.range g) (g := home g)
      (fun j _ => Finset.mem_range.2 (Nat.mod_lt _ hg))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← List.prod_toFinset _ (List.Nodup.filter _ List.nodup_range)]
    refine Finset.prod_congr ?_ fun j hj => ?_
    · ext j; simp
    · have hja : home g j = a := (Finset.mem_filter.1 hj).2
      rw [← hja, qj_st σ hP]
  · cases fl
    · simp
    · simp only [cond_true]
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      simp only [ownC_st σ hP]
      rw [Fin.sum_univ_eq_sum_range (fun a => oc g n D P a 0) g]
      exact sum_owner hg hw hP _

/-! ### Good settings are the settings of the pairs (σ, P) -/

/-- What `base` says: a value bit of a variable with a number ≥ n is 0, and every object that
touches a is unmarked or has all its literals at a false. -/
theorem base_iff {a : ℕ} {z : List Bool} : base g n D a z = true ↔
    (∀ r < qv g n, a * qv g n + r < n ∨ z.getD r false = false) ∧
      ∀ e ∈ tch g n D a, mark g n D a z e = false ∨
        ∀ l ∈ (clOf D e), l.1 / qv g n ≠ a ∨ z.getD (l.1 % qv g n) false ≠ l.2 := by
  simp only [base, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    bne_iff_ne, ne_eq, beq_eq_false_iff_ne]

/-- σ violates the clause C iff it makes all literals of C false. -/
theorem vio_iff {σ : ℕ → Bool} {C : Cl} : vio σ C = true ↔ ∀ l ∈ C, σ l.1 ≠ l.2 := by
  simp only [vio, List.all_eq_true, bne_iff_ne, ne_eq]

/-- The family z of settings is good: at every node `base` holds (the value bits of variables
numbered n or more are 0, no marked object has a true literal there), and any two nodes a < a' give
the same marks to the objects with the test {a, a'}. -/
def Gd (g n : ℕ) (D : Dat) (z : Fin g → List Bool) : Prop :=
  (∀ a : Fin g, base g n D a (z a) = true) ∧
    ∀ a a' : Fin g, a < a' → ∀ i < 2, str g n D a a' i (z a) = str g n D a' a i (z a')

/-- A node holds at least one variable, if there is a node and a variable: ⌈n/g⌉ > 0 for g > 0 and n > 0. -/
theorem qv_pos (hg : 0 < g) (hn : 0 < n) : 0 < qv g n := Nat.div_pos (by omega) hg

/-- For well-formed data (WfD), the variables of the clause of an object are below n. -/
theorem lit_lt (hw : WfD k n D) {e : ℕ} (he : e < (objs D).length) {l : ℕ × Bool} (hl : l ∈ (clOf D e)) : l.1 < n :=
  (clOf_wf hw he).2.2 l hl

/-- For well-formed data (WfD), the clause of an object has a literal. -/
theorem exists_lit (hw : WfD k n D) {e : ℕ} (he : e < (objs D).length) : ∃ l, l ∈ (clOf D e) :=
  List.exists_mem_of_ne_nil _ (clOf_wf hw he).1

/-- The settings of (σ, P) are good if g > 0, the data are well formed (WfD), σ is false at all
numbers ≥ n, and σ violates the clauses of all members of P. -/
theorem st_good (hg : 0 < g) (hw : WfD k n D) {σ : ℕ → Bool} (hσ : ∀ x, n ≤ x → σ x = false) {P : Finset ℕ}
    (hP : P ⊆ vset σ D) : Gd g n D fun a => st g n D σ P a := by
  refine ⟨fun a => base_iff.2 ⟨fun r hr => ?_, fun e he => ?_⟩, fun a a' _ i _ => ?_⟩
  · by_cases h : a.val * qv g n + r < n
    · exact Or.inl h
    · exact Or.inr (by rw [getD_st_lt σ P a hr]; exact hσ _ (not_lt.1 h))
  · rw [mark_st σ P he]
    by_cases heP : e ∈ P
    · refine Or.inr fun l hl => ?_
      by_cases hla : l.1 / qv g n = a
      · refine Or.inr ?_
        have hlt := lit_lt hw (mem_tch.1 he).1 hl
        have hq : 0 < qv g n := qv_pos hg (by omega)
        rw [getD_st_lt σ P a (Nat.mod_lt _ hq), ← hla, Nat.div_add_mod']
        exact vio_iff.1 (Finset.mem_filter.1 (hP heP)).2 l hl
      · exact Or.inl hla
    · exact Or.inl (by simpa using heP)
  · rw [str_st, str_st, tst_comm]

/-- The assignment σ of the n variables, continued to all numbers: at x < n it is σ. -/
theorem ext_of_lt {σ : Fin n → Bool} {x : ℕ} (h : x < n) : ext σ x = σ ⟨x, h⟩ := by simp [Mark.ext, h]

/-- The assignment σ of the n variables, continued to all numbers: at x ≥ n it is false. -/
theorem ext_of_le {σ : Fin n → Bool} {x : ℕ} (h : n ≤ x) : ext σ x = false := by simp [Mark.ext, not_lt.2 h]

/-- The settings determine σ and P: «each once». Needs g > 0, well-formed data (WfD), and that P and
P' are sets of places of objects. -/
theorem st_inj (hg : 0 < g) (hw : WfD k n D) {σ σ' : Fin n → Bool} {P P' : Finset ℕ}
    (hP : P ⊆ Finset.range (objs D).length) (hP' : P' ⊆ Finset.range (objs D).length)
    (h : (fun a : Fin g => st g n D (ext σ) P a) = fun a : Fin g => st g n D (ext σ') P' a) : σ = σ' ∧ P = P' := by
  constructor
  · funext x
    have hq : 0 < qv g n := qv_pos hg (by have := x.2; omega)
    have h1 := congrFun h ⟨x.1 / qv g n, div_qv_lt hg x.2⟩
    have h2 := congrArg (fun l => l.getD (x.1 % qv g n) false) h1
    simp only [getD_st_lt _ _ _ (Nat.mod_lt _ hq), Nat.div_add_mod'] at h2
    rwa [ext_of_lt x.2, ext_of_lt x.2] at h2
  · ext e
    by_cases he : e < (objs D).length
    · obtain ⟨l, hl⟩ := exists_lit hw he
      have hlt := lit_lt hw he hl
      have ht : e ∈ tch g n D (l.1 / qv g n) := mem_tch.2 ⟨he, tchB_iff.2 (Or.inl ⟨l, hl, rfl⟩)⟩
      have h1 := congrFun h ⟨l.1 / qv g n, div_qv_lt hg hlt⟩
      have h2 := congrArg (fun z => mark g n D (l.1 / qv g n) z e) h1
      simp only [mark_st _ _ ht] at h2
      simpa using h2
    · exact ⟨fun h => absurd (Finset.mem_range.1 (hP h)) he, fun h => absurd (Finset.mem_range.1 (hP' h)) he⟩

/-- «In a nonzero term the marks of an object agree at all nodes that it touches, because its tests
form a path»: in a good family z of settings, an object e has the same mark at any two nodes that it
touches. -/
theorem mark_eq {z : Fin g → List Bool} (hz : Gd g n D z) {e : ℕ} (he : e < (objs D).length) {a a' : Fin g}
    (ha : tchB g n D a e = true) (ha' : tchB g n D a' e = true) : mark g n D a (z a) e = mark g n D a' (z a') e := by
  refine SatNet.eq_of_consec (ι := Fin g) (V := Unit) (idx := fun a => a.val)
    (lab := fun a => if tchB g n D a e = true then some () else none) Fin.val_injective
    (z := fun a => mark g n D a (z a) e) ?_ (p := a) (q := a') (by simp [ha]) (by simp [ha, ha'])
  rintro p q ⟨h1, h2, h3, h4⟩
  have hp : tchB g n D p e = true := by
    by_contra h
    simp [h] at h2
  have hq : tchB g n D q e = true := by
    by_contra h
    simp [hp, h] at h3
  have hl : linkB g n D e p q = true := linkB_iff.2 ⟨h1, hp, hq, fun c hcg h5 h6 => by
    have h7 := h4 ⟨c, hcg⟩ h5 h6
    by_contra h
    simp only [Bool.not_eq_false] at h
    simp [hp, h] at h7⟩
  have hpq : p.val ≤ q.val := le_of_lt h1
  have hm : e ∈ tst g n D p q (obAt D e).1 := mem_tst.2 ⟨he, rfl, by rwa [min_eq_left hpq, max_eq_right hpq]⟩
  have hs := hz.2 p q h1 _ (kind_lt he)
  unfold str at hs
  rw [tst_comm q p] at hs
  exact List.map_inj_left.1 hs e hm

/-- Two words of the same length with the same bits are equal. -/
theorem ext_getD {l l' : List Bool} (hl : l.length = l'.length) (h : ∀ j < l.length, l.getD j false = l'.getD j false) : l = l' := by
  apply List.ext_getElem hl
  intro j h1 h2
  have := h j h1
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

/-- The mark bit number t of the setting of (σ, P) at a says whether the object number t in the list
of the objects that touch a is a member of P. -/
theorem getD_st_ge (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) {t : ℕ} (h : t < (tch g n D a).length) :
    (st g n D σ P a).getD (qv g n + t) false = decide ((tch g n D a)[t] ∈ P) := by
  unfold st
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, h]

/-- The mark of the object number t in the list of the objects that touch a is the bit number ⌈n/g⌉ +
t of the setting. -/
theorem mark_getElem (a : ℕ) (z : List Bool) {t : ℕ} (h : t < (tch g n D a).length) :
    mark g n D a z (tch g n D a)[t] = z.getD (qv g n + t) false := by
  unfold mark
  rw [(nodup_tch a).idxOf_getElem]

/-- Every good family of settings of the right lengths is the family of the settings of some (σ, P),
and σ violates the clauses of all members of P: «all literals of a marked clause are false, so Π₀ ⊆
V(ξ) and Π_j ⊆ V_j(ξ)». Needs g > 0 and well-formed data (WfD). -/
theorem st_surj (hg : 0 < g) (hw : WfD k n D) {z : Fin g → List Bool}
    (hlen : ∀ a, (z a).length = qv g n + (tch g n D a).length) (hz : Gd g n D z) :
    ∃ (σ : Fin n → Bool) (P : Finset ℕ), P ⊆ vset (ext σ) D ∧ (fun a : Fin g => st g n D (ext σ) P a) = z := by
  classical
  let σ : Fin n → Bool := fun x => (z ⟨x.1 / qv g n, div_qv_lt hg x.2⟩).getD (x.1 % qv g n) false
  let P : Finset ℕ := (Finset.range (objs D).length).filter fun e => ∃ a : Fin g, tchB g n D a e = true ∧ mark g n D a (z a) e = true
  have key : ∀ (a : Fin g) (e : ℕ), e ∈ tch g n D a → decide (e ∈ P) = mark g n D a (z a) e := by
    intro a e he
    obtain ⟨he1, he2⟩ := mem_tch.1 he
    by_cases hm : mark g n D a (z a) e = true
    · rw [hm]
      exact decide_eq_true (Finset.mem_filter.2 ⟨Finset.mem_range.2 he1, a, he2, hm⟩)
    · rw [Bool.not_eq_true] at hm
      rw [hm]
      refine decide_eq_false fun h => ?_
      obtain ⟨a', h1, h2⟩ := (Finset.mem_filter.1 h).2
      rw [mark_eq hz he1 h1 he2, hm] at h2
      exact Bool.false_ne_true h2
  refine ⟨σ, P, fun e he => ?_, funext fun a => ext_getD (by rw [length_st, hlen]) fun j hj => ?_⟩
  · obtain ⟨he1, a', h1, h2⟩ := Finset.mem_filter.1 he
    have he1' := Finset.mem_range.1 he1
    refine Finset.mem_filter.2 ⟨he1, vio_iff.2 fun l hl => ?_⟩
    have hlt := lit_lt hw he1' hl
    have ht : tchB g n D (l.1 / qv g n) e = true := tchB_iff.2 (Or.inl ⟨l, hl, rfl⟩)
    have hm : mark g n D (l.1 / qv g n) (z ⟨l.1 / qv g n, div_qv_lt hg hlt⟩) e = true := by
      rw [← h2]
      exact mark_eq hz he1' (a := ⟨l.1 / qv g n, div_qv_lt hg hlt⟩) ht h1
    have hb := (base_iff.1 (hz.1 ⟨l.1 / qv g n, div_qv_lt hg hlt⟩)).2 e (mem_tch.2 ⟨he1', ht⟩)
    rcases hb with hb | hb
    · rw [hm] at hb
      exact absurd hb (by simp)
    · rcases hb l hl with h | h
      · exact absurd rfl h
      · rw [ext_of_lt hlt]
        exact h
  · rw [length_st] at hj
    by_cases hjq : j < qv g n
    · rw [getD_st_lt _ _ _ hjq]
      by_cases hx : a.val * qv g n + j < n
      · rw [ext_of_lt hx]
        have e1 : (a.val * qv g n + j) / qv g n = a.val := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hjq, Nat.zero_add]
        have e2 : (a.val * qv g n + j) % qv g n = j := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjq]
        show (z ⟨(a.val * qv g n + j) / qv g n, _⟩).getD ((a.val * qv g n + j) % qv g n) false = _
        have e3 : (⟨(a.val * qv g n + j) / qv g n, div_qv_lt hg hx⟩ : Fin g) = a := Fin.ext e1
        rw [e3, e2]
      · rw [ext_of_le (not_lt.1 hx)]
        exact (((base_iff.1 (hz.1 a)).1 j hjq).resolve_left hx).symm
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hjq)
      have ht : t < (tch g n D a).length := by omega
      rw [getD_st_ge _ _ _ ht, key a _ (List.getElem_mem ht), mark_getElem _ _ ht]

/-- A sum over the good families of settings is a sum over the pairs (σ, P) of an assignment and a
set of objects whose clauses it violates, if g > 0 and the data are well formed (WfD). -/
theorem sum_good (hg : 0 < g) (hw : WfD k n D) (F : (Fin g → List Bool) → ℤ) :
    (∑ z ∈ Fintype.piFinset fun a : Fin g => words (qv g n + (tch g n D a).length),
      by classical exact if Gd g n D z then F z else 0) =
      ∑ σ : Fin n → Bool, ∑ P ∈ (vset (ext σ) D).powerset, F fun a => st g n D (ext σ) P a := by
  classical
  rw [← Finset.sum_filter, Finset.sum_sigma']
  symm
  have hsub : ∀ σ : ℕ → Bool, vset σ D ⊆ Finset.range (objs D).length := fun σ => Finset.filter_subset _ _
  refine Finset.sum_nbij (fun x => fun a : Fin g => st g n D (ext x.1) x.2 a) ?_ ?_ ?_ fun _ _ => rfl
  · rintro ⟨σ, P⟩ hx
    have hP : P ⊆ vset (ext σ) D := Finset.mem_powerset.1 (Finset.mem_sigma.1 hx).2
    exact Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun a => mem_words.2 (length_st _ _ _),
      st_good hg hw (fun x hx => ext_of_le hx) hP⟩
  · rintro ⟨σ, P⟩ hx ⟨σ', P'⟩ hx' h
    have hP : P ⊆ vset (ext σ) D := Finset.mem_powerset.1 (Finset.mem_sigma.1 (Finset.mem_coe.1 hx)).2
    have hP' : P' ⊆ vset (ext σ') D := Finset.mem_powerset.1 (Finset.mem_sigma.1 (Finset.mem_coe.1 hx')).2
    obtain ⟨h1, h2⟩ := st_inj hg hw (hP.trans (hsub _)) (hP'.trans (hsub _)) h
    subst h1; subst h2; rfl
  · intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hz)
    obtain ⟨σ, P, hP, hzz⟩ := st_surj hg hw (fun a => mem_words.1 (Fintype.mem_piFinset.1 h1 a)) h2
    exact ⟨⟨σ, P⟩, Finset.mem_coe.2 (Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_powerset.2 hP⟩), hzz⟩

/-! ### The value of the network of one profile -/

/-- One term of the value: the product of the weights at a good family of settings that has the
numbers of the profile, and 0 at every other family. Needs that the labels determine the strings
(StLab). -/
theorem term_eq (hL : StLab) (z : Fin g → List Bool) :
    (∏ a, (netDN g (ctx g n D y fl)).W a (z a)) *
        ∏ p ∈ pairs (Fin g), (netDN g (ctx g n D y fl)).Ψ p.1 p.2 (z p.1) (z p.2) =
      by classical exact if Gd g n D z then
        (if ∀ a : Fin g, prof g n D y a (z a) = true then ∏ a : Fin g, wz g n D fl a (z a) else 0) else 0 := by
  classical
  simp only [netDN_W, WD_eq]
  by_cases hp : ∀ a : Fin g, (base g n D a (z a) && prof g n D y a (z a)) = true
  · have hb1 : ∀ a : Fin g, base g n D a (z a) = true := fun a => (Bool.and_eq_true _ _ ▸ hp a).1
    have hp1 : ∀ a : Fin g, prof g n D y a (z a) = true := fun a => (Bool.and_eq_true _ _ ▸ hp a).2
    have hΨ : ∀ p ∈ pairs (Fin g), (netDN g (ctx g n D y fl)).Ψ p.1 p.2 (z p.1) (z p.2) =
        if ∀ i < (2 : ℕ), str g n D p.1 p.2 i (z p.1) = str g n D p.2 p.1 i (z p.2) then 1 else 0 :=
      fun p hpp => Ψ_eq hL (ne_of_lt (Finset.mem_filter.1 hpp).2) (hp1 p.1) (hp1 p.2)
    have hPs : ∏ p ∈ pairs (Fin g), (netDN g (ctx g n D y fl)).Ψ p.1 p.2 (z p.1) (z p.2) =
        if ∀ p ∈ pairs (Fin g), ∀ i < 2, str g n D p.1 p.2 i (z p.1) = str g n D p.2 p.1 i (z p.2) then 1 else 0 := by
      rw [Finset.prod_congr rfl hΨ, Finset.prod_ite_zero, Finset.prod_const_one]
      split_ifs <;> simp_all
    rw [hPs, Finset.prod_congr rfl fun a _ => if_pos (hp a), if_pos hp1]
    by_cases hG : Gd g n D z
    · have hall : ∀ p ∈ pairs (Fin g), ∀ i < 2, str g n D p.1 p.2 i (z p.1) = str g n D p.2 p.1 i (z p.2) :=
        fun p hpp => hG.2 p.1 p.2 (Finset.mem_filter.1 hpp).2
      rw [if_pos hG, if_pos hall, mul_one]
    · rw [if_neg hG, if_neg, mul_zero]
      intro h
      exact hG ⟨hb1, fun a a' haa => h (a, a') (Finset.mem_filter.2 ⟨Finset.mem_univ _, haa⟩)⟩
  · obtain ⟨a, ha⟩ := not_forall.1 hp
    rw [Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha), zero_mul]
    by_cases hG : Gd g n D z
    · rw [if_pos hG, if_neg]
      intro h
      exact ha (by rw [hG.1 a, h a]; rfl)
    · rw [if_neg hG]


/-- The value of the network of the profile y is the sum, over the assignments σ and the sets P of
objects whose clauses σ violates, of the term of P if P belongs to y. Needs that the labels
determine the strings (StLab), g > 0 and well-formed data (WfD). -/
theorem netVal (hL : StLab) (hg : 0 < g) (hw : WfD k n D) :
    (netDN g (ctx g n D y fl)).value =
      ∑ σ : Fin n → Bool, ∑ P ∈ (vset (ext σ) D).powerset, by classical exact if Match g n D y P then wt D fl P else 0 := by
  classical
  unfold Network.value
  simp only [term_eq hL]
  have hS : (Fintype.piFinset (netDN g (ctx g n D y fl)).S) =
      Fintype.piFinset fun a : Fin g => words (qv g n + (tch g n D a).length) := by
    congr 1
    funext a
    exact netDN_S a
  rw [hS]
  have := sum_good hg hw (fun z => if ∀ a : Fin g, prof g n D y a (z a) = true then ∏ a : Fin g, wz g n D fl a (z a) else 0)
  refine Eq.trans ?_ (this.trans ?_)
  · exact Finset.sum_congr rfl fun z _ => by congr
  · refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun P hP => ?_
    have hP' : P ⊆ Finset.range (objs D).length := (Finset.mem_powerset.1 hP).trans (Finset.filter_subset _ _)
    rw [prod_wz_st hg hw _ hP']
    exact if_congr (prof_st_iff _ hP') rfl rfl

/-- Step 3: «Hence the nonzero terms are the tuples (ξ, Π₀, …, Π_r), each once, with the values in
(65)», for the network of one profile y, admissible or not. Hypotheses: g > 0; ψ has clauses of 1 to
k literals on variables
below n and the checks are lists without repetition of numbers of clauses (WfD); the labels
determine the strings (StLab). -/
public theorem stVal (hL : StLab) : StVal := fun _ _ _ _ _ _ hg hw => netVal hL hg hw

/-- The plain functions `netD` present the network `netDN`, in every context. -/
public theorem stPresents : StPresents := fun c =>
  { S_eq := fun _ => rfl
    c_eq := fun _ _ _ => rfl
    lab_eq := fun a b _ => by
      rcases le_total a b with h | h
      · simp only [Network.lab, netDN, min_eq_left h, max_eq_right h]; rfl
      · simp only [Network.lab, netDN, min_eq_right h, max_eq_left h]
        exact congrArg words (capD_comm _ _)
    W_runs := fun _ _ _ => Stepped.Reaches.halt rfl (Nat.le_refl 0)
    f_runs := fun _ _ _ _ _ _ _ => Stepped.Reaches.halt rfl (Nat.le_refl 0) }

end VariableBound.Net.Val
