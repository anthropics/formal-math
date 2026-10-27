/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
import StepMachines.Math.SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup

/-! # Marks and layers: the value of the network of one profile

The clauses come as a list `Ls` of formulas, the layers; `cls Ls` lists all clauses, each with the
number of its layer, and a clause is named by its position in that list.
The plain functions `markF` present the network `markN` (StMarkPresents). The value of the network
of the profile y is the signed number of pairs (σ, P), where σ is an
assignment and P a set of clauses that σ violates, such that P has the profile y (StMarkVal). The
steps: if the states of two nodes have the profile, their
interaction is 1 if the marks that they compare agree and 0 otherwise, because the code of the
labels can be read back; the states at which all weights are
nonzero and all marks agree are exactly the states of the pairs (σ, P), because the nodes that a
clause touches form a chain; at such a state the profile's numbers count members of P. -/

namespace PaddedDescent.F.Mark.Val

open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark

/-- The codes of the strings of a list of layers, written one after the other, can be read back. -/
theorem encCat (hI : StEncInj) (β b : ℕ) (h0 : 0 < b) (hb : b ≤ 2 ^ β) (s s' : ℕ → List Bool) : ∀ l : List ℕ,
    (∀ i ∈ l, (s i).length = (s' i).length) → (l.flatMap fun i => enc β b (s i)) = (l.flatMap fun i => enc β b (s' i)) → ∀ i ∈ l, s i = s' i
  | [], _, _ => by simp
  | j :: l, hl, h => by
      simp only [List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := hI β b _ _ _ _ h0 hb (hl j (by simp)) h
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact h1
      · exact encCat hI β b h0 hb s s' l (fun i hi => hl i (List.mem_cons_of_mem _ hi)) h2 i hi

/-- The length of the codes of the strings of a list of layers, written one after the other. -/
theorem encLen (hL : StEncLen) (β b : ℕ) (h0 : 0 < b) (s : ℕ → List Bool) (l : List ℕ) :
    (l.flatMap fun i => enc β b (s i)).length = (l.map fun i => (s i).count true * (1 + β) + ((s i).length + b - 1) / b).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ih, hL β b _ h0]

variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}

/-! ### The lists of clause indices -/

theorem tchB_iff {a e : ℕ} : tchB g n Ls a e = true ↔ ∃ l ∈ (clAt Ls e).2, l.1 / qv g n = a := by
  simp [tchB]

theorem mem_tch {a e : ℕ} : e ∈ tch g n Ls a ↔ e < (cls Ls).length ∧ tchB g n Ls a e = true := by
  simp [tch]

theorem nodup_tch (a : ℕ) : (tch g n Ls a).Nodup := List.Nodup.filter _ List.nodup_range

theorem linkB_iff {e a b : ℕ} : linkB g n Ls e a b = true ↔
    a < b ∧ tchB g n Ls a e = true ∧ tchB g n Ls b e = true ∧ ∀ c < g, a < c → c < b → tchB g n Ls c e = false := by
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

theorem ownB_iff {e a : ℕ} : ownB g n Ls e a = true ↔ tchB g n Ls a e = true ∧ ∀ c < g, c < a → tchB g n Ls c e = false := by
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

theorem mem_tst {a b i e : ℕ} : e ∈ tst g n Ls a b i ↔
    e < (cls Ls).length ∧ (clAt Ls e).1 = i ∧ linkB g n Ls e (min a b) (max a b) = true := by
  simp [tst]

theorem nodup_tst (a b i : ℕ) : (tst g n Ls a b i).Nodup := List.Nodup.filter _ List.nodup_range

theorem tst_comm (a b i : ℕ) : tst g n Ls a b i = tst g n Ls b a i := by
  simp only [tst, min_comm, max_comm]

theorem mem_tch_of_mem_tst {a b i e : ℕ} (h : e ∈ tst g n Ls a b i) : e ∈ tch g n Ls a := by
  obtain ⟨h1, _, h3⟩ := mem_tst.1 h
  obtain ⟨_, h5, h6, _⟩ := linkB_iff.1 h3
  refine mem_tch.2 ⟨h1, ?_⟩
  rcases le_total a b with hab | hab
  · rwa [min_eq_left hab] at h5
  · rwa [max_eq_left hab] at h6

/-! ### The state of a pair (σ, P) -/

/-- The state word of the node a: the values of its variables, then the marks of the clauses that
touch it. -/
def st (g n : ℕ) (Ls : List Fml) (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) : List Bool :=
  (List.range (qv g n)).map (fun r => σ (a * qv g n + r)) ++ (tch g n Ls a).map fun e => decide (e ∈ P)

theorem length_st (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) : (st g n Ls σ P a).length = qv g n + (tch g n Ls a).length := by
  simp [st]

theorem getD_st_lt (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) {r : ℕ} (h : r < qv g n) :
    (st g n Ls σ P a).getD r false = σ (a * qv g n + r) := by
  unfold st
  rw [List.getD_append _ _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem mark_st (σ : ℕ → Bool) (P : Finset ℕ) {a e : ℕ} (h : e ∈ tch g n Ls a) :
    mark g n Ls a (st g n Ls σ P a) e = decide (e ∈ P) := by
  unfold mark st
  have h1 : (tch g n Ls a).idxOf e < (tch g n Ls a).length := List.idxOf_lt_length_iff.2 h
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, h1]

/-! ### The weight without the profile -/

/-- Variables beyond n are false, and every literal of a marked clause whose variable lies at the
node a is false in the state z. -/
def base (g n : ℕ) (Ls : List Fml) (a : ℕ) (z : List Bool) : Bool :=
  ((List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)) &&
    ((tch g n Ls a).all fun e => !(mark g n Ls a z e) ||
      (clAt Ls e).2.all fun l => !(l.1 / qv g n == a) || (z.getD (l.1 % qv g n) false != l.2))

/-- The number of marked clauses of layer i that the node a owns, in the state z. -/
def ownC (g n : ℕ) (Ls : List Fml) (a i : ℕ) (z : List Bool) : ℕ :=
  ((tch g n Ls a).filter fun e => (clAt Ls e).1 == i && ownB g n Ls e a && mark g n Ls a z e).length

/-- The number of marked clauses of the layers after the first that the node a owns, in the state z. -/
def sgE (g n : ℕ) (Ls : List Fml) (a : ℕ) (z : List Bool) : ℕ :=
  ((tch g n Ls a).filter fun e => decide (1 ≤ (clAt Ls e).1) && ownB g n Ls e a && mark g n Ls a z e).length

/-- The state z of the node a has the numbers that the profile y prescribes. -/
def prof (g n : ℕ) (Ls : List Fml) (y a : ℕ) (z : List Bool) : Bool :=
  ((List.range Ls.length).all fun i => ownC g n Ls a i z == mu g Ls y a a i) &&
    ((List.range g).all fun a' => a' == a || (List.range Ls.length).all fun i => (str g n Ls a a' i z).count true == mu g Ls y a a' i)

/-- The weight is the sign if the state is consistent and has the profile, and 0 otherwise. -/
theorem mW_eq (a : ℕ) (z : List Bool) :
    mW g n Ls y a z = if (base g n Ls a z && prof g n Ls y a z) = true then (-1) ^ sgE g n Ls a z else 0 := by
  unfold mW base prof ownC sgE
  simp only [Bool.and_assoc]

theorem prof_iff {a : ℕ} {z : List Bool} : prof g n Ls y a z = true ↔
    (∀ i < Ls.length, ownC g n Ls a i z = mu g Ls y a a i) ∧
      ∀ a' < g, a' ≠ a → ∀ i < Ls.length, (str g n Ls a a' i z).count true = mu g Ls y a a' i := by
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

/-- The context with the numbers g, n, β, b in unary. -/
abbrev ctx (g n β b : ℕ) (Ls : List Fml) (y : ℕ) : MCtx :=
  ((List.replicate g (), List.replicate n (), List.replicate β (), List.replicate b ()), (Ls, y))

theorem markN_W (a : Fin g) (z : List Bool) : (markN g (ctx g n β b Ls y)).W a z = mW g n Ls y a z := by
  simp [markN, markF]

theorem markN_f (a a' : Fin g) (z θ : List Bool) :
    (markN g (ctx g n β b Ls y)).f a a' z θ = if (mlab g n β b Ls a a' z == θ) = true then 1 else 0 := by
  simp [markN, markF]

theorem markN_S (a : Fin g) : (markN g (ctx g n β b Ls y)).S a = words (qv g n + (tch g n Ls a).length) := by
  simp [markN, markF]

theorem mu_comm (a a' i : ℕ) : mu g Ls y a a' i = mu g Ls y a' a i := by
  simp only [mu, min_comm, max_comm]

theorem mcap_comm (a a' : ℕ) : mcap g n β b Ls y a a' = mcap g n β b Ls y a' a := by
  unfold mcap
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  rw [mu_comm, tst_comm]

theorem markN_lab (a a' : Fin g) : (markN g (ctx g n β b Ls y)).lab a a' = words (mcap g n β b Ls y a a') := by
  rcases le_total a a' with h | h
  · simp [Network.lab, markN, markF, min_eq_left h, max_eq_right h]
  · simp only [Network.lab, markN, markF, min_eq_right h, max_eq_left h, List.length_replicate]
    rw [mcap_comm]

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

theorem length_str (a a' i : ℕ) (z : List Bool) : (str g n Ls a a' i z).length = (tst g n Ls a a' i).length := by
  simp [str]

/-- The label that a state with the profile writes has the prescribed length. -/
theorem length_mlab (hLen : StEncLen) (h0 : 0 < b) {a a' : ℕ} (ha' : a' < g) (hne : a' ≠ a) {z : List Bool}
    (hz : prof g n Ls y a z = true) : (mlab g n β b Ls a a' z).length = mcap g n β b Ls y a a' := by
  unfold mlab mcap
  rw [encLen hLen β b h0 (fun i => str g n Ls a a' i z)]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  rw [(prof_iff.1 hz).2 a' ha' hne i (List.mem_range.1 hi), length_str]

/-- The interaction of two nodes whose states have the profile is 1 if their strings agree in every
layer, and 0 otherwise. -/
theorem Ψ_eq (hLen : StEncLen) (hCat : StEncInj) (h0 : 0 < b) (hb : b ≤ 2 ^ β) {a a' : Fin g} (hne : a ≠ a') {z z' : List Bool}
    (hz : prof g n Ls y a z = true) :
    (markN g (ctx g n β b Ls y)).Ψ a a' z z' =
      if ∀ i < Ls.length, str g n Ls a a' i z = str g n Ls a' a i z' then 1 else 0 := by
  unfold Network.Ψ
  rw [markN_lab]
  simp only [markN_f]
  rw [sum_words_eq]
  have hl := length_mlab (β := β) hLen h0 a'.2 (fun h => hne (Fin.ext h.symm)) hz
  refine if_congr ⟨fun h i hi => ?_, fun h => ⟨?_, hl⟩⟩ rfl rfl
  · exact encCat hCat β b h0 hb (fun i => str g n Ls a a' i z) (fun i => str g n Ls a' a i z') (List.range Ls.length)
      (fun i _ => by rw [length_str, length_str, tst_comm]) h.1 i (List.mem_range.2 hi)
  · unfold mlab
    exact List.flatMap_congr fun i hi => by rw [h i (List.mem_range.1 hi)]

/-! ### The quantities of the profile at the state of (σ, P) -/

/-- The length of a filtered list without repetitions is the number of elements of the set that it
lists. -/
theorem length_filter_eq_card {l : List ℕ} (hl : l.Nodup) (p : ℕ → Bool) (S : Finset ℕ) (h : ∀ e, (e ∈ l ∧ p e = true) ↔ e ∈ S) :
    (l.filter p).length = S.card := by
  rw [← List.toFinset_card_of_nodup (hl.filter p)]
  congr 1
  ext e
  rw [List.mem_toFinset, List.mem_filter]
  exact h e

theorem str_st (σ : ℕ → Bool) (P : Finset ℕ) (a a' i : ℕ) :
    str g n Ls a a' i (st g n Ls σ P a) = (tst g n Ls a a' i).map fun e => decide (e ∈ P) := by
  unfold str
  exact List.map_congr_left fun e he => mark_st σ P (mem_tch_of_mem_tst he)

theorem count_str_st (σ : ℕ → Bool) (P : Finset ℕ) (a a' i : ℕ) :
    (str g n Ls a a' i (st g n Ls σ P a)).count true = pw g n Ls P a a' i := by
  rw [str_st, List.count, List.countP_map, List.countP_eq_length_filter]
  refine length_filter_eq_card (nodup_tst a a' i) _ _ fun e => ?_
  simp [and_comm]

theorem ownC_st (σ : ℕ → Bool) {P : Finset ℕ} (hP : P ⊆ Finset.range (cls Ls).length) (a i : ℕ) :
    ownC g n Ls a i (st g n Ls σ P a) = oc g n Ls P a i := by
  refine length_filter_eq_card (nodup_tch a) _ _ fun e => ?_
  simp only [Bool.and_eq_true, beq_iff_eq, Finset.mem_filter]
  constructor
  · rintro ⟨he, ⟨h1, h2⟩, h3⟩
    rw [mark_st σ P he] at h3
    exact ⟨by simpa using h3, h1, h2⟩
  · rintro ⟨h3, h1, h2⟩
    have he : e ∈ tch g n Ls a := mem_tch.2 ⟨Finset.mem_range.1 (hP h3), (ownB_iff.1 h2).1⟩
    refine ⟨he, ⟨h1, h2⟩, ?_⟩
    rw [mark_st σ P he]
    simpa using h3

theorem sgE_st (σ : ℕ → Bool) {P : Finset ℕ} (hP : P ⊆ Finset.range (cls Ls).length) (a : ℕ) :
    sgE g n Ls a (st g n Ls σ P a) = (P.filter fun e => 1 ≤ (clAt Ls e).1 ∧ ownB g n Ls e a = true).card := by
  refine length_filter_eq_card (nodup_tch a) _ _ fun e => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.mem_filter]
  constructor
  · rintro ⟨he, ⟨h1, h2⟩, h3⟩
    rw [mark_st σ P he] at h3
    exact ⟨by simpa using h3, h1, h2⟩
  · rintro ⟨h3, h1, h2⟩
    have he : e ∈ tch g n Ls a := mem_tch.2 ⟨Finset.mem_range.1 (hP h3), (ownB_iff.1 h2).1⟩
    refine ⟨he, ⟨h1, h2⟩, ?_⟩
    rw [mark_st σ P he]
    simpa using h3

/-- The states of (σ, P) have the profile y exactly if P has it. -/
theorem prof_st_iff (σ : ℕ → Bool) {P : Finset ℕ} (hP : P ⊆ Finset.range (cls Ls).length) :
    (∀ a : Fin g, prof g n Ls y a (st g n Ls σ P a) = true) ↔ Match g n Ls y P := by
  simp only [prof_iff, ownC_st σ hP, count_str_st]
  constructor
  · intro h i hi a ha
    exact ⟨(h ⟨a, ha⟩).1 i hi, fun b hb hne => (h ⟨a, ha⟩).2 b hb hne i hi⟩
  · intro h a
    exact ⟨fun i hi => (h i hi a a.2).1, fun b hb hne i hi => (h i hi a a.2).2 b hb hne⟩

/-! ### Every clause has one owner -/

/-- The layer of a clause of the list of all clauses is below the number of layers. -/
theorem layer_lt (Ls : List Fml) {e : ℕ} (he : e < (cls Ls).length) : (clAt Ls e).1 < Ls.length := by
  have hm : clAt Ls e ∈ cls Ls := by
    rw [clAt, List.getD_eq_getElem _ _ he]
    exact List.getElem_mem he
  obtain ⟨i, hi, hq⟩ := List.mem_flatMap.1 hm
  obtain ⟨C, -, hC⟩ := List.mem_map.1 hq
  rw [← hC]
  exact List.mem_range.1 hi

/-- A clause of the list of all clauses is a clause of some layer. -/
theorem clAt_mem {e : ℕ} (he : e < (cls Ls).length) : ∃ L ∈ Ls, (clAt Ls e).2 ∈ L := by
  have hm : clAt Ls e ∈ cls Ls := by
    rw [clAt, List.getD_eq_getElem _ _ he]
    exact List.getElem_mem he
  obtain ⟨i, hi, hq⟩ := List.mem_flatMap.1 hm
  obtain ⟨C, hC, hCe⟩ := List.mem_map.1 hq
  have hi := List.mem_range.1 hi
  rw [List.getD_eq_getElem _ _ hi] at hC
  exact ⟨Ls[i], List.getElem_mem hi, by rw [← hCe]; exact hC⟩

/-- The home of a variable below n is a node below g. -/
theorem div_qv_lt (hg : 0 < g) {x : ℕ} (hx : x < n) : x / qv g n < g := by
  have h1 := Nat.div_add_mod (n + g - 1) g
  have h2 := Nat.mod_lt (n + g - 1) hg
  unfold qv
  generalize (n + g - 1) / g = q at h1 ⊢
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · simp at h1; omega
    · exact h
  rw [Nat.div_lt_iff_lt_mul hq]
  omega

/-- A node that a clause touches is below g. -/
theorem tch_lt (hg : 0 < g) (hW : WfL k n Ls) {e a : ℕ} (he : e < (cls Ls).length) (h : tchB g n Ls a e = true) : a < g := by
  obtain ⟨l, hl, rfl⟩ := tchB_iff.1 h
  obtain ⟨L, hL, hC⟩ := clAt_mem he
  exact div_qv_lt hg ((hW L hL _ hC).2.2 l hl)

/-- Every clause has an owner. -/
theorem exists_owner (hg : 0 < g) (hW : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) : ∃ a < g, ownB g n Ls e a = true := by
  obtain ⟨L, hL, hC⟩ := clAt_mem he
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ (hW L hL _ hC).1
  have hex : ∃ a, tchB g n Ls a e = true := ⟨_, tchB_iff.2 ⟨l, hl, rfl⟩⟩
  classical
  refine ⟨Nat.find hex, tch_lt hg hW he (Nat.find_spec hex), ownB_iff.2 ⟨Nat.find_spec hex, fun c _ hc => ?_⟩⟩
  simpa using Nat.find_min hex hc

/-- A clause has at most one owner. -/
theorem owner_unique {e a a' : ℕ} (ha : a < g) (ha' : a' < g) (h : ownB g n Ls e a = true) (h' : ownB g n Ls e a' = true) : a = a' := by
  obtain ⟨h1, h2⟩ := ownB_iff.1 h
  obtain ⟨h3, h4⟩ := ownB_iff.1 h'
  rcases Nat.lt_trichotomy a a' with hlt | heq | hgt
  · rw [h4 a ha hlt] at h1; exact absurd h1 (by simp)
  · exact heq
  · rw [h2 a' ha' hgt] at h3; exact absurd h3 (by simp)

/-- Counting the clauses of P with a property p owner by owner counts each once. -/
theorem sum_owner (hg : 0 < g) (hW : WfL k n Ls) {P : Finset ℕ} (hP : P ⊆ Finset.range (cls Ls).length) (p : ℕ → Prop) [DecidablePred p] :
    ∑ a ∈ Finset.range g, (P.filter fun e => p e ∧ ownB g n Ls e a = true).card = (P.filter p).card := by
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

/-- The signs of the nodes at the states of (σ, P) multiply to the sign of P. -/
theorem prod_sign_st (hg : 0 < g) (hw : WfL k n Ls) (σ : ℕ → Bool) {P : Finset ℕ}
    (hP : P ⊆ Finset.range (cls Ls).length) :
    ∏ a : Fin g, (-1 : ℤ) ^ sgE g n Ls a (st g n Ls σ P a) = sgnP Ls P := by
  rw [Finset.prod_pow_eq_pow_sum, sgnP]
  congr 1
  simp only [sgE_st σ hP]
  rw [Fin.sum_univ_eq_sum_range (fun a => (P.filter fun e => 1 ≤ (clAt Ls e).1 ∧ ownB g n Ls e a = true).card) g]
  exact sum_owner hg hw hP _

/-! ### Good states are the states of the pairs (σ, P) -/

theorem base_iff {a : ℕ} {z : List Bool} : base g n Ls a z = true ↔
    (∀ r < qv g n, a * qv g n + r < n ∨ z.getD r false = false) ∧
      ∀ e ∈ tch g n Ls a, mark g n Ls a z e = false ∨
        ∀ l ∈ (clAt Ls e).2, l.1 / qv g n ≠ a ∨ z.getD (l.1 % qv g n) false ≠ l.2 := by
  simp only [base, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    bne_iff_ne, ne_eq, beq_eq_false_iff_ne]

theorem vio_iff {σ : ℕ → Bool} {C : Cl} : vio σ C = true ↔ ∀ l ∈ C, σ l.1 ≠ l.2 := by
  simp only [vio, List.all_eq_true, bne_iff_ne, ne_eq]

/-- All weights without the profile are nonzero and all strings agree. -/
def Gd (g n : ℕ) (Ls : List Fml) (z : Fin g → List Bool) : Prop :=
  (∀ a : Fin g, base g n Ls a (z a) = true) ∧
    ∀ a a' : Fin g, a < a' → ∀ i < Ls.length, str g n Ls a a' i (z a) = str g n Ls a' a i (z a')

theorem qv_pos (hg : 0 < g) (hn : 0 < n) : 0 < qv g n := Nat.div_pos (by omega) hg

theorem lit_lt (hw : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) {l : ℕ × Bool} (hl : l ∈ (clAt Ls e).2) : l.1 < n := by
  obtain ⟨L, hL, hC⟩ := clAt_mem he
  exact (hw L hL _ hC).2.2 l hl

theorem exists_lit (hw : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) : ∃ l, l ∈ (clAt Ls e).2 := by
  obtain ⟨L, hL, hC⟩ := clAt_mem he
  exact List.exists_mem_of_ne_nil _ (hw L hL _ hC).1

/-- The states of (σ, P) are good if σ violates all clauses of P. -/
theorem st_good (hg : 0 < g) (hw : WfL k n Ls) {σ : ℕ → Bool} (hσ : ∀ x, n ≤ x → σ x = false) {P : Finset ℕ}
    (hP : P ⊆ vset σ Ls) : Gd g n Ls fun a => st g n Ls σ P a := by
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

theorem ext_of_lt {σ : Fin n → Bool} {x : ℕ} (h : x < n) : ext σ x = σ ⟨x, h⟩ := by simp [ext, h]

theorem ext_of_le {σ : Fin n → Bool} {x : ℕ} (h : n ≤ x) : ext σ x = false := by simp [ext, not_lt.2 h]

/-- The states determine σ and P. -/
theorem st_inj (hg : 0 < g) (hw : WfL k n Ls) {σ σ' : Fin n → Bool} {P P' : Finset ℕ}
    (hP : P ⊆ Finset.range (cls Ls).length) (hP' : P' ⊆ Finset.range (cls Ls).length)
    (h : (fun a : Fin g => st g n Ls (ext σ) P a) = fun a : Fin g => st g n Ls (ext σ') P' a) : σ = σ' ∧ P = P' := by
  constructor
  · funext x
    have hq : 0 < qv g n := qv_pos hg (by have := x.2; omega)
    have h1 := congrFun h ⟨x.1 / qv g n, div_qv_lt hg x.2⟩
    have h2 := congrArg (fun l => l.getD (x.1 % qv g n) false) h1
    simp only [getD_st_lt _ _ _ (Nat.mod_lt _ hq), Nat.div_add_mod'] at h2
    rwa [ext_of_lt x.2, ext_of_lt x.2] at h2
  · ext e
    by_cases he : e < (cls Ls).length
    · obtain ⟨l, hl⟩ := exists_lit hw he
      have hlt := lit_lt hw he hl
      have ht : e ∈ tch g n Ls (l.1 / qv g n) := mem_tch.2 ⟨he, tchB_iff.2 ⟨l, hl, rfl⟩⟩
      have h1 := congrFun h ⟨l.1 / qv g n, div_qv_lt hg hlt⟩
      have h2 := congrArg (fun z => mark g n Ls (l.1 / qv g n) z e) h1
      simp only [mark_st _ _ ht] at h2
      simpa using h2
    · exact ⟨fun h => absurd (Finset.mem_range.1 (hP h)) he, fun h => absurd (Finset.mem_range.1 (hP' h)) he⟩

/-- In a good state all marks of a clause agree. -/
theorem mark_eq {z : Fin g → List Bool} (hz : Gd g n Ls z) {e : ℕ} (he : e < (cls Ls).length) {a a' : Fin g}
    (ha : tchB g n Ls a e = true) (ha' : tchB g n Ls a' e = true) : mark g n Ls a (z a) e = mark g n Ls a' (z a') e := by
  refine SatNet.eq_of_consec (ι := Fin g) (V := Unit) (idx := fun a => a.val)
    (lab := fun a => if tchB g n Ls a e = true then some () else none) Fin.val_injective
    (z := fun a => mark g n Ls a (z a) e) ?_ (p := a) (q := a') (by simp [ha]) (by simp [ha, ha'])
  rintro p q ⟨h1, h2, h3, h4⟩
  have hp : tchB g n Ls p e = true := by
    by_contra h
    simp [h] at h2
  have hq : tchB g n Ls q e = true := by
    by_contra h
    simp [hp, h] at h3
  have hl : linkB g n Ls e p q = true := linkB_iff.2 ⟨h1, hp, hq, fun c hcg h5 h6 => by
    have h7 := h4 ⟨c, hcg⟩ h5 h6
    by_contra h
    simp only [Bool.not_eq_false] at h
    simp [hp, h] at h7⟩
  have hpq : p.val ≤ q.val := le_of_lt h1
  have hm : e ∈ tst g n Ls p q (clAt Ls e).1 := mem_tst.2 ⟨he, rfl, by rwa [min_eq_left hpq, max_eq_right hpq]⟩
  have hs := hz.2 p q h1 _ (layer_lt Ls he)
  unfold str at hs
  rw [tst_comm q p] at hs
  exact List.map_inj_left.1 hs e hm

/-- Two words of the same length with the same bits are equal. -/
theorem ext_getD {l l' : List Bool} (hl : l.length = l'.length) (h : ∀ j < l.length, l.getD j false = l'.getD j false) : l = l' := by
  apply List.ext_getElem hl
  intro j h1 h2
  have := h j h1
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

theorem getD_st_ge (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) {t : ℕ} (h : t < (tch g n Ls a).length) :
    (st g n Ls σ P a).getD (qv g n + t) false = decide ((tch g n Ls a)[t] ∈ P) := by
  unfold st
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, h]

theorem mark_getElem (a : ℕ) (z : List Bool) {t : ℕ} (h : t < (tch g n Ls a).length) :
    mark g n Ls a z (tch g n Ls a)[t] = z.getD (qv g n + t) false := by
  unfold mark
  rw [(nodup_tch a).idxOf_getElem]

/-- Every good family of states is the family of the states of some (σ, P). -/
theorem st_surj (hg : 0 < g) (hw : WfL k n Ls) {z : Fin g → List Bool}
    (hlen : ∀ a, (z a).length = qv g n + (tch g n Ls a).length) (hz : Gd g n Ls z) :
    ∃ (σ : Fin n → Bool) (P : Finset ℕ), P ⊆ vset (ext σ) Ls ∧ (fun a : Fin g => st g n Ls (ext σ) P a) = z := by
  classical
  let σ : Fin n → Bool := fun x => (z ⟨x.1 / qv g n, div_qv_lt hg x.2⟩).getD (x.1 % qv g n) false
  let P : Finset ℕ := (Finset.range (cls Ls).length).filter fun e => ∃ a : Fin g, tchB g n Ls a e = true ∧ mark g n Ls a (z a) e = true
  have key : ∀ (a : Fin g) (e : ℕ), e ∈ tch g n Ls a → decide (e ∈ P) = mark g n Ls a (z a) e := by
    intro a e he
    obtain ⟨he1, he2⟩ := mem_tch.1 he
    by_cases hm : mark g n Ls a (z a) e = true
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
    have ht : tchB g n Ls (l.1 / qv g n) e = true := tchB_iff.2 ⟨l, hl, rfl⟩
    have hm : mark g n Ls (l.1 / qv g n) (z ⟨l.1 / qv g n, div_qv_lt hg hlt⟩) e = true := by
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
      have ht : t < (tch g n Ls a).length := by omega
      rw [getD_st_ge _ _ _ ht, key a _ (List.getElem_mem ht), mark_getElem _ _ ht]

/-- A sum over the good states is a sum over the pairs (σ, P). -/
theorem sum_good (hg : 0 < g) (hw : WfL k n Ls) (F : (Fin g → List Bool) → ℤ) :
    (∑ z ∈ Fintype.piFinset fun a : Fin g => words (qv g n + (tch g n Ls a).length),
      by classical exact if Gd g n Ls z then F z else 0) =
      ∑ σ : Fin n → Bool, ∑ P ∈ (vset (ext σ) Ls).powerset, F fun a => st g n Ls (ext σ) P a := by
  classical
  rw [← Finset.sum_filter, Finset.sum_sigma']
  symm
  have hsub : ∀ σ : ℕ → Bool, vset σ Ls ⊆ Finset.range (cls Ls).length := fun σ => Finset.filter_subset _ _
  refine Finset.sum_nbij (fun x => fun a : Fin g => st g n Ls (ext x.1) x.2 a) ?_ ?_ ?_ fun _ _ => rfl
  · rintro ⟨σ, P⟩ hx
    have hP : P ⊆ vset (ext σ) Ls := Finset.mem_powerset.1 (Finset.mem_sigma.1 hx).2
    exact Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun a => mem_words.2 (length_st _ _ _),
      st_good hg hw (fun x hx => ext_of_le hx) hP⟩
  · rintro ⟨σ, P⟩ hx ⟨σ', P'⟩ hx' h
    have hP : P ⊆ vset (ext σ) Ls := Finset.mem_powerset.1 (Finset.mem_sigma.1 (Finset.mem_coe.1 hx)).2
    have hP' : P' ⊆ vset (ext σ') Ls := Finset.mem_powerset.1 (Finset.mem_sigma.1 (Finset.mem_coe.1 hx')).2
    obtain ⟨h1, h2⟩ := st_inj hg hw (hP.trans (hsub _)) (hP'.trans (hsub _)) h
    subst h1; subst h2; rfl
  · intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hz)
    obtain ⟨σ, P, hP, hzz⟩ := st_surj hg hw (fun a => mem_words.1 (Fintype.mem_piFinset.1 h1 a)) h2
    exact ⟨⟨σ, P⟩, Finset.mem_coe.2 (Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_powerset.2 hP⟩), hzz⟩

/-! ### The value of the network of one profile -/

/-- One term of the value: the product of the signs at a good family of states with the profile, and
0 elsewhere. -/
theorem term_eq (hLen : StEncLen) (hCat : StEncInj) (h0 : 0 < b) (hb : b ≤ 2 ^ β) (z : Fin g → List Bool) :
    (∏ a, (markN g (ctx g n β b Ls y)).W a (z a)) *
        ∏ p ∈ pairs (Fin g), (markN g (ctx g n β b Ls y)).Ψ p.1 p.2 (z p.1) (z p.2) =
      by classical exact if Gd g n Ls z then
        (if ∀ a : Fin g, prof g n Ls y a (z a) = true then ∏ a : Fin g, (-1 : ℤ) ^ sgE g n Ls a (z a) else 0) else 0 := by
  classical
  simp only [markN_W, mW_eq]
  by_cases hp : ∀ a : Fin g, (base g n Ls a (z a) && prof g n Ls y a (z a)) = true
  · have hb1 : ∀ a : Fin g, base g n Ls a (z a) = true := fun a => (Bool.and_eq_true _ _ ▸ hp a).1
    have hp1 : ∀ a : Fin g, prof g n Ls y a (z a) = true := fun a => (Bool.and_eq_true _ _ ▸ hp a).2
    have hΨ : ∀ p ∈ pairs (Fin g), (markN g (ctx g n β b Ls y)).Ψ p.1 p.2 (z p.1) (z p.2) =
        if ∀ i < Ls.length, str g n Ls p.1 p.2 i (z p.1) = str g n Ls p.2 p.1 i (z p.2) then 1 else 0 :=
      fun p hpp => Ψ_eq hLen hCat h0 hb (ne_of_lt (Finset.mem_filter.1 hpp).2) (hp1 p.1)
    have hPs : ∏ p ∈ pairs (Fin g), (markN g (ctx g n β b Ls y)).Ψ p.1 p.2 (z p.1) (z p.2) =
        if ∀ p ∈ pairs (Fin g), ∀ i < Ls.length, str g n Ls p.1 p.2 i (z p.1) = str g n Ls p.2 p.1 i (z p.2) then 1 else 0 := by
      rw [Finset.prod_congr rfl hΨ, Finset.prod_ite_zero, Finset.prod_const_one]
      split_ifs <;> simp_all
    rw [hPs, Finset.prod_congr rfl fun a _ => if_pos (hp a), if_pos hp1]
    by_cases hG : Gd g n Ls z
    · have hall : ∀ p ∈ pairs (Fin g), ∀ i < Ls.length, str g n Ls p.1 p.2 i (z p.1) = str g n Ls p.2 p.1 i (z p.2) :=
        fun p hpp => hG.2 p.1 p.2 (Finset.mem_filter.1 hpp).2
      rw [if_pos hG, if_pos hall, mul_one]
    · rw [if_neg hG, if_neg, mul_zero]
      intro h
      exact hG ⟨hb1, fun a a' haa => h (a, a') (Finset.mem_filter.2 ⟨Finset.mem_univ _, haa⟩)⟩
  · obtain ⟨a, ha⟩ := not_forall.1 hp
    rw [Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha), zero_mul]
    by_cases hG : Gd g n Ls z
    · rw [if_pos hG, if_neg]
      intro h
      exact ha (by rw [hG.1 a, h a]; rfl)
    · rw [if_neg hG]

/-- The value of the network of the profile y: the signed number of pairs (σ, P), P a set of clauses
that σ violates, with that profile. -/
theorem markVal (hLen : StEncLen) (hCat : StEncInj) (hg : 0 < g) (h0 : 0 < b) (hb : b ≤ 2 ^ β) (hw : WfL k n Ls)
    :
    (markN g (ctx g n β b Ls y)).value =
      ∑ σ : Fin n → Bool, ∑ P ∈ (vset (ext σ) Ls).powerset, by classical exact if Match g n Ls y P then sgnP Ls P else 0 := by
  classical
  unfold Network.value
  simp only [term_eq hLen hCat h0 hb]
  have hS : (Fintype.piFinset (markN g (ctx g n β b Ls y)).S) =
      Fintype.piFinset fun a : Fin g => words (qv g n + (tch g n Ls a).length) := by
    congr 1
    funext a
    exact markN_S a
  rw [hS]
  have := sum_good hg hw (fun z => if ∀ a : Fin g, prof g n Ls y a (z a) = true then ∏ a : Fin g, (-1 : ℤ) ^ sgE g n Ls a (z a) else 0)
  refine Eq.trans ?_ (this.trans ?_)
  · exact Finset.sum_congr rfl fun z _ => by congr
  · refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun P hP => ?_
    have hP' : P ⊆ Finset.range (cls Ls).length := (Finset.mem_powerset.1 hP).trans (Finset.filter_subset _ _)
    rw [prod_sign_st hg hw _ hP']
    exact if_congr (prof_st_iff _ hP') rfl rfl


/-- A number in unary is the list of that many units. -/
theorem eq_replicate (u : U) : u = List.replicate u.length () := List.eq_replicate_iff.2 ⟨rfl, fun _ _ => rfl⟩

/-- The value of the network of one profile, admissible or not. -/
public theorem stMarkVal (hLen : StEncLen) (hCat : StEncInj) : StMarkVal := by
  intro k gu nu βu bu Ls y hg h0 hb hw
  have e : (((gu, nu, βu, bu), (Ls, y)) : MCtx) = ctx gu.length nu.length βu.length bu.length Ls y := by
    rw [ctx, ← eq_replicate, ← eq_replicate, ← eq_replicate, ← eq_replicate]
  rw [e]
  exact markVal hLen hCat hg h0 hb hw

/-- The plain functions markF present the network markN. -/
public theorem stMarkPresents : StMarkPresents := fun c =>
  { S_eq := fun _ => rfl
    c_eq := fun _ _ _ => rfl
    lab_eq := fun a b _ => by
      rcases le_total a b with h | h
      · simp only [Network.lab, markN, min_eq_left h, max_eq_right h]; rfl
      · simp only [Network.lab, markN, min_eq_right h, max_eq_left h]
        exact congrArg words (mcap_comm _ _)
    W_runs := fun _ _ _ => Stepped.Reaches.halt rfl (Nat.le_refl 0)
    f_runs := fun _ _ _ _ _ _ _ => Stepped.Reaches.halt rfl (Nat.le_refl 0) }

end PaddedDescent.F.Mark.Val
