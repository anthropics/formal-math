/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfIfc
public import StepMachines.Prog.Chunks

/-! # The pieces with ρ = 1/√2 as programs: the labels of the factorizations

A label θ of a factorization is read as a number and stands for the pair (j, τ) with that number in
the list `labs T tr h s`. Here: a sum over all words θ of c bits of a product of two
functions of the entry number θ of a list is the sum over the list, if the list has at most 2^c
entries (`sum_words_getElem`); for the table T of all partitions of 0, …, 4h and |s| ≤ 2h, the list
of the
pairs has Σ_j p(s + j) entries row-wise and Σ_j p(2h − s − j) column-wise (`length_labs`); a sum
over it is the double sum over j ≤ 2h and over the partitions τ of the weight that belongs to j
(`sum_map_labs`); and the partitions in it are listed in the flattened table
(`mem_flatten_of_mem_labs`). The theorems `stWords` and `stLabs` put this in the form of the
interface lemmas `StWords` and `StLabs`. -/

public section

namespace ClauseBound.Inst.Half

open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions

/-! ### Sums over lists -/

namespace Labs

/-- A sum over the positions of a list, continued by zeros. -/
theorem sum_range_getElem {β : Type} (F : β → ℤ) (L : List β) : ∀ M, L.length ≤ M → ∑ j ∈ range M, (L[j]?).elim 0 F = (L.map F).sum := by
  induction L with
  | nil => intro M _; simp
  | cons a L ih =>
    intro M hM
    obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by simp at hM; omega⟩
    rw [sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.elim_some, List.map_cons, List.sum_cons]
    rw [ih M (by simpa using hM), add_comm]

end Labs

open Labs

/-- A sum over all words θ of c bits of the product of two functions of the entry number θ of a list
with at most 2^c entries is the sum over the list. -/
theorem sum_words_getElem {β : Type} (L : List β) (c : ℕ) (hL : L.length ≤ 2 ^ c) (f g : β → ℤ) :
    ∑ θ ∈ words c, (L[ofWord θ]?).elim 0 f * (L[ofWord θ]?).elim 0 g = (L.map fun b => f b * g b).sum := by
  rw [← sum_toWord c fun θ => (L[ofWord θ]?).elim 0 f * (L[ofWord θ]?).elim 0 g, ← sum_range_getElem _ L _ hL]
  refine sum_congr rfl fun j hj => ?_
  rw [ofWord_toWord (mem_range.1 hj)]
  cases L[j]? <;> simp

namespace Labs

/-- The sum of the values F 0, …, F (n − 1), written with a list. -/
theorem sum_map_range_int (F : ℕ → ℤ) (n : ℕ) : ((List.range n).map F).sum = ∑ j ∈ range n, F j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The sum of z over w.flatMap e is the sum, over the members a of w, of the sums of z over e a. -/
theorem sum_map_flatMap {α β : Type} (w : List α) (e : α → List β) (z : β → ℤ) :
    ((w.flatMap e).map z).sum = (w.map fun a => ((e a).map z).sum).sum := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [List.flatMap_cons, ih]

/-- A member of an entry of a table is a member of the flattened table. -/
theorem mem_flatten_of_mem_getD {γ : Type} {T : List (List γ)} {i : ℕ} {L : γ} (h : L ∈ T.getD i []) : L ∈ T.flatten := by
  by_cases hi : i < T.length
  · rw [List.getD_eq_getElem _ _ hi] at h
    exact List.mem_flatten.2 ⟨_, List.getElem_mem hi, h⟩
  · rw [List.getD_eq_default _ _ (not_lt.1 hi)] at h
    cases h

end Labs

/-! ### The weights -/

/-- The weight of τ in a pair (j, τ) with j ≤ 2h is at most 4h if |s| ≤ 2h. -/
theorem wOf_le {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) (tr : Bool) {j : ℕ} (hj : j ≤ 2 * h) : wOf tr h s j ≤ 4 * h := by
  obtain ⟨h1, h2⟩ := abs_le.1 hs
  cases tr <;> simp only [wOf, cond_true, cond_false] <;> omega

theorem toNat_wOf_le {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) (tr : Bool) {j : ℕ} (hj : j ≤ 2 * h) : (wOf tr h s j).toNat ≤ 4 * h := by
  have := wOf_le hs tr hj
  omega

/-! ### The list of the labels -/

/-- What it means to be in the list of the pairs (j, τ). -/
theorem mem_labs {T : PT} {tr : Bool} {h : ℕ} {s : ℤ} {p : ℕ × List ℕ} :
    p ∈ labs T tr h s ↔ p.1 ≤ 2 * h ∧ 0 ≤ wOf tr h s p.1 ∧ p.2 ∈ T.getD (wOf tr h s p.1).toNat [] := by
  obtain ⟨j, τ⟩ := p
  simp only [labs, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, hp⟩
    split_ifs at hp with hw
    · obtain ⟨τ', hτ', he⟩ := List.mem_map.1 hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨by omega, hw, hτ'⟩
    · cases hp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨j, by omega, ?_⟩
    rw [if_pos h2]
    exact List.mem_map.2 ⟨τ, h3, rfl⟩

/-- The partition of a label is listed in the flattened table, and its number j is at most 2h. -/
theorem mem_flatten_of_mem_labs {T : PT} {tr : Bool} {h : ℕ} {s : ℤ} {p : ℕ × List ℕ} (hp : p ∈ labs T tr h s) : p.2 ∈ T.flatten ∧ p.1 ≤ 2 * h :=
  ⟨mem_flatten_of_mem_getD (mem_labs.1 hp).2.2, (mem_labs.1 hp).1⟩

/-- The number of labels is the number of terms of the expansion: Σ_j p(s + j) row-wise and Σ_j p(2h
− s − j) column-wise. -/
theorem length_labs {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) (tr : Bool) :
    (labs (allTab (4 * h)) tr h s).length = bif tr then Rcol h s else Rrow h s := by
  have h1 : (labs (allTab (4 * h)) tr h s).length = ∑ j ∈ range (2 * h + 1), pz (wOf tr h s j) := by
    rw [labs, List.length_flatMap, ← sum_map_range]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    have hj' : j ≤ 2 * h := by have := List.mem_range.1 hj; omega
    rw [pz]
    split_ifs with hw
    · rw [List.length_map, length_allTab_getD (toNat_wOf_le hs tr hj')]
    · rfl
  rw [h1]
  cases tr <;> rfl

/-- A sum over the list of the labels is the double sum of the expansion. -/
theorem sum_map_labs {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) (tr : Bool) (G : ℕ → Multiset ℕ → ℤ) :
    ((labs (allTab (4 * h)) tr h s).map fun p => G p.1 (p.2 : Multiset ℕ)).sum
      = ∑ j ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (wOf tr h s j), G j τ := by
  rw [labs, sum_map_flatMap, ← sum_map_range_int]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have hj' : j ≤ 2 * h := by have := List.mem_range.1 hj; omega
  rw [ClauseBound.Boson.Pz]
  split_ifs with hw
  · have hW := toNat_wOf_le hs tr hj'
    rw [← toFinset_map_coe_allTab_getD hW, List.sum_toFinset _ (nodup_map_coe_allTab_getD hW), List.map_map, List.map_map]
    rfl
  · simp

/-! ### The interface lemmas -/

/-- A sum over all words of c bits of a product of two functions of the entry of a list with at most
2^c entries is the sum over the list. -/
theorem stWords : StWords := fun _ L c f g hL => sum_words_getElem L c hL f g

/-- The list of the labels: its length, sums over it, its members. -/
theorem stLabs : StLabs := fun tr _ _ hs =>
  ⟨length_labs hs tr, sum_map_labs hs tr, fun _ hp => mem_flatten_of_mem_labs hp⟩

end ClauseBound.Inst.Half
