/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Part.ListP
public import ClauseBound.Part.Bits
public import ClauseBound.Boson.Basic
public import PaddedDescent.F.Fuel

/-! # The numbers of partitions and the table of all partitions, as programs

Without a pad: `pTab W` is the list p(0), …, p(W), computed one entry at a time by the recurrence
E·p(E) = Σ_{v ≥ 1} Σ_{k ≥ 1, kv ≤ E} v·p(E − kv) (`pTab_getD`). From it: `hF c₀ lam`, the first
E in 2 … c₀·lam² with p(E) ≥ 2^lam, which is `ClauseBound.Part.hOf lam` if that number is at most
c₀·lam² (`hF_eq`), and the sums `RrowF`, `RcolF` (`RrowF_eq`, `RcolF_eq`).
The table of all partitions of 0, …, W: `allTab W` is a list whose entry number E is the list of the
partitions of E as nonincreasing lists of positive integers (`allTab_getD`). It is built in
rounds k = 1, …, W; round k runs through E = 0, …, W and appends to entry E the lists k :: L for L
in the new entry E − k. `allTabF pad W` does the same with every state cut off by the pad; it is
equal to `allTab W` if the pad has length at least (7W + 10)·Σ_{E ≤ W} p(E) (`allTabF_eq`). -/

@[expose] public section

namespace ClauseBound.Inst.Half

open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset

/-! ### Definitions -/

/-- From the list T = p(0), …, p(N − 1) of length N: the number (Σ_{v=1}^{N} Σ_{k=1}^{N/v} v·T[N −
kv]) / N, which is p(N). -/
def nextP (T : List ℕ) : ℕ :=
  ((List.range T.length).map fun v =>
    ((List.range (T.length / (v + 1))).map fun k => (v + 1) * T.getD (T.length - (k + 1) * (v + 1)) 0).sum).sum / T.length

/-- The list p(0), …, p(W). -/
def pTab (W : ℕ) : List ℕ := (List.range W).foldl (fun T _ => T ++ [nextP T]) [1]

/-- The entry number E of a table of numbers, for an integer E; 0 for E < 0. -/
def pzF (T : List ℕ) (E : ℤ) : ℕ := if 0 ≤ E then T.getD E.toNat 0 else 0

/-- The first E in 2 … c₀·lam² with p(E) ≥ 2^lam; 2 if there is none. -/
def hF (c₀ lam : ℕ) : ℕ :=
  ((List.range (c₀ * lam ^ 2 + 1)).find? fun E => decide (2 ≤ E) && decide (2 ^ lam ≤ (pTab (c₀ * lam ^ 2)).getD E 0)).getD 2

/-- Σ_{i=0}^{2h} p(s + i), from the table p(0), …, p(4h). -/
def RrowF (h : ℕ) (s : ℤ) : ℕ := ((List.range (2 * h + 1)).map fun i : ℕ => pzF (pTab (4 * h)) (s + i)).sum

/-- Σ_{i=0}^{2h} p(2h − s − i), from the table p(0), …, p(4h). -/
def RcolF (h : ℕ) (s : ℤ) : ℕ := ((List.range (2 * h + 1)).map fun i : ℕ => pzF (pTab (4 * h)) (2 * h - s - i)).sum

/-- A table of partitions: entry number E is a list of partitions of E, each a list of its parts. -/
abbrev PT : Type := List (List (List ℕ))

/-- The table before the first round: the empty partition of 0. -/
def initT (W : ℕ) : PT := (List.range (W + 1)).map fun E => if E = 0 then [[]] else []

/-- One step of round k: the new entry number E, appended to the new entries 0, …, E − 1. -/
def stepE (k : ℕ) (old new : PT) (E : ℕ) : PT :=
  new ++ [old.getD E [] ++ (if k ≤ E then (new.getD (E - k) []).map fun L => k :: L else [])]

/-- Round k: from the partitions into parts < k to those into parts ≤ k. -/
def roundT (W k : ℕ) (old : PT) : PT := (List.range (W + 1)).foldl (stepE k old) []

/-- The table of the partitions of 0, …, W. -/
def allTab (W : ℕ) : PT := (List.range W).foldl (fun old k => roundT W (k + 1) old) (initT W)

/-- Round k with every state cut off by the pad. -/
def roundF (pad : U) (W k : ℕ) (old : PT) : PT :=
  (List.range (W + 1)).foldl (fun new E => cap pad [] (stepE k old new E)) (cap pad [] [])

/-- The table of the partitions of 0, …, W with every state cut off by the pad. -/
def allTabF (pad : U) (W : ℕ) : PT :=
  (List.range W).foldl (fun old k => cap pad [] (roundF pad W (k + 1) old)) (cap pad [] (initT W))

/-- The table after round k. -/
def tabK (W k : ℕ) : PT := (List.range (W + 1)).map fun E => partsLe E k

/-! ### Lists over a range -/

/-- The sum of a list f 0, …, f (n − 1) as a sum over a range. -/
theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- A sum over 1, …, n as a sum over a range. -/
theorem sum_Icc_one (f : ℕ → ℕ) (n : ℕ) : ∑ v ∈ Icc 1 n, f v = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- The entry number i of the list f 0, …, f (n − 1). -/
theorem getD_map_range {γ : Type} (f : ℕ → γ) (d : γ) {n i : ℕ} (h : i < n) : ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ### The table of the numbers of partitions -/

/-- The recurrence computes p(N) from p(0), …, p(N − 1), for N ≥ 1. -/
theorem nextP_map (E : ℕ) : nextP ((List.range (E + 1)).map p) = p (E + 1) := by
  have h : ((List.range (E + 1)).map fun v => ((List.range ((E + 1) / (v + 1))).map fun k =>
      (v + 1) * ((List.range (E + 1)).map p).getD (E + 1 - (k + 1) * (v + 1)) 0).sum).sum = (E + 1) * p (E + 1) := by
    rw [mul_p_eq, sum_Icc_one, sum_map_range]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [sum_Icc_one, sum_map_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [getD_map_range p 0 (by have : 1 ≤ (k + 1) * (v + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _); omega)]
  unfold nextP
  simp only [List.length_map, List.length_range]
  rw [h, Nat.mul_div_cancel_left _ (Nat.succ_pos E)]

/-- One more entry. -/
theorem pTab_succ (W : ℕ) : pTab (W + 1) = pTab W ++ [nextP (pTab W)] := by
  simp only [pTab, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The table is the list p(0), …, p(W). -/
theorem pTab_eq (W : ℕ) : pTab W = (List.range (W + 1)).map p := by
  induction W with
  | zero => simp [pTab, p_zero]
  | succ W ih => rw [pTab_succ, ih, nextP_map, List.range_succ (n := W + 1), List.map_append]; rfl

/-- The table has W + 1 entries. -/
theorem length_pTab (W : ℕ) : (pTab W).length = W + 1 := by
  rw [pTab_eq, List.length_map, List.length_range]

/-- The entry number i ≤ W of the table is p(i). -/
theorem pTab_getD (W i : ℕ) (h : i ≤ W) : (pTab W).getD i 0 = Partitions.p i := by
  rw [pTab_eq, getD_map_range p 0 (by omega)]

/-- The entry number E ≤ W, for an integer E. -/
theorem pzF_pTab {W : ℕ} {E : ℤ} (h : E ≤ W) : pzF (pTab W) E = pz E := by
  unfold pzF pz
  split_ifs with h0
  · exact pTab_getD W _ (by omega)
  · rfl

/-- `hF` finds `hOf lam` if that number is at most c₀·lam². -/
theorem hF_eq {c₀ lam : ℕ} (h : hOf lam ≤ c₀ * lam ^ 2) : hF c₀ lam = hOf lam := by
  have hfind : ((List.range (c₀ * lam ^ 2 + 1)).find? fun E => decide (2 ≤ E) && decide (2 ^ lam ≤ (pTab (c₀ * lam ^ 2)).getD E 0)) =
      some (hOf lam) := by
    rw [List.find?_range_eq_some]
    refine ⟨?_, List.mem_range.2 (by omega), fun j hj => ?_⟩
    · rw [pTab_getD _ _ h]
      simp [two_le_hOf lam, two_pow_le_p_hOf lam]
    · rw [pTab_getD _ _ (by omega)]
      have hmin : ¬(2 ≤ j ∧ 2 ^ lam ≤ p j) := Nat.find_min (exists_h lam) hj
      simpa [-not_and, ← Bool.decide_and] using hmin
  rw [hF, hfind, Option.getD_some]

/-- `hF` is at most c₀·lam² + 2. -/
theorem hF_le (c₀ lam : ℕ) : hF c₀ lam ≤ c₀ * lam ^ 2 + 2 := by
  unfold hF
  rcases hf : (List.range (c₀ * lam ^ 2 + 1)).find? (fun E => decide (2 ≤ E) && decide (2 ^ lam ≤ (pTab (c₀ * lam ^ 2)).getD E 0)) with _ | E
  · simp
  · have := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    rw [Option.getD_some]
    omega

/-- `hF` is at least 2. -/
theorem two_le_hF (c₀ lam : ℕ) : 2 ≤ hF c₀ lam := by
  unfold hF
  rcases hf : (List.range (c₀ * lam ^ 2 + 1)).find? (fun E => decide (2 ≤ E) && decide (2 ^ lam ≤ (pTab (c₀ * lam ^ 2)).getD E 0)) with _ | E
  · simp
  · have := List.find?_some hf
    rw [Option.getD_some]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1

/-- The number Σ_{i=0}^{2h} p(s + i) of terms of the row-wise factorization of a piece, read from
the table, for s ≤ 2h. -/
theorem RrowF_eq {h : ℕ} {s : ℤ} (hs : s ≤ 2 * h) : RrowF h s = Rrow h s := by
  unfold RrowF Rrow
  rw [sum_map_range]
  refine Finset.sum_congr rfl fun i hi => pzF_pTab ?_
  have := Finset.mem_range.1 hi
  push_cast
  omega

/-- The number Σ_{i=0}^{2h} p(2h − s − i) of terms of the column-wise factorization of a piece, read
from the table, for s ≥ −2h. -/
theorem RcolF_eq {h : ℕ} {s : ℤ} (hs : -(2 * h : ℤ) ≤ s) : RcolF h s = Rcol h s := by
  unfold RcolF Rcol
  rw [sum_map_range]
  refine Finset.sum_congr rfl fun i _ => pzF_pTab ?_
  push_cast
  omega

/-! ### The table of all partitions -/

/-- Before the first round. -/
theorem initT_eq (W : ℕ) : initT W = tabK W 0 := by
  unfold initT tabK
  simp only [partsLe_zero_right]

/-- The first j steps of round k + 1. -/
theorem foldl_stepE (W k j : ℕ) (hj : j ≤ W + 1) :
    (List.range j).foldl (stepE (k + 1) (tabK W k)) [] = (List.range j).map fun E => partsLe E (k + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.map_append]
    simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, stepE]
    congr 2
    rw [partsLe_succ, tabK, getD_map_range _ _ (by omega)]
    congr 1
    split_ifs with hk
    · rw [getD_map_range _ _ (by omega)]
    · rfl

/-- Round k + 1. -/
theorem roundT_tabK (W k : ℕ) : roundT W (k + 1) (tabK W k) = tabK W (k + 1) := foldl_stepE W k (W + 1) le_rfl

/-- The first j rounds. -/
theorem foldl_roundT (W j : ℕ) : (List.range j).foldl (fun old k => roundT W (k + 1) old) (initT W) = tabK W j := by
  induction j with
  | zero => exact initT_eq W
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, ih]
    exact roundT_tabK W j

/-- The entry number E ≤ W of the table is the list of the partitions of E. -/
theorem allTab_getD {W E : ℕ} (h : E ≤ W) : (allTab W).getD E [] = partsOf E := by
  rw [allTab, foldl_roundT, tabK, getD_map_range _ _ (by omega), partsLe_of_le h]

/-- Its members are the nonincreasing lists of positive integers with sum E. -/
theorem mem_allTab_getD {W E : ℕ} (h : E ≤ W) {L : List ℕ} :
    L ∈ (allTab W).getD E [] ↔ L.sum = E ∧ (∀ n ∈ L, 1 ≤ n) ∧ L.Pairwise (· ≥ ·) := by
  rw [allTab_getD h, mem_partsOf]

/-- There are p(E) partitions of E. -/
theorem length_allTab_getD {W E : ℕ} (h : E ≤ W) : ((allTab W).getD E []).length = Partitions.p E := by
  rw [allTab_getD h, length_partsOf]

/-- As multisets they are different from each other. -/
theorem nodup_map_coe_allTab_getD {W E : ℕ} (h : E ≤ W) : (((allTab W).getD E []).map fun L : List ℕ => (L : Multiset ℕ)).Nodup := by
  rw [allTab_getD h]
  exact nodup_map_coe_partsOf E

/-- As multisets they are the monomials of weight E. -/
theorem toFinset_map_coe_allTab_getD {W E : ℕ} (h : E ≤ W) :
    (((allTab W).getD E []).map fun L : List ℕ => (L : Multiset ℕ)).toFinset = ClauseBound.Boson.P E := by
  ext τ
  rw [allTab_getD h, List.mem_toFinset, mem_map_coe_partsOf, ClauseBound.Boson.mem_P]

/-- The members of the flattened table are the nonincreasing lists of positive integers with sum at
most W. -/
theorem mem_flatten_allTab {W : ℕ} {L : List ℕ} :
    L ∈ (allTab W).flatten ↔ L.sum ≤ W ∧ (∀ n ∈ L, 1 ≤ n) ∧ L.Pairwise (· ≥ ·) := by
  rw [allTab, foldl_roundT, tabK, List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hL⟩
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hs, hp, hw⟩ := (mem_partsLe E W L).1 hL
    have := List.mem_range.1 hE
    exact ⟨by omega, fun n hn => (hp n hn).1, hw⟩
  · rintro ⟨hs, hp, hw⟩
    exact ⟨partsLe L.sum W, List.mem_map.2 ⟨L.sum, List.mem_range.2 (by omega), rfl⟩,
      (mem_partsLe _ _ _).2 ⟨rfl, fun n hn => ⟨hp n hn, (ListP.le_sum_of_mem hn).trans hs⟩, hw⟩⟩

/-! ### The lengths of the words, and the pad -/

/-- A list of n members with words of length at most c has a word of length at most n·(c + 2) + 2. -/
theorem len_le_of_forall {γ : Type} [Enc γ] {c : ℕ} (l : List γ) (h : ∀ a ∈ l, len a ≤ c) : len l ≤ l.length * (c + 2) + 2 := by
  induction l with
  | nil => simp [len_nil]
  | cons a l ih =>
    have h1 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    have h2 := h a List.mem_cons_self
    rw [len_cons, List.length_cons, Nat.succ_mul]
    omega

/-- The word of a list of positive integers with sum E has length at most 7E + 2. -/
theorem len_parts_le (L : List ℕ) (h : ∀ n ∈ L, 1 ≤ n) : len L ≤ 7 * L.sum + 2 := by
  induction L with
  | nil => simp [len_nil]
  | cons n L ih =>
    have h1 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    have h2 := h n List.mem_cons_self
    have h3 : Nat.size n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self
    rw [len_cons, len_nat, List.sum_cons]
    omega

/-- The word of the list of the partitions of E into parts ≤ k. -/
theorem len_partsLe_le (E k : ℕ) : len (partsLe E k) ≤ p E * (7 * E + 4) + 2 := by
  have h1 := len_le_of_forall (c := 7 * E + 2) (partsLe E k) fun L hL => by
    obtain ⟨hs, hp, _⟩ := (mem_partsLe E k L).1 hL
    exact hs ▸ len_parts_le L fun n hn => (hp n hn).1
  have h2 : (partsLe E k).length * (7 * E + 2 + 2) ≤ p E * (7 * E + 4) := Nat.mul_le_mul_right _ (length_partsLe_le E k)
  omega

/-- The word of the first j entries of the table after round k. -/
theorem len_map_partsLe_le (W k j : ℕ) (hj : j ≤ W + 1) :
    len ((List.range j).map fun E => partsLe E k) ≤ (7 * W + 8) * ∑ E ∈ range j, p E + 2 := by
  induction j with
  | zero => simp [len_nil]
  | succ j ih =>
    have h1 := ih (by omega)
    have h2 := len_partsLe_le j k
    have h3 : p j * (7 * j + 4) ≤ p j * (7 * W + 4) := Nat.mul_le_mul_left _ (by omega)
    have h4 := p_pos j
    have h5 := len_append ((List.range j).map fun E => partsLe E k) [partsLe j k]
    rw [len_cons, len_nil] at h5
    rw [List.range_succ, List.map_append, Finset.sum_range_succ, Nat.mul_add]
    simp only [List.map_cons, List.map_nil]
    have h6 : (7 * W + 8) * p j = p j * (7 * W + 4) + 4 * p j := by ring
    omega

/-- All states of the computation of the table have words of length at most (7W + 10)·Σ_{E ≤ W}
p(E). -/
theorem len_state_le (W k j : ℕ) (hj : j ≤ W + 1) :
    len ((List.range j).map fun E => partsLe E k) ≤ (7 * W + 10) * ∑ E ∈ range (W + 1), p E := by
  have h1 := len_map_partsLe_le W k j hj
  have h2 : ∑ E ∈ range j, p E ≤ ∑ E ∈ range (W + 1), p E :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hj)
  have h3 : 1 ≤ ∑ E ∈ range (W + 1), p E := by
    rw [Finset.sum_range_succ']
    have := p_pos 0
    omega
  have h4 : (7 * W + 8) * ∑ E ∈ range j, p E ≤ (7 * W + 8) * ∑ E ∈ range (W + 1), p E := Nat.mul_le_mul_left _ h2
  have h5 : (7 * W + 10) * ∑ E ∈ range (W + 1), p E = (7 * W + 8) * ∑ E ∈ range (W + 1), p E + 2 * ∑ E ∈ range (W + 1), p E := by ring
  omega

/-- The first j steps of round k + 1 with the pad. -/
theorem foldl_stepE_cap {pad : U} {W : ℕ} (hp : (7 * W + 10) * ∑ E ∈ range (W + 1), p E ≤ pad.length) (k j : ℕ) (hj : j ≤ W + 1) :
    (List.range j).foldl (fun new E => cap pad [] (stepE (k + 1) (tabK W k) new E)) (cap pad [] []) =
      (List.range j).map fun E => partsLe E (k + 1) := by
  induction j with
  | zero => exact cap_eq ((len_state_le W (k + 1) 0 (Nat.zero_le _)).trans hp)
  | succ j ih =>
    have h1 := foldl_stepE W k (j + 1) hj
    rw [List.range_succ, List.foldl_append, foldl_stepE W k j (by omega)] at h1
    simp only [List.foldl_cons, List.foldl_nil] at h1
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [h1, ← List.range_succ]
    exact cap_eq ((len_state_le W (k + 1) (j + 1) hj).trans hp)

/-- With a pad of length at least (7W + 10)·Σ_{E ≤ W} p(E) no cut-off is active. -/
theorem allTabF_eq {pad : U} {W : ℕ} (hp : (7 * W + 10) * ∑ E ∈ range (W + 1), p E ≤ pad.length) : allTabF pad W = allTab W := by
  have key : ∀ j, (List.range j).foldl (fun old k => cap pad [] (roundF pad W (k + 1) old)) (cap pad [] (initT W)) = tabK W j := by
    intro j
    induction j with
    | zero =>
      rw [initT_eq]
      exact cap_eq ((len_state_le W 0 (W + 1) le_rfl).trans hp)
    | succ j ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, roundF]
      rw [foldl_stepE_cap hp j (W + 1) le_rfl]
      exact cap_eq ((len_state_le W (j + 1) (W + 1) le_rfl).trans hp)
  rw [allTabF, key, allTab, foldl_roundT]

end ClauseBound.Inst.Half
