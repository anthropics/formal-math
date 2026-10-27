/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Defs
import Mathlib.Tactic

/-! # Lemma 1 along the printed proof: the tables W̃_γ

This file proves two of the steps stated in proof/networks/Eight/ViaGrouping/Defs.lean, for a
network N as in Definition 2 (except that its procedures are not given B) and a grouping, given by
its number x.
* `stTable`, the first two sentences of the paragraph «Cost»: «The sum defining W̃_γ(Θ) has at most
  (2^P)^{2g/K} = 2^{2gP/K} terms, each a product of at most g² values. So |W̃_γ| < 2^{B'} with B' =
  ⌈2gP/K⌉ + g²B, and one entry costs
  2^{2gP/K}·poly(P + B)·τ operations.» The procedure is `tableM`, which calls the four procedures of
  Definition 2(iii); in particular Ψ_{a,b} inside a group costs one call, so there is no factor 2^P.
* `stValue`, the end of the paragraph «The algorithm»: «… so the value equals Z».

The order of the file:
1. a network in the sense of `IsNetworkP` gives a network in the sense of `Paper.IsNetwork`
   (`Table.isPaperNetwork`);
2. the parts z_a and θ_{a,b} that are cut out of a setting of the group and out of Θ have the
   lengths P_a and c_{a,b} (`Table.length_zA`, `Table.length_labOf`);
3. a procedure behind the test for membership in S_a (`Table.gate_runs`), and the integers that the
   factors return (`Table.f_toPaperNetwork`, `Table.psi_toPaperNetwork`, `Table.sum_valF`);
4. one factor (`Table.termP_runs`), one entry (`Table.tableM_runs`), its size
   (`Table.abs_entry_le`), one constant for K and g (`Table.tableM_runs_coarse`);
5. `stTable` and `stValue`.

The integer that `tableM` returns is `mergedVal` (proof/machines/StepMachines/Prog/NetProg.lean) for
the network `N.toPaperNetwork`: strings outside S_a give the factor 0, and on settings the procedure
for Ψ_{a,b} returns Σ_θ f_{a,b}·f_{b,a}, because (f_{a,b}, f_{b,a}) is a factorization of Ψ_{a,b}.
So that this integer is the entry of W̃_γ, and that the clique of the groups has the value Z, are
proved elsewhere (`toInst_eq_mergedVal`, `Paper.grouped_value`).

Different from the paper: 2g/K is rounded down, which (G1) allows, since the number of nodes of a
group is an integer; entries are «at most 2^{P·⌊2g/K⌋ + g²B}», as the definition of query access in
the namespace `Paper` asks; this exponent is at most the B' = ⌈2gP/K⌉ + g²B of the paper
(`Cost.le_Bp` in Main.lean). -/

public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks

namespace Table

variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

/-! ## 1. From `IsNetworkP` to `Paper.IsNetwork` -/

omit [HasSize C] in
/-- A network in the sense of `IsNetworkP` is a network in the sense of Definition 2 once the
procedures are told B. -/
theorem isNetwork (h : IsNetworkP Np c N P B τ S) : IsNetwork { Np with B := fun _ => B } c N P B τ S :=
  ⟨h.is, h.τ_pos, ⟨h.given.P_eq, rfl, h.given.len_eq, h.given.cap_eq, h.given.mem_runs, h.given.W_runs, h.given.Ψ_runs, h.given.f_runs⟩⟩

/-- The network `N.toPaperNetwork` with the procedures `Np.toPaperNetwork` is a network in the sense
of `Paper.IsNetwork` with the same P and B. (These procedures do not depend on what is given for B.) -/
theorem isPaperNetwork (h : IsNetworkP Np c N P B τ S) :
    Paper.IsNetwork Np.toPaperNetwork c N.toPaperNetwork P B (2 * τ + 1) (S + (size c + 2 * size g + 4 * P + 6)) :=
  have hp := presents_toPaperNetwork (isNetwork h)
  ⟨Net.sized_toPaperNetwork h.is, hp⟩

omit [HasSize C] in
/-- The numbers c_{a,b} that are given are symmetric. -/
theorem cap_symm (h : IsNetworkP Np c N P B τ S) (a b : Fin g) : Np.cap c a b = Np.cap c b a := by
  by_cases hab : a = b
  · rw [hab]
  · rw [h.given.cap_eq _ _ hab, h.given.cap_eq _ _ (Ne.symm hab), h.is.c_symm]

/-! ## 2. The parts of a setting of a group and of Θ -/

/-- The nodes of the group G of the grouping number x: the a < g whose digit in x is G. -/
theorem mem_members {x G a : ℕ} : a ∈ members K g x G ↔ a < g ∧ col K x a = G := by
  simp [members]

/-- A sum of numbers that are at most M is at most their number times M. -/
theorem sum_map_le {ι : Type} (l : List ι) (f : ι → ℕ) (M : ℕ) (h : ∀ i ∈ l, f i ≤ M) : (l.map f).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have h1 := h i List.mem_cons_self
    have h2 := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- |z| ≤ 2^n, said of the natural number `z.natAbs`. -/
theorem natAbs_le {z : ℤ} {n : ℕ} (h : |z| ≤ 2 ^ n) : z.natAbs ≤ 2 ^ n := by
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- «at most (2^P)^{2g/K} terms»: a setting of a group with at most m nodes has at most P·m bits,
since P_a ≤ P. -/
theorem stLen_le (h : IsNetworkP Np c N P B τ S) {x G m : ℕ} (hm : (members K g x G).length ≤ m) : stLen K g Np.toPaperNetwork c x G ≤ P * m := by
  unfold stLen stLens
  refine (sum_map_le _ _ P fun a ha => ?_).trans ?_
  · have hag := (mem_members.1 ha).1
    change Np.len c a ≤ P
    rw [h.given.len_eq ⟨a, hag⟩]
    exact h.is.len_le _
  · rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hm

omit [HasSize C] in
/-- The part z_a of the setting number y of the group G has P_a bits. -/
theorem length_zA (Nq : PNet C) {x G : ℕ} {θs : List (List Bool)} {y a : ℕ} (ha : a ∈ members K g x G) :
    (zA K g Nq (((c, x), (G, θs)), y) a).length = Nq.n c a := by
  unfold zA zAt zOf stLens
  rw [← cut_eq_getD]
  exact length_cut _ _ _ _ (by simp [stLen, stLens]) ha

omit [HasSize C] in
/-- The block of the pair p in a string with at least Y_{G,G'} bits has c_p bits. -/
theorem length_lAt (Nq : PNet C) {x G G' : ℕ} {θ : List Bool} {p : ℕ × ℕ} (hp : p ∈ prs K g x G G') (hθ : lbLen K g Nq c x G G' ≤ θ.length) :
    (lAt K g Nq c x G G' θ p).length = Nq.cap c p.1 p.2 := by
  unfold lAt lbLens
  rw [← cut_eq_getD_beq (fun p : ℕ × ℕ => Nq.cap c p.1 p.2)]
  exact length_cut_of_le _ _ _ _ hθ hp

/-- A pair of a node of G and a node of G' is in the list of the pairs that have a block. -/
theorem mem_prs {x G G' a b : ℕ} (ha : a ∈ members K g x G) (hb : b ∈ members K g x G') : (a, b) ∈ prs K g x G G' :=
  List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨b, hb, rfl⟩⟩

variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}

/-- «let θ_{a,b} ∈ {0,1}^{c_{a,b}} consist of the bits of Θ(χ(b)) in the block of {a, b}»: it has
c_{a,b} bits, if Y_{γ,γ'} ≤ β for all γ ≠ γ' and every Θ(γ') has β bits. -/
theorem length_labOf (h : IsNetworkP Np c N P B τ S) (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β)
    (hθ : ∀ G', G' ≠ G → (θ G').length = β) {a b : ℕ} (ha : a ∈ members K g x G) (hb : b < g) (hc : col K x b ≠ G) :
    (labOf K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) a b).length = Np.cap c a b := by
  have hK : 0 < K := G.pos
  have hG' : col K x b < K := Nat.mod_lt _ hK
  have hbm : b ∈ members K g x (col K x b) := mem_members.2 ⟨hb, rfl⟩
  have hget : (List.ofFn θ).getD (col K x b) [] = θ ⟨col K x b, hG'⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hG']
    rfl
  have hlen : ((List.ofFn θ).getD (col K x b) []).length = β := by
    rw [hget]
    exact hθ _ fun h => hc (congrArg Fin.val h)
  unfold labOf
  by_cases hlt : G.val < col K x b
  · rw [if_pos hlt]
    exact length_lAt _ (mem_prs ha hbm) (by rw [hlen]; exact hβ _ G.2 _ hG' (Ne.symm hc))
  · rw [if_neg hlt, length_lAt _ (mem_prs hbm ha) (by rw [hlen]; exact hβ _ hG' _ G.2 hc)]
    exact cap_symm h ⟨b, hb⟩ ⟨a, (mem_members.1 ha).1⟩

/-- The size of a well-formed query. -/
theorem size_query_le (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    size ((c, x), (G.val, List.ofFn θ)) ≤ size c + size x + size K + K * (2 * β + 2) + 1 := by
  have h1 : size (List.ofFn θ) ≤ K * (2 * β + 2) + 1 := by
    rw [size_list]
    have := sum_map_le (List.ofFn θ) (fun l => size l + 1) (2 * β + 2) (fun l hl => by
      obtain ⟨G', rfl⟩ : ∃ G', θ G' = l := by simpa [List.mem_ofFn] using hl
      rw [size_bits]
      by_cases h : G' = G
      · rw [h, hG]; simp
      · rw [hθ G' h])
    rw [List.length_ofFn] at this
    omega
  have h2 : size G.val ≤ size K := by
    have := Nat.size_le_size G.2.le
    simp only [size_nat]
    omega
  simp only [size_prod]
  omega

/-! ## 3. A procedure behind the test for membership, and the integers that the factors return -/

omit [HasSize C] in
/-- Test z ∈ S_a, then run M or return 0. If M takes at most t ≥ τ steps on states of size at most
S' ≥ S whenever z is a setting, then the whole takes at most 2t + 1 steps. -/
theorem gate_runs {α : Type} [HasSize α] (h : IsNetworkP Np c N P B τ S) {u : α} {q : α → C × WQ} {M : Stepped α ℤ} {a : Fin g} {z : List Bool} {t S' : ℕ} {v : ℤ}
    (hq : q u = (c, (a.val, z))) (hz : z.length = N.len a) (ht : τ ≤ t) (hS : S ≤ S') (hM : z ∈ N.S a → M.Runs u t S' v) :
    (gated (mapIn q Np.mem) M).Runs u (2 * t + 1) (size u + S' + 4) (if z ∈ N.S a then v else 0) := by
  have h1 : (mapIn q Np.mem).Runs u t S' (decide (z ∈ N.S a)) := mapIn_runs (by rw [hq]; exact (h.given.mem_runs a z hz).mono ht hS)
  have h2 := gated_runs (h.τ_pos.trans ht) h1 (v := v) fun hb => hM (of_decide_eq_true hb)
  simpa only [decide_eq_true_eq] using h2

/-- The factor f_{a,b}(z, θ) of `N.toPaperNetwork`, for a ≠ b and θ of c_{a,b} bits: [z ∈
S_a]·f_{a,b}(z, θ). -/
theorem f_toPaperNetwork {a b : Fin g} (hab : a ≠ b) {z θ : List Bool} (hθ : θ.length = N.c a b) :
    N.toPaperNetwork.f a b z θ = if z ∈ N.S a then N.f a b z θ else 0 := by
  simp only [Net.toPaperNetwork, mem_words, hθ, hab, ne_eq, not_false_eq_true, true_and, and_true]

/-- The Ψ_{a,b} defined from the factors of `N.toPaperNetwork` is [z ∈ S_a][z' ∈ S_b]·Ψ_{a,b}(z,
z'). -/
theorem psi_toPaperNetwork (h : N.Is P B) {a b : Fin g} (hab : a ≠ b) (z z' : List Bool) :
    N.toPaperNetwork.Ψ a b z z' = if z ∈ N.S a then (if z' ∈ N.S b then N.Ψ a b z z' else 0) else 0 := by
  by_cases hz : z ∈ N.S a
  · by_cases hz' : z' ∈ N.S b
    · rw [if_pos hz, if_pos hz', Net.Ψ_toPaperNetwork h hab hz hz']
    · rw [if_pos hz, if_neg hz', Net.Ψ_toPaperNetwork_eq_zero fun hh => hz' hh.2]
  · rw [if_neg hz, Net.Ψ_toPaperNetwork_eq_zero fun hh => hz hh.1]

/-- The sum over the 2^{c_{a,b}} strings θ by which `termVal` is defined inside a group is the
Ψ_{a,b} of `N.toPaperNetwork`. -/
theorem sum_valF (h : N.Is P B) {a b : ℕ} (ha : a < g) (hb : b < g) (z z' : List Bool) :
    ∑ y ∈ range (2 ^ N.c ⟨a, ha⟩ ⟨b, hb⟩), valF N.toPaperNetwork a b z (toWord (N.c ⟨a, ha⟩ ⟨b, hb⟩) y) * valF N.toPaperNetwork b a z' (toWord (N.c ⟨a, ha⟩ ⟨b, hb⟩) y) =
      N.toPaperNetwork.Ψ ⟨a, ha⟩ ⟨b, hb⟩ z z' := by
  rw [sum_toWord (N.c ⟨a, ha⟩ ⟨b, hb⟩) fun θ => valF N.toPaperNetwork a b z θ * valF N.toPaperNetwork b a z' θ, Groundwork.Network.Ψ, Net.lab_toPaperNetwork h]
  refine sum_congr rfl fun θ _ => ?_
  rw [show valF N.toPaperNetwork a b z θ = N.toPaperNetwork.f ⟨a, ha⟩ ⟨b, hb⟩ z θ from dif_pos ⟨ha, hb⟩,
    show valF N.toPaperNetwork b a z' θ = N.toPaperNetwork.f ⟨b, hb⟩ ⟨a, ha⟩ z' θ from dif_pos ⟨hb, ha⟩]

/-! ## 4. One factor, one entry -/

/-- One of the g² factors of a term of W̃_γ(Θ). The index i < g·g stands for the pair of nodes (a,
b) = (i / g, i % g). The factor is 1, or [z_a ∈ S_a]·W_a(z_a), or [z_a ∈ S_a][z_b ∈
S_b]·Ψ_{a,b}(z_a, z_b), or [z_a ∈ S_a]·f_{a,b}(z_a, θ_{a,b}).
It costs at most 4τ + 3 steps (two tests and one call, in the case of Ψ) and is at most 2^B in
absolute value. -/
theorem termP_runs (h : IsNetworkP Np c N P B τ S) (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β)
    (hθ : ∀ G', G' ≠ G → (θ G').length = β) (y : ℕ) {i : ℕ} (hi : i < g * g) :
    (termP K g Np).Runs ((((c, x), (G.val, List.ofFn θ)), y), i) (4 * τ + 3) (2 * size ((((c, x), (G.val, List.ofFn θ)), y), i) + S + 12)
      (termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)) ∧
    (termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)).natAbs ≤ 2 ^ B := by
  have hg : 0 < g := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have ha : i / g < g := Nat.div_lt_of_lt_mul hi
  have hb : i % g < g := Nat.mod_lt _ hg
  have h2B : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  have hτ := h.τ_pos
  have hS := Net.sized_toPaperNetwork h.is
  cases h1 : isOne K g ((((c, x), (G.val, List.ofFn θ)), y), i) with
  | true =>
    have ev : termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i) = 1 := by
      simp only [termVal, h1, if_true]
    rw [ev]
    refine ⟨(ite_runs_true h1 (const_runs (1 : ℤ) _)).mono (by omega) ?_, by simpa using h2B⟩
    simp only [size_prod, size_nat, size_int]
    have : (1 : ℤ).natAbs.size = 1 := rfl
    omega
  | false =>
    have hcolA : col K x (i / g) = G.val := by
      by_contra hne
      have : isOne K g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isOne, hne]
      rw [h1] at this
      cases this
    have ham : i / g ∈ members K g x G := mem_members.2 ⟨ha, hcolA⟩
    have hza : (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i / g)).length = N.len ⟨i / g, ha⟩ :=
      (length_zA Np.toPaperNetwork ham).trans (h.given.len_eq ⟨i / g, ha⟩)
    cases h2 : isW g ((((c, x), (G.val, List.ofFn θ)), y), i) with
    | true =>
      have ev : termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i) =
          N.toPaperNetwork.W ⟨i / g, ha⟩ (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i / g)) := by
        simp only [termVal, h1, h2, if_true, if_false, Bool.false_eq_true]
        exact dif_pos ha
      rw [ev]
      have r := gate_runs h (u := ((((c, x), (G.val, List.ofFn θ)), y), i)) (q := qW K g Np.toPaperNetwork) (M := mapIn (qW K g Np.toPaperNetwork) Np.W) rfl hza le_rfl le_rfl
        fun hm => mapIn_runs (h.given.W_runs ⟨i / g, ha⟩ _ hm)
      exact ⟨(ite_runs_false h1 (ite_runs_true h2 r)).mono (by omega) (by omega), natAbs_le (hS.abs_W _ _)⟩
    | false =>
      have hab : i / g ≠ i % g := by
        intro he
        have : isW g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isW, he]
        rw [h2] at this
        cases this
      have habF : (⟨i / g, ha⟩ : Fin g) ≠ ⟨i % g, hb⟩ := fun e => hab (congrArg Fin.val e)
      have hcap : Np.cap c (i / g) (i % g) = N.c ⟨i / g, ha⟩ ⟨i % g, hb⟩ := h.given.cap_eq ⟨i / g, ha⟩ ⟨i % g, hb⟩ habF
      cases h3 : isPsi K g ((((c, x), (G.val, List.ofFn θ)), y), i) with
      | false =>
        have hcolB : col K x (i % g) ≠ G.val := by
          intro he
          have : isPsi K g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isPsi, he]
          rw [h3] at this
          cases this
        have hl : (labOf K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) (i / g) (i % g)).length = N.c ⟨i / g, ha⟩ ⟨i % g, hb⟩ :=
          (length_labOf h hβ hθ ham hb hcolB).trans hcap
        have ev : termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i) =
            N.toPaperNetwork.f ⟨i / g, ha⟩ ⟨i % g, hb⟩ (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i / g))
              (labOf K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) (i / g) (i % g)) := by
          simp only [termVal, h1, h2, h3, if_false, Bool.false_eq_true]
          exact dif_pos ⟨ha, hb⟩
        rw [ev]
        refine ⟨?_, natAbs_le (hS.abs_f _ _ _ _)⟩
        rw [f_toPaperNetwork habF hl]
        have r := gate_runs h (u := ((((c, x), (G.val, List.ofFn θ)), y), i)) (q := qW K g Np.toPaperNetwork) (M := mapIn (qF K g Np.toPaperNetwork) Np.f) rfl hza le_rfl le_rfl
          fun hm => mapIn_runs (h.given.f_runs ⟨i / g, ha⟩ ⟨i % g, hb⟩ habF _ hm _ (mem_words.2 hl))
        exact (ite_runs_false h1 (ite_runs_false h2 (ite_runs_false h3 r))).mono (by omega) (by omega)
      | true =>
        have hcolB : col K x (i % g) = G.val := by simpa [isPsi] using h3
        have hbm : i % g ∈ members K g x G := mem_members.2 ⟨hb, hcolB⟩
        have hzb : (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i % g)).length = N.len ⟨i % g, hb⟩ :=
          (length_zA Np.toPaperNetwork hbm).trans (h.given.len_eq ⟨i % g, hb⟩)
        have ev : termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i) =
            N.toPaperNetwork.Ψ ⟨i / g, ha⟩ ⟨i % g, hb⟩ (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i / g))
              (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i % g)) := by
          rw [← sum_valF h.is ha hb, ← hcap]
          simp only [termVal, h1, h2, h3, if_true, if_false, Bool.false_eq_true, nLab]
          rfl
        rw [ev]
        refine ⟨?_, natAbs_le (hS.abs_Ψ _ _ _ _ habF)⟩
        rw [psi_toPaperNetwork h.is habF]
        have r := gate_runs h (u := ((((c, x), (G.val, List.ofFn θ)), y), i)) (q := qW K g Np.toPaperNetwork)
          (M := gated (mapIn (qMb K g Np) Np.mem) (mapIn (qPsi K g Np) Np.Ψ)) (t := 2 * τ + 1)
          (S' := size ((((c, x), (G.val, List.ofFn θ)), y), i) + S + 4) rfl hza (by omega) (by omega)
          fun hm => gate_runs h (q := qMb K g Np) (M := mapIn (qPsi K g Np) Np.Ψ) rfl hzb le_rfl le_rfl
            fun hm' => mapIn_runs (h.given.Ψ_runs ⟨i / g, ha⟩ ⟨i % g, hb⟩ habF _ hm _ hm')
        exact (ite_runs_false h1 (ite_runs_false h2 (ite_runs_true h3 r))).mono (by omega) (by omega)

/-- «The sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} terms, each a product of at most g² values …
and one entry costs 2^{2gP/K}·poly(P + B)·τ operations», with explicit numbers: if every group has
at most m nodes and Y_{γ,γ'} ≤ β, then `tableM` answers a well-formed
query (β bits for every other group) within 2^{Pm}·(g²(4τ + 4) + 1) steps. -/
theorem tableM_runs (h : IsNetworkP Np c N P B τ S) (m : ℕ) (hm : ∀ G < K, (members K g x G).length ≤ m)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β) (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    (tableM K g Np).Runs ((c, x), (G.val, List.ofFn θ)) (2 ^ (P * m) * (g * g * (4 * τ + 4) + 1))
      (S + 4 * (size c + size x + size K + K * (2 * β + 2)) + 5 * (P * m) + 2 * (B * (g * g)) + 3 * size (g * g) + 30)
      (mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ))) := by
  have hsu := size_query_le (c := c) (x := x) hθ hG
  have hst : stLen K g Np.toPaperNetwork c x G ≤ P * m := stLen_le h (hm G G.2)
  cases hv : validB K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) with
  | false =>
    have ev : mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) = 0 := by
      simp only [mergedVal, hv, if_false, Bool.false_eq_true]
    rw [ev]
    refine (ite_runs_false hv (const_runs (0 : ℤ) _)).mono (Nat.succ_le_of_lt (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.succ_pos _))) ?_
    have : size (0 : ℤ) = 1 := rfl
    omega
  | true =>
    have ev : mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) = ∑ y ∈ range (nStates K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ))),
        ∏ i ∈ range (g * g), termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i) := by
      simp only [mergedVal, hv, if_true]
    rw [ev]
    have eN : nStates K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) = 2 ^ stLen K g Np.toPaperNetwork c x G := rfl
    have hin : ∀ y < nStates K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)), (prodRange (nPairs g) (termP K g Np)).Runs (((c, x), (G.val, List.ofFn θ)), y)
        (g * g * (4 * τ + 3 + 1))
        (3 * (size ((c, x), (G.val, List.ofFn θ)) + (stLen K g Np.toPaperNetwork c x G + 1)) + 3 * size (g * g) + B * (g * g) + S + 15)
        (∏ i ∈ range (g * g), termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)) := by
      intro y hy
      have hy' : y.size ≤ stLen K g Np.toPaperNetwork c x G := Nat.size_le.2 (eN ▸ hy)
      have := prodRange_runs (N := nPairs g) (M := termP K g Np) (a := (((c, x), (G.val, List.ofFn θ)), y))
        (fun _ => 4 * τ + 3) (fun i => termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)) (2 ^ B)
        (2 * (size (((c, x), (G.val, List.ofFn θ)), y) + size (g * g)) + S + 12) Nat.one_le_two_pow
        (fun i hi => (termP_runs h hβ hθ y hi).1.mono le_rfl (by
          have := Nat.size_le_size (Nat.le_of_lt hi)
          simp only [nPairs] at this
          simp only [size_prod, size_nat] at this ⊢
          omega))
        (fun i hi => (termP_runs h hβ hθ y hi).2)
      refine this.mono (by simp [nPairs]) ?_
      simp only [nPairs, ← pow_mul]
      simp only [size_prod, size_nat, Nat.size_pow] at hsu ⊢
      omega
    have hout := sumRange_runs (N := nStates K g Np.toPaperNetwork) (a := ((c, x), (G.val, List.ofFn θ))) (fun _ => g * g * (4 * τ + 3 + 1))
      (fun y => ∏ i ∈ range (g * g), termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)) ((2 ^ B) ^ (g * g)) _ hin
      (fun y _ => natAbs_prod_le _ _ _ fun i hi => (termP_runs h hβ hθ y hi).2)
    refine (ite_runs_true hv hout).mono ?_ ?_
    · rw [sum_const, card_range, smul_eq_mul, eN]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hst) le_rfl
    · rw [eN, ← pow_mul, ← pow_add]
      simp only [size_nat, Nat.size_pow] at hsu ⊢
      omega

/-- «… at most (2^P)^{2g/K} = 2^{2gP/K} terms, each a product of at most g² values. So |W̃_γ| <
2^{B'} with B' = ⌈2gP/K⌉ + g²B»: if every group has at most m nodes, an entry is at most 2^{Pm +
g²B} in absolute value. -/
theorem abs_entry_le (h : IsNetworkP Np c N P B τ S) (m : ℕ) (hm : ∀ G < K, (members K g x G).length ≤ m)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β) (hθ : ∀ G', G' ≠ G → (θ G').length = β) :
    |mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ))| ≤ 2 ^ (P * m + g ^ 2 * B) := by
  have hst : stLen K g Np.toPaperNetwork c x G ≤ P * m := stLen_le h (hm G G.2)
  have key : (mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ))).natAbs ≤ 2 ^ (P * m + g ^ 2 * B) := by
    unfold mergedVal
    split_ifs
    · refine (natAbs_sum_le _ ((2 ^ B) ^ (g * g)) _ fun y _ => natAbs_prod_le _ _ _ fun i hi => (termP_runs h hβ hθ y hi).2).trans ?_
      change 2 ^ stLen K g Np.toPaperNetwork c x G * (2 ^ B) ^ (g * g) ≤ _
      rw [← pow_mul, ← pow_add]
      refine Nat.pow_le_pow_right (by omega) (Nat.add_le_add hst (le_of_eq ?_))
      ring
    · simp
  rw [Int.abs_eq_natAbs]
  exact_mod_cast key

/-- The bounds of `tableM_runs` with one constant c₁ that depends on K and g only: «one entry costs
2^{2gP/K}·poly(P + B)·τ operations». For a grouping whose groups have at most m ≤ 2g nodes, with
Y_{γ,γ'} ≤ β ≤ 2gP: at most c₁·2^{Pm}·τ steps on states of size at most
S + c₁·(size c + P + B)^{c₁}. -/
theorem tableM_runs_coarse (K g : ℕ) : ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
    ∀ x < K ^ g, ∀ β ≤ 2 * (g * P), ∀ m ≤ 2 * g, (∀ G < K, (members K g x G).length ≤ m) → (∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β) →
    ∀ (G : Fin K) (θ : Fin K → List Bool), (∀ G', G' ≠ G → (θ G').length = β) → θ G = [] →
    (tableM K g Np).Runs ((c, x), (G.val, List.ofFn θ)) (c₁ * 2 ^ (P * m) * τ) (S + c₁ * (size c + P + B) ^ c₁) (mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ))) := by
  obtain ⟨sx, hsx⟩ : ∃ sx, sx = size (K ^ g) := ⟨_, rfl⟩
  obtain ⟨sK, hsK⟩ : ∃ sK, sK = size K := ⟨_, rfl⟩
  obtain ⟨sg, hsg⟩ : ∃ sg, sg = size (g * g) := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = 4 + 4 * sx + 4 * sK + (16 * (K * g) + 8 * K) + 10 * g + 2 * (g * g) + 3 * sg + 30 := ⟨_, rfl⟩
  refine ⟨c₀ + (8 * (g * g) + 1), by omega, ?_⟩
  intro C _ Np c N P B τ S h x hx β hβ m hm hmem hlb G θ hθ hG
  have hτ := h.τ_pos
  have hP := h.is.P_pos
  refine (tableM_runs h m hmem hlb hθ hG).mono ?_ ?_
  · generalize 2 ^ (P * m) = a
    calc a * (g * g * (4 * τ + 4) + 1) ≤ a * (g * g * (8 * τ) + τ) := Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) hτ)
      _ = (8 * (g * g) + 1) * a * τ := by ring
      _ ≤ (c₀ + (8 * (g * g) + 1)) * a * τ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
  · obtain ⟨X, hX⟩ : ∃ X, X = size c + P + B := ⟨_, rfl⟩
    rw [← hX]
    have hX1 : 1 ≤ X := by omega
    have e1 : size x ≤ sx * X := by
      have : size x ≤ sx := by
        have := Nat.size_le_size hx.le
        simp only [hsx, size_nat]
        omega
      exact this.trans (Nat.le_mul_of_pos_right _ hX1)
    have e2 : sK ≤ sK * X := Nat.le_mul_of_pos_right _ hX1
    have e3 : K * (2 * β + 2) ≤ (4 * (K * g) + 2 * K) * X := by
      calc K * (2 * β + 2) ≤ K * (2 * (2 * (g * P)) + 2) := Nat.mul_le_mul_left _ (by omega)
        _ = 4 * (K * g) * P + 2 * K * 1 := by ring
        _ ≤ 4 * (K * g) * X + 2 * K * X := Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left _ hX1)
        _ = (4 * (K * g) + 2 * K) * X := by ring
    have e4 : P * m ≤ 2 * g * X := by
      calc P * m ≤ X * (2 * g) := Nat.mul_le_mul (by omega) hm
        _ = 2 * g * X := by ring
    have e5 : B * (g * g) ≤ g * g * X := by
      calc B * (g * g) ≤ X * (g * g) := Nat.mul_le_mul_right _ (by omega)
        _ = g * g * X := by ring
    have e6 : sg ≤ sg * X := Nat.le_mul_of_pos_right _ hX1
    have e7 : c₀ * X = 4 * X + 4 * (sx * X) + 4 * (sK * X) + 4 * ((4 * (K * g) + 2 * K) * X) + 5 * (2 * g * X) + 2 * (g * g * X) + 3 * (sg * X) + 30 * X := by
      rw [hc₀]
      ring
    have e8 : c₀ * X ≤ (c₀ + (8 * (g * g) + 1)) * X ^ (c₀ + (8 * (g * g) + 1)) := Nat.mul_le_mul (by omega) (Nat.le_self_pow (by omega) X)
    rw [← hsK, ← hsg]
    omega

/-- Y_{γ,γ'} as the programs compute it (a sum over a list of pairs of numbers) is the Y_{γ,γ'} of
the paper. -/
theorem lbLen_eq_Y (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x : ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') :
    lbLen K g Np.toPaperNetwork c x γ.val γ'.val = Y N.c (Paper.grouping hK0 x) γ γ' := by
  rw [lbLen_eq Np.toPaperNetwork hK0 (isPaperNetwork h).presented x hne, Groundwork.Network.merge_c]
  rfl

end Table

/-! ## 5. The two steps -/

open Table

/-- **«Cost», first two sentences.** «The sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} = 2^{2gP/K}
terms, each a product of at most g² values. So |W̃_γ| < 2^{B'} with B' = ⌈2gP/K⌉ + g²B, and one
entry costs 2^{2gP/K}·poly(P + B)·τ operations.»
Different from the paper: ⌊2g/K⌋ nodes in a group, so P·⌊2g/K⌋ in place of 2gP/K; «at most 2^{B'}»
in place of «below 2^{B'}». -/
theorem stTable : StTable := by
  intro K g
  obtain ⟨c₁, h1, hc₁⟩ := tableM_runs_coarse K g
  refine ⟨c₁, h1, fun hK0 C _ Np c N P B τ S h x hx L hL hG1 hY γ Θ hΘ hγ => ?_⟩
  have hmem : ∀ G < K, (members K g x G).length ≤ 2 * g / K := fun G hG => by
    rw [length_members hK0 x ⟨G, hG⟩, Nat.le_div_iff_mul_le hK0, Nat.mul_comm]
    exact hG1 ⟨G, hG⟩
  have hlb : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ L := fun G hG G' hG' hne => by
    have hne' : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e => hne (congrArg Fin.val e)
    rw [lbLen_eq_Y h hK0 x hne']
    exact hY _ _ hne'
  rw [Paper.groupedTables, toInst_eq_mergedVal Np.toPaperNetwork hK0 (isPaperNetwork h).presented x L γ Θ hΘ]
  exact ⟨hc₁ C Np c N P B τ S h x hx L hL _ (Nat.div_le_self _ _) hmem hlb γ Θ hΘ hγ, abs_entry_le h _ hmem hlb hΘ⟩

/-- **«… so the value equals Z»** (end of the paragraph «The algorithm»): the (K, L)-clique with the
tables W̃ has the value of the network, if Y_{γ,γ'} ≤ L. Same as in the paper, except that the value
of the (K, L)-clique is written with one string per edge (`Paper.cliqueValue`). -/
theorem stValue : StValue := by
  intro K g hK0 C _ Np c N P B τ S h x L hY
  rw [Paper.grouped_value Np.toPaperNetwork hK0 (isPaperNetwork h) x L fun γ γ' hne => by
    rw [Groundwork.Network.merge_c]
    exact hY γ γ' hne]
  exact Net.value_toPaperNetwork h.is

end Eight.ViaGrouping
