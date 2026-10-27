/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecNetworks_LemGrouping
import all StepMachines.Prog.NetVal
import Mathlib.Tactic

/-! # Proof of Lemma 1, «The algorithm»: the display of W̃_γ

«Put W̃_γ(Θ) = [all appended bits are 0] Σ_{(z_a), a ∈ G_γ} ∏_{a ∈ G_γ} W_a(z_a) ∏_{{a,b} ⊆ G_γ}
Ψ_{a,b}(z_a, z_b) ∏_{a ∈ G_γ, b ∉ G_γ} f_{a,b}(z_a, θ_{a,b}). Here each z_a ranges over S_a.»
The tables on which the algorithm of Lemma 1 runs are `Paper.groupedTables`, defined in two steps
(`Network.merge`, then `Network.toInst`). This file unfolds the two steps and states the result as
the one formula of the paper
(`groupedTables_eq`; for a network as Definition 2 prints it: `tables_eq`), with names for the
appended bits (`appendedBits`) and for θ_{a,b} (`thetaAt`, of c_{a,b} bits by `length_thetaAt`), and
proves the sentence «both W̃_γ and W̃_γ' read θ_{a,b} from the same block of this string, so θ_{a,b} =
θ_{b,a}» (`thetaAt_comm`).
Nothing here depends on Lemma 2 or on its pieces. -/

@[expose] public section

namespace Eight.SecNetworks

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Paper

variable {C : Type} {g K : ℕ}

/-- «the L − Y_{γ,γ'} positions after the last block hold the appended bits»: the bits of the string
θ on the edge {γ, γ'} after the first Y_{γ,γ'} positions. Here Y_{γ,γ'} is `lbLen`, the sum of the
numbers c_{a,b} that the procedures give,
over a in the group with the smaller number and b in the other. -/
def appendedBits (Np : NetworkProcedures C) (c : C) (x : ℕ) (γ γ' : Fin K) (θ : List Bool) : List Bool :=
  θ.drop (lbLen K g Np c x (min γ γ').val (max γ γ').val)

/-- «For a ∈ G_γ and b ∉ G_γ let θ_{a,b} ∈ {0,1}^{c_{a,b}} consist of the bits of Θ(χ(b)) in the
block of {a, b}.» The order of the pairs between two groups is that of the list `prs`: (a', b') with
a' in the group with the smaller
number, in increasing order of a', then of b'; the paper allows any order. -/
def thetaAt (Np : NetworkProcedures C) (c : C) (hK0 : 0 < K) (x : ℕ) (Θ : Fin K → List Bool) (a b : Fin g) : List Bool :=
  mdec K g Np c x (min (grouping hK0 x a) (grouping hK0 x b)) (max (grouping hK0 x a) (grouping hK0 x b)) (Θ (grouping hK0 x b))
    (if grouping hK0 x a < grouping hK0 x b then (a, b) else (b, a))

end Eight.SecNetworks

end

public section

namespace Eight.SecNetworks

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Paper

variable {C : Type} {g K : ℕ}

/-- **Proof of Lemma 1, «The algorithm»: the display of W̃_γ.** For Θ : [K] ∖ {γ} → {0,1}^L,
W̃_γ(Θ) = [all appended bits are 0] Σ_{(z_a), a ∈ G_γ} ∏_{a ∈ G_γ} W_a(z_a) ∏_{{a,b} ⊆ G_γ}
Ψ_{a,b}(z_a, z_b) ∏_{a ∈ G_γ, b ∉ G_γ} f_{a,b}(z_a, θ_{a,b}), each z_a ranging over S_a. Same as in
the paper. In Lean's terms: Θ is a function on all
of [K], whose value at γ is not read; (z_a) is a function on all nodes, with the empty string
outside G_γ; the pairs {a, b} ⊆ G_γ are the pairs a < b. -/
theorem groupedTables_eq (Np : NetworkProcedures C) (c : C) (N : Paper.Network (Fin g) (List Bool) (List Bool)) (hK0 : 0 < K) (x L : ℕ) (γ : Fin K) (Θ : Fin K → List Bool)
    (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) :
    groupedTables Np c N hK0 x L γ Θ =
      (if ∀ γ', γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np c x γ γ' (Θ γ'), bit = false then 1 else 0) *
        ∑ z ∈ tuples (fun a => grouping hK0 x a = γ) N.S [],
          (∏ a with grouping hK0 x a = γ, N.W a (z a)) *
            (∏ p ∈ pairs (Fin g) with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
            ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np c hK0 x Θ p.1 p.2) := by
  have hcond : (∀ b ∈ univ.erase γ, Θ b ∈ mD K g Np c x L (min γ b) (max γ b)) ↔
      ∀ γ', γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np c x γ γ' (Θ γ'), bit = false := by
    refine forall_congr' fun b => ?_
    simp only [mem_erase, mem_univ, and_true]
    refine imp_congr_right fun hb => ?_
    simp [mD, appendedBits, hΘ b hb]
  have hprod : ∀ z : Fin g → List Bool,
      ∏ b ∈ univ.erase γ, ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = b,
        N.f p.1 p.2 (z p.1) (mdec K g Np c x (min γ b) (max γ b) (Θ b) (if γ < b then p else p.swap))
      = ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np c hK0 x Θ p.1 p.2) := by
    intro z
    rw [← prod_fiberwise_of_maps_to (s := univ.filter fun p : Fin g × Fin g => grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 ≠ γ) (t := univ.erase γ)
      (g := fun p => grouping hK0 x p.2) (fun p hp => by simpa using (mem_filter.1 hp).2.2)]
    refine prod_congr rfl fun b hb => ?_
    have hb' : b ≠ γ := by simpa using hb
    rw [filter_filter]
    refine prod_congr (filter_congr fun p _ => ?_) fun p hp => ?_
    · constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2 ▸ hb'⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
    · obtain ⟨⟨h1, _⟩, h2⟩ := (mem_filter.1 hp).2
      unfold thetaAt
      rw [h1, h2]
      rfl
  change ∑ z ∈ tuples (fun a => grouping hK0 x a = γ) N.S [],
      ((∏ a with grouping hK0 x a = γ, N.W a (z a)) * ∏ p ∈ pairs (Fin g) with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
        ∏ b ∈ univ.erase γ, (if Θ b ∈ mD K g Np c x L (min γ b) (max γ b) then
          ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = b,
            N.f p.1 p.2 (z p.1) (mdec K g Np c x (min γ b) (max γ b) (Θ b) (if γ < b then p else p.swap)) else 0) = _
  rw [mul_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [prod_ite_zero, hprod]
  simp only [hcond]
  split_ifs <;> ring

/-- «The two copies of the string on an edge {γ, γ'} must agree, and both W̃_γ and W̃_γ' read
θ_{a,b} from the same block of this string, so θ_{a,b} = θ_{b,a}»: if a and b lie in different
groups and the argument Θ of the table of a's group
and the argument Θ' of the table of b's group have the same string on the edge between the two
groups, then θ_{a,b}, read from Θ, is θ_{b,a}, read from Θ'. -/
theorem thetaAt_comm (Np : NetworkProcedures C) (c : C) (hK0 : 0 < K) (x : ℕ) (Θ Θ' : Fin K → List Bool) {a b : Fin g} (hne : grouping hK0 x a ≠ grouping hK0 x b)
    (h : Θ (grouping hK0 x b) = Θ' (grouping hK0 x a)) : thetaAt Np c hK0 x Θ a b = thetaAt Np c hK0 x Θ' b a := by
  unfold thetaAt
  rw [h, min_comm, max_comm]
  rcases lt_or_gt_of_ne hne with h1 | h1
  · rw [if_pos h1, if_neg h1.not_gt]
  · rw [if_neg h1.not_gt, if_pos h1]

/-- «θ_{a,b} ∈ {0,1}^{c_{a,b}}»: if a and b lie in different groups, the string Θ(χ(b)) has L bits
and Y_{γ,γ'} ≤ L for all pairs of groups, then θ_{a,b} has c_{a,b} bits. -/
theorem length_thetaAt (Np : NetworkProcedures C) {c : C} {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ} (hK0 : 0 < K) (hN : Paper.IsNetwork Np c N P B τ S)
    (x L : ℕ) (hL : ∀ γ γ' : Fin K, γ ≠ γ' → (N.merge (grouping hK0 x) [] []).c γ γ' ≤ L) (Θ : Fin K → List Bool) {a b : Fin g}
    (hne : grouping hK0 x a ≠ grouping hK0 x b) (hΘ : (Θ (grouping hK0 x b)).length = L) : (thetaAt Np c hK0 x Θ a b).length = N.c a b := by
  have hab : a ≠ b := fun e => hne (e ▸ rfl)
  have key : ∀ (G G' : Fin K) (p : Fin g × Fin g), G ≠ G' → grouping hK0 x p.1 = G → grouping hK0 x p.2 = G' →
      (mdec K g Np c x G G' (Θ (grouping hK0 x b)) p).length = Np.cap c p.1.val p.2.val := by
    intro G G' p hG h1 h2
    change (lAt K g Np c x G G' (Θ (grouping hK0 x b)) (p.1.val, p.2.val)).length = _
    rw [lAt_eq_cut]
    refine length_cut_of_le (fun p : Fin g × Fin g => Np.cap c p.1.val p.2.val) [] _ _ ?_ ?_
    · rw [← lbLens_eq, hΘ]
      change lbLen K g Np c x G.val G'.val ≤ L
      rw [lbLen_eq Np hK0 hN.presented x hG]
      exact hL G G' hG
    · rw [mem_prsF]
      exact ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩
  unfold thetaAt
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le, if_pos h, key _ _ (a, b) hne rfl rfl]
    exact (hN.presented.c_eq a b hab).symm
  · rw [min_eq_right h.le, max_eq_left h.le, if_neg h.not_gt, key _ _ (b, a) hne.symm rfl rfl, hN.sized.c_symm a b]
    exact (hN.presented.c_eq b a hab.symm).symm

/-- **The display of W̃_γ for a network as Definition 2 prints it** (with sets S_a of settings and
functions Ψ_{a,b} of its own): the tables on which the algorithm of Lemma 1 runs are given by the
formula of the paper in terms of
W_a, Ψ_{a,b}, f_{a,b} and S_a of N, for Θ : [K] ∖ {γ} → {0,1}^L and Y_{γ,γ'} ≤ L. Same as in the
paper; the remarks at `groupedTables_eq` apply. -/
theorem tables_eq [HasSize C] {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ} (h : IsNetwork Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ)
    (hL : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (grouping hK0 x) γ γ' ≤ L) (γ : Fin K) (Θ : Fin K → List Bool) (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) :
    groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L γ Θ =
      (if ∀ γ', γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np.toPaperNetwork c x γ γ' (Θ γ'), bit = false then 1 else 0) *
        ∑ z ∈ tuples (fun a => grouping hK0 x a = γ) N.S [],
          (∏ a with grouping hK0 x a = γ, N.W a (z a)) *
            (∏ p ∈ pairs (Fin g) with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
            ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np.toPaperNetwork c hK0 x Θ p.1 p.2) := by
  have hN : Paper.IsNetwork Np.toPaperNetwork c N.toPaperNetwork P B _ _ := ⟨Net.sized_toPaperNetwork h.is, presents_toPaperNetwork h⟩
  have hL' : ∀ γ γ' : Fin K, γ ≠ γ' → (N.toPaperNetwork.merge (grouping hK0 x) [] []).c γ γ' ≤ L := fun γ γ' hne => by
    rw [Groundwork.Network.merge_c]
    exact hL γ γ' hne
  rw [groupedTables_eq Np.toPaperNetwork c N.toPaperNetwork hK0 x L γ Θ hΘ]
  congr 1
  symm
  refine sum_subset_zero_on_sdiff (fun z hz => ?_) (fun z hz => ?_) fun z hz => ?_
  · rw [mem_tuples] at hz ⊢
    exact fun a => ⟨fun ha => mem_words.2 (h.is.len_S a _ ((hz a).1 ha)), (hz a).2⟩
  · obtain ⟨hz1, hz2⟩ := mem_sdiff.1 hz
    rw [mem_tuples] at hz1 hz2
    obtain ⟨a, ha, hza⟩ : ∃ a, grouping hK0 x a = γ ∧ z a ∉ N.S a := by
      by_contra hcon
      exact hz2 fun a => ⟨fun ha => by_contra fun hza => hcon ⟨a, ha, hza⟩, (hz1 a).2⟩
    rw [prod_eq_zero (i := a) (mem_filter.2 ⟨mem_univ _, ha⟩) (by simp only [Net.toPaperNetwork]; rw [if_neg hza]), zero_mul, zero_mul]
  · rw [mem_tuples] at hz
    congr 1
    · congr 1
      · refine prod_congr rfl fun a ha => ?_
        simp only [Net.toPaperNetwork]
        rw [if_pos ((hz a).1 (mem_filter.1 ha).2)]
      · refine prod_congr rfl fun p hp => ?_
        obtain ⟨hp1, hp2, hp3⟩ := mem_filter.1 hp
        have hlt : p.1 < p.2 := (mem_filter.1 hp1).2
        exact (Net.Ψ_toPaperNetwork h.is hlt.ne ((hz _).1 hp2) ((hz _).1 hp3)).symm
    · refine prod_congr rfl fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := (mem_filter.1 hp).2
      have hne : grouping hK0 x p.1 ≠ grouping hK0 x p.2 := fun e => hp2 (e ▸ hp1)
      have hlen := length_thetaAt Np.toPaperNetwork hK0 hN x L hL' Θ hne (hΘ _ hp2)
      simp only [Net.toPaperNetwork] at hlen ⊢
      rw [if_pos ⟨fun e => hne (e ▸ rfl), (hz _).1 hp1, mem_words.2 hlen⟩]

end Eight.SecNetworks
