/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Value.Blocks
public import Value.Sums

/-! # The joint sum over z and θ

Proof of Lemma 1, paragraph «The algorithm»: the two copies of the string on an edge {γ, γ'} must
agree, and both W̃_γ and W̃_γ' read θ_{a,b} from the same block of this string, so θ_{a,b} =
θ_{b,a}; the appended bits must be 0. Together with the sums inside the tables, this is a sum over
all z ∈ ∏_{a ∈ [g]} S_a and over one string
θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair {a,b} of nodes in different groups.
`stJointSumOf` proves the last sentence from the ones before it, which are its hypotheses, in these
steps:
1. the choices Λ of one string per edge with a nonzero appended bit are dropped (`StAppendedZero`);
2. in the others the factor [all appended bits are 0] is 1, and each table reads the strings θ =
   `readBlocks` Λ, the same from both sides (`StSameBlock`; `display_eq`);
3. the variable Λ is changed for θ (`StBlocks`);
4. the product over the groups of the sums inside the tables is one sum over z (`StSumsInside`);
5. the products are regrouped: nodes by groups, pairs inside groups, and ordered pairs across groups
   into unordered pairs (`prod_groupTerm`). -/

public section

namespace Value

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping

variable {C : Type} [HasSize C] {g K : ℕ}

/-- The term of (z_a), a ∈ G_γ, in the display of W̃_γ, with the strings θ_{a,b} taken from a choice
θ of one string per pair {a, b} of nodes in different groups: ∏_{a ∈ G_γ} W_a(z_a) ∏_{{a,b} ⊆ G_γ}
Ψ_{a,b}(z_a, z_b) ∏_{a ∈ G_γ, b ∉ G_γ} f_{a,b}(z_a, θ_{a,b}). -/
def groupTerm (N : Net g) (χ : Fin g → Fin K) (θ : Fin g × Fin g → List Bool) (γ : Fin K) (z : Fin g → List Bool) : ℤ :=
  (∏ a with χ a = γ, N.W a (z a)) * (∏ p ∈ pairs (Fin g) with χ p.1 = γ ∧ χ p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
    ∏ p : Fin g × Fin g with χ p.1 = γ ∧ χ p.2 ≠ γ, N.f p.1 p.2 (z p.1) (θ (pr p.1 p.2))

/-- If all appended bits of Λ are 0, the table of the group γ at the strings of Λ on the edges at γ
is the sum inside the table, with the strings θ_{a,b} that are read from Λ. -/
theorem display_eq (hSB : StSameBlock) (Np : Procs C) (c : C) (N : Net g) (hK0 : 0 < K) (x : ℕ) {Λ : Fin K × Fin K → List Bool} (hA : AppendedZero g Np c x Λ) (γ : Fin K) :
    display Np c N hK0 x γ (star Λ γ) = ∑ z ∈ tuples (fun a => Paper.grouping hK0 x a = γ) N.S [], groupTerm N (Paper.grouping hK0 x) (readBlocks Np c hK0 x Λ) γ z := by
  unfold display
  rw [if_pos (hA γ), one_mul]
  refine sum_congr rfl fun z _ => ?_
  unfold groupTerm
  congr 1
  refine prod_congr rfl fun p hp => ?_
  obtain ⟨h1, h2⟩ := (mem_filter.1 hp).2
  rw [← thetaAt_eq_readBlocks hSB Np c hK0 x Λ (fun e => h2 (e ▸ h1)), h1]

/-- The product over the groups of the terms of the tables is the term of (z, θ) in the joint sum:
every node lies in one group; a pair of nodes in the same group lies inside one group; a pair {a, b}
of nodes in different groups occurs twice, as (a, b) in the table of a's group and as (b, a) in the
table of b's group, with the same string θ_{a,b}. -/
theorem prod_groupTerm (N : Net g) (χ : Fin g → Fin K) (z : Fin g → List Bool) (θ : Fin g × Fin g → List Bool) :
    ∏ γ, groupTerm N χ θ γ (fun a => if χ a = γ then z a else []) = jointTerm N χ z θ := by
  have h0 : ∀ γ, groupTerm N χ θ γ (fun a => if χ a = γ then z a else []) = groupTerm N χ θ γ z := by
    intro γ
    unfold groupTerm
    congr 1
    · congr 1
      · refine prod_congr rfl fun a ha => ?_
        simp only [if_pos (mem_filter.1 ha).2]
      · refine prod_congr rfl fun p hp => ?_
        simp only [if_pos (mem_filter.1 hp).2.1, if_pos (mem_filter.1 hp).2.2]
    · refine prod_congr rfl fun p hp => ?_
      simp only [if_pos (mem_filter.1 hp).2.1]
  simp only [h0]
  unfold groupTerm jointTerm
  rw [prod_mul_distrib, prod_mul_distrib, Finset.prod_fiberwise univ χ fun a => N.W a (z a), prod_inside χ fun p => N.Ψ p.1 p.2 (z p.1) (z p.2),
    prod_across χ fun p => N.f p.1 p.2 (z p.1) (θ (pr p.1 p.2))]
  congr 1
  refine prod_congr rfl fun p hp => ?_
  have hlt : p.1 < p.2 := (mem_filter.1 (mem_filter.1 hp).1).2
  simp only [Prod.fst_swap, Prod.snd_swap, (pr_of_lt hlt).1, (pr_of_lt hlt).2]

/-- «Together with the sums inside the tables, this is a sum over all z ∈ ∏_{a ∈ [g]} S_a and over
one string θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair {a,b} of nodes in different groups», from the
sentences before it. -/
theorem stJointSumOf : StJointSumOf := by
  intro hSB hAZ hBl hSI C _ g K hK0 Np c N P B τ S h x L hL
  classical
  obtain ⟨hB1, hB2⟩ := hBl C g K hK0 Np c N P B τ S h x L hL
  calc ∑ Λ ∈ edgeStrings K L, ∏ γ, display Np c N hK0 x γ (star Λ γ)
      = ∑ Λ ∈ (edgeStrings K L).filter (AppendedZero g Np c x), ∏ γ, display Np c N hK0 x γ (star Λ γ) :=
        (Finset.sum_filter_of_ne fun Λ _ hne => by_contra fun hn => hne (hAZ C g K Np c N hK0 x Λ hn)).symm
    _ = ∑ θ ∈ blockStrings N (Paper.grouping hK0 x), ∏ γ, ∑ z ∈ tuples (fun a => Paper.grouping hK0 x a = γ) N.S [], groupTerm N (Paper.grouping hK0 x) θ γ z := by
        refine Finset.sum_nbij (readBlocks Np c hK0 x) ?_ ?_ ?_ ?_
        · intro Λ hΛ
          exact hB1 Λ (mem_filter.1 hΛ).1 (mem_filter.1 hΛ).2
        · intro Λ₁ h₁ Λ₂ h₂ e
          have h₁' := mem_filter.1 (mem_coe.1 h₁)
          have h₂' := mem_filter.1 (mem_coe.1 h₂)
          exact (hB2 _ (hB1 Λ₂ h₂'.1 h₂'.2)).unique ⟨h₁'.1, h₁'.2, e⟩ ⟨h₂'.1, h₂'.2, rfl⟩
        · intro θ hθ
          obtain ⟨Λ, ⟨h1, h2, h3⟩, _⟩ := hB2 θ (mem_coe.1 hθ)
          exact ⟨Λ, mem_coe.2 (mem_filter.2 ⟨h1, h2⟩), h3⟩
        · intro Λ hΛ
          exact prod_congr rfl fun γ _ => display_eq hSB Np c N hK0 x (mem_filter.1 hΛ).2 γ
    _ = ∑ θ ∈ blockStrings N (Paper.grouping hK0 x), ∑ z ∈ Fintype.piFinset N.S, ∏ γ, groupTerm N (Paper.grouping hK0 x) θ γ fun a => if Paper.grouping hK0 x a = γ then z a else [] :=
        sum_congr rfl fun θ _ => hSI g K (Paper.grouping hK0 x) N.S (groupTerm N (Paper.grouping hK0 x) θ)
    _ = ∑ z ∈ Fintype.piFinset N.S, ∑ θ ∈ blockStrings N (Paper.grouping hK0 x), jointTerm N (Paper.grouping hK0 x) z θ := by
        rw [sum_comm]
        exact sum_congr rfl fun z _ => sum_congr rfl fun θ _ => prod_groupTerm N (Paper.grouping hK0 x) z θ

/-- «Together with the sums inside the tables, this is a sum over all z ∈ ∏_{a ∈ [g]} S_a and over
one string θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair {a,b} of nodes in different groups.» -/
theorem stJointSum : StJointSum := stJointSumOf stSameBlock stAppendedZero stBlocks stSumsInside

end Value
