/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Value.Words

/-! # The value of the (K, λ)-clique: from two copies on every edge to one string per edge

After Definition 3 the paper says that only the terms in which the two copies on every edge agree
contribute, and that the value is a sum over one string in {0,1}^λ per edge.
This file proves the statements of the first part of proof/networks/Value/Defs.lean, directly on the
sum that defines the value of the clique as a network:
* `stSumOverSettings`: the value is by definition a sum over the settings z = (z_w) of the nodes;
* `stCopiesMustAgree`: a term in which two copies differ is 0, and in the other terms the factors of
  the edges are 1;
* `stOneStringPerEdge`: the choices of settings in which all copies agree are the choices of one
  string per edge. A setting z_w is the concatenation of its K − 1 copies, so for given copies there
  is exactly one setting (`SecNetworks.sum_settings`, read with an indicator as summand);
* `stCliqueValueOf`, `stCliqueValue`: the sentence itself, from these three. -/

public section

namespace Value

open Groundwork Groundwork.Prog Finset Eight.SecNetworks

/-- The value of a (K, λ)-clique is by definition a sum over the settings of its nodes. -/
theorem stSumOverSettings : StSumOverSettings := fun _ _ _ => rfl

/-- Only the terms in which the two copies on every edge agree contribute. -/
theorem stCopiesMustAgree : StCopiesMustAgree := by
  intro K lam W z
  constructor
  · intro h
    obtain ⟨p, hp⟩ := not_forall.1 h
    obtain ⟨hp, hne⟩ := Classical.not_imp.1 hp
    unfold cliqueTerm
    rw [Finset.prod_eq_zero hp (if_neg hne), mul_zero]
  · intro h
    unfold cliqueTerm
    rw [Finset.prod_eq_one fun p hp => if_pos (h p hp), mul_one]

/-- The choices of settings in which all copies agree are the choices of one string per edge. -/
theorem stOneStringPerEdge : StOneStringPerEdge := by
  intro K lam
  constructor
  · intro Λ hΛ
    refine (existsUnique_congr fun z => ?_).2 (existsUnique_pi (fun (w : Fin K) (zw : List Bool) => zw ∈ words ((K - 1) * lam) ∧ ∀ w' : Fin K, w' ≠ w → copyAt lam w w' zw = star Λ w w') fun w => ?_)
    · rw [Fintype.mem_piFinset]
      exact forall_and.symm
    · have H := existsUnique_of_sum (words ((K - 1) * lam)) (tuples (fun w' => w' ≠ w) (fun _ => words lam) []) (fun z (w' : Fin K) => if w' = w then [] else copyAt lam w w' z)
        (sum_settings lam w) (fun t' => ∀ w' : Fin K, w' ≠ w → t' w' = star Λ w w')
        (existsUnique_tuple _ _ _ (star Λ w) fun w' hw' => ((mem_tuples _ _ _ _).1 (star_mem hΛ w) w').1 hw')
      refine (existsUnique_congr fun zw => and_congr_right fun _ => forall_congr' fun w' => imp_congr_right fun hw' => ?_).1 H
      simp only [if_neg hw']
  · intro z hz hag
    rw [Fintype.mem_piFinset] at hz
    refine ⟨fun p => if p.1 < p.2 then copyAt lam p.1 p.2 (z p.1) else [], (mem_tuples _ _ _ _).2 fun p => ⟨fun hp => ?_, fun hp => if_neg hp⟩, fun w w' hne => ?_⟩
    · rw [if_pos hp, mem_words]
      exact length_copyAt p.1 p.2 hp.ne' (mem_words.1 (hz p.1))
    · rcases lt_or_gt_of_ne hne with h | h
      · change _ = (fun p : Fin K × Fin K => if p.1 < p.2 then copyAt lam p.1 p.2 (z p.1) else []) (pr w w')
        rw [(pr_of_lt h).2]
        exact ((if_pos h).trans (hag (w', w) (mem_filter.2 ⟨mem_univ _, h⟩))).symm
      · change _ = (fun p : Fin K × Fin K => if p.1 < p.2 then copyAt lam p.1 p.2 (z p.1) else []) (pr w w')
        rw [(pr_of_lt h).1]
        exact (if_pos h).symm

/-- The value as a sum over one string per edge, from the three statements before it: restrict the
sum over the settings to the terms in which all copies agree, and change the variable. -/
theorem stCliqueValueOf : StCliqueValueOf := by
  intro h1 h2 h3 K lam W
  classical
  obtain ⟨hA, hB⟩ := h3 K lam
  rw [h1 K lam (tablesOn lam W), ← Finset.sum_filter_of_ne (p := CopiesAgree lam) fun z _ hne => by_contra fun hn => hne ((h2 K lam (tablesOn lam W) z).1 hn)]
  symm
  have hag : ∀ (Λ : Fin K × Fin K → List Bool) (z : Fin K → List Bool), (∀ w w' : Fin K, w' ≠ w → copyAt lam w w' (z w) = star Λ w w') → CopiesAgree lam z := by
    intro Λ z hz p hp
    have hlt : p.1 < p.2 := (mem_filter.1 hp).2
    rw [hz p.1 p.2 hlt.ne', hz p.2 p.1 hlt.ne, star_swap]
  refine Finset.sum_bij (fun Λ hΛ => (hA Λ hΛ).exists.choose) ?_ ?_ ?_ ?_
  · intro Λ hΛ
    have hs := (hA Λ hΛ).exists.choose_spec
    exact mem_filter.2 ⟨hs.1, hag Λ _ hs.2⟩
  · intro Λ₁ h₁ Λ₂ h₂ e
    have hs₁ := (hA Λ₁ h₁).exists.choose_spec
    have hs₂ := (hA Λ₂ h₂).exists.choose_spec
    rw [e] at hs₁
    funext p
    by_cases hp : p.1 < p.2
    · have e₁ := (hs₁.2 p.1 p.2 hp.ne').symm.trans (hs₂.2 p.1 p.2 hp.ne')
      change Λ₁ (pr p.1 p.2) = Λ₂ (pr p.1 p.2) at e₁
      rw [(pr_of_lt hp).1] at e₁
      exact e₁
    · rw [((mem_tuples _ _ _ _).1 h₁ p).2 hp, ((mem_tuples _ _ _ _).1 h₂ p).2 hp]
  · intro z hz
    obtain ⟨hz1, hz2⟩ := mem_filter.1 hz
    obtain ⟨Λ, hΛ, hrel⟩ := hB z hz1 hz2
    exact ⟨Λ, hΛ, (hA Λ hΛ).unique (hA Λ hΛ).exists.choose_spec ⟨hz1, hrel⟩⟩
  · intro Λ hΛ
    have hs := (hA Λ hΛ).exists.choose_spec
    rw [(h2 K lam (tablesOn lam W) _).2 (hag Λ _ hs.2)]
    refine Finset.prod_congr rfl fun w _ => ?_
    unfold tablesOn
    congr 1
    funext w'
    by_cases hw : w' = w
    · rw [if_pos hw, hw]
      exact ((mem_tuples _ _ _ _).1 (star_mem hΛ w) w).2 (by simp)
    · rw [if_neg hw, hs.2 w w' hw]

/-- The remark after Definition 3: the value of the clique is the sum, over one string in {0,1}^λ
per edge, of ∏_{w∈[K]} W_w at the strings on the edges at w. -/
theorem stCliqueValue : StCliqueValue := stCliqueValueOf stSumOverSettings stCopiesMustAgree stOneStringPerEdge

end Value
