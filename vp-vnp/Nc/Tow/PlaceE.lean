/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Net

/-!
# Places of the nodes
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset

variable {h b D J r AA : ℕ}

/-- The node of a base party. -/
def baseNd (T : Tower h b D J r) (ch : Fin AA ↪ T.X 0) : Fin AA ↪ Nd T where
  toFun a := nd T 0 (Nat.zero_le _) (ch a)
  inj' a c hac := ch.injective (nd_inj.1 hac)

/-- The number of extra parties. -/
def extra (T : Tower h b D J r) (AA : ℕ) : ℕ := Fintype.card (Nd T) - AA

/-- **Places exist.** -/
theorem exists_place (T : Tower h b D J r) (ch : Fin AA ↪ T.X 0) : Nonempty (Place T ch (extra T AA)) := by
  classical
  have hle : AA ≤ Fintype.card (Nd T) := by
    have := Fintype.card_le_of_embedding (baseNd T ch)
    rwa [Fintype.card_fin] at this
  -- the base nodes and the others
  let S : Finset (Nd T) := univ.map (baseNd T ch)
  have hS : S.card = AA := by rw [card_map, card_univ, Fintype.card_fin]
  have hc : Fintype.card {ν : Nd T // ν ∉ S} = extra T AA := by
    rw [Fintype.card_subtype_compl (fun ν => ν ∈ S), Fintype.card_coe, hS]
    rfl
  let e1 : {ν : Nd T // ν ∈ S} ≃ Fin AA :=
    (Equiv.ofBijective (fun a : Fin AA => (⟨baseNd T ch a, mem_map_of_mem _ (mem_univ a)⟩ : {ν : Nd T // ν ∈ S})) (by
      constructor
      · intro a c hac
        exact (baseNd T ch).injective (congrArg Subtype.val hac)
      · rintro ⟨ν, hν⟩
        obtain ⟨a, -, ha⟩ := mem_map.1 hν
        exact ⟨a, Subtype.ext ha⟩)).symm
  let e2 : {ν : Nd T // ν ∉ S} ≃ Fin (extra T AA) := Fintype.equivFinOfCardEq hc
  let e : Nd T ≃ Fin (AA + extra T AA) :=
    (Equiv.sumCompl (fun ν => ν ∈ S)).symm.trans ((Equiv.sumCongr e1 e2).trans finSumFinEquiv)
  refine ⟨⟨e, fun a => ?_⟩⟩
  have hmem : baseNd T ch a ∈ S := mem_map_of_mem _ (mem_univ a)
  have h1 : (Equiv.sumCompl (fun ν => ν ∈ S)).symm (baseNd T ch a) = Sum.inl ⟨baseNd T ch a, hmem⟩ :=
    Equiv.sumCompl_symm_apply_of_pos hmem
  have h2 : e1 ⟨baseNd T ch a, hmem⟩ = a := by
    rw [Equiv.symm_apply_eq]
    rfl
  change finSumFinEquiv ((Equiv.sumCongr e1 e2) ((Equiv.sumCompl (fun ν => ν ∈ S)).symm (baseNd T ch a))) = _
  rw [h1, Equiv.sumCongr_apply, Sum.map_inl, h2, finSumFinEquiv_apply_left]

end Nc.Tow
