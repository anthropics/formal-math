/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Grids

/-!
# The paper, appendix "All fields and the Hamiltonian cycle polynomial": grids as Hamiltonian cycles
-/

namespace Paper

open Finset MvPolynomial Nc

/-- **Paper: Proposition prop:hc-grid.** "In every commutative ring, the sum in the proposition on grids is HC_S of a
matrix with entries 0, 1 and single values W_n, for every S ≥ 40|N|." -/
theorem prop_hc_grid {R : Type} [CommRing R] {N V K : Type} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V]
    [Fintype K] [DecidableEq K] (v : N → V) (w : N → K) (hv : Function.Surjective v) (hw : Function.Surjective w)
    (W : N → Bool → Bool → R) {S : ℕ} (hS : 40 * Fintype.card N ≤ S) :
    ∃ M : Fin S → Fin S → R, (∀ i j, M i j = 0 ∨ M i j = 1 ∨ ∃ n x r, M i j = W n x r) ∧
      Hc.hcSum M = ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  have hV := Fintype.card_le_of_surjective v hv
  have hK := Fintype.card_le_of_surjective w hw
  let P := Fin (S - (Fintype.card V + Fintype.card K + 37 * Fintype.card N))
  obtain ⟨next, hnext, -⟩ := Finset.exists_cycleOn (Finset.univ : Finset (Hc.Seg N V K P))
  rw [Finset.coe_univ] at hnext
  have hcard : Fintype.card (Hc.Vtx (Hc.Seg N V K P) (Hc.Gad N)) = Fintype.card (Fin S) := by
    rw [Hc.card_gridVtx, Fintype.card_fin, Fintype.card_fin]
    omega
  let e := Fintype.equivOfCardEq hcard
  let T := Hc.gridRow v w next
  refine ⟨fun i j => T.weight (Hc.gridWeight W) (e.symm i) (e.symm j), fun i j => ?_,
    (Hc.hcSum_equiv e.symm (T.weight (Hc.gridWeight W))).trans (Hc.hcSum_grid hv hw hnext W)⟩
  show T.weight (Hc.gridWeight W) (e.symm i) (e.symm j) = 0 ∨ T.weight (Hc.gridWeight W) (e.symm i) (e.symm j) = 1 ∨
    ∃ n x r, T.weight (Hc.gridWeight W) (e.symm i) (e.symm j) = W n x r
  generalize e.symm i = a, e.symm j = b
  rcases a with s | ⟨g, side⟩ | g
  · simp only [Hc.Row.weight]
    by_cases hex : ∃ o : Hc.Opt s, T.place ⟨s, o⟩ 0 = b
    · obtain ⟨o, ho⟩ := hex
      rw [Finset.sum_eq_single o]
      · cases s with
        | edge n => exact Or.inr (Or.inr ⟨n, o.1, o.2, rfl⟩)
        | _ => exact Or.inr (Or.inl rfl)
      · intro o' ho' hne
        exact absurd (Hc.Row.place_zero_injective (Hc.gridRow_noParallel hv hw) ((mem_filter.1 ho').2.trans ho.symm)) hne
      · exact fun h => absurd (mem_filter.2 ⟨mem_univ o, ho⟩) h
    · exact Or.inl (Finset.sum_eq_zero fun o ho => absurd ⟨o, (mem_filter.1 ho).2⟩ hex)
  · simp only [Hc.Row.weight]
    split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · simp only [Hc.Row.weight]
    split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl



/-- The affine form of Proposition prop:hc-grid: the Hamiltonian cycle polynomial is complete for grid sums in every
characteristic. -/
theorem gridComplete_hc (F : Type) [Field F] : GridComplete F (genHC F) 40 := by
  intro ι N V K _ _ _ _ _ _ v w hv hw W o hW S hS
  obtain ⟨M, hM, hp⟩ := prop_hc_grid v w hv hw W hS
  refine ⟨fun q => M q.1 q.2, fun q => ?_, by rw [Hc.aeval_genHC]; exact hp⟩
  rcases hM q.1 q.2 with h | h | ⟨n, x, r, h⟩
  · exact Or.inl ⟨0, h.trans C_0.symm⟩
  · exact Or.inl ⟨1, h.trans C_1.symm⟩
  · show IsAffine (M q.1 q.2)
    rw [h]
    exact isAffine_of_mem (hW n x r)

/-- "With HC in place of PERM, the corollary on clause sums holds in every characteristic." -/
theorem cor_clauses_hc {F : Type} [Field F] {ι V K : Type} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
    (lits : K → List (V × Bool)) (hne : ∀ κ, lits κ ≠ []) (hocc : ∀ b, ∃ κ, ∃ l ∈ lits κ, l.1 = b)
    (wt : K → MvPolynomial ι F) (hwt : ∀ κ, (∃ i, wt κ = X i) ∨ ∃ a, wt κ = C a) {S : ℕ}
    (hS : 40 * ∑ κ, (lits κ).length ≤ S) :
    ∃ M : Fin S × Fin S → MvPolynomial ι F, (∀ q, IsAffine (M q)) ∧ aeval M (genHC F S) = clauseSum lits wt :=
  clauses_of_complete (gridComplete_hc F) lits hne hocc wt hwt hS

end Paper
