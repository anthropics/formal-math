/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Hc.Grid

/-!
# The paper, section "The flat case": sums over bits as permanents
-/

namespace Paper

open Finset MvPolynomial Nc

/-- The fixed entries of the grid matrix and the sums of weights of one row of clauses. -/
def GridEntry {R N K : Type} [CommRing R] (h : R) (w : N → K) (W : N → Bool → Bool → R) (z : R) : Prop :=
  z = 0 ∨ z = 1 ∨ z = -1 ∨ z = h ∨ z = -h ∨ ∃ k, z ∈ AddSubmonoid.closure {y : R | ∃ n x r, w n = k ∧ y = W n x r}

/-- **Paper: Proposition prop:grid.** "Let R be a commutative ring with an element ½, let v : N → V, w : N → K be
surjections of finite sets, and let W_n(x,r) ∈ R. Then ∑_x ∑_r ∏_n W_n(x_{v(n)}, r_{w(n)}) is the permanent of an S×S
matrix, for every S ≥ 3|N|, whose entries are 0, ±1, ±½ and sums of values W_n with the same w(n)." -/
theorem prop_grid {R : Type} [CommRing R] (h : R) (hh : h * 2 = 1) {N V K : Type} [Fintype N] [DecidableEq N]
    [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] (v : N → V) (w : N → K) (hv : Function.Surjective v)
    (hw : Function.Surjective w) (W : N → Bool → Bool → R) {S : ℕ} (hS : 3 * Fintype.card N ≤ S) :
    ∃ M : Matrix (Fin S) (Fin S) R, (∀ i j, GridEntry h w W (M i j)) ∧
      M.permanent = ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  obtain ⟨σ, ρ, hρ, H⟩ := exists_grid (R := R) v w hv hw
  have hcard : Fintype.card (N × Option Bool) ≤ S := by
    refine le_trans (le_of_eq ?_) hS
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_bool]
    ring
  obtain ⟨M, hM, hent⟩ := exists_permanent_fin (gridMatrix h σ ρ W) hcard
  refine ⟨M, fun i j => ?_, hM.trans (H h hh W)⟩
  rcases hent i j with (h0 | h1) | ⟨⟨n, q⟩, d, he⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  rw [he]
  have hh2 : h + h = 1 := by rw [← mul_two]; exact hh
  obtain ⟨n', q'⟩ := d
  rcases q with _ | _ | _
  · rcases q' with _ | _ | _ <;> by_cases e1 : n' = n <;> by_cases e2 : n' = σ n <;>
      simp [GridEntry, gridMatrix, ind, e1, e2, Prod.ext_iff] <;> simp_all
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨w n, ?_⟩))))
    have mem : ∀ (m : N) (c₀ : N × Option Bool) x r, w m = w n →
        ind c₀ (W m x r) (n', q') ∈ AddSubmonoid.closure {y : R | ∃ m x r, w m = w n ∧ y = W m x r} := by
      intro m c₀ x r hm
      unfold ind
      split_ifs
      · exact AddSubmonoid.subset_closure ⟨m, x, r, hm, rfl⟩
      · exact zero_mem _
    exact add_mem (add_mem (add_mem (mem n _ _ _ rfl) (mem n _ _ _ rfl)) (mem _ _ _ _ (hρ n))) (mem _ _ _ _ (hρ n))
  · rcases q' with _ | _ | _ <;> by_cases e1 : n' = n <;> by_cases e2 : n' = σ n <;>
      simp [GridEntry, gridMatrix, ind, e1, e2, Prod.ext_iff] <;> simp_all


/-- The affine form of Proposition prop:grid: if the weights at an incidence are affine in the variable of its second
class, the matrix has entries that are affine in one variable each. So the permanent is complete for grid sums. -/
theorem gridComplete_perm {F : Type} [Field F] (h2 : (2 : F) ≠ 0) : GridComplete F (genPerm F) 3 := by
  intro ι N V K _ _ _ _ _ _ v w hv hw W o hW S hS
  have hC2 : (C (2⁻¹ : F) : MvPolynomial ι F) * 2 = 1 := by
    rw [← map_ofNat C 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
  obtain ⟨M, hM, hp⟩ := prop_grid (C (2⁻¹ : F)) hC2 v w hv hw W hS
  refine ⟨fun q => M q.1 q.2, fun q => ?_, by rw [← hp, ← aeval_genPerm]⟩
  rcases hM q.1 q.2 with h | h | h | h | h | ⟨k, h⟩
  · exact Or.inl ⟨0, h.trans C_0.symm⟩
  · exact Or.inl ⟨1, h.trans C_1.symm⟩
  · exact Or.inl ⟨-1, h.trans (by rw [map_neg, C_1])⟩
  · exact Or.inl ⟨2⁻¹, h⟩
  · exact Or.inl ⟨-2⁻¹, h.trans (by rw [map_neg])⟩
  · refine isAffine_of_mem (o := o k) ?_
    refine (AddSubmonoid.closure_le (S := (affIn (F := F) (o k)).toAddSubmonoid)).2 ?_ h
    rintro _ ⟨n, x, r, rfl, rfl⟩
    exact hW n x r

/-- A clause sum: the sum over the bits of the product over the clauses of the weight of the clause if all its
literals hold, and 1 otherwise. -/
noncomputable def clauseSum {R V K : Type} [CommRing R] [Fintype V] [DecidableEq V] [Fintype K]
    (lits : K → List (V × Bool)) (wt : K → R) : R :=
  ∑ x : V → Bool, ∏ κ, if ∀ l ∈ lits κ, x l.1 = l.2 then wt κ else 1

/-- A clause sum is a projection of every family that is complete for grid sums. -/
theorem clauses_of_complete {F : Type} [Field F] {G : ∀ S, MvPolynomial (Fin S × Fin S) F} {c : ℕ}
    (hG : GridComplete F G c) {ι V K : Type} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
    (lits : K → List (V × Bool)) (hne : ∀ κ, lits κ ≠ []) (hocc : ∀ b, ∃ κ, ∃ l ∈ lits κ, l.1 = b)
    (wt : K → MvPolynomial ι F) (hwt : ∀ κ, (∃ i, wt κ = X i) ∨ ∃ a, wt κ = C a) {S : ℕ}
    (hS : c * ∑ κ, (lits κ).length ≤ S) :
    ∃ M : Fin S × Fin S → MvPolynomial ι F, (∀ q, IsAffine (M q)) ∧ aeval M (G S) = clauseSum lits wt := by
  classical
  let N := Σ κ, Fin (lits κ).length
  let v : N → V := fun n => ((lits n.1).get n.2).1
  let W : N → Bool → Bool → MvPolynomial ι F := fun n x r =>
    if r then (if x = ((lits n.1).get n.2).2 then (if n.2.1 = 0 then wt n.1 - 1 else 1) else 0) else 1
  let o : K → Option ι := fun κ => if h : ∃ i, wt κ = X i then some h.choose else none
  have hwt' : ∀ κ, wt κ ∈ affIn (F := F) (o κ) := by
    intro κ
    by_cases h : ∃ i, wt κ = X i
    · have key : ∀ i, wt κ = X i → wt κ ∈ affIn (F := F) (some i) := fun i e => by
        rw [e]
        exact Submodule.subset_span (by simp)
      rw [show o κ = some h.choose from dif_pos h]
      exact key _ h.choose_spec
    · obtain ⟨a, ha⟩ := (hwt κ).resolve_left h
      rw [ha]
      exact C_mem_affIn _ _
  have hv : Function.Surjective v := by
    intro b
    obtain ⟨κ, l, hl, rfl⟩ := hocc b
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
    exact ⟨⟨κ, i⟩, rfl⟩
  have hW : ∀ n x r, W n x r ∈ affIn (F := F) (o n.1) := fun n x r => by
    simp only [W]
    split_ifs
    · exact Submodule.sub_mem _ (hwt' _) (one_mem_affIn _)
    · exact one_mem_affIn _
    · exact Submodule.zero_mem _
    · exact one_mem_affIn _
  obtain ⟨M, hM, he⟩ := hG v (fun n : N => n.1) hv (fun κ => ⟨⟨κ, ⟨0, List.length_pos_iff.2 (hne κ)⟩⟩, rfl⟩) W o
    hW S (by simpa [N] using hS)
  · refine ⟨M, hM, he.trans (Finset.sum_congr rfl fun x _ => ?_)⟩
    have hp : ∀ r : K → Bool, ∏ n : N, W n (x (v n)) (r n.1) =
        ∏ κ, ∏ i : Fin (lits κ).length, W ⟨κ, i⟩ (x (v ⟨κ, i⟩)) (r κ) := fun r => Fintype.prod_sigma _
    simp only [hp]
    rw [← Fintype.prod_sum fun κ b => ∏ i : Fin (lits κ).length, W ⟨κ, i⟩ (x (v ⟨κ, i⟩)) b]
    refine Finset.prod_congr rfl fun κ _ => ?_
    have hpos := List.length_pos_iff.2 (hne κ)
    rw [Fintype.sum_bool]
    simp only [W, if_true, Bool.false_eq_true, if_false, Finset.prod_const_one]
    by_cases hall : ∀ l ∈ lits κ, x l.1 = l.2
    · rw [if_pos hall]
      have : ∀ i : Fin (lits κ).length, x ((lits κ).get i).1 = ((lits κ).get i).2 := fun i => hall _ (List.get_mem _ _)
      simp only [v, this, if_true]
      rw [Finset.prod_eq_single (⟨0, hpos⟩ : Fin (lits κ).length)]
      · simp
      · intro i _ hi
        exact if_neg fun h => hi (Fin.ext h)
      · simp
    · rw [if_neg hall]
      push Not at hall
      obtain ⟨l, hl, hne'⟩ := hall
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
      rw [Finset.prod_eq_zero (mem_univ i) (if_neg hne'), zero_add]

/-- **Paper: Corollary cor:clauses.** "Let 2 ≠ 0 in k. A clause sum with N literals in all, whose weights are constants
or variables, is the permanent of an S×S matrix, S ≥ 3N, with entries that are affine in one variable each." -/
theorem cor_clauses {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {ι V K : Type} [Fintype V] [DecidableEq V] [Fintype K]
    [DecidableEq K] (lits : K → List (V × Bool)) (hne : ∀ κ, lits κ ≠ []) (hocc : ∀ b, ∃ κ, ∃ l ∈ lits κ, l.1 = b)
    (wt : K → MvPolynomial ι F) (hwt : ∀ κ, (∃ i, wt κ = X i) ∨ ∃ a, wt κ = C a) {S : ℕ}
    (hS : 3 * ∑ κ, (lits κ).length ≤ S) :
    ∃ M : Matrix (Fin S) (Fin S) (MvPolynomial ι F), (∀ i j, IsAffine (M i j)) ∧
      M.permanent = clauseSum lits wt := by
  obtain ⟨M, hM, he⟩ := clauses_of_complete (gridComplete_perm h2) lits hne hocc wt hwt hS
  exact ⟨Matrix.of fun i j => M (i, j), fun i j => hM (i, j), by rw [← aeval_genPerm, ← he]; rfl⟩


end Paper
