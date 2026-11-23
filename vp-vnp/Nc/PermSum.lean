/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.PermGrid

/-!
# Sums over two families of bits, indexed by maps

The permutations of the grid are replaced by maps: all incidences with the same value of a map share a bit.
-/

namespace Nc

open Finset MvPolynomial

section Fibres

variable {N V : Type*} [Fintype N] [DecidableEq N]

/-- A permutation whose cycles are the fibres of a map. -/
theorem exists_perm_fibres (v : N → V) : ∃ σ : Equiv.Perm N, (∀ n, v (σ n) = v n) ∧
    ∀ s : N → Bool, (∀ n, s (σ n) = s n) → ∀ n m, v n = v m → s n = s m := by
  classical
  have h : ∀ y, ∃ f : Equiv.Perm {n // v n = y}, f.IsCycleOn ((univ : Finset {n // v n = y}) : Set _) :=
    fun y => (Finset.exists_cycleOn univ).imp fun f hf => hf.1
  choose f hf using h
  let e := Equiv.sigmaFiberEquiv v
  let σ : Equiv.Perm N := (e.symm.trans (Equiv.sigmaCongrRight f)).trans e
  have hσ : ∀ n, σ n = (f (v n) ⟨n, rfl⟩).1 := fun n => rfl
  refine ⟨σ, fun n => ?_, fun s hs n m e => ?_⟩
  · rw [hσ]
    exact (f (v n) ⟨n, rfl⟩).2
  · have h1 : ∀ y, ∀ x : {n // v n = y}, s (f y x).1 = s x.1 := by
      rintro y ⟨x, rfl⟩
      rw [← hσ]
      exact hs x
    obtain ⟨i, -, hi⟩ := (hf (v m)).exists_pow_eq (mem_univ ⟨n, e⟩) (mem_univ ⟨m, rfl⟩)
    have h2 : ∀ i : ℕ, s ((f (v m) ^ i) ⟨n, e⟩).1 = s n := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, h1, ih]
    rw [← h2 i, hi]

variable {R : Type*} [CommRing R]

open scoped Classical in
/-- A sum over the functions that are constant on the fibres. -/
theorem sum_invariant [Fintype V] [DecidableEq V] {v : N → V} (hv : Function.Surjective v) {σ : Equiv.Perm N}
    (h1 : ∀ n, v (σ n) = v n)
    (h2 : ∀ s : N → Bool, (∀ n, s (σ n) = s n) → ∀ n m, v n = v m → s n = s m) (Φ : (N → Bool) → R) :
    ∑ s : N → Bool, (if ∀ n, s (σ n) = s n then Φ s else 0) = ∑ x : V → Bool, Φ fun n => x (v n) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun x _ n => x (v n)) ?_ ?_ ?_ ?_
  · intro x _
    simp [h1]
  · intro x _ y _ e
    exact hv.injective_comp_right e
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    refine ⟨fun y => s (Function.surjInv hv y), mem_univ _, ?_⟩
    funext n
    exact h2 s hs _ _ (Function.surjInv_eq hv _)
  · intros
    rfl

/-- A sum over two families of bits is a permanent. -/
theorem exists_grid {K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] (v : N → V) (w : N → K)
    (hv : Function.Surjective v) (hw : Function.Surjective w) :
    ∃ σ ρ : Equiv.Perm N, (∀ n, w (ρ n) = w n) ∧ ∀ (h : R) (_ : h * 2 = 1) (W : N → Bool → Bool → R),
      (gridMatrix h σ ρ W).permanent =
        ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  obtain ⟨σ, s1, s2⟩ := exists_perm_fibres v
  obtain ⟨ρ, r1, r2⟩ := exists_perm_fibres w
  refine ⟨σ, ρ, r1, fun h hh W => ?_⟩
  rw [gridMatrix_permanent h hh]
  refine Eq.trans ?_ (sum_invariant hv s1 s2 fun s => ∑ r : K → Bool, ∏ n, W n (s n) (r (w n)))
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : ∀ n, s (σ n) = s n
  · rw [if_pos hs]
    refine Eq.trans ?_ (sum_invariant hw r1 r2 fun r => ∏ n, W n (s n) (r n))
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [hs]
  · rw [if_neg hs]
    exact Finset.sum_eq_zero fun r _ => if_neg fun hc => hs hc.1

end Fibres

end Nc
