/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Ov.Core.Equi

/-!
# Spectral points: the basic calculus

Paper: the subsection "Tensors". A spectral point F is multiplicative and
monotone for restriction, F(s) ≤ F(t_1) + … + F(t_m) if s = t_1 + … + t_m, and 1 ≤ F(t) ≤ rank of t for
a tensor t that is not 0. A spectral point can be pulled back along a map g of sets of parties (the
paper's t ↦ φ(gt)).
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Rank, in coordinates: a tensor has rank at most r if and only if it is a sum of r products of
vectors. -/
theorem rankLE_iff [Nonempty I] {t : Ten K I} {r : ℕ} :
    RankLE t r ↔ ∃ u : Fin r → ∀ p, t.ι p → K, ∀ x, t.val x = ∑ s, ∏ p, u s p (x p) := by
  have key : ∀ (L : ∀ p, t.ι p → Fin r → K) (x : ∀ p, t.ι p),
      (∑ y : I → Fin r, (∏ p, L p (x p) (y p)) * (if ∀ i j, y i = y j then 1 else 0)) =
        ∑ s, ∏ p, L p (x p) s := by
    intro L x
    let p₀ : I := Classical.arbitrary I
    symm
    refine Finset.sum_of_injOn (fun s _ => s) (fun a _ b _ h => congr_fun h p₀) (fun _ _ => by simp)
      (fun y _ hy => ?_) (fun s _ => by simp)
    rw [if_neg, mul_zero]
    intro h
    exact hy ⟨y p₀, by simp, funext fun p => h p₀ p⟩
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨fun s p a => L p a s, fun x => (hL x).trans (key L x)⟩
  · rintro ⟨u, hu⟩
    exact ⟨fun p a s => u s p a, fun x => (hu x).trans (key (fun p a s => u s p a) x).symm⟩

/-- A tensor of rank at most r is a sum of r restrictions of 1. -/
theorem RankLE.sumRestr [Nonempty I] {t : Ten K I} {r : ℕ} (h : RankLE t r) :
    SumRestr t (fun _ : Fin r => (1 : Ten K I)) := by
  obtain ⟨u, hu⟩ := rankLE_iff.1 h
  refine sumRestr_iff.2 ⟨fun s x => ∏ p, u s p (x p), hu, fun s => ?_⟩
  exact Restr.of_map (fun p a => u s p a) (fun _ _ => ()) fun x => (mul_one _).symm

/-- Every tensor has a rank bound: the number of its entries. -/
theorem rankLE_card [Nonempty I] (t : Ten K I) : RankLE t (Fintype.card (∀ p, t.ι p)) := by
  classical
  let p₀ : I := Classical.arbitrary I
  let e := (Fintype.equivFin (∀ p, t.ι p)).symm
  refine rankLE_iff.2 ⟨fun s p a => if a = e s p then (if p = p₀ then t.val (e s) else 1) else 0,
    fun x => ?_⟩
  rw [Finset.sum_eq_single (e.symm x)]
  · simp
  · intro s _ hs
    have : x ≠ e s := fun h => hs (by rw [h]; simp)
    obtain ⟨p, hp⟩ := Function.ne_iff.1 this
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)
  · simp

end Ten

namespace Spec

open Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (F : Spec K I)

/-- F is monotone for restriction. -/
theorem mono {s t : Ten K I} (h : Restr s t) : F.F s ≤ F.F t := by
  simpa using F.le_sum s _ h.sumRestr

/-- Equivalent tensors have the same price. -/
theorem congr {s t : Ten K I} (h : Equi s t) : F.F s = F.F t :=
  le_antisymm (F.mono h.1) (F.mono h.2)

/-- F of the product of a family indexed by 0, …, n-1. -/
theorem prod_fin {n : ℕ} (b : Fin n → Ten K I) : F.F (Ten.prod b) = ∏ k, F.F (b k) := by
  induction n with
  | zero => rw [F.congr (Equi.prod_empty b), F.one]; simp
  | succ n ih => rw [F.congr (Equi.prod_fin_succ b), F.mul, ih, Fin.prod_univ_succ]

/-- F of the product of a family. -/
theorem prod {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I) :
    F.F (Ten.prod b) = ∏ k, F.F (b k) := by
  rw [F.congr (Equi.prod_reindex b (Fintype.equivFin κ).symm), F.prod_fin]
  exact Fintype.prod_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

/-- F of a power. -/
theorem kpow (t : Ten K I) (k : ℕ) : F.F (Ten.kpow t k) = F.F t ^ k := by
  rw [kpow_eq_prod, F.prod]; simp

/-- F is 0 at a tensor whose array is 0. -/
theorem zero {t : Ten K I} (h : ∀ x, t.val x = 0) : F.F t = 0 := by
  refine le_antisymm ?_ (F.nonneg t)
  simpa using F.le_sum t (fun k : Empty => k.elim) (SumRestr.of_zero h _)

/-- F is at least 1 at a tensor with an entry that is not 0. -/
theorem one_le [Nonempty I] {t : Ten K I} {y : ∀ p, t.ι p} (h : t.val y ≠ 0) : 1 ≤ F.F t := by
  rw [← F.one]
  exact F.mono (Restr.one_le h)

/-- F is at most the rank. -/
theorem le_rank [Nonempty I] {t : Ten K I} {r : ℕ} (h : RankLE t r) : F.F t ≤ r := by
  simpa [F.one] using F.le_sum t _ h.sumRestr

/-- F is at most the number of entries. -/
theorem le_card [Nonempty I] (t : Ten K I) : F.F t ≤ Fintype.card (∀ p, t.ι p) :=
  F.le_rank (rankLE_card t)

/-- F is subadditive for sums of arrays. -/
theorem le_sum_val {κ : Type} [Fintype κ] (s : Ten K I) (v : κ → (∀ p, s.ι p) → K)
    (h : ∀ x, s.val x = ∑ k, v k x) : F.F s ≤ ∑ k, F.F (s.withVal (v k)) :=
  F.le_sum s _ (SumRestr.of_withVal s v h)

/-- A restriction of a product costs at most the product of the prices. -/
theorem le_mul {s t u : Ten K I} (h : Restr s (t * u)) : F.F s ≤ F.F t * F.F u := by
  rw [← F.mul]; exact F.mono h

/-- A restriction of the product of a family costs at most the product of the prices. -/
theorem le_prod {κ : Type} [Fintype κ] [DecidableEq κ] {s : Ten K I} {b : κ → Ten K I}
    (h : Restr s (Ten.prod b)) : F.F s ≤ ∏ k, F.F (b k) := by
  rw [← F.prod]; exact F.mono h

/-- The pull-back of a spectral point along a map π of parties: a tensor over J costs what it costs
if the leg j is held by π j. -/
def pull (F : Spec K I) (π : J → I) : Spec K J where
  F t := F.F (Ten.push π t)
  nonneg _ := F.nonneg _
  one := by rw [F.congr (Equi.push_one π), F.one]
  mul s t := by rw [F.congr (Equi.push_mul π s t), F.mul]
  le_sum s b h := F.le_sum _ _ (h.push π)

@[simp] theorem pull_F (π : J → I) (t : Ten K J) : (F.pull π).F t = F.F (Ten.push π t) := rfl

end Spec

end Ov
