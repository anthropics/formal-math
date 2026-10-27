/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecCrossing_Crossing
public import PaddedDescent.F.Fuel
public import SingleBitPieces.SecCrossing_PolyA
public import ToTuring.Lib.Table
public import SingleBitPieces.SecNetworks_LemGrouping
public import Paper.SecLevel_Recursion
public import ClauseBound.Alg.Grid
import Mathlib.Tactic

/-! # Proposition 3: lemmas on the procedures that present the network
The lemmas hold for any pieces. This folder uses them for a variant of the pieces of Lemma 2 made
from single bits, with ρ = (log 12)/4, which the paper does not use.
The procedure for the weights (a weight by g queries to the tables of the clique) and the function
for the factors (a value in one step) compute the weights and the factors of the row network or the
column network of ι (`W_eq`, `f_eq`). The lemmas after them bound the steps by a·(B + λ)^a·t and the
sizes by S + a·(size c + B + λ)^a, where a = `sideA g`. They serve the sentence «Both networks
satisfy Definition 2 with
… τ = poly(B + λ)» in the proof of Proposition 3. The file follows
proof/machines/StepMachines/Prog/SidePresents.lean, which does the same for the networks of
`Groundwork`; there a value of a factor takes about 4·4^λ steps. The weights and factors of the
network on words are those of proof/rates/ClauseBound/Alg/GridPresents.lean (`gridN_W`, `gridN_f`,
`gridFf_eq`). -/

public section

namespace SingleBitPieces.Level

open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped

namespace Presents

theorem nMemb_self (g : ℕ) (tr : Bool) : nMemb g g tr = g := by cases tr <;> rfl

theorem nParts_self (g : ℕ) (tr : Bool) : nParts g g tr = g := by cases tr <;> rfl

/-- The test of the procedure `sideChk` for the weights is the test of the grid with g rows and g
columns. -/
theorem sideChk_eq {C : Type} (g : ℕ) (tr : Bool) (lam : C → ℕ) (c : C) (y a : ℕ) (z : List Bool) :
    sideChk g tr lam ((c, y), (a, z)) = chkG g g tr (lam c) (a, z) := by
  unfold sideChk chkG
  rw [nMemb_self]
  rfl

/-- What the procedure for the weights (`sideWv` with `sideChk`) computes is the weight of the
network, for any pieces. -/
theorem W_eq (P : PiecesF) {C : Type} {g : ℕ} (tr : Bool) (lam : C → ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (c : C) (y : ℕ) (a : Fin (nParts g g tr))
    {z : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam c) :
    (gridN P [] g g tr 0 (lam c) y Rm).W a z = sideWv g tr (lam c) Rm (sideChk g tr lam ((c, y), (a.val, z))) a z := by
  rw [gridN_W P [] g g tr 0 (lam c) y Rm a hz, sideChk_eq, sideWv]
  by_cases hc : chkG g g tr (lam c) (a.val, z) = true
  · obtain ⟨h1, h2⟩ := (chkG_iff g g tr (lam c) a z).1 hc
    have e0 : ∀ F : ℕ → ℤ, ∏ i ∈ range g, F i = ∏ i ∈ range (nMemb g g tr), F i := fun F => by rw [nMemb_self]
    rw [if_pos hc, Finset.prod_eq_one (s := pairs (Fin (nMemb g g tr))) fun q hq => if_pos (h2 q hq), mul_one, e0, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hn : node g tr a i < g * g := nodeG_lt tr a.2 i.2
    rw [if_pos (h1 i), dif_pos hn]
    have e : (GridNet.gridE g g tr).symm (a, i) = ⟨node g tr a i, hn⟩ := Fin.ext (GridNet.gridE_symm_val g g tr (a, i))
    rw [e]
    congr 1
    funext u
    simp only [sideLabels, Fin.ext_iff]
    rfl
  · rw [if_neg hc]
    rw [chkG_iff, not_and_or] at hc
    rcases hc with h | h
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (mem_univ i) (if_neg hi), zero_mul]
    · push Not at h
      obtain ⟨q, hq, hne⟩ := h
      rw [Finset.prod_eq_zero hq (if_neg hne), mul_zero]

/-- The plain function for the factors computes the factor of the network, for any pieces. -/
theorem f_eq (P : PiecesF) {g : ℕ} (tr : Bool) (ℓ y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * ℓ) (hθ : θ.length = capG P g g tr 0 ℓ y a b) :
    gridFf P [] g g tr 0 ℓ y ((a.val, b.val), (z, θ)) = (gridN P [] g g tr 0 ℓ y Rm).f a b z θ := by
  rw [gridFf_eq, gridN_f P [] g g tr 0 ℓ y Rm hab hz hθ]

/-! ### The arithmetic of the bounds -/

/-- A number with at most b bits. -/
theorem size_int_le {v : ℤ} {b : ℕ} (h : |v| ≤ 2 ^ b) : size v ≤ b + 2 := by
  rw [size_int]
  have h1 : v.natAbs ≤ 2 ^ b := by
    have : ((v.natAbs : ℕ) : ℤ) ≤ ((2 ^ b : ℕ) : ℤ) := by rw [Int.natCast_natAbs]; exact_mod_cast h
    exact_mod_cast this
  have h2 : v.natAbs < 2 ^ (b + 1) := lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have := Nat.size_le.2 h2
  omega

/-- The steps of the weights. -/
theorem time_W (g B lm : ℕ) {t : ℕ} (hl : 1 ≤ lm) (ht : 1 ≤ t) : g * (t + 1) ≤ sideA g * (B + lm) ^ sideA g * t := by
  have h1 : 1 ≤ (B + lm) ^ sideA g := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 * g ≤ sideA g := by unfold sideA; omega
  calc g * (t + 1) ≤ g * (2 * t) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * g * 1 * t := by ring
    _ ≤ sideA g * (B + lm) ^ sideA g * t := Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 h1)

/-- One step. -/
theorem time_f (g B lm : ℕ) {t : ℕ} (hl : 1 ≤ lm) (ht : 1 ≤ t) : 1 ≤ sideA g * (B + lm) ^ sideA g * t := by
  have h1 : 1 ≤ (B + lm) ^ sideA g := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ sideA g := by unfold sideA; omega
  exact Nat.mul_pos (Nat.mul_pos h2 h1) ht

/-- The sizes of the factors: the query, and the value with at most g·B + 2g²λ bits. -/
theorem size_f {C : Type} [HasSize C] (g B S lm : ℕ) (hl : 1 ≤ lm) (c : C) {y a b : ℕ} {z θ : List Bool} {v : ℤ}
    (hy : y < (lm + 1) ^ nRect g) (ha : a < g) (hb : b < g) (hz : z.length = g ^ 3 * lm) (hθ : θ.length ≤ g ^ 2 * lm)
    (hv : |v| ≤ 2 ^ (g * B + g ^ 2 * (2 * lm))) :
    max (size ((c, y), ((a, b), (z, θ)))) (size v) + 1 ≤ S + sideA g * (size c + B + lm) ^ sideA g := by
  refine side_size_of ?_
  have h3 := sideA_mul g (size c + B + lm)
  have hY := size_pattern_le hy
  have hV := size_int_le hv
  have e4 : g ^ 4 * (size c + B + lm) = g ^ 4 * size c + g ^ 4 * B + g ^ 4 * lm := by ring
  have e3 : g ^ 3 * (size c + B + lm) = g ^ 3 * size c + g ^ 3 * B + g ^ 3 * lm := by ring
  have e2 : g ^ 2 * (size c + B + lm) = g ^ 2 * size c + g ^ 2 * B + g ^ 2 * lm := by ring
  have e1 : g * (size c + B + lm) = g * size c + g * B + g * lm := by ring
  have e0 : g ^ 2 * (2 * lm) = 2 * (g ^ 2 * lm) := by ring
  have hg : g ≤ g * lm := Nat.le_mul_of_pos_right _ hl
  have s1 := size_nat_le a
  have s2 := size_nat_le b
  clear hv hy
  have hq : size ((c, y), ((a, b), (z, θ))) + 1 ≤ S + sideA g * (size c + B + lm) := by
    simp only [size_prod, size_bools, hz]
    omega
  have hw : size v + 1 ≤ S + sideA g * (size c + B + lm) := by omega
  exact Nat.succ_le_of_lt (max_lt (Nat.lt_of_succ_le hq) (Nat.lt_of_succ_le hw))

end Presents

open Presents

end SingleBitPieces.Level
