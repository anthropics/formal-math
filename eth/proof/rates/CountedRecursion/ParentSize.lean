/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.CallParts
import ClauseBound.Gen.RateAux
import Mathlib.Tactic

/-! # The size of a parent

The procedure that computes an entry of a callee's tables keeps the parent (K, g, λ, B, the lists 𝓘,
c^row_i, c^col_i, the direction, the numbers y of the pattern and x of the grouping) in all its
states. `size_mkParent_le`: its size is at most Ξ^{2c+4}, Ξ = g²(λ + B). By Definition 7 (c) the
list of 𝓘 has at most (2λ)^c elements of at most (2λ)^c bits;
c^row_i, c^col_i ≤ 2λ; y < |𝓘|^{|ℛ|} has at most (2λ)^c·g⁴ bits and x < K^g at most g² bits. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- The size of a list of at most k elements of size at most s. -/
theorem size_list_bound {α : Type} [HasSize α] {l : List α} {k s : ℕ} (hl : l.length ≤ k) (hs : ∀ x ∈ l, size x ≤ s) : size l ≤ k * (s + 1) + 1 := by
  rw [size_list]
  have h := List.sum_le_card_nsmul (l.map fun x => size x + 1) (s + 1) fun v hv => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
    exact Nat.succ_le_succ (hs x hx)
  rw [List.length_map, smul_eq_mul] at h
  exact Nat.succ_le_succ (h.trans (Nat.mul_le_mul_right _ hl))

/-- The size of n in unary. -/
theorem size_unary_eq (n : ℕ) : size (unary n) = 2 * n + 1 := by
  unfold unary
  rw [size_list, List.map_replicate, List.sum_replicate, size_unit, smul_eq_mul]
  omega

/-- A number below 2^k has size at most k + 1. -/
theorem size_nat_of_lt {n k : ℕ} (h : n < 2 ^ k) : size n ≤ k + 1 := by
  rw [size_nat]
  exact Nat.succ_le_succ (Nat.size_le.2 h)

/-- The three lists: at most (2λ)^c elements each; an element of 𝓘 has at most (2λ)^c bits, and
c^row_i, c^col_i ≤ 2λ. -/
theorem size_listsOf_le {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {lam : ℕ} (hlam : 1 ≤ lam) :
    size (listsOf D lam) ≤ ((2 * lam) ^ c * ((2 * lam) ^ c + 1 + 1) + 1) + (((2 * lam) ^ c * (2 * lam + 1 + 1) + 1) + ((2 * lam) ^ c * (2 * lam + 1 + 1) + 1)) := by
  have hcard : ((D.fam lam).I.sort).length ≤ (2 * lam) ^ c := by
    rw [Finset.length_sort]
    exact hS.is.card lam hlam
  have h1 : size ((D.fam lam).I.sort) ≤ (2 * lam) ^ c * ((2 * lam) ^ c + 1 + 1) + 1 := size_list_bound hcard fun i hi => by
    have hi' : |i| < 2 ^ (2 * lam) ^ c := hS.is.size_I lam hlam i ((Finset.mem_sort _).1 hi)
    have h2 : i.natAbs < 2 ^ (2 * lam) ^ c := by
      have : ((i.natAbs : ℕ) : ℤ) < ((2 ^ (2 * lam) ^ c : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]
        exact_mod_cast hi'
      exact_mod_cast this
    rw [size_int]
    exact Nat.succ_le_succ (Nat.size_le.2 h2)
  have h2 : ∀ tr, size (((D.fam lam).I.sort).map fun i => D.cap lam tr i) ≤ (2 * lam) ^ c * (2 * lam + 1 + 1) + 1 := fun tr =>
    size_list_bound (by rw [List.length_map]; exact hcard) fun v hv => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
      exact (size_nat_of_lt Nat.lt_two_pow_self).trans (Nat.succ_le_succ (hS.short lam tr i))
  exact Nat.add_le_add h1 (Nat.add_le_add (h2 false) (h2 true))

/-- The arithmetic: with X = g²(λ + B) ≥ 8 and m = (2λ)^c ≤ X^c. -/
theorem parent_arith {X m c K g lam B R sy sx sl : ℕ} (hX : 8 ≤ X) (hm : m ≤ X ^ c) (hK : K ≤ X) (hg : g ≤ X) (hlam : 2 * lam ≤ X) (hB : B ≤ X) (hR : R ≤ X * X) (hsy : sy ≤ m * R + 1) (hsx : sx ≤ X + 1)
    (hsl : sl ≤ (m * (m + 1 + 1) + 1) + ((m * (2 * lam + 1 + 1) + 1) + (m * (2 * lam + 1 + 1) + 1))) :
    (2 * K + 1 + (2 * g + 1)) + ((2 * lam + 1 + (2 * B + 1)) + (sl + (1 + (sy + sx)))) ≤ X ^ (2 * c + 4) := by
  have hX0 : 0 < X := by omega
  have le : ∀ a, a ≤ 2 * c + 2 → X ^ a ≤ X ^ (2 * c + 2) := fun a ha => Nat.pow_le_pow_right hX0 ha
  have z0 : 1 ≤ X ^ (2 * c + 2) := Nat.one_le_pow _ _ hX0
  have z1 : X ≤ X ^ (2 * c + 2) := by simpa using le 1 (by omega)
  have zm : m ≤ X ^ (2 * c + 2) := hm.trans (le c (by omega))
  have zmm : m * m ≤ X ^ (2 * c + 2) := (Nat.mul_le_mul hm hm).trans (by rw [← pow_add]; exact le _ (by omega))
  have zmX : m * (2 * lam) ≤ X ^ (2 * c + 2) := (Nat.mul_le_mul hm hlam).trans (by rw [← pow_succ]; exact le _ (by omega))
  have zmR : m * R ≤ X ^ (2 * c + 2) := (Nat.mul_le_mul hm hR).trans (by rw [← pow_two, ← pow_add]; exact le _ (by omega))
  have e1 : m * (m + 1 + 1) = m * m + 2 * m := by ring
  have e2 : m * (2 * lam + 1 + 1) = m * (2 * lam) + 2 * m := by ring
  have top : 64 * X ^ (2 * c + 2) ≤ X ^ (2 * c + 4) := by
    have : X ^ (2 * c + 4) = X ^ 2 * X ^ (2 * c + 2) := by rw [← pow_add]; congr 1; omega
    rw [this]
    exact Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_left hX 2)
  rw [e1, e2] at hsl
  omega

/-- **The size of a parent** is at most Ξ^{2c+4}. -/
theorem size_mkParent_le {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {K g lam B y x : ℕ} (tr : Bool) (hK : K ≤ g) (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B)
    (hy : y < #(D.fam lam).I ^ nRectG g g) (hx : x < K ^ g) : size (mkParent D K g lam B tr y x) ≤ Xi g lam B ^ (2 * c + 4) := by
  have e : size (mkParent D K g lam B tr y x) = (size (unary K) + size (unary g)) + ((size (unary lam) + size (unary B)) + (size (listsOf D lam) + (1 + (size y + size x)))) := rfl
  rw [e, size_unary_eq, size_unary_eq, size_unary_eq, size_unary_eq]
  have hgg : 4 ≤ g ^ 2 := by simpa using Nat.pow_le_pow_left hg 2
  have hg1 : g ≤ g ^ 2 := Nat.le_self_pow (by norm_num) g
  have hs : ∀ t, t ≤ lam + B → 4 * t ≤ Xi g lam B := fun t ht => Nat.mul_le_mul hgg ht
  have hgX : g ^ 2 ≤ Xi g lam B := Nat.le_mul_of_pos_right _ (by omega)
  have h1 := hs lam (by omega)
  have h2 := hs B (by omega)
  have h3 := hs 2 (by omega)
  have hR : nRectG g g ≤ Xi g lam B * Xi g lam B := by
    have h4 := ClauseBound.Gen.Rate.four_nRect_le g
    have h5 : g ^ 4 = g ^ 2 * g ^ 2 := by ring
    have h6 := Nat.mul_le_mul hgX hgX
    omega
  have hm : (2 * lam) ^ c ≤ Xi g lam B ^ c := Nat.pow_le_pow_left (by omega) c
  have hsy : size y ≤ (2 * lam) ^ c * nRectG g g + 1 := size_nat_of_lt (hy.trans_le (by
    rw [pow_mul]
    exact Nat.pow_le_pow_left ((hS.is.card lam hlam).trans Nat.lt_two_pow_self.le) _))
  have hsx : size x ≤ Xi g lam B + 1 := (size_nat_of_lt (k := g ^ 2) (hx.trans_le (by
    rw [pow_two, pow_mul]
    exact Nat.pow_le_pow_left (hK.trans Nat.lt_two_pow_self.le) _))).trans (by omega)
  exact parent_arith (by omega) hm (by omega) (by omega) (by omega) (by omega) hR hsy hsx (size_listsOf_le hS hlam)

end ExplicitCost
