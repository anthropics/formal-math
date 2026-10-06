/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Sec2.Recursion
public import ThreeSumApsp.Sec2.Theorem5.Equation6

/-!
# Section 2.4.4: the remaining minutiae and the word size

* Minutiae.  The `K₀²` subsets, the tiles and the positions of `W` number `O(N² / D^{1/18})` in all
  (`minutiae_total_le`), because `K ≤ N` (`K_le_of_D_pow_le`), there are at most `4N²/N₀` tiles
  (`card_tiles_mul_N0_le`), `|W| ≤ 2^{-m} N²`, and `N, N₀ ≥ 2^{m/9}` (`two_rpow_le_of_D_pow_le`,
  `two_rpow_le_N0`).
* Word size.  An entry of an input array is an entry of `X` or `Y` or 0 (`abs_bandArrayL_le`,
  `abs_bandArrayR_le`); an encoded number is a `±1` combination of at most `7^L` of them
  (`abs_encodingL_le`, `abs_encodingR_le`); a value of `Pruned` is a sum of at most `10^L` products
  of two encoded numbers (`abs_Pruned_le`); and `10^L ≤ N²` by equation (6) (`ten_pow_le_sq`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The remaining minutiae -/

/-- `2^{m/9} ≤ 2^m`. -/
private theorem two_rpow_ninth_le (m : ℕ) : (2 : ℝ) ^ ((m : ℝ) / 9) ≤ (2 : ℝ) ^ m := by
  rw [← Real.rpow_natCast]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- A number that is at least `2^{m/9}` is at least 1 after multiplication by `2^{-m/9}`. -/
private theorem one_le_saving_mul {m : ℕ} {x : ℝ} (hx : (2 : ℝ) ^ ((m : ℝ) / 9) ≤ x) :
    1 ≤ saving m * x := by
  rw [← saving_mul_two_rpow m]
  exact mul_le_mul_of_nonneg_left hx (saving_pos m).le

/-- Section 2.4.4, in "the remaining minutiae": "K ≤ N". -/
theorem K_le_of_D_pow_le (m N : ℕ) (hN : D m ^ 18 ≤ N) : K (19 * m) m ≤ N :=
  (Nat.le_mul_of_pos_right _ (N0_pos _ _)).trans (K_mul_N0_le m N hN)

/-- Section 2.4.4, in "the remaining minutiae": "there are at most 4N²/N₀ tiles", where `N` is the
padded size. -/
theorem card_tiles_mul_N0_le {L m : ℕ} (hmL : m ≤ L) (N : ℕ) :
    (tiles L m N).card * N0 L m ≤ 4 * padN L m N ^ 2 := by
  -- `N₀ ≤ K N₀² = M`, and there are at most `4N²/M` tiles.
  refine le_trans (Nat.mul_le_mul_left _ ?_) (card_tiles_mul_M_le L m N)
  calc N0 L m = 1 * N0 L m ^ 1 := by ring
    _ ≤ K L m * N0 L m ^ 2 :=
        Nat.mul_le_mul (Nat.choose_pos hmL) (Nat.pow_le_pow_right (N0_pos L m) (by norm_num))

/-- Section 2.4.4, in "the remaining minutiae": `N ≥ 2^{m/9}`. -/
theorem two_rpow_le_of_D_pow_le (m N : ℕ) (hN : D m ^ 18 ≤ N) :
    (2 : ℝ) ^ ((m : ℝ) / 9) ≤ (N : ℝ) := by
  -- `2^{m/9} ≤ 2^m ≤ 4^{18m} = D^18 ≤ N`.
  have hpow : 2 ^ m ≤ N :=
    calc 2 ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) m
      _ ≤ (4 ^ m) ^ 18 := Nat.le_self_pow (by norm_num) _
      _ ≤ N := hN
  exact (two_rpow_ninth_le m).trans (by exact_mod_cast hpow)

/-- Section 2.4.4, in "the remaining minutiae": `N₀ ≥ 2^{m/9}`. -/
theorem two_rpow_le_N0 (m : ℕ) : (2 : ℝ) ^ ((m : ℝ) / 9) ≤ (N0 (19 * m) m : ℝ) := by
  -- `2^{m/9} ≤ 2^m ≤ 3^{18m} = N₀`.
  have hpow : 2 ^ m ≤ N0 (19 * m) m :=
    calc 2 ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by norm_num) m
      _ ≤ 3 ^ (19 * m - m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (two_rpow_ninth_le m).trans (by exact_mod_cast hpow)

/-- The three counts of "the remaining minutiae" (Section 2.4.4), one by one: the subsets in the
table, the tiles, and the positions of `W`. -/
private theorem minutiae_parts (m N : ℕ) (W : Finset (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hW : W.card * 2 ^ m ≤ N ^ 2) :
    (K (19 * m) m : ℝ) ≤ saving m * (N : ℝ) ^ 2
      ∧ ((tiles (19 * m) m N).card : ℝ) ≤ 4 * saving m * (padN (19 * m) m N : ℝ) ^ 2
      ∧ (W.card : ℝ) ≤ saving m * (N : ℝ) ^ 2 := by
  have hc := saving_pos m
  refine ⟨?_, ?_, ?_⟩
  · -- The subsets in the table: `K ≤ N ≤ 2^{-m/9} N²`.
    calc (K (19 * m) m : ℝ) ≤ N := by exact_mod_cast K_le_of_D_pow_le m N hN
      _ ≤ saving m * N * N :=
          le_mul_of_one_le_left N.cast_nonneg (one_le_saving_mul (two_rpow_le_of_D_pow_le m N hN))
      _ = saving m * (N : ℝ) ^ 2 := by ring
  · -- The tiles: at most `4N²/N₀ ≤ 4 · 2^{-m/9} N²`.
    have hT : ((tiles (19 * m) m N).card : ℝ) * N0 (19 * m) m
        ≤ 4 * (padN (19 * m) m N : ℝ) ^ 2 := by
      exact_mod_cast card_tiles_mul_N0_le (show m ≤ 19 * m by omega) N
    calc ((tiles (19 * m) m N).card : ℝ)
        ≤ (tiles (19 * m) m N).card * (saving m * N0 (19 * m) m) :=
          le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_saving_mul (two_rpow_le_N0 m))
      _ = saving m * ((tiles (19 * m) m N).card * N0 (19 * m) m) := by ring
      _ ≤ saving m * (4 * (padN (19 * m) m N : ℝ) ^ 2) := by gcongr
      _ = 4 * saving m * (padN (19 * m) m N : ℝ) ^ 2 := by ring
  · -- The positions: `|W| ≤ 2^{-m} N² ≤ 2^{-m/9} N²`.
    have hW' : (W.card : ℝ) * (2 : ℝ) ^ m ≤ (N : ℝ) ^ 2 := by exact_mod_cast hW
    calc (W.card : ℝ) = saving m * (W.card * (2 : ℝ) ^ ((m : ℝ) / 9)) := by
          rw [mul_left_comm, saving_mul_two_rpow, mul_one]
      _ ≤ saving m * (W.card * (2 : ℝ) ^ m) := by gcongr; exact two_rpow_ninth_le m
      _ ≤ saving m * (N : ℝ) ^ 2 := by gcongr

/-- Section 2.4.4: "O(L) operations per subset, per tile, and per position of W, which is
O(L 2^{-m/9} N²) in all": the number of these objects, with the `K₀²` subsets counted as at most
`K`, as the paper does ("as K ≤ N").  Here `N` is the size of the input.  The constant is
`18 = 1 + 16 + 1`, because the padding at most doubles `N`. -/
theorem minutiae_total_le (m N : ℕ) (W : Finset (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hW : W.card * 2 ^ m ≤ N ^ 2) :
    ((K (19 * m) m + (tiles (19 * m) m N).card + W.card : ℕ) : ℝ)
      ≤ 18 * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by
  obtain ⟨hK, hT, hW'⟩ := minutiae_parts m N W hN hW
  have hc := saving_pos m
  have hpad : (padN (19 * m) m N : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast padN_le_two_mul_of_D_pow_le m N hN
  have hsq : saving m * (padN (19 * m) m N : ℝ) ^ 2 ≤ saving m * (2 * (N : ℝ)) ^ 2 := by gcongr
  rw [← saving_eq_D_rpow]
  push_cast
  -- `K + |tiles| + |W| ≤ c N² + 4 c (2N)² + c N² = 18 c N²` with `c = 2^{-m/9}`.
  linarith [hK, hT, hW', hsq]

/-! ### The word size -/

/-- The subsets in the table are distinct (Section 2.3.4), so a sum over the table that selects the
subset `Q` is one of its terms or 0. -/
private theorem sum_table_eq_zero_or {L m : ℕ} {A : Type*} [AddCommMonoid A] (lay : Layout L m)
    (F : Fin (K0 L m) × Fin (K0 L m) → A) (Q : Finset (Fin L)) :
    (∑ gh, if lay.table gh = Q then F gh else 0) = 0
      ∨ ∃ gh, (∑ gh', if lay.table gh' = Q then F gh' else 0) = F gh := by
  by_cases hQ : ∃ gh, lay.table gh = Q
  · obtain ⟨gh, rfl⟩ := hQ
    exact .inr ⟨gh, by simp [lay.table_injective.eq_iff]⟩
  · exact .inl (sum_eq_zero fun gh _ => if_neg (not_exists.mp hQ gh))

/-- Section 2.4.4, word size: "The input entries are of this size, by assumption." Every entry of
the input array of a row band is an entry of `X` or 0.

NOTE.  `0 ≤ A` is needed only when `N = 0`. -/
theorem abs_bandArrayL_le {L m N : ℕ} (lay : Layout L m) {X : Matrix (Fin N) (Fin (D m)) ℤ} {A : ℤ}
    (hA : 0 ≤ A) (hX : ∀ I k, |X I k| ≤ A) (β : ℕ) (u : LeftStr L) :
    |bandArrayL lay X β u| ≤ A := by
  unfold bandArrayL arrayL bandFamilyL
  split_ifs with h
  · rcases sum_table_eq_zero_or lay (fun gh => rowBlock lay X (β * K0 L m + gh.1)) (innerSetL u)
      with hzero | ⟨gh, hgh⟩
    · rw [hzero]
      simpa using hA
    · rw [hgh]
      unfold rowBlock padRows
      split_ifs
      · exact hX _ _
      · simpa using hA
  · simpa using hA

/-- Section 2.4.4, word size: "The input entries are of this size, by assumption." Every entry of
the input array of a column band is an entry of `Y` or 0.

NOTE.  `0 ≤ B` is needed only when `N = 0`. -/
theorem abs_bandArrayR_le {L m N : ℕ} (lay : Layout L m) {Y : Matrix (Fin (D m)) (Fin N) ℤ} {B : ℤ}
    (hB : 0 ≤ B) (hY : ∀ k J, |Y k J| ≤ B) (β : ℕ) (v : RightStr L) :
    |bandArrayR lay Y β v| ≤ B := by
  unfold bandArrayR arrayR bandFamilyR
  split_ifs with h
  · rcases sum_table_eq_zero_or lay (fun gh => colBlock lay Y (β * K0 L m + gh.2)) (innerSetR v)
      with hzero | ⟨gh, hgh⟩
    · rw [hzero]
      simpa using hB
    · rw [hgh]
      unfold colBlock padCols
      split_ifs
      · exact hY _ _
      · simpa using hB
  · simpa using hB

/-- A combination of the entries of an array, with a product of coefficients 0, 1 or -1 for each
entry, is at most the number of entries times the largest absolute value of an entry. -/
theorem abs_encodeWith_le {α : Type} [Fintype α] {c : Term → α → ℤ} (hc : ∀ lam s, |c lam s| ≤ 1)
    {L : ℕ} {a : (Fin L → α) → ℤ} {A : ℤ} (ha : ∀ u, |a u| ≤ A) (τ : Leaf L) :
    |encodeWith c τ a| ≤ Fintype.card (Fin L → α) * A := by
  have h := abs_sum_mul_le univ (c := fun u => ∏ ℓ, c (τ ℓ) (u ℓ))
    (fun u _ => abs_prod_le_one _ fun ℓ _ => hc _ _) fun u _ => ha u
  simpa only [encodeWith, mul_comm, card_univ] using h

/-- Section 2.4.4, word size: "Every number in an encoding […] is a ±1 combination of at most 7^L
input entries", so its absolute value is at most `7^L` times the largest absolute value of an input
entry.  For the encoding of `a`. -/
theorem abs_encodingL_le {L : ℕ} {a : LeftStr L → ℤ} {A : ℤ} (ha : ∀ u, |a u| ≤ A) (τ : Leaf L) :
    |encodingL a τ| ≤ 7 ^ L * A := by
  have h := abs_encodeWith_le abs_phi_le_one ha τ
  rw [card_leftStr] at h
  exact_mod_cast h

/-- Section 2.4.4, word size: "Every number in an encoding […] is a ±1 combination of at most 7^L
input entries".  For the encoding of `b`. -/
theorem abs_encodingR_le {L : ℕ} {b : RightStr L → ℤ} {B : ℤ} (hb : ∀ v, |b v| ≤ B) (τ : Leaf L) :
    |encodingR b τ| ≤ 7 ^ L * B := by
  have h := abs_encodeWith_le abs_psi_le_one hb τ
  rw [card_rightStr] at h
  exact_mod_cast h

/-- Section 2.4.4, word size: "every value computed by Pruned is a sum of at most 10^L products of
two encoded numbers". -/
theorem abs_Pruned_le {n : ℕ} (encA encB : Leaf n → ℤ) (A B : ℤ) (hA : ∀ τ, |encA τ| ≤ A)
    (hB : ∀ τ, |encB τ| ≤ B) (S : Finset (OutStr n)) (w : OutStr n) :
    |Pruned n encA encB S w| ≤ 10 ^ n * (A * B) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA fun _ => Term.P0)
  have hAB : 0 ≤ A * B := mul_nonneg hA0 ((abs_nonneg _).trans (hB fun _ => Term.P0))
  -- The value is 0, or the sum over some of the `10^n` leaves of the product of the two numbers
  -- looked up there.
  rw [Pruned_eq_restrictTo_sum]
  simp only [restrictTo]
  split_ifs
  · calc |∑ τ : Leaf n with Leaf.Contributes τ w, encA τ * encB τ|
        ≤ (univ.filter fun τ : Leaf n => Leaf.Contributes τ w).card * (A * B) :=
          abs_sum_le_card_mul _ fun τ _ => by
            rw [abs_mul]
            exact mul_le_mul (hA τ) (hB τ) (abs_nonneg _) hA0
      _ ≤ 10 ^ n * (A * B) := by
          gcongr
          exact_mod_cast (card_le_univ _).trans_eq (card_vertex n)
  · rw [abs_zero]
    positivity

/-- Section 2.4.4, word size: "10^L ≤ N² by (6)", for `L = 19m` and `N ≥ D^18`. -/
theorem ten_pow_le_sq (m N : ℕ) (hN : D m ^ 18 ≤ N) : 10 ^ (19 * m) ≤ N ^ 2 := by
  -- `N₀ ≤ K N₀ ≤ N` and `2^{-m/9} ≤ 1`, so equation (6) gives `10^L ≤ N N₀ ≤ N²`.
  have hN0 : (N0 (19 * m) m : ℝ) ≤ N := by
    exact_mod_cast (Nat.le_mul_of_pos_left _ (Nat.choose_pos (by omega))).trans
      (K_mul_N0_le m N hN)
  have hc := saving_le_one m
  have hreal : (10 : ℝ) ^ (19 * m) ≤ (N : ℝ) ^ 2 :=
    calc (10 : ℝ) ^ (19 * m) ≤ saving m * N * N0 (19 * m) m := eq_6 m N hN
      _ ≤ 1 * N * N := by gcongr
      _ = (N : ℝ) ^ 2 := by ring
  exact_mod_cast hreal

end ThreeSumApsp
