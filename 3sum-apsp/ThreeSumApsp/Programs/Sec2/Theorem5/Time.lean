/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.AllTiles
public import ThreeSumApsp.Programs.Sec2.Theorem5.WordSize

/-!
# Theorem 5 in the light language: the running time, added up

Pure mathematics: no program occurs here.  thm5Shape p w work is the shape of the running time of
the program for Theorem 5.  For the parameters of Section 2.4.4, L = 19 m, and under the hypotheses
of Theorem 5, N ≥ D^18 and at most N²/√D wanted positions, it is at most a numeral times L
N² / D^{1/18} (thm5Shape_le), which is below the bound O(N² log² D / D^{1/18}) of the theorem
(thm5Shape_le_of_wanted).

The proof follows "The cost" in Section 2.4.4.  The shape is a polynomial in the sizes
(thm5Shape_eq), each term of which is a basic quantity times at most L + 1 (shapeOf_le).  The basic
quantities are at most a numeral times X = N² / D^{1/18}: the subsets, tiles and wanted positions
(minutiae_le), the encodings (encodings_le), the entries of the input arrays (bandArrays_le), the
leaves that the pruned recursions visit (work5_le), and N itself (le_rate).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-- The work of the pruned recursions of all tiles, for a set W of wanted positions. -/
def work5 {m N : ℕ} (lay : Layout (19 * m) m) (W : Finset (Fin N × Fin N)) : ℕ :=
  ∑ β ∈ Finset.range (numBands (19 * m) m N), ∑ β' ∈ Finset.range (numBands (19 * m) m N),
    tileWork (19 * m) (Spec.codesOf (wantedStrings lay W β β'))

/-- D^{-1/18} N² is N² / D^{1/18}. -/
theorem rate_eq (m N : ℕ) (k : ℝ) :
    k * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 = k * ((N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ)) :=
      by
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  ring

/-- Section 2.4.4: the work of the pruned recursions is at most 66 (L + 1) N² / D^{1/18}: it is at
most 2 (L + 1) for each leaf that contributes to a wanted entry, and there are at most 33 N² /
D^{1/18} such leaves. -/
theorem work5_le {m N : ℕ} (lay : Layout (19 * m) m) (W : Finset (Fin N × Fin N))
    (hN : D m ^ 18 ≤ N)
    (hW : W.card * 2 ^ m ≤ N ^ 2) :
    (work5 lay W : ℝ) ≤ 66 * ((19 * (m : ℝ) + 1) * ((N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ))) := by
  have hone : ∀ U : Finset (OutStr (19 * m)), tileWork (19 * m) (Spec.codesOf U) ≤ 2 *
    ((19 * m + 1) * (Leaves U).card) := by
    intro U
    unfold tileWork
    split_ifs with h
    · exact Nat.zero_le _
    · exact Spec.prunedWork_le U (Finset.nonempty_iff_ne_empty.2 fun he => h
        ((Spec.codesOf_eq_nil U).2 he))
  have hsum : work5 lay W
      ≤ 2 * ((19 * m + 1) * ∑ T ∈ tiles (19 * m) m N, (Leaves (wantedStrings lay W T.1 T.2)).card)
        := by
    unfold work5 tiles
    rw [Finset.sum_product, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun β _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun β' _ => hone _
  have hleaves := Theorem5.total_leaves lay W hN hW
  rw [rate_eq] at hleaves
  have hcast : (work5 lay W : ℝ)
      ≤ 2 * ((19 * (m : ℝ) + 1) * ((∑ T ∈ tiles (19 * m) m N,
        (Leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ)) := by
    exact_mod_cast hsum
  have hm0 : (0 : ℝ) ≤ 19 * (m : ℝ) + 1 := by positivity
  have := mul_le_mul_of_nonneg_left hleaves hm0
  linarith

/-- The shape as a polynomial in the sizes: lo stands for L - m, d for D, n0 for N₀, k0 for
K₀ = ⌊√K⌋, and nB for the number of bands. -/
def shapeOf (L m lo N d n0 k0 nB w work : ℕ) : ℕ :=
  ((L + 1) ^ 2 + (k0 + 1) + (k0 * k0 + 1) * (L + 1) + (N + 1) * (lo + 1) + (d + 1) * (m + 1)
      + nB * (10 ^ L + (7 ^ L + (k0 * k0 * n0 * d + 1) * (L + 1))))
    + (w + 1) * (L + 1) + ((L + 1) * (w + 10) + nB * nB + 1) + (work + nB * nB + 1) + (w + 1)
    + (m + 1)

/-- The shape for the parameters of Theorem 5, as this polynomial. -/
theorem thm5Shape_eq (m N w work : ℕ) :
    thm5Shape (thm5Par m N) w work
      = shapeOf (19 * m) m (18 * m) N (D m) (N0 (19 * m) m) (K0 (19 * m) m) (numBands (19 * m) m N)
        w work := by
  have h : 19 * m - m = 18 * m := by omega
  simp only [thm5Shape, sharedShape, bandArrayShape, thm5Par, Par.Lo, Par.D, Par.N0, Par.K, Par.K0,
    Par.KK, Par.nB, Par.nT, Par.T,
    Par.S7, shapeOf, h]
  rfl

/-- Each basic quantity of the shape is at most a numeral times X, which stands for
N² / D^{1/18}; the work of the pruned recursions is at most a numeral times (L + 1) X. -/
structure ShapeBounds (m N d n0 k0 nB w work : ℕ) (X : ℝ) : Prop where
  one : 1 ≤ X
  levels : 19 * (m : ℝ) + 1 ≤ X
  subsets : (k0 : ℝ) * (k0 : ℝ) ≤ 18 * X
  root : (k0 : ℝ) ≤ 18 * X
  rows : (N : ℝ) ≤ X
  cols : (d : ℝ) ≤ X
  bands : (nB : ℝ) ≤ 18 * X
  tiles : (nB : ℝ) * (nB : ℝ) ≤ 18 * X
  arrays : (nB : ℝ) * (7 : ℝ) ^ (19 * m) ≤ 2 * X
  encodings : (nB : ℝ) * (10 : ℝ) ^ (19 * m) ≤ 2 * X
  entries : (nB : ℝ) * ((k0 : ℝ) * (k0 : ℝ) * (n0 : ℝ) * (d : ℝ)) ≤ 2 * X
  wanted : (w : ℝ) ≤ 18 * X
  recursions : (work : ℝ) ≤ 66 * ((19 * (m : ℝ) + 1) * X)

/-- The polynomial, bounded term by term: every term is one of the basic quantities, or one of them
times L + 1 = 19 m + 1, m + 1 or 18 m + 1. -/
theorem shapeOf_le {m N d n0 k0 nB w work : ℕ} {X : ℝ}
    (h : ShapeBounds m N d n0 k0 nB w work X) :
    (shapeOf (19 * m) m (18 * m) N d n0 k0 nB w work : ℝ) ≤ 300 * ((19 * (m : ℝ) + 1) * X) := by
  obtain ⟨hone, hlevels, hsubsets, hroot, hrows, hcols, hbands, htiles, harrays, hencodings,
    hentries, hwanted, hrecursions⟩ := h
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- the same bounds multiplied by m
  have mone := mul_le_mul_of_nonneg_left hone hm
  have mlevels := mul_le_mul_of_nonneg_left hlevels hm
  have msubsets := mul_le_mul_of_nonneg_left hsubsets hm
  have mrows := mul_le_mul_of_nonneg_left hrows hm
  have mcols := mul_le_mul_of_nonneg_left hcols hm
  have mbands := mul_le_mul_of_nonneg_left hbands hm
  have mentries := mul_le_mul_of_nonneg_left hentries hm
  have mwanted := mul_le_mul_of_nonneg_left hwanted hm
  have hmX : 0 ≤ (m : ℝ) * X := mul_nonneg hm (by linarith)
  unfold shapeOf
  push_cast
  generalize (7 : ℝ) ^ (19 * m) = s, (10 : ℝ) ^ (19 * m) = t, (m : ℝ) = M, (N : ℝ) = n,
    (d : ℝ) = d', (n0 : ℝ) = n0', (k0 : ℝ) = a, (nB : ℝ) = b, (w : ℝ) = ww, (work : ℝ) = wk at *
  linarith

/-- 19 m + 1 ≤ D^18. -/
theorem levels_le_pow (m : ℕ) : 19 * m + 1 ≤ D m ^ 18 := by
  have h1 : D m ^ 18 = 2 ^ (36 * m) := by
    unfold D
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have h2 := Nat.lt_two_pow_self (n := 36 * m)
  rw [h1]
  omega

/-- 19 m + 1 ≤ 20 log D for m ≥ 1, since log D = m log 4 and log 4 ≥ 1. -/
theorem levels_le_log (m : ℕ) (hm : 1 ≤ m) : 19 * (m : ℝ) + 1 ≤ 20 * Real.log (D m) := by
  have h4 : 1 ≤ Real.log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hlog : Real.log (D m) = (m : ℝ) * Real.log 4 := by
    unfold D
    push_cast
    exact Real.log_pow 4 m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [hlog]
  linarith [mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ m by linarith)]

/-! ## The clauses of Section 2.4.4, in terms of X = N² / D^{1/18} -/

section clauses

variable {m N : ℕ}

/-- D ≥ 1. -/
private theorem one_le_D : (1 : ℝ) ≤ D m := by exact_mod_cast Nat.one_le_pow m 4 (by norm_num)

/-- D^{1/18} ≤ D. -/
private theorem D_rpow_le : (D m : ℝ) ^ (1 / 18 : ℝ) ≤ D m := by
  simpa using Real.rpow_le_rpow_of_exponent_le one_le_D (show (1 / 18 : ℝ) ≤ 1 by norm_num)

/-- N ≤ N² / D^{1/18}, because D^{1/18} ≤ D ≤ N. -/
theorem le_rate (hN : D m ^ 18 ≤ N) : (N : ℝ) ≤ (N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ) := by
  have hD1 : (1 : ℝ) ≤ D m := one_le_D
  have hDN : (D m : ℝ) ≤ N := by exact_mod_cast D_le_of_D_pow_le hN
  rw [le_div_iff₀ (by positivity), sq]
  exact mul_le_mul_of_nonneg_left (D_rpow_le.trans hDN) (Nat.cast_nonneg N)

/-- "O(L) operations per subset, per tile, and per position of W": there are at most
18 N² / D^{1/18} of these objects, for any number w ≤ N²/√D of wanted positions. -/
theorem minutiae_le {w : ℕ} (hN : D m ^ 18 ≤ N) (hw : w * 2 ^ m ≤ N ^ 2) :
    (K (19 * m) m : ℝ) + (numBands (19 * m) m N : ℝ) ^ 2 + w
      ≤ 18 * ((N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ)) := by
  -- a set of w positions
  obtain ⟨W, -, hWc⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin N × Fin N))) (n := w) (by
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      calc w ≤ w * 2 ^ m := Nat.le_mul_of_pos_right _ (by positivity)
        _ ≤ N ^ 2 := hw
        _ = N * N := sq N)
  have htiles : (tiles (19 * m) m N).card = numBands (19 * m) m N ^ 2 := by simp [tiles, sq]
  have hmin := minutiae_total_le m N W hN (by rw [hWc]; exact hw)
  rw [htiles, hWc, rate_eq] at hmin
  exact_mod_cast hmin

/-- "the encodings cost […] O(2^{-m/9} N²) operations": the encodings of all row bands have at most
2 N² / D^{1/18} entries. -/
theorem encodings_le (hN : D m ^ 18 ≤ N) :
    (numBands (19 * m) m N : ℝ) * (10 : ℝ) ^ (19 * m)
      ≤ 2 * ((N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ)) := by
  have henc := encodings_total_le m N hN
  rw [rate_eq] at henc
  push_cast at henc
  linarith

/-- The entries written into the input arrays of all the bands together:
n_B K₀² N₀ D = (padded N) · K₀ D ≤ 2N · N / D^{1/18}, because K₀ D² ≤ K N₀ ≤ N. -/
theorem bandArrays_le (hN : D m ^ 18 ≤ N) :
    (numBands (19 * m) m N : ℝ)
        * ((K0 (19 * m) m : ℝ) * (K0 (19 * m) m : ℝ) * (N0 (19 * m) m : ℝ) * (D m : ℝ))
      ≤ 2 * ((N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ)) := by
  have hD1 : (1 : ℝ) ≤ D m := one_le_D
  have hr0 : 0 < (D m : ℝ) ^ (1 / 18 : ℝ) := by positivity
  have hrD : (D m : ℝ) ^ (1 / 18 : ℝ) ≤ D m := D_rpow_le
  have hDD : D m ^ 2 ≤ N0 (19 * m) m := by
    unfold D N0
    rw [show 19 * m - m = 18 * m by omega]
    calc (4 ^ m) ^ 2 = 16 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (3 ^ 18) ^ m := Nat.pow_le_pow_left (by norm_num) m
      _ = 3 ^ (18 * m) := (pow_mul 3 18 m).symm
  have hpad : (numBands (19 * m) m N : ℝ) * ((K0 (19 * m) m : ℝ) * (N0 (19 * m) m : ℝ))
      ≤ 2 * N := by exact_mod_cast padN_le_two_mul_of_D_pow_le m N hN
  have hKD : (K0 (19 * m) m : ℝ) * (D m : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (Nat.mul_le_mul (Nat.sqrt_le_self _) hDD).trans
        (K_mul_N0_le m N hN)
  generalize (D m : ℝ) ^ (1 / 18 : ℝ) = r, (numBands (19 * m) m N : ℝ) = b,
    (N0 (19 * m) m : ℝ) = n0 at *
  have hK0 : (0 : ℝ) ≤ K0 (19 * m) m := Nat.cast_nonneg _
  generalize (K0 (19 * m) m : ℝ) = a, (D m : ℝ) = d at *
  have hKDr : a * d ≤ (N : ℝ) / r := by
    rw [le_div_iff₀ hr0]
    calc a * d * r ≤ a * d * d := mul_le_mul_of_nonneg_left hrD (mul_nonneg hK0 (by linarith))
      _ = a * d ^ 2 := by ring
      _ ≤ N := hKD
  calc b * (a * a * n0 * d) = b * (a * n0) * (a * d) := by ring
    _ ≤ 2 * N * ((N : ℝ) / r) := mul_le_mul hpad hKDr (mul_nonneg hK0 (by linarith)) (by positivity)
    _ = 2 * ((N : ℝ) ^ 2 / r) := by ring

end clauses

/-- **The shape of the running time is O(L N² / D^{1/18})**, in terms of numbers: w ≤ N²/√D wanted
positions, and work within the bound of work5_le. -/
theorem thm5Shape_le (m N w work : ℕ) (hN : D m ^ 18 ≤ N) (hw : w * 2 ^ m ≤ N ^ 2)
    (hwork : (work : ℝ)
      ≤ 66 * ((19 * (m : ℝ) + 1) * ((N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ)))) :
    (thm5Shape (thm5Par m N) w work : ℝ)
      ≤ 300 * ((19 * (m : ℝ) + 1) * ((N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ))) := by
  have hNX := le_rate hN
  have hmin := minutiae_le hN hw
  have henc := encodings_le hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast one_le_of_D_pow_le hN
  have hDN : (D m : ℝ) ≤ N := by exact_mod_cast D_le_of_D_pow_le hN
  have hLN : 19 * (m : ℝ) + 1 ≤ N := by exact_mod_cast (levels_le_pow m).trans hN
  have hKK : (K0 (19 * m) m : ℝ) * K0 (19 * m) m ≤ K (19 * m) m := by
    exact_mod_cast Nat.sqrt_le (K (19 * m) m)
  have hK0 : (K0 (19 * m) m : ℝ) ≤ K (19 * m) m := by
    exact_mod_cast Nat.sqrt_le_self (K (19 * m) m)
  have hB : (numBands (19 * m) m N : ℝ) ≤ (numBands (19 * m) m N : ℝ) ^ 2 := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have harr : (numBands (19 * m) m N : ℝ) * (7 : ℝ) ^ (19 * m)
      ≤ 2 * ((N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ)) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
      (Nat.cast_nonneg _)).trans henc
  have hK : (0 : ℝ) ≤ K (19 * m) m := Nat.cast_nonneg _
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hBB : (0 : ℝ) ≤ (numBands (19 * m) m N : ℝ) ^ 2 := by positivity
  rw [thm5Shape_eq]
  exact shapeOf_le
    { one := by linarith
      levels := by linarith
      subsets := by linarith
      root := by linarith
      rows := hNX
      cols := by linarith
      bands := by linarith
      tiles := by linarith [sq (numBands (19 * m) m N : ℝ)]
      arrays := harr
      encodings := henc
      entries := bandArrays_le hN
      wanted := by linarith
      recursions := hwork }

/-- **The shape of the running time is O(N² log D / D^{1/18})**, for a set W of wanted positions. -/
theorem thm5Shape_le_log {m N : ℕ} (lay : Layout (19 * m) m) (W : Finset (Fin N × Fin N))
    (hm : 1 ≤ m) (hN : D m ^ 18 ≤ N) (hW : W.card * 2 ^ m ≤ N ^ 2) :
    (thm5Shape (thm5Par m N) W.card (work5 lay W) : ℝ)
      ≤ 6000 * ((N : ℝ) ^ 2 * Real.log (D m) / (D m : ℝ) ^ (1 / 18 : ℝ)) := by
  have h := thm5Shape_le m N W.card (work5 lay W) hN hW (work5_le lay W hN hW)
  have hlog := levels_le_log m hm
  have hX0 : 0 ≤ (N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ) := by positivity
  have e1 : (N : ℝ) ^ 2 * Real.log (D m) / (D m : ℝ) ^ (1 / 18 : ℝ)
      = Real.log (D m) * ((N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ)) := by ring
  rw [e1]
  generalize (N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ) = X at h hX0 ⊢
  have h1 : (19 * (m : ℝ) + 1) * X ≤ 20 * Real.log (D m) * X :=
    mul_le_mul_of_nonneg_right hlog hX0
  linarith

/-- **The shape of the running time is within the bound of Theorem 5**, for a set W of wanted
positions. -/
theorem thm5Shape_le_of_wanted {m N : ℕ} (lay : Layout (19 * m) m) (W : Finset (Fin N × Fin N))
    (hm : 1 ≤ m) (hN : D m ^ 18 ≤ N) (hW : W.card * 2 ^ m ≤ N ^ 2) :
    (thm5Shape (thm5Par m N) W.card (work5 lay W) : ℝ)
      ≤ 6000 * ((N : ℝ) ^ 2 * Real.log (D m) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ)) := by
  refine (thm5Shape_le_log lay W hm hN hW).trans ?_
  have hlog := levels_le_log m hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog1 : 1 ≤ Real.log (D m) := by linarith
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (le_self_pow₀ hlog1 (by norm_num)) (by positivity))
    (by positivity)) (by norm_num)

end Light.Sec2
