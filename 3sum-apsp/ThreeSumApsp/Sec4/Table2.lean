/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.Table2.LogBounds

/-!
# Table 2

Section 4.4 prescribes how an entry is computed. The left half has the `γ` of Corollary 31, "with
the c of the row and the θ that gives the q of the column (θ = 1/9 for q = 0.43)". The right half
has the `γ` of Corollary 32, "with the θ at which γ = κ - q". "The ε of a row of the table is the
smallest R_c(γ) over its entries." All values are rounded down (caption).

* The `θ` of a column of the left half does not depend on the row. It is enclosed between two
  decimal numbers (`exists_qOf_eq_010` to `exists_qOf_eq_090`): `q(θ)` is at most the `q` of the
  column at the lower number (`qOf_le`) and at least that `q` at the upper number (`le_qOf`), and it
  is continuous.
* A row (`table_2_c40` to `table_2_c10_5`) depends on `c` through two numbers: `ln(1/ρ_c)/ln 4`, by
  which `θ` is multiplied to give `γ` (`hg`), and the denominator of (11) at `γ = 0` (`hB`), which
  gives `ε < R_c(γ)` for every `γ` up to the largest one of the row (`hR`).
* An entry of the left half is `Table2Query.intro` at the enclosure of the `θ` of its column. An
  entry of the right half (`Table2Density.intro`) names two decimal numbers: at the lower one
  `γ + q ≤ κ` (`qOf_le`), at the upper one `γ + q ≥ κ` (`le_qOf`), so the root `θ` of `γ + q = κ`
  lies between them; and `γ = θ ln(1/ρ_c)/ln 4` has the printed four decimals at both.

How to read the numbers in the proofs. The two decimal numbers around a `θ` are `θ` cut after five
decimals and the next such number, or after six decimals where `γ` is too close to a multiple of
`0.0001`. The argument `k` of `qOf_le`, `le_qOf` and `log_mem` is the exponent of the power of two
nearest to the number whose logarithm is taken, and the second argument of `log_mem` is the number
of terms of the series.
-/

public section

open Finset

namespace ThreeSumApsp

/-! ## The `θ` of the columns of the left half -/

/-- The `θ` of the column `q = 0.10` is `0.01945042…`. -/
theorem exists_qOf_eq_010 : ∃ θ ∈ Set.Icc 0.01945 0.019451, qOf θ = 0.10 :=
  exists_qOf_eq (qOf_le (-6)) (le_qOf (-6))

/-- The `θ` of the column `q = 0.25` is `0.05754017…`. -/
theorem exists_qOf_eq_025 : ∃ θ ∈ Set.Icc 0.05754 0.05755, qOf θ = 0.25 :=
  exists_qOf_eq (qOf_le (-4)) (le_qOf (-4))

/-- The `θ` of the column `q = 0.50` is `0.13518246…`. -/
theorem exists_qOf_eq_050 : ∃ θ ∈ Set.Icc 0.13518 0.13519, qOf θ = 0.50 :=
  exists_qOf_eq (qOf_le (-3)) (le_qOf (-3))

/-- The `θ` of the column `q = 0.75` is `0.22855783…`. -/
theorem exists_qOf_eq_075 : ∃ θ ∈ Set.Icc 0.22855 0.22856, qOf θ = 0.75 :=
  exists_qOf_eq (qOf_le (-2)) (le_qOf (-2))

/-- The `θ` of the column `q = 0.90` is `0.29269537…`. -/
theorem exists_qOf_eq_090 : ∃ θ ∈ Set.Icc 0.29269 0.292696, qOf θ = 0.90 :=
  exists_qOf_eq (qOf_le (-2)) (le_qOf (-2))

/-- Caption of Table 2: at `θ = 1/9`, "more precisely, q = 0.4277…". -/
theorem qOf_ninth_mem : qOf (1 / 9) ∈ Set.Icc 0.42773 0.42774 :=
  ⟨le_qOf (-3), qOf_le (-3)⟩

/-! ## The six rows -/

/-- Table 2, the row `c = 40`. -/
theorem table_2_c40 :
    Table2Row 40 0.029 0.0205 0.0608 0.1175 0.1429 0.2417 0.3095
      0.0166 0.0473 0.1060 0.1720 0.2442 :=
  have hg : gammaOf 40 1 ∈ Set.Icc 1.057738 1.057739 := gammaOf_one_mem (log_mem 2 3)
  have hB : lnΛ 40 0 ∈ Set.Icc 46.919 46.920 := lnΛ_zero_mem (log_mem (-5) 2) (log_mem 0 2)
  have hR : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 0.3096 → 0.029 < Rc 40 γ := lt_Rc_of_lnΛ_zero_mem hB
  { q010 := .intro exists_qOf_eq_010 hg hR
    q025 := .intro exists_qOf_eq_025 hg hR
    q043 := .intro hg hR
    q050 := .intro exists_qOf_eq_050 hg hR
    q075 := .intro exists_qOf_eq_075 hg hR
    q090 := .intro exists_qOf_eq_090 hg hR
    k010 := .intro hg hR 0.01574 0.01575 (qOf_le (-6)) (le_qOf (-6))
    k025 := .intro hg hR 0.04473 0.04474 (qOf_le (-4)) (le_qOf (-4))
    k050 := .intro hg hR 0.10029 0.10030 (qOf_le (-3)) (le_qOf (-3))
    k075 := .intro hg hR 0.162613 0.16262 (qOf_le (-3)) (le_qOf (-3))
    k100 := .intro hg hR 0.23090 0.23091 (qOf_le (-2)) (le_qOf (-2))
    eps := exists_Rc_lt exists_qOf_eq_090 hg hB }

/-- `ln(1/ρ_c)/ln 4` for `c = 21` (the proof of Corollary 26 uses it too). -/
theorem gammaOf_21_one_mem : gammaOf 21 1 ∈ Set.Icc 0.576001 0.576002 :=
  gammaOf_one_mem (log_mem 1 3)

/-- The denominator of (11) at `γ = 0` for `c = 21` (`Corollary26.Rc_digits` uses it too). -/
theorem lnΛ_21_zero_mem : lnΛ 21 0 ∈ Set.Icc 24.371 24.372 :=
  lnΛ_zero_mem (log_mem (-4) 3) (log_mem 0 3)

/-- Table 2, the row `c = 21`. -/
theorem table_2_c21 :
    Table2Row 21 0.056 0.0112 0.0331 0.0640 0.0778 0.1316 0.1685
      0.0099 0.0286 0.0653 0.1074 0.1546 :=
  have hg := gammaOf_21_one_mem
  have hB := lnΛ_21_zero_mem
  have hR : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 0.1686 → 0.056 < Rc 21 γ := lt_Rc_of_lnΛ_zero_mem hB
  { q010 := .intro exists_qOf_eq_010 hg hR
    q025 := .intro exists_qOf_eq_025 hg hR
    q043 := .intro hg hR
    q050 := .intro exists_qOf_eq_050 hg hR
    q075 := .intro exists_qOf_eq_075 hg hR
    q090 := .intro exists_qOf_eq_090 hg hR
    k010 := .intro hg hR 0.01722 0.01723 (qOf_le (-6)) (le_qOf (-6))
    k025 := .intro hg hR 0.04970 0.04971 (qOf_le (-4)) (le_qOf (-4))
    k050 := .intro hg hR 0.11337 0.11338 (qOf_le (-3)) (le_qOf (-3))
    k075 := .intro hg hR 0.18647 0.18648 (qOf_le (-2)) (le_qOf (-2))
    k100 := .intro hg hR 0.26854 0.26855 (qOf_le (-2)) (le_qOf (-2))
    eps := exists_Rc_lt exists_qOf_eq_090 hg hB }

/-- For `c = 19` one has `ρ_c = 1/2`, so `γ` is exactly `θ/2`. -/
theorem gammaOf_19 (θ : ℝ) : gammaOf 19 θ = θ / 2 := by
  have htwo : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [gammaOf, rhoC, Real.log_four, show (1 / (9 / (19 - 1)) : ℝ) = 2 by norm_num]
  field_simp

/-- The denominator of (11) at `γ = 0` for `c = 19` (Table 1's column on Section 2 uses it too). -/
theorem lnΛ_19_zero_mem : lnΛ 19 0 ∈ Set.Icc 22.015 22.016 :=
  lnΛ_zero_mem (log_mem (-4) 2) (log_mem 0 2)

/-- Table 2, the row `c = 19`. -/
theorem table_2_c19 :
    Table2Row 19 0.062 0.0097 0.0287 0.0555 0.0675 0.1142 0.1463
      0.0087 0.0253 0.0578 0.0954 0.1379 :=
  -- `ln(1/ρ_c)/ln 4` is exactly `1/2`, in the form that the entries take
  have hg : gammaOf 19 1 ∈ Set.Icc 0.5 0.5 := by rw [gammaOf_19]; norm_num
  have hB := lnΛ_19_zero_mem
  have hR : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 0.1464 → 0.062 < Rc 19 γ := lt_Rc_of_lnΛ_zero_mem hB
  { q010 := .intro exists_qOf_eq_010 hg hR
    q025 := .intro exists_qOf_eq_025 hg hR
    q043 := .intro hg hR
    q050 := .intro exists_qOf_eq_050 hg hR
    q075 := .intro exists_qOf_eq_075 hg hR
    q090 := .intro exists_qOf_eq_090 hg hR
    k010 := .intro hg hR 0.01748 0.01749 (qOf_le (-6)) (le_qOf (-6))
    k025 := .intro hg hR 0.05060 0.05061 (qOf_le (-4)) (le_qOf (-4))
    k050 := .intro hg hR 0.11579 0.115794 (qOf_le (-3)) (le_qOf (-3))
    k075 := .intro hg hR 0.19099 0.190998 (qOf_le (-2)) (le_qOf (-2))
    k100 := .intro hg hR 0.27584 0.27585 (qOf_le (-2)) (le_qOf (-2))
    eps := exists_Rc_lt exists_qOf_eq_090 hg hB }

/-- Table 2, the row `c = 15`. -/
theorem table_2_c15 :
    Table2Row 15 0.079 0.0061 0.0183 0.0354 0.0430 0.0728 0.0932
      0.0057 0.0168 0.0389 0.0646 0.0941 :=
  have hg : gammaOf 15 1 ∈ Set.Icc 0.318714 0.318715 := gammaOf_one_mem (log_mem 1 5)
  have hB : lnΛ 15 0 ∈ Set.Icc 17.321 17.322 := lnΛ_zero_mem (log_mem (-4) 2) (log_mem 0 2)
  have hR : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 0.0942 → 0.079 < Rc 15 γ := lt_Rc_of_lnΛ_zero_mem hB
  { q010 := .intro exists_qOf_eq_010 hg hR
    q025 := .intro exists_qOf_eq_025 hg hR
    q043 := .intro hg hR
    q050 := .intro exists_qOf_eq_050 hg hR
    q075 := .intro exists_qOf_eq_075 hg hR
    q090 := .intro exists_qOf_eq_090 hg hR
    k010 := .intro hg hR 0.01814 0.01815 (qOf_le (-6)) (le_qOf (-6))
    k025 := .intro hg hR 0.05290 0.05291 (qOf_le (-4)) (le_qOf (-4))
    k050 := .intro hg hR 0.12206 0.12207 (qOf_le (-3)) (le_qOf (-3))
    k075 := .intro hg hR 0.20286 0.20287 (qOf_le (-2)) (le_qOf (-2))
    k100 := .intro hg hR 0.29534 0.29535 (qOf_le (-2)) (le_qOf (-2))
    eps := exists_Rc_lt exists_qOf_eq_090 hg hB }

/-- Table 2, the row `c = 12`. -/
theorem table_2_c12 :
    Table2Row 12 0.099 0.0028 0.0083 0.0160 0.0195 0.0330 0.0423
      0.0027 0.0080 0.0186 0.0312 0.0459 :=
  have hg : gammaOf 12 1 ∈ Set.Icc 0.144753 0.144754 := gammaOf_one_mem (log_mem 0 4)
  have hB : lnΛ 12 0 ∈ Set.Icc 13.825 13.826 := lnΛ_zero_mem (log_mem (-4) 3) (log_mem 0 3)
  have hR : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 0.0460 → 0.099 < Rc 12 γ := lt_Rc_of_lnΛ_zero_mem hB
  { q010 := .intro exists_qOf_eq_010 hg hR
    q025 := .intro exists_qOf_eq_025 hg hR
    q043 := .intro hg hR
    q050 := .intro exists_qOf_eq_050 hg hR
    q075 := .intro exists_qOf_eq_075 hg hR
    q090 := .intro exists_qOf_eq_090 hg hR
    k010 := .intro hg hR 0.01883 0.01884 (qOf_le (-6)) (le_qOf (-6))
    k025 := .intro hg hR 0.05532 0.05533 (qOf_le (-4)) (le_qOf (-4))
    k050 := .intro hg hR 0.12884 0.12885 (qOf_le (-3)) (le_qOf (-3))
    k075 := .intro hg hR 0.21599 0.21600 (qOf_le (-2)) (le_qOf (-2))
    k100 := .intro hg hR 0.31749 0.31750 (qOf_le (-2)) (le_qOf (-2))
    eps := exists_Rc_lt exists_qOf_eq_090 hg hB }

/-- Table 2, the row `c = 10.5`. -/
theorem table_2_c10_5 :
    Table2Row 10.5 0.114 0.0007 0.0022 0.0043 0.0052 0.0089 0.0114
      0.0007 0.0022 0.0052 0.0087 0.0129 :=
  have hg : gammaOf 10.5 1 ∈ Set.Icc 0.039001 0.039002 := gammaOf_one_mem (log_mem 0 3)
  have hB : lnΛ 10.5 0 ∈ Set.Icc 12.089 12.090 := lnΛ_zero_mem (log_mem (-3) 3) (log_mem 0 3)
  have hR : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 0.0130 → 0.114 < Rc 10.5 γ := lt_Rc_of_lnΛ_zero_mem hB
  { q010 := .intro exists_qOf_eq_010 hg hR
    q025 := .intro exists_qOf_eq_025 hg hR
    q043 := .intro hg hR
    q050 := .intro exists_qOf_eq_050 hg hR
    q075 := .intro exists_qOf_eq_075 hg hR
    q090 := .intro exists_qOf_eq_090 hg hR
    k010 := .intro hg hR 0.01928 0.01929 (qOf_le (-6)) (le_qOf (-6))
    k025 := .intro hg hR 0.05692 0.05693 (qOf_le (-4)) (le_qOf (-4))
    k050 := .intro hg hR 0.13340 0.13341 (qOf_le (-3)) (le_qOf (-3))
    k075 := .intro hg hR 0.22500 0.22501 (qOf_le (-2)) (le_qOf (-2))
    k100 := .intro hg hR 0.33311 0.33312 (qOf_le (-2)) (le_qOf (-2))
    eps := exists_Rc_lt exists_qOf_eq_090 hg hB }

end ThreeSumApsp
