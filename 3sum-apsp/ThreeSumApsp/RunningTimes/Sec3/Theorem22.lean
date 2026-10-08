/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Machine.PolylogIsLittleO
public import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.TimeBound
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.TimeBound
public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.TimeBound
public import ThreeSumApsp.RunningTimes.Sec3.Theorem19
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ApspLayout
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.MinPlusLayout
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ThreeSumPolylog
public import ThreeSumApsp.TimeClaims.Sec3.Theorem21_22

/-!
# Theorem 22 on the word RAM

"Plug Theorem 19 into Theorem 21."  Each bound has three ingredients.

1. The paper's deduction between running times, proved for every reading `M` of the sentence "is
   solved by a deterministic algorithm in time T" (lemmas such as `threeSum_of_uniform_theorem_21a`;
   nothing is assumed about `M`).
2. The reading `lightModel`, in which the sentence means that a program of the light language solves
   the task within T steps.  For this reading the reductions that Theorem 21 cites are theorems,
   because they are written as programs that call an arbitrary solver (`Sec3.claim_…`); so
   Theorem 21 holds for it: `claim_theorem_21a` for 3SUM, `claim_theorem_21b_minPlus` and
   `claim_theorem_21b_apsp` for the (min,+)-product and APSP.
3. The way to the machine: a solver of a task, with one more procedure for the input layout,
   compiled, is a program of the word RAM that takes a constant times as many steps
   (`Sec3.realized_threeSum`, `realized_minPlusProduct`, `realized_apsp`).

From a bound `O(s^{3−δ} (log s)^e)` for Exact Triangle this gives

* 3SUM in `O(n^a)` time for every `a > 2 − δ/2` (`threeSum_of_uniform`);
* the (min,+)-product and APSP in `O(n^{3−δ/3} (log n)^{O(1)})` time (`minPlus_polylog_of_uniform`,
  `apsp_polylog_of_uniform`), and so in `O(n^a)` time for every `a > 3 − δ/3`
  (`SolvedInPolylogTime.solvedInTime`).

The theorem is the case `δ = 1/648` (using Theorem 5) and the case `δ = ε' = 0.00175` (using
Corollary 26).  For 3SUM the programs lose polylogarithmic factors only
(`Theorem22.threeSum_polylog`); the printed form with `n^{o(1)}` follows
(`SolvedInPolylogTime.solvedInLittleOTime`).
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3

/-! ## Theorem 21 for programs of the light language -/

/-- Theorem 21(a): 3SUM from Exact Triangle, through Convolution-3SUM. -/
theorem claim_theorem_21a : Claim.Theorem_21a lightModel :=
  Theorem21a.of_CH20_VW13 _ ChanHe.claim_CH20_Theorem_5_1
    claim_VW13_Theorem_4_3

/-- Theorem 21(b): the (min,+)-product from Exact Triangle, through Negative Triangle. -/
theorem claim_theorem_21b_minPlus : Claim.Theorem_21b_minPlus lightModel :=
  Theorem21b.minPlus_of_VW13_VW18 _ claim_VW13_Theorem_3_3
    claim_VW18_Theorem_4_2

/-- Theorem 21(b): APSP from Exact Triangle, through the (min,+)-product. -/
theorem claim_theorem_21b_apsp : Claim.Theorem_21b_apsp lightModel :=
  Theorem21b.apsp_of_minPlus _ claim_theorem_21b_minPlus claim_apspFromMinPlus

/-! ## A bound for Exact Triangle, plugged into Theorem 21 -/

/-- 3SUM in `O(n^a)` time for every `a > 2 − δ/2`. -/
theorem threeSum_of_uniform {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform lightModel δ e) {a : ℝ} (ha : 2 - δ / 2 < a) :
    SolvedInTime EndStatement.ThreeSum a 0 :=
  FromClaims.solvedInTime_of_claim realized_threeSum
    ((threeSum_of_uniform_theorem_21a _ e hδ hu claim_theorem_21a).mono
      fun _ hf => hf.upperBigOPow ha)

/-- The (min,+)-product in `O(n^{3−δ/3} (log n)^{O(1)})` time. -/
theorem minPlus_polylog_of_uniform {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform lightModel δ e) :
    SolvedInPolylogTime EndStatement.MinPlusProduct (3 - δ / 3) :=
  FromClaims.solvedInPolylogTime_of_claim realized_minPlusProduct
    (minPlus_of_uniform_theorem_21b _ e hδ hu claim_theorem_21b_minPlus)

/-- APSP in `O(n^{3−δ/3} (log n)^{O(1)})` time. -/
theorem apsp_polylog_of_uniform {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform lightModel δ e) :
    SolvedInPolylogTime EndStatement.APSP (3 - δ / 3) :=
  FromClaims.solvedInPolylogTime_of_claim realized_apsp
    (apsp_of_uniform_theorem_21b _ e hδ hu claim_theorem_21b_apsp)

end Light.Sec3

namespace ThreeSumApsp

/-- **Theorem 22**, on the word RAM: the bounds using Theorem 5. -/
theorem wordRam_theorem_22_first : Items.Theorem_22_first := by
  have hu := Light.Sec3.claim_exactTriangleUniform_usingTheorem5
  have hminPlus := Light.Sec3.minPlus_polylog_of_uniform (by norm_num) hu
  have hapsp := Light.Sec3.apsp_polylog_of_uniform (by norm_num) hu
  rw [show (3 : ℝ) - 1 / 648 / 3 = 3 - 1 / 1944 by norm_num] at hminPlus hapsp
  exact ⟨Light.Sec3.threeSum_of_uniform (by norm_num) hu (by norm_num), hminPlus, hapsp,
    hminPlus.solvedInTime (by norm_num), hapsp.solvedInTime (by norm_num)⟩

/-- **Theorem 22**, on the word RAM: the bounds using Corollary 26. -/
theorem wordRam_theorem_22_second : Items.Theorem_22_second :=
  have hu := Light.Sec3.claim_exactTriangleUniform_usingCorollary26
  have hminPlus := Light.Sec3.minPlus_polylog_of_uniform (by norm_num) hu
  have hapsp := Light.Sec3.apsp_polylog_of_uniform (by norm_num) hu
  ⟨Light.Sec3.threeSum_of_uniform (by norm_num) hu (by norm_num), hminPlus, hapsp,
    hminPlus.solvedInTime (by norm_num), hapsp.solvedInTime (by norm_num)⟩

/-- The bound for 3SUM using Corollary 26. -/
theorem WordRam.Items.Theorem_22_second.threeSum (h : Items.Theorem_22_second) :
    SolvedInTime EndStatement.ThreeSum 1.9992 0 :=
  h.1

/-- The bound for the (min,+)-product using Corollary 26. -/
theorem WordRam.Items.Theorem_22_second.minPlus (h : Items.Theorem_22_second) :
    SolvedInTime EndStatement.MinPlusProduct 2.99942 0 :=
  h.2.2.2.1

/-- The bound for APSP using Corollary 26. -/
theorem WordRam.Items.Theorem_22_second.apsp (h : Items.Theorem_22_second) :
    SolvedInTime EndStatement.APSP 2.99942 0 :=
  h.2.2.2.2

/-- Theorem 22, on the word RAM, with `(log n)^{O(1)}` in place of `n^{o(1)}`: 3SUM in
`O(n^{2−1/1296} (log n)^{O(1)})` and in `O(n^{2−ε'/2} (log n)^{O(1)})` time.

NOTE.  Theorem 22 has `n^{o(1)}` here.  The programs give `(log n)^{O(1)}`, and the printed form
follows (`wordRam_theorem_22_threeSum`). -/
theorem Theorem22.threeSum_polylog :
    SolvedInPolylogTime EndStatement.ThreeSum (2 - 1 / 1296) ∧
      SolvedInPolylogTime EndStatement.ThreeSum (2 - 0.00175 / 2) := by
  have hfirst := Light.Sec3.threeSum_solvedInPolylogTime (by norm_num)
    Light.Sec3.claim_exactTriangleUniform_usingTheorem5
  rw [show (2 : ℝ) - 1 / 648 / 2 = 2 - 1 / 1296 by norm_num] at hfirst
  exact ⟨hfirst, Light.Sec3.threeSum_solvedInPolylogTime (by norm_num)
    Light.Sec3.claim_exactTriangleUniform_usingCorollary26⟩

/-- **Theorem 22**, on the word RAM: 3SUM in `n^{2−1/1296+o(1)}` and in `n^{2−ε'/2+o(1)}`
time. -/
theorem wordRam_theorem_22_threeSum : Items.Theorem_22_threeSum :=
  ⟨Theorem22.threeSum_polylog.1.solvedInLittleOTime,
    Theorem22.threeSum_polylog.2.solvedInLittleOTime⟩

end ThreeSumApsp
