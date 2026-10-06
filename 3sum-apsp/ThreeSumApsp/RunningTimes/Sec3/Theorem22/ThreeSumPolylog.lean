/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Program
public import ThreeSumApsp.Programs.Sec3.Theorem21a.Convolution.TimeBound
public import ThreeSumApsp.RunningTimes.FromClaims.Bounds
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ThreeSumLayout
public import ThreeSumApsp.Util.Asymptotics.LogU

/-!
# 3SUM with polylogarithmic factors only

Theorem 22 states the time `n^{2−δ/2+o(1)}` for 3SUM, where `n^{3−δ}` is the time for Exact
Triangle. The two reductions as programmed here (`ChanHe.claim_CH20_Theorem_5_1`, `isHost_c3`) lose
polylogarithmic factors only: 3SUM on `n` numbers makes `(log n)^{O(1)}` instances of
Convolution-3SUM of length `N = n (log n)^{O(1)}`, and each of them `2t` instances of Exact Triangle
on `t = ⌊√N⌋ + 1` vertices per part. So the time is `O(n^{2−δ/2} (log n)^{O(1)})`.

The route: Convolution-3SUM from Exact Triangle (`c3_solvedIn_explicit`); its time at the lengths
`N = Õ(n)` is `Õ(n^{2−δ/2})` (`Polylog.c3_class`, by the closure lemmas of `IsPowPolylog`); the sum
over the instances of `ChanHe.claim_CH20_Theorem_5_1` (`threeSum_polylog_claim`); the transfer to
the word RAM (`threeSum_solvedInPolylogTime`, the result).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.WordRam Filter Asymptotics

/-- The time of Convolution-3SUM at the lengths `N n = Õ(n)` and the bounds `mag n` that the
reduction from 3SUM asks for is `Õ(n^{2−δ/2})`. -/
theorem Polylog.c3_class {N : ℕ → ℕ} {mag : ℕ → ℝ} {c' κ' C K δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1)
    (hN : IsPowPolylog (fun n => (N n : ℝ)) 1)
    (hb : ∀ n : ℕ, 1 ≤ n → 1 ≤ N n ∧ 1 ≤ mag n ∧ mag n ≤ c' * (n : ℝ) ^ κ') :
    IsPowPolylog (fun n => C * (N n : ℝ) ^ (3 / 2 : ℝ) * (1 + logU (mag n)) +
      2 * ((Nat.sqrt (N n) + 1 : ℕ) : ℝ) * uniformTime K δ e (Nat.sqrt (N n) + 1) (3 * mag n))
      (2 - δ / 2) := by
  have hmag : ∀ n : ℕ, 1 ≤ n → 1 ≤ mag n ∧ mag n ≤ c' * (n : ℝ) ^ κ' := fun n hn => (hb n hn).2
  -- the length to the power 3/2, and the two logarithms of the bound
  have hlen := hN.rpow (r := 3 / 2) (by norm_num)
  have hlog1 := (isPowPolylog_const 1).add (isPowPolylog_logU_of_le hmag)
  have hlog3 := ((isPowPolylog_const 1).add (isPowPolylog_logU_of_le (mag := fun n => 3 * mag n)
    (c := 3 * c') fun n hn => ⟨by linarith [(hmag n hn).1], by
      rw [mul_assoc]
      linarith [(hmag n hn).2]⟩)).pow 2
  -- the number of vertices, its power 3 - δ and its logarithm
  have hsize : IsPowPolylog (fun n => ((Nat.sqrt (N n) + 1 : ℕ) : ℝ)) (1 * (1 / 2)) := by
    refine ((hN.rpow (r := 1 / 2) (by norm_num)).const_mul 2).mono_left_of_nonneg
      (Eventually.of_forall fun n => by positivity) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact natSqrt_succ_le (hb n hn).1
  have hsizePow := hsize.rpow (r := 3 - δ) (by linarith)
  have hsizeLog := ((hsize.isBigOPow
    (by norm_num : (1 * (1 / 2) : ℝ) < 1)).isPowPolylog_log_natCast.add
    (isPowPolylog_const 1)).pow e
  -- the sum
  refine (((hlen.mul hlog1).const_mul C).mono (by linarith)).add
    (((hsize.const_mul 2).mul (((hsizePow.mul hsizeLog).mul hlog3).const_mul K)).mono
      (by linarith)) |>.congr (Eventually.of_forall fun n => ?_)
  simp only [uniformTime]
  ring

/-- **3SUM in time `O(n^{2−δ/2} (log n)^{O(1)})`** by programs of the light language, if Exact
Triangle is solved in the uniform time with exponent `3 − δ`. -/
theorem threeSum_polylog_claim {δ : ℝ} {e : ℕ} (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform lightModel δ e) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ T : ℕ → ℝ → ℝ, SolvedIn s3Task T ∧
      UpperPowPolylog (fun n => T n ((n : ℝ) ^ κ)) (2 - δ / 2) := by
  obtain ⟨K, hK, hT⟩ := hu
  obtain ⟨E, Num, mag, N, c', κ', hE, hNum, hN, hb, hF⟩ :=
    ChanHe.claim_CH20_Theorem_5_1 κ hκ
  obtain ⟨C, hC, hown⟩ := exists_c3Own_le
  obtain ⟨T', hs, hle⟩ := hF _ (c3_solvedIn_explicit hC hown (T := uniformTime K δ e) hT)
  have hclass := (hE.abs.mono (by linarith : (3 / 2 : ℝ) ≤ 2 - δ / 2)).add
    ((hNum.abs.mul (Polylog.c3_class (C := C) (K := K) e hδ1 hN hb)).mono
      (by linarith : (0 : ℝ) + (2 - δ / 2) ≤ 2 - δ / 2))
  refine ⟨T', hs, hclass.upperPowPolylog.mono_left ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hlog1 := (logU_pos (mag n)).le
  have hlog3 := (logU_pos (3 * mag n)).le
  have hlogS : 0 ≤ Real.log ((Nat.sqrt (N n) + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 _)
  have hK0 : 0 ≤ K := by linarith
  refine (hle n hn).trans (add_le_add (le_abs_self _)
    (mul_le_mul_of_nonneg_right (le_abs_self _) ?_))
  rw [uniformTime]
  positivity

/-- 3SUM in time `O(n^{2−δ/2} (log n)^{O(1)})` on the word RAM, if Exact Triangle is solved in the
uniform time with exponent `3 − δ`. -/
theorem threeSum_solvedInPolylogTime {δ : ℝ} {e : ℕ} (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform lightModel δ e) :
    SolvedInPolylogTime EndStatement.ThreeSum (2 - δ / 2) := by
  intro κ
  obtain ⟨T, hs, C, e', hb⟩ := threeSum_polylog_claim hδ1 hu κ (Nat.cast_nonneg κ)
  exact ⟨e', FromClaims.solvedAt_of_realized T κ (realized_threeSum T hs) hb⟩

end Light.Sec3
