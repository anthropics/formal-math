/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec3.Theorem21a.Convolution.Host

/-!
# Convolution-3SUM from Exact Triangle: the claim

Theorem 21(a), after [VW13, Theorem 4.3].  The arithmetic that turns the
host `isHost_c3` into the transfer of running times: if Exact Triangle is solved in time T, then
Convolution-3SUM on N numbers of absolute value at most u is solved in time
O(N^{3/2}) (1 + log u) + 2 (⌊√N⌋ + 1) T(⌊√N⌋ + 1, 3u) (`c3_solvedIn_explicit`,
`claim_VW13_Theorem_4_3`).

The host's own work is a cubic polynomial in ⌊√N⌋ (`exists_c3Own_le`), and the instances have
⌊√N⌋ + 1 ≤ 2 √N vertices per part (`natSqrt_succ_le`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp

/-- `⌊√N⌋ + 1 ≤ 2 N^{1/2}` for `N ≥ 1`. -/
theorem natSqrt_succ_le {N : ℕ} (hN : 1 ≤ N) :
    ((Nat.sqrt N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  have hfloor : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hone : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.2 (by exact_mod_cast hN)
  push_cast
  linarith

/-- `⌊√N⌋ + 1 = O(N^{1/2})`. -/
private theorem isBigOPow_natSqrt_succ :
    IsBigOPow (fun N : ℕ => ((Nat.sqrt N + 1 : ℕ) : ℝ)) (1 / 2) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact natSqrt_succ_le hN

/-- The host's own work: its time over a solver that takes no time. -/
def c3Own (N : ℕ) : ℕ := c3Time (fun _ _ => 0) N 0

/-- The time of the host is its own work and 2 (⌊√N⌋ + 1) runs of the solver. -/
theorem c3Time_eq (T : ℕ → ℕ → ℕ) (N U : ℕ) :
    c3Time T N U = c3Own N + 2 * (Nat.sqrt N + 1) * T (Nat.sqrt N + 1) (2 * U + 1) := by
  unfold c3Own c3Time c3RoundTime
  ring

/-- The host's own work is a cubic polynomial in ⌊√N⌋, so it is O(N^{3/2}). -/
theorem exists_c3Own_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → (c3Own N : ℝ) ≤ C * (N : ℝ) ^ (3 / 2 : ℝ) := by
  -- powers of 2 √N
  let s : Scale ℕ (Fin 1) := .ofBases (1 ≤ ·) (fun _ N => 2 * (N : ℝ) ^ (1 / 2 : ℝ)) fun _ N hN =>
    le_trans (by exact_mod_cast Nat.le_add_left 1 (Nat.sqrt N)) (natSqrt_succ_le hN)
  have hside : s.SoftO (fun N => Nat.sqrt N + 1) _ := .of_le_base 0 fun _ hN => natSqrt_succ_le hN
  have hown : s.SoftO c3Own ![3] := by
    unfold c3Own c3Time c3RoundTime convFillTime
    growth [hside, hside.of_le fun N _ => Nat.le_succ (Nat.sqrt N)]
  obtain ⟨C, hC, hle⟩ := hown.dominated fun _ _ => rfl
  refine ⟨C * 8, by positivity, fun N hN => (hle N hN).trans_eq ?_⟩
  have hpow : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 3 = (N : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul N.cast_nonneg]
    norm_num
  simp only [Scale.mon, s, Scale.ofBases, Fin.prod_univ_one, Matrix.cons_val_zero, mul_pow, hpow]
  ring

/-- Convolution-3SUM from Exact Triangle, with the explicit bound, where C is the constant of the
host's own work.  The weights of the instances are bounded by 2U + 1 ≤ 3u, because 1 ≤ U ≤ u.  The
factor 1 + log u is not needed here; it is the form in which the claim is stated. -/
theorem c3_solvedIn_explicit {C : ℝ} (hC : 0 ≤ C)
    (hown : ∀ N : ℕ, 1 ≤ N → (c3Own N : ℝ) ≤ C * (N : ℝ) ^ (3 / 2 : ℝ)) {T : ℕ → ℝ → ℝ}
    (hT : SolvedIn etTask T) :
    SolvedIn c3Task fun N u => C * (N : ℝ) ^ (3 / 2 : ℝ) * (1 + logU u) +
      2 * ((Nat.sqrt N + 1 : ℕ) : ℝ) * T (Nat.sqrt N + 1) (3 * u) := by
  refine isHost_c3.solvedIn hT fun Tn hTn N U u hN hU hu => ?_
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hsolver : (Tn (Nat.sqrt N + 1) (2 * U + 1) : ℝ) ≤ T (Nat.sqrt N + 1) (3 * u) :=
    hTn _ _ _ (by omega) (by omega) (by push_cast; linarith)
  have hlog : 0 ≤ logU u := Real.log_nonneg (le_trans (by norm_num) (le_max_right u 2))
  rw [c3Time_eq]
  push_cast
  -- the host's own work, and 2 (⌊√N⌋ + 1) runs of the solver
  exact add_le_add ((hown N hN).trans (le_mul_of_one_le_right (by positivity) (by linarith)))
    (mul_le_mul_of_nonneg_left hsolver (by positivity))

/-- [VW13, Theorem 4.3] for programs of the light language: Convolution-3SUM from Exact Triangle. -/
theorem claim_VW13_Theorem_4_3 : Claim.VW13_Theorem_4_3 lightModel :=
  let ⟨C, hC, hown⟩ := exists_c3Own_le
  ⟨3, fun N => C * (N : ℝ) ^ (3 / 2 : ℝ), fun N => 2 * ((Nat.sqrt N + 1 : ℕ) : ℝ),
    fun N => Nat.sqrt N + 1, by norm_num,
    IsBigOPow.isPowLittleO (Asymptotics.isBigO_const_mul_self _ _ _),
    isBigOPow_natSqrt_succ.const_mul_left 2, isBigOPow_natSqrt_succ, fun N _ => Nat.le_add_left 1 _,
    fun _ hT => c3_solvedIn_explicit hC hown hT⟩

end Light.Sec3
