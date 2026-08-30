/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PairCeiling/NearCUE.lean — the stability constants for grid laws whose pair rows are those of the sine process up to τ.

If the grid form factor S : ℕ → ℝ (atom masses s_j = S(j)/N at j/N) satisfies |N·S(j) − j| ≤ τ for 0 < j < N — the closed-band
row S(N) being free — then the integrated discrepancy E = ∫₀ˣ D of Defs.lean obeys, on all of [0,1],
      |E(x)| ≤ 1/(6N²) + τ/(2N),
in particular |E(1)| ≤ 1/(6N²) + τ/(2N); the free row enters only D(1) = Σ_j s_j − 1/2.  (Exact computation on each cell
[m/N, (m+1)/N]: with N·x = m + θ,  N³·E(x) = (−m + 3mθ(1−θ) − θ³)/6 + (perturbation of size ≤ m(m+1)τ/2), and
−(m+1) ≤ −m + 3mθ(1−θ) − θ³ ≤ 0.)  Consequently THEOREM 1′ (Stability.lean) holds for every such law with the constants
e₁ = M = 1/(6N²) + τ/(2N):  v ≤ p + d₁·|r(1)| + (1/(6N²) + τ/(2N))·(|r′(1)| + ∫₀¹|r″|)  for every certificate (c₀, r) with
c₀ + Σ_j s_j r(j/N) ≤ p and |D(1)| ≤ d₁.
-/
import Zeta23.PairCeiling.Ceiling
import Zeta23.PairCeiling.Bridge

open scoped BigOperators Interval
open MeasureTheory Set intervalIntegral Finset

noncomputable section

namespace Zeta23
namespace PairCeiling

variable {S : ℕ → ℝ} {N : ℕ} {τ : ℝ}

/-! ## 1. The row hypothesis propagated to the partial sums T and U -/

/-- **near-CUE rows.** -/
def NearCUE (S : ℕ → ℝ) (N : ℕ) (τ : ℝ) : Prop := ∀ j : ℕ, 1 ≤ j → j < N → |(N : ℝ) * S j - j| ≤ τ

/-- N·T_m = m(m+1)/2 up to m·τ, for m ≤ N − 1 (only rows j < N enter). -/
lemma abs_T_sub_le (h : NearCUE S N τ) {m : ℕ} (hm : m + 1 ≤ N) :
    |(N : ℝ) * T S m - (m : ℝ) * (m + 1) / 2| ≤ m * τ := by
  induction m with
  | zero => simp [T_zero]
  | succ m ih =>
    have ih' := ih (by omega)
    have hrow := h (m + 1) (by omega) (by omega)
    rw [T_succ]
    push_cast at hrow ⊢
    have e : (N : ℝ) * (T S m + S (m + 1)) - ((m : ℝ) + 1) * ((m : ℝ) + 1 + 1) / 2
        = ((N : ℝ) * T S m - (m : ℝ) * (m + 1) / 2) + ((N : ℝ) * S (m + 1) - ((m : ℝ) + 1)) := by ring
    rw [e]
    calc |((N : ℝ) * T S m - (m : ℝ) * (m + 1) / 2) + ((N : ℝ) * S (m + 1) - ((m : ℝ) + 1))|
        ≤ |(N : ℝ) * T S m - (m : ℝ) * (m + 1) / 2| + |(N : ℝ) * S (m + 1) - ((m : ℝ) + 1)| := abs_add_le _ _
      _ ≤ m * τ + τ := add_le_add ih' hrow
      _ = ((m : ℝ) + 1) * τ := by ring

/-- N·U_m = (m³ − m)/6 up to m(m−1)τ/2, for m ≤ N. -/
lemma abs_U_sub_le (h : NearCUE S N τ) {m : ℕ} (hm : m ≤ N) :
    |(N : ℝ) * U S m - ((m : ℝ) ^ 3 - m) / 6| ≤ (m : ℝ) * (m - 1) / 2 * τ := by
  induction m with
  | zero => simp [U_zero]
  | succ m ih =>
    have ih' := ih (by omega)
    have hT := abs_T_sub_le h (by omega : m + 1 ≤ N)
    rw [U_succ]
    push_cast
    have e : (N : ℝ) * (U S m + T S m) - (((m : ℝ) + 1) ^ 3 - ((m : ℝ) + 1)) / 6
        = ((N : ℝ) * U S m - ((m : ℝ) ^ 3 - m) / 6) + ((N : ℝ) * T S m - (m : ℝ) * (m + 1) / 2) := by ring
    rw [e]
    calc |((N : ℝ) * U S m - ((m : ℝ) ^ 3 - m) / 6) + ((N : ℝ) * T S m - (m : ℝ) * (m + 1) / 2)|
        ≤ |(N : ℝ) * U S m - ((m : ℝ) ^ 3 - m) / 6| + |(N : ℝ) * T S m - (m : ℝ) * (m + 1) / 2| := abs_add_le _ _
      _ ≤ (m : ℝ) * (m - 1) / 2 * τ + m * τ := add_le_add ih' hT
      _ = ((m : ℝ) + 1) * ((m : ℝ) + 1 - 1) / 2 * τ := by ring

/-! ## 2. E on a closed cell -/

/-- integrability of D on any subinterval of [0,1]. -/
private lemma ii_Dfun (hN : 0 < N) {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (Dfun (massOf S N) N) volume a b :=
  (intervalIntegrable_Dfun hN).mono_set (by
    rw [Set.uIcc_of_le zero_le_one]; exact Set.uIcc_subset_Icc ha hb)

/-- **E on the cell [m/N, (m+1)/N]** (m < N):  E(x) = E(m/N) + (T_m/N)(x − m/N) − (x³ − (m/N)³)/6. -/
lemma Efun_cell (hN : 0 < N) {m : ℕ} (hm : m < N) {x : ℝ} (hx : x ∈ Icc ((m : ℝ) / N) ((m + 1 : ℝ) / N)) :
    Efun (massOf S N) N x = Egrid S N m + T S m / N * (x - (m : ℝ) / N) - (x ^ 3 - ((m : ℝ) / N) ^ 3) / 6 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : ((m : ℝ) / N) ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hNr]; exact_mod_cast hm.le⟩
  have hb1 : ((m + 1 : ℝ) / N) ≤ 1 := by rw [div_le_one hNr]; exact_mod_cast hm
  have hxI : x ∈ Icc (0:ℝ) 1 := ⟨le_trans ha.1 hx.1, le_trans hx.2 hb1⟩
  -- split the integral at m/N
  have hsplit : Efun (massOf S N) N x = Efun (massOf S N) N ((m : ℝ) / N) + ∫ t in ((m : ℝ) / N)..x, Dfun (massOf S N) N t := by
    unfold Efun
    rw [integral_add_adjacent_intervals (ii_Dfun hN ⟨le_rfl, zero_le_one⟩ ha) (ii_Dfun hN ha hxI)]
  rw [hsplit, Efun_grid_eq_Egrid hN hm.le]
  -- on Ι(m/N, x) ⊆ the cell, D = T_m/N − t²/2 almost everywhere
  have hae : ∀ᵐ t ∂volume, t ∈ Ι ((m : ℝ) / N) x → Dfun (massOf S N) N t = T S m / N - t ^ 2 / 2 := by
    filter_upwards [Cstep_ae_cell (s := massOf S N) hN hm] with t ht hmem
    have hmem' : t ∈ Ι ((m : ℝ) / N) ((m + 1 : ℝ) / N) := by
      rw [Set.uIoc_of_le hx.1] at hmem
      rw [Set.uIoc_of_le (cell_le hN m)]
      exact ⟨hmem.1, le_trans hmem.2 hx.2⟩
    rw [Dfun, ht hmem', Csum_massOf]
  rw [integral_congr_ae hae]
  -- ∫ (c − t²/2) = c(x − a) − (x³ − a³)/6
  have hF : ∀ t ∈ uIcc ((m : ℝ) / N) x, HasDerivAt (fun t : ℝ => T S m / N * t - t ^ 3 / 6) (T S m / N - t ^ 2 / 2) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => T S m / N * t) (T S m / N) t := by
      simpa using (hasDerivAt_id t).const_mul (T S m / N)
    have h2 : HasDerivAt (fun t : ℝ => t ^ 3 / 6) (t ^ 2 / 2) t := by
      have := (hasDerivAt_pow 3 t).div_const 6
      exact this.congr_deriv (by push_cast; ring)
    exact h1.sub h2
  rw [integral_eq_sub_of_hasDerivAt hF ((by fun_prop : Continuous fun t : ℝ => T S m / N - t ^ 2 / 2).intervalIntegrable _ _)]
  ring

/-! ## 3. The sup bound -/

/-- the cubic on a cell: −(m+1) ≤ −m + 3mθ(1−θ) − θ³ ≤ 0 for 0 ≤ θ ≤ 1, m ≥ 0. -/
private lemma cubic_bounds {m θ : ℝ} (hm : 0 ≤ m) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    -(m + 1) ≤ -m + 3 * m * θ * (1 - θ) - θ ^ 3 ∧ -m + 3 * m * θ * (1 - θ) - θ ^ 3 ≤ 0 := by
  have hθ1 : 0 ≤ 1 - θ := by linarith
  have hprod : 0 ≤ θ * (1 - θ) := mul_nonneg h0 hθ1
  have hq : θ * (1 - θ) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * θ - 1)]
  have hcube : θ ^ 3 ≤ 1 := by
    calc θ ^ 3 ≤ 1 ^ 3 := by gcongr
      _ = 1 := by norm_num
  have hcube0 : 0 ≤ θ ^ 3 := by positivity
  constructor
  · nlinarith [mul_nonneg hm hprod]
  · nlinarith [mul_le_mul_of_nonneg_left hq hm]

/-- **the integrated discrepancy of a near-CUE law**: |E| ≤ 1/(6N²) + τ/(2N) on [0,1]. -/
theorem abs_Efun_le_of_nearCUE (hN : 0 < N) (hτ : 0 ≤ τ) (h : NearCUE S N τ) :
    ∀ x ∈ Icc (0:ℝ) 1, |Efun (massOf S N) N x| ≤ 1 / (6 * (N : ℝ) ^ 2) + τ / (2 * N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  intro x hx
  -- the cell index m < N with x ∈ [m/N, (m+1)/N]
  obtain ⟨m, hmN, hxm⟩ : ∃ m : ℕ, m < N ∧ x ∈ Icc ((m : ℝ) / N) ((m + 1 : ℝ) / N) := by
    rcases eq_or_lt_of_le hx.2 with hx1 | hx1
    · refine ⟨N - 1, Nat.sub_lt hN one_pos, ?_, ?_⟩
      · rw [hx1, div_le_one hNr]; exact_mod_cast Nat.sub_le N 1
      · rw [hx1, le_div_iff₀ hNr, one_mul]
        have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub hN]; simp
        rw [this]; linarith
    · refine ⟨⌊(N : ℝ) * x⌋₊, ?_, ?_, ?_⟩
      · have h1 : ((⌊(N:ℝ) * x⌋₊ : ℕ) : ℝ) ≤ N * x := Nat.floor_le (by have := hx.1; positivity)
        have h2 : (N:ℝ) * x < N := by nlinarith
        exact_mod_cast lt_of_le_of_lt h1 h2
      · rw [div_le_iff₀ hNr]
        have := Nat.floor_le (show 0 ≤ (N:ℝ) * x by have := hx.1; positivity)
        linarith [mul_comm (N:ℝ) x]
      · rw [le_div_iff₀ hNr]
        have := Nat.lt_floor_add_one ((N:ℝ) * x)
        linarith [mul_comm (N:ℝ) x]
  rw [Efun_cell hN hmN hxm]
  -- write N·x = m + θ
  set θ : ℝ := (N : ℝ) * x - m with hθ
  have hθ0 : 0 ≤ θ := by
    have := hxm.1; rw [div_le_iff₀ hNr] at this; rw [hθ]; linarith [mul_comm x (N:ℝ)]
  have hθ1 : θ ≤ 1 := by
    have := hxm.2; rw [le_div_iff₀ hNr] at this; rw [hθ]; linarith [mul_comm x (N:ℝ)]
  have hxe : x = ((m : ℝ) + θ) / N := by rw [hθ]; field_simp; ring
  -- the perturbations
  set P : ℝ := (N : ℝ) * U S m - ((m : ℝ) ^ 3 - m) / 6 with hP
  set Δ : ℝ := (N : ℝ) * T S m - (m : ℝ) * (m + 1) / 2 with hΔ
  have hPb : |P| ≤ (m : ℝ) * (m - 1) / 2 * τ := abs_U_sub_le h hmN.le
  have hΔb : |Δ| ≤ m * τ := abs_T_sub_le h (Nat.succ_le_of_lt hmN)
  -- the identity  N³·E = (−m + 3mθ(1−θ) − θ³)/6 + P + Δθ
  have hid : Egrid S N m + T S m / N * (x - (m : ℝ) / N) - (x ^ 3 - ((m : ℝ) / N) ^ 3) / 6
      = ((-(m : ℝ) + 3 * m * θ * (1 - θ) - θ ^ 3) / 6 + P + Δ * θ) / (N : ℝ) ^ 3 := by
    have eU : U S m = (P + ((m : ℝ) ^ 3 - m) / 6) / N := by rw [hP]; field_simp; ring
    have eT : T S m = (Δ + (m : ℝ) * (m + 1) / 2) / N := by rw [hΔ]; field_simp; ring
    unfold Egrid
    rw [eU, eT, hxe]
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (by positivity : (0:ℝ) < (N:ℝ) ^ 3)]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (N:ℝ) ^ 3)]
  -- bound the numerator
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (m : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hmN
  obtain ⟨hc1, hc2⟩ := cubic_bounds hm0 hθ0 hθ1
  have hmain : |(-(m : ℝ) + 3 * m * θ * (1 - θ) - θ ^ 3) / 6| ≤ (N : ℝ) / 6 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 6), div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 6), abs_le]
    constructor <;> linarith
  have hpert : |P + Δ * θ| ≤ (N : ℝ) ^ 2 / 2 * τ := by
    calc |P + Δ * θ| ≤ |P| + |Δ * θ| := abs_add_le _ _
      _ = |P| + |Δ| * θ := by rw [abs_mul, abs_of_nonneg hθ0]
      _ ≤ (m : ℝ) * (m - 1) / 2 * τ + m * τ * θ := by gcongr
      _ ≤ (m : ℝ) * (m - 1) / 2 * τ + m * τ * 1 := by gcongr
      _ = (m : ℝ) * (m + 1) / 2 * τ := by ring
      _ ≤ (N : ℝ) ^ 2 / 2 * τ := by
          apply mul_le_mul_of_nonneg_right _ hτ
          all_goals nlinarith
  calc |(-(m : ℝ) + 3 * m * θ * (1 - θ) - θ ^ 3) / 6 + P + Δ * θ|
      ≤ |(-(m : ℝ) + 3 * m * θ * (1 - θ) - θ ^ 3) / 6| + |P + Δ * θ| := by
        rw [add_assoc]; exact abs_add_le _ _
    _ ≤ (N : ℝ) / 6 + (N : ℝ) ^ 2 / 2 * τ := add_le_add hmain hpert
    _ = (1 / (6 * (N : ℝ) ^ 2) + τ / (2 * N)) * (N : ℝ) ^ 3 := by field_simp

/-- in particular at x = 1. -/
theorem abs_Efun_one_le_of_nearCUE (hN : 0 < N) (hτ : 0 ≤ τ) (h : NearCUE S N τ) :
    |Efun (massOf S N) N 1| ≤ 1 / (6 * (N : ℝ) ^ 2) + τ / (2 * N) :=
  abs_Efun_le_of_nearCUE hN hτ h 1 ⟨zero_le_one, le_rfl⟩

/-! ## 4. Theorem 1′ for near-CUE laws -/

/-- **CEILING FOR A NEAR-CUE GRID LAW.**  Let S be any grid form factor with |N·S(j) − j| ≤ τ for 0 < j < N (atom masses
s_j = S(j)/N at j/N; the row j = N free), and |D(1)| ≤ d₁.  For every certificate (c₀, r) — r ∈ C¹[0,1] with r′ =: g differentiable
off a countable set with integrable derivative h — that is valid against the law, c₀ + Σ_{j=1}^N s_j r(j/N) ≤ p, one has
      c₀ + ∫₀¹ r(x)·x dx ≤ p + d₁·|r(1)| + (1/(6N²) + τ/(2N))·|r′(1)| + (1/(6N²) + τ/(2N))·∫₀¹|r″|. -/
theorem ceiling_nearCUE (hN : 0 < N) (S : ℕ → ℝ) {τ d₁ : ℝ} (hτ : 0 ≤ τ) (hS : NearCUE S N τ)
    (hD1 : |Dfun (massOf S N) N 1| ≤ d₁)
    {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {c₀ p : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 N, massOf S N j * r ((j:ℝ)/N) ≤ p) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x
      ≤ p + d₁ * |r 1| + (1 / (6 * (N : ℝ) ^ 2) + τ / (2 * N)) * |g 1|
          + (1 / (6 * (N : ℝ) ^ 2) + τ / (2 * N)) * ∫ x in (0:ℝ)..1, |h x| :=
  ceiling_numeric hN hT hr hg hgh hh (abs_Efun_le_of_nearCUE hN hτ hS) hD1
    (abs_Efun_one_le_of_nearCUE hN hτ hS) le_rfl le_rfl le_rfl hvalid

end PairCeiling
end Zeta23

end
