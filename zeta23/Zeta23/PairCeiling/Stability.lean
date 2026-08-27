/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PairCeiling/Stability.lean — the analytic half of the bandwidth-1 pair-correlation ceiling theorem:
the configuration-free Abel/integration-by-parts identities and the stability bound.
For weights s at the grid j/N (Defs: Csum, Cstep, Dfun, Efun) and a weight r with r′ = g continuous on [0,1]:
  (A)  ∫₀¹ g·C = C_N·r(1) − Σ_{j=1}^{N} s_j r(j/N)                                  [cellwise FTC + Abel summation]
  (1)  Σ_j s_j r(j/N) − ∫₀¹ r(x)·x dx = r(1)·D(1) − ∫₀¹ g·D                           [first-order identity]
and, if g is differentiable off a finite set with derivative h, h integrable, (E continuous, E′ = D off the grid):
  (2)  … = r(1)·D(1) − g(1)·E(1) + ∫₀¹ h·E                                            [second-order identity]
  (B)  |…| ≤ |r 1|·|D 1| + |g 1|·|E 1| + M·∫₀¹|h|   whenever |E| ≤ M on [0,1].         [ceiling stability]
No sign condition on s. Standard axioms.
-/
import Zeta23.PairCeiling.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

open scoped BigOperators Interval
open MeasureTheory Set intervalIntegral

noncomputable section

namespace Zeta23
namespace PairCeiling

variable {s : ℕ → ℝ} {N : ℕ}

/-! ### 0. cell bookkeeping -/

lemma cell_le (hN : 0 < N) (m : ℕ) : (m:ℝ)/N ≤ (m+1:ℝ)/N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  gcongr; linarith

lemma cell_subset (hN : 0 < N) {m : ℕ} (hm : m < N) : uIcc ((m:ℝ)/N) ((m+1:ℝ)/N) ⊆ Icc (0:ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [uIcc_of_le (cell_le hN m)]
  refine Icc_subset_Icc (by positivity) ?_
  rw [div_le_one hNr]; exact_mod_cast hm

/-- a.e. on the cell (for the interval-integral measure), C = C_m. -/
lemma Cstep_ae_cell (hN : 0 < N) {m : ℕ} (hm : m < N) :
    ∀ᵐ x ∂volume, x ∈ Ι ((m:ℝ)/N) ((m+1:ℝ)/N) → Cstep s N x = Csum s m := by
  have : ∀ᵐ x ∂volume, x ≠ ((m+1:ℝ)/N) := by
    simpa [ae_iff] using (measure_singleton ((m+1:ℝ)/N) : volume {((m+1:ℝ)/N)} = 0)
  filter_upwards [this] with x hxb hx
  rw [uIoc_of_le (cell_le hN m)] at hx
  exact Cstep_eq_Csum_of_mem hN (Nat.succ_le_of_lt hm) ⟨hx.1.le, lt_of_le_of_ne hx.2 hxb⟩

/-- g·C is interval-integrable on each cell when g is continuous there. -/
lemma intervalIntegrable_gC_cell (hN : 0 < N) {m : ℕ} (hm : m < N) {g : ℝ → ℝ}
    (hg : ContinuousOn g (uIcc ((m:ℝ)/N) ((m+1:ℝ)/N))) :
    IntervalIntegrable (fun x => g x * Cstep s N x) volume ((m:ℝ)/N) ((m+1:ℝ)/N) := by
  have hgi : IntervalIntegrable (fun x => g x * Csum s m) volume ((m:ℝ)/N) ((m+1:ℝ)/N) :=
    hg.intervalIntegrable.mul_const _
  refine hgi.congr_ae ?_
  refine (ae_restrict_iff' (measurableSet_uIoc (a := ((m:ℝ)/N)) (b := ((m+1:ℝ)/N)))).mpr ?_
  filter_upwards [Cstep_ae_cell (s := s) hN hm] with x hx hmem
  rw [hx hmem]

/-! ### 1. (A): ∫₀¹ g·C via cells and Abel summation -/

/-- one cell: ∫ g·C = C_m (r(b) − r(a)). -/
lemma integral_cell (hN : 0 < N) {m : ℕ} (hm : m < N) {r g : ℝ → ℝ}
    (hr : ∀ x ∈ uIcc ((m:ℝ)/N) ((m+1:ℝ)/N), HasDerivAt r (g x) x)
    (hg : ContinuousOn g (uIcc ((m:ℝ)/N) ((m+1:ℝ)/N))) :
    ∫ x in ((m:ℝ)/N)..((m+1:ℝ)/N), g x * Cstep s N x = Csum s m * (r ((m+1:ℝ)/N) - r ((m:ℝ)/N)) := by
  have h1 : ∫ x in ((m:ℝ)/N)..((m+1:ℝ)/N), g x * Cstep s N x
      = ∫ x in ((m:ℝ)/N)..((m+1:ℝ)/N), g x * Csum s m := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Cstep_ae_cell (s := s) hN hm] with x hx hmem
    rw [hx hmem]
  rw [h1, intervalIntegral.integral_mul_const, intervalIntegral.integral_eq_sub_of_hasDerivAt hr hg.intervalIntegrable]
  ring

/-- (A) summed: ∫₀¹ g·C = Σ_{m<N} C_m (r((m+1)/N) − r(m/N)). -/
lemma integral_gC_eq_sum (hN : 0 < N) {r g : ℝ → ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1)) :
    ∫ x in (0:ℝ)..1, g x * Cstep s N x = ∑ m ∈ Finset.range N, Csum s m * (r ((m+1:ℝ)/N) - r ((m:ℝ)/N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun x => g x * Cstep s N x) (a := fun m : ℕ => (m:ℝ)/N) (n := N)
    (fun k hk => by
      simpa [Nat.cast_succ] using intervalIntegrable_gC_cell (s := s) hN hk (hg.mono (cell_subset hN hk)))
  simp only [Nat.cast_zero, zero_div] at key
  rw [div_self hNr.ne'] at key
  rw [← key]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.mp hm
  simpa [Nat.cast_succ] using
    integral_cell (s := s) hN hm' (fun x hx => hr x (cell_subset hN hm' hx)) (hg.mono (cell_subset hN hm'))

/-- Abel summation: Σ_{m<N} C_m (r_{m+1} − r_m) = C_N r(1) − Σ_{j=1}^{N} s_j r(j/N). -/
lemma abel (hN : 0 < N) (r : ℝ → ℝ) :
    ∑ m ∈ Finset.range N, Csum s m * (r ((m+1:ℝ)/N) - r ((m:ℝ)/N))
      = Csum s N * r 1 - ∑ j ∈ Finset.Icc 1 N, s j * r ((j:ℝ)/N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  suffices h : ∀ n : ℕ, ∑ m ∈ Finset.range n, Csum s m * (r ((m+1:ℝ)/N) - r ((m:ℝ)/N))
      = Csum s n * r ((n:ℝ)/N) - ∑ j ∈ Finset.Icc 1 n, s j * r ((j:ℝ)/N) by
    have := h N; rwa [div_self hNr.ne'] at this
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega), Csum_succ]
    push_cast
    ring

/-- (A): ∫₀¹ g·C = C_N r(1) − Σ_j s_j r(j/N). -/
theorem integral_gC (hN : 0 < N) {r g : ℝ → ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1)) :
    ∫ x in (0:ℝ)..1, g x * Cstep s N x = Csum s N * r 1 - ∑ j ∈ Finset.Icc 1 N, s j * r ((j:ℝ)/N) := by
  rw [integral_gC_eq_sum hN hr hg, abel hN r]

/-- integrability of g·C on [0,1] (from the cells). -/
lemma intervalIntegrable_gC (hN : 0 < N) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0:ℝ) 1)) :
    IntervalIntegrable (fun x => g x * Cstep s N x) volume 0 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h : ∀ k < N, IntervalIntegrable (fun x => g x * Cstep s N x) volume ((fun m : ℕ => (m:ℝ)/N) k) ((fun m : ℕ => (m:ℝ)/N) (k+1)) :=
    fun k hk => by simpa [Nat.cast_succ] using intervalIntegrable_gC_cell (s := s) hN hk (hg.mono (cell_subset hN hk))
  have := IntervalIntegrable.trans_iterate (a := fun m : ℕ => (m:ℝ)/N) h
  simpa [div_self hNr.ne'] using this

/-! ### 2. first-order identity -/

/-- ∫₀¹ r(x)·x dx = r(1)/2 − ∫₀¹ g(x)·(x²/2) dx. -/
lemma integral_r_mul_id {r g : ℝ → ℝ} (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x)
    (hg : ContinuousOn g (Icc (0:ℝ) 1)) :
    ∫ x in (0:ℝ)..1, r x * x = r 1 / 2 - ∫ x in (0:ℝ)..1, g x * (x ^ 2 / 2) := by
  have hr' : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt r (g x) x := by rwa [uIcc_of_le zero_le_one]
  have hv : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
    intro x _
    have h9 := (hasDerivAt_pow 2 x).div_const 2
    exact h9.congr_deriv (by ring)
  have hgi : IntervalIntegrable g volume 0 1 := by
    rw [← uIcc_of_le zero_le_one] at hg; exact hg.intervalIntegrable
  have := intervalIntegral.integral_mul_deriv_eq_deriv_mul hr' hv hgi (continuous_id.intervalIntegrable _ _)
  rw [this]
  simp
  ring

/-- **(1) FIRST-ORDER IDENTITY.** Σ_{j=1}^N s_j r(j/N) − ∫₀¹ r(x)x dx = r(1)·D(1) − ∫₀¹ g·D. -/
theorem abel_ibp_first (hN : 0 < N) {r g : ℝ → ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1)) :
    ∑ j ∈ Finset.Icc 1 N, s j * r ((j:ℝ)/N) - ∫ x in (0:ℝ)..1, r x * x
      = r 1 * Dfun s N 1 - ∫ x in (0:ℝ)..1, g x * Dfun s N x := by
  have hA := integral_gC (s := s) hN hr hg
  have hB := integral_r_mul_id hr hg
  have hgi : IntervalIntegrable g volume 0 1 := by
    rw [← uIcc_of_le zero_le_one] at hg; exact hg.intervalIntegrable
  have hq : IntervalIntegrable (fun x => g x * (x ^ 2 / 2)) volume 0 1 :=
    hgi.mul_continuousOn ((by fun_prop : Continuous fun x : ℝ => x ^ 2 / 2).continuousOn)
  have hsplit : ∫ x in (0:ℝ)..1, g x * Dfun s N x
      = (∫ x in (0:ℝ)..1, g x * Cstep s N x) - ∫ x in (0:ℝ)..1, g x * (x ^ 2 / 2) := by
    simp only [Dfun, mul_sub]
    exact intervalIntegral.integral_sub (intervalIntegrable_gC hN hg) hq
  rw [hsplit, hA, hB, Dfun_one hN]
  ring



/-! ### 3. first-order bound -/

/-- |Σ s_j r(j/N) − ∫₀¹ r x·x| ≤ |r 1|·|D 1| + M₁·∫₀¹|g| whenever |D| ≤ M₁ on [0,1]. -/
theorem first_order_bound (hN : 0 < N) {r g : ℝ → ℝ} {M₁ : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hM : ∀ x ∈ Icc (0:ℝ) 1, |Dfun s N x| ≤ M₁) :
    |∑ j ∈ Finset.Icc 1 N, s j * r ((j:ℝ)/N) - ∫ x in (0:ℝ)..1, r x * x|
      ≤ |r 1| * |Dfun s N 1| + M₁ * ∫ x in (0:ℝ)..1, |g x| := by
  rw [abel_ibp_first hN hr hg]
  have hgi : IntervalIntegrable g volume 0 1 := by
    rw [← uIcc_of_le zero_le_one] at hg; exact hg.intervalIntegrable
  have hM0 : 0 ≤ M₁ := le_trans (abs_nonneg _) (hM 0 ⟨le_rfl, zero_le_one⟩)
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  gcongr
  -- |∫ g D| ≤ ∫ |g|·M₁
  calc |∫ x in (0:ℝ)..1, g x * Dfun s N x|
      ≤ ∫ x in (0:ℝ)..1, |g x| * M₁ := by
        refine intervalIntegral.abs_integral_le_integral_abs (by norm_num) |>.trans ?_
        refine intervalIntegral.integral_mono_on (by norm_num) ?_ (hgi.abs.mul_const _) ?_
        · exact ((intervalIntegrable_gC (s := s) hN hg).sub
            (hgi.mul_continuousOn ((by fun_prop : Continuous fun x : ℝ => x ^ 2 / 2).continuousOn))).abs.congr_ae
            (by filter_upwards with x; simp [Dfun, mul_sub])
        · intro x hx
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg _)
    _ = M₁ * ∫ x in (0:ℝ)..1, |g x| := by
        rw [intervalIntegral.integral_mul_const]; ring

/-! ### 4. E is continuous, and E′ = D off the grid -/

/-- the grid {m/N : m ∈ ℕ}. -/
def grid (N : ℕ) : Set ℝ := Set.range (fun m : ℕ => (m:ℝ)/N)

lemma grid_countable : (grid N).Countable := Set.countable_range _

/-- Cstep is measurable (a finite sum of scaled indicators). -/
lemma measurable_Cstep : Measurable (Cstep s N) := by
  have : Cstep s N = fun x => ∑ j ∈ Finset.Icc 1 N, if ((j:ℕ):ℝ)/N ≤ x then s j else 0 := by
    funext x; simp [Cstep, Finset.sum_filter]
  rw [this]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

lemma measurable_Dfun : Measurable (Dfun s N) :=
  measurable_Cstep.sub ((measurable_id.pow_const 2).div_const 2)

/-- D is interval-integrable on [0,1]. -/
lemma intervalIntegrable_Dfun (hN : 0 < N) : IntervalIntegrable (Dfun s N) volume 0 1 := by
  have h1 : IntervalIntegrable (fun x => (1:ℝ) * Cstep s N x) volume 0 1 := intervalIntegrable_gC hN continuousOn_const
  simp only [one_mul] at h1
  exact h1.sub ((by fun_prop : Continuous fun x : ℝ => x ^ 2 / 2).intervalIntegrable _ _)

/-- E is continuous on [0,1]. -/
lemma continuousOn_Efun (hN : 0 < N) : ContinuousOn (Efun s N) (Icc (0:ℝ) 1) := by
  have := intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_Dfun (s := s) hN)
    (by simp : (0:ℝ) ∈ uIcc (0:ℝ) 1)
  rw [uIcc_of_le zero_le_one] at this
  exact this

/-- off the grid, a point of (0,1) sits in an open cell (m/N, (m+1)/N) with m < N. -/
lemma exists_cell (hN : 0 < N) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1 \ grid N) :
    ∃ m : ℕ, m < N ∧ x ∈ Ioo ((m:ℝ)/N) ((m+1:ℝ)/N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨⟨hx0, hx1⟩, hxg⟩ := hx
  refine ⟨⌊(N:ℝ) * x⌋₊, ?_, ?_, ?_⟩
  · have : ((⌊(N:ℝ) * x⌋₊ : ℕ) : ℝ) ≤ N * x := Nat.floor_le (by positivity)
    have : (N:ℝ) * x < N := by nlinarith
    exact_mod_cast lt_of_le_of_lt (Nat.floor_le (by positivity)) this
  · rw [div_lt_iff₀ hNr]
    have hle : ((⌊(N:ℝ) * x⌋₊ : ℕ) : ℝ) ≤ N * x := Nat.floor_le (by positivity)
    rcases hle.lt_or_eq with h | h
    · linarith [mul_comm (N:ℝ) x]
    · exfalso; apply hxg
      refine ⟨⌊(N:ℝ) * x⌋₊, ?_⟩
      show ((⌊(N:ℝ) * x⌋₊ : ℕ) : ℝ) / N = x
      rw [h]; field_simp
  · rw [lt_div_iff₀ hNr]
    have := Nat.lt_floor_add_one ((N:ℝ) * x)
    push_cast at this ⊢
    linarith [mul_comm (N:ℝ) x]

/-- on an open cell D agrees with the continuous function C_m − t²/2. -/
lemma Dfun_eqOn_cell (hN : 0 < N) {m : ℕ} (hm : m < N) :
    EqOn (Dfun s N) (fun t => Csum s m - t ^ 2 / 2) (Ioo ((m:ℝ)/N) ((m+1:ℝ)/N)) := fun t ht => by
  simp [Dfun, Cstep_eq_Csum_of_mem hN (Nat.succ_le_of_lt hm) (Ioo_subset_Ico_self ht)]

/-- D is continuous at every non-grid point of (0,1). -/
lemma continuousAt_Dfun (hN : 0 < N) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1 \ grid N) : ContinuousAt (Dfun s N) x := by
  obtain ⟨m, hm, hxm⟩ := exists_cell hN hx
  have hopen : IsOpen (Ioo ((m:ℝ)/N) ((m+1:ℝ)/N)) := isOpen_Ioo
  have hcont : ContinuousOn (fun t : ℝ => Csum s m - t ^ 2 / 2) (Ioo ((m:ℝ)/N) ((m+1:ℝ)/N)) := by fun_prop
  exact ((hcont.congr (Dfun_eqOn_cell hN hm)).continuousAt (hopen.mem_nhds hxm))

/-- E′ = D off the grid. -/
lemma hasDerivAt_Efun (hN : 0 < N) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1 \ grid N) :
    HasDerivAt (Efun s N) (Dfun s N x) x := by
  obtain ⟨m, hm, hxm⟩ := exists_cell hN hx
  have hI : IntervalIntegrable (Dfun s N) volume 0 x :=
    (intervalIntegrable_Dfun hN).mono_set (by
      rw [uIcc_of_le zero_le_one, uIcc_of_le hx.1.1.le]; exact Icc_subset_Icc le_rfl hx.1.2.le)
  have hmeas : StronglyMeasurableAtFilter (Dfun s N) (nhds x) volume :=
    measurable_Dfun.stronglyMeasurable.stronglyMeasurableAtFilter
  exact intervalIntegral.integral_hasDerivAt_right hI hmeas (continuousAt_Dfun hN hx)

/-! ### 5. second-order identity and the ceiling-stability bound -/

/-- **(2) SECOND-ORDER IDENTITY.** If additionally g is differentiable off a countable set T ⊆ ℝ with derivative h,
h interval-integrable on [0,1]:  Σ s_j r(j/N) − ∫₀¹ r x·x = r(1)·D(1) − g(1)·E(1) + ∫₀¹ h·E. -/
theorem abel_ibp_second (hN : 0 < N) {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable)
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1) :
    ∑ j ∈ Finset.Icc 1 N, s j * r ((j:ℝ)/N) - ∫ x in (0:ℝ)..1, r x * x
      = r 1 * Dfun s N 1 - g 1 * Efun s N 1 + ∫ x in (0:ℝ)..1, h x * Efun s N x := by
  rw [abel_ibp_first hN hr hg]
  -- FTC for F := g·E off the countable set T ∪ grid
  have hE := continuousOn_Efun (s := s) hN
  have hgi : IntervalIntegrable g volume 0 1 := by
    rw [← uIcc_of_le zero_le_one] at hg; exact hg.intervalIntegrable
  have hgD : IntervalIntegrable (fun x => g x * Dfun s N x) volume 0 1 :=
    ((intervalIntegrable_gC (s := s) hN hg).sub
      (hgi.mul_continuousOn ((by fun_prop : Continuous fun x : ℝ => x ^ 2 / 2).continuousOn))).congr_ae
      (by filter_upwards with x; simp [Dfun, mul_sub])
  have hhE : IntervalIntegrable (fun x => h x * Efun s N x) volume 0 1 :=
    hh.mul_continuousOn (by rwa [uIcc_of_le zero_le_one])
  have key := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (fun x => g x * Efun s N x) (fun x => h x * Efun s N x + g x * Dfun s N x) zero_le_one
    ((hT.union grid_countable)) (hg.mul hE)
    (fun x hx => by
      have hx' : x ∈ Ioo (0:ℝ) 1 \ T := ⟨hx.1, fun h' => hx.2 (Or.inl h')⟩
      have hx'' : x ∈ Ioo (0:ℝ) 1 \ grid N := ⟨hx.1, fun h' => hx.2 (Or.inr h')⟩
      exact (hgh x hx').mul (hasDerivAt_Efun hN hx''))
    (hhE.add hgD)
  rw [intervalIntegral.integral_add hhE hgD] at key
  simp only [Efun_zero, mul_zero, sub_zero] at key
  linarith

/-- **CEILING STABILITY (L1).** With |E| ≤ M on [0,1]:
  |Σ_{j=1}^{N} s_j r(j/N) − ∫₀¹ r(x)x dx| ≤ |r 1|·|D 1| + |g 1|·|E 1| + M·∫₀¹|h|. -/
theorem ceiling_stability (hN : 0 < N) {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {M : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hM : ∀ x ∈ Icc (0:ℝ) 1, |Efun s N x| ≤ M) :
    |∑ j ∈ Finset.Icc 1 N, s j * r ((j:ℝ)/N) - ∫ x in (0:ℝ)..1, r x * x|
      ≤ |r 1| * |Dfun s N 1| + |g 1| * |Efun s N 1| + M * ∫ x in (0:ℝ)..1, |h x| := by
  rw [abel_ibp_second hN hT hr hg hgh hh]
  have hE := continuousOn_Efun (s := s) hN
  have hhE : IntervalIntegrable (fun x => h x * Efun s N x) volume 0 1 :=
    hh.mul_continuousOn (by rwa [uIcc_of_le zero_le_one])
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨le_rfl, zero_le_one⟩)
  have h3 : |∫ x in (0:ℝ)..1, h x * Efun s N x| ≤ M * ∫ x in (0:ℝ)..1, |h x| := by
    calc |∫ x in (0:ℝ)..1, h x * Efun s N x|
        ≤ ∫ x in (0:ℝ)..1, |h x| * M := by
          refine intervalIntegral.abs_integral_le_integral_abs (by norm_num) |>.trans ?_
          refine intervalIntegral.integral_mono_on (by norm_num) hhE.abs (hh.abs.mul_const _) ?_
          intro x hx
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg _)
      _ = M * ∫ x in (0:ℝ)..1, |h x| := by rw [intervalIntegral.integral_mul_const]; ring
  calc |r 1 * Dfun s N 1 - g 1 * Efun s N 1 + ∫ x in (0:ℝ)..1, h x * Efun s N x|
      ≤ |r 1 * Dfun s N 1 - g 1 * Efun s N 1| + |∫ x in (0:ℝ)..1, h x * Efun s N x| := abs_add_le _ _
    _ ≤ (|r 1 * Dfun s N 1| + |g 1 * Efun s N 1|) + M * ∫ x in (0:ℝ)..1, |h x| := add_le_add (abs_sub _ _) h3
    _ = _ := by rw [abs_mul, abs_mul]

end PairCeiling
end Zeta23

end
