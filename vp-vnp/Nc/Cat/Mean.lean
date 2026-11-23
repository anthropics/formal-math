/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cat.Core

/-!
# Means over large windows

Windows: two sheets (`Bool`), `0 ≤ i < n²`, `0 ≤ k < n`. `mean f` is the limit (along an
ultrafilter) of the means of `f n` over the `n`-th window: a positive linear functional on bounded
functions, invariant under translations, with the inequality of Cauchy and Schwarz.
-/

open Filter Topology Finset

namespace Cat

/-- Functions on two sheets of `ℤ²`, one for every `n`. -/
abbrev Fn := ℕ → Bool → ℤ → ℤ → ℝ

/-- The mean over the `n`-th window. -/
noncomputable def avg (n : ℕ) (f : Bool → ℤ → ℤ → ℝ) : ℝ :=
  (∑ b, ∑ i ∈ range (n ^ 2), ∑ k ∈ range n, f b i k) / (2 * n ^ 3)

/-- Bounded functions. -/
def Bd (f : Fn) : Prop := ∃ C, ∀ n b i k, |f n b i k| ≤ C

theorem Bd.add {f g : Fn} (hf : Bd f) (hg : Bd g) : Bd (f + g) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun n b i k => (abs_add_le _ _).trans (add_le_add (hC n b i k) (hD n b i k))⟩

theorem Bd.mul {f g : Fn} (hf : Bd f) (hg : Bd g) : Bd (f * g) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C * D, fun n b i k => ?_⟩
  simp only [Pi.mul_apply, abs_mul]
  exact mul_le_mul (hC n b i k) (hD n b i k) (abs_nonneg _) ((abs_nonneg _).trans (hC n b i k))

theorem Bd.smul {f : Fn} (hf : Bd f) (c : ℝ) : Bd (c • f) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨|c| * C, fun n b i k => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC n b i k) (abs_nonneg _)

theorem Bd.const (c : ℝ) : Bd fun _ _ _ _ => c := ⟨|c|, fun _ _ _ _ => le_rfl⟩

theorem Bd.shift {f : Fn} (hf : Bd f) (a c : ℤ) : Bd fun n b i k => f n b (i + a) (k + c) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun n b i k => hC _ _ _ _⟩

theorem avg_add (n : ℕ) (f g : Bool → ℤ → ℤ → ℝ) : avg n (f + g) = avg n f + avg n g := by
  simp only [avg, Pi.add_apply, Finset.sum_add_distrib, add_div]

theorem avg_smul (n : ℕ) (c : ℝ) (f : Bool → ℤ → ℤ → ℝ) : avg n (c • f) = c * avg n f := by
  simp only [avg, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc]

theorem avg_mono {n : ℕ} {f g : Bool → ℤ → ℤ → ℝ}
    (h : ∀ b, ∀ i < n ^ 2, ∀ k < n, f b (i : ℕ) (k : ℕ) ≤ g b (i : ℕ) (k : ℕ)) :
    avg n f ≤ avg n g := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun k hk =>
    h b i (Finset.mem_range.1 hi) k (Finset.mem_range.1 hk)

theorem avg_const {n : ℕ} (hn : n ≠ 0) (c : ℝ) : avg n (fun _ _ _ => c) = c := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [avg, Finset.sum_const, Finset.card_univ, Fintype.card_bool, Finset.card_range,
    nsmul_eq_mul]
  push_cast
  field_simp

theorem abs_avg_le {n : ℕ} {f : Bool → ℤ → ℤ → ℝ} {C : ℝ} (h : ∀ b i k, |f b i k| ≤ C) :
    |avg n f| ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (h true 0 0)
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [avg] using hC
  · rw [abs_le]
    constructor
    · calc -C = avg n (fun _ _ _ => -C) := (avg_const hn _).symm
        _ ≤ _ := avg_mono fun b i _ k _ => (abs_le.1 (h b i k)).1
    · calc avg n f ≤ avg n (fun _ _ _ => C) := avg_mono fun b i _ k _ => (abs_le.1 (h b i k)).2
        _ = C := avg_const hn _

/-- The mean of a bounded function over large windows. -/
noncomputable def mean (f : Fn) : ℝ := limUnder (hyperfilter ℕ : Filter ℕ) fun n => avg n (f n)

theorem tendsto_mean {f : Fn} (hf : Bd f) :
    Tendsto (fun n => avg n (f n)) (hyperfilter ℕ : Filter ℕ) (𝓝 (mean f)) := by
  obtain ⟨C, hC⟩ := hf
  have h1 : ∀ n, avg n (f n) ∈ Set.Icc (-C) C := fun n => abs_le.1 (abs_avg_le (hC n))
  obtain ⟨a, -, ha⟩ := (isCompact_Icc (a := -C) (b := C)).ultrafilter_le_nhds
    ((hyperfilter ℕ).map fun n => avg n (f n)) (by
      rw [le_principal_iff]
      exact Filter.mem_map.2 (Filter.univ_mem' h1))
  exact tendsto_nhds_limUnder ⟨a, ha⟩

theorem mean_eq {f : Fn} (hf : Bd f) {c : ℝ}
    (h : Tendsto (fun n => avg n (f n)) atTop (𝓝 c)) : mean f = c :=
  tendsto_nhds_unique (tendsto_mean hf) (h.mono_left Nat.hyperfilter_le_atTop)

theorem mean_add {f g : Fn} (hf : Bd f) (hg : Bd g) : mean (f + g) = mean f + mean g := by
  refine tendsto_nhds_unique (tendsto_mean (hf.add hg)) ?_
  have := (tendsto_mean hf).add (tendsto_mean hg)
  simpa only [Pi.add_apply, avg_add] using this

theorem mean_smul {f : Fn} (hf : Bd f) (c : ℝ) : mean (c • f) = c * mean f := by
  refine tendsto_nhds_unique (tendsto_mean (hf.smul c)) ?_
  have := (tendsto_mean hf).const_mul c
  simpa only [Pi.smul_apply, avg_smul] using this

theorem mean_const (c : ℝ) : mean (fun _ _ _ _ => c) = c := by
  refine mean_eq (Bd.const c) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (avg_const hn c).symm

theorem mean_mono {f g : Fn} (hf : Bd f) (hg : Bd g)
    (h : ∀ᶠ n : ℕ in atTop, ∀ b, ∀ i < n ^ 2, ∀ k < n,
      f n b (i : ℕ) (k : ℕ) ≤ g n b (i : ℕ) (k : ℕ)) : mean f ≤ mean g := by
  refine le_of_tendsto_of_tendsto (tendsto_mean hf) (tendsto_mean hg) ?_
  exact (h.filter_mono Nat.hyperfilter_le_atTop).mono fun n hn => avg_mono hn

theorem mean_nonneg {f : Fn} (hf : Bd f) (h : ∀ n b i k, 0 ≤ f n b i k) : 0 ≤ mean f := by
  rw [← mean_const 0]
  exact mean_mono (Bd.const 0) hf (Eventually.of_forall fun _ _ _ _ _ _ => h _ _ _ _)

theorem mean_le {f g : Fn} (hf : Bd f) (hg : Bd g) (h : ∀ n b i k, f n b i k ≤ g n b i k) :
    mean f ≤ mean g :=
  mean_mono hf hg (Eventually.of_forall fun _ _ _ _ _ _ => h _ _ _ _)

/-! ### Translations -/

theorem sum_shift (φ : ℤ → ℝ) (N : ℕ) :
    ∑ i ∈ range N, φ ((i : ℤ) + 1) = ∑ i ∈ range N, φ (i : ℤ) + (φ N - φ 0) := by
  have h := Finset.sum_range_sub (fun i : ℕ => φ (i : ℤ)) N
  rw [Finset.sum_sub_distrib] at h
  push_cast at h
  linarith

theorem mean_eq_of_sub {f g : Fn} (hf : Bd f) (hg : Bd g)
    (h : Tendsto (fun n => avg n (f n) - avg n (g n)) atTop (𝓝 0)) : mean f = mean g := by
  have h1 := (tendsto_mean hf).sub (tendsto_mean hg)
  have h2 := tendsto_nhds_unique h1 (h.mono_left Nat.hyperfilter_le_atTop)
  linarith

theorem mean_shift_one {f : Fn} (hf : Bd f) :
    mean (fun n b i k => f n b (i + 1) k) = mean f := by
  obtain ⟨C, hC⟩ := id hf
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 true 0 0)
  refine mean_eq_of_sub (by simpa using hf.shift 1 0) hf ?_
  refine squeeze_zero_norm' (a := fun n : ℕ => 2 * C * (1 / (n : ℝ))) ?_ ?_
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h1 : (avg n fun b i k => f n b (i + 1) k) - avg n (f n) =
        (∑ b, ∑ k ∈ range n, (f n b ((n ^ 2 : ℕ) : ℤ) k - f n b 0 k)) / (2 * n ^ 3) := by
      rw [avg, avg, ← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm, Finset.sum_comm (s := range (n ^ 2)), ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sum_shift (fun i => f n b i k)]
      ring
    rw [h1, Real.norm_eq_abs, abs_div, abs_of_pos (show (0 : ℝ) < 2 * n ^ 3 by positivity),
      div_le_iff₀ (by positivity)]
    have h2 : |∑ b, ∑ k ∈ range n, (f n b ((n ^ 2 : ℕ) : ℤ) k - f n b 0 k)| ≤
        ∑ b : Bool, ∑ k ∈ range n, 2 * C := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      refine (abs_sub _ _).trans ?_
      linarith [hC n b ((n ^ 2 : ℕ) : ℤ) k, hC n b 0 k]
    refine h2.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Finset.card_range,
      nsmul_eq_mul]
    have h3 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h4 : 2 * C * (1 / (n : ℝ)) * (2 * n ^ 3) = 4 * C * n ^ 2 := by field_simp; ring
    rw [h4]
    push_cast
    nlinarith [mul_nonneg hC0 hn'.le]
  · simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 * C)

theorem mean_shift_one' {f : Fn} (hf : Bd f) :
    mean (fun n b i k => f n b i (k + 1)) = mean f := by
  obtain ⟨C, hC⟩ := id hf
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 true 0 0)
  refine mean_eq_of_sub (by simpa using hf.shift 0 1) hf ?_
  refine squeeze_zero_norm' (a := fun n : ℕ => 2 * C * (1 / (n : ℝ))) ?_ ?_
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h1 : (avg n fun b i k => f n b i (k + 1)) - avg n (f n) =
        (∑ b, ∑ i ∈ range (n ^ 2), (f n b i (n : ℕ) - f n b i 0)) / (2 * n ^ 3) := by
      rw [avg, avg, ← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_shift (fun k => f n b i k)]
      ring
    rw [h1, Real.norm_eq_abs, abs_div, abs_of_pos (show (0 : ℝ) < 2 * n ^ 3 by positivity),
      div_le_iff₀ (by positivity)]
    have h2 : |∑ b, ∑ i ∈ range (n ^ 2), (f n b i (n : ℕ) - f n b i 0)| ≤
        ∑ b : Bool, ∑ k ∈ range (n ^ 2), 2 * C := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (abs_sub _ _).trans ?_
      linarith [hC n b i (n : ℕ), hC n b i 0]
    refine h2.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Finset.card_range,
      nsmul_eq_mul]
    have h4 : 2 * C * (1 / (n : ℝ)) * (2 * n ^ 3) = 4 * C * n ^ 2 := by field_simp; ring
    rw [h4]
    push_cast
    nlinarith
  · simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 * C)

theorem mean_shift_left {f : Fn} (hf : Bd f) (a : ℤ) :
    mean (fun n b i k => f n b (i + a) k) = mean f := by
  induction a using Int.induction_on with
  | zero => simp
  | succ a ih =>
    rw [← ih, ← mean_shift_one (f := fun n b i k => f n b (i + a) k) (by simpa using hf.shift a 0)]
    congr 1
    funext n b i k
    congr 1
    ring
  | pred a ih =>
    rw [← ih, ← mean_shift_one (f := fun n b i k => f n b (i + (-a - 1)) k)
      (by simpa using hf.shift (-a - 1) 0)]
    congr 1
    funext n b i k
    congr 1
    ring

theorem mean_shift_right {f : Fn} (hf : Bd f) (a : ℤ) :
    mean (fun n b i k => f n b i (k + a)) = mean f := by
  induction a using Int.induction_on with
  | zero => simp
  | succ a ih =>
    rw [← ih, ← mean_shift_one' (f := fun n b i k => f n b i (k + a))
      (by simpa using hf.shift 0 a)]
    congr 1
    funext n b i k
    congr 1
    ring
  | pred a ih =>
    rw [← ih, ← mean_shift_one' (f := fun n b i k => f n b i (k + (-a - 1)))
      (by simpa using hf.shift 0 (-a - 1))]
    congr 1
    funext n b i k
    congr 1
    ring

theorem mean_shift {f : Fn} (hf : Bd f) (a c : ℤ) :
    mean (fun n b i k => f n b (i + a) (k + c)) = mean f := by
  rw [mean_shift_left (f := fun n b i k => f n b i (k + c)) (by simpa using hf.shift 0 c) a,
    mean_shift_right hf c]

/-- A telescoping sum. -/
theorem le_mean_tele {F : Fn} (hX : Bd fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k))
    {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀))
    (h : ∀ᶠ n : ℕ in atTop, ∀ k < n,
      c n ≤ ∑ b, (F n b ((n ^ 2 : ℕ) : ℤ) (k : ℕ) - F n b 0 (k : ℕ))) :
    c₀ / 2 ≤ mean fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k) := by
  refine le_of_tendsto_of_tendsto ((hc.div_const 2).mono_left Nat.hyperfilter_le_atTop)
    (tendsto_mean hX) ?_
  refine Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop ?_
  filter_upwards [h, eventually_ne_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have h1 : (avg n fun b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k)) =
      (∑ k ∈ range n, ∑ b, (F n b ((n ^ 2 : ℕ) : ℤ) k - F n b 0 k)) / (2 * n) := by
    rw [avg, Finset.sum_comm (s := range n)]
    have : ∀ b : Bool, ∑ i ∈ range (n ^ 2), ∑ k ∈ range n,
        (n : ℝ) ^ 2 * (F n b ((i : ℤ) + 1) k - F n b i k) =
        (n : ℝ) ^ 2 * ∑ k ∈ range n, (F n b ((n ^ 2 : ℕ) : ℤ) k - F n b 0 k) := by
      intro b
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_shift (fun i => F n b i k)]
      ring
    rw [Finset.sum_congr rfl fun b _ => this b, ← Finset.mul_sum]
    field_simp
  rw [h1, div_le_div_iff₀ (by norm_num) (by positivity)]
  have h2 : ∑ k ∈ range n, c n ≤
      ∑ k ∈ range n, ∑ b, (F n b ((n ^ 2 : ℕ) : ℤ) k - F n b 0 k) :=
    Finset.sum_le_sum fun k hk => hn k (Finset.mem_range.1 hk)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  linarith

/-- Many steps of a telescoping sum. -/
theorem mean_steps {F : Fn} (hX : Bd fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k))
    (S : ℕ) : Bd (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S) k - F n b i k)) ∧
      mean (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S) k - F n b i k)) =
        S * mean fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k) := by
  induction S with
  | zero =>
    have : (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + (0 : ℕ)) k - F n b i k) : Fn) =
        fun _ _ _ _ => (0 : ℝ) := by
      funext n b i k
      simp
    rw [this, mean_const, Nat.cast_zero, zero_mul]
    exact ⟨Bd.const 0, rfl⟩
  | succ S ih =>
    have hs := hX.shift S 0
    simp only [add_zero] at hs
    have : (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + (S + 1 : ℕ)) k - F n b i k) : Fn) =
        (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S + 1) k - F n b (i + S) k) : Fn) +
          (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S) k - F n b i k) : Fn) := by
      funext n b i k
      simp only [Pi.add_apply]
      push_cast
      rw [← add_assoc i]
      ring
    rw [this]
    refine ⟨hs.add ih.1, ?_⟩
    rw [mean_add hs ih.1, ih.2]
    rw [mean_shift_left hX S]
    push_cast
    ring

/-! ### Cauchy and Schwarz -/

/-- The root of the mean square. -/
noncomputable def nm (f : Fn) : ℝ := √(mean (f * f))

theorem nm_nonneg (f : Fn) : 0 ≤ nm f := Real.sqrt_nonneg _

theorem nm_sq {f : Fn} (hf : Bd f) : nm f ^ 2 = mean (f * f) :=
  Real.sq_sqrt (mean_nonneg (hf.mul hf) fun _ _ _ _ => mul_self_nonneg _)

theorem mean_mul_le {f g : Fn} (hf : Bd f) (hg : Bd g) : mean (f * g) ≤ nm f * nm g := by
  have h : 2 * mean (f * g) ≤ 2 * nm g * nm f := by
    apply le_two_mul_of_forall (nm_nonneg g) (nm_nonneg f)
    intro τ hτ
    rw [nm_sq hf, nm_sq hg]
    have h1 : mean ((2 : ℝ) • (f * g)) ≤ mean (τ • (f * f) + τ⁻¹ • (g * g)) := by
      apply mean_le ((hf.mul hg).smul 2) (((hf.mul hf).smul τ).add ((hg.mul hg).smul τ⁻¹))
      intro n b i k
      simp only [Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_eq_mul]
      have h2 : 0 ≤ τ⁻¹ * (τ * f n b i k - g n b i k) ^ 2 :=
        mul_nonneg (inv_nonneg.2 hτ.le) (sq_nonneg _)
      have h3 : τ⁻¹ * (τ * f n b i k - g n b i k) ^ 2 =
          τ * (f n b i k * f n b i k) + τ⁻¹ * (g n b i k * g n b i k)
            - 2 * (f n b i k * g n b i k) := by field_simp; ring
      linarith
    rw [mean_smul (hf.mul hg), mean_add ((hf.mul hf).smul τ) ((hg.mul hg).smul τ⁻¹),
      mean_smul (hf.mul hf), mean_smul (hg.mul hg)] at h1
    rw [div_eq_inv_mul]
    exact h1
  linarith

theorem nm_mono {f g : Fn} (hf : Bd f) (hg : Bd g) (h0 : ∀ n b i k, 0 ≤ f n b i k)
    (h : ∀ᶠ n : ℕ in atTop, ∀ b, ∀ i < n ^ 2, ∀ k < n,
      f n b (i : ℕ) (k : ℕ) ≤ g n b (i : ℕ) (k : ℕ)) : nm f ≤ nm g := by
  apply Real.sqrt_le_sqrt
  apply mean_mono (hf.mul hf) (hg.mul hg)
  filter_upwards [h] with n hn b i hi k hk
  exact mul_self_le_mul_self (h0 _ _ _ _) (hn b i hi k hk)

theorem nm_add_le {f g : Fn} (hf : Bd f) (hg : Bd g) : nm (f + g) ≤ nm f + nm g := by
  apply abs_le_of_sq_le_sq' _ (add_nonneg (nm_nonneg f) (nm_nonneg g)) |>.2
  rw [nm_sq (hf.add hg), add_sq, nm_sq hf, nm_sq hg]
  have h1 : (f + g) * (f + g) = f * f + (2 : ℝ) • (f * g) + g * g := by
    funext n b i k
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1, mean_add ((hf.mul hf).add ((hf.mul hg).smul 2)) (hg.mul hg),
    mean_add (hf.mul hf) ((hf.mul hg).smul 2), mean_smul (hf.mul hg)]
  linarith [mean_mul_le hf hg]

theorem mean_le_nm {f : Fn} (hf : Bd f) : mean f ≤ nm f := by
  have h := mean_mul_le hf (Bd.const 1)
  have h1 : f * (fun _ _ _ _ => (1 : ℝ)) = f := by
    funext n b i k
    simp
  have h2 : nm (fun _ _ _ _ => (1 : ℝ)) = 1 := by
    have : ((fun _ _ _ _ => (1 : ℝ)) * (fun _ _ _ _ => (1 : ℝ)) : Fn) = fun _ _ _ _ => 1 := by
      funext n b i k
      simp
    rw [nm, this, mean_const, Real.sqrt_one]
  rw [h1, h2, mul_one] at h
  exact h

theorem nm_shift {f : Fn} (hf : Bd f) (a c : ℤ) :
    nm (fun n b i k => f n b (i + a) (k + c)) = nm f := by
  rw [nm, nm, ← mean_shift (hf.mul hf) a c]
  rfl

end Cat
