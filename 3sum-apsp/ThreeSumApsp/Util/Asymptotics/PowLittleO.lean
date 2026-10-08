/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.PowPolylog

/-!
# Calculating with `n^{a+o(1)}`

`IsPowLittleO f a` reads `f(n) = n^{a+o(1)}` as an upper bound on `|f(n)|`: there is a sequence
`ε(n) → 0` with `|f(n)| ≤ n^{a+ε(n)}` for all large `n`. This says the same as `f(n) = O(n^{a+η})`
for every `η > 0` (`isPowLittleO_iff`). In the second form the rules of the notation follow from the
rules for `O`:

* the exponent may grow (`IsPowLittleO.mono`), and a strictly larger exponent absorbs the `o(1)`
  (`IsPowLittleO.isBigOPow`);
* sums, products and constant factors (`IsPowLittleO.add`, `IsPowLittleO.mul`,
  `IsPowLittleO.const_mul`);
* `(n^{d+o(1)})^{c+o(1)} = n^{cd+o(1)}` for `c, d ≥ 0` (`IsPowLittleO.comp`);
* `O(n^a)` and `O(n^a (log n)^{O(1)})` are `n^{a+o(1)}` (`IsBigOPow.isPowLittleO`,
  `IsPowPolylog.isPowLittleO`).
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

/-! ### The two readings of the notation -/

/-- The `o(1)` is absorbed: if `f = n^{a+o(1)}` and `a < b`, then `|f n| ≤ n ^ b` for all large `n`.
-/
theorem IsPowLittleO.eventually_abs_le (h : IsPowLittleO f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b := by
  obtain ⟨ε, hε, hf⟩ := h
  filter_upwards [hf, hε.eventually_lt_const (sub_pos.2 hab), eventually_ge_atTop 1]
    with n hfn hεn hn
  exact hfn.trans (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) (by linarith))

/-- If for every `η > 0`, `|f(n)| ≤ n^{a+η}` for all large `n`, then `f(n) = n^{a+o(1)}`. For
`ε(n)` take the excess of the exponent that is needed at `n`: the number with
`n^{a+ε(n)} = max(|f(n)|, n^a)`. -/
theorem IsPowLittleO.of_eventually_abs_le
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ (a + η)) : IsPowLittleO f a := by
  -- All three claims are about `n ≥ 2`, where `n > 1` and the maximum is positive.
  have hbase : ∀ n : ℕ, 2 ≤ n → (1 : ℝ) < n ∧ 0 < max |f n| ((n : ℝ) ^ a) := fun n hn =>
    ⟨by exact_mod_cast hn, lt_max_of_lt_right (Real.rpow_pos_of_pos (by positivity) a)⟩
  refine ⟨fun n => Real.logb n (max |f n| ((n : ℝ) ^ a)) - a,
    tendsto_order.2 ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩, ?_⟩
  · -- `ε(n) ≥ 0`, because the maximum is at least `n^a`.
    filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    have hge : a ≤ Real.logb n (max |f n| ((n : ℝ) ^ a)) :=
      (Real.le_logb_iff_rpow_le hn1 hpos).2 (le_max_right _ _)
    linarith [hδ, hge]
  · -- `ε(n) ≤ δ/2` as soon as `|f(n)| ≤ n^{a+δ/2}`.
    filter_upwards [h (δ / 2) (half_pos hδ), eventually_ge_atTop 2] with n hfn hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    have hle : Real.logb n (max |f n| ((n : ℝ) ^ a)) ≤ a + δ / 2 :=
      (Real.logb_le_iff_le_rpow hn1 hpos).2
        (max_le hfn (Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)))
    linarith [hδ, hle]
  · -- `n^{a+ε(n)}` is the maximum.
    filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    rw [add_sub_cancel, Real.rpow_logb (zero_lt_one.trans hn1) hn1.ne' hpos]
    exact le_max_left _ _

/-- `f(n) = n^{a+o(1)}` if and only if `f(n) = O(n^{a+η})` for every `η > 0`. -/
theorem isPowLittleO_iff : IsPowLittleO f a ↔ ∀ η : ℝ, 0 < η → IsBigOPow f (a + η) :=
  ⟨fun h η hη => (isBigOPow_rpow (a + η)).mono_left
      ((h.eventually_abs_le (lt_add_of_pos_right a hη)).mono
        fun _ hfn => hfn.trans (le_abs_self _)),
    fun h => .of_eventually_abs_le fun η hη =>
      (h (η / 2) (half_pos hη)).eventually_abs_le (by linarith)⟩

/-! ### The rules -/

/-- `n^{a+o(1)} ⊆ n^{b+o(1)}` for `a ≤ b`. -/
protected theorem IsPowLittleO.mono (h : IsPowLittleO f a) (hab : a ≤ b) : IsPowLittleO f b :=
  isPowLittleO_iff.2 fun η hη => (isPowLittleO_iff.1 h η hη).mono (by linarith)

/-- `n^{a+o(1)} ⊆ O(n^b)` for `a < b`. -/
theorem IsPowLittleO.isBigOPow (h : IsPowLittleO f a) (hab : a < b) : IsBigOPow f b :=
  (isPowLittleO_iff.1 h (b - a) (sub_pos.2 hab)).mono (by linarith)

/-- `O(n^a) ⊆ n^{a+o(1)}`. -/
theorem IsBigOPow.isPowLittleO (h : IsBigOPow f a) : IsPowLittleO f a :=
  isPowLittleO_iff.2 fun _ hη => h.mono (by linarith)

/-- `O(n^a (log n)^{O(1)}) ⊆ n^{a+o(1)}`. -/
theorem IsPowPolylog.isPowLittleO (h : IsPowPolylog f a) : IsPowLittleO f a :=
  isPowLittleO_iff.2 fun _ hη => h.isBigOPow (by linarith)

/-- `n^{a+o(1)} + n^{a+o(1)} = n^{a+o(1)}`. -/
protected theorem IsPowLittleO.add (hf : IsPowLittleO f a) (hg : IsPowLittleO g a) :
    IsPowLittleO (fun n => f n + g n) a :=
  isPowLittleO_iff.2 fun η hη => (isPowLittleO_iff.1 hf η hη).add (isPowLittleO_iff.1 hg η hη)

/-- `n^{a+o(1)} · n^{b+o(1)} = n^{a+b+o(1)}`. -/
protected theorem IsPowLittleO.mul (hf : IsPowLittleO f a) (hg : IsPowLittleO g b) :
    IsPowLittleO (fun n => f n * g n) (a + b) :=
  isPowLittleO_iff.2 fun η hη => ((isPowLittleO_iff.1 hf _ (half_pos hη)).mul
    (isPowLittleO_iff.1 hg _ (half_pos hη))).mono (by linarith)

/-- Constant factors are absorbed. -/
theorem IsPowLittleO.const_mul (hf : IsPowLittleO f a) (c : ℝ) :
    IsPowLittleO (fun n => c * f n) a :=
  isPowLittleO_iff.2 fun η hη => (isPowLittleO_iff.1 hf η hη).const_mul c

/-! ### Composition -/

/-- For `c, d ≥ 0` and `η > 0` there is `t > 0` with `(c + t)(d + t) ≤ cd + η`. -/
private theorem exists_pos_add_mul_add_le (hc : 0 ≤ c) (hd : 0 ≤ d) (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ (c + t) * (d + t) ≤ c * d + η := by
  have hcd : 0 < c + d + 1 := by linarith
  have ht : 0 < min 1 (η / (c + d + 1)) := lt_min one_pos (div_pos hη hcd)
  refine ⟨min 1 (η / (c + d + 1)), ht, ?_⟩
  set t := min 1 (η / (c + d + 1))
  have hsq : t * t ≤ t * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) ht.le
  have hlin : t * (c + d + 1) ≤ η := (le_div_iff₀ hcd).1 (min_le_right _ _)
  -- `(c + t)(d + t) = cd + t(c + d) + t² ≤ cd + t(c + d + 1) ≤ cd + η`
  linarith [hsq, hlin]

/-- `(n^{d+o(1)})^{c+o(1)} = n^{cd+o(1)}`: if `T(s) = s^{c+o(1)}` and `size(n) = n^{d+o(1)}` then
`T(size(n)) = n^{cd+o(1)}`, for `c, d ≥ 0`. The sizes need not tend to infinity. -/
protected theorem IsPowLittleO.comp (hT : IsPowLittleO T c)
    (hs : IsPowLittleO (fun n => (size n : ℝ)) d) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    IsPowLittleO (fun n => T (size n)) (c * d) := by
  refine isPowLittleO_iff.2 fun η hη => ?_
  obtain ⟨t, ht, hexp⟩ := exists_pos_add_mul_add_le hc hd hη
  exact ((isPowLittleO_iff.1 hT t ht).comp (isPowLittleO_iff.1 hs t ht) (by linarith)
    (by linarith)).mono hexp

end ThreeSumApsp
