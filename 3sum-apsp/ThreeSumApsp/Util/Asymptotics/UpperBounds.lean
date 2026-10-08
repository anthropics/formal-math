/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.PowLittleO

/-!
# One-sided bounds `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`

A running time is bounded from above only. `UpperBigOPow f a`, `UpperPowPolylog f a` and
`UpperPowLittleO f a` say that `f(n)` is eventually at most `C n^a`, at most `C n^a (log n)^e`, and
at most `n^{a+ε(n)}` with `ε(n) → 0`, where `IsBigOPow`, `IsPowPolylog` and `IsPowLittleO` say this
of `|f(n)|`.

A bound on `|f|` is a bound on `f` (`IsBigOPow.upperBigOPow`), and the function may be replaced by a
smaller one (`mono_left`); these two lemmas have the same names for the three classes. For `Õ(n^a)`
and `n^{a+o(1)}` a bound on `f` is a bound by a nonnegative function of the class that bounds `|f|`
(`UpperPowPolylog.exists_isPowPolylog`). For `Õ(n^a)` the closure properties follow: a bound on `f`
is a bound on `|f|` if `f` is eventually nonnegative (`UpperPowPolylog.isPowPolylog`), sums,
nonnegative constant factors, products with a nonnegative factor, a larger exponent (`mono`).
Logarithms and the `o(1)` are absorbed by a strictly larger exponent
(`UpperPowPolylog.upperBigOPow`, `UpperPowLittleO.upperBigOPow`).
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp

/-- `f(n) = O(n^a)`, as an upper bound. -/
def UpperBigOPow (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, f n ≤ C * (n : ℝ) ^ a

/-- `f(n) = O(n^a (log n)^{O(1)})`, as an upper bound. -/
def UpperPowPolylog (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ (C : ℝ) (e : ℕ), ∀ᶠ n : ℕ in Filter.atTop, f n ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)

/-- There is a sequence `ε(n) → 0` with `f(n) ≤ n^{a+ε(n)}` for all large `n`: a bound on `f` and
not on `|f|` (that is `IsPowLittleO`). -/
def UpperPowLittleO (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    ∀ᶠ n : ℕ in Filter.atTop, f n ≤ (n : ℝ) ^ (a + ε n)

variable {f f' g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` from above -/

/-- `f = O(n^a)` is in particular an upper bound on `f`. -/
theorem IsBigOPow.upperBigOPow (hf : IsBigOPow f a) : UpperBigOPow f a := by
  obtain ⟨C, hC⟩ := IsBigO.bound hf
  refine ⟨C, hC.mono fun n hn => ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)] at hn
  exact (le_abs_self _).trans hn

namespace UpperBigOPow

/-- The function may be replaced by one that is eventually at most as large. -/
theorem mono_left (h : UpperBigOPow f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) : UpperBigOPow f' a := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, (hle.and hC).mono fun n hn => hn.1.trans hn.2⟩

end UpperBigOPow

/-! ### `Õ(n^a)` from above -/

/-- `f = Õ(n^a)` is in particular an upper bound on `f`. -/
theorem IsPowPolylog.upperPowPolylog (hf : IsPowPolylog f a) : UpperPowPolylog f a := by
  obtain ⟨e, hf⟩ := hf
  obtain ⟨C, hC⟩ := hf.bound
  refine ⟨C, e, hC.mono fun n hn => ?_⟩
  have hnonneg : 0 ≤ (n : ℝ) ^ a * Real.log n ^ e :=
    mul_nonneg (Real.rpow_nonneg n.cast_nonneg a) (pow_nonneg (Real.log_natCast_nonneg n) e)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hn
  exact (le_abs_self _).trans hn

namespace UpperPowPolylog

/-- The function may be replaced by one that is eventually at most as large. -/
theorem mono_left (h : UpperPowPolylog f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) :
    UpperPowPolylog f' a := by
  obtain ⟨C, e, hC⟩ := h
  exact ⟨C, e, (hle.and hC).mono fun n hn => hn.1.trans hn.2⟩

/-- An upper bound `Õ(n^a)` is a bound by a nonnegative function of the class `Õ(n^a)`. -/
theorem exists_isPowPolylog (h : UpperPowPolylog f a) :
    ∃ g : ℕ → ℝ, (∀ n, 0 ≤ g n) ∧ IsPowPolylog g a ∧ ∀ᶠ n in atTop, f n ≤ g n := by
  obtain ⟨C, e, hC⟩ := h
  exact ⟨fun n => |C * ((n : ℝ) ^ a * Real.log n ^ e)|, fun n => abs_nonneg _,
    ((isPowPolylog_rpow_mul_log_pow a e).const_mul C).abs,
    hC.mono fun n hn => hn.trans (le_abs_self _)⟩

/-- For a function that is eventually nonnegative, the bound on `f` is a bound on `|f|`. -/
theorem isPowPolylog (h : UpperPowPolylog f a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n) :
    IsPowPolylog f a := by
  obtain ⟨g, -, hg, hfg⟩ := h.exists_isPowPolylog
  exact hg.mono_left_of_nonneg h0 hfg

/-- The exponent may be raised. -/
protected theorem mono (h : UpperPowPolylog f a) (hab : a ≤ b) : UpperPowPolylog f b := by
  obtain ⟨g, -, hg, hfg⟩ := h.exists_isPowPolylog
  exact (hg.mono hab).upperPowPolylog.mono_left hfg

/-- `Õ(n^a) + Õ(n^a) = Õ(n^a)`, from above. -/
protected theorem add (hf : UpperPowPolylog f a) (hg : UpperPowPolylog g a) :
    UpperPowPolylog (fun n => f n + g n) a := by
  obtain ⟨F, -, hF, hfF⟩ := hf.exists_isPowPolylog
  obtain ⟨G, -, hG, hgG⟩ := hg.exists_isPowPolylog
  exact (hF.add hG).upperPowPolylog.mono_left
    ((hfF.and hgG).mono fun n hn => add_le_add hn.1 hn.2)

/-- Nonnegative constant factors are absorbed. -/
theorem const_mul (hf : UpperPowPolylog f a) {c : ℝ} (hc : 0 ≤ c) :
    UpperPowPolylog (fun n => c * f n) a := by
  obtain ⟨F, -, hF, hfF⟩ := hf.exists_isPowPolylog
  exact (hF.const_mul c).upperPowPolylog.mono_left
    (hfF.mono fun n hn => mul_le_mul_of_nonneg_left hn hc)

/-- `Õ(n^a) · Õ(n^b) = Õ(n^(a+b))`, from above, if the second factor is eventually nonnegative. -/
protected theorem mul (hf : UpperPowPolylog f a) (hg : UpperPowPolylog g b)
    (hg0 : ∀ᶠ n in atTop, 0 ≤ g n) :
    UpperPowPolylog (fun n => f n * g n) (a + b) := by
  obtain ⟨F, -, hF, hfF⟩ := hf.exists_isPowPolylog
  exact (hF.mul (hg.isPowPolylog hg0)).upperPowPolylog.mono_left
    ((hfF.and hg0).mono fun n hn => mul_le_mul_of_nonneg_right hn.1 hn.2)

/-- Logarithms are absorbed: `Õ(n^a) ⊆ O(n^b)` for `a < b`, from above. -/
theorem upperBigOPow (h : UpperPowPolylog f a) (hab : a < b) : UpperBigOPow f b := by
  obtain ⟨g, -, hg, hfg⟩ := h.exists_isPowPolylog
  exact (hg.isBigOPow hab).upperBigOPow.mono_left hfg

end UpperPowPolylog

/-! ### `n^{a+o(1)}` from above -/

/-- `f = n^{a+o(1)}` is in particular an upper bound on `f`. -/
theorem IsPowLittleO.upperPowLittleO (hf : IsPowLittleO f a) : UpperPowLittleO f a := by
  obtain ⟨ε, hε, hf⟩ := hf
  exact ⟨ε, hε, hf.mono fun n hn => (le_abs_self _).trans hn⟩

namespace UpperPowLittleO

/-- The function may be replaced by one that is eventually at most as large. -/
theorem mono_left (h : UpperPowLittleO f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) :
    UpperPowLittleO f' a := by
  obtain ⟨ε, hε, hf⟩ := h
  exact ⟨ε, hε, (hle.and hf).mono fun n hn => hn.1.trans hn.2⟩

/-- An upper bound `n^{a+o(1)}` is a bound by a nonnegative function of the class `n^{a+o(1)}`. -/
theorem exists_isPowLittleO (h : UpperPowLittleO f a) :
    ∃ g : ℕ → ℝ, (∀ n, 0 ≤ g n) ∧ IsPowLittleO g a ∧ ∀ᶠ n in atTop, f n ≤ g n := by
  obtain ⟨ε, hε, hf⟩ := h
  exact ⟨fun n => (n : ℝ) ^ (a + ε n), fun n => Real.rpow_nonneg n.cast_nonneg _,
    ⟨ε, hε, Eventually.of_forall fun n => (abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg _)).le⟩,
    hf⟩

/-- The `o(1)` is absorbed: `n^{a+o(1)} ⊆ O(n^b)` for `a < b`, from above. -/
theorem upperBigOPow (h : UpperPowLittleO f a) (hab : a < b) : UpperBigOPow f b := by
  obtain ⟨g, -, hg, hfg⟩ := h.exists_isPowLittleO
  exact (hg.isBigOPow hab).upperBigOPow.mono_left hfg

end UpperPowLittleO

end ThreeSumApsp
