/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Asymptotics.Powers
public import ThreeSumApsp.Util.Log

/-!
# Calculating with `O(n^a)` and `Õ(n^a)`

Closure properties of the two classes `IsBigOPow f a`, that is `f(n) = O(n^a)`, and
`IsPowPolylog f a`, that is `f(n) = O(n^a (log n)^{O(1)})`, which the paper writes `Õ(n^a)`.

A bound enters by `of_abs_le`, by `of_isBigO`, or from the model functions (`isBigOPow_rpow`,
`isBigOPow_natCast_pow`, `isBigOPow_const`, `isPowPolylog_rpow_mul_log_pow`, `isPowPolylog_log_pow`,
and for rounded powers `isBigOPow_ceil_rpow`, `isBigOPow_floor_rpow` and their inverses;
`IsBigOPow.natCeil` for rounding in general). Both classes are closed under sums, constant factors
and passing to a smaller function (`mono_left`). A product has the exponent `a + b` and a power the
exponent `a * k` (`pow`, `rpow`), to be brought to the wanted form by `mono`, which asks only for an
inequality between exponents. Substituting `n ↦ size n` multiplies nonnegative exponents
(`IsBigOPow.comp`, `IsPowPolylog.comp`), for `size n = O(n^μ)`, and then `log (size n) = Õ(1)`
(`IsBigOPow.isPowPolylog_log_natCast`). The classes are related by `IsBigOPow.isPowPolylog` and,
with a loss in the exponent, `IsPowPolylog.isBigOPow`; `eventually_abs_le` absorbs the constant as
well.
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

variable {f g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` -/

/-- `n ^ a = O(n^a)`. -/
theorem isBigOPow_rpow (a : ℝ) : IsBigOPow (fun n : ℕ => (n : ℝ) ^ a) a :=
  isBigO_refl _ _

/-- `n ^ k = O(n^k)` for a natural number `k`. -/
theorem isBigOPow_natCast_pow (k : ℕ) : IsBigOPow (fun n : ℕ => (n : ℝ) ^ k) k := by
  simpa only [Real.rpow_natCast] using isBigOPow_rpow (k : ℝ)

/-- `n = O(n^1)`. -/
theorem isBigOPow_natCast : IsBigOPow (fun n : ℕ => (n : ℝ)) 1 := by
  simpa only [Real.rpow_one] using isBigOPow_rpow 1

/-- A constant is `O(n^0)`. -/
theorem isBigOPow_const (c : ℝ) : IsBigOPow (fun _ => c) 0 :=
  isBigO_of_abs_le |c| 0 fun n _ => by rw [Real.rpow_zero, mul_one]

namespace IsBigOPow

/-- A bound `|f n| ≤ C * n ^ a` from some `n₀` on gives `f = O(n^a)`. -/
theorem of_abs_le (C : ℝ) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → |f n| ≤ C * (n : ℝ) ^ a) : IsBigOPow f a :=
  isBigO_of_abs_le C n₀ h

/-- If `g = O(n^a)` and `f = O(g)`, then `f = O(n^a)`. -/
theorem of_isBigO (hg : IsBigOPow g a) (hfg : f =O[atTop] g) : IsBigOPow f a :=
  hfg.trans hg

/-- If `|f n| ≤ |g n|` for all large `n` and `g = O(n^a)`, then `f = O(n^a)`. -/
theorem mono_left (hg : IsBigOPow g a) (h : ∀ᶠ n in atTop, |f n| ≤ |g n|) : IsBigOPow f a :=
  hg.of_isBigO (IsBigO.of_bound' h)

/-- If `0 ≤ f n ≤ g n` for all large `n` and `g = O(n^a)`, then `f = O(n^a)`. -/
theorem mono_left_of_nonneg (hg : IsBigOPow g a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (h : ∀ᶠ n in atTop, f n ≤ g n) : IsBigOPow f a :=
  hg.mono_left ((h0.and h).mono fun _ hn => abs_le_abs_of_nonneg hn.1 hn.2)

/-- The exponent may be raised. -/
protected theorem mono (hf : IsBigOPow f a) (hab : a ≤ b) : IsBigOPow f b :=
  hf.trans (isBigO_rpow_rpow_of_le hab)

/-- `O(n^a) + O(n^a) = O(n^a)`. -/
protected theorem add (hf : IsBigOPow f a) (hg : IsBigOPow g a) :
    IsBigOPow (fun n => f n + g n) a :=
  IsBigO.add hf hg

/-- `O(n^a) · O(n^b) = O(n^(a+b))`. -/
protected theorem mul (hf : IsBigOPow f a) (hg : IsBigOPow g b) :
    IsBigOPow (fun n => f n * g n) (a + b) :=
  (IsBigO.mul hf hg).congr' EventuallyEq.rfl (rpow_mul_rpow_eventuallyEq a b)

/-- `O(n^a) ^ r = O(n^(a r))` for a real exponent `r ≥ 0`. -/
protected theorem rpow (hf : IsBigOPow f a) {r : ℝ} (hr : 0 ≤ r) :
    IsBigOPow (fun n => f n ^ r) (a * r) := by
  have h := IsBigO.rpow hr (Eventually.of_forall fun n : ℕ => Real.rpow_nonneg n.cast_nonneg a) hf
  exact h.congr_right fun n => (Real.rpow_mul n.cast_nonneg a r).symm

/-- `O(n^a) ^ k = O(n^(a k))` for a natural number `k`. -/
protected theorem pow (hf : IsBigOPow f a) (k : ℕ) : IsBigOPow (fun n => f n ^ k) (a * k) := by
  simpa only [Real.rpow_natCast] using hf.rpow k.cast_nonneg

/-- Constant factors are absorbed. -/
theorem const_mul (hf : IsBigOPow f a) (c : ℝ) : IsBigOPow (fun n => c * f n) a :=
  IsBigO.const_mul_left hf c

/-- If `f = O(n^a)` then `|f| = O(n^a)`. -/
protected theorem abs (hf : IsBigOPow f a) : IsBigOPow (fun n => |f n|) a :=
  IsBigO.norm_left hf

/-- The constant is absorbed: if `f = O(n^a)` and `a < b`, then `|f n| ≤ n ^ b` for all large `n`.
-/
theorem eventually_abs_le (hf : IsBigOPow f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b := by
  obtain ⟨C, hC⟩ := IsBigO.bound hf
  filter_upwards [hC, eventually_mul_rpow_le C hab] with n hn hCn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)] at hn
  exact hn.trans hCn

/-- `O(n^a) ⊆ Õ(n^a)`. -/
theorem isPowPolylog (hf : IsBigOPow f a) : IsPowPolylog f a :=
  ⟨0, by simpa only [pow_zero, mul_one, IsBigOPow] using hf⟩

end IsBigOPow

/-- Rounding up keeps the class: if `f = O(n^a)` with `a ≥ 0`, then `⌈f n⌉ = O(n^a)`. -/
theorem IsBigOPow.natCeil (hf : IsBigOPow f a) (ha : 0 ≤ a) :
    IsBigOPow (fun n => (⌈f n⌉₊ : ℝ)) a := by
  refine (hf.abs.add ((isBigOPow_const 1).mono ha)).mono_left_of_nonneg
    (Eventually.of_forall fun n => Nat.cast_nonneg _) (Eventually.of_forall fun n => ?_)
  obtain hneg | hpos := le_or_gt (f n) 0
  · rw [Nat.ceil_eq_zero.2 hneg, Nat.cast_zero]
    positivity
  · exact (Nat.ceil_lt_add_one hpos.le).le.trans (add_le_add_left (le_abs_self _) 1)

/-- `⌈n ^ μ⌉ = O(n^μ)` for `μ ≥ 0`. -/
theorem isBigOPow_ceil_rpow {μ : ℝ} (hμ : 0 ≤ μ) :
    IsBigOPow (fun n : ℕ => (⌈(n : ℝ) ^ μ⌉₊ : ℝ)) μ :=
  (isBigOPow_rpow μ).natCeil hμ

/-- `⌊n ^ μ⌋ = O(n^μ)`. -/
theorem isBigOPow_floor_rpow (μ : ℝ) : IsBigOPow (fun n : ℕ => (⌊(n : ℝ) ^ μ⌋₊ : ℝ)) μ := by
  refine .of_abs_le 1 0 fun n _ => ?_
  rw [abs_of_nonneg (Nat.cast_nonneg _), one_mul]
  exact Nat.floor_le (Real.rpow_nonneg n.cast_nonneg μ)

/-- `⌈n ^ μ⌉⁻¹ = O(n^(-μ))`. -/
theorem isBigOPow_inv_ceil_rpow (μ : ℝ) : IsBigOPow (fun n : ℕ => (⌈(n : ℝ) ^ μ⌉₊ : ℝ)⁻¹) (-μ) := by
  refine .of_abs_le 1 1 fun n hn => ?_
  have hpos : 0 < (n : ℝ) ^ μ := Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) μ
  rw [abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)), one_mul, Real.rpow_neg n.cast_nonneg]
  exact inv_anti₀ hpos (Nat.le_ceil _)

/-- `⌊n ^ μ⌋⁻¹ = O(n^(-μ))` for `μ ≥ 0`. -/
theorem isBigOPow_inv_floor_rpow {μ : ℝ} (hμ : 0 ≤ μ) :
    IsBigOPow (fun n : ℕ => (⌊(n : ℝ) ^ μ⌋₊ : ℝ)⁻¹) (-μ) := by
  refine .of_abs_le 2 1 fun n hn => ?_
  have hone : 1 ≤ (n : ℝ) ^ μ := Real.one_le_rpow (Nat.one_le_cast.2 hn) hμ
  have hfloor : (1 : ℝ) ≤ ⌊(n : ℝ) ^ μ⌋₊ := Nat.one_le_cast.2 (Nat.floor_pos.2 hone)
  have hlt : (n : ℝ) ^ μ < ⌊(n : ℝ) ^ μ⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)), Real.rpow_neg n.cast_nonneg,
    ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-! ### `Õ(n^a)` -/

/-- `n ^ a * (log n) ^ e = Õ(n^a)`. -/
theorem isPowPolylog_rpow_mul_log_pow (a : ℝ) (e : ℕ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) a :=
  ⟨e, isBigO_refl _ _⟩

/-- `n ^ a * log n = Õ(n^a)`. -/
theorem isPowPolylog_rpow_mul_log (a : ℝ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * Real.log n) a := by
  simpa only [pow_one] using isPowPolylog_rpow_mul_log_pow a 1

/-- `n ^ a = Õ(n^a)`. -/
theorem isPowPolylog_rpow (a : ℝ) : IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a) a :=
  (isBigOPow_rpow a).isPowPolylog

/-- `(log n) ^ e = Õ(1)`. -/
theorem isPowPolylog_log_pow (e : ℕ) : IsPowPolylog (fun n : ℕ => Real.log n ^ e) 0 :=
  ⟨e, by simpa only [Real.rpow_zero, one_mul] using isBigO_refl (fun n : ℕ => Real.log n ^ e) atTop⟩

/-- `log n = Õ(1)`. -/
theorem isPowPolylog_log : IsPowPolylog (fun n : ℕ => Real.log n) 0 := by
  simpa only [pow_one] using isPowPolylog_log_pow 1

/-- A constant is `Õ(1)`. -/
theorem isPowPolylog_const (c : ℝ) : IsPowPolylog (fun _ => c) 0 :=
  (isBigOPow_const c).isPowPolylog

namespace IsPowPolylog

/-- A bound `|f n| ≤ C * (n ^ a * (log n) ^ e)` from some `n₀` on gives `f = Õ(n^a)`. -/
theorem of_abs_le (C : ℝ) (e n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → |f n| ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)) : IsPowPolylog f a :=
  ⟨e, isBigO_of_abs_le C n₀ h⟩

/-- If `g = Õ(n^a)` and `f = O(g)`, then `f = Õ(n^a)`. -/
theorem of_isBigO (hg : IsPowPolylog g a) (hfg : f =O[atTop] g) : IsPowPolylog f a := by
  obtain ⟨e, hg⟩ := hg
  exact ⟨e, hfg.trans hg⟩

/-- If `|f n| ≤ |g n|` for all large `n` and `g = Õ(n^a)`, then `f = Õ(n^a)`. -/
theorem mono_left (hg : IsPowPolylog g a) (h : ∀ᶠ n in atTop, |f n| ≤ |g n|) : IsPowPolylog f a :=
  hg.of_isBigO (IsBigO.of_bound' h)

/-- If `0 ≤ f n ≤ g n` for all large `n` and `g = Õ(n^a)`, then `f = Õ(n^a)`. -/
theorem mono_left_of_nonneg (hg : IsPowPolylog g a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (h : ∀ᶠ n in atTop, f n ≤ g n) : IsPowPolylog f a :=
  hg.mono_left ((h0.and h).mono fun _ hn => abs_le_abs_of_nonneg hn.1 hn.2)

/-- The exponent may be raised. -/
protected theorem mono (hf : IsPowPolylog f a) (hab : a ≤ b) : IsPowPolylog f b := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.trans (isBigO_rpow_mul_log_pow_of_le hab le_rfl)⟩

/-- `Õ(n^a) + Õ(n^a) = Õ(n^a)`. -/
protected theorem add (hf : IsPowPolylog f a) (hg : IsPowPolylog g a) :
    IsPowPolylog (fun n => f n + g n) a := by
  obtain ⟨e₁, hf⟩ := hf
  obtain ⟨e₂, hg⟩ := hg
  exact ⟨max e₁ e₂, (hf.trans (isBigO_rpow_mul_log_pow_of_le le_rfl (le_max_left _ _))).add
    (hg.trans (isBigO_rpow_mul_log_pow_of_le le_rfl (le_max_right _ _)))⟩

/-- Constant factors are absorbed. -/
theorem const_mul (hf : IsPowPolylog f a) (c : ℝ) : IsPowPolylog (fun n => c * f n) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.const_mul_left c⟩

/-- Constant factors are absorbed. -/
theorem mul_const (hf : IsPowPolylog f a) (c : ℝ) : IsPowPolylog (fun n => f n * c) a := by
  simpa only [mul_comm] using hf.const_mul c

/-- `Õ(n^a) · Õ(n^b) = Õ(n^(a+b))`. -/
protected theorem mul (hf : IsPowPolylog f a) (hg : IsPowPolylog g b) :
    IsPowPolylog (fun n => f n * g n) (a + b) := by
  obtain ⟨e₁, hf⟩ := hf
  obtain ⟨e₂, hg⟩ := hg
  refine ⟨e₁ + e₂, (hf.mul hg).congr' EventuallyEq.rfl ?_⟩
  filter_upwards [rpow_mul_rpow_eventuallyEq a b] with n hn
  rw [← hn, pow_add, mul_mul_mul_comm]

/-- `Õ(n^a) ^ k = Õ(n^(a k))` for a natural number `k`. -/
protected theorem pow (hf : IsPowPolylog f a) (k : ℕ) :
    IsPowPolylog (fun n => f n ^ k) (a * k) := by
  obtain ⟨e, hf⟩ := hf
  refine ⟨e * k, (hf.pow k).congr_right fun n => ?_⟩
  rw [mul_pow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul n.cast_nonneg]

/-- `Õ(n^a) ^ r = Õ(n^(a r))` for a real exponent `r ≥ 0`. -/
protected theorem rpow (hf : IsPowPolylog f a) {r : ℝ} (hr : 0 ≤ r) :
    IsPowPolylog (fun n => f n ^ r) (a * r) := by
  obtain ⟨e, hf⟩ := hf
  obtain ⟨E, hE⟩ := exists_nat_ge ((e : ℝ) * r)
  have hpow : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ a := fun n => Real.rpow_nonneg n.cast_nonneg a
  have hlogpow : ∀ n : ℕ, 0 ≤ Real.log n ^ e := fun n => pow_nonneg (Real.log_natCast_nonneg n) e
  refine ⟨E, (hf.rpow hr (Eventually.of_forall fun n => mul_nonneg (hpow n) (hlogpow n))).trans ?_⟩
  -- `(n^a (log n)^e)^r = n^(a r) (log n)^(e r) ≤ n^(a r) (log n)^E` as soon as `log n ≥ 1`
  refine isBigO_of_abs_le 1 3 fun n hn => ?_
  have hlog : 1 ≤ Real.log n := Real.one_le_log_natCast_of_three_le hn
  rw [one_mul, abs_of_nonneg (Real.rpow_nonneg (mul_nonneg (hpow n) (hlogpow n)) r),
    Real.mul_rpow (hpow n) (hlogpow n), ← Real.rpow_mul n.cast_nonneg,
    ← Real.rpow_natCast (Real.log n) e, ← Real.rpow_mul (zero_le_one.trans hlog),
    ← Real.rpow_natCast (Real.log n) E]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog hE)
    (Real.rpow_nonneg n.cast_nonneg _)

/-- If `f = Õ(n^a)` then `|f| = Õ(n^a)`. -/
protected theorem abs (hf : IsPowPolylog f a) : IsPowPolylog (fun n => |f n|) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.norm_left⟩

/-- If `f = Õ(n^a)` and `g n = f n` for all large `n`, then `g = Õ(n^a)`. -/
protected theorem congr (hf : IsPowPolylog f a) (h : f =ᶠ[atTop] g) : IsPowPolylog g a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.congr' h EventuallyEq.rfl⟩

/-- Logarithms are absorbed: `Õ(n^a) ⊆ O(n^b)` for `a < b`. -/
theorem isBigOPow (hf : IsPowPolylog f a) (hab : a < b) : IsBigOPow f b := by
  obtain ⟨e, hf⟩ := hf
  exact hf.trans (isBigO_rpow_mul_log_pow_rpow hab e)

/-- The constant and the logarithms are absorbed: if `f = Õ(n^a)` and `a < b`, then `|f n| ≤ n ^ b`
for all large `n`. -/
theorem eventually_abs_le (hf : IsPowPolylog f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b :=
  (hf.isBigOPow (left_lt_add_div_two.2 hab)).eventually_abs_le (add_div_two_lt_right.2 hab)

end IsPowPolylog

/-- If `size n = O(n^μ)` for some `μ`, then `log (size n) = Õ(1)`. -/
theorem IsBigOPow.isPowPolylog_log_natCast {size : ℕ → ℕ} {μ : ℝ}
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) :
    IsPowPolylog (fun n => Real.log (size n)) 0 := by
  refine (isPowPolylog_log.const_mul (max μ 0 + 1)).mono_left_of_nonneg
    (Eventually.of_forall fun n => Real.log_natCast_nonneg _) ?_
  filter_upwards [(hsize.mono (le_max_left μ 0)).eventually_abs_le (lt_add_one _),
    eventually_gt_atTop 0] with n hle hn
  obtain hzero | hpos := (size n).eq_zero_or_pos
  · rw [hzero, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (add_nonneg (le_max_right μ 0) zero_le_one) (Real.log_natCast_nonneg n)
  · rw [abs_of_nonneg (Nat.cast_nonneg _)] at hle
    rw [← Real.log_rpow (Nat.cast_pos.2 hn)]
    exact Real.log_le_log (Nat.cast_pos.2 hpos) hle

/-- Substituting a size: if `G(s) = O(s^a)` and `size n = O(n^μ)` with `a, μ ≥ 0`, then
`G(size n) = O(n^(a μ))`. The sizes need not tend to infinity. -/
protected theorem IsBigOPow.comp {G : ℕ → ℝ} {size : ℕ → ℕ} {μ : ℝ} (hG : IsBigOPow G a)
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) (ha : 0 ≤ a) (hμ : 0 ≤ μ) :
    IsBigOPow (fun n => G (size n)) (a * μ) := by
  have hmodel : IsBigOPow (fun n => (size n : ℝ) ^ a + 1) (a * μ) :=
    ((hsize.rpow ha).mono (mul_comm μ a).le).add ((isBigOPow_const 1).mono (mul_nonneg ha hμ))
  exact hmodel.of_isBigO
    (isBigO_comp_add_one hG (fun s => Real.rpow_nonneg s.cast_nonneg a) size)

/-- Substituting a size: if `G(s) = Õ(s^a)` and `size n = O(n^μ)` with `a, μ ≥ 0`, then
`G(size n) = Õ(n^(a μ))`. The sizes need not tend to infinity. -/
protected theorem IsPowPolylog.comp {G : ℕ → ℝ} {size : ℕ → ℕ} {μ : ℝ} (hG : IsPowPolylog G a)
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) (ha : 0 ≤ a) (hμ : 0 ≤ μ) :
    IsPowPolylog (fun n => G (size n)) (a * μ) := by
  obtain ⟨e, hG⟩ := hG
  have hmain := (hsize.rpow ha).isPowPolylog.mul (hsize.isPowPolylog_log_natCast.pow e)
  rw [zero_mul, add_zero, mul_comm μ a] at hmain
  exact (hmain.add ((isPowPolylog_const 1).mono (mul_nonneg ha hμ))).of_isBigO
    (isBigO_comp_add_one hG (fun s => mul_nonneg (Real.rpow_nonneg s.cast_nonneg a)
      (pow_nonneg (Real.log_natCast_nonneg s) e)) size)

/-- `n ^ a * (log n + 1) ^ e = Õ(n^a)`. -/
theorem isPowPolylog_rpow_mul_log_add_one_pow (a : ℝ) (e : ℕ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * (Real.log n + 1) ^ e) a := by
  have h := (isPowPolylog_rpow a).mul ((isPowPolylog_log.add (isPowPolylog_const 1)).pow e)
  rwa [zero_mul, add_zero] at h

/-- `log (c * n ^ κ) = Õ(1)`. -/
theorem isPowPolylog_log_mul_rpow (c κ : ℝ) :
    IsPowPolylog (fun n : ℕ => Real.log (c * (n : ℝ) ^ κ)) 0 := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa only [zero_mul, Real.log_zero] using isPowPolylog_const 0
  · refine ((isPowPolylog_const (Real.log c)).add (isPowPolylog_log.const_mul κ)).congr ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [Real.log_mul hc (Real.rpow_pos_of_pos hpos κ).ne', Real.log_rpow hpos]

end ThreeSumApsp
