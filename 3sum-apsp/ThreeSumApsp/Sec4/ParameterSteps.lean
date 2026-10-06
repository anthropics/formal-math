/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.ChoosingParameters
public import ThreeSumApsp.Sec4.Theorem30
public import ThreeSumApsp.Util.Asymptotics.Dominated

/-!
# Section 4.4: the steps of the proof of Corollary 26 that hold for all parameters

The proof of Corollary 31 begins: "We repeat the proof of Corollary 26 with L := ⌈cm⌉ and t :=
⌈θm⌉". This file has the parts of the proof of Corollary 26 that mention neither `L = 21m` nor
`t = ⌈m/9⌉`, under the headings of that proof. Both corollaries use them.

* Setting up. The inner dimension is padded to `D = 4^m` with `m = ⌈log_4 D⌉`
  (`Corollary26.setting_up`). This changes no entry of the product (`Corollary26.padding`), and it
  changes the bounds by a constant factor (`padded_le`). The switching order `t = ⌈θm⌉` is
  `switchOf θ m`, and `t ≤ m` (`switchOf_le`).
* Queries. `∑_{d ≤ t} α_d ≤ (9x)^t (1 + 1/x)^m` for every `x ≥ 1/9` (`sum_alpha_le`), and for
  `x = (1-θ)/θ` the right-hand side at `t = θm` is `D^q` (`rpow_mul_pow_eq_D_rpow_qOf`).
* Encodings. Inequality (10), whose left-hand side is `lhs10 L m γ`, bounds the last term of (8) and
  gives the hypothesis `N ≥ √K N₀` of Theorem 30 (`Equation10.last_term`, `Equation10.tile_fits`).
* Conclusion. The expression (8) from a bound on its first term and (10)
  (`dominated_cost8_of_eq_10`).

Bounds "up to a constant" are written with `Dominated`, in the one parameter `m` or in the record
`Sizes` of the given inner dimension, of `N` and of `m`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/

/-- Proof of Corollary 26, "Setting up": for "m := ⌈log_4 D⌉" and `D ≥ 2` the padded inner dimension
satisfies `D ≤ 4^m` and "4^m < 4D", and "the original D was larger than 4^{m-1}". -/
theorem Corollary26.setting_up (D₀ m : ℕ) (hD : 2 ≤ D₀) (hm : m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊) :
    D₀ ≤ D m ∧ D m < 4 * D₀ ∧ 4 ^ (m - 1) < D₀ := by
  obtain rfl : m = Nat.clog 4 D₀ := by
    rw [hm, ← Real.natCeil_logb_natCast]
    norm_num
  have hpos : 1 ≤ Nat.clog 4 D₀ := Nat.clog_pos (by norm_num) hD
  have hlt : 4 ^ (Nat.clog 4 D₀ - 1) < D₀ := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hsucc : 4 ^ Nat.clog 4 D₀ = 4 * 4 ^ (Nat.clog 4 D₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_, hlt⟩
  unfold D
  omega

/-- Proof of Corollary 26, "Setting up": "pad the inner dimension to 4^m < 4D with zero columns of X
and zero rows of Y. This changes no entry of XY". -/
theorem Corollary26.padding {N D₀ : ℕ} (D' : ℕ) (hD : D₀ ≤ D') (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) :
    padInnerCols D' X * padInnerRows D' Y = X * Y := by
  ext I J
  rw [Matrix.mul_apply, Matrix.mul_apply]
  -- The sum over the `D'` columns has the `D₀` terms of `XY`, and zeros at the added columns.
  refine (Fintype.sum_of_injective (Fin.castLE hD) (Fin.castLE_injective hD) _ _
    (fun k hk => ?_) fun k => ?_).symm
  · have hk' : ¬ (k : ℕ) < D₀ := fun h => hk ⟨⟨k, h⟩, rfl⟩
    simp only [padInnerCols, dif_neg hk', zero_mul]
  · simp only [padInnerCols, padInnerRows, Fin.val_castLE, k.isLt, dite_true, Fin.eta]

/-- The numbers in which the bounds of Section 4.4 are stated. -/
structure Sizes where
  /-- The given inner dimension, before the padding. -/
  D₀ : ℕ
  /-- The size of the product: the matrices are `N × D₀` and `D₀ × N`. -/
  N : ℕ
  /-- The padded inner dimension is `D = 4^m`. -/
  m : ℕ

/-- Proof of Corollary 26, "Setting up": "m := ⌈log_4 D⌉", for a given inner dimension `D₀ ≥ 2`. -/
structure Sizes.SetUp (p : Sizes) : Prop where
  two_le : 2 ≤ p.D₀
  m_eq : p.m = ⌈Real.logb 4 (p.D₀ : ℝ)⌉₊

/-- The padded inner dimension is at least the given one. -/
theorem Sizes.SetUp.le {p : Sizes} (h : p.SetUp) : p.D₀ ≤ D p.m :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).1

/-- "4^m < 4D". -/
theorem Sizes.SetUp.lt {p : Sizes} (h : p.SetUp) : D p.m < 4 * p.D₀ :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).2.1

/-- "the original D was larger than 4^{m-1}". -/
theorem Sizes.SetUp.gt {p : Sizes} (h : p.SetUp) : 4 ^ (p.m - 1) < p.D₀ :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).2.2

/-- `m ≥ 1`, because `2 ≤ D₀ ≤ 4^m`. -/
theorem Sizes.SetUp.m_pos {p : Sizes} (h : p.SetUp) : 1 ≤ p.m :=
  Nat.pos_of_ne_zero fun h0 => by
    have hle := h.le
    have htwo := h.two_le
    rw [h0, D, pow_zero] at hle
    omega

/-- Proof of Corollary 26, "Setting up": padding "changes D by a factor less than 4, which only
affects the constants". A bound `D^a log^k D` in the padded `D = 4^m` is, up to a constant, the same
bound in the original inner dimension `D₀`. (Corollary 26 has `k = 0`; the bounds of Corollary 31
have logarithms.) -/
theorem padded_le (a : ℝ) (k : ℕ) :
    Dominated Sizes.SetUp (fun p => (D p.m : ℝ) ^ a * Real.log (D p.m) ^ k)
      fun p => (p.D₀ : ℝ) ^ a * Real.log p.D₀ ^ k := by
  refine .of_le_const_mul (C := 4 ^ |a| * 3 ^ k) (by positivity) fun ⟨D₀, _, m⟩ h => ?_
  have htwo : (2 : ℝ) ≤ D₀ := by exact_mod_cast h.two_le
  have hD₀ : (0 : ℝ) < D₀ := by linarith
  have hle' : 1 ≤ (D m : ℝ) / D₀ := (one_le_div hD₀).2 (by exact_mod_cast h.le)
  have hle4 : (D m : ℝ) ≤ 4 * D₀ := by exact_mod_cast h.lt.le
  have hpow : (D m : ℝ) ^ a ≤ 4 ^ |a| * (D₀ : ℝ) ^ a :=
    calc (D m : ℝ) ^ a = ((D m : ℝ) / D₀) ^ a * (D₀ : ℝ) ^ a := by
          rw [← Real.mul_rpow (by positivity) hD₀.le, div_mul_cancel₀ _ hD₀.ne']
      _ ≤ 4 ^ |a| * (D₀ : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right
            ((Real.rpow_le_rpow_of_exponent_le hle' (le_abs_self a)).trans
              (Real.rpow_le_rpow (by positivity) ((div_le_iff₀ hD₀).2 hle4) (abs_nonneg a)))
            (by positivity)
  have hlog : Real.log (D m) ≤ 3 * Real.log D₀ :=
    calc Real.log (D m) ≤ Real.log (4 * D₀) := Real.log_le_log (cast_D_pos m) hle4
      _ = 2 * Real.log 2 + Real.log D₀ := by
          rw [Real.log_mul (by norm_num) hD₀.ne', Real.log_four]
      _ ≤ 3 * Real.log D₀ := by linarith [Real.log_le_log two_pos htwo]
  calc (D m : ℝ) ^ a * Real.log (D m) ^ k
      ≤ 4 ^ |a| * (D₀ : ℝ) ^ a * (3 * Real.log D₀) ^ k :=
        mul_le_mul hpow (pow_le_pow_left₀ (by positivity) hlog k) (by positivity) (by positivity)
    _ = 4 ^ |a| * 3 ^ k * ((D₀ : ℝ) ^ a * Real.log D₀ ^ k) := by
        rw [mul_pow]
        ring

/-- The switching order `t = ⌈θm⌉`: "t := ⌈m/9⌉" in the proof of Corollary 26, where `θ = 1/9`, and
"t := ⌈θm⌉" in the proof of Corollary 31. -/
noncomputable def switchOf (θ : ℝ) (m : ℕ) : ℕ := ⌈θ * (m : ℝ)⌉₊

/-- The hypothesis `t ≤ m` of Theorem 30 holds for `t = ⌈θm⌉` with `θ ≤ 1`. -/
theorem switchOf_le {θ : ℝ} (hθ : θ ≤ 1) (m : ℕ) : switchOf θ m ≤ m :=
  Nat.ceil_le.2 (mul_le_of_le_one_left (Nat.cast_nonneg m) hθ)

/-! ### Queries -/

/-- Proof of Corollary 26, "Queries": "A query reads ∑_{d≤t} α_d numbers, and we bound this sum as
in the proof of Lemma 11. Since 9^d = 72^d 8^{-d} ≤ 72^t 8^{-d} for d ≤ t", the sum `∑_{d ≤ t} α_d`
is at most `72^t ∑_{d=0}^{m} binom(m, d) 8^{-d} = 72^t (9/8)^m`. Here any `x > 0` with `9x ≥ 1`
stands for 8, because the proof of Corollary 31 makes "the same calculation with x := (1-θ)/θ in
place of 8". -/
theorem sum_alpha_le {x : ℝ} (hx : 0 < x) (h9x : 1 ≤ 9 * x) {m t : ℕ} (htm : t ≤ m) :
    ∑ d ∈ range (t + 1), (alpha m d : ℝ) ≤ (9 * x) ^ t * (1 + 1 / x) ^ m := by
  -- `9^d = (9x)^d x^{-d} ≤ (9x)^t x^{-d}` for `d ≤ t`
  have hterm : ∀ d ∈ range (t + 1),
      (alpha m d : ℝ) ≤ (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by
    intro d hd
    have hpow : (9 * x) ^ d ≤ (9 * x) ^ t :=
      pow_le_pow_right₀ h9x (by rw [mem_range] at hd; omega)
    calc (alpha m d : ℝ) = (9 * x) ^ d * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by
          rw [alpha, one_pow, mul_one, ← mul_assoc, ← mul_pow,
            show 9 * x * (1 / x) = 9 by field_simp]
          push_cast
          ring
      _ ≤ (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by gcongr
  calc ∑ d ∈ range (t + 1), (alpha m d : ℝ)
      ≤ ∑ d ∈ range (t + 1), (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) :=
        sum_le_sum hterm
    _ ≤ ∑ d ∈ range (m + 1), (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
          fun _ _ _ => by positivity
    _ = (9 * x) ^ t * (1 + 1 / x) ^ m := by rw [← mul_sum, ← add_pow, add_comm]

/-- `(9x)^{θm} (1+1/x)^m = D^q` for "x := (1-θ)/θ". -/
theorem rpow_mul_pow_eq_D_rpow_qOf {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (m : ℕ) :
    (9 * ((1 - θ) / θ)) ^ (θ * (m : ℝ)) * (1 + 1 / ((1 - θ) / θ)) ^ m = (D m : ℝ) ^ qOf θ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ1
  have hinv : 1 + 1 / ((1 - θ) / θ) = (1 - θ)⁻¹ := by
    field_simp
    ring
  rw [← exp_entropy_eq_D_rpow_qOf, hinv, Real.rpow_def_of_pos (by positivity),
    ← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), ← Real.exp_add, Real.log_inv,
    Real.log_mul (by norm_num) (by positivity), Real.log_div h1θ.ne' hθ0.ne', entropy]
  congr 1
  ring

/-! ### Encodings -/

/-- The left-hand side of (10): "D^γ · 10^L / (√K N₀)", with `D = 4^m`. Inequality (10) says that it
is at most `N`. -/
noncomputable def lhs10 (L m : ℕ) (γ : ℝ) : ℝ := (D m : ℝ) ^ γ * (10 : ℝ) ^ L / sqrtKN0 L m

/-- Proof of Corollary 26: (10) implies "that the last term of (8) is at most N²/D^γ", "by
rearranging". -/
theorem Equation10.last_term {L m N : ℕ} {γ : ℝ} (h10 : lhs10 L m γ ≤ N) :
    (N : ℝ) * (10 : ℝ) ^ L / sqrtKN0 L m ≤ (N : ℝ) ^ 2 / (D m : ℝ) ^ γ := by
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (cast_D_pos m) γ)]
  calc (N : ℝ) * (10 : ℝ) ^ L / sqrtKN0 L m * (D m : ℝ) ^ γ
      = (N : ℝ) * lhs10 L m γ := by rw [lhs10]; ring
    _ ≤ (N : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_left h10 (Nat.cast_nonneg N)
    _ = (N : ℝ) ^ 2 := (sq _).symm

/-- Proof of Corollary 26: (10) implies "that N ≥ √K N₀", "because 10^L ≥ M = K N₀² and D^γ ≥ 1"
(here `γ ≥ 0`). -/
theorem Equation10.tile_fits {L m N : ℕ} (hmL : m ≤ L) {γ : ℝ} (hγ : 0 ≤ γ)
    (h10 : lhs10 L m γ ≤ N) : sqrtKN0 L m ≤ N := by
  have hpos := sqrtKN0_pos hmL
  have hM : sqrtKN0 L m ^ 2 ≤ (10 : ℝ) ^ L := by
    rw [sqrtKN0_sq]
    exact_mod_cast M_le_ten_pow L m
  have hD1 : 1 ≤ (D m : ℝ) ^ γ := Real.one_le_rpow (one_le_cast_D m) hγ
  calc sqrtKN0 L m = sqrtKN0 L m ^ 2 / sqrtKN0 L m := by field_simp
    _ ≤ (10 : ℝ) ^ L / sqrtKN0 L m := div_le_div_of_nonneg_right hM hpos.le
    _ ≤ lhs10 L m γ :=
        div_le_div_of_nonneg_right (le_mul_of_one_le_left (by positivity) hD1) hpos.le
    _ ≤ (N : ℝ) := h10

/-! ### Conclusion -/

/-- The expression (8) from its two terms, with `L` and `t` given as functions of `m`. If the first
term, without its factor `N²`, is `O(G)`, where `G ≥ D^{-γ}`, then (8) is `O(G N²)` wherever (10)
holds. -/
theorem dominated_cost8_of_eq_10 {Lof tof : ℕ → ℕ} {γ : ℝ} {G : ℕ → ℝ} {domM : ℕ → Prop}
    {dom : Sizes → Prop}
    (hfirst : Dominated domM
      (fun m => (Lof m : ℝ) * m * (rho (Lof m) m ^ tof m / (1 - rho (Lof m) m))) G)
    (hdom : ∀ p, dom p → domM p.m) (hG : ∀ p, dom p → (D p.m : ℝ) ^ (-γ) ≤ G p.m)
    (h10 : ∀ p, dom p → lhs10 (Lof p.m) p.m γ ≤ p.N) :
    Dominated dom (fun p => cost8 (Lof p.m) p.m (tof p.m) p.N) fun p => G p.m * (p.N : ℝ) ^ 2 := by
  -- the first term of (8), with its factor `N²`
  have hboxes := (hfirst.comp Sizes.m hdom).mul_right (k := fun p => (p.N : ℝ) ^ 2)
    fun _ _ => sq_nonneg _
  -- the last term
  have hencodings : Dominated dom
      (fun p => (p.N : ℝ) * (10 : ℝ) ^ Lof p.m / sqrtKN0 (Lof p.m) p.m)
      fun p => G p.m * (p.N : ℝ) ^ 2 :=
    .of_le fun p hp => (Equation10.last_term (h10 p hp)).trans <| by
      rw [div_eq_mul_inv, mul_comm, ← Real.rpow_neg (cast_D_pos p.m).le]
      exact mul_le_mul_of_nonneg_right (hG p hp) (sq_nonneg _)
  exact hboxes.add hencodings

end ThreeSumApsp
