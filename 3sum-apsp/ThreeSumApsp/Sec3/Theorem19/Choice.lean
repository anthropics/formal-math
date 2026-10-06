/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Parameters
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The cost analysis of Theorem 19 for a general choice of the parameters

The two halves of the proof of Theorem 19 are the same computation with different numbers.  Both
apply Theorem 17 with a number `D ≥ 16` between `n^{1/18}/c` and `n^{1/18}` and with `g = ⌈D^η⌉`,
and solve each of the at most `4ng` instances with a saving `D^{2η}`.  Such a pair `D`, `η` is a
`Choice`, and the computation is carried out here for every choice.

1. A choice satisfies the hypotheses `16 ≤ D ≤ n` and `1 ≤ g ≤ √D` of Theorem 17 and the hypothesis
   `D^18 ≤ n` of Corollaries 15 and 16 (`Choice.sixteen_le`, `Choice.le_n`, `Choice.one_le_ceil`,
   `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. The lower bound on `D` gives `D^{-η} ≤ c^η n^{-η/18}` (`Choice.saving`), and the upper bound
   gives `D^a ≤ n^{a/18}` (`Choice.rpow_le_rpow_div`).
3. Each of the four terms of the running time is `O(n^{3-η/18})` up to logarithms: the instances
   (`Choice.instances_le`) and the scans (`Choice.scans_le`) by the first bound, the choice of `p`
   (`Choice.strassen_le`) and building the instances (`Choice.build_le`) by the second.
4. So is their sum (`exists_total_le`).
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem19

/-- A choice of the parameters of Theorem 17 as in both halves of the proof of Theorem 19: `D ≥ 16`
lies between `n^{1/18}/c` and `n^{1/18}`, and `g = ⌈D^η⌉` with `0 ≤ η ≤ 1/4`. -/
structure Choice (n D : ℕ) (η c : ℝ) : Prop where
  /-- `D ≥ 16`, as Theorem 17 asks. -/
  sixteen_le : 16 ≤ D
  /-- `D ≤ n^{1/18}`. -/
  le_root : (D : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ)
  /-- `D ≥ n^{1/18}/c`. -/
  root_div_le : (n : ℝ) ^ (1 / 18 : ℝ) / c ≤ (D : ℝ)
  /-- The constant `c` is positive. -/
  c_pos : 0 < c
  /-- `η ≥ 0`. -/
  η_nonneg : 0 ≤ η
  /-- `η ≤ 1/4`, so that `g ≤ √D`. -/
  η_le : η ≤ 1 / 4

/-- `x ≤ n^{1/18}` says that `x^18 ≤ n`. -/
theorem le_root_iff (x n : ℕ) : (x : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ) ↔ x ^ 18 ≤ n := by
  have h := Real.natCast_le_rpow_inv_iff (e := 18) (by norm_num) x n
  rwa [show ((18 : ℕ) : ℝ)⁻¹ = 1 / 18 by norm_num] at h

/-- `n^{1/18} ≥ 16` for `n ≥ 16^18`. -/
theorem sixteen_le_root {n : ℕ} (hn : 16 ^ 18 ≤ n) : (16 : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ) := by
  exact_mod_cast (le_root_iff 16 n).mpr hn

namespace Choice

variable {n D : ℕ} {η c : ℝ} (P : Choice n D η c)
include P

/-! ### The hypotheses of Theorem 17 and of Corollaries 15 and 16 -/

/-- "Corollary 15 [...] applies because D^{18} ≤ n", and likewise Corollary 16. -/
theorem pow_eighteen_le : D ^ 18 ≤ n :=
  (le_root_iff D n).mp P.le_root

/-- `D ≤ n`, as Theorem 17 asks. -/
theorem le_n : D ≤ n :=
  (Nat.le_self_pow (by norm_num) D).trans P.pow_eighteen_le

private theorem one_le_D : (1 : ℝ) ≤ D :=
  Nat.one_le_cast.mpr (le_trans (by norm_num) P.sixteen_le)

private theorem D_pos : (0 : ℝ) < D :=
  zero_lt_one.trans_le P.one_le_D

private theorem one_le_n : (1 : ℝ) ≤ n :=
  P.one_le_D.trans (Nat.cast_le.mpr P.le_n)

private theorem n_pos : (0 : ℝ) < n :=
  zero_lt_one.trans_le P.one_le_n

private theorem one_le_rpow : 1 ≤ (D : ℝ) ^ η :=
  Real.one_le_rpow P.one_le_D P.η_nonneg

/-- `g ≥ 1`, as Theorem 17 asks. -/
theorem one_le_ceil : 1 ≤ ⌈(D : ℝ) ^ η⌉₊ :=
  Nat.ceil_pos.mpr (zero_lt_one.trans_le P.one_le_rpow)

/-- `g ≤ 2 D^η`: rounding up a number that is at least 1 at most doubles it. -/
private theorem ceil_le : (⌈(D : ℝ) ^ η⌉₊ : ℝ) ≤ 2 * (D : ℝ) ^ η :=
  Nat.ceil_le_two_mul ((by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans P.one_le_rpow)

/-- `g ≤ √D`, as Theorem 17 asks: with `r = D^{1/4} ≥ 2` we have `g ≤ 2 D^η ≤ 2r ≤ r² = √D`. -/
theorem ceil_le_sqrt : (⌈(D : ℝ) ^ η⌉₊ : ℝ) ≤ √(D : ℝ) := by
  have htwo : (2 : ℝ) ≤ (D : ℝ) ^ (1 / 4 : ℝ) :=
    calc (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ (D : ℝ) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (by exact_mod_cast P.sixteen_le) (by norm_num)
  calc (⌈(D : ℝ) ^ η⌉₊ : ℝ) ≤ 2 * (D : ℝ) ^ η := P.ceil_le
    _ ≤ 2 * (D : ℝ) ^ (1 / 4 : ℝ) := by
        gcongr
        exacts [P.one_le_D, P.η_le]
    _ ≤ (D : ℝ) ^ (1 / 4 : ℝ) * (D : ℝ) ^ (1 / 4 : ℝ) := by gcongr
    _ = √(D : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add P.D_pos]
        norm_num

/-! ### Logarithms -/

/-- `log n ≥ 1`, because `n ≥ D ≥ 16`. -/
theorem one_le_log : 1 ≤ Real.log n :=
  Real.one_le_log_natCast_of_three_le ((by norm_num : 3 ≤ 16).trans (P.sixteen_le.trans P.le_n))

/-- `log D ≤ log n`. -/
theorem log_le_log : Real.log D ≤ Real.log n :=
  Real.log_le_log P.D_pos (Nat.cast_le.mpr P.le_n)

/-! ### Powers of `D` in terms of `n` -/

/-- "Finally D^{−1/36} ≤ 4^{1/36} n^{−1/648}", and "D ≥ n^{1/18}/2 gives D^{−0.0315} ≤ 2
n^{−0.0315/18}".  In general, `D ≥ n^{1/18}/c` gives `D^{-η} ≤ c^η n^{-η/18}`. -/
private theorem saving : (D : ℝ) ^ (-η) ≤ c ^ η * (n : ℝ) ^ (-(η / 18)) := by
  have hroot : 0 < (n : ℝ) ^ (1 / 18 : ℝ) := Real.rpow_pos_of_pos P.n_pos _
  calc (D : ℝ) ^ (-η) ≤ ((n : ℝ) ^ (1 / 18 : ℝ) / c) ^ (-η) :=
        Real.rpow_le_rpow_of_nonpos (div_pos hroot P.c_pos) P.root_div_le
          (neg_nonpos.mpr P.η_nonneg)
    _ = ((n : ℝ) ^ (1 / 18 : ℝ)) ^ (-η) / c ^ (-η) := Real.div_rpow hroot.le P.c_pos.le _
    _ = c ^ η * (n : ℝ) ^ (-(η / 18)) := by
        rw [← Real.rpow_mul P.n_pos.le, Real.rpow_neg P.c_pos.le, div_inv_eq_mul, mul_comm,
          show 1 / 18 * -η = -(η / 18) by ring]

/-- `n³ D^{-η} ≤ c^η n^{3-η/18}`. -/
private theorem cube_mul_saving_le :
    (n : ℝ) ^ 3 * (D : ℝ) ^ (-η) ≤ c ^ η * (n : ℝ) ^ (3 - η / 18) :=
  calc (n : ℝ) ^ 3 * (D : ℝ) ^ (-η) ≤ (n : ℝ) ^ 3 * (c ^ η * (n : ℝ) ^ (-(η / 18))) := by
        gcongr
        exact P.saving
    _ = c ^ η * (n : ℝ) ^ (3 - η / 18) := by
        rw [sub_eq_add_neg, Real.rpow_add P.n_pos, Real.rpow_ofNat]
        ring

/-- `D^a ≤ n^{a/18}` for `a ≥ 0`. -/
private theorem rpow_le_rpow_div {a : ℝ} (ha : 0 ≤ a) : (D : ℝ) ^ a ≤ (n : ℝ) ^ (a / 18) :=
  calc (D : ℝ) ^ a ≤ ((n : ℝ) ^ (1 / 18 : ℝ)) ^ a := Real.rpow_le_rpow D.cast_nonneg P.le_root ha
    _ = (n : ℝ) ^ (a / 18) := by
        rw [← Real.rpow_mul n.cast_nonneg, show 1 / 18 * a = a / 18 by ring]

/-- A power `n^b` with `b ≤ 2.9` is at most `n^{3-η/18} Λ`, for every factor `Λ ≥ 1`. -/
private theorem rpow_le_of_le {b Λ : ℝ} (hb : b ≤ 2.9) (hΛ : 1 ≤ Λ) :
    (n : ℝ) ^ b ≤ (n : ℝ) ^ (3 - η / 18) * Λ :=
  (Real.rpow_le_rpow_of_exponent_le P.one_le_n (by linarith [P.η_le])).trans
    (le_mul_of_one_le_right (Real.rpow_nonneg n.cast_nonneg _) hΛ)

/-! ### The four terms of the running time

`Λ` is the logarithmic factor of the result, `log² n` or `log n`. -/

/-- "The O(nD^{1/36}) instances cost O(n² log² D/D^{1/18}) each, so O(n³ D^{−1/36} log² n) in all",
and "The instances cost O(nD^{0.0315}) · O(n²/D^{0.063}) = O(n³ D^{−0.0315})".  `X` is the
logarithmic factor in the cost of one instance, `log² D` or 1. -/
private theorem instances_le {X Λ : ℝ} (hX : 0 ≤ X) (hXΛ : X ≤ Λ) :
    4 * (n : ℝ) * (⌈(D : ℝ) ^ η⌉₊ : ℝ) * ((n : ℝ) ^ 2 * X / (D : ℝ) ^ (2 * η))
      ≤ 8 * (c ^ η * ((n : ℝ) ^ (3 - η / 18) * Λ)) := by
  have hΛ : 0 ≤ Λ := hX.trans hXΛ
  have hdiv : (D : ℝ) ^ η / (D : ℝ) ^ (2 * η) = (D : ℝ) ^ (-η) := by
    rw [← Real.rpow_sub P.D_pos, show η - 2 * η = -η by ring]
  calc 4 * (n : ℝ) * (⌈(D : ℝ) ^ η⌉₊ : ℝ) * ((n : ℝ) ^ 2 * X / (D : ℝ) ^ (2 * η))
      ≤ 4 * (n : ℝ) * (2 * (D : ℝ) ^ η) * ((n : ℝ) ^ 2 * Λ / (D : ℝ) ^ (2 * η)) := by
        gcongr
        exact P.ceil_le
    _ = 8 * ((n : ℝ) ^ 3 * ((D : ℝ) ^ η / (D : ℝ) ^ (2 * η)) * Λ) := by ring
    _ ≤ 8 * (c ^ η * (n : ℝ) ^ (3 - η / 18) * Λ) := by
        rw [hdiv]
        gcongr 8 * (?_ * Λ)
        exact P.cube_mul_saving_le
    _ = 8 * (c ^ η * ((n : ℝ) ^ (3 - η / 18) * Λ)) := by ring

/-- "the scans cost O(n³ D^{−1/36} log n)", and "the scans O(n³ D^{−0.0315} log n)", from the term
`κ n³ log n/g` of Theorem 17. -/
private theorem scans_le {κ Λ : ℝ} (hκ : 0 ≤ κ) (hΛ : Real.log n ≤ Λ) :
    termScans n ⌈(D : ℝ) ^ η⌉₊ κ ≤ κ * (c ^ η * ((n : ℝ) ^ (3 - η / 18) * Λ)) := by
  have hpos : 0 < (D : ℝ) ^ η := Real.rpow_pos_of_pos P.D_pos η
  have hΛ0 : 0 ≤ Λ := (Real.log_natCast_nonneg n).trans hΛ
  calc κ * (n : ℝ) ^ 3 * Real.log n / (⌈(D : ℝ) ^ η⌉₊ : ℝ)
      ≤ κ * (n : ℝ) ^ 3 * Λ / (D : ℝ) ^ η := by
        gcongr
        exact Nat.le_ceil _
    _ = κ * ((n : ℝ) ^ 3 * (D : ℝ) ^ (-η) * Λ) := by
        rw [Real.rpow_neg P.D_pos.le]
        ring
    _ ≤ κ * (c ^ η * (n : ℝ) ^ (3 - η / 18) * Λ) := by
        gcongr κ * (?_ * Λ)
        exact P.cube_mul_saving_le
    _ = κ * (c ^ η * ((n : ℝ) ^ (3 - η / 18) * Λ)) := by ring

/-- "the choice of p costs O(n^{log₂ 7} D^{3/2}) = O(n^{2.9}) with Strassen's algorithm" (both
cases): `log₂ 7 + (3/2)/18 < 2.81 + 0.09`.  Strassen's exponent stands for the `ω + o(1)` of
Theorem 17. -/
private theorem strassen_le {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    termPrime strassen n D ≤ (n : ℝ) ^ (3 - η / 18) * Λ :=
  calc (n : ℝ) ^ (Real.logb 2 7) * (D : ℝ) ^ (3 / 2 : ℝ)
      ≤ (n : ℝ) ^ (Real.logb 2 7) * (n : ℝ) ^ (3 / 2 / 18 : ℝ) := by
        gcongr
        exact P.rpow_le_rpow_div (by norm_num)
    _ = (n : ℝ) ^ (Real.logb 2 7 + 3 / 2 / 18) := (Real.rpow_add P.n_pos _ _).symm
    _ ≤ (n : ℝ) ^ (3 - η / 18) * Λ := P.rpow_le_of_le (by linarith [Real.logb_two_seven_lt]) hΛ

/-- "building the instances costs O(n² D^{1.03})", respectively "O(n² D^{1.04})", from the term
`n² D g` of Theorem 17: it is at most `2 n² D^{1+η} ≤ 2 n^{2+(1+η)/18}`. -/
private theorem build_le {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    termBuild n D ⌈(D : ℝ) ^ η⌉₊ ≤ 2 * ((n : ℝ) ^ (3 - η / 18) * Λ) :=
  calc (n : ℝ) ^ 2 * (D : ℝ) * (⌈(D : ℝ) ^ η⌉₊ : ℝ)
      ≤ (n : ℝ) ^ 2 * (D : ℝ) * (2 * (D : ℝ) ^ η) := by
        gcongr
        exact P.ceil_le
    _ = 2 * ((n : ℝ) ^ 2 * (D : ℝ) ^ (1 + η)) := by
        rw [Real.rpow_add P.D_pos, Real.rpow_one]
        ring
    _ ≤ 2 * ((n : ℝ) ^ 2 * (n : ℝ) ^ ((1 + η) / 18)) := by
        gcongr
        exact P.rpow_le_rpow_div (by linarith [P.η_nonneg])
    _ = 2 * (n : ℝ) ^ (2 + (1 + η) / 18) := by rw [Real.rpow_add P.n_pos, Real.rpow_ofNat]
    _ ≤ 2 * ((n : ℝ) ^ (3 - η / 18) * Λ) := by
        gcongr
        exact P.rpow_le_of_le (by linarith [P.η_le]) hΛ

end Choice

/-- **The cost analysis of Theorem 19**, for every choice of the parameters: the time is `O(κ
n^{3-η/18} Λ)`.  The left side is the bound of Theorem 17: the number `4ng` of instances times the
cost `a n² X/D^{2η}` of one instance, plus `b` times the three terms of the additional time (with
Strassen's exponent).  `a` and `b` stand for the constants hidden in the two `O(·)`, `X` is the
logarithmic factor in the cost of one instance, and `Λ` the one in the result.  `κ` is the exponent
in the bound on the weights, the paper's ν; the paper hides it in the `O(·)`.  The constant `C`
depends only on `c` and `η` and is chosen before `n` and `D`, which is why `c ≥ 0` is asked for
separately. -/
theorem exists_total_le {c : ℝ} (hc : 0 ≤ c) (η : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n D : ℕ}, Choice n D η c → ∀ {a b κ X Λ : ℝ}, 0 ≤ a → 0 ≤ b → 1 ≤ κ →
      0 ≤ X → X ≤ Λ → Real.log n ≤ Λ →
      4 * (n : ℝ) * (⌈(D : ℝ) ^ η⌉₊ : ℝ) * (a * ((n : ℝ) ^ 2 * X / (D : ℝ) ^ (2 * η)))
        + b * (termScans n ⌈(D : ℝ) ^ η⌉₊ κ + termPrime strassen n D + termBuild n D ⌈(D : ℝ) ^ η⌉₊)
        ≤ C * ((a + b) * (κ * ((n : ℝ) ^ (3 - η / 18) * Λ))) := by
  have hcη : 0 ≤ c ^ η := Real.rpow_nonneg hc η
  refine ⟨8 * c ^ η + 3, by positivity, fun {n D} P {a b κ X Λ} ha hb hκ hX hXΛ hlogΛ => ?_⟩
  -- The scans carry the factor `κ`.  The other three terms are bounded with the logarithmic factor
  -- `κ Λ`, which is at least `Λ`, hence at least `X` and 1.
  have hΛ : 1 ≤ Λ := P.one_le_log.trans hlogΛ
  have hΛκ : Λ ≤ κ * Λ := le_mul_of_one_le_left (zero_le_one.trans hΛ) hκ
  have hinstances := P.instances_le hX (hXΛ.trans hΛκ)
  have hscans := P.scans_le (zero_le_one.trans hκ) hlogΛ
  have hstrassen := P.strassen_le (hΛ.trans hΛκ)
  have hbuild := P.build_le (hΛ.trans hΛκ)
  set R := (n : ℝ) ^ (3 - η / 18) * (κ * Λ) with hR
  have hR0 : 0 ≤ R := by positivity
  have hcηR : 0 ≤ c ^ η * R := mul_nonneg hcη hR0
  rw [show κ * (c ^ η * ((n : ℝ) ^ (3 - η / 18) * Λ)) = c ^ η * R by rw [hR]; ring] at hscans
  -- Now `hinstances` bounds the instances by `8 c^η R`, `hscans` the scans by `c^η R`,
  -- `hstrassen` the choice of `p` by `R`, and `hbuild` the building by `2 R`.
  calc _ = a * (4 * (n : ℝ) * (⌈(D : ℝ) ^ η⌉₊ : ℝ) * ((n : ℝ) ^ 2 * X / (D : ℝ) ^ (2 * η)))
        + b * (termScans n ⌈(D : ℝ) ^ η⌉₊ κ + termPrime strassen n D
          + termBuild n D ⌈(D : ℝ) ^ η⌉₊) := by ring
    _ ≤ a * ((8 * c ^ η + 3) * R) + b * ((8 * c ^ η + 3) * R) := by
        gcongr a * ?_ + b * ?_
        · linarith [hinstances, hR0]
        · linarith [hscans, hstrassen, hbuild, hcηR]
    _ = (8 * c ^ η + 3) * ((a + b) * (κ * ((n : ℝ) ^ (3 - η / 18) * Λ))) := by
        rw [hR]
        ring

end Theorem19

end ThreeSumApsp
