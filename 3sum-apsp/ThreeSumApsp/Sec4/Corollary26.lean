/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.ParameterSteps
public import ThreeSumApsp.Sec4.Table2
public import ThreeSumApsp.Util.Asymptotics.Logarithms

/-!
# Corollary 26: the parameters `L = 21m`, `t = ⌈m/9⌉`

The proof of Corollary 26 from Theorem 30, in the five steps of the paper. The parts of these steps
that hold for all `L` and `t` are proved before (`Corollary26.setting_up` to
`dominated_cost8_of_eq_10`), and Corollary 31 uses them too. The exponents `γ` and `q` of the proof
are written `gammaOf 21 (1 / 9)` and `qOf (1 / 9)`: they are the `γ` and `q` of Corollary 31 at
`c = 21` and `θ = 1/9` (`Corollary26.gamma_eq`, `Corollary26.q_eq`). The result is
`Corollary26.costs`: for `N ≥ D^18` and `m = ⌈log_4 D⌉ ≥ 60` the hypothesis `N ≥ √K N₀` of Theorem
30 holds at `L = 21m` and `t = ⌈m/9⌉`, its preprocessing cost (8) (`cost8`) is `O(N²/D^{0.063})`,
and its query cost `L ∑_{d ≤ t} α_d` (`costQuery`) is `O(D^{0.437})`.

* Setting up. The inner dimension is padded to `D = 4^m` (`Corollary26.setting_up`). This changes no
  entry of the product (`Corollary26.padding`), it changes the bounds by a constant factor
  (`padded_le`), and the hypothesis reads `N ≥ 4^{18(m-1)}` (`Corollary26.hypothesis`). The number
  `t = ⌈m/9⌉` is `switchOf (1 / 9) m`, and `t ≤ m` (`switchOf_le`).
* Boxes. `ρ < 9/20` and `ρ^t ≤ (9/20)^{m/9} = D^{-γ}` with `γ = 0.0640…` (`Corollary26.rho_lt`,
  `Corollary26.rho_pow_le`, `Corollary26.gamma_digits`), so the first term of (8) is `O(m² N²/D^γ)`
  (`Corollary26.first_term`).
* Queries. `∑_{d ≤ t} α_d ≤ 72^t (9/8)^m < 72 D^q` with `q = 0.4277…` (`sum_alpha_le`,
  `Corollary26.sum_alpha_lt`, `Corollary26.q_digits`), so a query costs `O(m D^q)`
  (`Corollary26.query_cost`).
* Encodings. Inequality (10) bounds the last term of (8) and gives the hypothesis of Theorem 30
  (`Equation10.last_term`, `Equation10.tile_fits`). The standard bound on `K` (`Corollary26.le_K`)
  shows that the left-hand side of (10) is at most `√(21m+1) Λ^m` (`Corollary26.lhs10_le`);
  `Λ = 4.198… · 10^10` is below `4^18 = 6.871… · 10^10` by a factor of more than 1.63
  (`baseLambda_numeric`, `four_pow_eighteen_numeric`, `baseLambda_mul_lt`), and
  `1.63^m ≥ 4^18 √(21m+1)` for `m ≥ 60` (`Corollary26.threshold`). Together they give (10) for all
  `m ≥ 60` (`eq_10_corollary_26`).
* Conclusion. For `m ≥ 60` the hypothesis `N ≥ √K N₀` holds and (8) is `O(m² N²/D^γ)`
  (`Corollary26.tile_fits`, `dominated_cost8_of_eq_10`, `Corollary26.preprocessing`), the powers of
  `m` are absorbed into the exponents (`dominated_pow_mul_D_rpow`, `Corollary26.conclusion`), and
  the bounds are stated in the given `D` (`Corollary26.costs`). For `|W| ≤ N²/√D` queries the total
  is `O(N²/D^{0.063})` (`corollary_26_W`).

Bounds "up to a constant" are written with `Dominated`, in the one parameter `m` or in the record
`Sizes` of the given `D`, of `N` and of `m`. Two sentences of the proof are proved with the programs
(`wordRam_corollary_26`, `wordRam_corollary_26_wanted`): "(For m < 60, D is bounded by a constant,
and the corollary holds trivially.)" and "The bound for a set W follows by asking |W| queries." The
last section shows that the parameters of this proof are those of Corollary 31 and of Table 2 at
`c = 21` and `θ = 1/9`; nothing else rests on it.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/

/-- Proof of Corollary 26, "Setting up": "since the original D was larger than 4^{m-1}, the
assumption N ≥ D^18 now reads N ≥ 4^{18(m-1)}". -/
theorem Corollary26.hypothesis {D₀ N m : ℕ} (hgt : 4 ^ (m - 1) < D₀) (hN : D₀ ^ 18 ≤ N) :
    4 ^ (18 * (m - 1)) ≤ N := by
  rw [mul_comm, pow_mul]
  exact (Nat.pow_le_pow_left hgt.le 18).trans hN

/-! ### Boxes -/

/-- Proof of Corollary 26: "ρ = 9m/(L-m+1) = 9m/(20m+1) < 9/20, so 1/(1-ρ) < 2". -/
theorem Corollary26.rho_lt (m : ℕ) :
    rho (21 * m) m = 9 * (m : ℝ) / (20 * (m : ℝ) + 1) ∧ rho (21 * m) m < 9 / 20 ∧
      1 / (1 - rho (21 * m) m) < 2 := by
  have heq : rho (21 * m) m = 9 * (m : ℝ) / (20 * (m : ℝ) + 1) := by
    rw [rho]
    push_cast
    ring_nf
  have hlt : rho (21 * m) m < 9 / 20 := by
    rw [heq, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨heq, hlt, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- Proof of Corollary 26: "since t ≥ m/9, also ρ^t ≤ (9/20)^{m/9} = D^{-γ}". -/
theorem Corollary26.rho_pow_le (m : ℕ) :
    rho (21 * m) m ^ switchOf (1 / 9) m ≤ (9 / 20 : ℝ) ^ ((m : ℝ) / 9) ∧
      (9 / 20 : ℝ) ^ ((m : ℝ) / 9) = (D m : ℝ) ^ (-gammaOf 21 (1 / 9)) := by
  obtain ⟨-, hlt, -⟩ := Corollary26.rho_lt m
  constructor
  · calc rho (21 * m) m ^ switchOf (1 / 9) m
        ≤ (9 / 20 : ℝ) ^ switchOf (1 / 9) m :=
          pow_le_pow_left₀ (rho_nonneg (by omega)) hlt.le _
      _ = (9 / 20 : ℝ) ^ ((switchOf (1 / 9) m : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (9 / 20 : ℝ) ^ ((m : ℝ) / 9) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
            ((by ring_nf : (m : ℝ) / 9 = 1 / 9 * m).le.trans (Nat.le_ceil _))
  · -- `ρ_c = 9/20` at `c = 21`
    have h := rhoC_rpow_eq_D_rpow 21 (1 / 9) (by norm_num) m
    rwa [show rhoC 21 = 9 / 20 by norm_num [rhoC], show (1 / 9 : ℝ) * m = m / 9 by ring] at h

/-- Proof of Corollary 26: "γ := ln(20/9)/(9 ln 4)". This is the `γ` of Corollary 31 at `c = 21` and
`θ = 1/9`, where `ρ_c = 9/20`; the statements of this file write it `gammaOf 21 (1 / 9)`. -/
theorem Corollary26.gamma_eq : gammaOf 21 (1 / 9) = Real.log (20 / 9) / (9 * Real.log 4) := by
  have hfour : Real.log 4 ≠ 0 := log_four_pos.ne'
  rw [gammaOf, rhoC, show (1 / (9 / (21 - 1)) : ℝ) = 20 / 9 by norm_num]
  field_simp

/-- Proof of Corollary 26: "γ := ln(20/9)/(9 ln 4) = 0.0640…". The digits come from the bounds on
logarithms proved for Table 2. -/
theorem Corollary26.gamma_digits : 0.0640 < gammaOf 21 (1 / 9) ∧ gammaOf 21 (1 / 9) < 0.0641 := by
  have heq := gammaOf_eq_mul 21 (1 / 9)
  have hmem := gammaOf_21_one_mem
  exact ⟨by linarith [heq, hmem.1], by linarith [heq, hmem.2]⟩

/-- Proof of Corollary 26: "Hence the first term of (8) is O(m² N²/D^γ)". The common factor `N²` is
left out. -/
theorem Corollary26.first_term :
    Dominated (fun _ : ℕ => True)
      (fun m => ((21 * m : ℕ) : ℝ) * m *
        (rho (21 * m) m ^ switchOf (1 / 9) m / (1 - rho (21 * m) m)))
      fun m => (m : ℝ) ^ 2 * (D m : ℝ) ^ (-gammaOf 21 (1 / 9)) := by
  refine .of_le_const_mul (C := 42) (by norm_num) fun m _ => ?_
  obtain ⟨-, hlt, htwo⟩ := Corollary26.rho_lt m
  obtain ⟨hpow, heq⟩ := Corollary26.rho_pow_le m
  rw [heq] at hpow
  -- `ρ^t/(1-ρ) ≤ 2 D^{-γ}`
  have hdecay : rho (21 * m) m ^ switchOf (1 / 9) m / (1 - rho (21 * m) m)
      ≤ (D m : ℝ) ^ (-gammaOf 21 (1 / 9)) * 2 := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hpow htwo.le (one_div_nonneg.2 (by linarith)) (by positivity)
  calc ((21 * m : ℕ) : ℝ) * m * (rho (21 * m) m ^ switchOf (1 / 9) m / (1 - rho (21 * m) m))
      ≤ ((21 * m : ℕ) : ℝ) * m * ((D m : ℝ) ^ (-gammaOf 21 (1 / 9)) * 2) := by
        gcongr
    _ = 42 * ((m : ℝ) ^ 2 * (D m : ℝ) ^ (-gammaOf 21 (1 / 9))) := by
        push_cast
        ring

/-! ### Queries -/

/-- `72^{m/9} (9/8)^m = D^q`: at `θ = 1/9` the number `x = (1-θ)/θ` is 8. -/
private lemma rpow_div_nine_eq (m : ℕ) :
    (72 : ℝ) ^ ((m : ℝ) / 9) * (9 / 8 : ℝ) ^ m = (D m : ℝ) ^ qOf (1 / 9) := by
  have h := rpow_mul_pow_eq_D_rpow_qOf (θ := 1 / 9) (by norm_num) (by norm_num) m
  rwa [show (9 * ((1 - 1 / 9) / (1 / 9)) : ℝ) = 72 by norm_num,
    show (1 + 1 / ((1 - 1 / 9) / (1 / 9)) : ℝ) = 9 / 8 by norm_num,
    show (1 / 9 : ℝ) * m = m / 9 by ring] at h

/-- Proof of Corollary 26, the display of the step "Queries": "∑_{d=0}^{t} binom(m, d) 9^d ≤ 72^t
∑_{d=0}^{m} binom(m, d) 8^{-d} = 72^t (9/8)^m < 72 · (72 · (9/8)^9)^{m/9} = 72 D^q", with
`t = ⌈m/9⌉`. -/
theorem Corollary26.sum_alpha_lt (m : ℕ) :
    ∑ d ∈ range (switchOf (1 / 9) m + 1), (alpha m d : ℝ) < 72 * (D m : ℝ) ^ qOf (1 / 9) := by
  set t : ℕ := switchOf (1 / 9) m
  have htm : t ≤ m := switchOf_le (by norm_num) m
  -- "t < m/9 + 1"
  have htlt : (t : ℝ) < (m : ℝ) / 9 + 1 := by
    have h : (t : ℝ) < 1 / 9 * (m : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  calc ∑ d ∈ range (t + 1), (alpha m d : ℝ)
      ≤ (9 * 8) ^ t * (1 + 1 / 8 : ℝ) ^ m := sum_alpha_le (by norm_num) (by norm_num) htm
    _ = 72 ^ t * (9 / 8 : ℝ) ^ m := by norm_num
    _ < 72 * (72 : ℝ) ^ ((m : ℝ) / 9) * (9 / 8 : ℝ) ^ m := by
        gcongr
        calc (72 : ℝ) ^ t = (72 : ℝ) ^ (t : ℝ) := (Real.rpow_natCast _ _).symm
          _ < (72 : ℝ) ^ ((m : ℝ) / 9 + 1) :=
              Real.rpow_lt_rpow_of_exponent_lt (by norm_num) htlt
          _ = 72 * (72 : ℝ) ^ ((m : ℝ) / 9) := by
              rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
    _ = 72 * (D m : ℝ) ^ qOf (1 / 9) := by
        rw [mul_assoc, rpow_div_nine_eq]

/-- Proof of Corollary 26: "q := ln(72 · (9/8)^9)/(9 ln 4)". This is the `q` of Corollary 31 at
`θ = 1/9`; the statements of this file write it `qOf (1 / 9)`. -/
theorem Corollary26.q_eq : qOf (1 / 9) = Real.log (72 * (9 / 8) ^ 9) / (9 * Real.log 4) := by
  have hfour := log_four_pos.ne'
  have h72 : Real.log 72 = Real.log 8 + Real.log 9 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [qOf, entropy, show (1 : ℝ) - 1 / 9 = 8 / 9 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    Real.log_one, Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    Real.log_div (by norm_num) (by norm_num), h72]
  field_simp
  ring

/-- Proof of Corollary 26: "q := ln(72 · (9/8)^9)/(9 ln 4) = 0.4277…". The digits come from the
bounds on logarithms proved for Table 2. -/
theorem Corollary26.q_digits : 0.4277 < qOf (1 / 9) ∧ qOf (1 / 9) < 0.4278 :=
  ⟨lt_of_lt_of_le (by norm_num) qOf_ninth_mem.1, lt_of_le_of_lt qOf_ninth_mem.2 (by norm_num)⟩

/-- Proof of Corollary 26: "Hence a query takes O(L D^q) = O(m D^q) time." -/
theorem Corollary26.query_cost :
    Dominated (fun _ : ℕ => True) (fun m => costQuery (21 * m) m (switchOf (1 / 9) m))
      fun m => (m : ℝ) * (D m : ℝ) ^ qOf (1 / 9) := by
  refine .of_le_const_mul (C := 21 * 72) (by norm_num) fun m _ => ?_
  calc costQuery (21 * m) m (switchOf (1 / 9) m)
      ≤ ((21 * m : ℕ) : ℝ) * (72 * (D m : ℝ) ^ qOf (1 / 9)) :=
        mul_le_mul_of_nonneg_left (Corollary26.sum_alpha_lt m).le (Nat.cast_nonneg _)
    _ = 21 * 72 * ((m : ℝ) * (D m : ℝ) ^ qOf (1 / 9)) := by
        push_cast
        ring

/-! ### Encodings -/

/-- Proof of Corollary 26: "the standard bound [...] gives K = binom(21m, m) ≥ 1/(21m+1) ·
(21^21/20^20)^m". -/
theorem Corollary26.le_K {m : ℕ} (hm : 1 ≤ m) :
    ((21 : ℝ) ^ 21 / 20 ^ 20) ^ m / (21 * (m : ℝ) + 1) ≤ (K (21 * m) m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  -- the standard bound at `n = 21m`, `k = m`
  have hstd : ((21 : ℝ) * m) ^ (21 * m)
      ≤ (21 * (m : ℝ) + 1) * ((K (21 * m) m : ℝ) * (m : ℝ) ^ m * ((20 : ℝ) * m) ^ (20 * m)) := by
    have h := Nat.pow_self_le_mul_choose_mul_pow_mul_pow (n := 21 * m) (k := m) (by omega)
    rw [show 21 * m - m = 20 * m by omega] at h
    unfold K
    exact_mod_cast h
  -- the powers of `m` cancel: `m^{21m} = m^m m^{20m}`
  have hsplit : (m : ℝ) ^ (21 * m) = (m : ℝ) ^ m * (m : ℝ) ^ (20 * m) := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow, mul_pow, hsplit] at hstd
  have hcancel : (21 : ℝ) ^ (21 * m)
      ≤ (K (21 * m) m : ℝ) * ((20 : ℝ) ^ (20 * m) * (21 * (m : ℝ) + 1)) := by
    refine le_of_mul_le_mul_right (hstd.trans_eq ?_)
      (show 0 < (m : ℝ) ^ m * (m : ℝ) ^ (20 * m) by positivity)
    ring
  rwa [div_pow, ← pow_mul, ← pow_mul, div_div, div_le_iff₀ (by positivity)]

/-- The base `Λ` of the proof of Corollary 26: "Λ := 10^21 · (20/9)^{1/9} / ((21^21/20^20)^{1/2} ·
3^20)". -/
noncomputable def baseLambda : ℝ :=
  10 ^ 21 * (20 / 9 : ℝ) ^ (1 / 9 : ℝ) / (Real.sqrt (21 ^ 21 / 20 ^ 20) * 3 ^ 20)

/-- Proof of Corollary 26: "the left-hand side of (10) is at most √(21m+1) · Λ^m". -/
theorem Corollary26.lhs10_le {m : ℕ} (hm : 1 ≤ m) :
    lhs10 (21 * m) m (gammaOf 21 (1 / 9)) ≤ Real.sqrt (21 * (m : ℝ) + 1) * baseLambda ^ m := by
  -- "D^γ = (20/9)^{m/9}, 10^L = 10^{21m}, and N₀ = 3^{20m}"
  have hD : (D m : ℝ) ^ gammaOf 21 (1 / 9) = ((20 / 9 : ℝ) ^ (1 / 9 : ℝ)) ^ m := by
    have hfour := log_four_pos.ne'
    rw [Corollary26.gamma_eq, cast_D_rpow, ← Real.rpow_mul_natCast (by norm_num),
      Real.rpow_def_of_pos (by norm_num)]
    congr 1
    field_simp
  have hN0 : (N0 (21 * m) m : ℝ) = ((3 : ℝ) ^ 20) ^ m := by
    rw [N0, show 21 * m - m = 20 * m by omega, pow_mul]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hroot : 0 < Real.sqrt (21 * (m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hs : 0 < Real.sqrt (21 ^ 21 / 20 ^ 20) := Real.sqrt_pos.2 (by positivity)
  -- the bound on `K`, under the square root
  have hK : Real.sqrt (21 ^ 21 / 20 ^ 20) ^ m / Real.sqrt (21 * (m : ℝ) + 1)
      ≤ Real.sqrt (K (21 * m) m) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [div_pow, ← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    exact Corollary26.le_K hm
  rw [lhs10, sqrtKN0, hD, hN0, pow_mul]
  calc ((20 / 9 : ℝ) ^ (1 / 9 : ℝ)) ^ m * ((10 : ℝ) ^ 21) ^ m
        / (Real.sqrt (K (21 * m) m) * ((3 : ℝ) ^ 20) ^ m)
      ≤ ((20 / 9 : ℝ) ^ (1 / 9 : ℝ)) ^ m * ((10 : ℝ) ^ 21) ^ m
        / (Real.sqrt (21 ^ 21 / 20 ^ 20) ^ m / Real.sqrt (21 * (m : ℝ) + 1)
          * ((3 : ℝ) ^ 20) ^ m) := by
        gcongr
    _ = Real.sqrt (21 * (m : ℝ) + 1) * baseLambda ^ m := by
        rw [baseLambda, div_pow, mul_pow, mul_pow]
        field_simp

/-- Proof of Corollary 26: `Λ` "= 4.198… · 10^10". Eighteenth powers are compared: `Λ^18` is a
rational number. -/
theorem baseLambda_numeric : 4.198 * 10 ^ 10 < baseLambda ∧ baseLambda < 4.199 * 10 ^ 10 := by
  have hpow : baseLambda ^ 18
      = (10 ^ 21) ^ 18 * (20 / 9) ^ 2 / ((21 ^ 21 / 20 ^ 20) ^ 9 * (3 ^ 20) ^ 18) := by
    rw [baseLambda, div_pow, mul_pow, mul_pow, ← Real.rpow_mul_natCast (by norm_num),
      pow_mul (Real.sqrt _) 2 9, Real.sq_sqrt (by positivity)]
    norm_num
  exact ⟨lt_of_pow_lt_pow_left₀ 18 (by unfold baseLambda; positivity) (by rw [hpow]; norm_num),
    lt_of_pow_lt_pow_left₀ 18 (by norm_num) (by rw [hpow]; norm_num)⟩

/-- Proof of Corollary 26: "Its base 4^18 = 6.871… · 10^10". -/
theorem four_pow_eighteen_numeric :
    6.871 * 10 ^ 10 < (4 : ℝ) ^ 18 ∧ (4 : ℝ) ^ 18 < 6.872 * 10 ^ 10 := by
  constructor <;> norm_num

/-- Proof of Corollary 26: `4^18` "is larger than Λ by a factor of more than 1.63". -/
theorem baseLambda_mul_lt : 1.63 * baseLambda < 4 ^ 18 :=
  calc 1.63 * baseLambda < 1.63 * (4.199 * 10 ^ 10) :=
        mul_lt_mul_of_pos_left baseLambda_numeric.2 (by norm_num)
    _ < 6.871 * 10 ^ 10 := by norm_num
    _ < 4 ^ 18 := four_pow_eighteen_numeric.1

/-- Proof of Corollary 26: "1.63^m ≥ 4^18 √(21m+1), which is the case for all m ≥ 60". -/
theorem Corollary26.threshold {m : ℕ} (hm : 60 ≤ m) :
    (4 : ℝ) ^ 18 * Real.sqrt (21 * (m : ℝ) + 1) ≤ 1.63 ^ m := by
  -- the squares: `4^36 (21m + 1) ≤ 1.63^{2m}`, by induction from `m = 60`
  have hsq : (4 : ℝ) ^ 36 * (21 * (m : ℝ) + 1) ≤ (1.63 ^ m) ^ 2 := by
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have hn' : (60 : ℝ) ≤ n := by exact_mod_cast hn
      rw [pow_succ (1.63 : ℝ), mul_pow]
      push_cast
      -- `1.63²` times the bound for `n`, and `21 (n + 1) + 1 ≤ 1.63² (21n + 1)`
      linarith [ih, hn']
  rw [← le_div_iff₀' (by positivity)]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rwa [div_pow, le_div_iff₀' (by positivity), ← pow_mul]

/-- Equation (10), `D^γ · 10^L / (√K N₀) ≤ N`, where it is printed, in the proof of Corollary 26.
There `D = 4^m`, "L := 21m", "γ := ln(20/9)/(9 ln 4)", "K = binom(21m, m)", "N₀ = 3^{20m}", and "the
assumption N ≥ D^18 now reads N ≥ 4^{18(m-1)}". The inequality "holds whenever
1.63^m ≥ 4^18 √(21m+1), which is the case for all m ≥ 60". -/
theorem eq_10_corollary_26 (m N : ℕ) (hm : 60 ≤ m) (hN : 4 ^ (18 * (m - 1)) ≤ N) :
    (D m : ℝ) ^ (Real.log (20 / 9) / (9 * Real.log 4)) * (10 : ℝ) ^ (21 * m)
        / (Real.sqrt (K (21 * m) m) * (N0 (21 * m) m : ℝ))
      ≤ (N : ℝ) := by
  have hΛ0 : 0 ≤ baseLambda := by linarith [baseLambda_numeric.1]
  have hΛ : baseLambda ≤ 4 ^ 18 / 1.63 := by
    rw [le_div_iff₀' (by norm_num)]
    exact baseLambda_mul_lt.le
  rw [← Corollary26.gamma_eq]
  calc lhs10 (21 * m) m (gammaOf 21 (1 / 9))
      ≤ Real.sqrt (21 * (m : ℝ) + 1) * baseLambda ^ m := Corollary26.lhs10_le (by omega)
    _ ≤ Real.sqrt (21 * (m : ℝ) + 1) * ((4 : ℝ) ^ 18 / 1.63) ^ m := by gcongr
    _ = (4 : ℝ) ^ 18 * Real.sqrt (21 * (m : ℝ) + 1) / 1.63 ^ m * (4 : ℝ) ^ (18 * (m - 1)) := by
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        rw [Nat.add_sub_cancel, div_pow, ← pow_mul]
        field_simp
        ring
    _ ≤ 1 * (4 : ℝ) ^ (18 * (m - 1)) := by
        gcongr
        exact (div_le_one (by positivity)).2 (Corollary26.threshold hm)
    _ ≤ (N : ℝ) := by
        rw [one_mul]
        exact_mod_cast hN

/-! ### Conclusion -/

/-- The range of the step "Conclusion": "m ≥ 60", and "N ≥ 4^{18(m-1)}". -/
structure Sizes.Large26 (p : Sizes) : Prop where
  m_ge : 60 ≤ p.m
  N_ge : 4 ^ (18 * (p.m - 1)) ≤ p.N

/-- Inequality (10) holds in this range (`eq_10_corollary_26`). -/
theorem Sizes.Large26.lhs10_le {p : Sizes} (h : p.Large26) :
    lhs10 (21 * p.m) p.m (gammaOf 21 (1 / 9)) ≤ p.N := by
  rw [Corollary26.gamma_eq]
  exact eq_10_corollary_26 p.m p.N h.m_ge h.N_ge

/-- Proof of Corollary 26, "Conclusion": "For m ≥ 60, Theorem 30 thus applies": its hypothesis
`N ≥ √K N₀` holds. -/
theorem Corollary26.tile_fits {p : Sizes} (h : p.Large26) : sqrtKN0 (21 * p.m) p.m ≤ p.N :=
  Equation10.tile_fits (by omega) (by linarith [Corollary26.gamma_digits.1]) h.lhs10_le

/-- Proof of Corollary 26, "Conclusion": "The preprocessing takes O(m² N²/D^γ) time and space". -/
theorem Corollary26.preprocessing :
    Dominated Sizes.Large26 (fun p => cost8 (21 * p.m) p.m (switchOf (1 / 9) p.m) p.N)
      fun p => (p.m : ℝ) ^ 2 * (D p.m : ℝ) ^ (-gammaOf 21 (1 / 9)) * (p.N : ℝ) ^ 2 :=
  dominated_cost8_of_eq_10 (Lof := fun m => 21 * m) Corollary26.first_term (fun _ _ => trivial)
    (fun p hp => le_mul_of_one_le_left (by positivity)
      (one_le_pow₀ (Nat.one_le_cast.2 (le_trans (by norm_num) hp.m_ge))))
    fun _ hp => hp.lhs10_le

/-- Proof of Corollary 26, "Conclusion": "Since m = O(log D) and the exponents γ - 0.063 and 0.437 -
q are positive, we have m² = O(D^{γ-0.063}) and m = O(D^{0.437-q})". In general, `m^e D^a = O(D^b)`
for `D = 4^m` and `a < b`. -/
theorem dominated_pow_mul_D_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    Dominated (fun _ : ℕ => True) (fun m => (m : ℝ) ^ e * (D m : ℝ) ^ a)
      fun m => (D m : ℝ) ^ b := by
  refine ((dominated_rpow_mul_log_pow_rpow hab e).comp (fun m : ℕ => (D m : ℝ))
    fun m (_ : True) => one_le_cast_D m).mono_left fun m _ => ?_
  have hm := cast_le_log_cast_D m
  rw [mul_comm]
  gcongr

/-- Proof of Corollary 26, "Conclusion", with `D = 4^m`: "which gives the bounds O(N²/D^{0.063}) and
O(D^{0.437}) of the corollary". -/
theorem Corollary26.conclusion :
    Dominated Sizes.Large26 (fun p => cost8 (21 * p.m) p.m (switchOf (1 / 9) p.m) p.N)
        (fun p => (D p.m : ℝ) ^ (-0.063 : ℝ) * (p.N : ℝ) ^ 2) ∧
      Dominated (fun _ : ℕ => True) (fun m => costQuery (21 * m) m (switchOf (1 / 9) m))
        fun m => (D m : ℝ) ^ (0.437 : ℝ) := by
  -- "the exponents γ - 0.063 and 0.437 - q are positive"
  have hγ : -gammaOf 21 (1 / 9) < -0.063 := by linarith [Corollary26.gamma_digits.1]
  have hq : qOf (1 / 9) < 0.437 := by linarith [Corollary26.q_digits.2]
  exact ⟨Corollary26.preprocessing.trans
      (((dominated_pow_mul_D_rpow hγ 2).comp Sizes.m fun _ _ => trivial).mul_right
        fun _ _ => sq_nonneg _),
    Corollary26.query_cost.trans (by simpa only [pow_one] using dominated_pow_mul_D_rpow hq 1)⟩

/-- The instances of Corollary 26 from the threshold on: `N ≥ D^{18}` and `m = ⌈log_4 D⌉ ≥ 60`. -/
structure Sizes.Corollary26 (p : Sizes) : Prop where
  N_ge : p.D₀ ^ 18 ≤ p.N
  m_eq : p.m = ⌈Real.logb 4 (p.D₀ : ℝ)⌉₊
  m_ge : 60 ≤ p.m

/-- `D ≥ 2`, since `m = 0` for `D ≤ 1`. -/
theorem Sizes.Corollary26.setUp {p : Sizes} (h : p.Corollary26) : p.SetUp := by
  obtain ⟨-, hm, hm60⟩ := h
  refine ⟨?_, hm⟩
  by_contra hlt
  obtain h0 | h1 : p.D₀ = 0 ∨ p.D₀ = 1 := by omega
  · simp only [h0, Nat.cast_zero, Real.logb_zero, Nat.ceil_zero] at hm
    omega
  · simp only [h1, Nat.cast_one, Real.logb_one, Nat.ceil_zero] at hm
    omega

/-- After "Setting up", these instances are in the range of the step "Conclusion". -/
theorem Sizes.Corollary26.large {p : Sizes} (h : p.Corollary26) : p.Large26 :=
  ⟨h.m_ge, Corollary26.hypothesis h.setUp.gt h.N_ge⟩

/-- Corollary 26, the costs of Theorem 30 at "L := 21m and t := ⌈m/9⌉", in terms of the given `D`:
there is a constant `C` such that for all `N ≥ D^{18}` with `m = ⌈log_4 D⌉ ≥ 60` the hypothesis
`N ≥ √K N₀` of Theorem 30 holds, the expression (8) is at most `C N²/D^{0.063}`, and the query cost
is at most `C D^{0.437}`. -/
theorem Corollary26.costs :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D₀ N m : ℕ, D₀ ^ 18 ≤ N → m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → 60 ≤ m →
      sqrtKN0 (21 * m) m ≤ N ∧
      cost8 (21 * m) m (switchOf (1 / 9) m) N ≤ C * ((N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ)) ∧
      costQuery (21 * m) m (switchOf (1 / 9) m) ≤ C * (D₀ : ℝ) ^ (0.437 : ℝ) := by
  -- the padding "changes D by a factor less than 4, which only affects the constants"
  have hpad : ∀ a : ℝ, Dominated Sizes.Corollary26 (fun p => (D p.m : ℝ) ^ a)
      fun p => (p.D₀ : ℝ) ^ a := fun a => by
    simpa only [pow_zero, mul_one] using (padded_le a 0).mono_dom fun _ hp => hp.setUp
  have hpre := ((Corollary26.conclusion.1.mono_dom fun _ hp => hp.large).trans
    ((hpad (-0.063)).mul_right fun _ _ => sq_nonneg _)).congr (fun _ _ => rfl)
      fun p _ => show (p.D₀ : ℝ) ^ (-0.063 : ℝ) * (p.N : ℝ) ^ 2
          = (p.N : ℝ) ^ 2 / (p.D₀ : ℝ) ^ (0.063 : ℝ) by
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        ring
  have hquery := (Corollary26.conclusion.2.comp Sizes.m fun _ _ => trivial).trans (hpad 0.437)
  obtain ⟨C, hC, hboth⟩ := hpre.exists_const_and hquery (fun _ _ => by positivity)
    fun _ _ => by positivity
  exact ⟨C, hC, fun D₀ N m hN hm hm60 =>
    have hp : Sizes.Corollary26 ⟨D₀, N, m⟩ := ⟨hN, hm, hm60⟩
    ⟨Corollary26.tile_fits hp.large, hboth _ hp⟩⟩

/-- Corollary 26: `|W| D^{0.437} + N²/D^{0.063}` "is O(N²/D^{0.063}) whenever |W| ≤ N²/√D"
(with constant 2).

NOTE.  The paper states no lower bound on `D`; `D ≥ 1` is assumed, as in `Items.Corollary_26`. -/
theorem corollary_26_W (N D₀ W : ℕ) (hD : 1 ≤ D₀)
    (hW : (W : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt (D₀ : ℝ)) :
    (W : ℝ) * (D₀ : ℝ) ^ (0.437 : ℝ) + (N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ)
      ≤ 2 * ((N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ)) := by
  have hD0 : (0 : ℝ) < (D₀ : ℝ) := by exact_mod_cast hD
  have hpowq : 0 < (D₀ : ℝ) ^ (0.437 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hpowγ : 0 < (D₀ : ℝ) ^ (0.063 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hsqrt : 0 < Real.sqrt (D₀ : ℝ) := Real.sqrt_pos.mpr hD0
  -- `D^{0.437} D^{0.063} = √D`.
  have hprod : (D₀ : ℝ) ^ (0.437 : ℝ) * (D₀ : ℝ) ^ (0.063 : ℝ) = Real.sqrt (D₀ : ℝ) := by
    rw [← Real.rpow_add hD0, Real.sqrt_eq_rpow]
    norm_num
  have hqueries : (W : ℝ) * (D₀ : ℝ) ^ (0.437 : ℝ) ≤ (N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ) := by
    calc (W : ℝ) * (D₀ : ℝ) ^ (0.437 : ℝ)
        ≤ (N : ℝ) ^ 2 / Real.sqrt (D₀ : ℝ) * (D₀ : ℝ) ^ (0.437 : ℝ) := by gcongr
      _ = (N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ) := by
          rw [← hprod]
          field_simp
  linarith

/-! ### The parameters `c = 21` and `θ = 1/9` of Corollary 31 and Table 2

The sentence before Corollary 26 says: "It is the entry c = 21, q = 0.43 of Table 2". The parameters
of the proof above are those of Corollary 31 at `c = 21`, `θ = 1/9`: this holds for `L`
(`levelsOf_21`), for `γ` and `q` (`Corollary26.gamma_eq` and `Corollary26.q_eq` above), and for `Λ`
(`baseLambda_eq_exp_lnΛ`). The condition `ε < R_c(γ)` holds at `ε = 1/18` (`Corollary26.Rc_digits`),
and `N ≥ D^18` gives the condition `D ≤ N^{0.056}` of the row `c = 21` of the table, which is
`table_2_c21` (`Corollary26.row_condition`). Nothing else rests on this section. -/

/-- "L := 21m" is the `L = ⌈cm⌉` of Corollary 31 at `c = 21`. -/
theorem levelsOf_21 (m : ℕ) : levelsOf 21 m = 21 * m := by
  unfold levelsOf
  rw [show (21 : ℝ) * (m : ℝ) = ((21 * m : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]

/-- Section 4.4: the `Λ` of (11), whose logarithm is `lnΛ c γ`, is "the general form of the base Λ
above". At `c = 21` and `θ = 1/9` it is the `Λ` of the proof of Corollary 26. -/
theorem baseLambda_eq_exp_lnΛ : baseLambda = Real.exp (lnΛ 21 (gammaOf 21 (1 / 9))) := by
  have hfour := log_four_pos.ne'
  -- `21 H(1/21) = ln(21^21/20^20)`
  have hH : 21 * entropy (1 / 21) = Real.log ((21 : ℝ) ^ 21 / 20 ^ 20) := by
    rw [entropy, show (1 : ℝ) - 1 / 21 = 20 / 21 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_one]
    push_cast
    ring
  have hlog : Real.log baseLambda = 21 * Real.log 10 + 1 / 9 * Real.log (20 / 9)
      - (1 / 2 * Real.log ((21 : ℝ) ^ 21 / 20 ^ 20) + 20 * Real.log 3) := by
    rw [baseLambda, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_rpow (by norm_num), Real.log_sqrt (by positivity)]
    push_cast
    ring
  rw [← Real.exp_log (show 0 < baseLambda by unfold baseLambda; positivity), hlog, ← hH, lnΛ,
    Corollary26.gamma_eq]
  congr 1
  field_simp
  ring

/-- At `c = 21` and `θ = 1/9` the number `R_c(γ)` lies between 0.0566 and 0.0567, so the condition
`ε < R_c(γ)` of Corollary 31 holds at `ε = 1/18`. -/
theorem Corollary26.Rc_digits :
    0.0566 < Rc 21 (gammaOf 21 (1 / 9)) ∧ Rc 21 (gammaOf 21 (1 / 9)) < 0.0567 ∧
      1 / 18 < Rc 21 (gammaOf 21 (1 / 9)) := by
  obtain ⟨hγlo, hγhi⟩ := Corollary26.gamma_digits
  have hlow : 0.0566 < Rc 21 (gammaOf 21 (1 / 9)) :=
    (lt_Rc_of_lnΛ_zero_mem (Γ := 0.0641) lnΛ_21_zero_mem) _ (by linarith) hγhi.le
  have hupp : Rc 21 (gammaOf 21 (1 / 9)) < 0.0567 :=
    (Rc_lt_of_lnΛ_zero_mem (γlo := 0.0640) lnΛ_21_zero_mem) _ hγlo.le
  exact ⟨hlow, hupp, lt_trans (by norm_num) hlow⟩

/-- Table 2: "every entry of the row holds whenever D ≤ N^ε", and the row `c = 21` has `ε = 0.056`.
Under the hypothesis `N ≥ D^{18}` of Corollary 26 this condition holds: `D ≤ N^{1/18}`, and
`1/18 < 0.056`. -/
theorem Corollary26.row_condition (N D₀ : ℕ) (hD : 1 ≤ D₀) (hN : D₀ ^ 18 ≤ N) :
    (D₀ : ℝ) ≤ (N : ℝ) ^ (1 / 18 : ℝ) ∧ (D₀ : ℝ) ≤ (N : ℝ) ^ (0.056 : ℝ) := by
  have hD0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : 1 ≤ N := (Nat.one_le_pow _ _ hD).trans hN
    exact_mod_cast this
  have hN' : (D₀ : ℝ) ^ 18 ≤ (N : ℝ) := by exact_mod_cast hN
  have h18 : (D₀ : ℝ) ≤ (N : ℝ) ^ (1 / 18 : ℝ) := by
    calc (D₀ : ℝ) = ((D₀ : ℝ) ^ 18) ^ (1 / 18 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hD0]
          norm_num
      _ ≤ (N : ℝ) ^ (1 / 18 : ℝ) := Real.rpow_le_rpow (by positivity) hN' (by norm_num)
  exact ⟨h18, h18.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))⟩

end ThreeSumApsp
