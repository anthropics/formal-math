/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.ParameterSteps

/-!
# Corollary 31: the costs of Theorem 30 as powers of `D`

"We repeat the proof of Corollary 26 with L := ⌈cm⌉ and t := ⌈θm⌉". Here `L` is `levelsOf c m` and
`t` is `switchOf θ m`, for constants `c > 10` and `0 < θ < 0.9`; the inner dimension satisfies
`2 ≤ D ≤ N^ε` with `ε < R_c(γ)`, and `m = ⌈log_4 D⌉`. The main result is `Corollary31.costs`: for
all `m` from some `m₀` on, the preprocessing cost (8) of Theorem 30 (`cost8`, the sum of a first
term for the boxes and a last term for the encodings) is `O(N² log² D / D^γ)`, and its query cost
`L ∑_{d ≤ t} α_d` (`costQuery`) is `O(D^q log D)`. What the paper says of the finitely many smaller
`m` is `Corollary31.small_m`; nothing else rests on that lemma.

The steps are those of the proof of Corollary 26. What does not depend on `c` and `θ` is proved
before, for both corollaries; the rest is what the paper says of each step.

* Setting up. As for Corollary 26, the inner dimension is padded to `D = 4^m`
  (`Corollary26.setting_up`, `Corollary26.padding`); this changes the bounds by a constant factor
  (`padded_le`). The hypothesis reads `N ≥ 4^{(m-1)/ε}` (`Corollary31.hypothesis`).
* Boxes. `ρ < ρ_c` and `ρ^t ≤ D^{-γ}` (`Corollary31.rho_lt`, `Corollary31.rho_pow_le`), which bounds
  the first term of (8) (`Corollary31.first_term`).
* Queries. The calculation of Corollary 26, `∑_{d ≤ t} α_d ≤ (9x)^t (1 + 1/x)^m` (`sum_alpha_le`),
  with `x = (1-θ)/θ` in place of 8 gives `O(D^q)` (`Corollary31.sum_alpha`) and so
  `Corollary31.query_cost`.
* Encodings. As for Corollary 26, inequality (10) (`eq_10`) bounds the last term of (8)
  (`Equation10.last_term`) and gives the hypothesis `N ≥ √K N₀` of Theorem 30
  (`Equation10.tile_fits`). Its left-hand side is `O(√m · Λ^m)` (`Corollary31.lhs10_le`), and the
  base `Λ` is smaller than the base `4^{1/ε}` (`eq_11_iff`). This `Λ` is the general form of the `Λ`
  of Corollary 26 (`exp_lnΛ`, `baseLambda_eq_exp_lnΛ`).

The last sentence of the corollary, on `R_c(0)`, is `sec4_Rc_strictAntiOn` and
`sec4_Rc_zero_tendsto`. Bounds "up to a constant" are written with `Dominated`, in the one parameter
`m` or in the record `Sizes` of the given `D`, of `N` and of `m`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/

/-- The hypotheses of Corollary 31 on its parameters: "Let c > 10 and 0 < θ < 0.9", and "ε <
R_c(γ)". -/
structure Admissible (c θ ε : ℝ) : Prop where
  c_gt : 10 < c
  θ_pos : 0 < θ
  θ_lt : θ < 0.9
  thin : ε < Rc c (gammaOf c θ)

/-- The exponent `γ` of admissible parameters is positive. -/
theorem Admissible.gamma_pos {c θ ε : ℝ} (h : Admissible c θ ε) : 0 < gammaOf c θ :=
  corollary_31_gamma_pos c θ h.c_gt h.θ_pos

/-- With "L := ⌈cm⌉" (proof of Corollary 31) the hypothesis `L ≥ 10m` of Theorem 30 holds. -/
theorem ten_mul_le_levelsOf {c : ℝ} (hc : 10 < c) (m : ℕ) : 10 * m ≤ levelsOf c m := by
  have h : ((10 * m : ℕ) : ℝ) ≤ c * m := by
    push_cast
    exact mul_le_mul_of_nonneg_right hc.le (Nat.cast_nonneg m)
  exact_mod_cast h.trans (Nat.le_ceil _)

/-- `L = ⌈cm⌉ ≤ (c + 1) m` for `m ≥ 1`. -/
private lemma levelsOf_le {c : ℝ} (hc : 10 < c) {m : ℕ} (hm : 1 ≤ m) :
    (levelsOf c m : ℝ) ≤ (c + 1) * m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL : (levelsOf c m : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  linarith

/-- `m = O(log D)` for `D = 4^m`. -/
private lemma dominated_cast_log_D :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => (m : ℝ)) fun m => Real.log (D m) :=
  .of_le fun m _ => cast_le_log_cast_D m

/-- `L = ⌈cm⌉ = O(log D)` for `D = 4^m`. -/
private lemma dominated_levelsOf_log_D {c : ℝ} (hc : 10 < c) :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => (levelsOf c m : ℝ)) fun m => Real.log (D m) :=
  (Dominated.of_le_const_mul (C := c + 1) (by linarith) fun _ hm => levelsOf_le hc hm).trans
    dominated_cast_log_D

/-- Proof of Corollary 31: "After the padding, the assumption D ≤ N^ε now reads N ≥ 4^{(m-1)/ε}",
because `4^{m-1} < D ≤ N^ε` for the original `D`. -/
theorem Corollary31.hypothesis {m D₀ N : ℕ} {ε : ℝ} (hm : 1 ≤ m) (hε : 0 < ε)
    (hgt : 4 ^ (m - 1) < D₀) (hthin : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) :
    (4 : ℝ) ^ (((m : ℝ) - 1) / ε) ≤ (N : ℝ) := by
  have hle : (4 : ℝ) ^ ((m : ℝ) - 1) ≤ (N : ℝ) ^ ε := by
    rw [← Nat.cast_one, ← Nat.cast_sub hm, Real.rpow_natCast]
    exact le_trans (by exact_mod_cast hgt.le) hthin
  calc (4 : ℝ) ^ (((m : ℝ) - 1) / ε) = ((4 : ℝ) ^ ((m : ℝ) - 1)) ^ (1 / ε) := by
        rw [← Real.rpow_mul (by norm_num), mul_one_div]
    _ ≤ ((N : ℝ) ^ ε) ^ (1 / ε) := Real.rpow_le_rpow (by positivity) hle (by positivity)
    _ = (N : ℝ) := by
        rw [← Real.rpow_mul N.cast_nonneg, mul_one_div_cancel hε.ne', Real.rpow_one]

/-! ### Boxes -/

/-- Proof of Corollary 31: "ρ < ρ_c", where `ρ = 9m/(L-m+1)` and `L = ⌈cm⌉ ≥ cm`. -/
theorem Corollary31.rho_lt {c : ℝ} (hc : 10 < c) (m : ℕ) : rho (levelsOf c m) m < rhoC c := by
  have hL : c * m ≤ levelsOf c m := Nat.le_ceil _
  have hm : (m : ℝ) ≤ c * m := le_mul_of_one_le_left (Nat.cast_nonneg m) (by linarith)
  unfold rho rhoC
  -- after clearing denominators: `9m (c - 1) < 9 (L - m + 1)`, from `cm ≤ L`
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- Proof of Corollary 31: "ρ < ρ_c gives ρ^t ≤ ρ_c^{θm} = D^{-γ}". -/
theorem Corollary31.rho_pow_le {c : ℝ} (hc : 10 < c) (θ : ℝ) (m : ℕ) :
    rho (levelsOf c m) m ^ switchOf θ m ≤ (D m : ℝ) ^ (-gammaOf c θ) := by
  calc rho (levelsOf c m) m ^ switchOf θ m
      ≤ rhoC c ^ switchOf θ m :=
        pow_le_pow_left₀ (rho_nonneg (ten_mul_le_levelsOf hc m))
          (Corollary31.rho_lt hc m).le _
    _ = rhoC c ^ ((switchOf θ m : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ rhoC c ^ (θ * (m : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge (rhoC_pos hc) (rhoC_lt_one hc).le (Nat.le_ceil _)
    _ = (D m : ℝ) ^ (-gammaOf c θ) := rhoC_rpow_eq_D_rpow c θ hc m

/-- The step on the boxes for general `c` and `θ`: `1/(1-ρ) = O(1)` and `ρ^t ≤ D^{-γ}`, so the first
term of (8) is `O(L m D^{-γ} N²) = O(N² log² D / D^γ)`. (In the proof of Corollary 26: "Hence the
first term of (8) is O(m² N²/D^γ)".) The common factor `N²` is left out. -/
theorem Corollary31.first_term {c : ℝ} (hc : 10 < c) (θ : ℝ) :
    Dominated (fun m : ℕ => 1 ≤ m)
      (fun m => (levelsOf c m : ℝ) * m *
        (rho (levelsOf c m) m ^ switchOf θ m / (1 - rho (levelsOf c m) m)))
      fun m => (D m : ℝ) ^ (-gammaOf c θ) * Real.log (D m) ^ 2 := by
  have hgap : 0 < 1 - rhoC c := sub_pos.2 (rhoC_lt_one hc)
  have hgap_le : ∀ m, 1 - rhoC c ≤ 1 - rho (levelsOf c m) m := fun m => by
    linarith [Corollary31.rho_lt hc m]
  -- `ρ^t/(1-ρ) = O(D^{-γ})`
  have hboxes : Dominated (fun m : ℕ => 1 ≤ m)
      (fun m => rho (levelsOf c m) m ^ switchOf θ m / (1 - rho (levelsOf c m) m))
      fun m => (D m : ℝ) ^ (-gammaOf c θ) :=
    .of_le_const_mul (C := 1 / (1 - rhoC c)) (by positivity) fun m _ => by
      rw [one_div_mul_eq_div]
      exact div_le_div₀ (by positivity) (Corollary31.rho_pow_le hc θ m) hgap (hgap_le m)
  -- `L m = O(log² D)`
  have hLm := (dominated_levelsOf_log_D hc).mul dominated_cast_log_D
    (fun _ _ => by positivity) (fun _ _ => by positivity)
  exact (hLm.mul hboxes (fun _ _ => by positivity)
    fun m _ => rho_pow_div_nonneg _ (ten_mul_le_levelsOf hc m)).congr (fun _ _ => rfl)
      fun m _ => by ring

/-! ### Queries -/

/-- Proof of Corollary 31: "the same calculation with x := (1-θ)/θ in place of 8, where 9x > 1
because θ < 0.9, gives ∑_{d≤t} α_d ≤ (9x)^t (1+1/x)^m = O(D^q)". The constant is `9x`, because
`t = ⌈θm⌉ < θm + 1`. -/
theorem Corollary31.sum_alpha {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 0.9) :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => ∑ d ∈ range (switchOf θ m + 1), (alpha m d : ℝ))
      fun m => (D m : ℝ) ^ qOf θ := by
  have hx : 0 < (1 - θ) / θ := div_pos (by linarith) hθ0
  have h9x : 1 < 9 * ((1 - θ) / θ) := by
    rw [← mul_div_assoc, lt_div_iff₀ hθ0]
    linarith
  refine .of_le_const_mul (C := 9 * ((1 - θ) / θ)) (by positivity) fun m _ => ?_
  have ht : ((switchOf θ m : ℕ) : ℝ) ≤ θ * m + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  calc ∑ d ∈ range (switchOf θ m + 1), (alpha m d : ℝ)
      ≤ (9 * ((1 - θ) / θ)) ^ switchOf θ m * (1 + 1 / ((1 - θ) / θ)) ^ m :=
        sum_alpha_le hx h9x.le (switchOf_le (by linarith) m)
    _ ≤ (9 * ((1 - θ) / θ)) ^ (θ * (m : ℝ) + 1) * (1 + 1 / ((1 - θ) / θ)) ^ m := by
        gcongr
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le h9x.le ht
    _ = 9 * ((1 - θ) / θ) * (D m : ℝ) ^ qOf θ := by
        rw [← rpow_mul_pow_eq_D_rpow_qOf hθ0 (by linarith) m, Real.rpow_add (by positivity),
          Real.rpow_one]
        ring

/-- The query cost `L ∑_{d ≤ t} α_d` of Theorem 30 is `O(L D^q) = O(D^q log D)`, for `D = 4^m`. (In
the proof of Corollary 26: "Hence a query takes O(L D^q) = O(m D^q) time".) -/
theorem Corollary31.query_cost {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => costQuery (levelsOf c m) m (switchOf θ m))
      fun m => (D m : ℝ) ^ qOf θ * Real.log (D m) :=
  ((dominated_levelsOf_log_D hc).mul (Corollary31.sum_alpha hθ0 hθ1) (fun _ _ => by positivity)
    fun _ _ => by positivity).congr (fun _ _ => rfl) fun m _ => by ring

/-! ### Encodings

As in the proof of Corollary 26, `m`-th powers are compared by comparing their bases. The paper's
sentences are one lemma each: the bound on the binomial coefficient (`Corollary31.le_K`, for which
`Corollary31.mul_entropy_monotoneOn` passes from `L` to `cm`), the bound `O(√m · Λ^m)` on the
left-hand side (`Corollary31.lhs10_le`), where `Λ` is `Real.exp (lnΛ c γ)` (`exp_lnΛ`), and
`Λ < 4^{1/ε}` (`eq_11_iff`); `eq_10` puts them together with `Corollary31.hypothesis`. Throughout,
`L = ⌈cm⌉`, and `D₀` is the inner dimension before padding. -/

/-- The function `x ↦ x H(m/x)` is increasing on `x ≥ m ≥ 1`. The entropy function is concave with
`H(0) = 0`, and `m/y` is the point `(x/y) (m/x) + (1 - x/y) 0`. -/
theorem Corollary31.mul_entropy_monotoneOn {m : ℕ} (hm : 1 ≤ m) :
    MonotoneOn (fun x : ℝ => x * entropy ((m : ℝ) / x)) (Set.Ici (m : ℝ)) := by
  intro x hx y _ hxy
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : 0 < x := hm0.trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hmem : (m : ℝ) / x ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, div_le_one_of_le₀ hx hx0.le⟩
  have hconc := entropy_concaveOn.2 hmem ⟨le_rfl, zero_le_one⟩ (by positivity : 0 ≤ x / y)
    (sub_nonneg.2 ((div_le_one hy0).2 hxy)) (by ring)
  simp only [smul_eq_mul, entropy_zero, mul_zero, add_zero] at hconc
  rw [show x / y * ((m : ℝ) / x) = (m : ℝ) / y by field_simp] at hconc
  calc x * entropy ((m : ℝ) / x) = y * (x / y * entropy ((m : ℝ) / x)) := by field_simp
    _ ≤ y * entropy ((m : ℝ) / y) := mul_le_mul_of_nonneg_left hconc hy0.le

/-- Proof of Corollary 31: the bound on the binomial coefficient (`exp_entropy_div_le_choose`), for
`K = binom(L, m)`. It gives `K ≥ e^{L H(m/L)}/(L+1) ≥ e^{cm H(1/c)}/(cm+2)`, as `cm ≤ L < cm + 1`
and `x ↦ x H(m/x)` is increasing. -/
theorem Corollary31.le_K {c : ℝ} (hc : 10 < c) {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (c * m * entropy (1 / c)) / (c * m + 2) ≤ (K (levelsOf c m) m : ℝ) := by
  set L : ℕ := levelsOf c m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcm : (m : ℝ) ≤ c * m := le_mul_of_one_le_left (Nat.cast_nonneg m) (by linarith)
  have hcL : c * m ≤ L := Nat.le_ceil _
  have hLc : (L : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmL : m ≤ L := by exact_mod_cast hcm.trans hcL
  calc Real.exp (c * m * entropy (1 / c)) / (c * m + 2)
      = Real.exp (c * m * entropy (m / (c * m))) / (c * m + 2) := by
        rw [show (m : ℝ) / (c * m) = 1 / c by field_simp]
    _ ≤ Real.exp (L * entropy (m / L)) / (L + 1) :=
        div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.2
          (mul_entropy_monotoneOn hm (Set.mem_Ici.2 hcm) (Set.mem_Ici.2 (hcm.trans hcL)) hcL))
          (by positivity) (by linarith)
    _ ≤ (K L m : ℝ) := exp_entropy_div_le_choose m L hmL

/-- The bound on `K`, under the square root: `√K ≥ (e^{(1/2) c H(1/c)})^m / (√(c+2) √m)`. -/
private lemma le_sqrt_K {c : ℝ} (hc : 10 < c) {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (1 / 2 * c * entropy (1 / c)) ^ m / (Real.sqrt (c + 2) * Real.sqrt m)
      ≤ Real.sqrt (K (levelsOf c m) m) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine Real.le_sqrt_of_sq_le ?_
  calc (Real.exp (1 / 2 * c * entropy (1 / c)) ^ m / (Real.sqrt (c + 2) * Real.sqrt m)) ^ 2
      = Real.exp (c * m * entropy (1 / c)) / ((c + 2) * m) := by
        rw [div_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith), ← pow_mul,
          ← Real.exp_nat_mul]
        congr 2
        push_cast
        ring
    _ ≤ Real.exp (c * m * entropy (1 / c)) / (c * m + 2) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) (by linarith)
    _ ≤ (K (levelsOf c m) m : ℝ) := Corollary31.le_K hc hm

/-- `10^L / N₀ = (10/3)^L 3^m ≤ (10/3) (10^c 3^{-(c-1)})^m`, as `N₀ = 3^{L-m}` and `L < cm + 1`. -/
private lemma ten_pow_div_N0_le {c : ℝ} (hc : 10 < c) (m : ℕ) :
    (10 : ℝ) ^ levelsOf c m / (N0 (levelsOf c m) m : ℝ)
      ≤ 10 / 3 * ((10 : ℝ) ^ c * (3 : ℝ) ^ (-(c - 1))) ^ m := by
  set L : ℕ := levelsOf c m
  have hmL : m ≤ L := by have := ten_mul_le_levelsOf hc m; omega
  have hLc : (L : ℝ) ≤ c * m + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hbase : (10 : ℝ) ^ c * (3 : ℝ) ^ (-(c - 1)) = (10 / 3 : ℝ) ^ c * 3 := by
    rw [Real.div_rpow (by norm_num) (by norm_num), neg_sub, Real.rpow_sub (by norm_num),
      Real.rpow_one]
    ring
  calc (10 : ℝ) ^ L / (N0 L m : ℝ) = (10 / 3 : ℝ) ^ L * 3 ^ m := by
        rw [N0]
        push_cast
        rw [div_pow, pow_sub₀ _ (by norm_num) hmL]
        field_simp
    _ = (10 / 3 : ℝ) ^ (L : ℝ) * 3 ^ m := by rw [Real.rpow_natCast]
    _ ≤ (10 / 3 : ℝ) ^ (c * m + 1) * 3 ^ m := by
        gcongr
        norm_num
    _ = 10 / 3 * ((10 : ℝ) ^ c * (3 : ℝ) ^ (-(c - 1))) ^ m := by
        rw [hbase, mul_pow, Real.rpow_add (by norm_num), Real.rpow_one,
          Real.rpow_mul (by norm_num), Real.rpow_natCast]
        ring

/-- `Real.exp (lnΛ c γ)` is the `Λ` of Section 4.4: "Λ := 10^c e^{-(1/2) c H(1/c)} 3^{-(c-1)} 4^γ".
-/
theorem exp_lnΛ (c γ : ℝ) :
    Real.exp (lnΛ c γ)
      = (10 : ℝ) ^ c * Real.exp (-(1 / 2 * c * entropy (1 / c))) * (3 : ℝ) ^ (-(c - 1))
        * (4 : ℝ) ^ γ := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, lnΛ]
  congr 1
  ring

/-- Proof of Corollary 31: "the left-hand side of (10) is O(√m · Λ^m)", for `m ≥ 1`, with
`L = ⌈cm⌉`, `Λ = Real.exp (lnΛ c γ)` and any real `γ`. -/
theorem Corollary31.lhs10_le {c : ℝ} (hc : 10 < c) (γ : ℝ) :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => lhs10 (levelsOf c m) m γ)
      fun m => Real.sqrt m * Real.exp (lnΛ c γ) ^ m := by
  refine .of_le_const_mul (C := 10 / 3 * Real.sqrt (c + 2)) (by positivity) fun m hm => ?_
  have hD : (D m : ℝ) ^ γ = ((4 : ℝ) ^ γ) ^ m := by
    rw [cast_D_eq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  have hc2 : 0 < Real.sqrt (c + 2) := Real.sqrt_pos.2 (by linarith)
  have hroot : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
  calc lhs10 (levelsOf c m) m γ
      = ((4 : ℝ) ^ γ) ^ m * ((10 : ℝ) ^ levelsOf c m / (N0 (levelsOf c m) m : ℝ))
        / Real.sqrt (K (levelsOf c m) m) := by
        rw [lhs10, sqrtKN0, hD]
        ring
    _ ≤ ((4 : ℝ) ^ γ) ^ m * (10 / 3 * ((10 : ℝ) ^ c * (3 : ℝ) ^ (-(c - 1))) ^ m)
        / (Real.exp (1 / 2 * c * entropy (1 / c)) ^ m / (Real.sqrt (c + 2) * Real.sqrt m)) := by
        gcongr
        · exact ten_pow_div_N0_le hc m
        · exact le_sqrt_K hc hm
    _ = 10 / 3 * Real.sqrt (c + 2) * (Real.sqrt m * Real.exp (lnΛ c γ) ^ m) := by
        rw [exp_lnΛ, Real.exp_neg, mul_pow, mul_pow, mul_pow, mul_pow, inv_pow]
        field_simp

/-- A power `r^m` with `r > 1` exceeds `A √m` "once m exceeds a constant". -/
private lemma exists_mul_sqrt_le_pow {A r : ℝ} (hA : 0 ≤ A) (hr : 1 < r) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → A * Real.sqrt m ≤ r ^ m := by
  -- `A m / r^m` tends to 0
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt 1 hr).const_mul A
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1
    (hlim.eventually_le_const (by norm_num : A * 0 < 1))
  refine ⟨m₀, fun m hm => ?_⟩
  have hpow : 0 < r ^ m := by positivity
  have hsqrt : Real.sqrt m ≤ m := Real.sqrt_le_self_iff.2 <| by
    rcases m.eq_zero_or_pos with rfl | hpos
    · exact .inl Nat.cast_zero
    · exact .inr (by exact_mod_cast hpos)
  calc A * Real.sqrt m ≤ A * m := mul_le_mul_of_nonneg_left hsqrt hA
    _ = A * ((m : ℝ) ^ 1 / r ^ m) * r ^ m := by field_simp
    _ ≤ 1 * r ^ m := mul_le_mul_of_nonneg_right (hm₀ m hm) hpow.le
    _ = r ^ m := one_mul _

/-- `4^{m-1} < D₀ ≤ N^ε` is possible only for `ε > 0`, because `D₀ ≥ 2`. -/
private lemma pos_of_le_rpow {m D₀ N : ℕ} {ε : ℝ} (hgt : 4 ^ (m - 1) < D₀)
    (hthin : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) : 0 < ε := by
  have hD : (2 : ℝ) ≤ D₀ := by
    have : 1 ≤ 4 ^ (m - 1) := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast (by omega : 2 ≤ D₀)
  have hN : 0 < N := by
    by_contra h0
    obtain rfl : N = 0 := by omega
    rw [Nat.cast_zero] at hthin
    linarith [Real.zero_rpow_le_one ε]
  refine lt_of_not_ge fun hε => ?_
  linarith [Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 hN) hε]

/-- Equation (10), `D^γ · 10^L / (√K N₀) ≤ N`, with the parameters of Corollary 31, whose proof
says: "the inequality (10) thus holds once m exceeds a constant depending on c, θ, and ε". Here `D₀`
is the original inner dimension, `m = ⌈log_4 D₀⌉` (that is, `4^{m-1} < D₀ ≤ 4^m`), the `D` of (10)
is the padded `4^m`, `L = ⌈cm⌉`, `γ = θ ln(1/ρ_c)/ln 4`, and `D₀ ≤ N^ε` with `ε < R_c(γ)`. The
threshold `m₀` depends only on `c`, `θ`, `ε`. No hypothesis `ε > 0` is needed: for `ε ≤ 0` no
natural number `N` satisfies `2 ≤ D₀ ≤ N^ε`. -/
theorem eq_10 (c θ ε : ℝ) (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9)
    (hε : ε < Rc c (gammaOf c θ)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ D₀ N : ℕ, 4 ^ (m - 1) < D₀ → D₀ ≤ D m → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
        (D m : ℝ) ^ gammaOf c θ * (10 : ℝ) ^ levelsOf c m
            / (Real.sqrt (K (levelsOf c m) m) * (N0 (levelsOf c m) m : ℝ))
          ≤ (N : ℝ) := by
  have _ := hθ1 -- the corollary's hypothesis `θ < 0.9` is not needed for (10)
  rcases le_or_gt ε 0 with hε0 | hε0
  · exact ⟨0, fun m _ D₀ N hgt _ hthin => absurd (pos_of_le_rpow hgt hthin) hε0.not_gt⟩
  set γ : ℝ := gammaOf c θ
  obtain ⟨C, hC, hlhs⟩ := Corollary31.lhs10_le hc γ
  -- "As ε < R_c(γ) says that Λ < 4^{1/ε}"
  have hΛ0 : 0 < Real.exp (lnΛ c γ) := Real.exp_pos _
  have hΛ : Real.exp (lnΛ c γ) < (4 : ℝ) ^ (1 / ε) :=
    (eq_11_iff c γ ε hc.le (corollary_31_gamma_pos c θ hc hθ0).le hε0).2 hε
  -- "once m exceeds a constant": `(4^{1/ε}/Λ)^m ≥ C 4^{1/ε} √m`
  obtain ⟨m₀, hm₀⟩ := exists_mul_sqrt_le_pow (A := C * (4 : ℝ) ^ (1 / ε)) (by positivity)
    ((one_lt_div hΛ0).2 hΛ)
  refine ⟨m₀ + 1, fun m hm D₀ N hgt _ hthin => ?_⟩
  have hpow : (4 : ℝ) ^ (((m : ℝ) - 1) / ε) = ((4 : ℝ) ^ (1 / ε)) ^ m / (4 : ℝ) ^ (1 / ε) := by
    rw [sub_div, Real.rpow_sub (by norm_num), div_eq_mul_one_div (m : ℝ) ε, mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  calc lhs10 (levelsOf c m) m γ
      ≤ C * (Real.sqrt m * Real.exp (lnΛ c γ) ^ m) := hlhs m (by omega)
    _ = C * (4 : ℝ) ^ (1 / ε) * Real.sqrt m / ((4 : ℝ) ^ (1 / ε) / Real.exp (lnΛ c γ)) ^ m
          * (4 : ℝ) ^ (((m : ℝ) - 1) / ε) := by
        rw [hpow, div_pow]
        field_simp
    _ ≤ 1 * (4 : ℝ) ^ (((m : ℝ) - 1) / ε) := by
        gcongr
        exact (div_le_one (by positivity)).2 (hm₀ m (by omega))
    _ ≤ (N : ℝ) := by
        rw [one_mul]
        exact Corollary31.hypothesis (by omega) hε0 hgt hthin

/-! ### The corollary -/

/-- The expression (8) is `O(N² log² D / D^γ)`, in the given `D`, wherever (10) holds: by the step
on the boxes and by (10) this is so for `D = 4^m`, and the padding only affects the constant. -/
private lemma dominated_cost8 {c : ℝ} (hc : 10 < c) (θ : ℝ) {dom : Sizes → Prop}
    (hset : ∀ p, dom p → p.SetUp)
    (h10 : ∀ p, dom p → lhs10 (levelsOf c p.m) p.m (gammaOf c θ) ≤ p.N) :
    Dominated dom (fun p => cost8 (levelsOf c p.m) p.m (switchOf θ p.m) p.N)
      fun p => (p.N : ℝ) ^ 2 * Real.log p.D₀ ^ 2 / (p.D₀ : ℝ) ^ gammaOf c θ := by
  have hpadded : Dominated dom (fun p => cost8 (levelsOf c p.m) p.m (switchOf θ p.m) p.N)
      fun p => (D p.m : ℝ) ^ (-gammaOf c θ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 :=
    dominated_cost8_of_eq_10 (Lof := levelsOf c) (tof := switchOf θ)
      (G := fun m => (D m : ℝ) ^ (-gammaOf c θ) * Real.log (D m) ^ 2)
      (Corollary31.first_term hc θ) (fun p hp => (hset p hp).m_pos)
      (fun p hp => le_mul_of_one_le_right (by positivity) (one_le_pow₀
        ((Nat.one_le_cast.2 (hset p hp).m_pos).trans (cast_le_log_cast_D p.m)))) h10
  refine (hpadded.trans (((padded_le (-gammaOf c θ) 2).mono_dom hset).mul_right
    fun _ _ => sq_nonneg _)).congr (fun _ _ => rfl) fun p _ => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  ring

/-- The cost of a query is `O(D^q log D)`, in the given `D`. -/
private lemma dominated_costQuery {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) :
    Dominated Sizes.SetUp (fun p => costQuery (levelsOf c p.m) p.m (switchOf θ p.m))
      fun p => (p.D₀ : ℝ) ^ qOf θ * Real.log p.D₀ :=
  ((Corollary31.query_cost hc hθ0 hθ1).comp Sizes.m fun _ hp => hp.m_pos).trans
    (by simpa only [pow_one] using padded_le (qOf θ) 1)

/-- The instances of Corollary 31 from a threshold `m₀` on: `2 ≤ D ≤ N^ε` and `m = ⌈log_4 D⌉ ≥ m₀`.
-/
structure Sizes.Corollary31 (ε : ℝ) (m₀ : ℕ) (p : Sizes) : Prop where
  setUp : p.SetUp
  thin : (p.D₀ : ℝ) ≤ (p.N : ℝ) ^ ε
  large : m₀ ≤ p.m

/-- Corollary 31, the cost bounds obtained from Theorem 30, for all large `m`. For `c > 10`,
`0 < θ < 0.9`, `ε < R_c(γ)` there are a constant `C` and a threshold `m₀`, depending only on `c`,
`θ`, `ε` ("The constants hidden in the O(·) depend on c, θ, and ε"), such that for all `2 ≤ D ≤ N^ε`
with `m = ⌈log_4 D⌉ ≥ m₀`, `L = ⌈cm⌉`, `t = ⌈θm⌉`: the hypothesis `N ≥ √K N₀` of Theorem 30 holds,
the expression (8) is at most `C N² log² D / D^γ`, and the query cost is at most `C D^q log D`, all
in terms of the original `D`. (The case `m < m₀` is `Corollary31.small_m`. No hypothesis `ε > 0` is
needed: for `ε ≤ 0` no natural number `N` satisfies `2 ≤ D₀ ≤ N^ε`.) -/
theorem Corollary31.costs {c θ ε : ℝ} (h : Admissible c θ ε) :
    ∃ (C : ℝ) (m₀ : ℕ), 0 ≤ C ∧ ∀ D₀ N m : ℕ, 2 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → m₀ ≤ m →
      sqrtKN0 (levelsOf c m) m ≤ N ∧
      cost8 (levelsOf c m) m (switchOf θ m) N
        ≤ C * ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ gammaOf c θ) ∧
      costQuery (levelsOf c m) m (switchOf θ m) ≤ C * ((D₀ : ℝ) ^ qOf θ * Real.log (D₀ : ℝ)) := by
  obtain ⟨hc, hθ0, hθ1, hε⟩ := h
  obtain ⟨m₀, heq10⟩ := eq_10 c θ ε hc hθ0 hθ1 hε
  -- (10) holds for the instances of the corollary from the threshold on
  have h10 : ∀ p : Sizes, p.Corollary31 ε m₀ →
      lhs10 (levelsOf c p.m) p.m (gammaOf c θ) ≤ p.N :=
    fun p hp => heq10 p.m hp.large p.D₀ p.N hp.setUp.gt hp.setUp.le hp.thin
  have hpre := dominated_cost8 hc θ (fun p (hp : p.Corollary31 ε m₀) => hp.setUp) h10
  have hquery := (dominated_costQuery hc hθ0 hθ1).mono_dom
    fun p (hp : p.Corollary31 ε m₀) => hp.setUp
  obtain ⟨C, hC, hboth⟩ := hpre.exists_const_and hquery
    (fun p _ => div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    fun p hp => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.log_nonneg (Nat.one_le_cast.2 (one_le_two.trans hp.setUp.two_le)))
  refine ⟨C, m₀, hC, fun D₀ N m hD hDN hm hm₀ => ?_⟩
  have hp : Sizes.Corollary31 ε m₀ ⟨D₀, N, m⟩ := ⟨⟨hD, hm⟩, hDN, hm₀⟩
  have hmL : m ≤ levelsOf c m := by have := ten_mul_le_levelsOf hc m; omega
  exact ⟨Equation10.tile_fits hmL (corollary_31_gamma_pos c θ hc hθ0).le (h10 ⟨D₀, N, m⟩ hp),
    hboth ⟨D₀, N, m⟩ hp⟩

/-- Proof of Corollary 31: "for smaller m the corollary again holds trivially": `D` is bounded, and
a query can compute an inner product. For `D₀ ≤ 4^{m₀}` the `D₀` operations of an inner product are
at most `C D₀^q log D₀`, with a constant `C` that depends only on `q` and `m₀`. -/
theorem Corollary31.small_m (q : ℝ) (hq : 0 ≤ q) (m₀ : ℕ) :
    ∃ C : ℝ, ∀ D₀ : ℕ, 2 ≤ D₀ → D₀ ≤ 4 ^ m₀ →
      (D₀ : ℝ) ≤ C * ((D₀ : ℝ) ^ q * Real.log (D₀ : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(4 : ℝ) ^ m₀ / Real.log 2, fun D₀ hD hD' => ?_⟩
  have hD2 : (2 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hpow : (1 : ℝ) ≤ (D₀ : ℝ) ^ q := Real.one_le_rpow (by linarith) hq
  have hlog : Real.log 2 ≤ Real.log (D₀ : ℝ) := Real.log_le_log (by norm_num) hD2
  have hle : (D₀ : ℝ) ≤ (4 : ℝ) ^ m₀ := by exact_mod_cast hD'
  calc (D₀ : ℝ) ≤ (4 : ℝ) ^ m₀ := hle
    _ = (4 : ℝ) ^ m₀ / Real.log 2 * (1 * Real.log 2) := by field_simp
    _ ≤ (4 : ℝ) ^ m₀ / Real.log 2 * ((D₀ : ℝ) ^ q * Real.log (D₀ : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hpow hlog hlog2.le (by linarith)) (by positivity)

end ThreeSumApsp
