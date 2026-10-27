/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
import VariableBound.Net.Tests
import VariableBound.Params.Ineq
import ClauseBound.ParityChecks.Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Step 3, «The total»: display (68)

The total U of the network of an admissible profile is twice the sum, over the pairs {a, b} of nodes
and the two kinds κ, of ⌈log C(t_(a,b,κ), μ_(a,b,κ))⌉. The file follows the text sentence by
sentence: a product of binomial
coefficients is at most the binomial coefficient of the sums (`sum_lg_choose_le`); the numbers T₀
and T₁ of tests (`tests_le`); the cost of kind 0 (`kind_zero_le`) and of kind 1 (`kind_one_le`),
both by display (59); two
roundings per pair (`sum_cw_le`, `two_mul_pairs_le`). The result is display (68) with M in place of
14n and k − 1 in place of k in its first term (`stU`), and as printed if M ≤ 14n (`stUPrinted`). The
constants 6, 28, 96 and 2g² are those of the text.
That U is twice the sum over the pairs, and the count of the tests of an object, come from
`VariableBound.Net.Tests`. Of «Setting and parameters», the bounds s̄ < 32Δ·log(2Δ) and 3m/(n̄ + 1)
< 6Δ·log(2Δ) ≤ (2Δ)³ are read from the hypothesis
`ParamIneq`; display (59), log(2Δ) ≥ 2, n̄ ≥ 1 and n̄·log(2Δ) ≤ n are taken from
`VariableBound.Params.Ineq`. -/

public section

namespace VariableBound.Net.SizeU

open Finset Groundwork AppVariables

/-! ### Admissible profiles -/

variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}

/-- μ_κ as a sum over the pairs a < b < g. -/
theorem totP_eq (g : ℕ) (D : Dat) (y κ : ℕ) : totP g D y κ = ∑ b ∈ range g, ∑ a ∈ range b, mu g D y a b κ := by
  simp only [totP, Tests.sum_map_range]

/-- What an admissible profile satisfies: Σ_a μ_(a,0) ≤ n̄ + 1, Σ_a μ_(a,1) ≤ M, and for both kinds
μ_κ ≤ (k − 1 + κ)·Σ_a μ_(a,κ) and μ_(a,b,κ) ≤ t_(a,b,κ) for a < b < g. -/
theorem adm_spec (h : admD k g n nb M D fl y = true) :
    tot g D y 0 ≤ nb + 1 ∧ tot g D y 1 ≤ M ∧ ∀ κ < 2, totP g D y κ ≤ (k - 1 + κ) * tot g D y κ ∧
      ∀ b < g, ∀ a < b, mu g D y a b κ ≤ (tst g n D a b κ).length := by
  simp only [admD, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨?_, h1, fun κ hκ => ⟨(h2 κ hκ).1, fun b hb a hab => ?_⟩⟩
  · cases fl
    · simp only [cond_false, beq_iff_eq] at h0; omega
    · simp only [cond_true, decide_eq_true_eq] at h0; omega
  · have h3 := (h2 κ hκ).2 a (hab.trans hb) b hb
    rw [if_neg (by omega)] at h3
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h3
    rcases h3 with h3 | h3
    · omega
    · exact h3

/-! ### The sentences of «The total» -/

/-- log x ≤ log z for 0 ≤ x ≤ z and z ≥ 1; x = 0 is allowed because Lean's log 0 is 0. -/
theorem lg_le_lg {x z : ℝ} (h0 : 0 ≤ x) (h : x ≤ z) (h1 : 1 ≤ z) : lg x ≤ lg z := by
  unfold lg
  rcases h0.eq_or_lt with rfl | h0
  · rw [Real.logb_zero]; exact Real.logb_nonneg (by norm_num) h1
  · exact Real.logb_le_logb_of_le (by norm_num) h0 h

/-- Step 3, «The total»: «A product of binomial coefficients is at most the binomial coefficient of
the sums, so Σ_({a,b}) log C(t_(a,b), μ_(a,b)) ≤ log C(T, μ)», where T and μ are the sums of the
t_(a,b) and of the
μ_(a,b) over the pairs a < b < g. Needs μ_(a,b) ≤ t_(a,b) for these pairs. -/
theorem sum_lg_choose_le (g : ℕ) (t μ : ℕ → ℕ → ℕ) (h : ∀ b < g, ∀ a < b, μ a b ≤ t a b) :
    ∑ b ∈ range g, ∑ a ∈ range b, lg ((t a b).choose (μ a b)) ≤
      lg ((∑ b ∈ range g, ∑ a ∈ range b, t a b).choose (∑ b ∈ range g, ∑ a ∈ range b, μ a b)) := by
  have hpos : ∀ x ∈ (range g).sigma fun b => range b, 1 ≤ (t x.2 x.1).choose (μ x.2 x.1) := fun x hx =>
    Nat.choose_pos (h x.1 (mem_range.1 (mem_sigma.1 hx).1) x.2 (mem_range.1 (mem_sigma.1 hx).2))
  rw [sum_sigma' (range g) (fun b => range b) fun b a => lg ((t a b).choose (μ a b)),
    sum_sigma' (range g) (fun b => range b) fun b a => t a b, sum_sigma' (range g) (fun b => range b) fun b a => μ a b]
  unfold lg
  rw [← Real.logb_prod _ _ fun x hx => by exact_mod_cast (Nat.pos_iff_ne_zero.1 (hpos x hx))]
  refine Real.logb_le_logb_of_le (by norm_num) (prod_pos fun x hx => by exact_mod_cast hpos x hx) ?_
  exact_mod_cast ClauseBound.ParityChecks.prod_choose_le ((range g).sigma fun b => range b) (fun x => t x.2 x.1) fun x => μ x.2 x.1

/-- I ≤ r·s̄: if n̄·|Λ_j| ≤ c for every check, then n̄·I ≤ r·c. -/
theorem nb_mul_sum_le (nb c : ℕ) (Ls : List (List ℕ)) (h : ∀ L ∈ Ls, nb * L.length ≤ c) : nb * (Ls.map List.length).sum ≤ Ls.length * c := by
  induction Ls with
  | nil => simp
  | cons L Ls ih =>
    have h1 := h L (List.mem_cons_self ..)
    have h2 := ih fun L' hL' => h L' (List.mem_cons_of_mem _ hL')
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- Step 3, «The total»: «T₀ ≤ (k − 1)m and T₁ ≤ kr·s̄», the second as T₁ ≤ kI and n̄·I ≤ r·16m,
that is I ≤ r·s̄ with s̄ = 16m/n̄. Here T_κ is the sum of the t_(a,b,κ) over the pairs a < b < g and
I the number of incidences.
Needs k ≥ 1, ψ and the checks well formed, and n̄·|Λ_j| ≤ 16m for every check. -/
theorem tests_le (g : ℕ) (hk : 1 ≤ k) (hW : WfD k n D) (hrow : ∀ L ∈ D.2, nb * L.length ≤ 16 * D.1.length) :
    ∑ b ∈ range g, ∑ a ∈ range b, (tst g n D a b 0).length ≤ (k - 1) * D.1.length ∧
      ∑ b ∈ range g, ∑ a ∈ range b, (tst g n D a b 1).length ≤ k * (D.2.map List.length).sum ∧
      nb * (D.2.map List.length).sum ≤ D.2.length * (16 * D.1.length) := by
  refine ⟨?_, ?_, nb_mul_sum_le nb _ D.2 hrow⟩
  · have h := Tests.sum_length_tst_le (g := g) hW 0
    rwa [Tests.card_kind_zero hW, Nat.add_zero] at h
  · have h := Tests.sum_length_tst_le (g := g) hW 1
    rwa [Tests.card_kind_one hW, Nat.sub_add_cancel hk] at h

/-- A formula with a clause, all of whose clauses have 1 to k literals, has k ≥ 1. -/
theorem one_le_k (hW : WfD k n D) (hm : 0 < D.1.length) : 1 ≤ k := by
  obtain ⟨h1, h2, -⟩ := hW.1 D.1 (List.mem_singleton.2 rfl) D.1[0] (List.getElem_mem hm)
  exact (List.length_pos_iff.2 h1).trans_le h2

/-- Step 3, «The total»: by display (59) with μ' = (k − 1)(n̄ + 1), kind 0 costs at most (k − 1)(n̄ + 1)·3·log(2Δ)
≤ 3(k − 1)(n + log(2Δ)) bits. Needs 2 ≤ Δ, m ≤ Δn, the n̄ of the text, T₀ ≤ (k − 1)m and μ₀ ≤ (k − 1)(n̄ + 1),
and the inequalities of «Setting and parameters». For k = 1, where μ' = 0 and display (59) does not
apply, T₀ = μ₀ = 0 and the cost is 0. -/
theorem kind_zero_le (hp : ParamIneq) {k n Δ m nb T μ : ℕ} (hΔ : 2 ≤ Δ) (hm : m ≤ Δ * n) (hnb : IsNb n Δ nb) (hT : T ≤ (k - 1) * m)
    (hμ : μ ≤ (k - 1) * (nb + 1)) :
    lg (T.choose μ) ≤ ((k - 1 : ℕ) : ℝ) * (nb + 1) * (3 * lg (2 * Δ)) ∧
      ((k - 1 : ℕ) : ℝ) * (nb + 1) * (3 * lg (2 * Δ)) ≤ 3 * (k - 1 : ℕ) * (n + lg (2 * Δ)) := by
  obtain ⟨j, hj⟩ : ∃ j, j = k - 1 := ⟨_, rfl⟩
  rw [← hj] at hT hμ ⊢
  have hl := Ineq.two_le_lg hΔ
  have hn := Ineq.nb_mul_le (by omega : 1 ≤ Δ) hnb
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hjp
    · have hT0 : T = 0 := by omega
      have hμ0 : μ = 0 := by omega
      simp [hT0, hμ0, lg]
    · have h1 : 1 ≤ j * (nb + 1) := Nat.mul_pos hjp (Nat.succ_pos _)
      have h2 := Ineq.binom (t := T) hμ h1
      have hjr : (0 : ℝ) < j := by exact_mod_cast hjp
      have hnr : (0 : ℝ) < (nb : ℝ) + 1 := by positivity
      have h3 : 3 * (T : ℝ) / ((j * (nb + 1) : ℕ) : ℝ) ≤ 3 * (m : ℝ) / (nb + 1) := by
        have hT' : (T : ℝ) ≤ j * m := by exact_mod_cast hT
        push_cast
        rw [div_le_div_iff₀ (by positivity) hnr]
        nlinarith [mul_le_mul_of_nonneg_right hT' hnr.le]
      have h4 := hp.three_m n Δ m nb hΔ hm hnb
      have h5 : lg (3 * (T : ℝ) / ((j * (nb + 1) : ℕ) : ℝ)) ≤ 3 * lg (2 * Δ) := by
        have h6 : lg (((2 : ℝ) * Δ) ^ 3) = 3 * lg (2 * Δ) := by unfold lg; rw [Real.logb_pow]; norm_num
        rw [← h6]
        refine lg_le_lg (by positivity) (h3.trans (h4.1.le.trans h4.2)) ?_
        have : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
        exact one_le_pow₀ (by linarith)
      have h7 : max 1 (lg (3 * (T : ℝ) / ((j * (nb + 1) : ℕ) : ℝ))) ≤ 3 * lg (2 * Δ) := max_le (by linarith) h5
      calc lg (T.choose μ) ≤ ((j * (nb + 1) : ℕ) : ℝ) * max 1 (lg (3 * (T : ℝ) / ((j * (nb + 1) : ℕ) : ℝ))) := h2
        _ ≤ ((j * (nb + 1) : ℕ) : ℝ) * (3 * lg (2 * Δ)) := mul_le_mul_of_nonneg_left h7 (Nat.cast_nonneg _)
        _ = (j : ℝ) * (nb + 1) * (3 * lg (2 * Δ)) := by push_cast; ring
  · have : (j : ℝ) * ((nb : ℝ) * lg (2 * Δ)) ≤ j * n := mul_le_mul_of_nonneg_left hn hj0
    nlinarith

/-- Step 3, «The total»: «With μ' = kM and 3T₁/μ' ≤ 3s̄ (as r ≤ M), kind 1 costs at most kM·log(3s̄)
bits», where s̄ = 16m/n̄; this is at most kM·log(96Δ·log(2Δ)), as 3s̄ < 96Δ·log(2Δ). Needs 2 ≤ Δ, n̄
< m ≤ Δn, the n̄ of the text, k ≥ 1, r ≤ M, M ≥ 1,
I ≤ r·s̄ (as n̄·I ≤ r·16m), T₁ ≤ kI and μ₁ ≤ kM, and the inequalities of «Setting and parameters». -/
theorem kind_one_le (hp : ParamIneq) {k n Δ m nb M r I T μ : ℕ} (hΔ : 2 ≤ Δ) (hnm : nb < m) (hm : m ≤ Δ * n) (hnb : IsNb n Δ nb) (hk : 1 ≤ k) (hr : r ≤ M)
    (hM : 1 ≤ M) (hI : nb * I ≤ r * (16 * m)) (hT : T ≤ k * I) (hμ : μ ≤ k * M) :
    lg (T.choose μ) ≤ k * M * lg (3 * (16 * m / nb)) ∧ (k : ℝ) * M * lg (3 * (16 * m / nb)) ≤ k * M * lg (96 * Δ * lg (2 * Δ)) := by
  have hnb1 : (1 : ℝ) ≤ nb := Ineq.nb_pos hnb
  have hnb0 : (0 : ℝ) < nb := by linarith
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : (16 : ℝ) ≤ 16 * m / nb := by
    rw [le_div_iff₀ hnb0]
    have : (nb : ℝ) ≤ m := by exact_mod_cast hnm.le
    linarith
  refine ⟨?_, ?_⟩
  · have h1 : 1 ≤ k * M := Nat.mul_pos hk hM
    have h2 := Ineq.binom (t := T) hμ h1
    have h3 : 3 * (T : ℝ) / ((k * M : ℕ) : ℝ) ≤ 3 * (16 * m / nb) := by
      have hT' : (T : ℝ) ≤ k * I := by exact_mod_cast hT
      have hI' : (nb : ℝ) * I ≤ r * (16 * m) := by exact_mod_cast hI
      have hr' : (r : ℝ) ≤ M := by exact_mod_cast hr
      have hI2 : (I : ℝ) ≤ M * (16 * m / nb) := by
        have : (I : ℝ) ≤ r * (16 * m) / nb := by rw [le_div_iff₀ hnb0]; linarith
        refine this.trans ?_
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hr' (by linarith)
      push_cast
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hI2 hkr.le
      nlinarith
    have h5 : lg (3 * (T : ℝ) / ((k * M : ℕ) : ℝ)) ≤ lg (3 * (16 * m / nb)) := lg_le_lg (by positivity) h3 (by linarith)
    have h6 : 1 ≤ lg (3 * (16 * (m : ℝ) / nb)) := by
      have : lg 2 = 1 := by unfold lg; exact Real.logb_self_eq_one (by norm_num)
      rw [← this]
      exact lg_le_lg (by norm_num) (by linarith) (by linarith)
    calc lg (T.choose μ) ≤ ((k * M : ℕ) : ℝ) * max 1 (lg (3 * (T : ℝ) / ((k * M : ℕ) : ℝ))) := h2
      _ ≤ ((k * M : ℕ) : ℝ) * lg (3 * (16 * m / nb)) := mul_le_mul_of_nonneg_left (max_le h6 h5) (Nat.cast_nonneg _)
      _ = k * M * lg (3 * (16 * m / nb)) := by push_cast; ring
  · have h4 := (hp.sb_lt n Δ m nb hΔ hm hnb).2
    refine mul_le_mul_of_nonneg_left (lg_le_lg (by linarith) (by linarith) (by linarith)) (by positivity)

/-- Step 3, «The total», «Adding two roundings per pair»: for each kind one rounding per pair,
Σ_({a,b}) ⌈log C(t_(a,b), μ_(a,b))⌉ ≤ log C(T, μ) + Σ_(b<g) b, and Σ_(b<g) b is the number of pairs;
T and μ are the sums of the t_(a,b) and of the μ_(a,b). Needs μ_(a,b) ≤ t_(a,b) for the pairs a < b
< g. -/
theorem sum_cw_le (g : ℕ) (t μ : ℕ → ℕ → ℕ) (h : ∀ b < g, ∀ a < b, μ a b ≤ t a b) :
    ((∑ b ∈ range g, ∑ a ∈ range b, cw (t a b) (μ a b) : ℕ) : ℝ) ≤
      lg ((∑ b ∈ range g, ∑ a ∈ range b, t a b).choose (∑ b ∈ range g, ∑ a ∈ range b, μ a b)) + (∑ b ∈ range g, b : ℕ) := by
  have h1 : ((∑ b ∈ range g, ∑ a ∈ range b, cw (t a b) (μ a b) : ℕ) : ℝ) ≤ ∑ b ∈ range g, ∑ a ∈ range b, (lg ((t a b).choose (μ a b)) + 1) := by
    push_cast
    exact sum_le_sum fun b hb => sum_le_sum fun a ha =>
      ClauseBound.ParityChecks.Binom.clog_le_logb_add_one (Nat.choose_pos (h b (mem_range.1 hb) a (mem_range.1 ha)))
  have h2 : ∑ b ∈ range g, ∑ a ∈ range b, (lg ((t a b).choose (μ a b)) + 1) =
      ∑ b ∈ range g, ∑ a ∈ range b, lg ((t a b).choose (μ a b)) + (∑ b ∈ range g, b : ℕ) := by
    simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one, Nat.cast_sum]
  have h3 := sum_lg_choose_le g t μ h
  linarith

/-- There are Σ_(b<g) b = g(g − 1)/2 pairs {a, b}: twice their number is at most g². -/
theorem two_mul_pairs_le (g : ℕ) : 2 * ∑ b ∈ range g, b ≤ g ^ 2 := by
  rw [Nat.mul_comm, sum_range_id_mul_two, pow_two]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-! ### Display (68) -/

/-- Step 3, «The total», display (68) before display (61) is used: in the setting of Step 3 for m >
n̄, with g ≥ 1 nodes, the network of an admissible profile has U ≤ 6(k − 1)(n + log(2Δ)) +
2kM·log(96Δ·log(2Δ)) + 2g². Needs the
inequalities of «Setting and parameters» (the hypothesis `ParamIneq`, proved as
`VariableBound.paramIneq`). -/
theorem stU (hp : ParamIneq) : StU := by
  intro k g n Δ nb M D fl y _ hS hadm
  obtain ⟨h0, h1, h2⟩ := adm_spec hadm
  have hk : 1 ≤ k := one_le_k hS.wf (Nat.zero_lt_of_lt hS.lt_m)
  obtain ⟨hT0, hT1, hI⟩ := tests_le g hk hS.wf hS.row
  have hμ0 : ∑ b ∈ range g, ∑ a ∈ range b, mu g D y a b 0 ≤ (k - 1) * (nb + 1) := by
    rw [← totP_eq]
    exact ((h2 0 (by norm_num)).1).trans (Nat.mul_le_mul_left _ h0)
  have hμ1 : ∑ b ∈ range g, ∑ a ∈ range b, mu g D y a b 1 ≤ k * M := by
    rw [← totP_eq]
    refine ((h2 1 (by norm_num)).1).trans ?_
    rw [Nat.sub_add_cancel hk]
    exact Nat.mul_le_mul_left _ h1
  have c0 := sum_cw_le g (fun a b => (tst g n D a b 0).length) (fun a b => mu g D y a b 0) (h2 0 (by norm_num)).2
  have c1 := sum_cw_le g (fun a b => (tst g n D a b 1).length) (fun a b => mu g D y a b 1) (h2 1 (by norm_num)).2
  have k0 := kind_zero_le hp hS.two hS.m_le hS.isNb hT0 hμ0
  have k1 := kind_one_le hp hS.two hS.lt_m hS.m_le hS.isNb hk hS.r_le hS.one_le hI hT1 hμ1
  have hg : 2 * ((∑ b ∈ range g, b : ℕ) : ℝ) ≤ (g : ℝ) ^ 2 := by exact_mod_cast two_mul_pairs_le g
  have hU : ((netDN g (ctx g n D y fl)).U : ℝ) =
      2 * (((∑ b ∈ range g, ∑ a ∈ range b, cw (tst g n D a b 0).length (mu g D y a b 0) : ℕ) : ℝ) +
        ((∑ b ∈ range g, ∑ a ∈ range b, cw (tst g n D a b 1).length (mu g D y a b 1) : ℕ) : ℝ)) := by
    rw [Tests.U_eq]
    simp only [Tests.capD_eq, sum_range_succ, sum_range_zero, Nat.zero_add, sum_add_distrib]
    push_cast
    ring
  rw [hU]
  linarith [k0.1, k0.2, k1.1, k1.2]

/-- Step 3, «The total», display (68) as printed: in the setting of Step 3 for m > n̄, with g ≥ 1
nodes and M ≤ 14n from display (61), the network of an admissible profile has
U ≤ 6k(n + log(2Δ)) + 28kn·log(96Δ·log(2Δ)) + 2g². Follows from display (68) with M. -/
theorem stUPrinted (h : StU) : StUPrinted := by
  intro k g n Δ nb M D fl y hg hS hM hadm
  have h1 := h k g n Δ nb M D fl y hg hS hadm
  have hl := Ineq.two_le_lg hS.two
  have hΔ : (2 : ℝ) ≤ Δ := by exact_mod_cast hS.two
  have hL : 0 ≤ lg (96 * Δ * lg (2 * Δ)) := Real.logb_nonneg (by norm_num) (by nlinarith)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hM' : (M : ℝ) ≤ 14 * n := by exact_mod_cast hM
  have e1 : ((k - 1 : ℕ) : ℝ) * (n + lg (2 * Δ)) ≤ k * (n + lg (2 * Δ)) := mul_le_mul_of_nonneg_right hk (by linarith)
  have e2 : (k : ℝ) * M * lg (96 * Δ * lg (2 * Δ)) ≤ k * (14 * n) * lg (96 * Δ * lg (2 * Δ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM' hk0) hL
  linarith

end VariableBound.Net.SizeU
