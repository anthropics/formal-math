/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Top.ArithDefs
import all ClauseBound.ParityChecks.ArithOL
import all ClauseBound.TopN.Arith
import ClauseBound.Alg.TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Steps 4 and 5: the exponent of the pad is at most (140·k·35·k + `ccD k C₀`·A₁ + 1)·n·e·(s+1)

`stNeedD : StNeedD`, from the statements on natural numbers `StUbD`, `StArgD`, `StLowerD` and
`UniformInK.StBetaU`, which are hypotheses here. The estimate between real numbers
`real_coreM` of proof/rates/ClauseBound/ParityChecks/ArithOL.lean, which speaks of real numbers
only, is used as it is. In the words of Step 4: the exponent is at most the sum of the terms of the
paper's cost display in Step 4 and of the exponents for the
profiles, the list of checks and the walk (`needD_le_sum`); the main term is e·U, with
e·140·k·n·(β+1) ≤ 140·k·35·k·n·e·(s+1) because β + 1 ≤ 35·k·(s+1) (one network costs 2^(O(e·k·n·log
Δ)) operations, and
log Δ = O(k·log(k/e)) of Step 5); all other terms together are at most (`ccD k C₀`·A₁ + 1)·n·e, if W
≤ A₁·K·e, where `ccD k C₀` = `ccD 0 C₀` + 140·k. Where the paper says that all these terms are
o(en), the bound here is
weaker, O(k·e·n), because of the part (K − 1)·λ, which that display of the paper does not have. -/

public section

namespace VariableBound.ArithNeed

open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL UniformInK VariableBound.Net

/-- The inequalities of `StLowerD` for β = `betaU k s`, between real numbers; for 1 ≤ β, k ≤ β, 2 ≤
K and K^17 ≤ n < K^(17·C₀). -/
theorem lowerDR (hL : StLowerD) {k K n s C₀ : ℕ} (hβ1 : 1 ≤ betaU k s) (hkβ : k ≤ betaU k s) (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    (K : ℝ) * ((3 * K ^ 8 * K.size : ℕ) : ℝ) ≤ 3 * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((PbD K n (2 ^ betaU k s) * (2 * (3 * K ^ 8) / K + 1) : ℕ) : ℝ) ≤ ((3 * GD C₀ : ℕ) : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (((K - 1) * lamS K (3 * K ^ 8) (UbD k K n (2 ^ betaU k s)) (PbD K n (2 ^ betaU k s)) : ℕ) : ℝ) ≤
      ((19 + 140 * k + GD C₀ : ℕ) : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    ((3 * K ^ 8 * PbD K n (2 ^ betaU k s) : ℕ) : ℝ) ≤ (GD C₀ : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((18 * K ^ 16 : ℕ) : ℝ) ≤ 18 * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (K : ℝ) ^ 2 ≤ ((WofU (betaU k s) K : ℕ) : ℝ) * n ∧
    (K : ℝ) * ((C₀ : ℝ) * (K : ℝ) ^ 2 * ((5 * (17 * C₀ * K.size) + 16 : ℕ) : ℝ)) ≤ ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ betaU k s)) : ℕ) : ℝ) ≤ ((18 * (4 + 17 * C₀) : ℕ) : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ betaU k s) + 1) * (Nat.size (2 ^ betaU k s * n) + 2) + 8) + 2 + (betaU k s + 5 * k + 10 + (k + 3) * n.size) : ℕ) : ℝ) ≤
      ((10 + 34 * C₀ : ℕ) : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := hL (betaU k s) k K n C₀ hβ1 hkβ hK hn17 hlt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast o1
  · exact_mod_cast o2
  · exact_mod_cast o3
  · exact_mod_cast o4
  · exact_mod_cast o5
  · exact_mod_cast o6
  · exact_mod_cast o7
  · exact_mod_cast o8
  · exact_mod_cast o9

/-- The exponent is at most the sum of its parts, if 2^β ≤ n + 1. -/
theorem needD_le_sum {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {k n s : ℕ} (hD : 2 ^ betaU k s ≤ n + 1) :
    needD S k i n s ≤ 3 * S.K i ^ 8 * (S.K i).size + PbD (S.K i) n (2 ^ betaU k s) * (2 * (3 * S.K i ^ 8) / S.K i + 1) +
      (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s)) +
      S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s))) (),
        List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n (2 ^ betaU k s)) (BbD k n)) ()) +
      3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n (2 ^ betaU k s)) +
      (Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ betaU k s) + 1) * (Nat.size (2 ^ betaU k s * n) + 2) + 8) + 2 + (betaU k s + 5 * k + 10 + (k + 3) * n.size)) + n / 2 ^ s := by
  have hblock : blockU k n s = 2 ^ betaU k s := min_eq_left hD
  unfold needD needNet restD
  rw [hblock]
  generalize S.need _ = nd
  generalize 3 * S.K i ^ 8 * (S.K i).size = x1
  generalize PbD (S.K i) n (2 ^ betaU k s) * (2 * (3 * S.K i ^ 8) / S.K i + 1) = x2
  generalize (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s)) = x3
  generalize 3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n (2 ^ betaU k s)) = x4
  generalize (k + 3) * n.size = x5
  generalize n / 2 ^ s = x6
  generalize Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ betaU k s) + 1) * (Nat.size (2 ^ betaU k s * n) + 2) + 8) = x7
  omega

/-- The last step between real numbers: from Z ≤ e·(140·k·n·b) + cA·(n·e), b ≤ ck·q, R₃ ≤ n·e and N
≤ Z + R₃ to N ≤ (140·k·ck + cA + 1)·n·e·q; for e, n, k, cA ≥ 0 and q ≥ 1. -/
theorem real_finalD {e n k b ck q cA Z R3 N : ℝ} (he0 : 0 ≤ e) (hn0 : 0 ≤ n) (hk0 : 0 ≤ k) (hq : 1 ≤ q) (hcA : 0 ≤ cA)
    (rb : b ≤ ck * q) (hZ : Z ≤ e * (140 * k * n * b) + cA * (n * e)) (hR3 : R3 ≤ n * e) (hN : N ≤ Z + R3) :
    N ≤ (140 * k * ck + cA + 1) * n * e * q := by
  have hne : 0 ≤ n * e := mul_nonneg hn0 he0
  have hne2 : n * e ≤ n * e * q := le_mul_of_one_le_right hne hq
  have hmain : e * (140 * k * n * b) ≤ (140 * k * ck) * (n * e * q) := by
    calc e * (140 * k * n * b) = 140 * k * (n * e) * b := by ring
      _ ≤ 140 * k * (n * e) * (ck * q) := mul_le_mul_of_nonneg_left rb (mul_nonneg (mul_nonneg (by norm_num) hk0) hne)
      _ = (140 * k * ck) * (n * e * q) := by ring
  have h2 := mul_le_mul_of_nonneg_left hne2 hcA
  have e1 : (140 * k * ck + cA + 1) * n * e * q = (140 * k * ck) * (n * e * q) + cA * (n * e * q) + n * e * q := by ring
  rw [e1]
  linarith

/-- Steps 4 and 5: the exponent `needD` is at most (140·k·35·k + `ccD k C₀`·A₁ + 1)·n·e·(s+1), if W
≤ A₁·K·e; for k ≥ 1, 2 ≤ K, K^17 ≤ n < K^(17·C₀), 2^β ≤ n + 1, 0 < e ≤ 1, 2^(−s) ≤ e and a solver
with the bound `hrate` on its cost. -/
theorem needD_le (hU : StUbD) (hA : StArgD) (hL : StLowerD) (hB : StBetaU) {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {e : ℝ} {C₀ k n s A₁ : ℕ}
    (hk : 1 ≤ k) (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n)
    (hlt : n < S.K i ^ (17 * C₀)) (hD : 2 ^ betaU k s ≤ n + 1) (he0 : 0 < e) (he1 : e ≤ 1) (hs : 1 / (2 : ℝ) ^ s ≤ e)
    (hM : ((WofU (betaU k s) (S.K i) : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needD S k i n s : ℝ) ≤ ((140 * k * (35 * k) + ccD k C₀ * A₁ + 1 : ℕ) : ℝ) * n * e * ((s : ℝ) + 1) := by
  obtain ⟨hkβ, hbD, hlin⟩ := hB k s hk
  have hβ1 : 1 ≤ betaU k s := hk.trans hkβ
  have hK1 : 1 ≤ S.K i := by omega
  have hKn : S.K i ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn1 : 1 ≤ n := hK1.trans hKn
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := lowerDR hL (k := k) (s := s) (C₀ := C₀) hβ1 hkβ hK hn17 hlt
  have harg := hA (betaU k s) k (S.K i) n C₀ hkβ hbD hK hn17 hlt hD
  have hlam1 := one_le_lamS hK1 (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s))
  have hlamK := lamS_mul_le (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s))
  have hUb := hU (betaU k s) k (S.K i) n hβ1 hn1
  have hB1 : 1 ≤ bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n (2 ^ betaU k s)) (BbD k n) := by
    have b1 : 1 ≤ BbD k n := by unfold BbD BD; omega
    have b2 : 1 ≤ 2 * (3 * S.K i ^ 8) / S.K i := by
      rw [Arith.two_g_div hK1]
      exact Nat.mul_pos (by norm_num) (by positivity)
    unfold bitsS
    exact (Nat.mul_pos (Nat.mul_pos b1 (Nat.add_pos_left b2 _)) hK1).trans_le (Nat.le_add_left _ _)
  have hr := hrate _ _ hlam1 hB1
  have hsum := needD_le_sum S i hD
  have hlog : Real.logb 2 ((S.K i : ℝ) * ((lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s)) : ℝ) +
      (bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n (2 ^ betaU k s)) (BbD k n) : ℝ))) ≤ ((5 * (17 * C₀ * (S.K i).size) + 16 : ℕ) : ℝ) := by
    have h := logb_le_of_le_pow _ _ (Nat.mul_pos hK1 (Nat.add_pos_left hlam1 _)) harg
    push_cast at h ⊢
    exact h
  generalize S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s))) (),
    List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n (2 ^ betaU k s)) (BbD k n)) ()) = nd at hr hsum
  generalize bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n (2 ^ betaU k s)) (BbD k n) = Bt at hr hlog
  generalize lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s)) = lam at hr hlog hsum r3 hlamK
  have rU : ((UbD k (S.K i) n (2 ^ betaU k s) : ℕ) : ℝ) ≤ 140 * (k : ℝ) * n * ((betaU k s + 1 : ℕ) : ℝ) + ((18 * S.K i ^ 16 : ℕ) : ℝ) := by exact_mod_cast hUb
  have rL : (lam : ℝ) * (S.K i : ℝ) ^ 3 ≤ (S.K i : ℝ) ^ 3 + (S.K i : ℝ) * ((UbD k (S.K i) n (2 ^ betaU k s) : ℕ) : ℝ) +
      ((3 * S.K i ^ 8 * PbD (S.K i) n (2 ^ betaU k s) : ℕ) : ℝ) := by
    exact_mod_cast hlamK
  have rS : (needD S k i n s : ℝ) ≤ (((3 * S.K i ^ 8 * (S.K i).size : ℕ) : ℝ) + ((PbD (S.K i) n (2 ^ betaU k s) * (2 * (3 * S.K i ^ 8) / S.K i + 1) : ℕ) : ℝ) +
      (((S.K i - 1) * lam : ℕ) : ℝ) + (nd : ℝ) + ((3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n (2 ^ betaU k s)) : ℕ) : ℝ) +
      ((Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ betaU k s) + 1) * (Nat.size (2 ^ betaU k s * n) + 2) + 8) + 2 + (betaU k s + 5 * k + 10 + (k + 3) * n.size) : ℕ) : ℝ)) +
      ((n / 2 ^ s : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have rb : ((betaU k s + 1 : ℕ) : ℝ) ≤ ((35 * k : ℕ) : ℝ) * ((s : ℝ) + 1) := by
    exact_mod_cast hlin
  have rdiv : ((n / 2 ^ s : ℕ) : ℝ) ≤ (n : ℝ) * e := by
    have h1 : ((n / 2 ^ s : ℕ) : ℝ) ≤ (n : ℝ) / ((2 ^ s : ℕ) : ℝ) := Nat.cast_div_le
    have h2 : (n : ℝ) / ((2 ^ s : ℕ) : ℝ) = (n : ℝ) * (1 / (2 : ℝ) ^ s) := by push_cast; ring
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n))
  have hKr : (0 : ℝ) < (S.K i : ℝ) := by exact_mod_cast hK1
  have core := real_coreM (A := (A₁ : ℝ)) hKr he0 he1 (Nat.cast_nonneg n) (Nat.cast_nonneg C₀) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hM r1 r2 r3 r4 r5 r6 r7 r8 r9 rU rL hr hlog
  have ecc : (3 + ((3 * GD C₀ : ℕ) : ℝ) + ((19 + 140 * k + GD C₀ : ℕ) : ℝ) + (GD C₀ : ℝ) + 18 + 1 + ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) + ((18 * (4 + 17 * C₀) : ℕ) : ℝ) +
      ((10 + 34 * C₀ : ℕ) : ℝ)) * (A₁ : ℝ) = ((ccD k C₀ * A₁ : ℕ) : ℝ) := by
    unfold ccD; push_cast; ring
  rw [ecc] at core
  have hq : (1 : ℝ) ≤ (s : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    linarith
  have fin := real_finalD (ck := ((35 * k : ℕ) : ℝ)) (q := (s : ℝ) + 1) he0.le (Nat.cast_nonneg n) (Nat.cast_nonneg k) hq (Nat.cast_nonneg _) rb core rdiv rS
  have efin : ((140 * k * (35 * k) + ccD k C₀ * A₁ + 1 : ℕ) : ℝ) = 140 * (k : ℝ) * ((35 * k : ℕ) : ℝ) + ((ccD k C₀ * A₁ : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [efin]
  exact fin

end VariableBound.ArithNeed

namespace VariableBound

/-- Steps 4 and 5: the exponent `needD` is at most (140·k·35·k + `ccD k C₀`·A₁ + 1)·n·e·(s+1), if W
≤ A₁·K·e, under the hypotheses listed at `StNeedD`; from the statements on natural numbers. -/
theorem stNeedD (hU : StUbD) (hA : StArgD) (hL : StLowerD) (hB : UniformInK.StBetaU) : StNeedD :=
  fun _ _ S i _ _ _ _ _ _ hk hK hn17 hlt hD he0 he1 hs hM hrate => ArithNeed.needD_le hU hA hL hB S i hk hK hn17 hlt hD he0 he1 hs hM hrate

end VariableBound
