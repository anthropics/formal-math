/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Defs
public import VariableBound.Top.ArithDefs
import RecursionToBound.Numbers
import VariableBound.Top.ArithNat
import UniformInK.Top.ArithMaster
import VariableBound.Net.Main
import VariableBound.Net.StepCost
import VariableBound.Printed.VariablesA.Level
import VariableBound.Printed.VariablesA.Arith
import VariableBound.Paper.Arith
import ClauseBound.Alg.TopArith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-! # Theorem D (a), with sparsification as in Step 5: the cost of one output (Step 4 of Appendix D)

«Hence the number of satisfying assignments of Φ is computed in time 2^{O(ekn·log Δ)}» (Step 4 of
Appendix D), for the exponent `needAt` of one output with its own Δ.

The arithmetic of proof/variables/VariableBound/Top is stated for Δ a power of two, 2^β, and its
parts of lower order ask k ≤ β. An output's own Δ is any number from 2 on. So two powers of two are
used. With β₁ = ⌈log₂ Δ⌉ the main term, e·U, is bounded by display (68) at 2^β₁ ≥ Δ
(`VariableBound.StUbD`): U ≤ 140·k·n·(β₁+1) + 18·K^16, and β₁ + 1 ≤ 3·log Δ.
With β = max(β₁, k) all other parts are bounded at 2^β ≥ Δ (`VariableBound.StLowerD`,
`VariableBound.StArgD`): «All these are o(en)». Both steps use that the bounds grow with Δ
(`boundsGrowWithDelta`). The exponent of the solver itself need not grow with the label length; what
grows is the bound of the hypothesis of Theorem D (a) on it (the field `rate` of the
sequence of levels), and only that is used. Last, W = (β+3)²·2^β·(number of binary digits of K) ≤
A₁·K·e (`UniformInK.StMasterU`), because (2^β)⁶ ≤ K for large n (`UniformInK.StSixU`): 2^β ≤ (⌊log₂
n⌋+1)^(4kC₀+1), and k² ≤ √(log n).

`real_core` has the statement and proof of the estimate between real numbers
`ClauseBound.ParityChecks.ArithOL.real_coreM`, which is not public in its module. -/

public section

namespace RecursionToBound

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper

/-! ### Between real numbers -/

/-- The estimate of the exponent, between real numbers: the parts T1, T2, T3, R1, Rx of lower order
and the exponent nd of the solver; M is the main part of the bound on the total. -/
theorem real_core {Kr e n W A C₀ M T1 T2 T3 R1 Rx gP U36 Ubr Lc Lg lam nd c1 c2 c3 c4 c5 c7 c8 c9 : ℝ}
    (hKr : 0 < Kr) (he0 : 0 < e) (he1 : e ≤ 1) (hn0 : 0 ≤ n) (hC0 : 0 ≤ C₀) (hgP0 : 0 ≤ gP) (hU36 : 0 ≤ U36)
    (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (h4 : 0 ≤ c4) (h5 : 0 ≤ c5) (h7 : 0 ≤ c7) (h8 : 0 ≤ c8) (h9 : 0 ≤ c9) (hM : W ≤ A * Kr * e)
    (r1 : Kr * T1 ≤ c1 * (W * n)) (r2 : Kr * T2 ≤ c2 * (W * n)) (r3 : Kr * T3 ≤ c3 * (W * n)) (r4 : gP ≤ c4 * (W * n))
    (r5 : Kr * U36 ≤ c5 * (W * n)) (r6 : Kr * Kr ^ 2 ≤ W * n) (r7 : Kr * (C₀ * Kr ^ 2 * Lc) ≤ c7 * (W * n)) (r8 : Kr * R1 ≤ c8 * (W * n))
    (r9 : Kr * Rx ≤ c9 * (W * n)) (rU : Ubr ≤ M + U36) (rL : lam * Kr ^ 3 ≤ Kr ^ 3 + Kr * Ubr + gP)
    (hr : nd ≤ e * Kr ^ 2 * lam + C₀ * Kr ^ 2 * Lg) (hlog : Lg ≤ Lc) :
    T1 + T2 + T3 + nd + R1 + Rx ≤ e * M + (c1 + c2 + c3 + c4 + c5 + 1 + c7 + c8 + c9) * A * (n * e) := by
  have e1 : Kr * (gP / Kr) = gP := by field_simp
  have hl2 : Kr ^ 2 * lam ≤ Kr ^ 2 + Ubr + gP / Kr := by
    have g1 : Kr * (Kr ^ 2 * lam) ≤ Kr * (Kr ^ 2 + Ubr + gP / Kr) := by
      calc Kr * (Kr ^ 2 * lam) = lam * Kr ^ 3 := by ring
        _ ≤ Kr ^ 3 + Kr * Ubr + gP := rL
        _ = Kr * (Kr ^ 2 + Ubr + gP / Kr) := by rw [mul_add, mul_add, e1]; ring
    exact le_of_mul_le_mul_left g1 hKr
  have hgK0 : 0 ≤ gP / Kr := div_nonneg hgP0 hKr.le
  have hK2 : 0 ≤ Kr ^ 2 := by positivity
  have hnd : nd ≤ e * M + (Kr ^ 2 + U36 + gP / Kr + C₀ * Kr ^ 2 * Lc) := by
    have a1 : e * Kr ^ 2 * lam ≤ e * (Kr ^ 2 + (M + U36) + gP / Kr) := by
      calc e * Kr ^ 2 * lam = e * (Kr ^ 2 * lam) := by ring
        _ ≤ e * (Kr ^ 2 + Ubr + gP / Kr) := mul_le_mul_of_nonneg_left hl2 he0.le
        _ ≤ e * (Kr ^ 2 + (M + U36) + gP / Kr) := mul_le_mul_of_nonneg_left (by linarith) he0.le
    have a2 : e * (Kr ^ 2 + U36 + gP / Kr) ≤ 1 * (Kr ^ 2 + U36 + gP / Kr) := mul_le_mul_of_nonneg_right he1 (by linarith)
    have a3 : C₀ * Kr ^ 2 * Lg ≤ C₀ * Kr ^ 2 * Lc := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC0 hK2)
    have e2 : e * (Kr ^ 2 + (M + U36) + gP / Kr) = e * M + e * (Kr ^ 2 + U36 + gP / Kr) := by ring
    linarith
  obtain ⟨X, hX⟩ : ∃ X, X = T1 + T2 + T3 + (Kr ^ 2 + U36 + gP / Kr + C₀ * Kr ^ 2 * Lc) + R1 + Rx := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc, cc = c1 + c2 + c3 + c4 + c5 + 1 + c7 + c8 + c9 := ⟨_, rfl⟩
  have hcc0 : 0 ≤ cc := by rw [hcc]; linarith
  have hKX : Kr * X ≤ cc * (W * n) := by
    have e3 : Kr * X = Kr * T1 + Kr * T2 + Kr * T3 + (Kr * Kr ^ 2 + Kr * U36 + Kr * (gP / Kr) + Kr * (C₀ * Kr ^ 2 * Lc)) + Kr * R1 + Kr * Rx := by
      rw [hX]; ring
    have e4 : cc * (W * n) = c1 * (W * n) + c2 * (W * n) + c3 * (W * n) + c4 * (W * n) + c5 * (W * n) + W * n + c7 * (W * n) + c8 * (W * n) + c9 * (W * n) := by
      rw [hcc]; ring
    rw [e3, e4, e1]
    linarith
  have hXle : X ≤ cc * A * (n * e) := by
    have g1 : Kr * X ≤ Kr * (cc * A * (n * e)) := by
      calc Kr * X ≤ cc * (W * n) := hKX
        _ ≤ cc * (A * Kr * e * n) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM hn0) hcc0
        _ = Kr * (cc * A * (n * e)) := by ring
    exact le_of_mul_le_mul_left g1 hKr
  rw [← hcc]
  rw [hX] at hXle
  linarith

/-! ### The parts of the exponent grow with Δ -/

/-- The bound on the label length grows with the bounds on the total and on P. -/
theorem lamS_mono (K g : ℕ) {U U' P P' : ℕ} (hU : U ≤ U') (hP : P ≤ P') : lamS K g U P ≤ lamS K g U' P' := by
  unfold lamS
  exact Nat.div_le_div_right (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left K hU) _) (Nat.mul_le_mul_left g hP))

/-- The bound on the length of the entries grows with the bound on P. -/
theorem bitsS_mono (K g B : ℕ) {P P' : ℕ} (hP : P ≤ P') : bitsS K g P B ≤ bitsS K g P' B := by
  unfold bitsS
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hP) _

/-- The number of binary digits of the number of profiles: at most g·g·2 times that of the number of
objects, plus 1, g = 3K⁸. -/
theorem size_nPrMax_le (K n Δ : ℕ) : Nat.size (nPrMax K n Δ) ≤ 3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n Δ) + 1 := by
  rw [Nat.size_le]
  unfold nPrMax PaddedDescent.F.Mark.nProf
  calc (objMax n Δ + 1) ^ (3 * K ^ 8 * (3 * K ^ 8) * 2) ≤ (2 ^ Nat.size (objMax n Δ)) ^ (3 * K ^ 8 * (3 * K ^ 8) * 2) := Nat.pow_le_pow_left (Nat.lt_size_self _) _
    _ = 2 ^ (3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n Δ)) := by rw [← pow_mul, Nat.mul_comm (Nat.size _)]
    _ < 2 ^ (3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n Δ) + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)

/-- The exponent for one output with Δ ≤ D is at most the sum of its parts, all but the exponent of
the solver taken at D. -/
theorem needAt_le_sum {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (k n : ℕ) {Δ D : ℕ} (h : Δ ≤ D) :
    needAt S k i n Δ ≤ 3 * S.K i ^ 8 * (S.K i).size + PbD (S.K i) n D * (2 * (3 * S.K i ^ 8) / S.K i + 1) +
      (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n D) (PbD (S.K i) n D) +
      S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ)) (),
        List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n Δ) (BbD k n)) ()) +
      3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n D) +
      (Nat.size (8 * (10 * n + 1) * (sbMax D + 1) * (Nat.size (D * n) + 2) + 8) + 1) := by
  obtain ⟨hU, hP, -, hsb⟩ := boundsGrowWithDelta k (S.K i) n Δ D h
  have a2 : PbD (S.K i) n Δ * (2 * (3 * S.K i ^ 8) / S.K i + 1) ≤ PbD (S.K i) n D * (2 * (3 * S.K i ^ 8) / S.K i + 1) := Nat.mul_le_mul_right _ hP
  have a3 : (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) ≤
      (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n D) (PbD (S.K i) n D) := Nat.mul_le_mul_left _ (lamS_mono _ _ hU hP)
  have a4 := size_nPrMax_le (S.K i) n Δ
  have a5 : 3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n Δ) ≤ 3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n D) :=
    Nat.mul_le_mul_left _ (Nat.size_le_size (objMax_mono n h))
  have a6 : Nat.size (8 * (10 * n + 1) * (sbMax Δ + 1) * (Nat.size (Δ * n) + 2) + 8) ≤ Nat.size (8 * (10 * n + 1) * (sbMax D + 1) * (Nat.size (D * n) + 2) + 8) :=
    Nat.size_le_size (Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.succ_le_succ hsb)) (Nat.add_le_add_right (Nat.size_le_size (Nat.mul_le_mul_right n h)) 2)) 8)
  unfold needAt needNet
  generalize S.need _ = nd
  generalize 3 * S.K i ^ 8 * (S.K i).size = x1
  generalize PbD (S.K i) n Δ * (2 * (3 * S.K i ^ 8) / S.K i + 1) = x2 at a2 ⊢
  generalize PbD (S.K i) n D * (2 * (3 * S.K i ^ 8) / S.K i + 1) = y2 at a2 ⊢
  generalize (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) = x3 at a3 ⊢
  generalize (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n D) (PbD (S.K i) n D) = y3 at a3 ⊢
  generalize Nat.size (nPrMax (S.K i) n Δ) = x4 at a4 ⊢
  generalize 3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n Δ) = x5 at a4 a5
  generalize 3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n D) = y5 at a5 ⊢
  generalize Nat.size (8 * (10 * n + 1) * (sbMax Δ + 1) * (Nat.size (Δ * n) + 2) + 8) = x6 at a6 ⊢
  generalize Nat.size (8 * (10 * n + 1) * (sbMax D + 1) * (Nat.size (D * n) + 2) + 8) = y6 at a6 ⊢
  omega

/-! ### The exponent for one output -/

/-- Step 4 for one output. Let 2 ≤ K, K^17 ≤ n < K^(17·C₀), Δ ≤ 2^β₁ with 1 ≤ β₁ ≤ β, k ≤ β, β + 3 ≤
2^β ≤ n + 1, 0 < e ≤ 1, W = `WofU β K` ≤ A₁·K·e, and let the solver have the bound of the hypothesis
of Theorem D (a) at the index i. Then the exponent for one output with this Δ is at most
e·140·k·n·(β₁+1) + `ccD k C₀`·A₁·n·e. -/
theorem needAt_le {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {e : ℝ} {C₀ k n Δ β₁ β A₁ : ℕ}
    (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n) (hlt : n < S.K i ^ (17 * C₀))
    (hβ₁ : 1 ≤ β₁) (hΔ : Δ ≤ 2 ^ β₁) (hββ : β₁ ≤ β) (hkβ : k ≤ β) (hbD : β + 3 ≤ 2 ^ β) (hD : 2 ^ β ≤ n + 1)
    (he0 : 0 < e) (he1 : e ≤ 1) (hM : ((WofU β (S.K i) : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needAt S k i n Δ : ℝ) ≤ e * (140 * (k : ℝ) * n * ((β₁ + 1 : ℕ) : ℝ)) + ((VariableBound.ccD k C₀ * A₁ : ℕ) : ℝ) * ((n : ℝ) * e) := by
  have hB := VariableBound.Net.Main.bounds
  have hsum := needAt_le_sum S i k n (hΔ.trans (Nat.pow_le_pow_right (by norm_num) hββ))
  obtain ⟨K, hKdef⟩ : ∃ K, K = S.K i := ⟨_, rfl⟩
  rw [← hKdef] at hK hn17 hlt hM hrate hsum
  have hΔD : Δ ≤ 2 ^ β := hΔ.trans (Nat.pow_le_pow_right (by norm_num) hββ)
  have hβ1 : 1 ≤ β := hβ₁.trans hββ
  have hK1 : 1 ≤ K := by omega
  have hKn : K ≤ n := (Nat.le_self_pow (by norm_num) K).trans hn17
  have hn1 : 1 ≤ n := hK1.trans hKn
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := VariableBound.stLowerD hB β k K n C₀ hβ1 hkβ hK hn17 hlt
  have harg := VariableBound.stArgD hB β k K n C₀ hkβ hbD hK hn17 hlt hD
  have hUb := VariableBound.stUbD hB β₁ k K n hβ₁ hn1
  obtain ⟨hU1, -, -, -⟩ := boundsGrowWithDelta k K n Δ (2 ^ β₁) hΔ
  obtain ⟨hU2, hP2, -, -⟩ := boundsGrowWithDelta k K n Δ (2 ^ β) hΔD
  have hlam1 : 1 ≤ lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ) := by
    unfold lamS
    rw [Nat.le_div_iff_mul_le (by positivity)]
    omega
  have hB1 : 1 ≤ bitsS K (3 * K ^ 8) (PbD K n Δ) (BbD k n) := by
    rw [StepCost.bitsS_eq hK1]
    have b1 : 1 ≤ BbD k n := by unfold BbD BD; omega
    have b2 : 1 ≤ 6 * K ^ 8 + 36 * K ^ 15 := Nat.add_pos_left (by positivity) _
    exact (Nat.mul_pos b2 b1).trans_le (Nat.le_add_left _ _)
  have hlamK : lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ) * K ^ 3 ≤ K ^ 3 + K * UbD k K n (2 ^ β₁) + 3 * K ^ 8 * PbD K n (2 ^ β) :=
    (Nat.div_mul_le_self _ _).trans (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left K hU1) _) (Nat.mul_le_mul_left _ hP2))
  have harg' : K * (lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ) + bitsS K (3 * K ^ 8) (PbD K n Δ) (BbD k n)) ≤ 2 ^ (5 * (17 * C₀ * K.size) + 16) :=
    (Nat.mul_le_mul_left K (Nat.add_le_add (lamS_mono _ _ hU2 hP2) (bitsS_mono _ _ _ hP2))).trans harg
  have hr := hrate _ _ hlam1 hB1
  have hlog : Real.logb 2 ((K : ℝ) * ((lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ) : ℝ) + (bitsS K (3 * K ^ 8) (PbD K n Δ) (BbD k n) : ℝ))) ≤
      ((5 * (17 * C₀ * K.size) + 16 : ℕ) : ℝ) := by
    have h := logb_le_of_le_pow _ _ (Nat.mul_pos hK1 (Nat.add_pos_left hlam1 _)) harg'
    push_cast at h ⊢
    exact h
  generalize S.need (i, List.replicate (lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ)) (), List.replicate (bitsS K (3 * K ^ 8) (PbD K n Δ) (BbD k n)) ()) = nd at hr hsum
  generalize bitsS K (3 * K ^ 8) (PbD K n Δ) (BbD k n) = Bt at hr hlog
  generalize lamS K (3 * K ^ 8) (UbD k K n Δ) (PbD K n Δ) = lam at hr hlog hlamK
  have o9' : K * (Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) + 1) ≤ (10 + 34 * C₀) * (WofU β K * n) :=
    (Nat.mul_le_mul_left K (by omega)).trans o9
  have r1 : (K : ℝ) * ((3 * K ^ 8 * K.size : ℕ) : ℝ) ≤ 3 * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o1
  have r2 : (K : ℝ) * ((PbD K n (2 ^ β) * (2 * (3 * K ^ 8) / K + 1) : ℕ) : ℝ) ≤ ((3 * VariableBound.GD C₀ : ℕ) : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o2
  have r3 : (K : ℝ) * (((K - 1) * lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) : ℕ) : ℝ) ≤ ((19 + 140 * k + VariableBound.GD C₀ : ℕ) : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by
    exact_mod_cast o3
  have r4 : ((3 * K ^ 8 * PbD K n (2 ^ β) : ℕ) : ℝ) ≤ (VariableBound.GD C₀ : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o4
  have r5 : (K : ℝ) * ((18 * K ^ 16 : ℕ) : ℝ) ≤ 18 * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o5
  have r6 : (K : ℝ) * (K : ℝ) ^ 2 ≤ ((WofU β K : ℕ) : ℝ) * n := by exact_mod_cast o6
  have r7 : (K : ℝ) * ((C₀ : ℝ) * (K : ℝ) ^ 2 * ((5 * (17 * C₀ * K.size) + 16 : ℕ) : ℝ)) ≤ ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o7
  have r8 : (K : ℝ) * ((3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ β)) : ℕ) : ℝ) ≤ ((18 * (4 + 17 * C₀) : ℕ) : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by exact_mod_cast o8
  have r9 : (K : ℝ) * ((Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) + 1 : ℕ) : ℝ) ≤ ((10 + 34 * C₀ : ℕ) : ℝ) * (((WofU β K : ℕ) : ℝ) * n) := by
    exact_mod_cast o9'
  have rU : ((UbD k K n (2 ^ β₁) : ℕ) : ℝ) ≤ 140 * (k : ℝ) * n * ((β₁ + 1 : ℕ) : ℝ) + ((18 * K ^ 16 : ℕ) : ℝ) := by exact_mod_cast hUb
  have rL : (lam : ℝ) * (K : ℝ) ^ 3 ≤ (K : ℝ) ^ 3 + (K : ℝ) * ((UbD k K n (2 ^ β₁) : ℕ) : ℝ) + ((3 * K ^ 8 * PbD K n (2 ^ β) : ℕ) : ℝ) := by exact_mod_cast hlamK
  have rS : (needAt S k i n Δ : ℝ) ≤ ((3 * K ^ 8 * K.size : ℕ) : ℝ) + ((PbD K n (2 ^ β) * (2 * (3 * K ^ 8) / K + 1) : ℕ) : ℝ) +
      (((K - 1) * lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) : ℕ) : ℝ) + (nd : ℝ) + ((3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ β)) : ℕ) : ℝ) +
      ((Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have core := real_core (A := (A₁ : ℝ)) hKr he0 he1 (Nat.cast_nonneg n) (Nat.cast_nonneg C₀) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hM r1 r2 r3 r4 r5 r6 r7 r8 r9 rU rL hr hlog
  have ecc : (3 + ((3 * VariableBound.GD C₀ : ℕ) : ℝ) + ((19 + 140 * k + VariableBound.GD C₀ : ℕ) : ℝ) + (VariableBound.GD C₀ : ℝ) + 18 + 1 + ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) + ((18 * (4 + 17 * C₀) : ℕ) : ℝ) +
      ((10 + 34 * C₀ : ℕ) : ℝ)) * (A₁ : ℝ) = ((VariableBound.ccD k C₀ * A₁ : ℕ) : ℝ) := by
    unfold VariableBound.ccD; push_cast; ring
  rw [ecc] at core
  exact rS.trans core

/-! ### For large n the hypotheses hold -/

/-- β + 3 ≤ 2^β for β ≥ 3. -/
theorem add_three_le_two_pow {β : ℕ} (h : 3 ≤ β) : β + 3 ≤ 2 ^ β := by
  induction β, h using Nat.le_induction with
  | base => norm_num
  | succ β hβ ih =>
    rw [pow_succ]
    omega

/-- If (520200·C₀⁴)² ≤ ℓ and k⁴ ≤ ℓ, then 2·(102·C₀·(4kC₀+1))² ≤ ℓ, for C₀, k ≥ 1, because the left
side is at most 520200·C₀⁴·k² ≤ ℓ. -/
theorem six_test {C₀ k ℓ : ℕ} (hC : 1 ≤ C₀) (hk : 1 ≤ k) (h1 : (520200 * C₀ ^ 4) ^ 2 ≤ ℓ) (h2 : k ^ 4 ≤ ℓ) : 2 * (102 * C₀ * (4 * k * C₀ + 1)) ^ 2 ≤ ℓ := by
  have a : 4 * k * C₀ + 1 ≤ 5 * k * C₀ := by nlinarith [Nat.mul_pos hk hC]
  have b : 2 * (102 * C₀ * (4 * k * C₀ + 1)) ^ 2 ≤ 2 * (102 * C₀ * (5 * k * C₀)) ^ 2 :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ a) 2)
  have c : 2 * (102 * C₀ * (5 * k * C₀)) ^ 2 = 520200 * C₀ ^ 4 * k ^ 2 := by ring
  have d : (520200 * C₀ ^ 4 * k ^ 2) ^ 2 ≤ ℓ ^ 2 := by
    calc (520200 * C₀ ^ 4 * k ^ 2) ^ 2 = (520200 * C₀ ^ 4) ^ 2 * k ^ 4 := by ring
      _ ≤ ℓ * ℓ := Nat.mul_le_mul h1 h2
      _ = ℓ ^ 2 := by ring
  have f := (Nat.pow_le_pow_iff_left (by norm_num)).1 d
  omega

/-- 2^⌈log₂ Δ⌉ ≤ 2Δ, 1 ≤ ⌈log₂ Δ⌉ and ⌈log₂ Δ⌉ + 1 ≤ 3·log Δ, for Δ ≥ 2. -/
theorem clog_facts {Δ : ℕ} (hΔ : 2 ≤ Δ) : 2 ^ Nat.clog 2 Δ ≤ 2 * Δ ∧ 1 ≤ Nat.clog 2 Δ ∧ ((Nat.clog 2 Δ + 1 : ℕ) : ℝ) ≤ 3 * lg Δ := by
  have h1 : 1 ≤ Nat.clog 2 Δ := Nat.clog_pos (by norm_num) hΔ
  obtain ⟨p, hp⟩ : ∃ p, Nat.clog 2 Δ = p + 1 := ⟨Nat.clog 2 Δ - 1, by omega⟩
  have h2 : 2 ^ p < Δ := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := Δ) (by omega)
    rwa [hp, Nat.pred_succ] at this
  refine ⟨by rw [hp, pow_succ]; omega, h1, ?_⟩
  have h3 : (p : ℝ) ≤ lg Δ := by
    refine (Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast (by omega : 0 < Δ))).2 ?_
    rw [Real.rpow_natCast]
    exact_mod_cast h2.le
  have h4 := one_le_lg hΔ
  rw [hp]
  push_cast
  linarith

/-- «Hence the number of satisfying assignments of Φ is computed in time 2^{O(ekn·log Δ)}» (Step 4
of Appendix D): for large n, the level ℓ of n, 3 ≤ k ≤ (log n)^(1/4) and 2 ≤ Δ ≤ (log n)^(4kC₀) the
exponent for one output with this Δ is at most A·e_ℓ·k·n·log Δ. -/
theorem oneOutputCost : OneOutputCost := by
  intro Idx _ S e C₀ Q _
  refine ⟨420 + (VariableBound.ccD 0 C₀ + 140) * A1U C₀, 2 ^ ((520200 * C₀ ^ 4) ^ 2), fun k n l Δ hn hl hk hk4 hΔ2 hΔ => ?_⟩
  have hC := VariableBound.VariablesA.one_le_C₀ Q
  have hK := Q.K_two l
  have hlt : n < S.K (Q.idx l) ^ (17 * C₀) := lt_of_lt_of_le hl.2 (by rw [Nat.mul_comm, pow_mul]; exact Nat.pow_le_pow_left (Q.K_le l) 17)
  have hKn := VariableBound.VariablesA.K_le_n Q hl
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Nat.log 2 n := ⟨_, rfl⟩
  have hℓB : (520200 * C₀ ^ 4) ^ 2 ≤ ℓ := hℓ ▸ Nat.le_log_of_pow_le (by norm_num) hn
  have hℓ1 : 1 ≤ ℓ := le_trans (Nat.one_le_pow _ _ (Nat.mul_pos (by norm_num) (pow_pos hC 4))) hℓB
  have hk4ℓ : k ^ 4 ≤ ℓ := by
    have h1 : (((k ^ 4 : ℕ) : ℕ) : ℝ) ≤ lg n := by push_cast; exact hk4
    have h2 := (Real.le_logb_iff_rpow_le one_lt_two hn0).1 h1
    rw [Real.rpow_natCast] at h2
    exact hℓ ▸ Nat.le_log_of_pow_le (by norm_num) (by exact_mod_cast h2)
  have hlgℓ : lg n ≤ ((ℓ + 1 : ℕ) : ℝ) := by
    have := VariableBound.VariablesA.lg_lt_log_succ hn1
    rw [hℓ]
    push_cast
    exact this.le
  have hL0 : 0 ≤ lg n := le_trans (by positivity) hk4
  obtain ⟨hc1, hc2, hc3⟩ := clog_facts hΔ2
  obtain ⟨β₁, hβ₁⟩ : ∃ β₁, β₁ = Nat.clog 2 Δ := ⟨_, rfl⟩
  rw [← hβ₁] at hc1 hc2 hc3
  have hΔℓ : Δ ≤ (ℓ + 1) ^ (4 * k * C₀) := by
    have : (Δ : ℝ) ≤ (((ℓ + 1) ^ (4 * k * C₀) : ℕ) : ℝ) := by
      rw [Nat.cast_pow]
      exact hΔ.trans (pow_le_pow_left₀ hL0 hlgℓ _)
    exact_mod_cast this
  have hD1 : 2 ^ β₁ ≤ (ℓ + 1) ^ (4 * k * C₀ + 1) := by
    rw [pow_succ, Nat.mul_comm]
    exact hc1.trans (Nat.mul_le_mul (by omega) hΔℓ)
  have hD2 : 2 ^ k ≤ (ℓ + 1) ^ (4 * k * C₀ + 1) :=
    (Nat.pow_le_pow_left (by omega) k).trans (Nat.pow_le_pow_right (by omega) (by nlinarith [Nat.mul_pos (by omega : 0 < k) hC]))
  have hDle : 2 ^ max β₁ k ≤ (Nat.log 2 n + 1) ^ (4 * k * C₀ + 1) := by
    rw [← hℓ]
    rcases le_total β₁ k with h | h
    · rw [max_eq_right h]; exact hD2
    · rw [max_eq_left h]; exact hD1
  have h6 : (2 ^ max β₁ k) ^ 6 ≤ S.K (Q.idx l) :=
    stSixU _ (4 * k * C₀ + 1) _ n C₀ (by omega) hn1 hlt hDle (hℓ ▸ six_test hC (by omega) hℓB hk4ℓ)
  have hbD : max β₁ k + 3 ≤ 2 ^ max β₁ k := add_three_le_two_pow (hk.trans (le_max_right _ _))
  have hD : 2 ^ max β₁ k ≤ n + 1 := ((Nat.le_self_pow (by norm_num) _).trans h6).trans (hKn.trans (Nat.le_succ n))
  have hM := stMasterU (max β₁ k) _ C₀ (e l) hbD hK (Q.e_ge l) h6
  have main := needAt_le S (Q.idx l) (k := k) hK hl.1 hlt hc2 (hβ₁ ▸ Nat.le_pow_clog (by norm_num) Δ) (le_max_left _ _) (le_max_right _ _) hbD hD
    (VariableBound.VariablesA.e_pos Q l) (Q.e_le l) hM (Q.rate l)
  refine main.trans ?_
  have he0 := (VariableBound.VariablesA.e_pos Q l).le
  have hw := one_le_lg hΔ2
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hy0 : 0 ≤ (n : ℝ) * e l := mul_nonneg hn0.le he0
  have s0 : VariableBound.ccD k C₀ * A1U C₀ ≤ (VariableBound.ccD 0 C₀ + 140) * A1U C₀ * k := by
    have : VariableBound.ccD k C₀ ≤ (VariableBound.ccD 0 C₀ + 140) * k := by
      have e1 : VariableBound.ccD k C₀ = VariableBound.ccD 0 C₀ + 140 * k := by unfold VariableBound.ccD; ring
      rw [e1]
      nlinarith [Nat.zero_le (VariableBound.ccD 0 C₀)]
    calc VariableBound.ccD k C₀ * A1U C₀ ≤ (VariableBound.ccD 0 C₀ + 140) * k * A1U C₀ := Nat.mul_le_mul_right _ this
      _ = _ := by ring
  have s1 : ((VariableBound.ccD k C₀ * A1U C₀ : ℕ) : ℝ) ≤ (((VariableBound.ccD 0 C₀ + 140) * A1U C₀ : ℕ) : ℝ) * k := by exact_mod_cast s0
  have s2 : (n : ℝ) * e l ≤ (n : ℝ) * e l * lg Δ := le_mul_of_one_le_right hy0 hw
  have t2 : ((VariableBound.ccD k C₀ * A1U C₀ : ℕ) : ℝ) * ((n : ℝ) * e l) ≤ (((VariableBound.ccD 0 C₀ + 140) * A1U C₀ : ℕ) : ℝ) * k * ((n : ℝ) * e l * lg Δ) :=
    mul_le_mul s1 s2 hy0 (by positivity)
  have t1 : e l * (140 * (k : ℝ) * n * ((β₁ + 1 : ℕ) : ℝ)) ≤ e l * (140 * (k : ℝ) * n * (3 * lg Δ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc3 (by positivity)) he0
  have e1 : ((420 + (VariableBound.ccD 0 C₀ + 140) * A1U C₀ : ℕ) : ℝ) * e l * k * n * lg Δ =
      e l * (140 * (k : ℝ) * n * (3 * lg Δ)) + (((VariableBound.ccD 0 C₀ + 140) * A1U C₀ : ℕ) : ℝ) * k * ((n : ℝ) * e l * lg Δ) := by
    rw [Nat.cast_add]
    push_cast
    ring
  rw [e1]
  linarith

end RecursionToBound
