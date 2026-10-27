/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Top.ArithDefs
import ClauseBound.ParityChecks.ArithAux
import all ClauseBound.TopN.Arith
import all ClauseBound.TopN.ArithR
import all UniformInK.Top.ArithTop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The exponent of the pad is O(k²·e·n·(s+1)) unless k² is larger than a multiple of log n

`stArithD_of`: `StArithD` from the interface statements of
proof/variables/VariableBound/Top/ArithDefs.lean and
proof/sparsification/UniformInK/Top/ArithDefs.lean.
Let a = `aU C C₀`, B = `BkD C C₀` and suppose B·k² ≤ ⌊log₂ n⌋. Then D = 2^β ≤ (⌊log₂ n⌋ + 1)^(a·k),
hence D⁶ ≤ K ≤ n. So the second and the third test of the plan are passed, and W ≤ A₁·K·e with A₁ =
`A1U C₀`.
If the first test is passed too, the exponent is at most `needD`, which is at most (140·35·k² +
`ccD k C₀`·A₁ + 1)·n·e·(s+1), where `ccD k C₀` ≤ (`ccD 0 C₀` + 140)·k. If it fails, then 2^s < 4k²
and the exponent is n ≤ 4k²·n·e.
The condition B·k² ≤ ⌊log₂ n⌋ takes the place of «k ≤ (log n)^(1/4)» and «n large» of Steps 5 and 6,
and follows from them once log₂ n is large enough; D⁶ ≤ K takes the place of Δ ≤ n^(1/(40·C₀)) of
Step 4. -/

namespace VariableBound.Arith

open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.Arith

/-- For k ≥ 1, the constant of `StNeedD` is at most a constant times k². -/
theorem const_le {k : ℕ} (hk : 1 ≤ k) (C₀ A₁ : ℕ) : 140 * k * (35 * k) + ccD k C₀ * A₁ + 1 ≤ (140 * 35 + (ccD 0 C₀ + 140) * A₁ + 1) * k ^ 2 := by
  have h1 : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k
  have h2 : 1 ≤ k ^ 2 := hk.trans h1
  have e1 : ccD k C₀ = ccD 0 C₀ + 140 * k := by unfold ccD; ring
  have h3 : ccD k C₀ ≤ (ccD 0 C₀ + 140) * k ^ 2 := by
    rw [e1]
    calc ccD 0 C₀ + 140 * k ≤ ccD 0 C₀ * k ^ 2 + 140 * k ^ 2 := Nat.add_le_add (Nat.le_mul_of_pos_right _ h2) (Nat.mul_le_mul_left _ h1)
      _ = (ccD 0 C₀ + 140) * k ^ 2 := by ring
  calc 140 * k * (35 * k) + ccD k C₀ * A₁ + 1 ≤ 140 * 35 * k ^ 2 + (ccD 0 C₀ + 140) * k ^ 2 * A₁ + k ^ 2 :=
        Nat.add_le_add (Nat.add_le_add (by rw [show 140 * k * (35 * k) = 140 * 35 * k ^ 2 by ring]) (Nat.mul_le_mul_right _ h3)) h2
    _ = (140 * 35 + (ccD 0 C₀ + 140) * A₁ + 1) * k ^ 2 := by ring

/-- From B·k² ≤ ℓ with B = `BkD C C₀`: the condition 2·(102·C₀·c)² ≤ ℓ of `UniformInK.StSixU` for c =
a·k, a = `aU C C₀`. -/
theorem of_BkD {C C₀ k ℓ : ℕ} (h : BkD C C₀ * k ^ 2 ≤ ℓ) : 2 * (102 * C₀ * (aU C C₀ * k)) ^ 2 ≤ ℓ := by
  unfold BkD at h
  rwa [show 2 * (102 * C₀ * (aU C C₀ * k)) ^ 2 = 2 * (102 * C₀ * aU C C₀) ^ 2 * k ^ 2 by ring]

/-- The third test of the plan, 29·⌈log₂(2Δ)⌉ + 19 ≤ n for Δ = 2^β, is passed if β + 3 ≤ 2^β and
(2^β)⁶ ≤ n. -/
theorem test3 {β n : ℕ} (hb : β + 3 ≤ 2 ^ β) (h6 : (2 ^ β) ^ 6 ≤ n) : 29 * LD (2 ^ β) + 19 ≤ n := by
  rw [LD_two_pow]
  refine le_trans ?_ h6
  generalize 2 ^ β = D at hb
  have h3 : 3 ^ 5 ≤ D ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have h4 : 3 ^ 5 * D ≤ D ^ 6 := by rw [pow_succ D 5]; exact Nat.mul_le_mul_right D h3
  omega

/-- The statement at one level: for k ≥ 1, a polynomial-time solver with K ≥ 2 nodes at the index i
and the bound need(λ, B) ≤ e·K²·λ + C₀·K²·log₂(K·(λ+B)), K^17 ≤ n < K^(17·C₀), 2^(−s) ≤ e ≤ 1,
1/(log₂ K)^C₀ ≤ e,
2^s ≤ (2/e)^C and B·k² ≤ ⌊log₂ n⌋, the exponent of the plan, or else n, is at most A·k²·n·e·(s+1),
with A = `AexpD C₀` and B = `BkD C C₀`; from the interface statements. -/
theorem planAtD_le (hN : StNeedD) (hP : StPlanLeD) (hPN : StPlanNeedD) (hM : StMasterU) (hDL : StDLogU) (h6 : StSixU) (hB : StBetaU)
    {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (i : Idx) {e : ℝ} {C C₀ k n s : ℕ} (hk : 1 ≤ k) (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n)
    (hlt : n < S.K i ^ (17 * C₀)) (he1 : e ≤ 1) (hs : 1 / (2 : ℝ) ^ s ≤ e) (heK : 1 / Real.logb 2 (S.K i) ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B)))
    (hBk : BkD C C₀ * k ^ 2 ≤ Nat.log 2 n) :
    (((planAtD S k n i s).getD n : ℕ) : ℝ) ≤ (AexpD C₀ : ℝ) * (k : ℝ) ^ 2 * n * e * ((s : ℝ) + 1) := by
  have pn : (((planAtD S k n i s).getD n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hP Idx S k n i s
  have hK1 : 1 ≤ S.K i := by omega
  have hKn : S.K i ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn1 : 1 ≤ n := hK1.trans hKn
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) hs
  have hq : (1 : ℝ) ≤ (s : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    linarith
  have hne : 0 ≤ (n : ℝ) * e := mul_nonneg (Nat.cast_nonneg n) he0.le
  have hneq : (n : ℝ) * e ≤ (n : ℝ) * e * ((s : ℝ) + 1) := le_mul_of_one_le_right hne hq
  obtain ⟨-, hbD, -⟩ := hB k s hk
  have t6 := of_BkD hBk
  have ha1 : 1 ≤ aU C C₀ * k := Nat.mul_pos (by unfold aU; omega) hk
  have t4 := hDL (S.K i) n s C C₀ k e hK hKn heK h2
  have hsix := h6 (2 ^ betaU k s) (aU C C₀ * k) (S.K i) n C₀ ha1 hn1 hlt t4 t6
  have hMas := hM (betaU k s) (S.K i) C₀ e hbD hK heK hsix
  have t2 : 2 ^ betaU k s ≤ n + 1 := ((Nat.le_self_pow (by norm_num) _).trans (hsix.trans hKn)).trans (Nat.le_succ n)
  have t3 : 29 * LD (2 ^ betaU k s) + 19 ≤ n := test3 hbD (hsix.trans hKn)
  have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
  have hT : 0 ≤ (k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1)) := mul_nonneg hk2 (hne.trans hneq)
  have eA : (AexpD C₀ : ℝ) * (k : ℝ) ^ 2 * n * e * ((s : ℝ) + 1) =
      ((140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 : ℕ) : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1))) + 4 * ((k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1))) := by
    unfold AexpD; push_cast; ring
  rw [eA]
  by_cases c1 : s0U k ≤ s
  · have h3 : (((planAtD S k n i s).getD n : ℕ) : ℝ) ≤ (needD S k i n s : ℝ) := by
      exact_mod_cast hPN Idx S hS k n i s c1 t2 t3
    have h4 := hN Idx S i e C₀ k n s (A1U C₀) hk hK hn17 hlt t2 he0 he1 hs hMas hrate
    have h5 : ((140 * k * (35 * k) + ccD k C₀ * A1U C₀ + 1 : ℕ) : ℝ) ≤ ((140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 : ℕ) : ℝ) * (k : ℝ) ^ 2 := by
      exact_mod_cast const_le hk C₀ (A1U C₀)
    have h6' := mul_le_mul_of_nonneg_right h5 (hne.trans hneq)
    have e2 : ((140 * k * (35 * k) + ccD k C₀ * A1U C₀ + 1 : ℕ) : ℝ) * n * e * ((s : ℝ) + 1) =
        ((140 * k * (35 * k) + ccD k C₀ * A1U C₀ + 1 : ℕ) : ℝ) * ((n : ℝ) * e * ((s : ℝ) + 1)) := by ring
    rw [e2] at h4
    have e3 : ((140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 : ℕ) : ℝ) * (k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1)) =
        ((140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 : ℕ) : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1))) := by ring
    rw [e3] at h6'
    linarith
  · have h3 := le_of_small (n := n) (not_le.1 c1).le hs
    have h4 : ((2 ^ s0U k : ℕ) : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by exact_mod_cast two_pow_s0U_le hk
    have h5 := mul_le_mul_of_nonneg_right h4 hne
    have h6' : 4 * (k : ℝ) ^ 2 * ((n : ℝ) * e) ≤ 4 * (k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1)) := mul_le_mul_of_nonneg_left hneq (by positivity)
    have h7 : 0 ≤ ((140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 : ℕ) : ℝ) * ((k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1))) := mul_nonneg (Nat.cast_nonneg _) hT
    have e4 : 4 * (k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1)) = 4 * ((k : ℝ) ^ 2 * ((n : ℝ) * e * ((s : ℝ) + 1))) := by ring
    linarith

/-- Steps 4 and 5, the exponent: with A = `AexpD C₀`, B = `BkD C C₀`, for k ≥ 1 and n ≥ K^17 (K the
number of nodes of the first level), l the level picked for n and s = s(l), the exponent of the
plan, or n if there is none,
is at most A·k²·n·e_l·(s+1), or ⌊log₂ n⌋ < B·k²; for a polynomial-time solver with a sequence of
levels and 2^(−s(l)) ≤ e_l, 2^(s(l)) ≤ (2/e_l)^C; from the interface statements. -/
public theorem stArithD_of (hN : StNeedD) (hP : StPlanLeD) (hPN : StPlanNeedD) (hM : StMasterU) (hDL : StDLogU) (h6 : StSixU) (hB : StBetaU) : StArithD := by
  intro Idx _ S e C₀ Q hS slU C h1 h2
  refine ⟨AexpD C₀, BkD C C₀, fun k n hk hn => ?_⟩
  by_cases hBk : BkD C C₀ * k ^ 2 ≤ Nat.log 2 n
  swap
  · exact Or.inr (not_le.1 hBk)
  left
  obtain ⟨hr1, hr2⟩ := root17_spec n
  have hK0 : S.K (Q.idx 0) ≤ (root17 n).length := by
    by_contra h
    have h' := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 h)) 17
    exact absurd (h'.trans hn) (not_le.2 hr2)
  have hle := Q.pick_le _ hK0
  have hmax := Q.pick_max (root17 n)
  have hidx := Q.pick_idx (root17 n)
  have hu := eq_replicate (Q.pick (root17 n)).1
  obtain ⟨l, hl⟩ : ∃ l, l = (Q.pick (root17 n)).1.length := ⟨_, rfl⟩
  rw [← hl] at hu hidx hmax ⊢
  rw [hidx] at hle ⊢
  rw [hu]
  have g1 := h1 l
  have g2 := h2 l
  obtain ⟨s, hs⟩ : ∃ s, s = (slU (List.replicate l ())).length := ⟨_, rfl⟩
  rw [← hs] at g1 g2 ⊢
  have hK2 := Q.K_two l
  have hn17 : S.K (Q.idx l) ^ 17 ≤ n := (Nat.pow_le_pow_left hle 17).trans hr1
  have hlt : n < S.K (Q.idx l) ^ (17 * C₀) := by
    calc n < ((root17 n).length + 1) ^ 17 := hr2
      _ ≤ (S.K (Q.idx l) ^ C₀) ^ 17 := Nat.pow_le_pow_left ((Nat.succ_le_of_lt hmax).trans (Q.K_le _)) 17
      _ = S.K (Q.idx l) ^ (17 * C₀) := by rw [← pow_mul, mul_comm]
  exact planAtD_le hN hP hPN hM hDL h6 hB hS (Q.idx l) hk hK2 hn17 hlt (Q.e_le l) g1 (Q.e_ge l) g2 (Q.rate l) hBk

end VariableBound.Arith
