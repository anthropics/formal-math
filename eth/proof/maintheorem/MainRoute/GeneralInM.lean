/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainRoute.GeneralDefs
import MainRoute.EveryMachine
import GeneralPieces.Top.EndM
import GeneralPieces.Top.CaseI
import GeneralPieces.Num.TopDisplay
import GeneralPieces.ThmRunningTime
import ClauseBound.Gen.End
import ClauseBound.Alg.TopArith
import ClauseBound.Alg.TopVal
import ClauseBound.Alg.CertTop
import ClauseBound.Alg.Decode
import PaddedDescent.Col.CertG
import CountKSatRate.Pad
import VariableBound.Paper.Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Item (5) on every solver, and both bounds from one algorithm

The items of the route are numbered as in proof/maintheorem/MainRoute/Defs.lean.

* `e_le_rPow_of_sqrt`: at the level ℓ picked for m, «the largest ℓ with K_ℓ ≤ m^(1/9)», m <
  K_(ℓ+1)^9 ≤ K_ℓ^(9C₀), so log(m+2) ≤ (9C₀+1)·log K_ℓ; with e_ℓ ≤ a/√(log K_ℓ) this gives e_ℓ ≤
  (a·(9C₀+1)+1)/√(log(m+2)).
* `topM_of_sqrt`: `GeneralPieces.Tied.TopM` for the function for the bound in m (it and its exponent
  are polynomial-time, it is right, its exponent is O(k·m/√(log m)), and a machine computes it), for
  EVERY polynomial-time solver with a sequence of levels and e_ℓ ≤ a/√(log K_ℓ). Each ingredient is
  proved for any sequence of levels: `GeneralPieces.Top.topM_of_arith`, and the inequality that it
  asks for (the exponent is O(k·m·e_ℓ)), through the bound on the logarithm of the number of
  operations
  in the proof of Theorem A(c) (`GeneralPieces.TopDisplay.stTopArith2`). The network of the formula
  is rebalanced by case (i) of Lemma 8, as in the proof of Theorem A(c)
  (`GeneralPieces.partC_m_tied`).
* `meetsBoundInM_of_topM`: from three of these facts (right, exponent, machine), an ARBITRARY
  machine that computes the function with its exponent meets the bound in m.
* `boundInMOnEverySolver`, and `bothBounds_of`: `BothBoundsOnEverySolver` from it and
  `RouteOnEverySolver`. -/

public section

namespace MainRoute

open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)

/-- At the level picked for m: if e_ℓ ≤ a/√(log K_ℓ) for all ℓ, then e_ℓ ≤
(a·(9C₀+1)+1)/√(log(m+2)), for every m. -/
theorem e_le_rPow_of_sqrt {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) {a : ℕ} (ha : ∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) (m : ℕ) :
    e (Q.pick (root9 m)).1.length ≤ ((a * (9 * C₀ + 1) + 1 : ℕ) : ℝ) * SatM.rPow (1 / 2) m := by
  obtain ⟨l, hl⟩ : ∃ l, l = (Q.pick (root9 m)).1.length := ⟨_, rfl⟩
  rw [← hl]
  have hK2 := Q.K_two l
  have h1 : (root9 m).length < S.K (Q.idx (l + 1)) := hl ▸ Q.pick_max (root9 m)
  have h2 : m < S.K (Q.idx l) ^ (9 * C₀) := by
    calc m < ((root9 m).length + 1) ^ 9 := (TopArith.root9_spec m).2
      _ ≤ S.K (Q.idx (l + 1)) ^ 9 := Nat.pow_le_pow_left h1 9
      _ ≤ (S.K (Q.idx l) ^ C₀) ^ 9 := Nat.pow_le_pow_left (Q.K_le l) 9
      _ = _ := by rw [← pow_mul, mul_comm]
  have h3 : m + 2 ≤ S.K (Q.idx l) ^ (9 * C₀ + 1) := by
    rw [pow_succ]
    have : 1 ≤ S.K (Q.idx l) ^ (9 * C₀) := Nat.one_le_pow _ _ (by omega)
    nlinarith
  obtain ⟨y, hy⟩ : ∃ y, y = Real.logb 2 ((m : ℝ) + 2) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = lg (S.K (Q.idx l)) := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := hy ▸ ClauseBound.Alg.End.one_le_log m
  have hz1 : 1 ≤ z := hz ▸ VariableBound.Paper.one_le_lg hK2
  have h4 : y ≤ ((9 * C₀ + 1 : ℕ) : ℝ) * z := by
    have g1 : ((m : ℝ) + 2) ≤ (S.K (Q.idx l) : ℝ) ^ (9 * C₀ + 1) := by exact_mod_cast h3
    have g2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) g1
    rw [Real.logb_pow] at g2
    rw [hy, hz]
    exact g2
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((9 * C₀ + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hc] at h4
  have hc1 : 1 ≤ c := by rw [hc]; exact_mod_cast (by omega : 1 ≤ 9 * C₀ + 1)
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 (by linarith)
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.2 (by linarith)
  -- √y ≤ c·√z
  have h5 : Real.sqrt y ≤ c * Real.sqrt z := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    nlinarith
  have h6 : 1 / Real.sqrt z ≤ c / Real.sqrt y := by
    rw [div_le_div_iff₀ hsz hsy]
    linarith
  have hr : SatM.rPow (1 / 2) m = 1 / Real.sqrt y := by
    unfold SatM.rPow
    rw [← hy, ← Real.sqrt_eq_rpow]
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  calc e l ≤ a / Real.sqrt z := hz ▸ ha l
    _ = a * (1 / Real.sqrt z) := by ring
    _ ≤ a * (c / Real.sqrt y) := mul_le_mul_of_nonneg_left h6 ha0
    _ ≤ (a * c + 1) * (1 / Real.sqrt y) := by
        have : 0 ≤ 1 / Real.sqrt y := by positivity
        have e1 : (a : ℝ) * (c / Real.sqrt y) = a * c * (1 / Real.sqrt y) := by ring
        rw [e1]
        nlinarith
    _ = _ := by rw [hr, hc]; push_cast; ring

/-- `GeneralPieces.Tied.TopM` for the function for the bound in m, for every polynomial-time solver
with a sequence of levels and e_ℓ ≤ a/√(log K_ℓ). -/
theorem topM_of_sqrt {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) (hS : S.Poly) {a : ℕ} (ha : ∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) :
    GeneralPieces.Tied.TopM S Q.pick (SatM.rPow (1 / 2)) :=
  GeneralPieces.Top.topM_of_arith CountKSatRate.stPaddedW (TopVal.stCorrectM Decode.stDecM (GeneralPieces.Top.stCountG2 TopVal.stSatPresentsK))
    (CertTop.stCertM Decode.stCertDecM CertTop.stCertSatK PaddedDescent.F.certRebalG) S e C₀ Q (GeneralPieces.TopDisplay.stTopArith2 Idx S e C₀ Q) hS _
    (a * (9 * C₀ + 1) + 1) (fun m _ => ClauseBound.Gen.End.le_rPow (by norm_num) (by omega) m) fun m _ => e_le_rPow_of_sqrt Q ha m

/-- From `GeneralPieces.Tied.TopM`: every machine that computes the function for the bound in m with
its exponent meets the bound in m. -/
theorem meetsBoundInM_of_topM {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} (hT : GeneralPieces.Tied.TopM S pick (SatM.rPow (1 / 2)))
    (M : TM2ComputableAux Bool Bool) (q : ℕ) (hM : Computes M (AM S pick) (eM S pick) q) : ∃ C : ℕ, MeetsBoundInM M C := by
  obtain ⟨G, hG⟩ := hT.rate
  refine ⟨2 * q + 2 * q * (G + 1) + q * 4 ^ q, fun k n φ hk hφ hm hocc => ?_⟩
  have hm1 : 1 ≤ φ.length := by omega
  have hx : Outputs M (SatM.enc k φ) (AM S pick (SatM.enc k φ, pad (eM S pick (SatM.enc k φ)))) (q * ((SatM.enc k φ).length + 2 ^ eM S pick (SatM.enc k φ) + 1) ^ q) := hM (SatM.enc k φ)
  rw [hT.correct k n φ hk hm1 hφ hocc (pad _) (by simp [pad])] at hx
  obtain ⟨ev⟩ := hx
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  have hX : 1 ≤ expM k φ.length := le_trans (by norm_num) (VariableBound.Paper.two_le_expM hk hm)
  have hE : (eM S pick (SatM.enc k φ) : ℝ) ≤ G * expM k φ.length :=
    (hG k n φ hk hm1 hφ hocc).trans (mul_le_mul_of_nonneg_left (VariableBound.Paper.shiftM_le k hm) (by positivity))
  have hL : 1 ≤ (SatM.enc k φ).length := by
    simp only [SatM.enc, List.length_append, List.length_cons]
    omega
  exact steps_le_of_exponent_le q G hX hE hL

/-- Item (5) for every solver: some machine computes the function for the bound in m on it, and
every machine that does meets the bound in m. -/
theorem boundInMOnEverySolver : BoundInMOnEverySolver := by
  intro Idx _ S e C₀ Q hS a ha
  have hT := topM_of_sqrt Q hS ha
  refine ⟨?_, meetsBoundInM_of_topM hT⟩
  obtain ⟨N, q, -, hfin, hN, -⟩ := hT.machine
  exact ⟨N, q, hfin, hN⟩

/-- Both bounds from one algorithm for cliques, from the chain for every solver and item (5) for
every solver. -/
theorem bothBounds_of (hOn : RouteOnEverySolver) (hInM : BoundInMOnEverySolver) : BothBoundsOnEverySolver := by
  intro Idx _ S e C₀ Q hS num hnum
  obtain ⟨n₀, hn₀⟩ := hOn Idx S e C₀ Q hS num hnum
  refine ⟨n₀, fun a ha => ?_⟩
  obtain ⟨hex, hall⟩ := hInM Idx S e C₀ Q hS a ha
  exact ⟨hall, hn₀ a ha _ _ hex hall⟩

end MainRoute
