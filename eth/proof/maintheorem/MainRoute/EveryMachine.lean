/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainRoute.Defs
import RecursionWithPieces.Main
import GeneralPieces.ThmRunningTime
import GeneralPieces.Num.Asymptotic
import VariableBound.Paper.Rename.Time
import VariableBound.Paper.Arith

/-! # The bound in m of the Main Theorem, for every machine that computes the named function

`boundInMForEveryMachine`: an ARBITRARY machine that computes the function `AM` with the exponent
`eM` (`PairsToBound.Computes`) on the recursion of Appendix A meets the bound in m. The proof uses
nothing of the machine but what it puts out and the bound q·(|x| + 2^(exponent) + 1)^q on its steps,
and of the function three facts from `GeneralPieces.Tied.TopM` (part (c) of Theorem A for the named
programs): it is
right, its exponent is O(k·m/√(log m)), and a machine that computes it exists. (Theorem D (a) in the
same form is `RecursionToBound.thmVariablesAForEveryMachine`.) -/

public section

namespace MainRoute

open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)

/-! ### The bound in m -/

/-- The numbers: if E ≤ G·X with X ≥ 1, then q·(L + 2^E + 1)^q ≤ ⌊2^(C·X)⌋ + C·L^C for L ≥ 1, with C =
2q + 2q(G + 1) + q·4^q. -/
theorem steps_le_of_exponent_le (q G : ℕ) {E L : ℕ} {X : ℝ} (hX : 1 ≤ X) (hE : (E : ℝ) ≤ G * X) (hL : 1 ≤ L) :
    q * (L + 2 ^ E + 1) ^ q ≤ ⌊(2 : ℝ) ^ (((2 * q + 2 * q * (G + 1) + q * 4 ^ q : ℕ) : ℝ) * X)⌋₊ + (2 * q + 2 * q * (G + 1) + q * 4 ^ q) * L ^ (2 * q + 2 * q * (G + 1) + q * 4 ^ q) := by
  have h0 := VariableBound.Rename.steps_split q L 0 E
  have h1 : q * 2 ^ q * (L + 1) ^ q ≤ (2 * q + 2 * q * (G + 1) + q * 4 ^ q) * L ^ (2 * q + 2 * q * (G + 1) + q * 4 ^ q) :=
    (VariableBound.Rename.poly_le q hL).trans (VariableBound.Rename.poly_mono (by omega) hL)
  have h2 : 2 * q * (0 + 2 ^ E + 1) ^ (2 * q) ≤ ⌊(2 : ℝ) ^ (((2 * q + 2 * q * (G + 1) + q * 4 ^ q : ℕ) : ℝ) * X)⌋₊ := by
    refine Nat.le_floor ?_
    have a1 : 0 + 2 ^ E + 1 ≤ 2 ^ (E + 1) := by
      have : 1 ≤ 2 ^ E := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    have a2 : 2 * q * (0 + 2 ^ E + 1) ^ (2 * q) ≤ 2 * q * 2 ^ ((E + 1) * (2 * q)) := by
      rw [pow_mul 2 (E + 1) (2 * q)]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left a1 _)
    have a3 : ((2 * q * (0 + 2 ^ E + 1) ^ (2 * q) : ℕ) : ℝ) ≤ ((2 * q : ℕ) : ℝ) * (2 : ℝ) ^ (((E + 1) * (2 * q) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast a2
    have a4 : ((2 * q : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((2 * q : ℕ) : ℝ) * X) := VariableBound.Paper.natCast_le_two_rpow (2 * q) hX
    have a5 : (((E + 1) * (2 * q) : ℕ) : ℝ) ≤ ((2 * q * (G + 1) : ℕ) : ℝ) * X := by
      push_cast
      have : (E : ℝ) + 1 ≤ (G + 1) * X := by nlinarith
      have hq : (0 : ℝ) ≤ 2 * q := by positivity
      nlinarith
    have a6 : (2 : ℝ) ^ (((E + 1) * (2 * q) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((2 * q * (G + 1) : ℕ) : ℝ) * X) := Real.rpow_le_rpow_of_exponent_le one_le_two a5
    have a7 : (2 : ℝ) ^ (((2 * q : ℕ) : ℝ) * X) * (2 : ℝ) ^ (((2 * q * (G + 1) : ℕ) : ℝ) * X) ≤ (2 : ℝ) ^ (((2 * q + 2 * q * (G + 1) + q * 4 ^ q : ℕ) : ℝ) * X) := by
      rw [← Real.rpow_add two_pos]
      refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
      push_cast
      have : (0 : ℝ) ≤ (q : ℝ) * 4 ^ q * X := by positivity
      nlinarith
    exact a3.trans ((mul_le_mul a4 a6 (by positivity) (by positivity)).trans a7)
  omega

/-- The first sentence of Theorem A (c) at ρ = 1/√2 for every machine that computes the named
function, and there is one. -/
theorem boundInMForEveryMachine : BoundInMForEveryMachine := by
  intro c P₀ A val h
  have hT : GeneralPieces.Tied.TopM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c) (SatM.rPow (AppRunningTime.alpha' (1 / Real.sqrt 2))) := GeneralPieces.thmRunningTime_c_m_tied h
  have hα : AppRunningTime.alpha' (1 / Real.sqrt 2) = 1 / 2 := GeneralPieces.Asymptotic.alpha_half
  rw [hα] at hT
  refine ⟨?_, fun M q hM => ?_⟩
  · obtain ⟨N, q, -, hfin, hN, -⟩ := hT.machine
    exact ⟨N, q, hfin, hN⟩
  · obtain ⟨G, hG⟩ := hT.rate
    refine ⟨2 * q + 2 * q * (G + 1) + q * 4 ^ q, fun k n φ hk hφ hm hocc => ?_⟩
    have hm1 : 1 ≤ φ.length := by omega
    have hx : Outputs M (SatM.enc k φ) (AM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c) (SatM.enc k φ, pad (eM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c) (SatM.enc k φ))))
        (q * ((SatM.enc k φ).length + 2 ^ eM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c) (SatM.enc k φ) + 1) ^ q) := hM (SatM.enc k φ)
    rw [hT.correct k n φ hk hm1 hφ hocc (pad _) (by simp [pad])] at hx
    obtain ⟨ev⟩ := hx
    refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
    have hX : 1 ≤ expM k φ.length := le_trans (by norm_num) (VariableBound.Paper.two_le_expM hk hm)
    have hE : (eM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c) (SatM.enc k φ) : ℝ) ≤ G * expM k φ.length :=
      (hG k n φ hk hm1 hφ hocc).trans (mul_le_mul_of_nonneg_left (VariableBound.Paper.shiftM_le k hm) (by positivity))
    have hL : 1 ≤ (SatM.enc k φ).length := by
      simp only [SatM.enc, List.length_append, List.length_cons]
      omega
    exact steps_le_of_exponent_le q G hX hE hL

end MainRoute
