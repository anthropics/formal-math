/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Top.Defs
public import VariableBound.Paper.Decide
public import ClauseBound.Inst.Half

/-! # Two statement forms for the bound in n: definitions

Two definitions for statements about the Lean proof of the bound in n (Appendix D):
* `TiedOut A e post rn rm`: ONE machine and ONE constant such that the machine, on EVERY bit string
  x, halts with `post` of `A` at x and a pad of 2^(e x) units, within C·(|x| + 2^(e x) + 1)^C steps,
  and, on the code of (k, φ), halts
  with `post` of the number of satisfying assignments within the three bounds of
  `SatM.CountUniformInRate`, each under its conditions. With `post` the identity the last three
  clauses are `SatM.CountUniformInRate` for that machine.
* `StEndS R`: hypotheses on a solver for cliques with a sequence of levels, a precision `slU` and
  the rates, with a conclusion R that may name the solver, the function `pick` of its sequence of
  levels and the precision `slU`. -/

@[expose] public section

namespace VariableBound

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound.Decide

/-- One machine, finite alphabets, one constant C. On every bit string x the machine halts with
`post (A (x, pad))`, where the pad has 2^(e x) units, within C·(|x| + 2^(e x) + 1)^C steps. On the
code of (k, φ), k ≥ 1, φ a k-CNF on n
variables, it halts with `post` of the number of satisfying assignments in n + 1 bits: within
C·2^{C·k²·n·rn(n)} steps if n ≥ 1; within C·2^{C·k·m·rm(m)} steps if all variables occur and m ≥ 1;
within
C·2^{C·min(k²·n·rn(n), k·m·rm(m))} steps if all variables occur and n ≥ 1. -/
def TiedOut (A : List Bool × U → List Bool) (e : List Bool → ℕ) (post : List Bool → List Bool) (rn rm : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    (∀ x : List Bool, Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some ((post (A (x, pad (e x)))).map M.outputAlphabet.invFun)) (C * (x.length + 2 ^ e x + 1) ^ C))) ∧
    (∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ →
      Nonempty (TM2OutputsInTime M.tm ((SatM.enc k φ).map M.inputAlphabet.invFun) (some ((post (SatK.binary n (SatK.numSat φ))).map M.outputAlphabet.invFun)) (SatM.boundNK rn C k n))) ∧
    (∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
      Nonempty (TM2OutputsInTime M.tm ((SatM.enc k φ).map M.inputAlphabet.invFun) (some ((post (SatK.binary n (SatK.numSat φ))).map M.outputAlphabet.invFun)) (SatM.bound rm C k φ.length))) ∧
    ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ → SatM.AllOccur φ →
      Nonempty (TM2OutputsInTime M.tm ((SatM.enc k φ).map M.inputAlphabet.invFun) (some ((post (SatK.binary n (SatK.numSat φ))).map M.outputAlphabet.invFun)) (SatM.boundBothK rn rm C k n φ.length))

/-- Hypotheses on a solver S for cliques with a sequence of levels, a precision `slU` and two rates,
with the conclusion R for S, the function `pick` of its sequence of levels, `slU` and the two rates. -/
def StEndS (R : ∀ (Idx : Type) [Enc Idx], Solver Idx → (U → U × Idx) → (U → U) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ), PolyT slU →
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∀ (rn rm : ℕ → ℝ) (c₁ : ℕ), (∀ n : ℕ, 1 ≤ n → 1 / (c₁ * Real.logb 2 ((n : ℝ) + 2) ^ c₁) ≤ rn n) →
  (∀ n : ℕ, S.K (Q.idx 0) ^ 17 ≤ n → e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ) ≤ c₁ * rn n) → FallBack rn →
  (∀ m : ℕ, 1 ≤ m → 1 / (c₁ * Real.logb 2 ((m : ℝ) + 2) ^ c₁) ≤ rm m) →
  (∀ m : ℕ, S.K (Q.idx 0) ^ 9 ≤ m → e (Q.pick (root9 m)).1.length ≤ c₁ * rm m) → (∀ n, 0 ≤ rn n) → (∀ m, 0 ≤ rm m) → R Idx S Q.pick slU rn rm

end VariableBound
