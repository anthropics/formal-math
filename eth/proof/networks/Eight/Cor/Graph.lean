/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblemsStatement
public import PaperSentencesStatement
public import Eight.Cor.Defs
public import Eight.Level.End
public import WidthK.Top.Poly
public import KSatStatement
public import ToTuring.PolyT
public import ToTuring.Machine.EndTM
public import WidthK.Top.EndLemmas
public import WidthK.Decode
public import SparsifyWidthK.DefsProg
public import StepMachines.Prog.BruteE
public import StepMachines.Prog.NetProg
public import StepMachines.Prog.NetRun
public import StepMachines.Prog.NetVal
public import StepMachines.Math.RebalanceArith
public import StepMachines.Prog.GridLoop
public import StepMachines.Prog.SidePresents
public import StepMachines.Prog.Sat
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import StepMachines.Math.SparsifyCount
public import NetworkStatements
public import Mathlib.Algebra.Polynomial.Coeff
public import ToTuring.Poly.Spec
public import ToTuring.Poly.Brute
public import ToTuring.Poly.NetFun
public import ToTuring.Poly.Basic
public import ToTuring.Poly.Range
public import ToTuring.Poly.Comb
public import ToTuring.Poly.GridSide
public import ToTuring.Poly.Count
public import ToTuring.Poly.Sat
public import CountKSat.Interfaces
public import CountKSat.EndLemmas
public import GraphProblems.Engine
public import GraphProblems.Sized
public import GraphProblems.ColorTM
import GraphProblems.Read
import GraphProblems.Sets
import GraphProblems.Color
import GraphProblems.Blocks
import GraphProblems.DomTree
import GraphProblems.Cert
import GraphProblems.SetTM
import GraphProblems.Interfaces
import GraphProblems.Host
import CountKSat.Walk
import all StepMachines.Prog.Sat
import all StepMachines.Prog.Decode
import all WidthK.Top.Sat
import Mathlib.Tactic

/-! # Section 7, Corollary 7: the machine for colorings on a procedure E that is a parameter

As in the paper, Corollary 7 applies Corollary 6 to formulas made from the graph. The procedure for #k-SAT
enters the proofs of proof/consequences/GraphProblems/ at two places: the machine
`GraphProblems.sized b E`, which counts the satisfying assignments with exactly s true
variables by calls of E, and the machine for colorings, one call of E. Here the machine for
colorings is proved for a procedure E that is a parameter (`color_counts`; the lines are those of
proof/consequences/GraphProblems/ColorTM.lean), and E is
then the machine of Corollary 6 on CLIQUE(ℓ) of Algorithm 1. Everything else (the formulas, their
counts, the tree for dominating sets, the readers, the host) is that of
proof/consequences/GraphProblems/ and does not use Algorithm 1 or Lemma 2.

-/

@[expose] public section

namespace Eight

open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat GraphProblems Finset Turing

/-! ### Colorings -/

/-- The machine for colorings on a procedure E that is a parameter: the reader
`GraphProblems.readC k`, which makes (n·k in unary, the formula of the colorings), followed by one
call of E. If E serves for width max(k, 2) with the exponent δ/k, the machine returns the
number of satisfying assignments of the formula, in n·k + 1 bits, within c'·2^{δn} steps, c' = c·k^c +
c. -/
theorem color_counts (hR1 : StRead1) (hSh : StShapeColor) (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} {E : Stepped (List Unit × Fml) (List Bool)} {c : ℕ} (hc : Serves E (max k 2) (δ / k) c)
    (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ T : ℕ, (Stepped.mapIn (readC k) E).Runs (code G) T ((c * k ^ c + c) * (n + 2) ^ (c * k ^ c + c)) (SatK.binary (n * k) (cntN (n * k) (colorF k n (matrix G)))) ∧
      (T : ℝ) ≤ ((c * k ^ c + c : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨T, hr, hT⟩ := hc (n * k) (colorF k n (matrix G)).dedup (fun C hC => hSh k n (matrix G) C (List.mem_dedup.1 hC)) (List.nodup_dedup _)
  have hread : readC k (code G) = (List.replicate (n * k) (), (colorF k n (matrix G)).dedup) := by
    simp [readC, hR1 n G]
  rw [← hread] at hr
  have hrun := Stepped.mapIn_runs hr
  rw [cntN_dedup] at hrun
  have hc1 : c ≤ c * k ^ c := Nat.le_mul_of_pos_right c (Nat.pow_pos hk)
  refine ⟨T, hrun.mono le_rfl ?_, hT.trans ?_⟩
  · calc c * (n * k + 2) ^ c ≤ c * (k * (n + 2)) ^ c := by
          refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ c)
          nlinarith
      _ = c * k ^ c * (n + 2) ^ c := by rw [mul_pow, mul_assoc]
      _ ≤ (c * k ^ c + c) * (n + 2) ^ (c * k ^ c + c) :=
          Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))
  · have e1 : δ / k * ((n * k : ℕ) : ℝ) = δ * n := by
      push_cast
      field_simp
    rw [e1]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast hc1.trans (Nat.le_add_right _ _)

end Eight
