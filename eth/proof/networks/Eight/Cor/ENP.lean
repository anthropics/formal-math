/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBoundStatement
public import CircuitLowerBoundInfinitelyOftenStatement
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
public import CircuitLowerBound.Closed
public import CircuitLowerBound.Inf
import ToTuring.Machine.EndTM
import Mathlib.Tactic

/-! # Section 7, the circuit lower bound for E^NP: E^NP does not have circuits of linear size; the algorithm for satisfiability as a parameter

The proof of proof/consequences/CircuitLowerBound/ uses the algorithm for satisfiability at one
place, the interface statement `CircuitLowerBound.StAlg`: a machine that, given 1^m 0 y, reads y as
a circuit and tests by the procedure for #3-SAT whether the assignment that the circuit computes
violates some clause of the formula `Phi m`. The machine cut into steps is
`CircuitLowerBound.Alg.algo E F fb`, with the procedure E as a parameter. In this development E is
the machine of the proof of Corollary 6 at width 3, which runs CLIQUE(ℓ) of Algorithm 1; here E is
left open, and
`StAlg` is proved from a procedure that is a parameter (`stAlg_of`). Everything else of
proof/consequences/CircuitLowerBound/ (the language, the tables, the chains, the circuits, the two
forms of E^NP) is used as it
is and does not use Algorithm 1 or Lemma 2.

Different from the paper: the paragraph «Circuit lower bounds» in Section 7 derives the statement
from «ETH is false» by citing a theorem of Williams (see also Jahanjou, Miles and Viola). In
proof/consequences/CircuitLowerBound/ the implication is proved, for the algorithm of this
development, not for an arbitrary algorithm for 3-SAT. -/

public section

namespace Eight

open ENP Groundwork Turing CircuitLowerBound

/-- The interface statement `CircuitLowerBound.StAlg`, from a procedure for #3-SAT that is a
parameter and the statements on the formula, on circuits as data, on the schedule and on the last
place of a chain. -/
theorem stAlg_of (hEng : StEngine) (h1 : StForm) (h2 : StNorm) (h3 : StCertSched) (h4 : StFlip) : StAlg := by
  intro c₀
  obtain ⟨a₀, g, F, hFp, hF⟩ := h1
  obtain ⟨fb, hbp, hb⟩ := h4
  have hF' : Alg.FormOK a₀ g F := hF
  have hb' : Alg.FlipOK fb := hb
  have hδ : (0 : ℝ) < 1 / (32 * ((3 * c₀ + a₀ + 1 : ℕ) : ℝ)) := by positivity
  obtain ⟨E, ⟨hEp⟩, cE, hE⟩ := hEng 3 (by norm_num) _ hδ
  have hE' : Alg.EngineOK E cE (1 / (32 * ((3 * c₀ + a₀ + 1 : ℕ) : ℝ))) := hE
  have := hEp
  have := Alg.isPolyT_algo (E := E) h3 hFp hbp
  obtain ⟨N, q, hfin, hN⟩ := PaddedDescent.exists_tm' (Alg.algo E F fb)
  refine ⟨N, hfin, ?_, fun e => ?_⟩
  · rintro m T ⟨y, ⟨ev⟩⟩
    obtain ⟨T', b, hr, hbi, -⟩ := Alg.runs_algo (fb := fb) hE' hF' (unary m ++ y)
    obtain ⟨ev'⟩ := hN _ _ _ _ hr
    have h5 := Alg.outputs_unique ev ev'
    have h6 : b = true := by
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h5
      exact (N.outputAlphabet.symm.injective h5).symm
    have h7 := Alg.sat_Phi_of_pre hF' hb' _ (hbi.1 h6)
    rwa [Parse.ones_unary_append] at h7
  · obtain ⟨m₀, hm₀⟩ := Time.exists_threshold q cE c₀ a₀ (g e)
    refine ⟨max m₀ 1, fun m hm he hpos C hCl hC => ?_⟩
    obtain ⟨y, hy, hns, hNv⟩ := Alg.exists_guess hF' hb' h2 (le_of_max_le_right hm) hpos C hC
    obtain ⟨T, b, hr, hbi, hT⟩ := Alg.runs_algo (fb := fb) hE' hF' (unary m ++ y)
    obtain rfl : b = true := hbi.2 hns
    obtain ⟨ev⟩ := hN _ _ _ _ hr
    rw [he] at hNv
    have h8 := hm₀ m (le_of_max_le_left hm) C.length _ T hCl hNv hT
    have h9 : (unary m ++ y).length = m + 1 + ((m + C.length) + 1 + C.length * (4 + 2 * (m + C.length))) := by
      rw [List.length_append, hy]
      simp [unary]
    rw [← h9] at h8
    exact ⟨y, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans h8⟩⟩⟩

end Eight
