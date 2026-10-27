/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GivenStatement
public import Printed.LevelFrom
public import Printed.Count
import Mathlib.Tactic

/-! # The three statements of GivenStatement.lean

* `stOnGiven`: the count of operations is `Printed.stOnProcedures` for the procedures with the
  oracle built in, read as own steps plus queries (`QueryMachines.stClose`,
  `Printed.networkOn_close`); the polynomial-time steps are `Printed.networkOn_poly`;
* `stGridGiven`: `Printed.grid_isNetwork_of` and the certificates of the four procedures `gridProcs`
  (`gridProcs_poly`);
* `stFormulaGiven`: `Printed.formula_isNetwork` and `Printed.formulaProcs_keeps`;
* `onClosed`, `onSteps`: `stOnGiven` read for the step machine with the oracle built in, and for
  procedures that are step machines. -/

public section

namespace Given

open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed

variable {Q A C : Type}

/-- Step machines with polynomial-time steps and numbers in unary, as procedures that ask nothing. -/
theorem ofProcs_poly [Enc C] (Np : Procs C) (h : Np.Keeps) (hP : Unary Np.P) (hB : Unary Np.B) : PolyTimeProcs (ofProcs Np) := by
  obtain ⟨i1⟩ := h.mem
  obtain ⟨i2⟩ := h.W
  obtain ⟨i3⟩ := h.Ψ
  obtain ⟨i4⟩ := h.f
  exact ⟨hP, hB, h.len, h.cap, ⟨IsPolyQ.lift _⟩, ⟨IsPolyQ.lift _⟩, ⟨IsPolyQ.lift _⟩, ⟨IsPolyQ.lift _⟩⟩

/-- **Lemma 1, applied to a network given in the sense of `IsGivenNetwork`.** -/
theorem stOnGiven : StOnGiven := by
  intro NM C₁ g K e hNM Q A C _ _ _ _ _ Np O c N P B τ S h
  refine ⟨fun hN => networkOn_poly g NM Np hN h.2.P h.2.B h.2.len h.2.cap h.2.mem h.2.W h.2.Ψ h.2.f, ?_⟩
  obtain ⟨T, hT1, hT2⟩ := stOnProcedures NM C₁ g K e hNM C (Np.close O) c N P B τ S h.1
  refine ⟨T, (stClose _ _ _ _ _ _ _ _ _ _).1 ?_, hT2⟩
  rw [networkOn_close]
  exact hT1

/-- The four procedures of the row network and the column network of ι have polynomial-time steps,
and their numbers are given in unary. -/
theorem gridProcs_poly (g : ℕ) (tr : Bool) : PolyTimeProcs (gridProcs g tr) := by
  have hl := Printed.lamOf_unary
  have hb := bitsOf_unary
  have hl1 : Unary fun c : (List Unit × List Unit) × ℕ => c.1.1.length := hl.comp (h := fun c : (List Unit × List Unit) × ℕ => c.1) PolyT.id'.fst
  have hb1 : Unary fun c : (List Unit × List Unit) × ℕ => c.1.2.length := hb.comp (h := fun c : (List Unit × List Unit) × ℕ => c.1) PolyT.id'.fst
  refine ⟨?_, ?_, ?_, ?_, ?_, sideWQ_poly g tr, ?_, ?_⟩
  · exact (Unary.const (g ^ 3)).mul hl1
  · exact (((Unary.const g).mul hb1).add ((Unary.const (g ^ 2)).mul hl1)).add (Unary.const 1)
  · exact (Unary.const (nMemb g g tr * (g * g))).mul (hl.comp (h := fun p : ((List Unit × List Unit) × ℕ) × ℕ => p.1.1) PolyT.id'.fst.fst)
  · exact CertGridG.capG_unary Eight.stKeeps (Unary.const g) (Unary.const g) (PolyT.const tr) (Unary.const 0)
      (hl.comp (h := fun p : ((List Unit × List Unit) × ℕ) × ℕ × ℕ => p.1.1) PolyT.id'.fst.fst) PolyT.id'.fst.snd PolyT.id'.snd.fst PolyT.id'.snd.snd
  · have i0 := IsPolyT.const (α := Unit) true
    have i1 := IsPolyT.mapIn (M := (Stepped.const true : Stepped Unit Bool)) (f := fun _ : ((List Unit × List Unit) × ℕ) × WQ => ()) (by fun_prop)
    exact ⟨IsPolyQ.lift _⟩
  · have i0 : IsPolyT (Stepped.ofFun fun x : ((List Unit × List Unit) × ℕ) × PsiQ => gridPsi g tr x.1.1.1.length x.1.2 x.2) := IsPolyT.ofFun (stPsiPoly g tr (List Unit × List Unit) (fun c => c.1.length) hl)
    exact ⟨IsPolyQ.lift _⟩
  · have i0 : IsPolyT (Stepped.ofFun fun x : ((List Unit × List Unit) × ℕ) × FQ => gridFf eightF [] g g tr 0 x.1.1.1.length x.1.2 x.2) := IsPolyT.ofFun (Eight.Level.Cert.factor_polyT (lam := fun c : List Unit × List Unit => c.1.length) Eight.stKeeps g tr hl)
    exact ⟨IsPolyQ.lift _⟩

/-- **«Both networks satisfy Definition 2 with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the
role of B, and with τ = poly(B + λ)»**, Definition 2 being `IsGivenNetwork`. -/
theorem stGridGiven : StGridGiven := by
  intro g hg
  obtain ⟨a, ha⟩ := grid_isNetwork_of stAskServes g hg
  exact ⟨a, fun tr c lam B W y h1 h2 h3 h4 h5 => ⟨ha tr c lam B W y h1 h2 h3 h4 h5, gridProcs_poly g tr⟩⟩

/-- **Section 6, «Definition 2 holds»**, of the network of Φ, Definition 2 being `IsGivenNetwork`. -/
theorem stFormulaGiven : StFormulaGiven := fun g hg k Φ =>
  ⟨formula_isNetwork hg k Φ, ofProcs_poly _ (formulaProcs_keeps g k) (satProcs_keepsP g k).P (Unary.const 1)⟩

/-- `stOnGiven`, the count of operations, read for the step machine with the oracle built in. -/
theorem onClosed {NM : NetMachine} {C₁ g K : ℕ} {e : ℝ} (hNM : ComputesNetworks NM C₁ g K e) [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] {Np : ProcsQ Q A C} {O : Q → Option A} {c : C} {N : Net g} {P B τ S : ℕ}
    (h : IsGivenNetwork Np O c N P B τ S) :
    ∃ T : ℕ, (networkOnSteps g NM (Np.close O)).Runs c T (size c + C₁ * (P + B) ^ C₁ + S + 4) N.value ∧
      (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁) * τ := by
  obtain ⟨T, h1, h2⟩ := (stOnGiven NM C₁ g K e hNM Q A C Np O c N P B τ S h).2
  refine ⟨T, ?_, h2⟩
  rw [← networkOn_close]
  exact (stClose _ _ _ _ _ _ _ _ _ _).2 h1

/-- `stOnGiven` for procedures that are step machines: polynomial-time steps of the step machine
`networkOnSteps g NM Np` and the number of its steps, in one conclusion. -/
theorem onSteps {NM : NetMachine} {C₁ g K : ℕ} {e : ℝ} (hNM : ComputesNetworks NM C₁ g K e) [HasSize C] [Enc C] [Carried C] {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
    (h : IsGivenNetwork (ofProcs Np) noTable c N P B τ S) :
    (NM.PolyTimeSteps → Nonempty (IsPolyT (networkOnSteps g NM Np))) ∧
    ∃ T : ℕ, (networkOnSteps g NM Np).Runs c T (size c + C₁ * (P + B) ^ C₁ + S + 4) N.value ∧
      (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁) * τ := by
  refine ⟨fun hN => ?_, onClosed hNM h⟩
  obtain ⟨i⟩ := (stOnGiven NM C₁ g K e hNM Unit Unit C (ofProcs Np) noTable c N P B τ S h).1 hN
  have hc : (networkOn g NM (ofProcs Np)).close noTable = networkOnSteps g NM Np := networkOn_close g NM (ofProcs Np) noTable
  rw [← hc]
  exact ⟨close_isPolyT _ (by unfold noTable; fun_prop)⟩

end Given
