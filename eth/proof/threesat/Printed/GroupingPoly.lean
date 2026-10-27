/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Programs
public import QueryMachines.Poly
public import Eight.ViaGrouping.Keeps
public import Exits.Poly
import Mathlib.Tactic

/-! # The machine of Lemma 1 has polynomial-time steps

The model is proof/networks/Eight/ViaGrouping/Keeps.lean: the plain functions are those defined
there and their certificates are taken from there; the machines are put together with the
certificates of proof/machines/QueryMachines/Poly.lean.
* `asked_keepsP`: the numbers P, P_a, c_{a,b} are read off the input, where they stand in unary;
  each of the four procedures is one query;
* `tableQ_poly`: one entry W̃_γ(Θ);
* `stGroupingPoly`: the search (`Exits.IsPolyT.firstUntil`), L and B' in unary, the machine M with
  its queries answered by `tableQ` (`QueryMachines.stPolySubst`). -/

public section

namespace Printed

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

/-- «Is z ∈ S_a?», asked. -/
theorem asked_mem_poly : asked.mem.PolyTimeSteps :=
  have := IsPolyQ.query (Q := NetQuery) (A := ℤ) (h := fun x : NetInput × WQ => (Sum.inl x.2 : NetQuery)) (by fun_prop)
  ⟨IsPolyQ.mapOut _ (by fun_prop : PolyT fun v : ℤ => decide (v ≠ 0))⟩

/-- W_a(z), asked. -/
theorem asked_W_poly : asked.W.PolyTimeSteps := ⟨IsPolyQ.query (Q := NetQuery) (A := ℤ) (h := fun x : NetInput × WQ => (Sum.inr (Sum.inl x.2) : NetQuery)) (by fun_prop)⟩

/-- Ψ_{a,b}(z, z'), asked. -/
theorem asked_Ψ_poly : asked.Ψ.PolyTimeSteps := ⟨IsPolyQ.query (Q := NetQuery) (A := ℤ) (h := fun x : NetInput × PsiQ => (Sum.inr (Sum.inr (Sum.inl x.2)) : NetQuery)) (by fun_prop)⟩

/-- f_{a,b}(z, θ), asked. -/
theorem asked_f_poly : asked.f.PolyTimeSteps := ⟨IsPolyQ.query (Q := NetQuery) (A := ℤ) (h := fun x : NetInput × FQ => (Sum.inr (Sum.inr (Sum.inr x.2)) : NetQuery)) (by fun_prop)⟩

/-- The numbers of Definition 2(iii) stand in the input in unary, and the step machines under the
four procedures have polynomial-time steps. -/
theorem asked_keepsP : KeepsP asked.under := by
  obtain ⟨i1⟩ := asked_mem_poly
  obtain ⟨i2⟩ := asked_W_poly
  obtain ⟨i3⟩ := asked_Ψ_poly
  obtain ⟨i4⟩ := asked_f_poly
  exact
    { keeps :=
        { len := Unary.of_length (w := fun p : NetInput × ℕ => p.1.2.1.getD p.2 []) (by fun_prop)
          cap := Unary.of_length (w := fun p : NetInput × ℕ × ℕ => (p.1.2.2.getD p.2.1 []).getD p.2.2 []) (by fun_prop)
          mem := ⟨IsPolyQ.under asked.mem⟩
          W := ⟨IsPolyQ.under asked.W⟩
          Ψ := ⟨IsPolyQ.under asked.Ψ⟩
          f := ⟨IsPolyQ.under asked.f⟩ }
      P := Unary.of_length (w := fun c : NetInput => c.1.1) (by fun_prop) }

/-- One entry W̃_γ(Θ) has polynomial-time steps, if the four procedures have and P_a, c_{a,b} are
given in unary. -/
theorem tableQ_poly {Q A C : Type} [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] (K g : ℕ) (Np : ProcsQ Q A C) (h : Np.under.toPaperNetwork.Keeps)
    [IsPolyQ Np.mem] [IsPolyQ Np.W] [IsPolyQ Np.Ψ] [IsPolyQ Np.f] : (tableQ K g Np).PolyTimeSteps := by
  have m1 := IsPolyQ.mapIn (qW_polyT K g h) Np.mem
  have m2 := IsPolyQ.mapIn (qW_polyT K g h) Np.W
  have m3 := IsPolyQ.mapIn (qMb_polyT K g h) Np.mem
  have m4 := IsPolyQ.mapIn (qPsi_polyT K g h) Np.Ψ
  have m5 := IsPolyQ.mapIn (qF_polyT K g h) Np.f
  have w : IsPolyQ (wQ K g Np) := IsPolyQ.gated _ _
  have p0 := IsPolyQ.gated (QueryMachine.mapIn (qMb K g Np.under) Np.mem) (QueryMachine.mapIn (qPsi K g Np.under) Np.Ψ)
  have p : IsPolyQ (psiQ K g Np) := IsPolyQ.gated _ _
  have f : IsPolyQ (fQ K g Np) := IsPolyQ.gated _ _
  have t1 := IsPolyQ.ite (isPsi_polyT K g) (psiQ K g Np) (fQ K g Np)
  have t2 := IsPolyQ.ite (isW_polyT g) (wQ K g Np) (QueryMachine.ite (isPsi K g) (psiQ K g Np) (fQ K g Np))
  have t3 : IsPolyQ (QueryMachine.const 1 : QueryMachine Q A ((X0 C × ℕ) × ℕ) ℤ) := IsPolyQ.const 1
  have t : IsPolyQ (termQ K g Np) := IsPolyQ.ite (isOne_polyT K g) _ _
  have s1 := IsPolyQ.prodRange (termQ K g Np) (nPairs_polyT g)
  have s2 := IsPolyQ.sumRange (QueryMachine.prodRange (nPairs g) (termQ K g Np)) (nStates_polyT K g h)
  have s3 : IsPolyQ (QueryMachine.const 0 : QueryMachine Q A (X0 C) ℤ) := IsPolyQ.const 0
  exact ⟨IsPolyQ.ite (validB_polyT K g h) _ _⟩

/-- B' in unary is computed in polynomial time from the input. -/
theorem bitsOut_unary (K g : ℕ) : Unary fun cx : NetInput × ℕ => bitsOut K g (asked.P cx.1) (asked.B cx.1) := by
  have hP : Unary fun cx : NetInput × ℕ => asked.P cx.1 := Unary.of_length (w := fun cx : NetInput × ℕ => cx.1.1.1) (by fun_prop)
  have hB : Unary fun cx : NetInput × ℕ => asked.B cx.1 := Unary.of_length (w := fun cx : NetInput × ℕ => cx.1.1.2) (by fun_prop)
  refine Unary.of_le (g := fun cx => (2 * (g * asked.P cx.1) + (K - 1)) + g ^ 2 * asked.B cx.1) ?_ ?_ fun cx => ?_
  · exact (((Unary.const 2).mul ((Unary.const g).mul hP)).add (Unary.const (K - 1))).add ((Unary.const (g ^ 2)).mul hB)
  · have h1 := hP.poly
    have h2 := hB.poly
    unfold bitsOut
    fun_prop (disch := assumption)
  · unfold bitsOut
    exact Nat.add_le_add_right (Nat.div_le_self _ _) _

/-- Cutting a setting z_w into its K − 1 strings of λ bits is computed in polynomial time. -/
theorem toLists_polyT {C : Type} [Enc C] (K : ℕ) {lam : C → ℕ} (h : PolyT lam) : PolyT fun y : C × TableQuery => (y.1, toLists K (lam y.1) y.2) := by
  unfold toLists copyAt place
  fun_prop

/-- **The machine of Lemma 1 has polynomial-time steps if M has.** -/
theorem stGroupingPoly : StGroupingPoly := by
  intro K g M hM
  have hkp := asked_keepsP
  have hk := keeps_toPaperNetwork hkp.keeps
  obtain ⟨i1⟩ := asked_mem_poly
  obtain ⟨i2⟩ := asked_W_poly
  obtain ⟨i3⟩ := asked_Ψ_poly
  obtain ⟨i4⟩ := asked_f_poly
  obtain ⟨hT⟩ := tableQ_poly K g asked hk
  have hq : PolyT fun y : (NetInput × ℕ) × TableQuery => (y.1, toLists K (lamP K g asked.under y.1) y.2) := toLists_polyT K (lamP_polyT K g hkp)
  have n1 := IsPolyQ.mapIn hq (tableQ K g asked)
  obtain ⟨hs⟩ := stPolySubst _ _ _ _ _ _ _ M (QueryMachine.mapIn (fun y : (NetInput × ℕ) × TableQuery => (y.1, toLists K (lamP K g asked.under y.1) y.2)) (tableQ K g asked)) hM ⟨n1⟩
  have u1 : PolyT fun cx : NetInput × ℕ => unary (lamP K g asked.under cx) := lamP_unary K g hkp
  have u2 : PolyT fun cx : NetInput × ℕ => unary (bitsOut K g (asked.P cx.1) (asked.B cx.1)) := bitsOut_unary K g
  have hin : PolyT fun cx : NetInput × ℕ => (cx, (unary (lamP K g asked.under cx), unary (bitsOut K g (asked.P cx.1) (asked.B cx.1)))) := by fun_prop
  have n2 := IsPolyQ.mapIn hin (M.subst (QueryMachine.mapIn (fun y : (NetInput × ℕ) × TableQuery => (y.1, toLists K (lamP K g asked.under y.1) y.2)) (tableQ K g asked)))
  have := IsPolyT.ofFun (goodP_polyT K g hkp)
  have sr : IsPolyT (Exits.search K g asked.under) := Exits.IsPolyT.firstUntil (nCol_polyT K g) (by change PolyT fun b : Bool => b; fun_prop)
  have sl : IsPolyQ (QueryMachine.lift (Exits.search K g asked.under) : QueryMachine NetQuery ℤ NetInput (Option ℕ)) := IsPolyQ.lift _
  exact ⟨IsPolyQ.optBind _ _ zeroOf_polyT⟩

end Printed
