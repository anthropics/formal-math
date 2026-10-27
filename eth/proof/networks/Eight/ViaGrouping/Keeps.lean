/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Defs
public import ToTuring.Poly.NetFun
public import ToTuring.Poly.Basic
public import ToTuring.Poly.Range
public import ToTuring.Poly.Comb

/-! # The algorithm of the proof of Lemma 1 has polynomial-time steps

A bound on the number of steps of a step machine says something only if each step is cheap. This
file shows that every step of `netAlg K g E` is computable in polynomial time (`IsPolyT`) if the
steps of the four procedures of Definition 2(iii) and of
the algorithm E for cliques are, and the numbers P_a, c_{a,b} and P are given in unary (`KeepsP`):
`stKeeps : StKeeps`.
The parts, in the order of proof/networks/Eight/ViaGrouping/Defs.lean: the plain functions `lamP`
(polynomial-time, and of polynomial size even in unary: E is given L in unary), `goodP` (one test of
a grouping, which the search counts as one step), `qMb`, `qPsi`; then
the machines `wM`, `psiP`, `fM`, `termP`, `tableM`, `searchP`. The certificates of the plain
functions that cut a setting of a group and a string Θ(γ') into their parts are those of
proof/machines/ToTuring/Poly/NetFun.lean. -/

@[expose] public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Stepped Eight.SecNetworks

variable {C : Type} [HasSize C] [Enc C] [Carried C] (K g : ℕ) {Np : Procs C}

/-! ## The plain functions -/

/-- L is computable in polynomial time. -/
theorem lamP_polyT (h : KeepsP Np) : PolyT (lamP K g Np) := by
  have hU : PolyT fun cx : C × ℕ => Uc g Np.toPaperNetwork cx.1 := PolyT.comp (Uc_unary g (keeps_toPaperNetwork h.keeps)).poly (by fun_prop)
  have hP : PolyT fun cx : C × ℕ => Np.P cx.1 := PolyT.comp h.P.poly (by fun_prop)
  unfold lamP Colouring.beta
  fun_prop (disch := assumption)

/-- L is computable in polynomial time even if written in unary, since L ≤ 1 + K·U + g·P and the
numbers c_{a,b} and P are given in unary. -/
theorem lamP_unary (h : KeepsP Np) : Unary (lamP K g Np) := by
  have hU : Unary fun cx : C × ℕ => Uc g Np.toPaperNetwork cx.1 := (Uc_unary g (keeps_toPaperNetwork h.keeps)).comp (h := fun cx : C × ℕ => cx.1) (by fun_prop)
  have hP : Unary fun cx : C × ℕ => Np.P cx.1 := h.P.comp (h := fun cx : C × ℕ => cx.1) (by fun_prop)
  refine Unary.of_le (g := fun cx => 1 + (K * Uc g Np.toPaperNetwork cx.1 + g * Np.P cx.1)) ?_ (lamP_polyT K g h) fun cx => ?_
  · exact (Unary.const 1).add (((Unary.const K).mul hU).add ((Unary.const g).mul hP))
  · have h2 := Nat.div_le_self (K * Uc g Np.toPaperNetwork cx.1 + g * Np.P cx.1) (K ^ 3)
    unfold lamP Colouring.beta
    omega

omit [HasSize C] [Carried C] in
/-- The test (G1) is computable in polynomial time. -/
theorem g1_polyT : PolyT fun cx : C × ℕ => (List.range K).all fun G => decide (K * (members K g cx.2 G).length ≤ 2 * g) := by
  have hl : PolyT fun q : (C × ℕ) × ℕ => K * (members K g q.1.2 q.2).length := by fun_prop
  exact PolyT.all (f := fun (cx : C × ℕ) G => decide (K * (members K g cx.2 G).length ≤ 2 * g)) (PolyT.decide_le hl (PolyT.const (2 * g))) (by fun_prop)

/-- The test (G2) is computable in polynomial time. -/
theorem g2_polyT (h : KeepsP Np) : PolyT fun cx : C × ℕ => (List.range K).all fun G => (List.range K).all fun G' =>
    G == G' || decide (K ^ 3 * lbLen K g Np.toPaperNetwork cx.1 cx.2 G G' ≤ K * Uc g Np.toPaperNetwork cx.1 + g * Np.P cx.1) := by
  have hk := keeps_toPaperNetwork h.keeps
  have hU : PolyT fun q : ((C × ℕ) × ℕ) × ℕ => Uc g Np.toPaperNetwork q.1.1.1 := PolyT.comp (Uc_unary g hk).poly (by fun_prop)
  have hP : PolyT fun q : ((C × ℕ) × ℕ) × ℕ => Np.P q.1.1.1 := PolyT.comp h.P.poly (by fun_prop)
  have hb : PolyT fun q : ((C × ℕ) × ℕ) × ℕ => K * Uc g Np.toPaperNetwork q.1.1.1 + g * Np.P q.1.1.1 := ((PolyT.const K).mul hU).add ((PolyT.const g).mul hP)
  have hl : PolyT fun q : ((C × ℕ) × ℕ) × ℕ => K ^ 3 * lbLen K g Np.toPaperNetwork q.1.1.1 q.1.1.2 q.1.2 q.2 :=
    (PolyT.const (K ^ 3)).mul (lbLen_polyT K g hk (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
  exact PolyT.all (f := fun (cx : C × ℕ) G => (List.range K).all fun G' =>
        G == G' || decide (K ^ 3 * lbLen K g Np.toPaperNetwork cx.1 cx.2 G G' ≤ K * Uc g Np.toPaperNetwork cx.1 + g * Np.P cx.1))
      (PolyT.all (f := fun (q : (C × ℕ) × ℕ) G' =>
          q.2 == G' || decide (K ^ 3 * lbLen K g Np.toPaperNetwork q.1.1 q.1.2 q.2 G' ≤ K * Uc g Np.toPaperNetwork q.1.1 + g * Np.P q.1.1))
        (PolyT.or' (by fun_prop) (PolyT.decide_le hl hb)) (by fun_prop)) (by fun_prop)

/-- The test of a grouping, (G1) and (G2), is computable in polynomial time. -/
theorem goodP_polyT (h : KeepsP Np) : PolyT (goodP K g Np) := PolyT.and' (g1_polyT K g) (g2_polyT K g h)

omit [Carried C] in
/-- The query (b, z_b) is computable in polynomial time. -/
theorem qMb_polyT (h : Np.toPaperNetwork.Keeps) : PolyT (qMb K g Np) := by
  unfold qMb; fun_prop (disch := assumption)

omit [Carried C] in
/-- The query ((a, b), (z_a, z_b)) is computable in polynomial time. -/
theorem qPsi_polyT (h : Np.toPaperNetwork.Keeps) : PolyT (qPsi K g Np) := by
  unfold qPsi; fun_prop (disch := assumption)

/-! ## The machines -/

/-- [z_a ∈ S_a]·W_a(z_a) has polynomial-time steps. -/
@[instance_reducible] def wM_isPolyT (h : Np.toPaperNetwork.Keeps) [IsPolyT Np.mem] [IsPolyT Np.W] : IsPolyT (wM K g Np) :=
  haveI := IsPolyT.mapIn (M := Np.mem) (qW_polyT K g h)
  haveI := IsPolyT.mapIn (M := Np.W) (qW_polyT K g h)
  gated_isPolyT _ _

/-- [z_a ∈ S_a][z_b ∈ S_b]·Ψ_{a,b}(z_a, z_b) has polynomial-time steps. -/
@[instance_reducible] def psiP_isPolyT (h : Np.toPaperNetwork.Keeps) [IsPolyT Np.mem] [IsPolyT Np.Ψ] : IsPolyT (psiP K g Np) :=
  haveI := IsPolyT.mapIn (M := Np.mem) (qW_polyT K g h)
  haveI := IsPolyT.mapIn (M := Np.mem) (qMb_polyT K g h)
  haveI := IsPolyT.mapIn (M := Np.Ψ) (qPsi_polyT K g h)
  haveI := gated_isPolyT (mapIn (qMb K g Np) Np.mem) (mapIn (qPsi K g Np) Np.Ψ)
  gated_isPolyT _ _

/-- [z_a ∈ S_a]·f_{a,b}(z_a, θ_{a,b}) has polynomial-time steps. -/
@[instance_reducible] def fM_isPolyT (h : Np.toPaperNetwork.Keeps) [IsPolyT Np.mem] [IsPolyT Np.f] : IsPolyT (fM K g Np) :=
  haveI := IsPolyT.mapIn (M := Np.mem) (qW_polyT K g h)
  haveI := IsPolyT.mapIn (M := Np.f) (qF_polyT K g h)
  gated_isPolyT _ _

/-- One factor of a term of W̃_γ(Θ) has polynomial-time steps. -/
@[instance_reducible] def termP_isPolyT (h : Np.toPaperNetwork.Keeps) [IsPolyT Np.mem] [IsPolyT Np.W] [IsPolyT Np.Ψ] [IsPolyT Np.f] : IsPolyT (termP K g Np) :=
  haveI := wM_isPolyT K g h
  haveI := psiP_isPolyT K g h
  haveI := fM_isPolyT K g h
  haveI := IsPolyT.ite (M := psiP K g Np) (N := fM K g Np) (isPsi_polyT K g)
  haveI := IsPolyT.ite (M := wM K g Np) (N := Stepped.ite (isPsi K g) (psiP K g Np) (fM K g Np)) (isW_polyT g)
  haveI := IsPolyT.const (α := (X0 C × ℕ) × ℕ) (1 : ℤ)
  IsPolyT.ite (isOne_polyT K g)

/-- One entry W̃_γ(Θ) has polynomial-time steps. -/
@[instance_reducible] def tableM_isPolyT (h : Np.toPaperNetwork.Keeps) [IsPolyT Np.mem] [IsPolyT Np.W] [IsPolyT Np.Ψ] [IsPolyT Np.f] : IsPolyT (tableM K g Np) :=
  haveI := termP_isPolyT K g h
  haveI := IsPolyT.prodRange (M := termP K g Np) (N := nPairs g) (nPairs_polyT g)
  haveI := IsPolyT.sumRange (M := Stepped.prodRange (nPairs g) (termP K g Np)) (nStates_polyT K g h)
  haveI := IsPolyT.const (α := X0 C) (0 : ℤ)
  IsPolyT.ite (validB_polyT K g h)

/-- The search through the K^g groupings has polynomial-time steps. -/
@[instance_reducible] def searchP_isPolyT (h : KeepsP Np) : IsPolyT (searchP K g Np) :=
  haveI := IsPolyT.ofFun (goodP_polyT K g h)
  IsPolyT.firstRange (nCol_polyT K g) (by change PolyT fun b : Bool => b; fun_prop)

/-- **The algorithm of the proof of Lemma 1 has polynomial-time steps** if the algorithm E for
cliques has: whenever the four procedures have polynomial-time steps and P_a, c_{a,b}, P are given
in unary, so has `netAlg K g E` on them. -/
theorem stKeeps : StKeeps := by
  intro K g E hE C _ _ _ Np hN
  have hk := keeps_toPaperNetwork hN.keeps
  obtain ⟨hm⟩ := hN.keeps.mem
  obtain ⟨hW⟩ := hN.keeps.W
  obtain ⟨hΨ⟩ := hN.keeps.Ψ
  obtain ⟨hf⟩ := hN.keeps.f
  obtain ⟨hE'⟩ := hE (C × ℕ) (lamP K g Np) (tableM K g Np) (lamP_unary K g hN) ⟨tableM_isPolyT K g hk⟩
  have := searchP_isPolyT K g hN
  exact ⟨IsPolyT.optBind zeroOf_polyT⟩

end Eight.ViaGrouping
