/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ExplicitCost.GroupingDefs
import ExplicitCost.Poly
import Exits.Poly
import QueryMachines.Poly
import PaddedDescent.F.CertNet
import Mathlib.Tactic

/-! # The procedure of Lemma 8 (Appendix A, the grouping with explicit cost) has polynomial-time steps

One certificate for all K, g and ζ: these are read from the input. The certificates of the
constructions are those of proof/machines/QueryMachines/Poly.lean and
proof/threesat/Exits/Poly.lean; those of the plain functions, jointly in K, g and the input, are
those of proof/rates/PaddedDescent/F/CertNet.lean; that of an entry is `entryDataCert`. Proved here:

* `inK_unary`, `inG_unary`, `inP_unary`, `inB_unary`, `inU_unary`: K, g, P, B stand in the input in
  unary, and U is a sum of numbers that do;
* `label_le`, `labelLength_polyT`, `labelLength_unary`: L is at most U + 2gP + 1 on EVERY input
  (this is what min(a, b) in its definition is for), so it can be written in unary;
* `bitsOut_unary`: B' in unary; `good_joint`, `goodData_polyT`: the test of a grouping;
  `toLists_joint`, `entryInput_polyT`: cutting a setting into its strings, with K and L computed
  from the input; `callOf_polyT`: the call;
* `groupingPoly`: the search, the call, and the two substitutions. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed PaddedDescent.F.CertNet

variable {α : Type} [Enc α]

/-! ## The numbers -/

/-- K is given in unary. -/
theorem inK_unary {c : α → GroupingInput} (hc : PolyT c) : Unary fun t => inK (c t) := Unary.of_length (w := fun t => (c t).2.1.1) (by fun_prop)

/-- g is given in unary. -/
theorem inG_unary {c : α → GroupingInput} (hc : PolyT c) : Unary fun t => inG (c t) := Unary.of_length (w := fun t => (c t).2.1.2) (by fun_prop)

/-- P is given in unary. -/
theorem inP_unary {c : α → GroupingInput} (hc : PolyT c) : Unary fun t => inP (c t) := Unary.of_length (w := fun t => (c t).2.2.1.1) (by fun_prop)

/-- B is given in unary. -/
theorem inB_unary {c : α → GroupingInput} (hc : PolyT c) : Unary fun t => inB (c t) := Unary.of_length (w := fun t => (c t).2.2.1.2) (by fun_prop)

/-- U is a sum of g² numbers that are given in unary. -/
theorem inU_unary {c : α → GroupingInput} (hc : PolyT c) : Unary fun t => inU (c t) :=
  UcU keepsU_askedData (inG_unary hc) (c := fun t => (c t).2) (by fun_prop)

/-- ⌈(bU + 2·min(a, b)·gP)/(bK²)⌉ ≤ U + 2gP + 1, for all natural numbers. -/
private theorem label_le (a b K g P U : ℕ) : (b * U + 2 * min a b * g * P + b * K ^ 2 - 1) / (b * K ^ 2) ≤ U + 2 * g * P + 1 := by
  obtain ⟨d, hd⟩ : ∃ d, d = b * K ^ 2 := ⟨_, rfl⟩
  rw [← hd]
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [h0, Nat.div_zero]
    omega
  · have hK : 0 < K ^ 2 := Nat.pos_of_mul_pos_left (hd ▸ hpos)
    have hbd : b ≤ d := hd ▸ Nat.le_mul_of_pos_right _ hK
    have n1 : b * U ≤ d * U := Nat.mul_le_mul_right _ hbd
    have n2 : 2 * min a b * g * P ≤ d * (2 * g * P) :=
      calc 2 * min a b * g * P = min a b * (2 * g * P) := by ring
        _ ≤ d * (2 * g * P) := Nat.mul_le_mul_right _ ((min_le_right a b).trans hbd)
    have e : d * (U + 2 * g * P + 1) = d * U + d * (2 * g * P) + d := by ring
    apply Nat.div_le_of_le_mul
    rw [e]
    omega

/-- The formula for L, jointly in all its numbers. -/
private theorem label_joint {a b K g P U : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hK : PolyT K) (hg : PolyT g) (hP : PolyT P) (hU : PolyT U) :
    PolyT fun t => (b t * U t + 2 * min (a t) (b t) * g t * P t + b t * K t ^ 2 - 1) / (b t * K t ^ 2) := by
  have hq : ∀ {n d : α → ℕ}, PolyT n → PolyT d → PolyT fun t => (n t + d t - 1) / d t := fun hn hd => by fun_prop
  have hn : ∀ {m : α → ℕ}, PolyT m → PolyT fun t => b t * U t + 2 * m t * g t * P t := fun hm => by fun_prop
  have hd : PolyT fun t => b t * K t ^ 2 := by fun_prop
  exact hq (hn (PolyT.min' ha hb)) hd

/-- L is computed in polynomial time. -/
theorem labelLength_polyT {c : α → GroupingInput} (hc : PolyT c) : PolyT fun t => labelLength (c t) :=
  label_joint (a := fun t => (c t).1.1) (b := fun t => (c t).1.2) (by fun_prop) (by fun_prop) (inK_unary hc).poly (inG_unary hc).poly (inP_unary hc).poly (inU_unary hc).poly

/-- L can be written in unary in polynomial time. -/
theorem labelLength_unary {c : α → GroupingInput} (hc : PolyT c) : Unary fun t => labelLength (c t) :=
  Unary.of_le (g := fun t => inU (c t) + 2 * inG (c t) * inP (c t) + 1)
    (((inU_unary hc).add (((Unary.const 2).mul (inG_unary hc)).mul (inP_unary hc))).add (Unary.const 1)) (labelLength_polyT hc) fun _ => label_le _ _ _ _ _ _

/-- The formula for B', jointly in all its numbers. -/
private theorem bits_joint {K g P B : α → ℕ} (hK : PolyT K) (hg : PolyT g) (hP : PolyT P) (hB : PolyT B) : PolyT fun t => bitsOut (K t) (g t) (P t) (B t) := by
  unfold bitsOut
  fun_prop

/-- B' can be written in unary in polynomial time. -/
theorem bitsOut_unary {c : α → GroupingInput} (hc : PolyT c) : Unary fun t => bitsOut (inK (c t)) (inG (c t)) (inP (c t)) (inB (c t)) := by
  have hK := inK_unary hc
  have hg := inG_unary hc
  have hP := inP_unary hc
  have hB := inB_unary hc
  refine Unary.of_le (g := fun t => 2 * (inG (c t) * inP (c t)) + inK (c t) + inG (c t) * inG (c t) * inB (c t)) ?_ ?_ fun t => ?_
  · exact (((Unary.const 2).mul (hg.mul hP)).add hK).add ((hg.mul hg).mul hB)
  · exact bits_joint hK.poly hg.poly hP.poly hB.poly
  · unfold bitsOut
    have h := Nat.div_le_self (2 * (inG (c t) * inP (c t)) + (inK (c t) - 1)) (inK (c t))
    have e : inG (c t) ^ 2 * inB (c t) = inG (c t) * inG (c t) * inB (c t) := by ring
    omega

/-! ## The test, the queries, the call -/

/-- The test of a grouping, jointly in K, g, L, the number of the grouping and the input. -/
private theorem good_joint {K g L x : α → ℕ} {c : α → DataInput} (hK : Unary K) (hg : Unary g) (hL : PolyT L) (hx : PolyT x) (hc : PolyT c) :
    PolyT fun t => ((List.range (K t)).all fun G => decide (K t * (members (K t) (g t) (x t) G).length ≤ 2 * g t)) &&
      (List.range (K t)).all fun G => (List.range (K t)).all fun G' => G == G' || decide (lbLen (K t) (g t) askedData.under.toPaperNetwork (c t) (x t) G G' ≤ L t) := by
  have hKp := hK.poly
  have hgp := hg.poly
  have h1 : PolyT fun t => (List.range (K t)).all fun G => decide (K t * (members (K t) (g t) (x t) G).length ≤ 2 * g t) := by fun_prop
  have hb : PolyT fun q : (α × ℕ) × ℕ => L q.1.1 := by fun_prop
  have hl : PolyT fun q : (α × ℕ) × ℕ => lbLen (K q.1.1) (g q.1.1) askedData.under.toPaperNetwork (c q.1.1) (x q.1.1) q.1.2 q.2 :=
    lbLen2 keepsU_askedData (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : PolyT fun t => (List.range (K t)).all fun G => (List.range (K t)).all fun G' =>
      G == G' || decide (lbLen (K t) (g t) askedData.under.toPaperNetwork (c t) (x t) G G' ≤ L t) :=
    PolyT.all (f := fun t G => (List.range (K t)).all fun G' => G == G' || decide (lbLen (K t) (g t) askedData.under.toPaperNetwork (c t) (x t) G G' ≤ L t))
      (PolyT.all (f := fun (q : α × ℕ) G' => q.2 == G' || decide (lbLen (K q.1) (g q.1) askedData.under.toPaperNetwork (c q.1) (x q.1) q.2 G' ≤ L q.1))
        (PolyT.or' (by fun_prop) (PolyT.decide_le hl hb)) (by fun_prop)) (by fun_prop)
  exact PolyT.and' h1 h2

/-- The test of the procedure is computed in polynomial time. -/
theorem goodData_polyT : PolyT goodData :=
  good_joint (K := fun cx : GroupingInput × ℕ => inK cx.1) (g := fun cx => inG cx.1) (L := fun cx => labelLength cx.1) (x := fun cx => cx.2) (c := fun cx => cx.1.2)
    (inK_unary (by fun_prop)) (inG_unary (by fun_prop)) (labelLength_polyT (by fun_prop)) (by fun_prop) (by fun_prop)

/-- Cutting a setting z_w into its K − 1 strings of λ bits, jointly in K, λ and the query. -/
private theorem toLists_joint {K lam : α → ℕ} {q : α → TableQuery} (hK : Unary K) (hl : PolyT lam) (hq : PolyT q) : PolyT fun t => toLists (K t) (lam t) (q t) := by
  have hKp := hK.poly
  unfold toLists copyAt place
  fun_prop (disch := assumption)

/-- How a query to the tables becomes an input of `entryData`. -/
theorem entryInput_polyT : PolyT entryInput := by
  have h := toLists_joint (K := fun y : (GroupingInput × ℕ) × TableQuery => inK y.1.1) (lam := fun y => labelLength y.1.1) (q := fun y => y.2)
    (inK_unary (by fun_prop)) (labelLength_polyT (by fun_prop)) (by fun_prop)
  unfold entryInput
  fun_prop

/-- The call is computed in polynomial time. -/
theorem callOf_polyT : PolyT callOf := by
  have u1 : PolyT fun cx : GroupingInput × ℕ => unary (inK cx.1) := inK_unary (by fun_prop)
  have u2 : PolyT fun cx : GroupingInput × ℕ => unary (labelLength cx.1) := labelLength_unary (by fun_prop)
  have u3 : PolyT fun cx : GroupingInput × ℕ => unary (bitsOut (inK cx.1) (inG cx.1) (inP cx.1) (inB cx.1)) := bitsOut_unary (by fun_prop)
  unfold callOf
  fun_prop

/-! ## The machines -/

/-- The procedure up to the call has polynomial-time steps. -/
theorem groupingCall_poly : groupingCall.PolyTimeSteps := by
  have := IsPolyT.ofFun goodData_polyT
  have sr : IsPolyT searchData := Exits.IsPolyT.firstUntil (N := fun c : GroupingInput => inK c ^ inG c)
    (PolyT.pow_unary (inK_unary PolyT.id').poly (inG_unary PolyT.id')) (by change PolyT fun b : Bool => b; fun_prop)
  have sl : QueryMachine.IsPolyQ (QueryMachine.lift searchData : QueryMachine CliqueCall ℤ GroupingInput (Option ℕ)) := QueryMachine.IsPolyQ.lift _
  have q : QueryMachine.IsPolyQ (QueryMachine.query callOf : QueryMachine CliqueCall ℤ (GroupingInput × ℕ) ℤ) := QueryMachine.IsPolyQ.query callOf_polyT
  exact ⟨QueryMachine.IsPolyQ.optBind _ _ zeroOf_polyT⟩

/-- The procedure has polynomial-time steps, up to the call and as a whole if E has and `arg` is
polynomial-time. -/
theorem groupingPoly : GroupingPoly := by
  refine ⟨groupingCall_poly, fun β _ E arg hE harg => ?_⟩
  have := entryDataCert
  have n1 := QueryMachine.IsPolyQ.mapIn entryInput_polyT entryData
  obtain ⟨s1⟩ := stPolySubst _ _ _ _ (GroupingInput × ℕ) _ _ E (QueryMachine.mapIn entryInput entryData) hE ⟨n1⟩
  have hin : PolyT fun y : GroupingInput × CliqueCall => ((y.1, y.2.1), arg y.2.2) := by fun_prop
  have n2 : QueryMachine.IsPolyQ (answerCall E arg) := QueryMachine.IsPolyQ.mapIn hin _
  obtain ⟨s2⟩ := stPolySubst _ _ _ _ GroupingInput _ _ groupingCall (answerCall E arg) groupingCall_poly ⟨n2⟩
  exact ⟨QueryMachine.IsPolyQ.mapIn (by fun_prop : PolyT fun c : GroupingInput => (c, c)) _⟩

end ExplicitCost
