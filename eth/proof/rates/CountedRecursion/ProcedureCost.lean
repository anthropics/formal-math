/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.CallFacts
public import CountedRecursion.ParentSize
public import CountedRecursion.Within
import Mathlib.Tactic

/-! # One entry of the callee's tables

`procedureCostFrom : ProcedureCostFrom`. Proof of Lemma 8: «an entry is a sum of at most 2^{2gP/K}
terms, each a product of at most g² values» and «answer each query by computing the entry»; proof of
Theorem A (b): «Definition 2 holds with B₁ = gB + g²(2λ)^c in the role of B and with τ =
2^{cλ}Ξ^{C₂}», «Crude bounds give L ≤ N + 1, … g(P + B₁) ≤ Ξ^{c+4}».
The procedure is `entryData` with each of its queries of Definition 2(iii) answered by the
procedures of the network (`QueryMachine.subst`). So: `EntryCostExplicit` at the price τ = (2^{cλ} +
2 + tq)·Ξ^{C₂} + 2 of a query; `BothNetworks` answers a query within τ − 2;
`QueryMachines.StSubstWithin` puts the two together; the context that is carried along is the parent
(`size_mkParent_le`);
and the clause g(P + B₁) ≤ Ξ^{c+4} of `CrudeBounds` turns (g(P + B₁))^{c₁} into a power of Ξ.
`EntryCostExplicit` asks L ≤ 2gP for the L of the call: this is had from `LabelCrude`, L ≤ N + 1 =
gP + 1 ≤ 2gP. The constant is C₂ + (c + 4)c₁ + 2c + 6. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- The arithmetic: with A the price of a query one level up, G ≤ X^e, and a context of size at most
X^s. -/
theorem procedure_arith {X A C₂ c₁ e s G sp : ℕ} (hX : 2 ≤ X) (hA : 2 ≤ A) (hG : G ≤ X ^ e) (hsp : sp ≤ X ^ s) :
    (A * X ^ C₂ + 2) * G ^ c₁ ≤ A * X ^ (C₂ + e * c₁ + s + 2) ∧ sp + G ^ c₁ + X ^ C₂ + 1 ≤ X ^ (C₂ + e * c₁ + s + 2) := by
  have hX0 : 0 < X := by omega
  have hv : G ^ c₁ ≤ X ^ (e * c₁) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hG c₁
  have etop : X ^ (C₂ + e * c₁ + s + 2) = X ^ C₂ * X ^ (e * c₁) * X ^ s * X ^ 2 := by rw [pow_add, pow_add, pow_add]
  have h4 : 4 ≤ X ^ 2 := by simpa using Nat.pow_le_pow_left hX 2
  have hu1 : 1 ≤ X ^ C₂ := Nat.one_le_pow _ _ hX0
  have hv1 : 1 ≤ X ^ (e * c₁) := Nat.one_le_pow _ _ hX0
  have hw1 : 1 ≤ X ^ s := Nat.one_le_pow _ _ hX0
  rw [etop]
  generalize X ^ C₂ = u at *
  generalize X ^ (e * c₁) = v at *
  generalize X ^ s = w at *
  generalize X ^ 2 = r at *
  generalize G ^ c₁ = k at *
  have t4 : u * v * w * 4 ≤ u * v * w * r := Nat.mul_le_mul_left _ h4
  have tu : u * 1 * 1 ≤ u * v * w := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hv1) hw1
  have tv : 1 * v * 1 ≤ u * v * w := Nat.mul_le_mul (Nat.mul_le_mul hu1 le_rfl) hw1
  have tw : 1 * 1 * w ≤ u * v * w := Nat.mul_le_mul (Nat.mul_le_mul hu1 hv1) le_rfl
  have tuv : u * v * 1 ≤ u * v * w := Nat.mul_le_mul le_rfl hw1
  constructor
  · have h2 : 2 ≤ A * u := hA.trans (Nat.le_mul_of_pos_right _ hu1)
    calc (A * u + 2) * k ≤ (A * u + A * u) * v := Nat.mul_le_mul (by omega) hv
      _ = A * (u * v * 1 * 2) := by ring
      _ ≤ A * (u * v * w * r) := Nat.mul_le_mul_left _ (by omega)
  · omega

/-- **An entry of the callee's tables**, from Lemma 8 up to the call, its L and case (ii), the cost
of an entry with one constant, the procedures of the network, «L ≤ N + 1» for the L of the call,
«g(P + B₁) ≤ Ξ^{c+4}», and «answer each query by computing …». -/
theorem procedureCostFrom : ProcedureCostFrom := by
  intro hG hL hC hE hBN hLC hCB hSub c
  obtain ⟨c₁, hE⟩ := entryCost_cast hE
  obtain ⟨C₂, hB2⟩ := hBN c
  refine ⟨C₂ + (c + 4) * c₁ + (2 * c + 4) + 2, fun ρ x₀ D hS Bound a a' f l hF hl hc q v hq tq Lam hLam => ?_⟩
  obtain ⟨y, x, h⟩ := at_call hG hL hC hBN hS hF hl hc
  obtain ⟨hK2, hKg, hg2⟩ := level_numbers hS.x₀_ge l
  obtain ⟨hlam, hB1, hW, hf⟩ := fits_succ hF hl
  have hK0 : 0 < Levels.Gen.K x₀ l := by omega
  have hpK : pK (callParent D x₀ l a y x) = Levels.Gen.K x₀ l := length_unary _
  -- the query names a group γ and a setting Θ of it, and the answer is W̃_γ(Θ)
  have htab : (spec D c x₀ Bound).tab a' f = answersOf (Levels.Gen.K x₀ l) (callL D c x₀ l a f y) (groupTables D c (callParent D x₀ l a y x) (callL D c x₀ l a f y) (readTables f)) := by
    change answersOf (pK (parentOf a')) (cLam a') (groupTables D c (parentOf a') (cLam a') (readTables f)) = _
    rw [h.parent, h.lam, hpK]
  rw [htab] at hq
  obtain ⟨hq1, hq2, rfl⟩ := answersOf_some hq
  have hval : groupTables D c (callParent D x₀ l a y x) (callL D c x₀ l a f y) (readTables f) q.1 q.2 =
      (Value.groupClique asked.under (netInput (callNet D c x₀ l a f y) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) (callNet D c x₀ l a f y) hK0 x (callL D c x₀ l a f y)).W ⟨q.1, hq1⟩ q.2 := by
    unfold callParent
    rw [groupTables_mkParent]
    exact dif_pos hq1
  rw [hval]
  -- what the procedure hands to `entryData`
  have hin : calleeInput c (a', q) = (callParent D x₀ l a y x, ((((unary (Levels.Gen.K x₀ l), unary (Levels.Gen.g x₀ l)),
      netInput (callNet D c x₀ l a f y) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))), x), toLists (Levels.Gen.K x₀ l) (callL D c x₀ l a f y) ((⟨q.1, hq1⟩ : Fin (Levels.Gen.K x₀ l)).val, q.2))) := by
    change (parentOf a', ((netData c (parentOf a'), pX (parentOf a')), toLists (pK (parentOf a')) (cLam a') q)) = _
    rw [h.parent, h.lam, h.data, hpK]
    rfl
  -- «Crude bounds give L ≤ N + 1», for the L of the call; so L ≤ 2gP, which the cost of an entry
  -- asks
  have hLle : callL D c x₀ l a f y ≤ Levels.Gen.g x₀ l ^ 4 * cLam a + 1 :=
    hLC ρ c x₀ D hS l (cLam a) y (direction (readyOf D x₀ a.1, y)) (readTables f) hlam
  have hL2 : callL D c x₀ l a f y ≤ 2 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) := by
    have e : Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) = Levels.Gen.g x₀ l ^ 4 * cLam a := by ring
    have h1 : 1 ≤ Levels.Gen.g x₀ l ^ 4 * cLam a := Nat.mul_pos (Nat.pow_pos (by omega)) hlam
    omega
  -- an entry, at the price τ of a query of Definition 2(iii)
  have hent := (hE _ _ _ (nParts_self _ _) hK0 (callNet D c x₀ l a f y) _ _ ((askCost c (cLam a) + tq) * Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₂ + 2) hKg h.is (by omega) x h.x_lt _
    hL2 (h.few hK0) (h.short hK0) ⟨q.1, hq1⟩ q.2 hq2).1
  -- each such query is answered within τ − 2
  have hans := (hB2 ρ x₀ D hS (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) y x tq Lam (direction (readyOf D x₀ a.1, y)) (readTables f) hg2 hKg hlam hLam hB1 hW h.y_lt h.x_lt).2.2.2
  rw [← hf] at hans
  have hrun := hSub NetQuery ℤ UpQuery Ans Parent (X0 DataInput) ℤ entryData (gridProcsData c).answer (netOracle (callNet D c x₀ l a f y)) (Sum.elim f (piecesUpTo D Lam))
    (fun _ => (askCost c (cLam a) + tq) * Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₂ + 2) (upPrices c tq) (callParent D x₀ l a y x) _ _ _ _ _
    (fun _ => (askCost c (cLam a) + tq) * Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₂) hent hans (fun _ => le_rfl)
  -- the arithmetic
  have hX2 : 2 ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) := by
    have h1 : 1 * 2 ≤ Levels.Gen.g x₀ l ^ 2 * (cLam a + cB a) := Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) (by omega)
    exact h1
  have hA : 2 ≤ askCost c (cLam a) + tq := by
    unfold askCost
    omega
  obtain ⟨hT, hSz⟩ := procedure_arith (C₂ := C₂) (c₁ := c₁) hX2 hA (hCB c x₀ l (cLam a) (cB a) 0 hS.x₀_ge hlam hB1 (Nat.zero_le _)).2.1
    (size_mkParent_le hS (direction (readyOf D x₀ a.1, y)) hKg hg2 hlam hB1 h.y_lt h.x_lt)
  unfold procedure
  refine mapOut_within (mapIn_within ?_)
  rw [hin]
  refine hrun.mono ?_ hSz
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ hT

end ExplicitCost
