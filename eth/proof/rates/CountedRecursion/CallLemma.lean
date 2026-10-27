/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.CallParts
public import Printed.GroupingEntry
import Mathlib.Tactic

/-! # Lemma 8 at the network of a pattern

The row network and the column network of a pattern are networks on `nParts g g tr` nodes, a number
that equals g but is not g by definition, while the machines write g. Here the statements of Lemma 8
are put into the form «a network on n nodes, n = g», for ζ = 1/b:
* `firstGrouping_cast`: from `GroupingWithCall` and `LabelLengthIsL`: the first grouping that the
  test accepts has at most 2g/K nodes in every group and Y_{γ,γ'} ≤ L, and the number that the
  procedure computes is L;
* `entryCost_cast`: `EntryCostExplicit`;
* `groupClique_value`: `ValueIsKept`, for the procedures `asked`, run with the oracle `netOracle N`
  of the network;
* `netTotal_le`, `Lof_bounds`: U ≤ gP and 1 ≤ L ≤ gP. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- **The first grouping that the test accepts**, for ζ = 1/b and a network on n = g nodes in case (i)
or (ii). -/
theorem firstGrouping_cast (hG : GroupingWithCall) (hL : LabelLengthIsL) {b K g n : ℕ} (hn : n = g) (hK0 : 0 < K) (N : Net n) {P B : ℕ} (hK : 2 ≤ K) (hg : 2 ≤ g) (hb : 1 ≤ b) (hN : N.Is P B)
    (hC : AppRunningTime.Cases K n ((1 : ℝ) / b) P N.c) {x : ℕ} (hx : (List.range (K ^ g)).find? (fun x' => goodData (((1, b), ((unary K, unary g), netInput N P B)), x')) = some x) :
    x < K ^ g ∧ (∀ γ : Fin K, K * #{v : Fin n | Paper.grouping hK0 x v = γ} ≤ 2 * g) ∧
      (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ AppRunningTime.Lof K g ((1 : ℝ) / b) P N.U) ∧
      labelLength ((1, b), ((unary K, unary g), netInput N P B)) = AppRunningTime.Lof K g ((1 : ℝ) / b) P N.U := by
  subst hn
  obtain ⟨C, hG⟩ := hG
  have hC' : AppRunningTime.Cases K n (((1 : ℕ) : ℝ) / b) P N.c := by
    rw [Nat.cast_one]
    exact hC
  obtain ⟨x', hx', hf, h1, h2, -⟩ := hG 1 b K n hK0 N P B 0 hK hg Nat.one_pos hb hN hC'
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hf)
  have h3 := (hL 1 b K n N P B (by omega) hb hK0 hN).1
  rw [Nat.cast_one] at h2 h3
  exact ⟨hx', h1, h2, h3⟩

/-- **The cost of an entry, with one constant**, for a network on n = g nodes. -/
theorem entryCost_cast (hE : EntryCostExplicit) : ∃ c₁ : ℕ, ∀ (K g n : ℕ) (_ : n = g) (hK0 : 0 < K) (N : Net n) (P B τ : ℕ), K ≤ g → N.Is P B → 1 ≤ τ →
    ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin n | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
      ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * L),
        entryData.Within (netOracle N) (fun _ => τ) ((((unary K, unary g), netInput N P B), x), toLists K L (γ.val, Θ)) (2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁) ((g * (P + B)) ^ c₁)
          ((Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ) ∧
        |(Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ| < 2 ^ bitsOut K g P B := by
  obtain ⟨c₁, h⟩ := hE
  refine ⟨c₁, fun K g n hn => ?_⟩
  subst hn
  exact h K n

/-- «… the (K, L)-clique with the tables W̃_γ, whose value is that of the network», for the clique
of the groups as the statements of Lemma 8 name it. -/
theorem groupClique_value (hV : ValueIsKept) {K n : ℕ} (hK0 : 0 < K) (N : Net n) {P B : ℕ} (hN : N.Is P B) (x L : ℕ) (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) :
    (Value.groupClique asked.under (netInput N P B) N hK0 x L).value = N.value :=
  hV NetInput n K hK0 (asked.close (netOracle N)) (netInput N P B) N P B 1 _ (asked_isNetworkP N hN) x L hY

/-- U ≤ gP, by (i) of Definition 2. -/
theorem netTotal_le {n : ℕ} (N : Net n) {P B : ℕ} (hN : N.Is P B) : N.U ≤ n * P := by
  unfold Net.U
  calc ∑ a, ∑ b ∈ univ.erase a, N.c a b ≤ ∑ _a : Fin n, P := Finset.sum_le_sum fun a _ => hN.i a
    _ = n * P := by rw [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- 1 ≤ L ≤ gP, for ζ = 1/b, K ≥ 2 and U ≤ gP. -/
theorem Lof_bounds {K g P U b : ℕ} (hK : 2 ≤ K) (hg : 1 ≤ g) (hP : 1 ≤ P) (hb : 1 ≤ b) (hU : U ≤ g * P) : 1 ≤ AppRunningTime.Lof K g ((1 : ℝ) / b) P U ∧ AppRunningTime.Lof K g ((1 : ℝ) / b) P U ≤ g * P := by
  unfold AppRunningTime.Lof
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hbr : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg U
  have hζ1 : (1 : ℝ) / b ≤ 1 := (div_le_one hb0).2 hbr
  have hζ0 : (0 : ℝ) < 1 / b := by positivity
  constructor
  · exact Nat.ceil_pos.2 (div_pos (by positivity) (by positivity))
  · refine Nat.ceil_le.2 ?_
    rw [div_le_iff₀ (by positivity)]
    push_cast
    have hUr : (U : ℝ) ≤ g * P := by exact_mod_cast hU
    have h4 : (4 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have hgP : (0 : ℝ) < (g : ℝ) * P := by positivity
    have h2 : 2 * (1 / (b : ℝ)) * g * P ≤ 2 * ((g : ℝ) * P) := by
      have : 1 / (b : ℝ) * ((g : ℝ) * P) ≤ 1 * ((g : ℝ) * P) := mul_le_mul_of_nonneg_right hζ1 hgP.le
      nlinarith
    nlinarith

end ExplicitCost
