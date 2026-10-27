/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ExplicitCost.GroupingDefs
import ExplicitCost.GroupingNumbers
import ExplicitCost.GroupingSearch
import ExplicitCost.GroupingCall
import ExplicitCost.Cost
import Printed.GroupingEntry
import Printed.GroupingRun
import Printed.Achievable
import QueryMachines.Runs
import GeneralPieces.Main
import Mathlib.Tactic

/-! # The lemma on groupings with explicit cost, for the procedure of its proof

«… define the (K, L)-clique with the tables W̃_γ, whose value is that of the network, run the given
algorithm on it, and answer each query by computing the entry.» The procedure is
`groupingData E arg`, for ANY machine E that outputs the value of every (K, L)-clique with |W_w| <
2^{B'} within 𝒯 operations. With X = g(P+B), n = 2^{P⌊2g/K⌋} and t = n·τ·X^{c₁}, the cost of an
entry:

1. E takes 𝒯 operations, a query counted as one; at t + 2 operations for a query it takes at most
   𝒯·(t + 2) (`QueryMachines.StSlowDown`);
2. each query answered by `entryData` within t operations: the same bound, now at τ operations for a
   query of Definition 2(iii) (`QueryMachines.StSubstWithin`): this is the call carried out,
   `answerCall_within`;
3. the procedure up to the call costs C·K^g + tc when the call costs tc; with tc = 𝒯·(t + 2) + 2 and
   the call carried out as in 2, the whole costs C·K^g + 𝒯·(t + 2) + 2
   (`QueryMachines.StSubstWithin` again);
4. arithmetic: `time_le` (natural numbers; the constants go into a power of X ≥ 2), `real_time_le`
   (P·⌊2g/K⌋ ≤ 2gP/K).

With the constant C of the part of the procedure before the call (`groupingWithCall`) and the
constant c₁ of an entry, C₁ = C + c₁ + 12. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed Sizes

/-! ## Arithmetic -/

/-- C·K^g + 𝒯·(t + 2) + 2 ≤ (K^g + 𝒯·n·τ)·X^{C + c₁ + 12} for t = n·τ·X^{c₁}; Kg stands for K^g. -/
private theorem time_le {C c₁ Kg 𝒯 n τ X : ℕ} (hX : 2 ≤ X) (hKg : 1 ≤ Kg) (hn : 1 ≤ n) (hτ : 1 ≤ τ) :
    C * Kg + (𝒯 * (n * τ * X ^ c₁ + 2) + 2) ≤ (Kg + 𝒯 * n * τ) * X ^ (C + c₁ + 12) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ c₁ := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := hY ▸ Nat.one_le_pow _ _ (by omega)
  have hD : C + 3 ≤ X ^ (C + 12) :=
    calc C + 3 ≤ 2 ^ (C + 3) := Nat.lt_two_pow_self.le
      _ ≤ X ^ (C + 3) := Nat.pow_le_pow_left hX _
      _ ≤ X ^ (C + 12) := Nat.pow_le_pow_right (by omega) (by omega)
  have e : X ^ (C + c₁ + 12) = X ^ (C + 12) * Y := by
    rw [hY, ← pow_add]
    congr 1
    omega
  rw [← hY, e]
  have ht : 1 ≤ n * τ * Y := Nat.mul_pos (Nat.mul_pos hn hτ) hY1
  have a1 : 𝒯 * (n * τ * Y + 2) ≤ 𝒯 * (3 * (n * τ * Y)) := Nat.mul_le_mul_left _ (by omega)
  have a2 : (C + 2) * Kg = C * Kg + 2 * Kg := by ring
  have a3 : (C + 2) * Kg ≤ (C + 2) * Kg * Y := Nat.le_mul_of_pos_right _ hY1
  have e1 : (C + 2) * Kg * Y + 𝒯 * (3 * (n * τ * Y)) + (Kg * Y + C * (𝒯 * n * τ * Y)) = (C + 3) * ((Kg + 𝒯 * n * τ) * Y) := by ring
  calc C * Kg + (𝒯 * (n * τ * Y + 2) + 2) ≤ (C + 3) * ((Kg + 𝒯 * n * τ) * Y) := by omega
    _ ≤ X ^ (C + 12) * ((Kg + 𝒯 * n * τ) * Y) := Nat.mul_le_mul_right _ hD
    _ = (Kg + 𝒯 * n * τ) * (X ^ (C + 12) * Y) := by ring

/-- From 2^{P⌊2g/K⌋} to the printed 2^{2gP/K}, and from natural to real numbers. -/
private theorem real_time_le {T K g P B 𝒯 τ C₁ : ℕ} (h : T ≤ (K ^ g + 𝒯 * 2 ^ (P * (2 * g / K)) * τ) * (g * (P + B)) ^ C₁) :
    (T : ℝ) ≤ ((K : ℝ) ^ g + 𝒯 * (2 : ℝ) ^ (2 * (g : ℝ) * P / K) * τ) * ((g : ℝ) * (P + B)) ^ C₁ := by
  have h1 : (T : ℝ) ≤ (((K ^ g + 𝒯 * 2 ^ (P * (2 * g / K)) * τ) * (g * (P + B)) ^ C₁ : ℕ) : ℝ) := by exact_mod_cast h
  have hexp : ((P * (2 * g / K) : ℕ) : ℝ) ≤ 2 * (g : ℝ) * P / K := by
    have hd : ((2 * g / K : ℕ) : ℝ) ≤ ((2 * g : ℕ) : ℝ) / K := Nat.cast_div_le
    calc ((P * (2 * g / K) : ℕ) : ℝ) = (P : ℝ) * ((2 * g / K : ℕ) : ℝ) := Nat.cast_mul _ _
      _ ≤ (P : ℝ) * (((2 * g : ℕ) : ℝ) / K) := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
      _ = 2 * (g : ℝ) * P / K := by
        push_cast
        ring
  have h2 : (2 : ℝ) ^ (P * (2 * g / K)) ≤ (2 : ℝ) ^ (2 * (g : ℝ) * P / K) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hexp
  have e : (((K ^ g + 𝒯 * 2 ^ (P * (2 * g / K)) * τ) * (g * (P + B)) ^ C₁ : ℕ) : ℝ) = ((K : ℝ) ^ g + 𝒯 * (2 : ℝ) ^ (P * (2 * g / K)) * τ) * ((g : ℝ) * (P + B)) ^ C₁ := by
    push_cast
    ring
  rw [e] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) _

/-! ## The tables of the clique of the groups -/

/-- The tables W̃ of the clique of the groups, as a machine for cliques takes tables: a function of
the number of the node and of the setting. -/
@[expose] def groupW {g K : ℕ} (N : Net g) (P B : ℕ) (hK0 : 0 < K) (x L : ℕ) : ℕ → List Bool → ℤ :=
  fun w z => if h : w < K then (Value.groupClique asked.under (netInput N P B) N hK0 x L).W ⟨w, h⟩ z else 0

/-- The clique with these tables is the clique of the groups. -/
theorem clique_groupW {g K : ℕ} (N : Net g) (P B : ℕ) (hK0 : 0 < K) (x L : ℕ) :
    (clique K L fun w => groupW N P B hK0 x L w.val) = Value.groupClique asked.under (netInput N P B) N hK0 x L :=
  congrArg (clique K L) (funext fun w => funext fun _ => dif_pos w.2)

/-! ## The call carried out -/

/-- **«run the given algorithm on it, and answer each query by computing the entry»**: for a
grouping number x with the two properties, the call of x, carried out by E with its queries answered
by `entryData`, returns the value of the clique of the groups within 𝒯·(t + 2) operations, t the
cost of an entry. -/
theorem answerCall_within (hL : LabelLengthIsL) (hSlow : QueryMachines.StSlowDown) (hSub : QueryMachines.StSubstWithin) {c₁ : ℕ} {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α)
    {a b K g : ℕ} (hK0 : 0 < K) {N : Net g} {P B τ 𝒯 SE x : ℕ} (hb : 0 < b) (hab : a ≤ b) (hN : N.Is P B)
    (hE : SolvesCliques E (arg (unary K, unary (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U), unary (AppRunningTime.B'of K g P B))) K (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) (AppRunningTime.B'of K g P B) 𝒯 SE)
    (hentry : ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * AppRunningTime.Lof K g ((a : ℝ) / b) P N.U),
      entryData.Within (netOracle N) (fun _ => τ) ((dataInput K N P B, x), toLists K (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) (γ.val, Θ)) (2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁) ((g * (P + B)) ^ c₁)
        ((Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).W γ Θ) ∧
      |(Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).W γ Θ| < 2 ^ bitsOut K g P B) :
    (answerCall E arg).Within (netOracle N) (fun _ => τ) (groupingInput a b K N P B, callOf (groupingInput a b K N P B, x)) (𝒯 * (2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁ + 2))
      (size (groupingInput a b K N P B, x) + SE + (g * (P + B)) ^ c₁ + 1) (Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).value := by
  obtain ⟨hLL, hBB⟩ := hL a b K g N P B hb hab hK0 hN
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = AppRunningTime.Lof K g ((a : ℝ) / b) P N.U := ⟨_, rfl⟩
  rw [← hLdef] at hLL hE hentry ⊢
  rw [← hBB] at hE
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = 2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁ := ⟨_, rfl⟩
  rw [← ht] at hentry ⊢
  -- E on the tables of the clique of the groups
  have hrun := hE (groupW N P B hK0 x L) fun w hw z hz => by
    unfold groupW
    rw [dif_pos hw]
    exact (hentry ⟨w, hw⟩ z hz).2
  rw [clique_groupW] at hrun
  have hslow := hSlow _ _ _ _ E _ _ 𝒯 SE (t + 2) _ (by omega) hrun
  -- each query answered by computing the entry
  have hsub := hSub _ _ _ _ (GroupingInput × ℕ) _ _ E (QueryMachine.mapIn entryInput entryData) (tables K L (groupW N P B hK0 x L)) (netOracle N) (fun _ => t + 2) (fun _ => τ)
    (groupingInput a b K N P B, x) _ _ SE ((g * (P + B)) ^ c₁) _ (fun _ => t) hslow
    (fun q v hq => mapIn_within (by
      obtain ⟨hq1, hq2, rfl⟩ := tables_eq_some hq
      change entryData.Within (netOracle N) (fun _ => τ) ((dataInput K N P B, x), toLists (inK (groupingInput a b K N P B)) (labelLength (groupingInput a b K N P B)) q) _ _ _
      rw [inK_groupingInput, hLL]
      unfold groupW
      rw [dif_pos hq1]
      exact (hentry ⟨q.1, hq1⟩ q.2 hq2).1))
    (fun _ => le_rfl)
  refine mapIn_within ?_
  change (E.subst (QueryMachine.mapIn entryInput entryData)).Within (netOracle N) (fun _ => τ)
    ((groupingInput a b K N P B, x), arg (unary (inK (groupingInput a b K N P B)), unary (labelLength (groupingInput a b K N P B)),
      unary (bitsOut (inK (groupingInput a b K N P B)) (inG (groupingInput a b K N P B)) (inP (groupingInput a b K N P B)) (inB (groupingInput a b K N P B))))) _ _ _
  rw [inK_groupingInput, inG_groupingInput, inP_groupingInput, inB_groupingInput, hLL]
  exact hsub

/-! ## The lemma -/

/-- How the bound on the part of the procedure before the call (`groupingWithCall`), the cost of an
entry and the rules of substitution give the lemma. -/
theorem groupingExplicitFrom : GroupingExplicitFrom := by
  classical
  intro hW hL hEC hS hMono hSlow hSub
  obtain ⟨C, hC⟩ := hW
  obtain ⟨c₁, hc₁⟩ := hEC
  refine ⟨C + c₁ + 12, fun α E arg a b K g N P B τ 𝒯 SE hK hg ha hab hN hτ hCases hE => ?_⟩
  have hK0 : 0 < K := by omega
  have hb : 0 < b := by omega
  have hζ0 : (0 : ℝ) < (a : ℝ) / b := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hζ1 : (a : ℝ) / b ≤ 1 := (div_le_one (by exact_mod_cast hb)).2 (by exact_mod_cast hab)
  obtain ⟨hKg, hLle⟩ := hS K g _ P N.c hK hg hζ0 hζ1 hN.P_pos hN.i hCases
  have hgP : 1 ≤ g * P := Nat.mul_pos (by omega) hN.P_pos
  have hL2 : AppRunningTime.Lof K g ((a : ℝ) / b) P N.U ≤ 2 * (g * P) := le_trans hLle (by omega)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = 2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁ := ⟨_, rfl⟩
  obtain ⟨x, hx, -, h1, h2, hcall⟩ := hC a b K g hK0 N P B (𝒯 * (t + 2) + 2) hK hg ha hab hN hCases
  have hans := answerCall_within hL hSlow hSub E arg hK0 hb hab hN hE (hc₁ K g hK0 N P B τ hKg hN hτ x hx _ hL2 h1 h2)
  rw [← ht] at hans
  -- the oracle that answers the call of x, and nothing else
  have hup := hcall (fun y => if y = callOf (groupingInput a b K N P B, x) then
    some (Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).value else none) (if_pos rfl)
  have hsub := hSub _ _ _ _ GroupingInput _ _ groupingCall (answerCall E arg) _ (netOracle N) (fun _ => 𝒯 * (t + 2) + 2) (fun _ => τ) (groupingInput a b K N P B) _ _ _
    (size (groupingInput a b K N P B, x) + SE + (g * (P + B)) ^ c₁ + 1) _ (fun _ => 𝒯 * (t + 2)) hup
    (fun y v hy => by
      by_cases e : y = callOf (groupingInput a b K N P B, x)
      · rw [if_pos e] at hy
        obtain rfl := Option.some.inj hy
        rw [e]
        exact hans
      · rw [if_neg e] at hy
        cases hy)
    (fun _ => le_rfl)
  obtain ⟨own, Lq, hr, hle⟩ := mapIn_within (f := fun c : GroupingInput => (c, c)) hsub
  have hX := (basic_facts (hK0.trans_le hKg) hN.P_pos hN.B_pos).1
  refine ⟨C * K ^ g + (𝒯 * (t + 2) + 2), ⟨own, Lq, hMono _ _ _ _ _ _ _ _ _ _ _ _ _ hr le_rfl ?_, hle⟩, real_time_le ?_⟩
  · -- the sizes of the states
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = g * (P + B) + size (a, b) := ⟨_, rfl⟩
    rw [← hZ]
    have hZ2 : 2 ≤ Z := by omega
    have m1 : Z ^ 10 ≤ Z ^ (C + c₁ + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    have m2 : Z ^ C ≤ Z ^ (C + c₁ + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    have m3 : (g * (P + B)) ^ c₁ ≤ Z ^ (C + c₁ + 10) := (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have s1 := search_sizes (s := size (a, b)) hK0 hKg hN.P_pos hN.B_pos (size_netInput_le N hN) (size_pow_le hKg)
    have s4 := size_groupingInput a b K N P B
    have s5 : size x ≤ size (K ^ g) := by
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size hx.le)
    have s6 : size (groupingInput a b K N P B, x) = size (groupingInput a b K N P B) + size x := rfl
    rw [← hZ] at s1
    have key := add_three_le (n := C + c₁ + 10) (u := 2 * size (groupingInput a b K N P B) + size x + 2) (v := Z ^ C) (w := (g * (P + B)) ^ c₁) hZ2 (by omega) m2 m3
    have e : C + c₁ + 12 = C + c₁ + 10 + 2 := by omega
    rw [e]
    omega
  · rw [ht]
    exact time_le (by omega) (Nat.one_le_pow _ _ hK0) Nat.one_le_two_pow hτ

/-- **Lemma 8**, for the procedure of its proof. -/
theorem groupingExplicit : GroupingExplicit :=
  groupingExplicitFrom groupingWithCall labelLengthIsL entryCostExplicit AppRunningTime.groupingSizes stMono stSlowDown stSubstWithin

end ExplicitCost
