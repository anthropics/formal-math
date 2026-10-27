/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Group.Lemma
public import ClauseBound.Alg.Top
public import ClauseBound.Alg.TopNet
import CountKSat.Value
import CountKSat.InOut
import StepMachines.Prog.NetVal
import StepMachines.Prog.Count
import StepMachines.Math.SatNet

/-! # The top levels of Theorem A(c), by case (i) of Lemma 8

"Let K = K_ℓ, e = e_ℓ for the largest ℓ with K_ℓ ≤ m^{1/9}, and g = 3K⁸ ≤ m": a network on g = 3K⁸
nodes is rebalanced to K nodes and handed to the algorithm for cliques. `val_caseI` calls the lemma
(`GeneralPieces.grouping_general`) in case (i), with ζ = 1/(2K); `Lof_le_of` compares the lemma's L =
⌈(U + gP/K)/K²⌉ with the string lengths of the cliques that the programs build, which are computed
from an upper bound for U.
`stCountG2` is the statement for the network of a k-CNF (the bound in m), `stValS2` the one for any
network (the bound in n). -/

public section

namespace GeneralPieces.Top

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg CountKSat

/-- A network with parameter P is one with every parameter P' ≥ P. -/
theorem sized_mono {J σ τ : Type} [Fintype J] [LinearOrder J] {N : Network J σ τ} {P P' B : ℕ} (h : N.Sized P B) (hP : P ≤ P') : N.Sized P' B :=
  { h with
    card_S := fun a => (h.card_S a).trans (Nat.pow_le_pow_right (by norm_num) hP)
    sum_c := fun a => (h.sum_c a).trans hP }

/-- K^g ≤ 2^(g·size K). -/
theorem pow_le_two_pow (K g : ℕ) : K ^ g ≤ 2 ^ (g * Nat.size K) := by
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_size_self K).le g

/-- With ζ = 1/(2K), the lemma's L = ⌈(U + gP/K)/K²⌉ is at most ⌊(K³ + K·Ub + gP)/K³⌋ for every Ub ≥
U. -/
theorem Lof_le_of {K g P Uv Ub : ℕ} (hK : 0 < K) (hU : Uv ≤ Ub) : AppRunningTime.Lof K g (1 / (2 * (K : ℝ))) P Uv ≤ (K ^ 3 + K * Ub + g * P) / K ^ 3 := by
  have hK3 : 0 < K ^ 3 := Nat.pow_pos hK
  have h1 := Nat.lt_mul_div_succ (K ^ 3 + K * Ub + g * P) hK3
  generalize (K ^ 3 + K * Ub + g * P) / K ^ 3 = β at *
  have h2 : K * Uv + g * P ≤ K ^ 3 * β := by
    have := Nat.mul_le_mul_left K hU
    have e : K ^ 3 * (β + 1) = K ^ 3 * β + K ^ 3 := by ring
    omega
  have h3 : (K : ℝ) * Uv + g * P ≤ (K : ℝ) ^ 3 * β := by exact_mod_cast h2
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold AppRunningTime.Lof
  rw [Nat.ceil_le, div_le_iff₀ (by positivity)]
  have e : (Uv : ℝ) + 2 * (1 / (2 * (K : ℝ))) * g * P = (K * Uv + g * P) / K := by field_simp
  rw [e, div_le_iff₀ hKr]
  calc (K : ℝ) * Uv + g * P ≤ (K : ℝ) ^ 3 * β := h3
    _ = β * (K : ℝ) ^ 2 * K := by ring

/-- 1 ≤ ⌊(K³ + r)/K³⌋. -/
theorem one_le_div {K : ℕ} (r : ℕ) (hK : 0 < K) : 1 ≤ (K ^ 3 + r) / K ^ 3 := by
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos hK)]
  omega

/-- A network on g = 3K⁸ nodes, rebalanced to K nodes by case (i) of Lemma 8 and handed to a correct
algorithm for cliques, gives its value, if β, the string length of the clique handed on, is at
least the lemma's L and the length of the padding string `pad` is at least each of the five powers
`f1`–`f5`, which bound the work. -/
theorem val_caseI {Idx : Type} [Enc Idx] (S : Solver Idx) (ok : Idx → Prop) (hS : S.Correct ok) {C : Type} (F : FNet C) (c : C) (pad : U) (i : Idx)
    (N : Network (Fin (3 * S.K i ^ 8)) (List Bool) (List Bool)) (P B β : ℕ) (hi : ok i) (hK : 2 ≤ S.K i)
    (hN : F.toP.Presents c N 0 0) (hSz : N.Sized P B) (hβ : AppRunningTime.Lof (S.K i) (3 * S.K i ^ 8) (1 / (2 * (S.K i : ℝ))) P N.U ≤ β) (hβ1 : 1 ≤ β)
    (f1 : S.K i ^ (3 * S.K i ^ 8) ≤ pad.length) (f2 : 2 ^ (P * (2 * (3 * S.K i ^ 8) / S.K i)) ≤ pad.length) (f3 : 2 ^ P ≤ pad.length)
    (f4 : 2 ^ ((S.K i - 1) * β) ≤ pad.length)
    (f5 : 2 ^ S.need (i, List.replicate β (), List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) P B) ()) ≤ pad.length) :
    ((rebalG pad (S.K i) (3 * S.K i ^ 8) β F c).elim 0 fun I => S.run (pad, i, I)) = N.value := by
  have hKr : (2 : ℝ) ≤ S.K i := by exact_mod_cast hK
  have hg : 2 ≤ 3 * S.K i ^ 8 := by
    have : 0 < S.K i ^ 8 := Nat.pow_pos (by omega)
    omega
  obtain ⟨J, hJ, hz, hWF⟩ := grouping_general C F c (S.K i) (3 * S.K i ^ 8) (1 / (2 * (S.K i : ℝ))) N P B β pad hK hg (by positivity)
    (by rw [div_le_one (by positivity)]; linarith) hN hSz (Or.inl ⟨rfl, rfl⟩) hβ hβ1 f1 f2 f3 f4
  rw [hJ]
  simp only [Option.elim]
  rw [hS pad i _ _ J hi hβ1 (wfe_mono hWF (min_le_right _ _)) f5, hz]

/-- The algorithm for cliques at the index i, fed with the rebalanced network, returns the value of
the network. -/
theorem stValS2 : StValS := by
  intro Idx _ S ok hS C F c pad i N Ub P B hi hK hN hSz hU hpad
  have hp : ∀ e, e ≤ needNet S i Ub P B → 2 ^ e ≤ pad.length := fun e he => (Nat.pow_le_pow_right (by norm_num) he).trans hpad
  have hK0 : 0 < S.K i := by omega
  unfold valS
  refine val_caseI S ok hS F c pad i N P B _ hi hK hN hSz (Lof_le_of hK0 hU) (by unfold lamS; rw [Nat.add_assoc]; exact one_le_div _ hK0) ?_ ?_ ?_ ?_ ?_
  · exact (pow_le_two_pow _ _).trans (hp _ ((le_max_left _ _).trans (le_max_left _ _)))
  · exact hp _ ((Nat.mul_le_mul_left _ (Nat.le_succ _)).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · exact hp _ ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · exact hp _ ((le_max_left _ _).trans (le_max_right _ _))
  · exact hp _ ((le_max_right _ _).trans (le_max_right _ _))

/-- "So P = 2k⌈m/g⌉, B = 1, U < 2km": the algorithm for cliques at the index i, fed with the
rebalanced network of a k-CNF ψ, returns the value of that network. Here the values of the network
are 0 and ±1,
and B = 0 because bounds are "at most 2^B". -/
theorem stCountG2 (h : StSatPresentsK) : StCountG := by
  intro Idx _ S ok hS pad i k ψ hi hK _ _ hpad
  have hp : ∀ e, e ≤ needTop S i k ψ.length → 2 ^ e ≤ pad.length := fun e he => (Nat.pow_le_pow_right (by norm_num) he).trans hpad
  have hK0 : 0 < S.K i := by omega
  have hg0 : 0 < 3 * S.K i ^ 8 := by
    have : 0 < S.K i ^ 8 := Nat.pow_pos hK0
    omega
  have hN := h (List.replicate (3 * S.K i ^ 8) ()) (List.replicate k ()) ψ (by rw [List.length_replicate]; exact hg0)
  rw [List.length_replicate, List.length_replicate] at hN
  have hSz : (wordNet (3 * S.K i ^ 8) k ψ).Sized (PtopK (3 * S.K i ^ 8) k ψ.length) 0 := sized_mono (sized_wordNet hg0 0) (le_max_right _ _)
  have hU : (wordNet (3 * S.K i ^ 8) k ψ).U ≤ 2 * k * ψ.length := by
    rw [U_wordNet hg0]
    exact SatNet.U_net_le
  unfold countG
  rw [List.length_replicate]
  refine val_caseI S ok hS satFk _ pad i _ _ 0 _ hi hK hN hSz (Lof_le_of hK0 hU) (by unfold lamTopK; rw [Nat.add_assoc]; exact one_le_div _ hK0) ?_ ?_ ?_ ?_ ?_
  · exact (pow_le_two_pow _ _).trans (hp _ ((le_max_left _ _).trans (le_max_left _ _)))
  · exact hp _ ((Nat.mul_le_mul_left _ (Nat.le_succ _)).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · exact hp _ ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · exact hp _ ((le_max_left _ _).trans (le_max_right _ _))
  · have e : bitsS (S.K i) (3 * S.K i ^ 8) (PtopK (3 * S.K i ^ 8) k ψ.length) 0 = PtopK (3 * S.K i ^ 8) k ψ.length * (2 * (3 * S.K i ^ 8) / S.K i) := by
      simp [bitsS]
    rw [e]
    exact hp _ ((le_max_right _ _).trans (le_max_right _ _))

end GeneralPieces.Top
