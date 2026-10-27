/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Achievable
public import Printed.HandOver
public import Eight.ViaGrouping.Count
import Mathlib.Tactic

/-! # Section 6, «Cost», for a machine that does what Lemma 1 says

Section 6: the network of Φ on g clusters satisfies Definition 2 with P = 6m̄ and B = 1; Lemma 1 is
applied to it; «So … Z is computed in time O(2^{δ'm})». Here Lemma 1 is `Printed.ComputesNetworks`
(PrintedStatement.lean): a machine with query access, in which each query of Definition 2(iii) costs
τ operations. Its queries are answered by the procedures of the network of Φ (`formulaProcs`), one
step each.
* `formula_isNetwork`: «Definition 2 holds», with B = 1 handed over;
* `onFormula`: Lemma 1 applied to the network of Φ (through `StOnProcedures`, a hypothesis here);
* `cost_of_bound`: the paragraph «Cost», sentence by sentence, for any step machine that obeys the
  bound of Lemma 1 on the network of Φ. It is the proof of `Eight.ViaGrouping.count_cost_of`
  (proof/networks/Eight/ViaGrouping/Count.lean) after its first line, which does not look at the
  machine again;
* `cost_with_first_line`: line 6 of Algorithm 1, «if m = 0 then return 1»;
* `stCountCost_of`: «Cost» for Count(ℓ). -/

public section

namespace Printed

open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines

/-! ### «Definition 2 holds» -/

/-- The network of Φ, given by the procedures `formulaProcs`, is a network in the sense of
Definition 2 with parameters P = max{1, 2k·m̄}, B = 1, τ = 1. This is
`Eight.ViaGrouping.satNet_isNetworkP`; what is added is that the procedures hand over B = 1. -/
theorem formula_isNetwork {g : ℕ} (hg : 0 < g) (k : ℕ) (Φ : Fml) :
    SecNetworks.IsNetwork (formulaProcs g k) Φ (satNet g k Φ) (satPf g k Φ) 1 1 (size Φ + 2 * g + 6 * (mu g Φ * k) + 8 + 2) :=
  have h := (satNet_isNetworkP hg k Φ).1
  ⟨h.is, h.τ_pos,
    { P_eq := h.given.P_eq, B_eq := rfl, len_eq := h.given.len_eq, cap_eq := h.given.cap_eq, mem_runs := h.given.mem_runs, W_runs := h.given.W_runs, Ψ_runs := h.given.Ψ_runs, f_runs := h.given.f_runs }⟩

/-- The procedures have polynomial-time steps and the lengths are given in unary. -/
theorem formulaProcs_keeps (g k : ℕ) : (formulaProcs g k).Keeps :=
  have h := (satProcs_keepsP g k).keeps
  ⟨h.len, h.cap, h.mem, h.W, h.Ψ, h.f⟩

/-- A machine for networks with polynomial-time steps, on the network of Φ: polynomial-time steps. -/
theorem onFormula_poly (g k : ℕ) (NM : NetMachine) (hN : NM.PolyTimeSteps) : Nonempty (IsPolyT (networkOnSteps g NM (formulaProcs g k))) :=
  networkOnSteps_poly g NM _ hN (formulaProcs_keeps g k) (satProcs_keepsP g k).P (Unary.const 1)

/-! ### Lemma 1, applied to the network of Φ -/

/-- The part of the states that comes from answering the queries by procedures, put under one
constant. -/
theorem size_under (s P C₁ : ℕ) : s + C₁ * (P + 1) ^ C₁ + 4 ≤ (3 * C₁ + 5) * (s + P + 1) ^ (3 * C₁ + 5) := by
  have p1 : s + P + 1 ≤ (s + P + 1) ^ (3 * C₁ + 5) := Nat.le_self_pow (by omega) _
  have p2 : (P + 1) ^ C₁ ≤ (s + P + 1) ^ (3 * C₁ + 5) := (Nat.pow_le_pow_left (by omega) C₁).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have p3 := Nat.mul_le_mul_left C₁ p2
  have e : (3 * C₁ + 5) * (s + P + 1) ^ (3 * C₁ + 5) = 5 * (s + P + 1) ^ (3 * C₁ + 5) + C₁ * (s + P + 1) ^ (3 * C₁ + 5) + 2 * (C₁ * (s + P + 1) ^ (3 * C₁ + 5)) := by ring
  omega

/-- **Lemma 1, applied to the network of Φ.** If NM does what Lemma 1 says for (K, e) on networks on
[g], then NM, with its queries answered by the procedures of the network of Φ, returns the value Z
of that network within C·2^{eU + (e+2)·gP/K}·(P + 1)^C steps: B = 1 and τ = 1. The bounds are
written as in `Eight.ViaGrouping.Correct.onFormula`; C = 3C₁ + 5 (the 3 is that of `StOnProcedures`:
a query takes τ + 2 ≤ 3τ steps). -/
theorem onFormula (hOn : StOnProcedures) {NM : NetMachine} {C₁ g K : ℕ} {e : ℝ} (hg : 0 < g) (k : ℕ) (h : ComputesNetworks NM C₁ g K e) :
    ∃ C : ℕ, ∀ Φ : Fml, ∃ T : ℕ,
      (networkOnSteps g NM (formulaProcs g k)).Runs Φ T (size Φ + 2 * g + 6 * (mu g Φ * k) + 10 + C * (size Φ + satPf g k Φ + 1) ^ C) (wordNet g k Φ).value ∧
      (T : ℝ) ≤ C * (2 : ℝ) ^ (e * ((wordNet g k Φ).U : ℝ) + (e + 2) * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C := by
  refine ⟨3 * C₁ + 5, fun Φ => ?_⟩
  obtain ⟨_, hv, hU⟩ := satNet_isNetworkP hg k Φ
  obtain ⟨T, hrun, hT⟩ := hOn NM C₁ g K e h Fml (formulaProcs g k) Φ (satNet g k Φ) _ _ _ _ (formula_isNetwork hg k Φ)
  rw [hv] at hrun
  rw [hU, Nat.cast_one, mul_one] at hT
  refine ⟨T, hrun.mono le_rfl ?_, hT.trans ?_⟩
  · have := size_under (size Φ) (satPf g k Φ) C₁
    omega
  · have he : e * ((wordNet g k Φ).U : ℝ) + (e + 2) * ((g : ℝ) * (satPf g k Φ : ℝ)) / K = e * (((wordNet g k Φ).U : ℝ) + (g : ℝ) * (satPf g k Φ : ℝ) / K) + 2 * ((g : ℝ) * (satPf g k Φ : ℝ)) / K := by ring
    rw [he]
    have hY : (1 : ℝ) ≤ (satPf g k Φ : ℝ) + 1 := by linarith [(Nat.cast_nonneg (satPf g k Φ) : (0 : ℝ) ≤ _)]
    have h2 : ((satPf g k Φ : ℝ) + 1) ^ C₁ ≤ ((satPf g k Φ : ℝ) + 1) ^ (3 * C₁ + 5) := pow_le_pow_right₀ hY (by omega)
    have h3 : 3 * (C₁ : ℝ) ≤ ((3 * C₁ + 5 : ℕ) : ℝ) := by push_cast; linarith
    calc 3 * ((C₁ : ℝ) * (2 : ℝ) ^ (e * (((wordNet g k Φ).U : ℝ) + (g : ℝ) * (satPf g k Φ : ℝ) / K) + 2 * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C₁)
        = 3 * (C₁ : ℝ) * (2 : ℝ) ^ (e * (((wordNet g k Φ).U : ℝ) + (g : ℝ) * (satPf g k Φ : ℝ) / K) + 2 * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C₁ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right h3 (by positivity)) h2 (by positivity) (by positivity)

/-! ### «Cost» -/

/-- A list is shorter than its size. -/
theorem length_lt_size {α : Type} [HasSize α] (l : List α) : l.length < size l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [size_list, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- **Section 6, «Cost».** «So … Z is computed in time O(2^{δ'm})», and «Z is the number of
assignments of the variables occurring in Φ that satisfy Φ», for any step machine Mc that returns
the value of the network of Φ within the bound of Lemma 1 with e = δ'/12 and K ≥ 72/δ'. The
sentences of the paper in their order: what Z is (`Eight.network_value_eq`); U < 6m
(`Eight.network_total_lt`) and gP ≤ 6(m + g); the exponent (`Eight.network_exponent_lt'`); the
remaining factor (`Eight.remaining_factor`). The case m = 0 is run through as well (then U = 0, P = 1). -/
theorem cost_of_bound {g K : ℕ} {δ' : ℝ} {Mc : Stepped Fml ℤ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hg : 0 < g) (hK : 72 / δ' ≤ K)
    (h : ∃ C₁ : ℕ, ∀ Φ : Fml, ∃ T : ℕ,
      Mc.Runs Φ T (size Φ + 2 * g + 6 * (mu g Φ * 3) + 10 + C₁ * (size Φ + satPf g 3 Φ + 1) ^ C₁) (wordNet g 3 Φ).value ∧
      (T : ℝ) ≤ C₁ * (2 : ℝ) ^ (δ' / 12 * ((wordNet g 3 Φ).U : ℝ) + (δ' / 12 + 2) * ((g : ℝ) * (satPf g 3 Φ : ℝ)) / K) * ((satPf g 3 Φ : ℝ) + 1) ^ C₁) :
    ∃ A : ℕ, ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) →
      ∃ T : ℕ, Mc.Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) := by
  obtain ⟨C₁, hC₁⟩ := h
  -- «The remaining factor … is polynomial in m, hence O(2^{δ'm/4}).»
  obtain ⟨A₁, hA₁⟩ := Eight.remaining_factor C₁ g hδ'
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ, A = (6 * 3 + 2 * g + 11) + C₁ * (2 * 3 + 3) ^ C₁ + C₁ + 1 + 2 ^ C₁ * A₁ := ⟨_, rfl⟩
  refine ⟨A, fun Φ hΦ => ?_⟩
  obtain ⟨T, hrun, hT⟩ := hC₁ Φ
  obtain ⟨m, hm⟩ : ∃ m, m = Φ.length := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = mu g Φ := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = size Φ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = satPf g 3 Φ := ⟨_, rfl⟩
  have hms : m + 1 ≤ s := by rw [hm, hs]; exact length_lt_size Φ
  have hμm : μ ≤ m := by rw [hm, hμ]; exact mu_le hg Φ
  have hP1 : P ≤ 2 * (μ * 3) + 1 := by rw [hP, hμ]; exact Eight.ViaGrouping.satPf_le g 3 Φ
  -- «Hence Z is the number of assignments of the variables occurring in Φ that satisfy Φ.»
  have hZ : (wordNet g 3 Φ).value = numSat Φ := Eight.network_value_eq hg Φ hΦ
  rw [hZ, ← hP, ← hμ, ← hs] at hrun
  rw [← hP] at hT
  rw [← hm, ← hs]
  refine ⟨T, hrun.mono le_rfl (Eight.ViaGrouping.size_bound (by omega) hP1 (by omega)), ?_⟩
  -- «gP = 6g⌈m/g⌉ ≤ 6(m + g)»
  have hgP : g * P ≤ 6 * (m + g) := by rw [hP, hm]; exact Eight.ViaGrouping.mul_satPf_le (by norm_num) g Φ
  -- «the exponent in Lemma 1 is … ≤ ¾δ'm + δ'g»
  have hexp : δ' / 12 * (((wordNet g 3 Φ).U : ℕ) : ℝ) + (δ' / 12 + 2) * ((g : ℝ) * P) / K ≤ 3 / 4 * δ' * m + δ' * g := by
    rw [SingleBitPieces.exponent_eq]
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · -- m = 0
      have hnil : Φ = [] := List.eq_nil_of_length_eq_zero (hm ▸ h0)
      have hU0 : (wordNet g 3 Φ).U ≤ 6 * m := by rw [hnil]; exact (Eight.network_total_nil hg).le.trans (Nat.zero_le _)
      exact SingleBitPieces.network_exponent_le' hδ' h1 hK hU0 hgP
    · -- m ≥ 1: «U ≤ 2(3m − 1) < 6m»
      have hU : (wordNet g 3 Φ).U < 6 * m := hm ▸ Eight.network_total_lt hg hΦ (hm ▸ h0)
      exact (Eight.network_exponent_lt' hδ' h1 hK hU hgP).le
  have hE : (2 : ℝ) ^ (δ' / 12 * (((wordNet g 3 Φ).U : ℕ) : ℝ) + (δ' / 12 + 2) * ((g : ℝ) * P) / K) ≤ (2 : ℝ) ^ (3 / 4 * δ' * m) * (2 : ℝ) ^ (δ' * g) := by
    rw [← Real.rpow_add two_pos]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hexp
  -- P + B = 6m̄ + 1 for m ≥ 1; for m = 0 it is 2
  have hPB : (P : ℝ) + 1 ≤ 2 * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) := by
    have : P + 1 ≤ 2 * (6 * ((m + g - 1) / g) + 1) := by
      have e : (m + g - 1) / g = μ := by rw [hm, hμ]; rfl
      rw [e]; omega
    exact_mod_cast this
  have hsplit : (2 : ℝ) ^ (3 / 4 * δ' * m) * (2 : ℝ) ^ (δ' * m / 4) = (2 : ℝ) ^ (δ' * m) := by
    rw [← Real.rpow_add two_pos]
    congr 1
    ring
  calc (T : ℝ) ≤ C₁ * (2 : ℝ) ^ (δ' / 12 * (((wordNet g 3 Φ).U : ℕ) : ℝ) + (δ' / 12 + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + 1) ^ C₁ := hT
    _ ≤ C₁ * ((2 : ℝ) ^ (3 / 4 * δ' * m) * (2 : ℝ) ^ (δ' * g)) * (2 * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ)) ^ C₁ := by gcongr
    _ = 2 ^ C₁ * (2 : ℝ) ^ (3 / 4 * δ' * m) * ((C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * (((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ)) ^ C₁) := by rw [mul_pow]; ring
    _ ≤ 2 ^ C₁ * (2 : ℝ) ^ (3 / 4 * δ' * m) * (A₁ * (2 : ℝ) ^ (δ' * m / 4)) := mul_le_mul_of_nonneg_left (hA₁ m) (by positivity)
    _ = ((2 ^ C₁ * A₁ : ℕ) : ℝ) * (2 : ℝ) ^ (δ' * m) := by rw [← hsplit]; push_cast; ring
    _ ≤ A * (2 : ℝ) ^ (δ' * m) := by
        gcongr
        omega

/-! ### «if m = 0 then return 1» -/

/-- **Line 6 of Algorithm 1** in front of a machine that counts: the bounds hold with A + 4 in the
place of A. On the formula without clauses the result 1 is the number of satisfying assignments of
no variables (`Eight.numSat_nil`), after one step. -/
theorem cost_with_first_line {Mc : Stepped Formula ℤ} {δ' : ℝ} {A : ℕ}
    (h : ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, Mc.Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)) :
    ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, (Stepped.ite (fun Φ : Formula => Φ.isEmpty) (Stepped.const 1) Mc).Runs Φ T ((A + 4) * size Φ ^ (A + 4)) (numSat Φ) ∧
      (T : ℝ) ≤ ((A + 4 : ℕ) : ℝ) * (2 : ℝ) ^ (δ' * Φ.length) := by
  intro Φ hΦ
  cases Φ with
  | nil =>
    refine ⟨1, ?_, ?_⟩
    · rw [Eight.numSat_nil, Nat.cast_one]
      refine (Stepped.ite_runs_true (p := fun Φ : Formula => Φ.isEmpty) rfl (Stepped.const_runs (1 : ℤ) ([] : Formula))).mono le_rfl ?_
      have h0 : size ([] : Formula) = 1 := rfl
      have h1 : size (1 : ℤ) ≤ 2 := by simp
      rw [h0, one_pow, mul_one]
      omega
    · have e : (2 : ℝ) ^ (δ' * (([] : Formula).length : ℝ)) = 1 := by simp
      rw [e, mul_one]
      exact_mod_cast (by omega : 1 ≤ A + 4)
  | cons C Ψ =>
    obtain ⟨T, hr, hT⟩ := h (C :: Ψ) hΦ
    refine ⟨T, (Stepped.ite_runs_false (p := fun Φ : Formula => Φ.isEmpty) rfl hr).mono le_rfl ?_, hT.trans ?_⟩
    · have hs : 1 ≤ size (C :: Ψ) := by have := length_lt_size (C :: Ψ); omega
      have p1 := Nat.mul_le_mul_left A (Nat.pow_le_pow_right hs (by omega : A ≤ A + 4))
      have p0 : 1 ≤ size (C :: Ψ) ^ (A + 4) := Nat.one_le_pow _ _ hs
      have e : (A + 4) * size (C :: Ψ) ^ (A + 4) = A * size (C :: Ψ) ^ (A + 4) + 4 * size (C :: Ψ) ^ (A + 4) := by ring
      omega
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : A ≤ A + 4)) (by positivity)

/-- Line 6 keeps polynomial-time steps. -/
theorem firstLine_poly {Mc : Stepped Formula ℤ} (h : Nonempty (IsPolyT Mc)) : Nonempty (IsPolyT (Stepped.ite (fun Φ : Formula => Φ.isEmpty) (Stepped.const 1) Mc)) := by
  obtain ⟨h⟩ := h
  have := IsPolyT.const (α := Formula) (1 : ℤ)
  exact ⟨IsPolyT.ite (by fun_prop)⟩

/-! ### Count(ℓ) -/

/-- **Section 6, «Cost», for Count**, from «(K_ℓ, e_ℓ) is achievable» by Clique(ℓ), Lemma 1 for the
algorithm of its proof, its polynomial-time steps, and Lemma 1 for networks given by procedures. -/
theorem stCountCost_of (hC : StClique) (hG : StGroupingTied) (hGp : StGroupingPoly) (hOn : StOnProcedures) : StCountCost := by
  intro δ' ℓ hδ' h1 hK hE
  obtain ⟨hp, Cc, hA⟩ := hC ℓ
  have hK2 : 2 ≤ levelK ℓ := (by norm_num : 2 ≤ 64).trans (levelK_ge ℓ)
  obtain ⟨C₁, hC₁⟩ := hG (levelK ℓ) (δ' / 12) (CLIQUE ℓ) Cc hK2 (by positivity) (hA.mono hE)
  have hC₁' : ComputesNetworks (NETWORK ℓ) C₁ (levelG ℓ) (levelK ℓ) (δ' / 12) := hC₁
  have hg : 0 < levelG ℓ := Nat.mul_pos (by norm_num) (pow_pos (by omega) 8)
  obtain ⟨A, hA'⟩ := cost_of_bound hδ' h1 hg hK (onFormula hOn hg 3 hC₁')
  exact ⟨firstLine_poly (onFormula_poly _ 3 _ (hGp _ _ _ hp)), A + 4, cost_with_first_line hA'⟩

end Printed
