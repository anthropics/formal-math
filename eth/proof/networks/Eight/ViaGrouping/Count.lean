/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.SatPsi
public import Eight.SecProof_Network
public import Eight.SecProof_Proof
import all StepMachines.Prog.Count
import Mathlib.Tactic

/-! # Section 6, «Cost», for an algorithm that is given networks as Definition 2 prints them

Here «So … Z is computed in time O(2^{δ'm})» is proved for an algorithm `NA : SecNetworks.NetAlg`,
which is given P and the four procedures of Definition 2(iii),
and which obeys the bound of Lemma 1 (`ViaGrouping.Correct`). The machine is
`NA.app (satProcs g 3)`: NA on the procedures of the network of Φ, with the procedure for Ψ of
proof/networks/Eight/ViaGrouping/SatPsiDefs.lean.
* Lemma 1 applied to the network of Φ: `Correct.onFormula`; the steps of the machine take polynomial
  time: `count_isPolyT`;
* «Cost», in the order of the sentences of the paper: `count_cost_of`, `count_cost_pos_of`.
The sentences on the network itself (what Z is, U < 6m, the exponent, the remaining factor) are
those of proof/networks/Eight/SecProof_Network.lean. -/

public section

namespace Eight.ViaGrouping

open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Paper

/-- **Lemma 1, applied to the network of Φ.** If NA obeys the bound of Lemma 1 with the exponent ε·U +
b·gP/K, then on the procedures of the network of Φ it returns the value Z of that network within
C₁·2^{εU + b·gP/K}·(P + 1)^{C₁} steps: B = 1 and τ = 1. -/
theorem Correct.onFormula {NA : NetAlg} {g K : ℕ} {ε b : ℝ} (hg : 0 < g) (k : ℕ) (h : Correct NA g K ε b) :
    ∃ C₁ : ℕ, ∀ Φ : Fml, ∃ T : ℕ,
      (NA.app (satProcs g k)).Runs Φ T (size Φ + 2 * g + 6 * (mu g Φ * k) + 10 + C₁ * (size Φ + satPf g k Φ + 1) ^ C₁) (wordNet g k Φ).value ∧
      (T : ℝ) ≤ C₁ * (2 : ℝ) ^ (ε * ((wordNet g k Φ).U : ℝ) + b * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C₁ := by
  obtain ⟨C₁, hC₁⟩ := h
  refine ⟨C₁, fun Φ => ?_⟩
  obtain ⟨hN, hv, hU⟩ := satNet_isNetworkP hg k Φ
  obtain ⟨T, hrun, hT⟩ := hC₁ Fml (satProcs g k) Φ (satNet g k Φ) _ _ _ _ hN
  rw [hv] at hrun
  rw [hU, Nat.cast_one, mul_one] at hT
  exact ⟨T, hrun, hT⟩

/-- The machine has polynomial-time steps if the algorithm has them whenever the procedures have and
P is given in unary. -/
theorem count_isPolyT {NA : NetAlg} (h : AlgKeeps NA) (g k : ℕ) : Nonempty (IsPolyT (NA.app (satProcs g k))) := h Fml (satProcs g k) (satProcs_keepsP g k)

/-- The sizes of the states: a polynomial in the size s of Φ. Here μ = m̄ ≤ m < s and P ≤ 2kμ + 1. -/
theorem size_bound {g k C₁ A s μ P : ℕ} (hμ : μ + 1 ≤ s) (hP : P ≤ 2 * (μ * k) + 1) (hA : (6 * k + 2 * g + 11) + C₁ * (2 * k + 3) ^ C₁ + C₁ + 1 ≤ A) :
    s + 2 * g + 6 * (μ * k) + 10 + C₁ * (s + P + 1) ^ C₁ ≤ A * s ^ A := by
  have hsk : μ * k + k ≤ s * k := by
    calc μ * k + k = (μ + 1) * k := by ring
      _ ≤ s * k := Nat.mul_le_mul_right k hμ
  have hgs : g ≤ g * s := Nat.le_mul_of_pos_right _ (by omega)
  have e1 : s + 2 * g + 6 * (μ * k) + 10 ≤ (6 * k + 2 * g + 11) * s := by
    have : (6 * k + 2 * g + 11) * s = 6 * (s * k) + 2 * (g * s) + 11 * s := by ring
    omega
  have e2 : s + P + 1 ≤ (2 * k + 3) * s := by
    have : (2 * k + 3) * s = 2 * (s * k) + 3 * s := by ring
    omega
  have hs1 : 1 ≤ s := by omega
  have p1 : s ≤ s ^ A := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ A := Nat.pow_le_pow_right hs1 (by omega)
  have p2 : s ^ C₁ ≤ s ^ A := Nat.pow_le_pow_right hs1 (by omega)
  calc s + 2 * g + 6 * (μ * k) + 10 + C₁ * (s + P + 1) ^ C₁
      ≤ (6 * k + 2 * g + 11) * s + C₁ * ((2 * k + 3) * s) ^ C₁ := Nat.add_le_add e1 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e2 _))
    _ = (6 * k + 2 * g + 11) * s + C₁ * (2 * k + 3) ^ C₁ * s ^ C₁ := by rw [Nat.mul_pow, Nat.mul_assoc]
    _ ≤ (6 * k + 2 * g + 11) * s ^ A + C₁ * (2 * k + 3) ^ C₁ * s ^ A := Nat.add_le_add (Nat.mul_le_mul_left _ p1) (Nat.mul_le_mul_left _ p2)
    _ = ((6 * k + 2 * g + 11) + C₁ * (2 * k + 3) ^ C₁) * s ^ A := by ring
    _ ≤ A * s ^ A := Nat.mul_le_mul_right _ (by omega)

/-- gP = 2k·g⌈m/g⌉ ≤ 2k(m + g), for P = max{1, 2k·m̄} and k ≥ 1 (for k = 3 the paper's «gP = 6g⌈m/g⌉
≤ 6(m + g)»). -/
theorem mul_satPf_le {k : ℕ} (hk : 1 ≤ k) (g : ℕ) (Φ : Fml) : g * satPf g k Φ ≤ 2 * k * (Φ.length + g) := by
  unfold satPf
  rcases le_total 1 (2 * k * mu g Φ) with h | h
  · rw [max_eq_right h]; exact SatNet.mul_size_le Φ.length g k
  · rw [max_eq_left h, Nat.mul_one]
    calc g ≤ Φ.length + g := Nat.le_add_left _ _
      _ = 1 * (Φ.length + g) := (Nat.one_mul _).symm
      _ ≤ 2 * k * (Φ.length + g) := Nat.mul_le_mul_right _ (by omega)

theorem satPf_le (g k : ℕ) (Φ : Fml) : satPf g k Φ ≤ 2 * (mu g Φ * k) + 1 := by
  have : 2 * k * mu g Φ = 2 * (mu g Φ * k) := by ring
  unfold satPf
  omega

/-! ## «Cost» -/

/-- **Section 6, «Cost», for a named algorithm.** «So … Z is computed in time O(2^{δ'm})», and «Z is
the number of assignments of the variables occurring in Φ that satisfy Φ». If `NA` evaluates the
networks on [g], given as Definition 2 prints them, within the bound of
Lemma 1 with e = δ'/12 and K ≥ 72/δ', the constants of the paper, then `NA` on the network of Φ
(procedure COUNT of Algorithm 1) returns that number within A·2^{δ'm} steps, on states of polynomial
size. The proof goes through the sentences of the paper in their order:
Definition 2 holds, with P = 6m̄ and B = 1 (`satNet_isNetworkP`, inside `Correct.onFormula`); what Z
is (`network_value_eq`); U < 6m (`network_total_lt`) and gP ≤ 6(m + g); the exponent
(`network_exponent_lt'`); the remaining factor (`remaining_factor`).
Different from the paper: the case m = 0, which the paper sets apart, is run through the same
machine (then U = 0, P = 1, P + B = 2 ≤ 2(6m̄ + 1), which costs the constant factor 2^{C₁}, and the
exponent is at most δ'g); only steps are counted here (they take polynomial time when those of `NA`
do: `satProcs_keepsP`), so τ = 1 and there
is no «preparation in time polynomial in n». -/
theorem count_cost_of {g K : ℕ} {δ' : ℝ} {NA : NetAlg} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hg : 0 < g) (hK : 72 / δ' ≤ K)
    (h : Correct NA g K (δ' / 12) (δ' / 12 + 2)) :
    ∃ A : ℕ, ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) →
      ∃ T : ℕ, (NA.app (satProcs g 3)).Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) := by
  -- «Definition 2 holds», and Lemma 1, applied to the network of Φ
  obtain ⟨C₁, hC₁⟩ := h.onFormula hg 3
  -- «The remaining factor … is polynomial in m, hence O(2^{δ'm/4}).»
  obtain ⟨A₁, hA₁⟩ := remaining_factor C₁ g hδ'
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ, A = (6 * 3 + 2 * g + 11) + C₁ * (2 * 3 + 3) ^ C₁ + C₁ + 1 + 2 ^ C₁ * A₁ := ⟨_, rfl⟩
  refine ⟨A, fun Φ hΦ => ?_⟩
  obtain ⟨T, hrun, hT⟩ := hC₁ Φ
  obtain ⟨m, hm⟩ : ∃ m, m = Φ.length := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = mu g Φ := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = size Φ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = satPf g 3 Φ := ⟨_, rfl⟩
  have hms : m + 1 ≤ s := by rw [hm, hs]; exact length_lt_size Φ
  have hμm : μ ≤ m := by rw [hm, hμ]; exact mu_le hg Φ
  have hP1 : P ≤ 2 * (μ * 3) + 1 := by rw [hP, hμ]; exact satPf_le g 3 Φ
  -- «Hence Z is the number of assignments of the variables occurring in Φ that satisfy Φ.»
  have hZ : (wordNet g 3 Φ).value = numSat Φ := network_value_eq hg Φ hΦ
  rw [hZ, ← hP, ← hμ, ← hs] at hrun
  rw [← hP] at hT
  rw [← hm, ← hs]
  refine ⟨T, hrun.mono le_rfl (size_bound (by omega) hP1 (by omega)), ?_⟩
  -- the number of steps. «gP = 6g⌈m/g⌉ ≤ 6(m + g)»
  have hgP : g * P ≤ 6 * (m + g) := by rw [hP, hm]; exact mul_satPf_le (by norm_num) g Φ
  -- «the exponent in Lemma 1 is … ≤ ¾δ'm + δ'g»
  have hexp : δ' / 12 * (((wordNet g 3 Φ).U : ℕ) : ℝ) + (δ' / 12 + 2) * ((g : ℝ) * P) / K ≤ 3 / 4 * δ' * m + δ' * g := by
    rw [SingleBitPieces.exponent_eq]
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · -- m = 0
      have hnil : Φ = [] := List.eq_nil_of_length_eq_zero (hm ▸ h0)
      have hU0 : (wordNet g 3 Φ).U ≤ 6 * m := by rw [hnil]; exact (network_total_nil hg).le.trans (Nat.zero_le _)
      exact SingleBitPieces.network_exponent_le' hδ' h1 hK hU0 hgP
    · -- m ≥ 1: «U ≤ 2(3m − 1) < 6m»
      have hU : (wordNet g 3 Φ).U < 6 * m := hm ▸ network_total_lt hg hΦ (hm ▸ h0)
      exact (network_exponent_lt' hδ' h1 hK hU hgP).le
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

/-- The same in the form that the reduction to sparse formulas takes («… and Φ is satisfiable if and
only if Z > 0»): the machine returns an integer that is positive exactly if Φ is satisfiable. -/
theorem count_cost_pos_of {g K : ℕ} {δ' : ℝ} {NA : NetAlg} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hg : 0 < g) (hK : 72 / δ' ≤ K)
    (h : Correct NA g K (δ' / 12) (δ' / 12 + 2)) :
    ∃ A : ℕ, ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) →
      ∃ (T : ℕ) (v : ℤ), (NA.app (satProcs g 3)).Runs Φ T (A * size Φ ^ A) v ∧ (0 < v ↔ Φ.Sat) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) := by
  obtain ⟨A, hA⟩ := count_cost_of hδ' h1 hg hK h
  refine ⟨A, fun Φ hΦ => ?_⟩
  obtain ⟨T, hrun, hT⟩ := hA Φ hΦ
  exact ⟨T, _, hrun, by rw [Nat.cast_pos]; exact numSat_pos_iff Φ, hT⟩

end Eight.ViaGrouping
