/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/Tail.lean — the K-tail of the dyadic majorant is uniformly small (used in
the H3 assembly in Coeff/DiagLaw.lean).

Per-term input (Coeff/Upper.lean, Fmaj_term_le): under x·u ≤ 4 and 32eK·x ≤ 1,
  2^{i+1} x^{2(i+1)} u^{i+1} Σ_{N≤e^u}Λ^{∗(i+1)}(N)/N ≤ 64^{i+1}/(i+1)! + 2^{−(i+1)} =: tailMaj i,
a summable sequence independent of (x,u).  Hence for every ε > 0 there is K with
  Σ_{K ≤ i < X} (term i) ≤ Σ_{i ≥ K} tailMaj i ≤ ε   uniformly in x, u, X.     (Fmaj_tail_small)
-/
import Zeta23.XiPrime.Coeff.Upper
import Mathlib.Analysis.SpecificLimits.Normed

open scoped BigOperators ArithmeticFunction
open Finset Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

/-- the (x,u)-free summable majorant of the dyadic terms. -/
def tailMaj (i : ℕ) : ℝ := (64:ℝ) ^ (i + 1) / ((i + 1).factorial : ℝ) + (1 / 2 : ℝ) ^ (i + 1)

lemma tailMaj_nonneg (i : ℕ) : 0 ≤ tailMaj i := by unfold tailMaj; positivity

lemma summable_tailMaj : Summable tailMaj := by
  have h1 : Summable (fun i : ℕ => (64:ℝ) ^ (i + 1) / ((i + 1).factorial : ℝ)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial 64)
  have h2 : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  exact h1.add h2

/-- the truncated majorant 𝟙_{K ≤ i}·tailMaj i. -/
def tailMajFrom (K i : ℕ) : ℝ := if K ≤ i then tailMaj i else 0

lemma tailMajFrom_nonneg (K i : ℕ) : 0 ≤ tailMajFrom K i := by
  unfold tailMajFrom; split_ifs <;> simp [tailMaj_nonneg]

lemma tailMajFrom_le (K i : ℕ) : tailMajFrom K i ≤ tailMaj i := by
  unfold tailMajFrom; split_ifs <;> simp [tailMaj_nonneg]

lemma summable_tailMajFrom (K : ℕ) : Summable (tailMajFrom K) :=
  summable_tailMaj.of_nonneg_of_le (tailMajFrom_nonneg K) (tailMajFrom_le K)

/-- Σ' i, 𝟙_{K≤i} tailMaj i = Σ' j, tailMaj (j + K). -/
lemma tsum_tailMajFrom (K : ℕ) : ∑' i, tailMajFrom K i = ∑' j, tailMaj (j + K) := by
  rw [← (summable_tailMajFrom K).sum_add_tsum_nat_add K]
  have h0 : ∑ i ∈ range K, tailMajFrom K i = 0 :=
    sum_eq_zero fun i hi => by
      have : ¬ K ≤ i := by simpa using hi
      simp [tailMajFrom, this]
  have h1 : (fun j => tailMajFrom K (j + K)) = fun j => tailMaj (j + K) := by
    ext j; simp [tailMajFrom]
  rw [h0, zero_add, h1]

/-- **the K-tail of the dyadic majorant is uniformly small.** -/
theorem Fmaj_tail_small : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ (x u : ℝ), 0 ≤ x → 0 ≤ u → x * u ≤ 4 →
    32 * Real.exp 1 * KM * x ≤ 1 → ∀ X : ℕ,
      (∑ i ∈ (Finset.range X).filter (fun i => K ≤ i),
        2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * Sdiv (Λ ^ (i + 1)) u) ≤ ε := by
  intro ε hε
  have ht : Tendsto (fun K => ∑' j, tailMaj (j + K)) atTop (𝓝 0) := tendsto_sum_nat_add tailMaj
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨K, hK⟩ := ht ε hε
  refine ⟨K, fun x u hx hu hxu hxK X => ?_⟩
  have hKK := hK K le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun j => tailMaj_nonneg _)] at hKK
  calc ∑ i ∈ (range X).filter (fun i => K ≤ i),
          2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * Sdiv (Λ ^ (i + 1)) u
      ≤ ∑ i ∈ (range X).filter (fun i => K ≤ i), tailMajFrom K i := by
        refine sum_le_sum fun i hi => ?_
        have hKi : K ≤ i := (mem_filter.mp hi).2
        simp only [tailMajFrom, hKi, if_true, tailMaj]
        exact Fmaj_term_le hx hu hxu hxK i
    _ ≤ ∑' i, tailMajFrom K i :=
        (summable_tailMajFrom K).sum_le_tsum _ fun i _ => tailMajFrom_nonneg K i
    _ = ∑' j, tailMaj (j + K) := tsum_tailMajFrom K
    _ ≤ ε := hKK.le

end XiPrime
end Zeta23
