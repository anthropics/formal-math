/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Basic.lean — shared elementary definitions for prop:tail (the paper §4.2).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace Zeta23
namespace Tail

/-- Distance from γ to the interval I = [T, 2T] (paper: D := dist(γ, I) in the proof of
[prop:tail]); equals 0 for γ ∈ I, T − γ for γ < T, γ − 2T for γ > 2T. -/
def distI (T γ : ℝ) : ℝ := max 0 (max (T - γ) (γ - 2 * T))

lemma distI_nonneg (T γ : ℝ) : 0 ≤ distI T γ := le_max_left _ _

lemma distI_of_le {T γ : ℝ} (hT : 0 ≤ T) (h : γ ≤ T) : distI T γ = T - γ := by
  unfold distI
  have h1 : max (T - γ) (γ - 2 * T) = T - γ := max_eq_left (by linarith)
  rw [h1, max_eq_right (by linarith)]

lemma distI_of_ge {T γ : ℝ} (hT : 0 ≤ T) (h : 2 * T ≤ γ) : distI T γ = γ - 2 * T := by
  unfold distI
  have h1 : max (T - γ) (γ - 2 * T) = γ - 2 * T := max_eq_right (by linarith)
  rw [h1, max_eq_right (by linarith)]

/-- The tail predicate: ordinate γ ∉ I' := (T − D₀, 2T + D₀], D₀ := T^{1/2} [eq:D0].
(Paper: "split the sum [eq:Gdef] over distinct zeros according to whether the ordinate
γ = Re γ_ρ lies in I'"; E is the part with γ ∉ I' [eq:AE]. Note: this includes all
zeros with γ ≤ 0.) -/
def InTail (T γ : ℝ) : Prop := γ ≤ T - Real.sqrt T ∨ 2 * T + Real.sqrt T < γ

lemma InTail_iff_not_mem_Ioc (T γ : ℝ) :
    InTail T γ ↔ γ ∉ Set.Ioc (T - Real.sqrt T) (2 * T + Real.sqrt T) := by
  simp only [InTail, Set.mem_Ioc, not_and_or, not_lt, not_le]

lemma sqrt_le_distI_of_InTail {T γ : ℝ} (hT : 0 ≤ T) (h : InTail T γ) :
    Real.sqrt T ≤ distI T γ := by
  have hs := Real.sqrt_nonneg T
  rcases h with h | h
  · rw [distI_of_le hT (by linarith)]; linarith
  · rw [distI_of_ge hT (by linarith)]; linarith

/-- Explicit absolute threshold standing in for "T ≥ T₀" in [prop:tail]. Chosen ≥ 256 ≥ 16π²
(using only π ≤ 4) so that log(4T) ≤ 2·log(T/2π) = 2l (used in the "so that
θ₀ ≤ 32A₀‖ϱ″‖₁² l T^{λ/2−1}" clause); the zero-count estimate needs far less. Any larger
absolute constant would also do. -/
def T₀ : ℝ := 300

lemma T₀_pos : 0 < T₀ := by norm_num [T₀]

/-- Local zero-count hypothesis of [prop:tail]: "Let A₀ ≥ 1 be an absolute constant such
that N(t+1) − N(t) ≤ A₀ log(t+3) for all t ≥ 0" [Tit86, Thm 9.2], for an abstract family of
ordinates γ : ι → ℝ with multiplicities m : ι → ℕ. We use the two-sided unit-window form
(all real t, bound A₀·log(|t|+3)) as in PaperInputs.RvM.local: it is
equally classical and covers the zeros with γ ≤ 0 — which are in the tail
(paper: "zeros with γ ≤ 0 have D ≥ T and contribute at most ∑_{j≥0} A₀ log(j+4)(T+j)⁻³",
silently using the γ ↦ −γ symmetry and ζ(σ) ≠ 0 for 0<σ<1) — with no separate seam fact.
Stated for finite sub-families so that no summability is presupposed; instantiated from
ZeroConfig + PaperInputs.RvM.local in Zeta23/Tail.lean (LocalCount.ofWindowCount). -/
structure LocalCount {ι : Type*} (γ : ι → ℝ) (m : ι → ℕ) (A₀ : ℝ) : Prop where
  one_le : 1 ≤ A₀
  window : ∀ t : ℝ, ∀ s : Finset ι, (∀ ρ ∈ s, t < γ ρ ∧ γ ρ ≤ t + 1) →
    (∑ ρ ∈ s, (m ρ : ℝ)) ≤ A₀ * Real.log (|t| + 3)

lemma LocalCount.A₀_pos {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ : ℝ}
    (h : LocalCount γ m A₀) : 0 < A₀ := lt_of_lt_of_le one_pos h.one_le

end Tail
end Zeta23
