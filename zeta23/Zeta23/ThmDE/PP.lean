/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmDE/PP.lean.  The §7.1 partial-summation step for a
Dirichlet character: [thm:E] proof (iii) "Σ_{(n,q)=1} Λ(n)²/n = (log²x)/2 + O_q(log x)"
([eq:cheb2a] for n coprime to q, Zeta23.ThmE.ChebyshevMertensCoprime.cheb2a) fed into the abstract
Abel-summation lemma Zeta23.ThmD.abel_sum_close:
  Σ_{n≤X,(n,q)=1} Λ(n)²/n · g(log n) = ∫_0^L g(y)·y dy + O_q(L²)   (g C¹, |g'| ≤ 2, g ≡ 0 on [L,∞)).
-/
import Zeta23.ThmD.PP
import Zeta23.ThmE.PPChi

noncomputable section

open Real Finset
open scoped ArithmeticFunction

namespace Zeta23
namespace ThmDE

/-- the coprime partial-summation step (χ-version of Zeta23.ThmD.sumA2g_close). -/
theorem sumA2gCoprime_close {q : ℕ} (hchebq : ThmE.ChebyshevMertensCoprime q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L X : ℝ) (g : ℝ → ℝ), 8 ≤ L → X = Real.exp L →
      Differentiable ℝ g → Continuous (deriv g) → (∀ y : ℝ, |deriv g y| ≤ 2) →
      (∀ y : ℝ, L ≤ y → g y = 0) →
      |ThmE.sumA2gCoprime q X g - ∫ y in (0:ℝ)..L, g y * y| ≤ C * L ^ 2 := by
  classical
  obtain ⟨C₀, hC₀⟩ := hchebq.cheb2a
  set c : ℕ → ℝ := fun n => if Nat.Coprime n q then (Λ n : ℝ) ^ 2 / n else 0 with hcdef
  have hC₀' : ∀ t : ℝ, 2 ≤ t →
      |(∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, c k) - Real.log t ^ 2 / 2| ≤ C₀ * Real.log t := by
    intro t ht
    have := hC₀ t ht
    rwa [Finset.sum_filter] at this
  refine ⟨2 * |C₀| + 10, by positivity, fun L X g hL hX hgd hg'c hg'le hgsupp => ?_⟩
  have h := ThmD.abel_sum_close (c := c) (by simp [hcdef]) (by simp [hcdef]) hC₀' L X g hL hX
    hgd hg'c hg'le hgsupp
  have e : ThmE.sumA2gCoprime q X g = ∑ n ∈ PrimeSide.primeRange X, c n * g (Real.log n) := by
    unfold ThmE.sumA2gCoprime PrimeSide.primeRange
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hcdef]
    split_ifs <;> simp
  rw [e]
  exact h

end ThmDE
end Zeta23

end
