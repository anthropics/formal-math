/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# The Preissmann–Lévêque eigen-identity (arXiv:2203.14950 Lemma 2.1)

For real `c_r > 0`, injective real `freq`, complex `u` and real `μ` with the eigen-relation
`Σ_{n≠m} c_m c_n u_n/(freq m − freq n) = iμ u_m` for every `m`, we prove, for every `m`,

  `μ² |u_m|² = Σ_{n≠m} c_m² c_n² |u_n|²/(freq m − freq n)²
               + 2 Σ_{n≠m} c_m³ c_n Re(u_m ū_n)/(freq m − freq n)²`.

Proof (pure finite algebra): expand `|iμ u_m|²` as a double sum over `(n,p)`; the diagonal
`p = n` is the first term; off the diagonal use the partial fraction
`1/((λm−λn)(λm−λp)) = 1/((λm−λn)(λn−λp)) − 1/((λm−λp)(λn−λp))` to write the summand as
`G(n,p) + G(p,n)`, so the off-diagonal part is `2 Σ_n Σ_{p≠n,m} G(n,p)`; the inner sum is
`Re(u_n · W_n)` with `W_n = Σ_{p≠n,m} c_p ū_p/(λn−λp)`, and the conjugate eigen-relation at `n`
gives `W_n = −iμ ū_n/c_n − c_m ū_m/(λn−λm)`; the `−iμ|u_n|²/c_n` piece is purely imaginary and
dies under `Re` — the Montgomery–Vaughan cancellation — leaving the second term.
-/

noncomputable section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq : ι → ℝ}

/-- `‖z‖² = Re(z z̄)`. -/
private lemma norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- `Re(u_n ū_p)` is symmetric in `(n,p)`. -/
private lemma re_mul_conj_comm (a b : ℂ) : (a * conj b).re = (b * conj a).re := by
  simp [Complex.mul_re]; ring

/-- **Preissmann–Lévêque eigen-identity** (arXiv:2203.14950 Lemma 2.1). -/
theorem eigen_identity' (hinj : Function.Injective freq) (c : ι → ℝ) (hc : ∀ r, 0 < c r)
    (u : ι → ℂ) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
        ((c m * c n / (freq m - freq n) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m)
    (m : ι) :
    μ ^ 2 * ‖u m‖ ^ 2 =
      (∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2)
      + 2 * ∑ n ∈ Finset.univ.erase m,
          c m ^ 3 * c n * (u m * conj (u n)).re / (freq m - freq n) ^ 2 := by
  classical
  set S : Finset ι := Finset.univ.erase m with hSdef
  have hmemS : ∀ {n : ι}, n ∈ S → n ≠ m := fun h => (Finset.mem_erase.mp h).1
  have hfr : ∀ {n p : ι}, n ≠ p → freq n - freq p ≠ 0 :=
    fun h => sub_ne_zero.mpr (fun e => h (hinj e))
  -- real coefficients a_n := c_m c_n/(λ_m − λ_n) and the real numbers R n p := Re(u_n ū_p)
  set a : ι → ℝ := fun n => c m * c n / (freq m - freq n) with hadef
  set R : ι → ι → ℝ := fun n p => (u n * conj (u p)).re with hRdef
  have hRsymm : ∀ n p, R n p = R p n := fun n p => re_mul_conj_comm _ _
  have hRdiag : ∀ n, R n n = ‖u n‖ ^ 2 := fun n => (norm_sq_eq_re_mul_conj _).symm
  /- Step A: μ²|u_m|² = Σ_n Σ_p a_n a_p R(n,p). -/
  have hA : μ ^ 2 * ‖u m‖ ^ 2 = ∑ n ∈ S, ∑ p ∈ S, a n * a p * R n p := by
    have h1 : μ ^ 2 * ‖u m‖ ^ 2 = ‖(μ : ℂ) * Complex.I * u m‖ ^ 2 := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, mul_pow,
        Real.norm_eq_abs, sq_abs]
    rw [h1, ← heig m, norm_sq_eq_re_mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    have : ((a n : ℝ) : ℂ) * u n * (((a p : ℝ) : ℂ) * conj (u p))
        = ((a n * a p : ℝ) : ℂ) * (u n * conj (u p)) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  /- Step B: split off the diagonal. -/
  have hB : ∑ n ∈ S, ∑ p ∈ S, a n * a p * R n p
      = (∑ n ∈ S, a n * a n * R n n) + ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Finset.add_sum_erase S _ hn]
  have hdiag : ∑ n ∈ S, a n * a n * R n n
      = ∑ n ∈ S, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have h1 := hfr (hmemS hn).symm
    rw [hRdiag]; simp only [hadef]; field_simp
  /- Step C: the off-diagonal part. G(n,p) := c_m² c_n c_p R(n,p)/((λm−λn)(λn−λp)). -/
  set G : ι → ι → ℝ := fun n p =>
    c m ^ 2 * c n * c p * R n p / ((freq m - freq n) * (freq n - freq p)) with hGdef
  have hF : ∀ n ∈ S, ∀ p ∈ S.erase n, a n * a p * R n p = G n p + G p n := by
    intro n hn p hp
    have hpn : p ≠ n := (Finset.mem_erase.mp hp).1
    have hpS : p ∈ S := (Finset.mem_erase.mp hp).2
    have h1 := hfr (hmemS hn).symm   -- freq m - freq n ≠ 0
    have h2 := hfr (hmemS hpS).symm  -- freq m - freq p ≠ 0
    have h3 := hfr hpn.symm          -- freq n - freq p ≠ 0
    have h4 := hfr hpn               -- freq p - freq n ≠ 0
    simp only [hadef, hGdef]
    rw [hRsymm p n]
    field_simp
    ring
  have hOff : ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p
      = 2 * ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
    have hswap : ∑ n ∈ S, ∑ p ∈ S.erase n, G p n = ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
      refine Finset.sum_comm' ?_
      intro n p
      simp only [Finset.mem_erase]
      tauto
    calc ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p
        = ∑ n ∈ S, ∑ p ∈ S.erase n, (G n p + G p n) := by
          refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun p hp => hF n hn p hp
      _ = (∑ n ∈ S, ∑ p ∈ S.erase n, G n p) + ∑ n ∈ S, ∑ p ∈ S.erase n, G p n := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => Finset.sum_add_distrib
      _ = 2 * ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by rw [hswap]; ring
  /- Step C2–C4: the inner sum, via the conjugate eigen-relation at n. -/
  have hInner : ∀ n ∈ S, ∑ p ∈ S.erase n, G n p
      = c m ^ 3 * c n * R m n / (freq m - freq n) ^ 2 := by
    intro n hn
    have hnm : n ≠ m := hmemS hn
    have h1 : freq m - freq n ≠ 0 := hfr hnm.symm
    have h1' : freq n - freq m ≠ 0 := hfr hnm
    have hcn : (c n : ℂ) ≠ 0 := by exact_mod_cast (hc n).ne'
    -- W_n := Σ_{p ∈ S.erase n} (c_p/(λn−λp)) ū_p
    set W : ℂ := ∑ p ∈ S.erase n, ((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p) with hWdef
    -- (i) Σ_p G n p = (c_m² c_n/(λm−λn)) · Re(u_n W)
    have hi : ∑ p ∈ S.erase n, G n p = c m ^ 2 * c n / (freq m - freq n) * (u n * W).re := by
      rw [hWdef, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpn : p ≠ n := (Finset.mem_erase.mp hp).1
      have h3 : freq n - freq p ≠ 0 := hfr hpn.symm
      have : u n * (((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p))
          = ((c p / (freq n - freq p) : ℝ) : ℂ) * (u n * conj (u p)) := by ring
      rw [this, Complex.re_ofReal_mul]
      simp only [hGdef, hRdef]
      field_simp
    -- (ii) the conjugate eigen-relation at n, with the p = m term split off:
    --      c_n · (c_m/(λn−λm) ū_m + W) = −iμ ū_n
    have hii : (c n : ℂ) * ((((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m) + W)
        = -((μ : ℂ) * Complex.I * conj (u n)) := by
      have hconj := congrArg conj (heig n)
      rw [map_sum] at hconj
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hconj
      -- split p = m off the sum over univ.erase n
      have hmS : m ∈ Finset.univ.erase n := Finset.mem_erase.mpr ⟨hnm.symm, Finset.mem_univ _⟩
      have hsplit := Finset.add_sum_erase (Finset.univ.erase n)
        (fun p => ((c n * c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)) hmS
      have hSS : (Finset.univ.erase n).erase m = S.erase n := by
        rw [hSdef, Finset.erase_right_comm]
      rw [hSS] at hsplit
      rw [← hsplit] at hconj
      -- factor c n out
      have hfac : ∀ p, ((c n * c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)
          = (c n : ℂ) * (((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)) := by
        intro p; push_cast; ring
      simp only [hfac, ← Finset.mul_sum] at hconj
      rw [hWdef]
      linear_combination hconj
    -- (iii) solve for W and take Re(u_n W): the −iμ|u_n|²/c_n piece is purely imaginary
    have hiii : (u n * W).re = -(c m / (freq n - freq m)) * R n m := by
      have hW : W = -((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ)
          - (((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m) := by
        field_simp
        linear_combination hii
      have hkill : (u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))).re = 0 := by
        have hz : u n * conj (u n) = ((‖u n‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have e : u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))
            = -((μ : ℂ) / (c n : ℂ)) * (u n * conj (u n)) * Complex.I := by
          field_simp
        have : u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))
            = ((-(μ / c n) * ‖u n‖ ^ 2 : ℝ) : ℂ) * Complex.I := by
          rw [e, hz]; push_cast; ring
        rw [this, Complex.re_ofReal_mul]; simp
      rw [hW, mul_sub, Complex.sub_re, hkill, zero_sub]
      have : u n * ((((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m))
          = (((c m / (freq n - freq m)) : ℝ) : ℂ) * (u n * conj (u m)) := by ring
      rw [this, Complex.re_ofReal_mul]
      simp only [hRdef]; ring
    rw [hi, hiii, hRsymm n m]
    field_simp
    ring
  -- assemble
  rw [hA, hB, hdiag, hOff, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hInner n hn]

end MV
end Zeta23

end
