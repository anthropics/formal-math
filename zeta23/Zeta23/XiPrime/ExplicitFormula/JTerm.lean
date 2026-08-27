/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/JTerm.lean — evaluation of the correction functional J for a two-bump test function on
a line Re s = c.  [XF′ Thm 4.2 proof (b)–(e); Thm 9.2 (b)–(e).]  ONE generic theorem
JcorrG_estimate (abstract E′/E-on-the-line dE, abstract frozen-parameter map Lpar, line c; inputs: continuity and a
uniform bound for dE, its conjugation symmetry, the freezing estimate and the uniform bound for the frozen Dirichlet
object D_c(Λ; t) := B(c+it)/(Λ − A(c+it))), with two instances: ξ′ (c = 5/4, dE = dEE, Lpar = Lstar, complex) here —
Jcorr_estimate — and W (dE = dE2 c, Lpar = L2star, real) in Hardy/EFJTermW.lean — JcorrW_estimate.
   JcorrG c dE k = Σ'_N [cJ N · k(log N) + conj(cJ N) · k(−log N)]/√N + Err,
   ‖Err‖ ≤ K · ( (W + W′)/(T log T) · 1/(4+(a−b)²) + W/T² ).
The tsum is ∫ paperFT k · Pc_X(cJ) by PrimeTermJ.prime_term_complex.
-/
import Zeta23.XiPrime.ExplicitFormula.LitCorr
import Zeta23.XiPrime.ExplicitFormula.EntryError

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

open Zeta23.WeilEF (Hfn Hfn_mirror norm_Hfn_le continuous_Hfn_line)

/-! ## The generic layer -/

/-- the frozen Dirichlet object on the line c:  D_c(Λ; t) := B(c+it)/(Λ − A(c+it)). -/
def DfroG (c : ℝ) (Λs : ℂ) (t : ℝ) : ℂ := Bfn ((c:ℂ) + t * I) / (Λs - Afn ((c:ℂ) + t * I))

theorem conj_lineC (c t : ℝ) : conj ((c:ℂ) + t * I) = (c:ℂ) + (-t:ℝ) * I := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

theorem DfroG_conj_neg (c : ℝ) (Λs : ℂ) (t : ℝ) : DfroG c (conj Λs) t = conj (DfroG c Λs (-t)) := by
  unfold DfroG
  rw [map_div₀, map_sub, ← Bfn_conj, ← Afn_conj, conj_lineC]; simp

/-- continuity of t ↦ L(a, c+it) transported to D_c via an L-series identity. -/
theorem continuous_DfroG_of (c : ℝ) {Λs : ℂ} {a : ℕ → ℂ}
    (ha : Summable (fun N : ℕ => ‖a N‖ * (N : ℝ) ^ (-c)))
    (hLS : ∀ t : ℝ, LSeries a ((c:ℂ) + t * I) = DfroG c Λs t) : Continuous (DfroG c Λs) := by
  have h := continuous_LSeries_line a c ha
  have e : (fun t : ℝ => LSeries a ((c:ℂ) + t * I)) = DfroG c Λs := funext hLS
  rwa [e] at h

/-- the correction functional on the line c against an abstract dE:  (1/2π)∫ HwC c k t · dE t. -/
def JcorrG (c : ℝ) (dE : ℝ → ℂ) (k : ℝ → ℂ) : ℂ := (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, HwC c k t * dE t

/-- **The generic J-term estimate** on a line Re s = c for an abstract "E′/E on the line" dE and an abstract fixed
parameter map Lpar (ξ′: c = 5/4, dE = dEE, Lpar = Lstar; W: dE = dE2 c, Lpar = L2star).  All analytic input enters
through the five hypotheses; all constants are packaged in K, T₀. -/
theorem JcorrG_estimate {c : ℝ} {dE : ℝ → ℂ} {Lpar : ℝ → ℂ}
    (hdEc : Continuous dE) (hdEb : ∃ CE : ℝ, 0 ≤ CE ∧ ∀ t : ℝ, ‖dE t‖ ≤ CE)
    (hconj : ∀ t : ℝ, t ≠ 0 → conj (dE (-t)) = dE t)
    (hfreezeG : ∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ → T / 4 ≤ t →
      ‖dE t - DfroG c (Lpar τ) t‖ ≤ C * (|t - τ| + 1) / (T * Real.log T))
    (hunifG : ∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ →
      ‖DfroG c (Lpar τ) t‖ ≤ C / Real.log T) :
    ∃ K T₀ : ℝ, 0 ≤ K ∧ 8 ≤ T₀ ∧
    ∀ {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
      {T a b W W' : ℝ} (hT : T₀ ≤ T) (ha : T ≤ a) (hb : T ≤ b) (hW : 0 ≤ W) (hW' : 0 ≤ W')
      (hw1 : ∀ t : ℝ, ‖Hfn k ((c:ℂ) + t * I)‖ ≤ W * (cauchyK a t * cauchyK b t))
      (hw2 : ∀ t : ℝ, (|t - a| + |t - b|) * ‖Hfn k ((c:ℂ) + t * I)‖ ≤ W' * (cauchyK a t * cauchyK b t))
      (hw1' : ∀ t : ℝ, ‖Hfn k (1 - (c:ℂ) - t * I)‖ ≤ W * (cauchyK (-a) t * cauchyK (-b) t))
      (hw2' : ∀ t : ℝ, (|t + a| + |t + b|) * ‖Hfn k (1 - (c:ℂ) - t * I)‖ ≤ W' * (cauchyK (-a) t * cauchyK (-b) t))
      {cJ : ℕ → ℂ} (hcs : Summable (fun N : ℕ => ‖cJ N‖ * (N : ℝ) ^ (-c)))
      (hC1 : ∀ t : ℝ, LSeries cJ ((c:ℂ) + t * I) = DfroG c (Lpar ((a + b) / 2)) t)
      (hC1' : ∀ t : ℝ, LSeries (fun N => conj (cJ N)) ((c:ℂ) + t * I) = DfroG c (conj (Lpar ((a + b) / 2))) t),
      ‖JcorrG c dE k - ((∑' N : ℕ, cJ N / ((Real.sqrt N : ℝ) : ℂ) * k (Real.log N))
          + ∑' N : ℕ, conj (cJ N) / ((Real.sqrt N : ℝ) : ℂ) * k (-Real.log N))‖
        ≤ K * ((W + W') / (T * Real.log T) / (4 + (a - b) ^ 2) + W / T ^ 2) := by
  obtain ⟨Cf, Tf, hCf0, hTf8, hfreeze⟩ := hfreezeG
  obtain ⟨Cu, Tu, hCu0, hTu8, hfro⟩ := hunifG
  obtain ⟨CE, hCE0, hCE⟩ := hdEb
  -- constants
  refine ⟨(1 / Real.pi) * (8 * Real.pi * Cf + 16 * Real.pi / 9 * (CE + Cu)), max Tf Tu, by positivity,
    le_trans hTf8 (le_max_left _ _), ?_⟩
  intro k hk hkc T a b W W' hT ha hb hW hW' hw1 hw2 hw1' hw2' cJ hcs hC1 hC1'
  have hTf : Tf ≤ T := le_trans (le_max_left _ _) hT
  have hTu : Tu ≤ T := le_trans (le_max_right _ _) hT
  have hT8 : 8 ≤ T := le_trans hTf8 hTf
  have hT0 : 0 < T := by linarith
  have hlogT1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set τs : ℝ := (a + b) / 2 with hτs
  have hτs_ge : T ≤ τs := by rw [hτs]; linarith
  set Λs : ℂ := Lpar τs with hΛs
  -- the two error integrands
  set g₁ : ℝ → ℂ := fun t => dE t - DfroG c Λs t with hg₁
  set g₂ : ℝ → ℂ := fun t => dE t - DfroG c (conj Λs) t with hg₂
  have hcs' : Summable (fun N : ℕ => ‖conj (cJ N)‖ * (N : ℝ) ^ (-c)) := by
    simpa only [Complex.norm_conj] using hcs
  have hD₁c : Continuous (DfroG c Λs) := continuous_DfroG_of c hcs hC1
  have hD₂c : Continuous (DfroG c (conj Λs)) := continuous_DfroG_of c hcs' hC1'
  have hdEEc' : Continuous dE := hdEc
  have hg₁c : Continuous g₁ := hdEEc'.sub hD₁c
  have hg₂c : Continuous g₂ := hdEEc'.sub hD₂c
  -- uniform bounds: ‖gᵢ‖ ≤ CE + Cu
  have hCg : ∀ t, ‖g₁ t‖ ≤ CE + Cu ∧ ‖g₂ t‖ ≤ CE + Cu := by
    intro t
    have h1 := hCE t
    have h2 : ‖DfroG c Λs t‖ ≤ Cu := by
      have := hfro T hTu τs t hτs_ge
      exact this.trans (div_le_self hCu0 hlogT1)
    have h3 : ‖DfroG c (conj Λs) t‖ ≤ Cu := by
      rw [DfroG_conj_neg, Complex.norm_conj]
      have := hfro T hTu τs (-t) hτs_ge
      exact this.trans (div_le_self hCu0 hlogT1)
    exact ⟨(norm_sub_le _ _).trans (add_le_add h1 h2), (norm_sub_le _ _).trans (add_le_add h1 h3)⟩
  -- ε-bounds near the bumps
  set ε : ℝ := Cf / (T * Real.log T) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hgε₁ : ∀ t : ℝ, T / 4 ≤ t → ‖g₁ t‖ ≤ ε * (|t - (a + b) / 2| + 1) := by
    intro t ht
    have := hfreeze T hTf τs t hτs_ge ht
    show ‖dE t - DfroG c Λs t‖ ≤ Cf / (T * Real.log T) * (|t - (a + b) / 2| + 1)
    calc ‖dE t - DfroG c Λs t‖ ≤ Cf * (|t - τs| + 1) / (T * Real.log T) := this
      _ = Cf / (T * Real.log T) * (|t - (a + b) / 2| + 1) := by rw [hτs]; ring
  have hgε₂ : ∀ t : ℝ, t ≤ -(T / 4) → ‖g₂ t‖ ≤ ε * (|t + (a + b) / 2| + 1) := by
    intro t ht
    have := hfreeze T hTf τs (-t) hτs_ge (by linarith)
    show ‖dE t - DfroG c (conj Λs) t‖ ≤ Cf / (T * Real.log T) * (|t + (a + b) / 2| + 1)
    have htne : t ≠ 0 := by intro h0; rw [h0] at ht; linarith
    have e : dE t - DfroG c (conj Λs) t = conj (dE (-t) - DfroG c Λs (-t)) := by
      rw [map_sub, hconj t htne, ← DfroG_conj_neg]
    rw [e, Complex.norm_conj]
    calc ‖dE (-t) - DfroG c Λs (-t)‖ ≤ Cf * (|-t - τs| + 1) / (T * Real.log T) := this
      _ = Cf / (T * Real.log T) * (|t + (a + b) / 2| + 1) := by
          rw [hτs, show -t - (a + b) / 2 = -(t + (a + b) / 2) by ring, abs_neg]; ring
  -- the two core estimates
  obtain ⟨hint₁, hE₁⟩ := entry_core (w := fun t => Hfn k ((c:ℂ) + t * I)) (g := g₁) hT0 ha hb
    (continuous_Hfn_line hk hkc c) hg₁c hε0 (by positivity : (0:ℝ) ≤ CE + Cu) hW hW'
    hw1 hw2 (fun t => (hCg t).1) hgε₁
  have hw2c : Continuous (fun t : ℝ => Hfn k (1 - (c:ℂ) - t * I)) := by
    have : (fun t : ℝ => Hfn k (1 - (c:ℂ) - t * I))
        = (fun t : ℝ => Hfn k (((1 - c : ℝ) : ℂ) + t * I)) ∘ fun t : ℝ => -t := by
      funext t; simp only [Function.comp]; congr 1; push_cast; ring
    rw [this]; exact (continuous_Hfn_line hk hkc (1 - c)).comp continuous_neg
  obtain ⟨hint₂, hE₂⟩ := entry_core_mirror (w := fun t => Hfn k (1 - (c:ℂ) - t * I)) (g := g₂) hT0 ha hb
    hw2c hg₂c hε0 (by positivity : (0:ℝ) ≤ CE + Cu) hW hW' hw1' hw2' (fun t => (hCg t).2) hgε₂
  -- the two main terms via dirichlet_line
  obtain ⟨hintM₁, hM₁⟩ := dirichlet_line hk hkc c cJ hcs
  obtain ⟨hintM₂, hM₂⟩ := dirichlet_line_mirror hk hkc c (fun N => conj (cJ N)) hcs'
  -- assemble: JcorrG c dE k = M₁ + M₂ + (1/2π)(∫w₁g₁ + ∫w₂g₂)
  have hsplit1 : ∀ t : ℝ, Hfn k ((c:ℂ) + t * I) * dE t
      = Hfn k ((c:ℂ) + t * I) * LSeries cJ ((c:ℂ) + t * I)
        + Hfn k ((c:ℂ) + t * I) * g₁ t := by
    intro t; rw [hC1 t, hg₁]; ring
  have hsplit2 : ∀ t : ℝ, Hfn k (1 - (c:ℂ) - t * I) * dE t
      = Hfn k (1 - (c:ℂ) - t * I) * LSeries (fun N => conj (cJ N)) ((c:ℂ) + t * I)
        + Hfn k (1 - (c:ℂ) - t * I) * g₂ t := by
    intro t; rw [hC1' t, hg₂]; ring
  have hJ : JcorrG c dE k = ((∑' N : ℕ, cJ N / ((Real.sqrt N : ℝ) : ℂ) * k (Real.log N))
        + ∑' N : ℕ, conj (cJ N) / ((Real.sqrt N : ℝ) : ℂ) * k (-Real.log N))
      + (1 / (2 * Real.pi) : ℂ) * ((∫ t : ℝ, Hfn k ((c:ℂ) + t * I) * g₁ t)
        + ∫ t : ℝ, Hfn k (1 - (c:ℂ) - t * I) * g₂ t) := by
    unfold JcorrG
    have eHw : ∀ t : ℝ, HwC c k t * dE t
        = (Hfn k ((c:ℂ) + t * I) * LSeries cJ ((c:ℂ) + t * I)
            + Hfn k ((c:ℂ) + t * I) * g₁ t)
          + (Hfn k (1 - (c:ℂ) - t * I) * LSeries (fun N => conj (cJ N)) ((c:ℂ) + t * I)
            + Hfn k (1 - (c:ℂ) - t * I) * g₂ t) := by
      intro t; rw [HwC, add_mul, hsplit1, hsplit2]
    simp_rw [eHw]
    have hA : Integrable (fun t : ℝ => Hfn k ((c:ℂ) + t * I) * LSeries cJ ((c:ℂ) + t * I)
        + Hfn k ((c:ℂ) + t * I) * g₁ t) := hintM₁.add hint₁
    have hB : Integrable (fun t : ℝ => Hfn k (1 - (c:ℂ) - t * I)
        * LSeries (fun N => conj (cJ N)) ((c:ℂ) + t * I)
        + Hfn k (1 - (c:ℂ) - t * I) * g₂ t) := hintM₂.add hint₂
    rw [integral_add hA hB, integral_add hintM₁ hint₁, integral_add hintM₂ hint₂, ← hM₁, ← hM₂]
    ring
  rw [hJ]
  have e2 : ((∑' N : ℕ, cJ N / ((Real.sqrt N : ℝ) : ℂ) * k (Real.log N))
        + ∑' N : ℕ, conj (cJ N) / ((Real.sqrt N : ℝ) : ℂ) * k (-Real.log N))
      + (1 / (2 * Real.pi) : ℂ) * ((∫ t : ℝ, Hfn k ((c:ℂ) + t * I) * g₁ t)
        + ∫ t : ℝ, Hfn k (1 - (c:ℂ) - t * I) * g₂ t)
      - ((∑' N : ℕ, cJ N / ((Real.sqrt N : ℝ) : ℂ) * k (Real.log N))
        + ∑' N : ℕ, conj (cJ N) / ((Real.sqrt N : ℝ) : ℂ) * k (-Real.log N))
      = (1 / (2 * Real.pi) : ℂ) * ((∫ t : ℝ, Hfn k ((c:ℂ) + t * I) * g₁ t)
        + ∫ t : ℝ, Hfn k (1 - (c:ℂ) - t * I) * g₂ t) := by ring
  rw [e2, norm_mul]
  have hπ : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hπ]
  set B : ℝ := ε * (W + W' / 2) * (8 * Real.pi / (4 + (a - b) ^ 2))
    + (CE + Cu) * W * (16 * Real.pi / (9 * T ^ 2)) with hB
  have hsumE : ‖(∫ t : ℝ, Hfn k ((c:ℂ) + t * I) * g₁ t) + ∫ t : ℝ, Hfn k (1 - (c:ℂ) - t * I) * g₂ t‖
      ≤ B + B := (norm_add_le _ _).trans (add_le_add hE₁ hE₂)
  calc 1 / (2 * Real.pi) * ‖(∫ t : ℝ, Hfn k ((c:ℂ) + t * I) * g₁ t)
        + ∫ t : ℝ, Hfn k (1 - (c:ℂ) - t * I) * g₂ t‖
      ≤ 1 / (2 * Real.pi) * (B + B) := mul_le_mul_of_nonneg_left hsumE (by positivity)
    _ = (1 / Real.pi) * B := by ring
    _ ≤ (1 / Real.pi) * (8 * Real.pi * Cf + 16 * Real.pi / 9 * (CE + Cu))
          * ((W + W') / (T * Real.log T) / (4 + (a - b) ^ 2) + W / T ^ 2) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hB, hε]
        have hD : 0 < 4 + (a - b) ^ 2 := by positivity
        have hQ1 : 0 ≤ (W + W') / (T * Real.log T) / (4 + (a - b) ^ 2) := by positivity
        have hQ2 : 0 ≤ W / T ^ 2 := by positivity
        have h1 : Cf / (T * Real.log T) * (W + W' / 2) * (8 * Real.pi / (4 + (a - b) ^ 2))
            ≤ 8 * Real.pi * Cf * ((W + W') / (T * Real.log T) / (4 + (a - b) ^ 2)) := by
          have : W + W' / 2 ≤ W + W' := by linarith
          calc Cf / (T * Real.log T) * (W + W' / 2) * (8 * Real.pi / (4 + (a - b) ^ 2))
              ≤ Cf / (T * Real.log T) * (W + W') * (8 * Real.pi / (4 + (a - b) ^ 2)) := by
                gcongr
            _ = 8 * Real.pi * Cf * ((W + W') / (T * Real.log T) / (4 + (a - b) ^ 2)) := by
                field_simp
        have h2 : (CE + Cu) * W * (16 * Real.pi / (9 * T ^ 2))
            = 16 * Real.pi / 9 * (CE + Cu) * (W / T ^ 2) := by field_simp
        calc Cf / (T * Real.log T) * (W + W' / 2) * (8 * Real.pi / (4 + (a - b) ^ 2))
              + (CE + Cu) * W * (16 * Real.pi / (9 * T ^ 2))
            ≤ 8 * Real.pi * Cf * ((W + W') / (T * Real.log T) / (4 + (a - b) ^ 2))
              + 16 * Real.pi / 9 * (CE + Cu) * (W / T ^ 2) := by rw [h2]; exact add_le_add h1 le_rfl
          _ ≤ (8 * Real.pi * Cf + 16 * Real.pi / 9 * (CE + Cu))
              * ((W + W') / (T * Real.log T) / (4 + (a - b) ^ 2) + W / T ^ 2) := by
              nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 8 * Real.pi * Cf) hQ2,
                mul_nonneg (by positivity : (0:ℝ) ≤ 16 * Real.pi / 9 * (CE + Cu)) hQ1]

/-! ## The ξ′ instance: c = 5/4, dE = dEE, Λ⋆ = Lstar(τ⋆) -/

/-- the frozen Dirichlet object on the line 5/4, D(Λ⋆; t) := B(5/4+it)/(Λ⋆ − A(5/4+it)) (= DfroG (5/4)). -/
def Dfro (Λs : ℂ) (t : ℝ) : ℂ :=
  Bfn (((5/4:ℝ):ℂ) + t * I) / (Λs - Afn (((5/4:ℝ):ℂ) + t * I))

theorem Dfro_eq_DfroG : Dfro = DfroG (5/4) := rfl

theorem dEE_conj_neg (hF2 : XiDerivZerosInStrip) (t : ℝ) : dEE t = conj (dEE (-t)) := by
  unfold dEE
  rw [← derivE_div_E_conj (one_lt_re_54 (-t)) (xiDeriv_ne_zero_line hF2 (-t)), conj_s54]; simp

/-- **the ξ′ J-term estimate** at c = 5/4 — instance of JcorrG_estimate with Expansion's freeze_on_line /
frozen_uniform / derivE_div_E_uniform. -/
theorem Jcorr_estimate (hF2 : XiDerivZerosInStrip) :
    ∃ K T₀ : ℝ, 0 ≤ K ∧ 8 ≤ T₀ ∧
    ∀ {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
      {T a b W W' : ℝ} (hT : T₀ ≤ T) (ha : T ≤ a) (hb : T ≤ b) (hW : 0 ≤ W) (hW' : 0 ≤ W')
      (hw1 : ∀ t : ℝ, ‖Hfn k (((5/4:ℝ):ℂ) + t * I)‖ ≤ W * (cauchyK a t * cauchyK b t))
      (hw2 : ∀ t : ℝ, (|t - a| + |t - b|) * ‖Hfn k (((5/4:ℝ):ℂ) + t * I)‖ ≤ W' * (cauchyK a t * cauchyK b t))
      (hw1' : ∀ t : ℝ, ‖Hfn k (1 - (5/4:ℝ) - t * I)‖ ≤ W * (cauchyK (-a) t * cauchyK (-b) t))
      (hw2' : ∀ t : ℝ, (|t + a| + |t + b|) * ‖Hfn k (1 - (5/4:ℝ) - t * I)‖ ≤ W' * (cauchyK (-a) t * cauchyK (-b) t))
      {cJ : ℕ → ℂ} (hcs : Summable (fun N : ℕ => ‖cJ N‖ * (N : ℝ) ^ (-(5/4:ℝ))))
      (hC1 : ∀ t : ℝ, LSeries cJ (((5/4:ℝ):ℂ) + t * I) = Dfro (Lstar ((a + b) / 2)) t)
      (hC1' : ∀ t : ℝ, LSeries (fun N => conj (cJ N)) (((5/4:ℝ):ℂ) + t * I) = Dfro (conj (Lstar ((a + b) / 2))) t),
      ‖Jcorr k - ((∑' N : ℕ, cJ N / ((Real.sqrt N : ℝ) : ℂ) * k (Real.log N))
          + ∑' N : ℕ, conj (cJ N) / ((Real.sqrt N : ℝ) : ℂ) * k (-Real.log N))‖
        ≤ K * ((W + W') / (T * Real.log T) / (4 + (a - b) ^ 2) + W / T ^ 2) :=
  JcorrG_estimate (c := 5/4) (dE := dEE) (Lpar := Lstar)
    (continuous_derivE_div_E_line (xiDeriv_ne_zero_line hF2)) (derivE_div_E_uniform hF2)
    (fun t _ => (dEE_conj_neg hF2 t).symm) freeze_on_line frozen_uniform

end XiPrime
end Zeta23
