/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail.lean — Proposition [prop:tail] (the paper §4.2 "The tail"), assembled for the
concrete objects of Zeta23/Defs.lean.

Paper, verbatim: "Proposition [prop:tail]. Let A₀ ≥ 1 be an absolute constant such that
N(t+1)−N(t) ≤ A₀ log(t+3) for all t ≥ 0. Then for T ≥ T₀,
  ‖Ẽ‖ ≤ θ₀ := 4A₀ C₁² X^{1/2} log(4T)/D₀²,   C₁ := ‖φ″‖₁ = 2‖ϱ″‖₁/w,
so that θ₀ ≤ 32A₀‖ϱ″‖₁² l T^{λ/2−1} ≪ l T^{λ/2−1}. Moreover the trace norm satisfies
‖Ê‖₁ ≤ θ₀/(aL) ≤ 2θ₀/L."
Here E := G − A [eq:AE] is the contribution of the zeros with ordinate γ ∉ I' := (T−D₀, 2T+D₀],
D₀ := T^{1/2} [eq:D0] (including all zeros with γ ≤ 0), Ẽ := E/L,
Ê := E/(aL²) [eq:hatunits].

Structure of the proof (sub-files):
* Zeta23/Tail/RankOne.lean — ‖E‖, ‖E‖₁ ≤ ∑ m_ρ ‖u_ρ‖₂² for E = ∑ m_ρ u_ρ u_ρᵀ  [eq:Enormsum];
* Zeta23/Tail/Grid.lean    — ∑_{k<d} |γ−τ_k|⁻⁴ ≤ L·dist(γ,I)⁻³;
* Zeta23/Tail/Count.lean   — ∑_{γ∉I'} m_ρ dist(γ,I)⁻³ ≤ 4A₀ log(4T)/T, and N(I'∖I) ≪ D₀ l;
* this file              — [eq:hfbound] ⇒ ‖u_ρ k‖ ≤ e^{L/4}C₁|γ−τ_k|⁻², summability of the
  zero-side series entrywise, E = (the series over γ ∉ I'), and the two bounds in the exact
  shapes consumed downstream: ∀ i, |λᵢ(Ẽ)| ≤ θ₀ (for RHLinalg.weyl_posIndexAbove_le) and
  traceNorm Ê ≤ θ₀/(aL) (for [prop:zeroside-rank]).

Hypotheses taken (all proved elsewhere in the repository; none are Lean axioms):
* hloc  — PaperInputs.RvM.local (Hypotheses.lean), two-sided unit-window form;
* hdecay — [eq:hfbound] specialised to f = φ, in the exact shape of
  Zeta23.Params.norm_phiHat_sub_I_mul_le (Taper.lean), with C₁ := P.C1 T = ‖φ″‖₁;
* hEt/hEh — Hermitian-ness of Ẽ, Ê (from the ρ ↦ 1−ρ̄ symmetry).
-/
import Zeta23.Defs
import Zeta23.Assembly.Inputs
import Zeta23.Tail.Basic
import Zeta23.Tail.Grid
import Zeta23.Tail.Count
import Zeta23.Tail.RankOne
import Mathlib.Topology.Instances.Matrix
import Mathlib.Order.Filter.AtTopBot.Field

noncomputable section

open Matrix Finset Complex
open scoped ComplexOrder

namespace Zeta23
namespace Tail

open RHLinalg

/-! ### θ₀ and its size -/

/-- θ₀ := 4 A₀ C₁² X^{1/2} log(4T)/D₀²  [prop:tail], written with K := e^{L/4}·C₁ = X^{1/4}C₁
(so K² = C₁² X^{1/2}) and D₀² = T:  theta0 A₀ K T = 4·A₀·K²·log(4T)/T. -/
def theta0 (A₀ K T : ℝ) : ℝ := 4 * A₀ * K ^ 2 * Real.log (4 * T) / T

lemma theta0_nonneg {A₀ K T : ℝ} (hA₀ : 0 ≤ A₀) (hT : T₀ ≤ T) : 0 ≤ theta0 A₀ K T := by
  have hT' : (300:ℝ) ≤ T := hT
  have := one_le_log_four_mul hT
  unfold theta0; positivity

/-- log(4T) ≤ 2 l = 2 log(T/2π) for T ≥ T₀ (≥ 256 ≥ 16π²; uses only π ≤ 4). -/
lemma log_four_mul_le_two_mul_l {T : ℝ} (hT : T₀ ≤ T) : Real.log (4 * T) ≤ 2 * l T := by
  have hT' : (300:ℝ) ≤ T := hT
  have hπ : Real.pi ≤ 4 := Real.pi_le_four
  have hπ0 : 0 < Real.pi := Real.pi_pos
  unfold l
  have h2π : 0 < T / (2 * Real.pi) := by positivity
  have hsq : (2 * Real.pi) * (2 * Real.pi) ≤ 64 := by nlinarith
  have h : Real.log (4 * T) ≤ Real.log ((T / (2 * Real.pi)) * (T / (2 * Real.pi))) := by
    apply Real.log_le_log (by positivity)
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    nlinarith
  rw [Real.log_mul h2π.ne' h2π.ne'] at h
  linarith

/-- The "so that" clause of [prop:tail]: with K = e^{L/4} C₁, C₁ ≤ 2‖ϱ″‖₁ (as w ≥ 1),
e^{L/2} = X^{1/2} = (T/2π)^{λ/2} ≤ T^{λ/2}, log(4T) ≤ 2l, D₀² = T:
θ₀ ≤ 32 A₀ ‖ϱ″‖₁² l T^{λ/2−1}. Stated for the concrete L = λ·l of Defs; R stands for ‖ϱ″‖₁. -/
theorem theta0_le (P : Params) (hP : P.Valid) {T A₀ C₁ R : ℝ} (hT : T₀ ≤ T) (hA₀ : 0 ≤ A₀)
    (hC₁ : 0 ≤ C₁) (hC₁R : C₁ ≤ 2 * R) :
    theta0 A₀ (Real.exp (P.L T / 4) * C₁) T ≤ 32 * A₀ * R ^ 2 * l T * T ^ (P.lam / 2 - 1) := by
  have hT' : (300:ℝ) ≤ T := hT
  have hT0 : 0 < T := by linarith
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hlam := hP.lam_pos
  -- e^{L/2} = (T/2π)^{λ/2} ≤ T^{λ/2}
  have hexp : Real.exp (P.L T / 4) ^ 2 ≤ T ^ (P.lam / 2) := by
    rw [← Real.exp_nat_mul]; push_cast
    have : (2:ℝ) * (P.L T / 4) = (P.lam / 2) * Real.log (T / (2 * Real.pi)) := by
      unfold Params.L l; ring
    rw [this, ← Real.log_rpow (by positivity), Real.exp_log (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.two_le_pi]
  have hlog := log_four_mul_le_two_mul_l hT
  have hl0 : 0 ≤ l T := by
    have := one_le_log_four_mul hT; linarith
  have hK2 : (Real.exp (P.L T / 4) * C₁) ^ 2 ≤ T ^ (P.lam / 2) * (4 * R ^ 2) := by
    rw [mul_pow]
    apply mul_le_mul hexp _ (by positivity) (by positivity)
    nlinarith
  unfold theta0
  rw [div_le_iff₀ hT0]
  have hTpow : T ^ (P.lam / 2 - 1) * T = T ^ (P.lam / 2) := by
    rw [Real.rpow_sub hT0, Real.rpow_one, div_mul_cancel₀ _ hT0.ne']
  calc 4 * A₀ * (Real.exp (P.L T / 4) * C₁) ^ 2 * Real.log (4 * T)
      ≤ 4 * A₀ * (T ^ (P.lam / 2) * (4 * R ^ 2)) * (2 * l T) := by
        apply mul_le_mul _ hlog (by linarith [one_le_log_four_mul hT]) (by positivity)
        exact mul_le_mul_of_nonneg_left hK2 (by positivity)
    _ = 32 * A₀ * R ^ 2 * l T * T ^ (P.lam / 2 - 1) * T := by rw [mul_assoc _ _ T, hTpow]; ring

/-! ### The local count from PaperInputs.RvM.local -/

/-- From the two-sided local count on Z.N (PaperInputs.RvM.local) to the
finite-sub-family form LocalCount used by Zeta23/Tail/Count.lean, for the family of all
distinct zeros ρ ∈ Z.carrier with ordinate γ_ρ = Im ρ and multiplicity m_ρ = Z.mult ρ. -/
theorem LocalCount.ofWindowCount (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    LocalCount (fun ρ : Z.carrier => (ρ : ℂ).im) (fun ρ : Z.carrier => Z.mult ρ) A₀ where
  one_le := hA₀
  window t s hs := by
    classical
    refine le_trans ?_ (hloc t)
    have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨ρ, hρ, rfl⟩ := hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ.2, hs ρ hρ⟩
    have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
    rw [Finset.sum_map] at h
    exact_mod_cast h

/-! ### The vectors u_ρ and their decay from [eq:hfbound] -/

section Concrete

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

/-- u_ρ := (φ̂(γ_ρ − τ_k))_{0≤k<d} ∈ ℂ^d (proof of [prop:tail]; also prop:block's u_ρ). -/
def uvec (ρ : ℂ) : Fin (P.d T) → ℂ := fun k => P.phiHat T (gammaOf ρ - P.tau T k)

lemma Gsummand_eq (k l : Fin (P.d T)) (ρ : ℂ) :
    Z.Gsummand P T k l ρ = (Z.mult ρ : ℂ) * (uvec P T ρ k * uvec P T ρ l) := by
  unfold ZeroConfig.Gsummand uvec; ring

lemma gammaOf_sub_ofReal (ρ : ℂ) (x : ℝ) :
    gammaOf ρ - x = ((ρ.im - x : ℝ) : ℂ) - I * ((ρ.re - 1 / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [gammaOf]

variable {P T}

/-- τ_k = T + k·(2π/L) as a real number, for k : Fin d. -/
lemma tau_fin (k : Fin (P.d T)) : P.tau T k = T + (k : ℕ) * (2 * Real.pi / P.L T) := by
  unfold Params.tau Params.hgrid; push_cast; ring

/-- d·h ≤ T  (d = ⌊LT/2π⌋, h = 2π/L) [eq:fk]. -/
lemma d_mul_hgrid_le (hL : 0 < P.L T) (hT : 0 ≤ T) :
    (P.d T : ℝ) * (2 * Real.pi / P.L T) ≤ T := by
  have hπ := Real.pi_pos
  have hfl : (P.d T : ℝ) ≤ P.L T * T / (2 * Real.pi) := Nat.floor_le (by positivity)
  calc (P.d T : ℝ) * (2 * Real.pi / P.L T)
      ≤ (P.L T * T / (2 * Real.pi)) * (2 * Real.pi / P.L T) :=
        mul_le_mul_of_nonneg_right hfl (by positivity)
    _ = T := by field_simp

/-- "τ_0,…,τ_{d−1} ∈ [T, 2T)" [eq:fk]. -/
lemma tau_mem (hL : 0 < P.L T) (hT : 0 ≤ T) (k : Fin (P.d T)) :
    T ≤ P.tau T k ∧ P.tau T k < 2 * T := by
  rw [tau_fin]
  have hπ := Real.pi_pos
  have hh : 0 < 2 * Real.pi / P.L T := by positivity
  have hk : ((k : ℕ) : ℝ) + 1 ≤ P.d T := by exact_mod_cast k.2
  have hd := d_mul_hgrid_le hL hT
  constructor
  · have : 0 ≤ ((k : ℕ) : ℝ) * (2 * Real.pi / P.L T) := by positivity
    linarith
  · nlinarith

variable {Z}

/-- [eq:hfbound] ⇒ decay of the entries of u_ρ for a tail zero ρ:
"φ̂(γ_ρ−τ_k) = φ̂((γ−τ_k) − iy), |φ̂(r−iy)| ≤ e^{L/4}‖φ″‖₁|r−iy|⁻² ≤ X^{1/4}C₁ r⁻² for real
r ≠ 0" (y = β − 1/2, |y| < 1/2 as 0 < β < 1 — the only use of the strip). -/
lemma norm_uvec_le (hL : 0 < P.L T) (hT : 0 < T) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
        ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ / ‖(r : ℂ) - I * y‖ ^ 2)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (htail : InTail T ρ.im) (k : Fin (P.d T)) :
    ‖uvec P T ρ k‖
      ≤ (Real.exp (P.L T / 4) * C₁) * (|ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))| ^ 2)⁻¹ := by
  set r : ℝ := ρ.im - P.tau T k with hr
  set y : ℝ := ρ.re - 1 / 2 with hy
  have hstrip := Z.strip ρ hρ
  have hyab : |y| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
  have hτ := tau_mem hL hT.le k
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hr0 : r ≠ 0 := by
    rcases htail with h | h
    · have : r < 0 := by rw [hr]; linarith
      exact this.ne
    · have : 0 < r := by rw [hr]; linarith
      exact this.ne'
  have hz : (r : ℂ) - I * y ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hr0 this
  have hnormz : r ^ 2 ≤ ‖(r : ℂ) - I * y‖ ^ 2 := by
    have h1 : |((r : ℂ) - I * y).re| ≤ ‖(r : ℂ) - I * y‖ := Complex.abs_re_le_norm _
    have h2 : ((r : ℂ) - I * y).re = r := by simp
    rw [h2] at h1
    calc r ^ 2 = |r| ^ 2 := (sq_abs r).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg r) h1 2
  have hrsq : 0 < r ^ 2 := by positivity
  have heq : uvec P T ρ k = P.phiHat T (r - I * y) := by
    unfold uvec; rw [gammaOf_sub_ofReal]
  rw [heq, ← tau_fin, ← hr, sq_abs]
  calc ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ / ‖(r : ℂ) - I * y‖ ^ 2 :=
        hdecay r y hyab hz
    _ ≤ Real.exp (P.L T / 4) * C₁ / r ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hrsq hnormz
    _ = _ := by rw [div_eq_mul_inv]

/-- ‖u_ρ‖₂² ≤ K² · L · dist(γ,I)⁻³ for a tail zero (decay + the grid estimate). -/
lemma norm_sq_uvec_le (hT : T₀ ≤ T) (hL : 2 ≤ P.L T) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
        ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ / ‖(r : ℂ) - I * y‖ ^ 2)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (htail : InTail T ρ.im) :
    ∑ k, ‖uvec P T ρ k‖ ^ 2
      ≤ (Real.exp (P.L T / 4) * C₁) ^ 2 * P.L T * ((distI T ρ.im) ^ 3)⁻¹ := by
  have hT' : (300 : ℝ) ≤ T := hT
  have hL0 : 0 < P.L T := by linarith
  set K := Real.exp (P.L T / 4) * C₁ with hK
  have hK0 : 0 ≤ K := by positivity
  have hD : 1 ≤ distI T ρ.im := by
    have h1 := sqrt_le_distI_of_InTail (by linarith) htail
    have h2 : (17 : ℝ) ≤ Real.sqrt T := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    linarith
  calc ∑ k, ‖uvec P T ρ k‖ ^ 2
      ≤ ∑ k : Fin (P.d T),
          K ^ 2 * (|ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))| ^ 4)⁻¹ := by
        refine sum_le_sum fun k _ => ?_
        have h := norm_uvec_le hL0 (by linarith) hC₁ hdecay hρ htail k
        calc ‖uvec P T ρ k‖ ^ 2
            ≤ (K * (|ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))| ^ 2)⁻¹) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h 2
          _ = _ := by rw [mul_pow, inv_pow, ← pow_mul]
    _ = K ^ 2 * ∑ k ∈ range (P.d T),
          (|ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))| ^ 4)⁻¹ := by
        rw [mul_sum, Fin.sum_univ_eq_sum_range
          (fun k : ℕ => K ^ 2 * (|ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))| ^ 4)⁻¹)]
    _ ≤ K ^ 2 * (P.L T * ((distI T ρ.im) ^ 3)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (grid_sum_le hL (by linarith) (d_mul_hgrid_le hL0 (by linarith)) hD) (sq_nonneg _)
    _ = _ := by ring

end Concrete

/-! ### Summability of the zero-side series and E as the series over γ ∉ I' -/

section Series

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}

/-- Standing hypotheses of [prop:tail], bundled to keep signatures short. -/
structure TailHyp (Z : ZeroConfig) (P : Params) (T A₀ C₁ : ℝ) : Prop where
  hT : T₀ ≤ T
  hL : 2 ≤ P.L T
  hA₀ : 1 ≤ A₀
  /-- PaperInputs.RvM.local (two-sided unit-window local count). -/
  hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)
  hC₁ : 0 ≤ C₁
  /-- [eq:hfbound] for f = φ, shape of Zeta23.Params.norm_phiHat_sub_I_mul_le with C₁ := P.C1 T. -/
  hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
    ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ / ‖(r : ℂ) - I * y‖ ^ 2

/-- The set of zeros in the window I' (complement of the tail) is finite (as a subset of the
carrier subtype). -/
lemma finite_notTail (Z : ZeroConfig) (T : ℝ) :
    {ρ : Z.carrier | ¬ InTail T (ρ : ℂ).im}.Finite := by
  have hfin : (Z.ZIprime T).Finite := Z.finite_window _ _
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  intro ρ hρ
  simp only [Set.mem_setOf_eq, InTail, not_or, not_le, not_lt] at hρ
  exact ⟨ρ.2, hρ.1, hρ.2⟩

namespace TailHyp

variable (H : TailHyp Z P T A₀ C₁)
include H

lemma T_pos : 0 < T := by have h : (300:ℝ) ≤ T := H.hT; linarith
lemma L_pos : 0 < P.L T := by linarith [H.hL]
lemma A₀_nonneg : 0 ≤ A₀ := by linarith [H.hA₀]

/-- sA := the zeros of 𝒵(I') as a Finset of the carrier subtype. -/
def sA (_ : TailHyp Z P T A₀ C₁) : Finset Z.carrier := (finite_notTail Z T).toFinset

lemma not_mem_sA_iff (ρ : Z.carrier) : ρ ∉ H.sA ↔ InTail T (ρ : ℂ).im := by
  rw [sA, Set.Finite.mem_toFinset]; simp

/-- K := e^{L/4} C₁. -/
def K (_ : TailHyp Z P T A₀ C₁) : ℝ := Real.exp (P.L T / 4) * C₁

lemma K_nonneg : 0 ≤ H.K := by unfold K; have := H.hC₁; positivity

/-- Finite partial sums over tail zeros: ∑ m_ρ ‖u_ρ‖₂² ≤ L·θ₀
("(eq:Enormsum) gives ‖E‖ ≤ 4A₀C₁²X^{1/2} L log(4T) D₀⁻² = Lθ₀"). -/
lemma partial_sum_le (u : Finset {ρ : Z.carrier // ρ ∉ H.sA}) :
    ∑ x ∈ u, (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2
      ≤ P.L T * theta0 A₀ H.K T := by
  classical
  have hLC := LocalCount.ofWindowCount Z H.hA₀ H.hloc
  -- push u forward to a Finset of the carrier; all its elements are tail zeros
  set s : Finset Z.carrier := u.map (Function.Embedding.subtype _) with hs
  have hs_tail : ∀ ρ ∈ s, InTail T ((fun ρ : Z.carrier => (ρ : ℂ).im) ρ) := by
    intro ρ hρ
    rw [hs, Finset.mem_map] at hρ
    obtain ⟨x, _, rfl⟩ := hρ
    exact (H.not_mem_sA_iff _).mp x.2
  have hcount := tail_count_sum_le hLC H.hT s hs_tail
  have hterm : ∀ x ∈ u,
      (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2
        ≤ H.K ^ 2 * P.L T *
          ((Z.mult (x : Z.carrier) : ℝ) * ((distI T ((x : Z.carrier) : ℂ).im) ^ 3)⁻¹) := by
    intro x _
    have hx : InTail T ((x : Z.carrier) : ℂ).im := (H.not_mem_sA_iff _).mp x.2
    have h := norm_sq_uvec_le H.hT H.hL H.hC₁ H.hdecay (x : Z.carrier).2 hx
    have hm : (0:ℝ) ≤ Z.mult (x : Z.carrier) := Nat.cast_nonneg _
    calc _ ≤ (Z.mult (x : Z.carrier) : ℝ) * (H.K ^ 2 * P.L T * ((distI T ((x : Z.carrier) : ℂ).im) ^ 3)⁻¹) :=
          mul_le_mul_of_nonneg_left h hm
      _ = _ := by ring
  calc _ ≤ ∑ x ∈ u, H.K ^ 2 * P.L T *
          ((Z.mult (x : Z.carrier) : ℝ) * ((distI T ((x : Z.carrier) : ℂ).im) ^ 3)⁻¹) :=
        sum_le_sum hterm
    _ = H.K ^ 2 * P.L T *
          ∑ ρ ∈ s, (Z.mult ρ : ℝ) * ((distI T (ρ : ℂ).im) ^ 3)⁻¹ := by
        rw [← mul_sum, hs, Finset.sum_map]; rfl
    _ ≤ H.K ^ 2 * P.L T * (4 * A₀ * Real.log (4 * T) / T) :=
        mul_le_mul_of_nonneg_left hcount (by have := H.L_pos; positivity)
    _ = P.L T * theta0 A₀ H.K T := by unfold theta0; ring

/-- ∑_{γ∉I'} m_ρ ‖u_ρ‖₂² is summable … -/
lemma summable_tail :
    Summable (fun x : {ρ : Z.carrier // ρ ∉ H.sA} =>
      (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2) :=
  summable_of_sum_le (fun x => by positivity) H.partial_sum_le

/-- … with sum ≤ L·θ₀. -/
lemma tsum_tail_le :
    ∑' x : {ρ : Z.carrier // ρ ∉ H.sA},
      (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2
      ≤ P.L T * theta0 A₀ H.K T :=
  Real.tsum_le_of_sum_le (fun x => by positivity) H.partial_sum_le

/-- Each entry series ρ ↦ m_ρ φ̂(γ_ρ−τ_k)φ̂(γ_ρ−τ_l) is summable over ALL distinct zeros
(the absolute convergence of [eq:Gdef]'s first expression, here obtained from [eq:hfbound]
and the local count rather than assumed). -/
lemma summable_Gsummand (k l : Fin (P.d T)) :
    Summable (fun ρ : Z.carrier => Z.Gsummand P T k l ρ) := by
  apply (Finset.summable_compl_iff H.sA).mp
  refine Summable.of_norm_bounded H.summable_tail (fun x => ?_)
  rw [Gsummand_eq, norm_mul, norm_mul, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have h1 : ‖uvec P T (x : Z.carrier) k‖ ^ 2 ≤ ∑ j, ‖uvec P T (x : Z.carrier) j‖ ^ 2 :=
    single_le_sum (f := fun j => ‖uvec P T (x : Z.carrier) j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (mem_univ k)
  have h2 : ‖uvec P T (x : Z.carrier) l‖ ^ 2 ≤ ∑ j, ‖uvec P T (x : Z.carrier) j‖ ^ 2 :=
    single_le_sum (f := fun j => ‖uvec P T (x : Z.carrier) j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (mem_univ l)
  nlinarith [sq_nonneg (‖uvec P T (x : Z.carrier) k‖ - ‖uvec P T (x : Z.carrier) l‖),
    norm_nonneg (uvec P T (x : Z.carrier) k), norm_nonneg (uvec P T (x : Z.carrier) l)]

/-- A_{kl} [eq:AE] is the finite part of the series: ∑ over the zeros of 𝒵(I'). -/
lemma Az_eq_sum (k l : Fin (P.d T)) :
    Z.Az P T k l = ∑ x ∈ H.sA, Z.Gsummand P T k l (x : ℂ) := by
  classical
  have hfin : (Z.ZIprime T).Finite := Z.finite_window _ _
  show (∑ᶠ ρ ∈ Z.ZIprime T, Z.Gsummand P T k l ρ) = _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hmap : H.sA.map (Function.Embedding.subtype _) = hfin.toFinset := by
    ext y
    rw [Finset.mem_map, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : ¬ InTail T ((x : Z.carrier) : ℂ).im := by
        rw [sA, Set.Finite.mem_toFinset] at hx; exact hx
      simp only [InTail, not_or, not_le, not_lt] at hx'
      exact ⟨x.2, hx'.1, hx'.2⟩
    · rintro ⟨hy, h1, h2⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [sA, Set.Finite.mem_toFinset]
      simp only [Set.mem_setOf_eq, InTail, not_or, not_le, not_lt]
      exact ⟨h1, h2⟩
  rw [← hmap, Finset.sum_map]
  rfl

/-- **E = ∑_{γ∉I'} m_ρ u_ρ u_ρᵀ** [eq:AE]/proof of [prop:tail]: the matrix E := G − A is the
(convergent) sum of the rank-one pieces over the tail zeros. -/
theorem hasSum_Ez :
    HasSum (fun x : {ρ : Z.carrier // ρ ∉ H.sA} =>
      ((Z.mult (x : Z.carrier) : ℝ) : ℂ) • vecMulVec (uvec P T (x : Z.carrier)) (uvec P T (x : Z.carrier)))
      (Z.Ez P T) := by
  refine Pi.hasSum.mpr fun k => Pi.hasSum.mpr fun l => ?_
  have hG : HasSum (fun ρ : Z.carrier => Z.Gsummand P T k l ρ) (Z.Gz P T k l) :=
    (H.summable_Gsummand k l).hasSum
  have hE : HasSum (fun x : {ρ : Z.carrier // ρ ∉ H.sA} => Z.Gsummand P T k l (x : Z.carrier))
      (Z.Ez P T k l) := by
    apply (Finset.hasSum_compl_iff (f := fun ρ : Z.carrier => Z.Gsummand P T k l ρ) H.sA).mpr
    have : Z.Ez P T k l + ∑ x ∈ H.sA, Z.Gsummand P T k l (x : ℂ) = Z.Gz P T k l := by
      rw [← H.Az_eq_sum]; show (Z.Gz P T - Z.Az P T) k l + _ = _; simp
    rw [this]; exact hG
  simpa only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Complex.ofReal_natCast,
    Gsummand_eq] using hE

/-- The scaled version: κ•E = ∑ (κ m_ρ) u_ρ u_ρᵀ, and traceNorm (κ•E) ≤ κ·L·θ₀ for κ ≥ 0. -/
theorem traceNorm_smul_Ez_le {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : (((κ : ℝ) : ℂ) • Z.Ez P T).IsHermitian) :
    traceNorm hM ≤ κ * (P.L T * theta0 A₀ H.K T) := by
  have hsum := H.hasSum_Ez
  have hS := H.summable_tail.hasSum
  refine le_trans ?_ (mul_le_mul_of_nonneg_left H.tsum_tail_le hκ)
  apply traceNorm_le_of_hasSum_vecMulVec hM
    (fun x : {ρ : Z.carrier // ρ ∉ H.sA} => κ * (Z.mult (x : Z.carrier) : ℝ))
    (fun x => by positivity)
    (fun x : {ρ : Z.carrier // ρ ∉ H.sA} => uvec P T (x : Z.carrier))
  · have := hS.mul_left κ
    simpa only [mul_assoc] using this
  · have := hsum.const_smul ((κ : ℝ) : ℂ)
    simpa only [smul_smul, Complex.ofReal_mul] using this

end TailHyp

/-! ### Proposition [prop:tail] -/

/-- **Proposition [prop:tail]** for the concrete E := G − A of Zeta23/Defs.lean.
With θ₀ := 4A₀C₁²X^{1/2}log(4T)/D₀² (= theta0 A₀ (e^{L/4}C₁) T):
(T1) every eigenvalue of Ẽ = E/L has |λᵢ(Ẽ)| ≤ θ₀ ("‖Ẽ‖ ≤ θ₀", the hypothesis shape of
RHLinalg.weyl_posIndexAbove_le); also ‖Ẽ‖₁ ≤ θ₀;
(T2) ‖Ê‖₁ ≤ θ₀/(aL) for Ê = E/(aL²) ("Moreover the trace norm satisfies ‖Ê‖₁ ≤ θ₀/(aL)";
the further "≤ 2θ₀/L" is a ≥ 1/2, Zeta23.Params.half_le_a).
Hypotheses: T ≥ T₀ (:= 300, explicit), L ≥ 2, the local count (PaperInputs.RvM.local),
[eq:hfbound] for φ (Taper), a > 0, and Hermitian-ness of Ẽ, Ê. -/
theorem prop_tail {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ} (H : TailHyp Z P T A₀ C₁)
    (ha : 0 < P.a T)
    (hEt : (P.tilde T (Z.Ez P T)).IsHermitian) (hEh : (P.hat T (Z.Ez P T)).IsHermitian) :
    (∀ i, |hEt.eigenvalues i| ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T) ∧
    traceNorm hEt ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T ∧
    traceNorm hEh ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T) := by
  have hL := H.L_pos
  -- tilde: κ = L⁻¹
  have htilde : P.tilde T (Z.Ez P T) = (((P.L T)⁻¹ : ℝ) : ℂ) • Z.Ez P T := by
    unfold Params.tilde; rw [Complex.ofReal_inv]
  have hEt' : ((((P.L T)⁻¹ : ℝ) : ℂ) • Z.Ez P T).IsHermitian := htilde ▸ hEt
  have h1 : traceNorm hEt ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T := by
    have h := H.traceNorm_smul_Ez_le (κ := (P.L T)⁻¹) (by positivity) hEt'
    have e : (P.L T)⁻¹ * (P.L T * theta0 A₀ H.K T) = theta0 A₀ H.K T := by
      field_simp
    rw [e] at h
    convert h using 2
    rfl
  -- hat: κ = (a L²)⁻¹
  have hhat : P.hat T (Z.Ez P T) = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • Z.Ez P T := by
    unfold Params.hat; push_cast; rfl
  have hEh' : ((((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • Z.Ez P T).IsHermitian := hhat ▸ hEh
  have h2 : traceNorm hEh ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T) := by
    have h := H.traceNorm_smul_Ez_le (κ := (P.a T * P.L T ^ 2)⁻¹) (by positivity) hEh'
    have e : (P.a T * P.L T ^ 2)⁻¹ * (P.L T * theta0 A₀ H.K T)
        = theta0 A₀ H.K T / (P.a T * P.L T) := by
      field_simp
    rw [e] at h
    convert h using 2
    rfl
  exact ⟨fun i => (abs_eigenvalues_le_traceNorm hEt i).trans h1, h1, h2⟩

end Series

/-! ### E is Hermitian (real symmetric) — "since ρ and 1−ρ̄ have the same ordinate, both index
sets are invariant under ρ ↦ 1−ρ̄, so A and E are real symmetric" [eq:AE] -/

section Hermitian

lemma reflect_im (ρ : ℂ) : (reflect ρ).im = ρ.im := by simp [reflect]

lemma reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by simp [reflect]

lemma gammaOf_reflect (ρ : ℂ) : gammaOf (reflect ρ) = (starRingEnd ℂ) (gammaOf ρ) := by
  apply Complex.ext <;> simp [gammaOf, reflect]; ring

variable {P : Params} {T : ℝ}

/-- conj φ̂(z̄) = φ̂(z) ("since φ̂ is real on ℝ") transports u_ρ to u_{1−ρ̄}:
u_{1−ρ̄} = conj u_ρ. -/
lemma uvec_reflect
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z))
    (ρ : ℂ) (k : Fin (P.d T)) :
    uvec P T (reflect ρ) k = (starRingEnd ℂ) (uvec P T ρ k) := by
  unfold uvec
  rw [gammaOf_reflect, ← hconj, map_sub, Complex.conj_ofReal]

variable {Z : ZeroConfig} {A₀ C₁ : ℝ}

/-- E := G − A is Hermitian, from E = ∑_{γ∉I'} m_ρ u_ρ u_ρᵀ, m_{1−ρ̄} = m_ρ, u_{1−ρ̄} = ū_ρ. -/
theorem TailHyp.Ez_isHermitian (H : TailHyp Z P T A₀ C₁)
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    (Z.Ez P T).IsHermitian := by
  classical
  -- the involution x ↦ 1 − x̄ on the tail subtype
  have hrefl : ∀ x : {ρ : Z.carrier // ρ ∉ H.sA},
      (⟨reflect ((x : Z.carrier) : ℂ), Z.reflect_mem _ (x : Z.carrier).2⟩ : Z.carrier) ∉ H.sA := by
    intro x
    rw [H.not_mem_sA_iff]
    simp only [reflect_im]
    exact (H.not_mem_sA_iff _).mp x.2
  set σ : {ρ : Z.carrier // ρ ∉ H.sA} → {ρ : Z.carrier // ρ ∉ H.sA} :=
    fun x => ⟨⟨reflect ((x : Z.carrier) : ℂ), Z.reflect_mem _ (x : Z.carrier).2⟩, hrefl x⟩ with hσdef
  have hσ : Function.Involutive σ := fun x => by
    apply Subtype.ext; apply Subtype.ext
    simp only [hσdef, reflect_reflect]
  set f : {ρ : Z.carrier // ρ ∉ H.sA} → Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
    fun x => ((Z.mult (x : Z.carrier) : ℝ) : ℂ) •
      vecMulVec (uvec P T (x : Z.carrier)) (uvec P T (x : Z.carrier)) with hfdef
  have hf : HasSum f (Z.Ez P T) := H.hasSum_Ez
  have hfH : HasSum (fun x => (f x)ᴴ) (Z.Ez P T)ᴴ := hf.matrix_conjTranspose
  have hfσ : ∀ x, (f x)ᴴ = f (σ x) := by
    intro x
    ext k l
    have hm : Z.mult (reflect ((x : Z.carrier) : ℂ)) = Z.mult ((x : Z.carrier) : ℂ) :=
      Z.mult_reflect _ (x : Z.carrier).2
    simp only [hfdef, hσdef, conjTranspose_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal, uvec_reflect hconj, hm]
    ring
  have h2 : HasSum (f ∘ (hσ.toPerm σ)) (Z.Ez P T)ᴴ := by
    have : (f ∘ (hσ.toPerm σ)) = fun x => (f x)ᴴ := by
      funext x; simp [Function.comp, hfσ]
    rw [this]; exact hfH
  rw [Equiv.hasSum_iff] at h2
  exact h2.unique hf

/-- Real scalings of a Hermitian matrix are Hermitian (for Ẽ = E/L, Ê = E/(aL²)). -/
lemma isHermitian_real_smul {n : Type*} {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ) :
    ((c : ℂ) • M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_smul, hM.eq]
  simp [Complex.conj_ofReal]

lemma TailHyp.tilde_Ez_isHermitian (H : TailHyp Z P T A₀ C₁)
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    (P.tilde T (Z.Ez P T)).IsHermitian := by
  have h := isHermitian_real_smul (H.Ez_isHermitian hconj) (P.L T)⁻¹
  unfold Params.tilde; rw [← Complex.ofReal_inv]; exact h

lemma TailHyp.hat_Ez_isHermitian (H : TailHyp Z P T A₀ C₁)
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    (P.hat T (Z.Ez P T)).IsHermitian := by
  have h := isHermitian_real_smul (H.Ez_isHermitian hconj) (P.a T * P.L T ^ 2)⁻¹
  unfold Params.hat
  have e : ((P.a T * P.L T ^ 2)⁻¹ : ℂ) = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [e]; exact h

end Hermitian

/-! ### Exports in the shapes consumed by Zeta23/Assembly.lean (Assembly.TailInputs) -/

section Export

open Filter

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}

/-- [prop:tail] packaged as Assembly.TailInputs at height T, with
θ₀ = theta0 A₀ (e^{L/4} C₁) T and B := ‖Ê‖₁ = traceNorm Ê. -/
theorem TailHyp.tailInputs (H : TailHyp Z P T A₀ C₁) (ha : 0 < P.a T)
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    Assembly.TailInputs Z P T (theta0 A₀ (Real.exp (P.L T / 4) * C₁) T) := by
  have hEt := H.tilde_Ez_isHermitian hconj
  have hEh := H.hat_Ez_isHermitian hconj
  have hp := prop_tail H ha hEt hEh
  exact
    { theta_nonneg := theta0_nonneg H.A₀_nonneg H.hT
      tilde := ⟨hEt, hp.1⟩
      hat := ⟨traceNorm hEh, traceNorm_nonneg _, abs_rtrace_le_traceNorm _,
        frobSq_le_traceNorm_sq _, hp.2.2⟩ }

/-- N(I'∖I) = N(T−D₀,T) + N(2T,2T+D₀) ≤ 3A₀·√T·log(4T) ≤ 6A₀·D₀·l for T ≥ T₀
("N(I'∖I) ≪ D₀ l by N(t+1)−N(t) ≤ A₀log(t+3)", [prop:zeroside]). -/
theorem NII_le (Z : ZeroConfig) {A₀ T : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (hT : T₀ ≤ T) :
    (Assembly.NII Z T : ℝ) ≤ 3 * A₀ * Real.sqrt T * Real.log (4 * T) := by
  classical
  have hT' : (300:ℝ) ≤ T := hT
  have hLC := LocalCount.ofWindowCount Z hA₀ hloc
  have hfin1 : (Z.window (T - D0 T) T).Finite := Z.finite_window _ _
  have hfin2 : (Z.window (2 * T) (2 * T + D0 T)).Finite := Z.finite_window _ _
  set s1 : Finset Z.carrier := hfin1.toFinset.subtype (· ∈ Z.carrier) with hs1
  set s2 : Finset Z.carrier := hfin2.toFinset.subtype (· ∈ Z.carrier) with hs2
  have hN1 : (Z.N (T - D0 T) T : ℝ) = ∑ ρ ∈ s1, (Z.mult (ρ : ℂ) : ℝ) := by
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin1, hs1,
      Finset.sum_subtype_of_mem (f := fun ρ : ℂ => (Z.mult ρ : ℝ))]
    · push_cast; rfl
    · intro x hx; exact ((Set.Finite.mem_toFinset _).mp hx).1
  have hN2 : (Z.N (2 * T) (2 * T + D0 T) : ℝ) = ∑ ρ ∈ s2, (Z.mult (ρ : ℂ) : ℝ) := by
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin2, hs2,
      Finset.sum_subtype_of_mem (f := fun ρ : ℂ => (Z.mult ρ : ℝ))]
    · push_cast; rfl
    · intro x hx; exact ((Set.Finite.mem_toFinset _).mp hx).1
  have hmem1 : ∀ ρ ∈ s1, T - Real.sqrt T < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T := by
    intro ρ hρ
    rw [hs1, Finset.mem_subtype, Set.Finite.mem_toFinset] at hρ
    exact hρ.2
  have hmem2 : ∀ ρ ∈ s2, 2 * T < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T + Real.sqrt T := by
    intro ρ hρ
    rw [hs2, Finset.mem_subtype, Set.Finite.mem_toFinset] at hρ
    exact hρ.2
  have hdisj : Disjoint s1 s2 := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    have := (hmem1 ρ h1).2; have := (hmem2 ρ h2).1; linarith
  have hunion : ∀ ρ ∈ s1 ∪ s2, (T - Real.sqrt T < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T)
      ∨ (2 * T < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T + Real.sqrt T) := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h | h
    · exact Or.inl (hmem1 ρ h)
    · exact Or.inr (hmem2 ρ h)
  have h := boundary_count_le hLC hT (s1 ∪ s2) hunion
  rw [Finset.sum_union hdisj] at h
  unfold Assembly.NII
  push_cast
  rw [hN1, hN2]
  exact h

/-- L = λ log(T/2π) → ∞; in particular eventually L ≥ 2 (and ≥ 8w, etc.). -/
lemma tendsto_L_atTop (P : Params) (hP : P.Valid) : Tendsto (fun T => P.L T) atTop atTop := by
  unfold Params.L l
  apply Tendsto.const_mul_atTop hP.lam_pos
  exact Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))

/-- **[prop:tail], eventually-in-T form** for thmA_abstract: given the local
count (PaperInputs.RvM.local) and, eventually in T, [eq:hfbound] for φ with constant C₁(T)
(= ‖φ″‖₁, T-independent in value but a T-dependent Lean term), a > 0 and conj φ̂(z̄) = φ̂(z)
(all three from Taper.lean), TailInputs holds eventually with
θ₀(T) = theta0 A₀ (e^{L/4} C₁(T)) T = 4A₀C₁²X^{1/2}log(4T)/T. -/
theorem eventually_tailInputs (Z : ZeroConfig) (P : Params) (hP : P.Valid) {A₀ : ℝ}
    (hA₀ : 1 ≤ A₀) (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (C₁ : ℝ → ℝ) (hC₁ : ∀ T, 0 ≤ C₁ T)
    (hdecay : ∀ᶠ T in atTop, ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
      ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ T / ‖(r : ℂ) - I * y‖ ^ 2)
    (ha : ∀ᶠ T in atTop, 0 < P.a T)
    (hconj : ∀ᶠ T in atTop, ∀ z : ℂ,
      P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    ∀ᶠ T in atTop, Assembly.TailInputs Z P T (theta0 A₀ (Real.exp (P.L T / 4) * C₁ T) T) := by
  have hL2 : ∀ᶠ T in atTop, 2 ≤ P.L T := (tendsto_L_atTop P hP).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop T₀, hL2, hdecay, ha, hconj] with T hT hL hd ha' hc
  have H : TailHyp Z P T A₀ (C₁ T) :=
    { hT := hT, hL := hL, hA₀ := hA₀, hloc := hloc, hC₁ := hC₁ T, hdecay := hd }
  exact H.tailInputs ha' hc

/-- **The "so that" clause, eventually**: if C₁(T) ≤ 2R (R = ‖ϱ″‖₁; Taper's C1_le with w ≥ 1),
then θ₀(T) ≤ 32A₀R² · l(T) · T^{λ/2−1} for T ≥ T₀; hence ∃ C, eventually θ₀ ≤ C·l·T^{λ/2−1}. -/
theorem eventually_theta0_le (P : Params) (hP : P.Valid) {A₀ R : ℝ} (hA₀ : 1 ≤ A₀)
    (C₁ : ℝ → ℝ) (hC₁ : ∀ T, 0 ≤ C₁ T) (hC₁R : ∀ᶠ T in atTop, C₁ T ≤ 2 * R) :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      theta0 A₀ (Real.exp (P.L T / 4) * C₁ T) T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  refine ⟨32 * A₀ * R ^ 2, ?_⟩
  filter_upwards [eventually_ge_atTop T₀, hC₁R] with T hT hR
  exact theta0_le P hP hT (by linarith) (hC₁ T) hR

/-- **N(I'∖I) ≪ D₀ l, eventually**: ∃ C, eventually N(I'∖I) ≤ C·√T·l(T) (C = 6A₀). -/
theorem eventually_NII_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    ∃ C : ℝ, ∀ᶠ T in atTop, (Assembly.NII Z T : ℝ) ≤ C * Real.sqrt T * l T := by
  refine ⟨6 * A₀, ?_⟩
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have h1 := NII_le Z hA₀ hloc hT
  have h2 := log_four_mul_le_two_mul_l hT
  have : 0 ≤ 3 * A₀ * Real.sqrt T := by
    have := Real.sqrt_nonneg T; nlinarith
  nlinarith

end Export

end Tail
end Zeta23
