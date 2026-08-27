/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Transfer.lean — ξ′: **XiTraceTransfer** [XF′ Lemma 5.1 + Lemma 6.1].
The target is Zeta23.XiPrime.XiTraceTransfer (XiPrime/Statement.lean §4).

THE STATEMENT PROVED.  In hat units M ↦ M/(aL²), with
  Ĝ¹  := hat (Z.Gz (Pf T) T)                 — zero-side Gram matrix of the configuration Z,
  M   := (Pf T).Gp1 T                          — entry-dependent main term (coefficients C(N; L⋆^{kl})),
  Mᵀ  := (Pf T).GpC T (F.c T)                  — fixed-coefficient prime-side matrix (c^{(T)}_N),
for every δ > 0, eventually in T:
  |tr Ĝ¹ − tr M̂ᵀ| ≤ δ·N(T,2T)   and   ‖Ĝ¹‖_F² ≤ (1+δ)‖M̂ᵀ‖_F² + δ·N(T,2T).

ROUTE.  Write G = Mᵀ + D + E with E := G − M ("entry errors", [XF′ Lemma 5.1]) and D := M − Mᵀ
("entry dependence", [XF′ Lemma 6.1]).  Both are HatNegligible (|tr Â| ≤ ηN and ‖Â‖_F² ≤ η²N for
every η > 0 eventually), and Transfer/Abstract.lean §E turns that into the two displayed lines
(xiTraceTransfer_of_negligible — pure algebra, no analytic input).
  • E (§2): XiEF gives ‖E_{kl}‖ ≤ C T^{−δ}(1/max(1,Δ_{kl}²) + 1/T), Δ_{kl} = (k−l)h; the lattice sum
    Σ_l (1/max(1,Δ²))² ≤ 8(1 + 1/h) (Abstract §D) and d ≤ LT/2π, a ≥ a₀, N ≥ Tl/4π give
    |tr Ê| ≪ T^{1−δ}/L = o(N), ‖Ê‖_F² ≪ T^{1−2δ}/L² = o(N).
  • D (§3): M_{kl} − Mᵀ_{kl} = Q_{kl}(C(·; L_T+δ_{kl}) − c^{(T)}), Q_{kl}(e) := ∫ φ̂_k φ̂_l P_e (the P-part
    Gram entry, linear in e), δ_{kl} = ½ log(τ⋆_{kl}/T) ∈ [0, ½ log 2].  The re-expansion
    C(N; L_T+δ) − c_N = Σ_{r≥1} e_r(N) δ^r separates the (k,l)-dependence: D = Σ_r Δ^{(r)} ∘ Q(e_r);
    Minkowski over r (Abstract §B) with ‖Q(e_r)‖_F² ≤ A (ρ₀/l)^{2r} (aL²)² T l gives
    ‖D̂‖_F² ≪ T/l = o(N); for the trace, the diagonal formula Q_{kk}(e) = 2Σ_N A_φ(log N) N^{−1/2}
    Re(e_N N^{−iτ_k}), Abel summation in k (weights δ_k^r monotone) and the Dirichlet-kernel bound
    A_φ(y)|Σ_{k<K} e^{iτ_k y}| ≤ L²/(2 log 2) give |tr D| ≪ L²√X·l^{O(1)}, |tr D̂| = o(N).

INPUTS of the theorem xiTraceTransfer_of (§5), all named hypotheses:
  P.Valid, P.lam < 1, (Pf T).lam = P.lam ∧ (Pf T).w = P.w   (height-indexed window family over fixed (λ, w);
                                   λ < 1 is needed: PPUpper's r-independent end-effect term is o(N) iff λ < 1)
  LocalHypsCore cϱ ((Pf T).toSetting T) ((Pf T).localFun T) for T ≥ T₁   (taper facts of the window family)
  GammaFacts                       (μ-integrability, to split the prime-side entry)
  ∃ a₀ > 0, ∀ᶠ T, a₀ ≤ (Pf T).a T  (hat units divide by aL²)
  RiemannVonMangoldt Z             (only N(T,2T) ≥ Tl/4π eventually, Assembly.eventually_N_ge)
  XiEF Z Pf                        (Statement.lean §4; only the entrywise norm bound is used)
  0 ≤ ρ₀, Reexpansion F e ρ₀ A T₀  ([XF′ §6] e_r(N), the δ-expansion identity, H1–H3-type bounds)
  PPUpper cϱ P.lam                 (frobSq_Ppart_le, [prop:PP] upper bound, general coefficients)
-/
import Zeta23.XiPrime.Transfer.Inputs
import Zeta23.XiPrime.Transfer.Abstract
import Zeta23.XiPrime.Transfer.Dependence
import Zeta23.PrimeSideA.Bridge

noncomputable section

open Finset Filter Topology RHLinalg MeasureTheory Real
open scoped BigOperators

namespace Zeta23

namespace XiPrime

open PrimeSide

/-! ## §1. HatNegligible and the algebraic reduction -/

/-- a height-indexed matrix family A_T is negligible in hat units against N(T,2T):
for every η > 0, eventually |tr Â_T| ≤ η N and ‖Â_T‖_F² ≤ η² N. -/
def HatNegligible (Z : ZeroConfig) (Pf : ℝ → Params)
    (A : (T : ℝ) → Matrix (Fin ((Pf T).d T)) (Fin ((Pf T).d T)) ℂ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ T in atTop,
    |rtrace ((Pf T).hat T (A T))| ≤ η * (Z.N T (2 * T) : ℝ) ∧
    frobSq ((Pf T).hat T (A T)) ≤ η ^ 2 * (Z.N T (2 * T) : ℝ)

lemma hat_sub' (P : Params) (T : ℝ) {m : Type*} (M N : Matrix m m ℂ) :
    P.hat T (M - N) = P.hat T M - P.hat T N := by
  simp [Params.hat, smul_sub]

lemma hat_add' (P : Params) (T : ℝ) {m : Type*} (M N : Matrix m m ℂ) :
    P.hat T (M + N) = P.hat T M + P.hat T N := by
  simp [Params.hat, smul_add]

section FrobAdd
open scoped Matrix.Norms.Frobenius

/-- HatNegligible families form an additive class. -/
theorem HatNegligible.add {Z : ZeroConfig} {Pf : ℝ → Params}
    {A B : (T : ℝ) → Matrix (Fin ((Pf T).d T)) (Fin ((Pf T).d T)) ℂ}
    (hA : HatNegligible Z Pf A) (hB : HatNegligible Z Pf B) :
    HatNegligible Z Pf (fun T => A T + B T) := by
  intro η hη
  filter_upwards [hA (η / 2) (by positivity), hB (η / 2) (by positivity)] with T hAT hBT
  have hN : (0:ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  rw [hat_add']
  constructor
  · rw [rtrace_add]
    calc |rtrace ((Pf T).hat T (A T)) + rtrace ((Pf T).hat T (B T))|
        ≤ |rtrace ((Pf T).hat T (A T))| + |rtrace ((Pf T).hat T (B T))| := abs_add_le _ _
      _ ≤ η / 2 * (Z.N T (2 * T) : ℝ) + η / 2 * (Z.N T (2 * T) : ℝ) := add_le_add hAT.1 hBT.1
      _ = η * (Z.N T (2 * T) : ℝ) := by ring
  · have hsN := Real.sqrt_nonneg (Z.N T (2 * T) : ℝ)
    have ha : ‖(Pf T).hat T (A T)‖ ≤ η / 2 * Real.sqrt (Z.N T (2 * T) : ℝ) := by
      rw [Assembly.norm_eq_sqrt_frobSq]
      calc Real.sqrt (frobSq ((Pf T).hat T (A T))) ≤ Real.sqrt ((η / 2) ^ 2 * (Z.N T (2 * T) : ℝ)) :=
            Real.sqrt_le_sqrt hAT.2
        _ = η / 2 * Real.sqrt (Z.N T (2 * T) : ℝ) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have hb : ‖(Pf T).hat T (B T)‖ ≤ η / 2 * Real.sqrt (Z.N T (2 * T) : ℝ) := by
      rw [Assembly.norm_eq_sqrt_frobSq]
      calc Real.sqrt (frobSq ((Pf T).hat T (B T))) ≤ Real.sqrt ((η / 2) ^ 2 * (Z.N T (2 * T) : ℝ)) :=
            Real.sqrt_le_sqrt hBT.2
        _ = η / 2 * Real.sqrt (Z.N T (2 * T) : ℝ) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    rw [Assembly.frobSq_eq_norm_sq]
    calc ‖(Pf T).hat T (A T) + (Pf T).hat T (B T)‖ ^ 2
        ≤ (η / 2 * Real.sqrt (Z.N T (2 * T) : ℝ) + η / 2 * Real.sqrt (Z.N T (2 * T) : ℝ)) ^ 2 := by
          apply pow_le_pow_left₀ (norm_nonneg _)
          exact (norm_add_le _ _).trans (add_le_add ha hb)
      _ = η ^ 2 * (Z.N T (2 * T) : ℝ) := by
          rw [show η / 2 * Real.sqrt (Z.N T (2 * T) : ℝ) + η / 2 * Real.sqrt (Z.N T (2 * T) : ℝ)
              = η * Real.sqrt (Z.N T (2 * T) : ℝ) by ring, mul_pow, Real.sq_sqrt hN]

/-- a family congruent to a HatNegligible one is HatNegligible. -/
theorem HatNegligible.congr {Z : ZeroConfig} {Pf : ℝ → Params}
    {A B : (T : ℝ) → Matrix (Fin ((Pf T).d T)) (Fin ((Pf T).d T)) ℂ}
    (hA : HatNegligible Z Pf A) (h : ∀ T, A T = B T) : HatNegligible Z Pf B := by
  have : A = B := funext h
  subst this; exact hA

end FrobAdd

/-- **the algebra, one piece**: if G − Mᵀ is HatNegligible then XiTraceTransfer holds. -/
theorem xiTraceTransfer_of_negligible₁ (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily)
    (h : HatNegligible Z Pf (fun T => Z.Gz (Pf T) T - (Pf T).GpC T (F.c T))) :
    XiTraceTransfer Z Pf F := by
  -- write G − Mᵀ = (G − Mᵀ) + 0 and reuse the two-piece bookkeeping with E := G − Mᵀ, D := 0
  constructor
  · intro δ hδ
    filter_upwards [h δ hδ] with T hT
    set P := Pf T
    have : rtrace (P.hat T (Z.Gz P T)) - rtrace (P.hat T (P.GpC T (F.c T)))
        = rtrace (P.hat T (Z.Gz P T - P.GpC T (F.c T))) := by
      rw [hat_sub', rtrace_sub]
    rw [this]; exact hT.1
  · intro δ hδ
    set η : ℝ := min (δ / 2) (1 / 2) with hη
    have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
    have hηδ : η ≤ δ / 2 := min_le_left _ _
    have hη1 : η ≤ 1 / 2 := min_le_right _ _
    filter_upwards [h η hη0] with T hT
    set P := Pf T
    have hdec : P.hat T (Z.Gz P T) = P.hat T (P.GpC T (F.c T))
        + P.hat T (Z.Gz P T - P.GpC T (F.c T)) + 0 := by
      rw [hat_sub']; abel
    have hN : (0:ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
    have h0 : frobSq (0 : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ) ≤ 0 ^ 2 * (Z.N T (2 * T) : ℝ) := by
      simp [Assembly.frobSq_eq_sum_norm_sq]
    have h := Transfer.frobSq_le_of_decomp hdec hN hη0.le le_rfl hT.2 h0
    have hm : 0 ≤ frobSq (P.hat T (P.GpC T (F.c T))) := Assembly.frobSq_nonneg _
    have h1 : 1 + (η + 0) ≤ 1 + δ := by linarith
    have h2 : (η + 0) + (η + 0) ^ 2 ≤ δ := by nlinarith
    calc frobSq (P.hat T (Z.Gz P T))
        ≤ (1 + (η + 0)) * frobSq (P.hat T (P.GpC T (F.c T))) + ((η + 0) + (η + 0) ^ 2) * (Z.N T (2 * T) : ℝ) := h
      _ ≤ (1 + δ) * frobSq (P.hat T (P.GpC T (F.c T))) + δ * (Z.N T (2 * T) : ℝ) := by gcongr

/-- **[XF′ Lemma 5.1 + 6.1 ⇒ XiTraceTransfer], the algebra**: if both E = G − M and D = M − Mᵀ are
HatNegligible then XiTraceTransfer holds. -/
theorem xiTraceTransfer_of_negligible (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily)
    (hE : HatNegligible Z Pf (fun T => Z.Gz (Pf T) T - (Pf T).Gp1 T))
    (hD : HatNegligible Z Pf (fun T => (Pf T).Gp1 T - (Pf T).GpC T (F.c T))) :
    XiTraceTransfer Z Pf F := by
  constructor
  · intro δ hδ
    filter_upwards [hE (δ / 2) (by positivity), hD (δ / 2) (by positivity)] with T hET hDT
    set P := Pf T
    have hdec : P.hat T (Z.Gz P T) = P.hat T (P.GpC T (F.c T))
        + P.hat T (P.Gp1 T - P.GpC T (F.c T)) + P.hat T (Z.Gz P T - P.Gp1 T) := by
      rw [hat_sub', hat_sub']; abel
    have := Transfer.rtrace_sub_of_decomp hdec
    rw [this]
    calc |rtrace (P.hat T (P.Gp1 T - P.GpC T (F.c T))) + rtrace (P.hat T (Z.Gz P T - P.Gp1 T))|
        ≤ |rtrace (P.hat T (P.Gp1 T - P.GpC T (F.c T)))| + |rtrace (P.hat T (Z.Gz P T - P.Gp1 T))| :=
          abs_add_le _ _
      _ ≤ δ / 2 * (Z.N T (2 * T) : ℝ) + δ / 2 * (Z.N T (2 * T) : ℝ) := add_le_add hDT.1 hET.1
      _ = δ * (Z.N T (2 * T) : ℝ) := by ring
  · intro δ hδ
    set η : ℝ := min (δ / 4) (1 / 4) with hη
    have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
    have hηδ : η ≤ δ / 4 := min_le_left _ _
    have hη1 : η ≤ 1 / 4 := min_le_right _ _
    filter_upwards [hE η hη0, hD η hη0] with T hET hDT
    set P := Pf T
    have hdec : P.hat T (Z.Gz P T) = P.hat T (P.GpC T (F.c T))
        + P.hat T (P.Gp1 T - P.GpC T (F.c T)) + P.hat T (Z.Gz P T - P.Gp1 T) := by
      rw [hat_sub', hat_sub']; abel
    have hN : (0:ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
    have h := Transfer.frobSq_le_of_decomp hdec hN hη0.le hη0.le hDT.2 hET.2
    have hm : 0 ≤ frobSq (P.hat T (P.GpC T (F.c T))) := Assembly.frobSq_nonneg _
    have h1 : 1 + (η + η) ≤ 1 + δ := by linarith
    have h2 : (η + η) + (η + η) ^ 2 ≤ δ := by nlinarith
    calc frobSq (P.hat T (Z.Gz P T))
        ≤ (1 + (η + η)) * frobSq (P.hat T (P.GpC T (F.c T))) + ((η + η) + (η + η) ^ 2) * (Z.N T (2 * T) : ℝ) := h
      _ ≤ (1 + δ) * frobSq (P.hat T (P.GpC T (F.c T))) + δ * (Z.N T (2 * T) : ℝ) := by
          gcongr

/-! ## §2. [XF′ Lemma 5.1]: the entry errors E = G¹ − M are HatNegligible -/

section FamilyFacts
variable {Pf : ℝ → Params} {P : Params}

/-- scalars of the family that depend only on (λ, T) agree with those of P. -/
lemma fam_L (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w) (T : ℝ) : (Pf T).L T = P.L T := by
  simp [Params.L, (hPf T).1]
lemma fam_d (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w) (T : ℝ) : (Pf T).d T = P.d T := by
  simp [Params.d, fam_L hPf]
lemma fam_hgrid (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w) (T : ℝ) :
    (Pf T).hgrid T = P.hgrid T := by
  simp [Params.hgrid, fam_L hPf]
lemma fam_tau (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w) (T : ℝ) (k : ℤ) :
    (Pf T).tau T k = P.tau T k := by
  simp [Params.tau, fam_hgrid hPf]
lemma fam_X (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w) (T : ℝ) : (Pf T).X T = P.X T := by
  simp [Params.X, fam_L hPf]

end FamilyFacts

lemma tau_sub_tau (P : Params) (T : ℝ) (k l : ℤ) :
    P.tau T k - P.tau T l = ((k:ℝ) - l) * P.hgrid T := by
  simp [Params.tau]; ring

lemma d_le (P : Params) (T : ℝ) (hLT : 0 ≤ P.L T * T) : (P.d T : ℝ) ≤ P.L T * T / (2 * π) := by
  unfold Params.d
  exact Nat.floor_le (by positivity)

/-- **[XF′ Lemma 5.1] at fixed T** (explicit): from the entrywise bound of XiEF,
|tr E| ≤ d·C T^{−δ}(1 + 1/T)  and  ‖E‖_F² ≤ 2(C T^{−δ})²(8d(1 + 1/h) + d²/T²). -/
theorem entryError_bounds (Z : ZeroConfig) (P : Params) (T : ℝ) (M : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ)
    {C δ : ℝ} (hC : 0 ≤ C) (hT : 0 < T) (hh : 0 < P.hgrid T)
    (hEF : ∀ k l : Fin (P.d T), ‖Z.Gz P T k l - M k l‖
      ≤ C * T ^ (-δ) * (1 / max 1 ((P.tau T k - P.tau T l) ^ 2) + 1 / T)) :
    |rtrace (Z.Gz P T - M)| ≤ (P.d T : ℝ) * (C * T ^ (-δ) * (1 + 1 / T)) ∧
    frobSq (Z.Gz P T - M)
      ≤ 2 * (C * T ^ (-δ)) ^ 2 * ((P.d T : ℝ) * (8 * (1 + 1 / P.hgrid T)) + (P.d T : ℝ) ^ 2 / T ^ 2) := by
  have hCT : 0 ≤ C * T ^ (-δ) := mul_nonneg hC (Real.rpow_nonneg hT.le _)
  have hentry : ∀ k l : Fin (P.d T), ‖(Z.Gz P T - M) k l‖
      ≤ C * T ^ (-δ) * (1 / max 1 (((((k:ℕ):ℝ) - ((l:ℕ):ℝ)) * P.hgrid T) ^ 2) + 1 / T) := by
    intro k l
    have := hEF k l
    rw [tau_sub_tau] at this
    simpa [Matrix.sub_apply] using this
  constructor
  · refine (Transfer.abs_rtrace_le_sum_norm_diag _).trans ?_
    calc ∑ k : Fin (P.d T), ‖(Z.Gz P T - M) k k‖
        ≤ ∑ _k : Fin (P.d T), C * T ^ (-δ) * (1 + 1 / T) := by
          refine Finset.sum_le_sum fun k _ => (hentry k k).trans ?_
          simp
      _ = (P.d T : ℝ) * (C * T ^ (-δ) * (1 + 1 / T)) := by simp
  · set t : ℕ → ℕ → ℝ := fun k l => 1 / max 1 ((((k:ℝ) - (l:ℝ)) * P.hgrid T) ^ 2) with ht
    have ht0 : ∀ k l, 0 ≤ t k l := fun k l => by simp only [ht]; positivity
    have ht1 : ∀ k l, t k l ≤ 1 := fun k l => by
      simp only [ht]; exact div_le_one_of_le₀ (le_max_left _ _) (by positivity)
    refine (Transfer.frobSq_le_of_norm_le _ (fun k l : Fin (P.d T) => C * T ^ (-δ) * (t k l + 1 / T))
      (fun k l => by simpa [ht] using hentry k l)).trans ?_
    -- (CT^{-δ})²(t + 1/T)² ≤ 2(CT^{-δ})²(t² + 1/T²)
    have hsq : ∀ k l : Fin (P.d T), (C * T ^ (-δ) * (t k l + 1 / T)) ^ 2
        ≤ 2 * (C * T ^ (-δ)) ^ 2 * (t k l ^ 2) + 2 * (C * T ^ (-δ)) ^ 2 / T ^ 2 := by
      intro k l
      have : (t k l + 1 / T) ^ 2 ≤ 2 * (t k l ^ 2 + (1 / T) ^ 2) := by
        nlinarith [sq_nonneg (t k l - 1 / T)]
      calc (C * T ^ (-δ) * (t k l + 1 / T)) ^ 2 = (C * T ^ (-δ)) ^ 2 * (t k l + 1 / T) ^ 2 := by ring
        _ ≤ (C * T ^ (-δ)) ^ 2 * (2 * (t k l ^ 2 + (1 / T) ^ 2)) := by gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hsq k l).trans ?_
    have hlat : ∀ k : Fin (P.d T), ∑ l : Fin (P.d T), t k l ^ 2 ≤ 8 * (1 + 1 / P.hgrid T) := by
      intro k
      rw [Fin.sum_univ_eq_sum_range (fun l => t k l ^ 2) (P.d T)]
      simpa only [ht] using Transfer.lattice_sum_le hh (P.d T) k k.isLt
    calc ∑ k : Fin (P.d T), ∑ l : Fin (P.d T),
          (2 * (C * T ^ (-δ)) ^ 2 * t k l ^ 2 + 2 * (C * T ^ (-δ)) ^ 2 / T ^ 2)
        = 2 * (C * T ^ (-δ)) ^ 2 * ∑ k : Fin (P.d T), ∑ l : Fin (P.d T), t k l ^ 2
          + (P.d T : ℝ) ^ 2 * (2 * (C * T ^ (-δ)) ^ 2 / T ^ 2) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Finset.mul_sum]
          ring
      _ ≤ 2 * (C * T ^ (-δ)) ^ 2 * ∑ _k : Fin (P.d T), 8 * (1 + 1 / P.hgrid T)
          + (P.d T : ℝ) ^ 2 * (2 * (C * T ^ (-δ)) ^ 2 / T ^ 2) := by
          gcongr with k _
          · exact hlat k
      _ = 2 * (C * T ^ (-δ)) ^ 2 * ((P.d T : ℝ) * (8 * (1 + 1 / P.hgrid T)) + (P.d T : ℝ) ^ 2 / T ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

/-- rtrace / frobSq in hat units. -/
lemma rtrace_hat' (P : Params) (T : ℝ) {m : Type*} [Fintype m] (M : Matrix m m ℂ) :
    rtrace (P.hat T M) = (P.a T * P.L T ^ 2)⁻¹ * rtrace M := by
  rw [Assembly.hat_eq, Assembly.rtrace_smul_ofReal]

lemma frobSq_hat' (P : Params) (T : ℝ) {m : Type*} [Fintype m] (M : Matrix m m ℂ) :
    frobSq (P.hat T M) = ((P.a T * P.L T ^ 2)⁻¹) ^ 2 * frobSq M := by
  rw [Assembly.hat_eq, Assembly.frobSq_smul_ofReal]

set_option maxHeartbeats 400000 in
/-- **[XF′ Lemma 5.1], for any entrywise main term** M_T with the XiEF/WEF error shape:
‖G_{kl} − M_{kl}‖ ≤ C T^{−δ}(1/max(1,Δ²_{kl}) + 1/T) for T ≥ T₀  ⇒  G − M is HatNegligible. -/
theorem hatNegligible_of_entryBound (Z : ZeroConfig) (Pf : ℝ → Params) (P : Params) (hP : P.Valid)
    (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w)
    (ha : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ᶠ T in atTop, a₀ ≤ (Pf T).a T)
    (hR : RiemannVonMangoldt Z)
    (M : (T : ℝ) → Matrix (Fin ((Pf T).d T)) (Fin ((Pf T).d T)) ℂ)
    (hEF : ∃ C δ T₀ : ℝ, 0 < δ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ k l : Fin ((Pf T).d T),
      ‖Z.Gz (Pf T) T k l - M T k l‖
        ≤ C * T ^ (-δ) * (1 / max 1 (((Pf T).tau T k - (Pf T).tau T l) ^ 2) + 1 / T)) :
    HatNegligible Z Pf (fun T => Z.Gz (Pf T) T - M T) := by
  obtain ⟨C₀, δ, T₀, hδ, hEF⟩ := hEF
  obtain ⟨a₀, ha₀, ha⟩ := ha
  set C := max C₀ 1 with hCdef
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  intro η hη
  have hπ2 : 9 < π ^ 2 := by have := Real.pi_gt_three; nlinarith
  have h13 : 4 * π ≤ 13 := by have := Real.pi_lt_d2; norm_num at this ⊢; linarith
  have c1 : 4 / π ^ 2 ≤ (1:ℝ) / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]; linarith only [hπ2]
  have c2 : 1 / (4 * π ^ 2) ≤ (1:ℝ) / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]; linarith only [hπ2]
  -- smallness: T^{-δ} ≤ ε
  set ε : ℝ := min 1 (min (η * a₀ / (4 * C)) (η ^ 2 * a₀ ^ 2 / (26 * C ^ 2))) with hεdef
  have hε0 : 0 < ε := by positivity
  have hsmall : ∀ᶠ T : ℝ in atTop, T ^ (-δ) ≤ ε :=
    ((tendsto_rpow_neg_atTop hδ).eventually (eventually_le_nhds hε0))
  have hLtop := Assembly.tendsto_L_atTop P hP.lam_pos
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (1:ℝ), ha, Assembly.eventually_N_ge Z hR,
    Assembly.eventually_one_le_l, hLtop.eventually_ge_atTop (2 * π), hsmall]
    with T hT₀ hT1 haT hN hl hL hTδ
  have hT : 0 < T := by linarith
  have hπ := Real.pi_pos
  have hLf : (Pf T).L T = P.L T := fam_L hPf T
  have hL0 : 0 < P.L T := by nlinarith [Real.pi_gt_three]
  have hh : (Pf T).hgrid T = 2 * π / P.L T := by simp [Params.hgrid, hLf]
  have hhpos : 0 < (Pf T).hgrid T := by rw [hh]; positivity
  have hinvh : 1 / (Pf T).hgrid T = P.L T / (2 * π) := by rw [hh]; field_simp
  have hdle : ((Pf T).d T : ℝ) ≤ P.L T * T / (2 * π) := by
    have := d_le (Pf T) T (by rw [hLf]; positivity); rwa [hLf] at this
  have hd0 : (0:ℝ) ≤ ((Pf T).d T : ℝ) := Nat.cast_nonneg _
  have hTδ0 : 0 ≤ T ^ (-δ) := Real.rpow_nonneg hT.le _
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ η * a₀ / (4 * C) := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ η ^ 2 * a₀ ^ 2 / (26 * C ^ 2) := (min_le_right _ _).trans (min_le_right _ _)
  -- the entrywise bound with C in place of C₀
  have hEF' : ∀ k l : Fin ((Pf T).d T), ‖Z.Gz (Pf T) T k l - M T k l‖
      ≤ C * T ^ (-δ) * (1 / max 1 (((Pf T).tau T k - (Pf T).tau T l) ^ 2) + 1 / T) := by
    intro k l
    refine (hEF T hT₀ k l).trans ?_
    have h0 : 0 ≤ T ^ (-δ) * (1 / max 1 (((Pf T).tau T k - (Pf T).tau T l) ^ 2) + 1 / T) := by
      positivity
    have := mul_le_mul_of_nonneg_right (le_max_left C₀ 1) h0
    simpa only [mul_assoc] using this
  obtain ⟨htr, hfr⟩ := entryError_bounds Z (Pf T) T (M T) hC.le hT hhpos hEF'
  have haT0 : 0 < (Pf T).a T := ha₀.trans_le haT
  have haL : 0 < (Pf T).a T * (Pf T).L T ^ 2 := by rw [hLf]; positivity
  have ha₀L : 0 < a₀ * P.L T ^ 2 := by positivity
  have hinv : ((Pf T).a T * (Pf T).L T ^ 2)⁻¹ ≤ (a₀ * P.L T ^ 2)⁻¹ := by
    rw [hLf]; exact inv_anti₀ ha₀L (by gcongr)
  constructor
  · rw [rtrace_hat', abs_mul, abs_of_pos (inv_pos.2 haL)]
    have hT1' : 1 + 1 / T ≤ 2 := by
      have : 1 / T ≤ 1 := by rw [div_le_one hT]; exact hT1
      linarith
    calc ((Pf T).a T * (Pf T).L T ^ 2)⁻¹ * |rtrace (Z.Gz (Pf T) T - M T)|
        ≤ (a₀ * P.L T ^ 2)⁻¹ * (((Pf T).d T : ℝ) * (C * T ^ (-δ) * (1 + 1 / T))) :=
          mul_le_mul hinv htr (abs_nonneg _) (inv_nonneg.2 ha₀L.le)
      _ ≤ (a₀ * P.L T ^ 2)⁻¹ * ((P.L T * T / (2 * π)) * (C * T ^ (-δ) * 2)) := by gcongr
      _ = (C * T ^ (-δ)) * T / (π * a₀ * P.L T) := by field_simp
      _ ≤ (C * ε) * T / (π * a₀ * P.L T) := by gcongr
      _ ≤ (η * a₀ / 4) * T / (π * a₀ * P.L T) := by
          gcongr
          calc C * ε ≤ C * (η * a₀ / (4 * C)) := by gcongr
            _ = η * a₀ / 4 := by field_simp
      _ = η * (T / (4 * π)) * (1 / P.L T) := by field_simp
      _ ≤ η * (T / (4 * π)) * l T := by
          gcongr
          calc 1 / P.L T ≤ 1 := by rw [div_le_one hL0]; linarith [Real.pi_gt_three]
            _ ≤ l T := hl
      _ = η * (T * l T / (4 * π)) := by ring
      _ ≤ η * (Z.N T (2 * T) : ℝ) := by gcongr
  · rw [frobSq_hat']
    have hbr : ((Pf T).d T : ℝ) * (8 * (1 + 1 / (Pf T).hgrid T)) + ((Pf T).d T : ℝ) ^ 2 / T ^ 2
        ≤ P.L T ^ 2 * T := by
      rw [hinvh]
      have hL2π : 1 ≤ P.L T / (2 * π) := by rw [le_div_iff₀ (by positivity)]; linarith
      have h1 : ((Pf T).d T : ℝ) * (8 * (1 + P.L T / (2 * π)))
          ≤ (P.L T * T / (2 * π)) * (8 * (P.L T / π)) := by
        gcongr
        calc 1 + P.L T / (2 * π) ≤ P.L T / (2 * π) + P.L T / (2 * π) := by linarith
          _ = P.L T / π := by ring
      have h2 : ((Pf T).d T : ℝ) ^ 2 / T ^ 2 ≤ (P.L T * T / (2 * π)) ^ 2 / T ^ 2 := by gcongr
      have e1 : (P.L T * T / (2 * π)) * (8 * (P.L T / π)) = (4 / π ^ 2) * (P.L T ^ 2 * T) := by
        (field_simp; ring)
      have e2 : (P.L T * T / (2 * π)) ^ 2 / T ^ 2 = (1 / (4 * π ^ 2)) * P.L T ^ 2 := by
        (field_simp; ring)
      have hLT0 : 0 ≤ P.L T ^ 2 * T := by positivity
      have hLT : P.L T ^ 2 ≤ P.L T ^ 2 * T := le_mul_of_one_le_right (sq_nonneg _) hT1
      have i1 : (4 / π ^ 2) * (P.L T ^ 2 * T) ≤ (1 / 2) * (P.L T ^ 2 * T) :=
        mul_le_mul_of_nonneg_right c1 hLT0
      have i2 : (1 / (4 * π ^ 2)) * P.L T ^ 2 ≤ (1 / 2) * (P.L T ^ 2 * T) :=
        mul_le_mul c2 hLT (sq_nonneg _) (by norm_num)
      linarith only [h1, h2, e1, e2, i1, i2]
    have hfr' : frobSq (Z.Gz (Pf T) T - M T) ≤ 2 * (C * T ^ (-δ)) ^ 2 * (P.L T ^ 2 * T) :=
      hfr.trans (mul_le_mul_of_nonneg_left hbr (by positivity))
    have hinv2 : (((Pf T).a T * (Pf T).L T ^ 2)⁻¹) ^ 2 ≤ ((a₀ * P.L T ^ 2)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.2 haL.le) hinv 2
    have hTδ2 : (T ^ (-δ)) ^ 2 ≤ ε := by
      calc (T ^ (-δ)) ^ 2 = T ^ (-δ) * T ^ (-δ) := sq _
        _ ≤ ε * 1 := mul_le_mul hTδ (hTδ.trans hε1) hTδ0 hε0.le
        _ = ε := mul_one _
    calc (((Pf T).a T * (Pf T).L T ^ 2)⁻¹) ^ 2 * frobSq (Z.Gz (Pf T) T - M T)
        ≤ ((a₀ * P.L T ^ 2)⁻¹) ^ 2 * (2 * (C * T ^ (-δ)) ^ 2 * (P.L T ^ 2 * T)) :=
          mul_le_mul hinv2 hfr' (Assembly.frobSq_nonneg _) (sq_nonneg _)
      _ = 2 * C ^ 2 * (T ^ (-δ)) ^ 2 * T / (a₀ ^ 2 * P.L T ^ 2) := by field_simp
      _ ≤ 2 * C ^ 2 * ε * T / (a₀ ^ 2 * P.L T ^ 2) := by gcongr
      _ ≤ 2 * C ^ 2 * (η ^ 2 * a₀ ^ 2 / (26 * C ^ 2)) * T / (a₀ ^ 2 * P.L T ^ 2) := by gcongr
      _ = η ^ 2 * (T / 13) * (1 / P.L T ^ 2) := by (field_simp; ring)
      _ ≤ η ^ 2 * (T / 13) * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
      _ ≤ η ^ 2 * (T * l T / (4 * π)) := by
          rw [mul_one]
          gcongr η ^ 2 * ?_
          calc T / 13 ≤ T / (4 * π) := div_le_div_of_nonneg_left hT.le (by positivity) h13
            _ ≤ T * l T / (4 * π) :=
                div_le_div_of_nonneg_right (le_mul_of_one_le_right hT.le hl) (by positivity)
      _ ≤ η ^ 2 * (Z.N T (2 * T) : ℝ) := by gcongr

/-- **[XF′ Lemma 5.1]**: from XiEF, E = G¹ − M is HatNegligible. -/
theorem hatNegligible_entryError (Z : ZeroConfig) (Pf : ℝ → Params) (P : Params) (hP : P.Valid)
    (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w)
    (ha : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ᶠ T in atTop, a₀ ≤ (Pf T).a T)
    (hR : RiemannVonMangoldt Z) (hEF : XiEF Z Pf) :
    HatNegligible Z Pf (fun T => Z.Gz (Pf T) T - (Pf T).Gp1 T) := by
  obtain ⟨C, δ, T₀, hδ, h⟩ := hEF
  exact hatNegligible_of_entryBound Z Pf P hP hPf ha hR (fun T => (Pf T).Gp1 T)
    ⟨C, δ, T₀, hδ, fun T hT k l => (h T hT k l).2⟩

/-! ## §3. [XF′ Lemma 6.1]: the entry dependence D = M − Mᵀ is HatNegligible -/

section DeltaFacts
variable (P : Params) (T : ℝ)

/-- L⋆(τ⋆) = L_T + ½ log(τ⋆/T) for T, τ⋆ > 0. -/
lemma Lstar_eq_LT_add {τs : ℝ} (hT : 0 < T) (hτ : 0 < τs) :
    Lstar τs = LT T + ((Real.log (τs / T) / 2 : ℝ) : ℂ) := by
  unfold Lstar LT l
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  rw [Real.log_div hτ.ne' h2π.ne', Real.log_div hT.ne' h2π.ne', Real.log_div hτ.ne' hT.ne']
  push_cast
  ring

lemma tau_pos {k : ℕ} (hT : 0 < T) (hh : 0 ≤ P.hgrid T) : 0 < P.tau T k := by
  unfold Params.tau; push_cast; positivity

lemma tau_ge_T {k : ℕ} (hh : 0 ≤ P.hgrid T) : T ≤ P.tau T k := by
  unfold Params.tau; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- d·h ≤ T (d = ⌊LT/2π⌋, h = 2π/L). -/
lemma d_mul_hgrid_le (hL : 0 < P.L T) (hT : 0 ≤ T) : (P.d T : ℝ) * P.hgrid T ≤ T := by
  unfold Params.d Params.hgrid
  have := Nat.floor_le (show 0 ≤ P.L T * T / (2 * Real.pi) by positivity)
  calc (⌊P.L T * T / (2 * Real.pi)⌋₊ : ℝ) * (2 * Real.pi / P.L T)
      ≤ (P.L T * T / (2 * Real.pi)) * (2 * Real.pi / P.L T) := by gcongr
    _ = T := by field_simp

lemma tau_lt_two_T {k : ℕ} (hk : k < P.d T) (hL : 0 < P.L T) (hT : 0 < T) : P.tau T k < 2 * T := by
  have hh : 0 < P.hgrid T := by unfold Params.hgrid; positivity
  have h1 : ((k:ℕ):ℝ) * P.hgrid T < (P.d T : ℝ) * P.hgrid T := by
    gcongr
  have h2 := d_mul_hgrid_le P T hL hT.le
  unfold Params.tau; push_cast; linarith

/-- 0 ≤ δ_{kl} ≤ 1/2 for grid indices 0 ≤ k, l < d. -/
lemma deltaKL_mem {k l : ℕ} (hk : k < P.d T) (hl : l < P.d T) (hL : 0 < P.L T) (hT : 0 < T) :
    P.deltaKL T k l ∈ Set.Icc (0:ℝ) (1 / 2) := by
  have hh : 0 ≤ P.hgrid T := by unfold Params.hgrid; positivity
  have h1 := tau_ge_T P T (k := k) hh
  have h2 := tau_ge_T P T (k := l) hh
  have h3 := tau_lt_two_T P T hk hL hT
  have h4 := tau_lt_two_T P T hl hL hT
  have hτs : T ≤ P.tauStar T k l := by unfold Params.tauStar; linarith
  have hτs' : P.tauStar T k l < 2 * T := by unfold Params.tauStar; linarith
  have hq1 : 1 ≤ P.tauStar T k l / T := by rw [le_div_iff₀ hT]; linarith
  have hq2 : P.tauStar T k l / T ≤ 2 := by rw [div_le_iff₀ hT]; linarith
  unfold Params.deltaKL
  constructor
  · have := Real.log_nonneg hq1; linarith
  · have := Real.log_le_log (by linarith) hq2
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (zero_lt_two' ℝ); linarith
    linarith

lemma tauStar_pos {k l : ℕ} (hT : 0 < T) (hh : 0 ≤ P.hgrid T) : 0 < P.tauStar T k l := by
  unfold Params.tauStar
  have := tau_pos P T (k := k) hT hh
  have := tau_pos P T (k := l) hT hh
  linarith

/-- k ↦ δ_{kk} = ½ log(τ_k/T) is monotone. -/
lemma deltaKL_diag_monotone (hT : 0 < T) (hh : 0 ≤ P.hgrid T) :
    Monotone (fun k : ℕ => P.deltaKL T k k) := by
  intro a b hab
  simp only [Params.deltaKL, Params.tauStar]
  have ha := tau_pos P T (k := a) hT hh
  have hab' : P.tau T a ≤ P.tau T b := by
    unfold Params.tau; push_cast; gcongr
  gcongr

end DeltaFacts

/-- l^n · X / T → 0 for λ < 1 (X = (T/2π)^λ, l = log(T/2π)). -/
lemma tendsto_lpow_mul_X_div (P : Params) (hlam1 : P.lam < 1) (n : ℕ) :
    Tendsto (fun T => l T ^ n * P.X T / T) atTop (𝓝 0) := by
  set c : ℝ := 1 - P.lam with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  -- u ↦ (c u)^n e^{-(c u)} → 0 as u → ∞
  have h1 : Tendsto (fun u : ℝ => (c * u) ^ n * Real.exp (-(c * u))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp (tendsto_id.const_mul_atTop hc0)
  have h2 : Tendsto (fun T : ℝ => (c * l T) ^ n * Real.exp (-(c * l T))) atTop (𝓝 0) :=
    h1.comp Assembly.tendsto_l_atTop
  have h3 : Tendsto (fun T : ℝ => (1 / (2 * π * c ^ n)) * ((c * l T) ^ n * Real.exp (-(c * l T))))
      atTop (𝓝 0) := by
    simpa using h2.const_mul (1 / (2 * π * c ^ n))
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  have hexp : Real.exp (l T) = T / (2 * π) := by
    rw [l, Real.exp_log (by positivity)]
  have hX : P.X T = Real.exp (P.lam * l T) := rfl
  have e1 : Real.exp (-(c * l T)) = Real.exp (P.lam * l T) / Real.exp (l T) := by
    rw [← Real.exp_sub]; congr 1; rw [hc]; ring
  rw [e1, hexp, hX, mul_pow]
  field_simp

/-- **base-generic re-expansion input** (the five fields of Transfer/Inputs.lean's Reexpansion with the base
point Λ₀(T) and the frozen coefficients c(T) as parameters): ξ′ is Λ₀ = LT, c = xiCoeffFamily.c (Reexpansion.toAt);
Z′ is Λ₀ = ½l, c = wCoeffFamily.c (Transfer/W.lean). -/
structure ReexpansionAt (Λ₀ : ℝ → ℂ) (c : ℝ → ℕ → ℂ) (e : ℝ → ℕ → ℕ → ℂ) (ρ₀ A T₀ : ℝ) : Prop where
  expand : ∀ T : ℝ, T₀ ≤ T → ∀ δ : ℝ, δ ∈ Set.Icc (0:ℝ) (1 / 2) → ∀ N : ℕ,
    HasSum (fun r : ℕ => e T (r + 1) N * (δ : ℂ) ^ (r + 1)) (xiCoeff (Λ₀ T + δ) N - c T N)
  e_one : ∀ T : ℝ, ∀ r : ℕ, e T r 1 = 0
  H1 : ∀ T : ℝ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖e T r N‖ / Real.sqrt N) ≤ A * (ρ₀ / l T) ^ r * Real.sqrt x * l T
  H2 : ∀ T : ℝ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖e T r N‖ ^ 2) ≤ A * (ρ₀ / l T) ^ (2 * r) * x * l T ^ 2
  H3 : ∀ T : ℝ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖e T r N‖ ^ 2 / N) ≤ A * (ρ₀ / l T) ^ (2 * r) * l T ^ 2 * (1 + Real.log x)

theorem Reexpansion.toAt {F : CoeffFamily} {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ}
    (h : Reexpansion F e ρ₀ A T₀) : ReexpansionAt LT F.c e ρ₀ A T₀ :=
  ⟨h.expand, h.e_one, h.H1, h.H2, h.H3⟩

/-- the GEOMETRIC form actually consumed by the proof of Lemma 6.1 (derived in §4 from ReexpansionAt +
PPUpper; kept separate so that the analytic argument does not depend on the producers' exact shapes).
For T ≥ T₀ and r ≥ 1, with X = X(T), l = l(T), ρ = ρ₀/l, L = L(T), and the P-part Gram sums over the
window data of Pf T:  the expansion of C(N; L_T+δ) − c_N on δ ∈ [0,1/2] for N ≤ X;  e_r(1) = 0;
S₁(e_r; X) ≤ A ρ^r √X·l;   Σ_{k,l<d} Q_{kl}(e_r)² ≤ A ρ^{2r}·L⁴ T l² + A·L³ l⁴ (1 + X)
(the second, r-independent term is the end-effect term of PPUpper; it is o((aL²)² N) iff λ < 1). -/
structure ReexpansionGeom (Pf : ℝ → Params) (Λ₀ : ℝ → ℂ) (c : ℝ → ℕ → ℂ) (e : ℝ → ℕ → ℕ → ℂ)
    (ρ₀ A T₀ : ℝ) : Prop where
  expand : ∀ T : ℝ, T₀ ≤ T → ∀ δ : ℝ, δ ∈ Set.Icc (0:ℝ) (1 / 2) →
    ∀ N ∈ Finset.Ioc 0 ⌊(Pf T).X T⌋₊,
    HasSum (fun r : ℕ => e T (r + 1) N * (δ : ℂ) ^ (r + 1)) (xiCoeff (Λ₀ T + δ) N - c T N)
  e_one : ∀ T : ℝ, ∀ r : ℕ, e T r 1 = 0
  S1_le : ∀ T : ℝ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r →
    S1 (e T r) ((Pf T).X T) ≤ A * (ρ₀ / l T) ^ r * (Real.sqrt ((Pf T).X T) * l T)
  sumSq_le : ∀ T : ℝ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r →
    (∑ k ∈ Finset.range ((Pf T).d T), ∑ l' ∈ Finset.range ((Pf T).d T),
      GentryNu (Pc ((Pf T).X T) (e T r)) ((Pf T).toSetting T) ((Pf T).localFun T) k l' ^ 2)
      ≤ A * (ρ₀ / l T) ^ (2 * r) * ((Pf T).L T ^ 4 * T * l T ^ 2)
        + A * ((Pf T).L T ^ 3 * l T ^ 4 * (1 + (Pf T).X T))

/-- the entries of D = M − Mᵀ are P-part entries of the coefficient DIFFERENCES (μ, Π_X cancel). -/
lemma Gp1_sub_GpC_apply (P : Params) (T : ℝ) {cϱ : ℝ} (hΓ : GammaFacts)
    (hF : LocalHypsCore cϱ (P.toSetting T) (P.localFun T)) (hX : 0 < P.X T) (hT : 0 < T)
    (hh : 0 ≤ P.hgrid T) (c : ℕ → ℂ) (k l : Fin (P.d T)) :
    (P.Gp1 T - P.GpC T c) k l
      = ((GentryNu (Pc (P.toSetting T).X (xiCoeff (Lstar (P.tauStar T k l)) - c))
          (P.toSetting T) (P.localFun T) k l : ℝ) : ℂ) := by
  have hk := tau_pos P T (k := k) hT hh
  have hl := tau_pos P T (k := l) hT hh
  rw [Matrix.sub_apply]
  simp only [Params.Gp1, Params.GpC, Params.Gentry1]
  rw [← Complex.ofReal_sub, Params.GentryC_eq_GentryW, Params.GentryC_eq_GentryW,
    Transfer.gentryW_one_sub hΓ hF hX _ _ hk hl]

set_option maxHeartbeats 800000 in
/-- **[XF′ Lemma 6.1], base-generic engine**: a matrix family D whose entries are the P-part entries of the
coefficient differences C(·; Λ₀(T)+δ_{kl}) − c(T) is HatNegligible, given the geometric re-expansion input at Λ₀. -/
theorem hatNegligible_of_geom (Z : ZeroConfig) (Pf : ℝ → Params)
    (P : Params) (hP : P.Valid) (hlam1 : P.lam < 1) (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w)
    {cϱ : ℝ} (hcore : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → LocalHypsCore cϱ ((Pf T).toSetting T) ((Pf T).localFun T))
    (ha : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ᶠ T in atTop, a₀ ≤ (Pf T).a T)
    (hR : RiemannVonMangoldt Z)
    {Λ₀ : ℝ → ℂ} {c : ℝ → ℕ → ℂ} {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hA : 0 ≤ A)
    (hG : ReexpansionGeom Pf Λ₀ c e ρ₀ A T₀)
    (D : (T : ℝ) → Matrix (Fin ((Pf T).d T)) (Fin ((Pf T).d T)) ℂ)
    (hD : ∀ T : ℝ, 0 < T → LocalHypsCore cϱ ((Pf T).toSetting T) ((Pf T).localFun T) →
      D T = fun (k l' : Fin ((Pf T).d T)) => ((GentryNu (Pc ((Pf T).toSetting T).X
        (fun N => xiCoeff (Λ₀ T + (((Pf T).deltaKL T k l' : ℝ) : ℂ)) N - c T N))
        ((Pf T).toSetting T) ((Pf T).localFun T) k l' : ℝ) : ℂ)) :
    HatNegligible Z Pf D := by
  obtain ⟨T₁, hcore⟩ := hcore
  obtain ⟨a₀, ha₀, ha⟩ := ha
  intro η hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hπ3 := Real.pi_gt_three
  -- thresholds
  set κtr : ℝ := 2 / Real.log 2 * A * ρ₀ / a₀ with hκtr      -- |tr D̂| ≤ κtr √X
  have hκtr0 : 0 ≤ κtr := by positivity
  set ε : ℝ := a₀ ^ 2 * η ^ 2 / (32 * π * (A + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hsmallX : ∀ᶠ T : ℝ in atTop, l T ^ 4 * P.X T / T ≤ ε :=
    (tendsto_lpow_mul_X_div P hlam1 4).eventually (eventually_le_nhds hε)
  have hsmall0 : ∀ᶠ T : ℝ in atTop, l T ^ 4 * 1 / T ≤ ε := by
    have : Tendsto (fun T => l T ^ 4 * 1 / T) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ (tendsto_lpow_mul_X_div P hlam1 4)
      · filter_upwards [Assembly.eventually_l_pos, eventually_gt_atTop (0:ℝ)] with T hl hT
        positivity
      · filter_upwards [Assembly.eventually_l_pos, eventually_gt_atTop (0:ℝ)] with T hl hT
        have hX1 : 1 ≤ P.X T := by
          unfold Params.X; exact Real.one_le_exp (by unfold Params.L; nlinarith [hP.lam_pos])
        gcongr
    exact this.eventually (eventually_le_nhds hε)
  have hLtop := Assembly.tendsto_L_atTop P hP.lam_pos
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop T₁, eventually_gt_atTop (0:ℝ), ha,
    Assembly.eventually_N_ge Z hR, Assembly.eventually_one_le_l, hLtop.eventually_ge_atTop 1,
    hsmallX, hsmall0, eventually_ge_atTop ((4 * π * κtr / η) ^ 2),
    Assembly.tendsto_l_atTop.eventually_ge_atTop (ρ₀ + 32 * π * A * ρ₀ ^ 2 / (a₀ ^ 2 * η ^ 2))]
    with T hT₀ hT₁ hT haT hN hl1 hL1 hsX hs0 hTbig hlbig
  set P' := Pf T with hP'
  set p := P'.toSetting T with hp
  set Fn := P'.localFun T with hFn
  have hF : LocalHypsCore cϱ p Fn := hcore T hT₁
  have hLf : P'.L T = P.L T := fam_L hPf T
  have hXf : P'.X T = P.X T := fam_X hPf T
  have hL0 : 0 < P.L T := by linarith
  have hX0 : 0 < P.X T := by unfold Params.X; exact Real.exp_pos _
  have hh0 : 0 ≤ P'.hgrid T := by unfold Params.hgrid; rw [hLf]; positivity
  have hl0 : 0 < l T := by linarith
  have hbig0 : (0:ℝ) ≤ 32 * π * A * ρ₀ ^ 2 / (a₀ ^ 2 * η ^ 2) := by positivity
  set ρ : ℝ := ρ₀ / l T with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hl0]; linarith
  set g : ℕ → ℕ → ℕ → ℂ := fun k l' N => xiCoeff (Λ₀ T + ((P'.deltaKL T k l' : ℝ) : ℂ)) N - c T N with hg
  -- δ ≥ 0 for all indices; capped weights
  have hδnn : ∀ k l' : ℕ, 0 ≤ P'.deltaKL T k l' := by
    intro k l'
    have := tau_ge_T P' T (k := k) hh0
    have := tau_ge_T P' T (k := l') hh0
    simp only [Params.deltaKL, Params.tauStar]
    have : 1 ≤ (P'.tau T k + P'.tau T l') / 2 / T := by rw [le_div_iff₀ hT]; linarith
    have := Real.log_nonneg this
    linarith
  set δm : ℕ → ℕ → ℝ := fun k l' => min (P'.deltaKL T k l') (1 / 2) with hδm
  have hδm0 : ∀ k l', 0 ≤ δm k l' := fun k l' => le_min (hδnn k l') (by norm_num)
  have hδm1 : ∀ k l', δm k l' ≤ 1 / 2 := fun k l' => min_le_right _ _
  have hδm_eq : ∀ k, k < P'.d T → ∀ l', l' < P'.d T → δm k l' = P'.deltaKL T k l' := by
    intro k hk l' hl'
    exact min_eq_left (deltaKL_mem P' T hk hl' (by rw [hLf]; exact hL0) hT).2
  have hδv_mono : Monotone (fun k : ℕ => δm k k) :=
    fun a b hab => min_le_min_right _ (deltaKL_diag_monotone P' T hT hh0 hab)
  -- entries of D
  have hDeq : D T = fun (k l' : Fin (P'.d T)) => ((GentryNu (Pc p.X (g k l')) p Fn k l' : ℝ) : ℂ) :=
    hD T hT hF
  -- expansions at the entries
  have hexp2 : ∀ k, k < p.d → ∀ l', l' < p.d → ∀ N ∈ Finset.Ioc 0 ⌊p.X⌋₊,
      HasSum (fun r : ℕ => e T (r + 1) N * (δm k l' : ℂ) ^ (r + 1)) (g k l' N) := by
    intro k hk l' hl' N hN
    have hmem := deltaKL_mem P' T hk hl' (by rw [hLf]; exact hL0) hT
    have := hG.expand T hT₀ _ hmem N hN
    rw [hδm_eq k hk l' hl', hg]
    exact this
  -- S1 and sumSq inputs
  set σ : ℝ := A * (Real.sqrt (P.X T) * l T) with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hS1 : ∀ r : ℕ, 1 ≤ r → S1 (e T r) p.X ≤ σ * ρ ^ r := by
    intro r hr
    calc S1 (e T r) p.X = S1 (e T r) (P'.X T) := rfl
      _ ≤ A * (ρ₀ / l T) ^ r * (Real.sqrt (P'.X T) * l T) := hG.S1_le T hT₀ r hr
      _ = σ * ρ ^ r := by rw [hXf, hσ, hρ]; ring
  set K₁ : ℝ := A * (P.L T ^ 4 * T * l T ^ 2) with hK₁
  set K₀ : ℝ := A * (P.L T ^ 3 * l T ^ 4 * (1 + P.X T)) with hK₀
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hQ : ∀ r : ℕ, 1 ≤ r → (∑ k ∈ Finset.range p.d, ∑ l' ∈ Finset.range p.d,
      GentryNu (Pc p.X (e T r)) p Fn k l' ^ 2) ≤ K₁ * ρ ^ (2 * r) + K₀ := by
    intro r hr
    calc _ = (∑ k ∈ Finset.range (P'.d T), ∑ l' ∈ Finset.range (P'.d T),
          GentryNu (Pc (P'.X T) (e T r)) (P'.toSetting T) (P'.localFun T) k l' ^ 2) := rfl
      _ ≤ A * (ρ₀ / l T) ^ (2 * r) * (P'.L T ^ 4 * T * l T ^ 2)
          + A * (P'.L T ^ 3 * l T ^ 4 * (1 + P'.X T)) := hG.sumSq_le T hT₀ r hr
      _ = K₁ * ρ ^ (2 * r) + K₀ := by rw [hLf, hXf, hK₁, hK₀, hρ]; ring
  -- the two fixed-T conclusions
  have hfrob := Transfer.dependence_frob hF (e := e T) (g := g) (δm := δm)
    hδm0 hδm1 hexp2 hK₁0 hK₀0 hρ0 hρ1 hQ
  have htrace := Transfer.dependence_trace hF (e := e T) (hG.e_one T) (g := fun k => g k k)
    (δv := fun k => δm k k) (fun k => hδm0 k k) (fun k => hδm1 k k) hδv_mono
    (fun k hk => hexp2 k hk k hk) hσ0 hρ0 hρ1 hS1
  -- hat units
  have haT0 : 0 < P'.a T := ha₀.trans_le haT
  have haL : 0 < P'.a T * P'.L T ^ 2 := by rw [hLf]; positivity
  have ha₀L : 0 < a₀ * P.L T ^ 2 := by positivity
  have hinv : (P'.a T * P'.L T ^ 2)⁻¹ ≤ (a₀ * P.L T ^ 2)⁻¹ := by
    rw [hLf]; exact inv_anti₀ ha₀L (by gcongr)
  have hXT : P.X T ≤ T := by
    have h1 : P.X T ≤ Real.exp (l T) := by
      unfold Params.X Params.L
      exact Real.exp_le_exp.2 (by nlinarith [hP.lam_le_one])
    rw [l, Real.exp_log (by positivity)] at h1
    have : T / (2 * π) ≤ T := div_le_self hT.le (by linarith)
    linarith
  constructor
  · -- trace
    rw [rtrace_hat', abs_mul, abs_of_pos (inv_pos.2 haL)]
    have htrD : rtrace (D T)
        = ∑ k ∈ Finset.range p.d, GentryNu (Pc p.X (g k k)) p Fn k k := by
      rw [hDeq]
      unfold rtrace
      simp only [Matrix.trace, Matrix.diag_apply, map_sum, RCLike.re_to_complex, Complex.ofReal_re]
      exact Fin.sum_univ_eq_sum_range (fun k => GentryNu (Pc p.X (g k k)) p Fn k k) _
    rw [htrD]
    have hsqT : 4 * π * κtr / η ≤ Real.sqrt T := by
      calc 4 * π * κtr / η = Real.sqrt ((4 * π * κtr / η) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt T := Real.sqrt_le_sqrt hTbig
    calc (P'.a T * P'.L T ^ 2)⁻¹ * |∑ k ∈ Finset.range p.d, GentryNu (Pc p.X (g k k)) p Fn k k|
        ≤ (a₀ * P.L T ^ 2)⁻¹ * (2 / Real.log 2 * p.L ^ 2 * σ * ρ) :=
          mul_le_mul hinv htrace (abs_nonneg _) (inv_nonneg.2 ha₀L.le)
      _ = κtr * Real.sqrt (P.X T) := by
          rw [show p.L = P'.L T from rfl, hLf, hκtr, hσ, hρ]; field_simp
      _ ≤ κtr * Real.sqrt T := by gcongr
      _ = η / (4 * π) * (4 * π * κtr / η) * Real.sqrt T := by field_simp
      _ ≤ η / (4 * π) * Real.sqrt T * Real.sqrt T := by gcongr
      _ = η * (T / (4 * π)) := by rw [mul_assoc, Real.mul_self_sqrt hT.le]; ring
      _ ≤ η * (T * l T / (4 * π)) := by
          gcongr
          exact le_mul_of_one_le_right hT.le hl1
      _ ≤ η * (Z.N T (2 * T) : ℝ) := by gcongr
  · -- Frobenius
    rw [frobSq_hat']
    have hfrD : frobSq (D T)
        = ∑ k ∈ Finset.range p.d, ∑ l' ∈ Finset.range p.d, GentryNu (Pc p.X (g k l')) p Fn k l' ^ 2 := by
      rw [hDeq]
      exact Transfer.frobSq_ofReal_fin _ (fun k l' => GentryNu (Pc p.X (g k l')) p Fn k l')
    rw [hfrD]
    have hinv2 : ((P'.a T * P'.L T ^ 2)⁻¹) ^ 2 ≤ ((a₀ * P.L T ^ 2)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.2 haL.le) hinv 2
    -- the two smallness facts
    have hsX' : l T ^ 4 * P.X T ≤ ε * T := by
      have := (div_le_iff₀ hT).1 hsX; linarith
    have hs0' : l T ^ 4 ≤ ε * T := by
      have := (div_le_iff₀ hT).1 hs0; linarith
    have i1 : 2 * A * ρ₀ ^ 2 / a₀ ^ 2 * T ≤ η ^ 2 / (8 * π) * (T * l T) := by
      -- l ≥ 16πAρ₀²/(a₀²η²)
      have hl' : 16 * π * A * ρ₀ ^ 2 / (a₀ ^ 2 * η ^ 2) ≤ l T := by
        have : 16 * π * A * ρ₀ ^ 2 / (a₀ ^ 2 * η ^ 2) ≤ 32 * π * A * ρ₀ ^ 2 / (a₀ ^ 2 * η ^ 2) := by
          gcongr; norm_num
        linarith
      have h2 : 2 * A * ρ₀ ^ 2 / a₀ ^ 2 = η ^ 2 / (8 * π) * (16 * π * A * ρ₀ ^ 2 / (a₀ ^ 2 * η ^ 2)) := by
        field_simp; ring
      rw [h2, mul_assoc]
      gcongr η ^ 2 / (8 * π) * ?_
      rw [mul_comm]
      gcongr
    have i2 : 2 * A / a₀ ^ 2 * (l T ^ 4 * (1 + P.X T) / P.L T) ≤ η ^ 2 / (8 * π) * (T * l T) := by
      have h1 : l T ^ 4 * (1 + P.X T) / P.L T ≤ l T ^ 4 * (1 + P.X T) :=
        div_le_self (by positivity) hL1
      have h2 : l T ^ 4 * (1 + P.X T) ≤ 2 * ε * T := by nlinarith
      have h3 : 2 * A / a₀ ^ 2 * (2 * ε * T) = A / (A + 1) * (η ^ 2 / (8 * π) * T) := by
        rw [hεdef]; field_simp; ring
      have h4 : A / (A + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      calc 2 * A / a₀ ^ 2 * (l T ^ 4 * (1 + P.X T) / P.L T)
          ≤ 2 * A / a₀ ^ 2 * (2 * ε * T) := by gcongr; exact h1.trans h2
        _ = A / (A + 1) * (η ^ 2 / (8 * π) * T) := h3
        _ ≤ 1 * (η ^ 2 / (8 * π) * T) := by gcongr
        _ = η ^ 2 / (8 * π) * (T * 1) := by ring
        _ ≤ η ^ 2 / (8 * π) * (T * l T) := by gcongr
    calc ((P'.a T * P'.L T ^ 2)⁻¹) ^ 2
          * ∑ k ∈ Finset.range p.d, ∑ l' ∈ Finset.range p.d, GentryNu (Pc p.X (g k l')) p Fn k l' ^ 2
        ≤ ((a₀ * P.L T ^ 2)⁻¹) ^ 2 * (2 * (K₁ * ρ ^ 2 + K₀)) :=
          mul_le_mul hinv2 hfrob (by positivity) (sq_nonneg _)
      _ = 2 * A * ρ₀ ^ 2 / a₀ ^ 2 * T + 2 * A / a₀ ^ 2 * (l T ^ 4 * (1 + P.X T) / P.L T) := by
          rw [hK₁, hK₀, hρ]; field_simp
      _ ≤ η ^ 2 / (8 * π) * (T * l T) + η ^ 2 / (8 * π) * (T * l T) := add_le_add i1 i2
      _ = η ^ 2 * (T * l T / (4 * π)) := by ring
      _ ≤ η ^ 2 * (Z.N T (2 * T) : ℝ) := by gcongr

/-- **[XF′ Lemma 6.1]** for ξ′: D = M − Mᵀ (Gp1 vs GpC, base L_T) is HatNegligible. -/
theorem hatNegligible_entryDependence (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily)
    (P : Params) (hP : P.Valid) (hlam1 : P.lam < 1) (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w)
    {cϱ : ℝ} (hcore : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → LocalHypsCore cϱ ((Pf T).toSetting T) ((Pf T).localFun T))
    (hΓ : GammaFacts)
    (ha : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ᶠ T in atTop, a₀ ≤ (Pf T).a T)
    (hR : RiemannVonMangoldt Z)
    {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hA : 0 ≤ A)
    (hG : ReexpansionGeom Pf LT F.c e ρ₀ A T₀) :
    HatNegligible Z Pf (fun T => (Pf T).Gp1 T - (Pf T).GpC T (F.c T)) := by
  refine hatNegligible_of_geom Z Pf P hP hlam1 hPf hcore ha hR hρ₀ hA hG _ (fun T hT hF => ?_)
  have hLf : (Pf T).L T = P.L T := fam_L hPf T
  have hL0 : 0 < (Pf T).L T := by
    rw [hLf]; unfold Params.L
    have : 1 ≤ l T := by
      have h := hF.one_le_l; simpa using h
    nlinarith [hP.lam_pos]
  have hh0 : 0 ≤ (Pf T).hgrid T := by unfold Params.hgrid; positivity
  have hX0 : 0 < (Pf T).X T := by unfold Params.X; exact Real.exp_pos _
  ext k l'
  rw [Gp1_sub_GpC_apply (Pf T) T hΓ hF hX0 hT hh0 (F.c T) k l',
    Lstar_eq_LT_add T hT (tauStar_pos (Pf T) T hT hh0)]
  rfl

/-! ## §4. Glue: ReexpansionAt + PPUpper ⇒ ReexpansionGeom -/

lemma sum_fin_fin_eq (d : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ k : Fin d, ∑ l : Fin d, f k l = ∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d, f k l := by
  calc ∑ k : Fin d, ∑ l : Fin d, f k l = ∑ k : Fin d, ∑ l ∈ Finset.range d, f k l :=
        Finset.sum_congr rfl fun k _ => Fin.sum_univ_eq_sum_range (fun l => f k l) d
    _ = ∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d, f k l :=
        Fin.sum_univ_eq_sum_range (fun k => ∑ l ∈ Finset.range d, f k l) d

set_option maxHeartbeats 800000 in
/-- Reexpansion + PPUpper ⇒ the geometric form, with
A' = 4·max(C,1)·max(A,1)² and T₀' large (L ≥ 1, l ≥ max(1,ρ₀), 2 ≤ X ≤ T, T past all thresholds). -/
theorem reexpansionGeom_of (Pf : ℝ → Params) (P : Params) (hP : P.Valid)
    (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w)
    {cϱ : ℝ} (hcore : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → LocalHypsCore cϱ ((Pf T).toSetting T) ((Pf T).localFun T))
    {Λ₀ : ℝ → ℂ} {c : ℝ → ℕ → ℂ} {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hE : ReexpansionAt Λ₀ c e ρ₀ A T₀) (hPP : PPUpper cϱ P.lam) :
    ∃ A' T₀' : ℝ, 0 ≤ A' ∧ ReexpansionGeom Pf Λ₀ c e ρ₀ A' T₀' := by
  obtain ⟨T₁, hcore⟩ := hcore
  obtain ⟨C, T₂, hPP⟩ := hPP
  set C' := max C 1 with hC'
  set A₁ := max A 1 with hA₁
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hA₁1 : 1 ≤ A₁ := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  have hAA₁ : A ≤ A₁ := le_max_left _ _
  have hC'0 : 0 ≤ C' := by linarith
  have hA₁0 : 0 ≤ A₁ := by linarith
  have hA₁sq : A₁ ≤ A₁ ^ 2 := by nlinarith
  set A' := 4 * C' * A₁ ^ 2 with hA'
  have hA'0 : 0 ≤ A' := by positivity
  have hA₁A' : A₁ ≤ A' := by
    rw [hA']; nlinarith [mul_nonneg hC'0 (sq_nonneg A₁)]
  have hAA' : A ≤ A' := hAA₁.trans hA₁A'
  have hLtop := Assembly.tendsto_L_atTop P hP.lam_pos
  have hXtop : Tendsto (fun T => P.X T) atTop atTop := Real.tendsto_exp_atTop.comp hLtop
  have hev : ∀ᶠ T in atTop, T₀ ≤ T ∧ T₁ ≤ T ∧ T₂ ≤ T ∧ 0 < T ∧ 1 ≤ l T ∧ ρ₀ ≤ l T ∧ 1 ≤ P.L T ∧
      2 ≤ P.X T := by
    filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop T₁, eventually_ge_atTop T₂,
      eventually_gt_atTop (0:ℝ), Assembly.eventually_one_le_l,
      Assembly.tendsto_l_atTop.eventually_ge_atTop ρ₀, hLtop.eventually_ge_atTop 1,
      hXtop.eventually_ge_atTop 2] with T h0 h1 h2 h3 h4 h5 h6 h7
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨T₀', hT₀'⟩ := Filter.eventually_atTop.1 hev
  refine ⟨A', T₀', hA'0, ?_⟩
  have hXexp : ∀ T, 0 ≤ l T → P.X T ≤ Real.exp (l T) := by
    intro T hl
    unfold Params.X Params.L
    exact Real.exp_le_exp.2 (by nlinarith [hP.lam_le_one, hl])
  constructor
  · intro T hT δ hδ N _
    exact hE.expand T (hT₀' T hT).1 δ hδ N
  · exact hE.e_one
  · intro T hT r hr
    obtain ⟨h0, -, -, hTpos, hl1, hρl, hL1, hX2⟩ := hT₀' T hT
    have hXf : (Pf T).X T = P.X T := fam_X hPf T
    rw [hXf]
    have H1 := hE.H1 T h0 r hr (P.X T) hX2 (hXexp T (by linarith))
    have hρr : 0 ≤ (ρ₀ / l T) ^ r := by positivity
    calc S1 (e T r) (P.X T) ≤ A * (ρ₀ / l T) ^ r * Real.sqrt (P.X T) * l T := H1
      _ ≤ A' * (ρ₀ / l T) ^ r * Real.sqrt (P.X T) * l T := by gcongr
      _ = A' * (ρ₀ / l T) ^ r * (Real.sqrt (P.X T) * l T) := by ring
  · intro T hT r hr
    obtain ⟨h0, h1, h2, hTpos, hl1, hρl, hL1, hX2⟩ := hT₀' T hT
    have hXe := hXexp T (by linarith)
    have hXT : P.X T ≤ T := by
      have := hXe
      rw [l, Real.exp_log (by positivity)] at this
      have : T / (2 * π) ≤ T := div_le_self hTpos.le (by linarith [Real.pi_gt_three])
      linarith
    have hLf : (Pf T).L T = P.L T := fam_L hPf T
    have hXf : (Pf T).X T = P.X T := fam_X hPf T
    have hF := hcore T h1
    have hpp0 := hPP ((Pf T).toSetting T) ((Pf T).localFun T) (e T r) (hPf T).1 h2 hF (hE.e_one T r)
    have hpp := (sum_fin_fin_eq ((Pf T).toSetting T).d (fun k l =>
      GentryNu (Pc ((Pf T).toSetting T).X (e T r)) ((Pf T).toSetting T) ((Pf T).localFun T) k l ^ 2)).symm.trans_le
      hpp0
    have H3 := hE.H3 T h0 r hr (P.X T) hX2 hXe
    have H2 := hE.H2 T h0 r hr (P.X T) hX2 hXe
    have H1 := hE.H1 T h0 r hr (P.X T) hX2 hXe
    have hlogX : Real.log (P.X T) = P.L T := by unfold Params.X; exact Real.log_exp _
    rw [hlogX] at H3
    -- abstract scalars → concrete
    have eL : ((Pf T).toSetting T).L = P.L T := hLf
    have eX : ((Pf T).toSetting T).X = P.X T := hXf
    have el : ((Pf T).toSetting T).l = l T := rfl
    have eT : ((Pf T).toSetting T).T = T := rfl
    have ed : ((Pf T).toSetting T).d = (Pf T).d T := rfl
    rw [eL, eX, el, eT, ed] at hpp
    rw [hLf, hXf]
    refine hpp.trans ?_
    set Xr := P.X T with hXr
    set Lr := P.L T with hLr
    set lr := l T with hlr
    set ρ' : ℝ := (ρ₀ / lr) ^ (2 * r) with hρ'
    set S := S1 (e T r) Xr with hS
    set Ssq := ∑ N ∈ Finset.Ioc 0 ⌊Xr⌋₊, ‖e T r N‖ ^ 2 with hSsq
    set Sdiv := ∑ N ∈ Finset.Ioc 0 ⌊Xr⌋₊, ‖e T r N‖ ^ 2 / N with hSdiv
    have hρ'0 : 0 ≤ ρ' := by positivity
    have hlr0 : 0 < lr := by linarith
    have hρle : ρ₀ / lr ≤ 1 := by rw [div_le_one hlr0]; exact hρl
    have hρq0 : 0 ≤ ρ₀ / lr := by positivity
    have hρr1 : (ρ₀ / lr) ^ r ≤ 1 := pow_le_one₀ hρq0 hρle
    have hρ'eq : ((ρ₀ / lr) ^ r) ^ 2 = ρ' := by rw [hρ', ← pow_mul, mul_comm]
    have hS0 : 0 ≤ S := S1_nonneg _ _
    have hSsq0 : 0 ≤ Ssq := Finset.sum_nonneg fun _ _ => by positivity
    have hSdiv0 : 0 ≤ Sdiv := Finset.sum_nonneg fun _ _ => by positivity
    have hX0 : 0 ≤ Xr := by linarith
    have hsX : Real.sqrt Xr ^ 2 = Xr := Real.sq_sqrt hX0
    have hlogl : Real.log lr ≤ lr := by
      have := Real.log_le_sub_one_of_pos hlr0; linarith
    have hlogl0 : 0 ≤ Real.log lr := Real.log_nonneg hl1
    -- the four coefficient inputs with A ↦ A₁
    have H2' : Ssq ≤ A₁ * ρ' * Xr * lr ^ 2 :=
      calc Ssq ≤ A * ρ' * Xr * lr ^ 2 := H2
        _ ≤ A₁ * ρ' * Xr * lr ^ 2 := by gcongr
    have H3' : Sdiv ≤ A₁ * ρ' * lr ^ 2 * (1 + Lr) :=
      calc Sdiv ≤ A * ρ' * lr ^ 2 * (1 + Lr) := H3
        _ ≤ A₁ * ρ' * lr ^ 2 * (1 + Lr) := by gcongr
    have hS1' : S ≤ A₁ * (ρ₀ / lr) ^ r * Real.sqrt Xr * lr :=
      calc S ≤ A * (ρ₀ / lr) ^ r * Real.sqrt Xr * lr := H1
        _ ≤ A₁ * (ρ₀ / lr) ^ r * Real.sqrt Xr * lr := by gcongr
    have hSsq' : S ^ 2 ≤ A₁ ^ 2 * ρ' * Xr * lr ^ 2 :=
      calc S ^ 2 ≤ (A₁ * (ρ₀ / lr) ^ r * Real.sqrt Xr * lr) ^ 2 := pow_le_pow_left₀ hS0 hS1' 2
        _ = A₁ ^ 2 * ((ρ₀ / lr) ^ r) ^ 2 * Real.sqrt Xr ^ 2 * lr ^ 2 := by ring
        _ = A₁ ^ 2 * ρ' * Xr * lr ^ 2 := by rw [hρ'eq, hsX]
    have hSle : S ≤ A₁ * Real.sqrt Xr * lr :=
      calc S ≤ A₁ * (ρ₀ / lr) ^ r * Real.sqrt Xr * lr := hS1'
        _ ≤ A₁ * 1 * Real.sqrt Xr * lr := by gcongr
        _ = A₁ * Real.sqrt Xr * lr := by ring
    have hend : (lr + S) ^ 2 ≤ 2 * A₁ ^ 2 * lr ^ 2 * (1 + Xr) := by
      have h1 : (lr + S) ^ 2 ≤ 2 * lr ^ 2 + 2 * S ^ 2 := by nlinarith only [sq_nonneg (lr - S)]
      have h2 : S ^ 2 ≤ A₁ ^ 2 * Xr * lr ^ 2 :=
        calc S ^ 2 ≤ (A₁ * Real.sqrt Xr * lr) ^ 2 := pow_le_pow_left₀ hS0 hSle 2
          _ = A₁ ^ 2 * Xr * lr ^ 2 := by rw [mul_pow, mul_pow, hsX]
      have h3 : lr ^ 2 ≤ A₁ ^ 2 * lr ^ 2 := by
        have : 1 ≤ A₁ ^ 2 := by nlinarith only [hA₁1]
        nlinarith only [this, sq_nonneg lr]
      have e : 2 * A₁ ^ 2 * lr ^ 2 * (1 + Xr) = 2 * (A₁ ^ 2 * lr ^ 2) + 2 * (A₁ ^ 2 * Xr * lr ^ 2) := by
        ring
      linarith only [h1, h2, h3, e]
    -- C ↦ C'
    have hbr0 : 0 ≤ T * Lr * Sdiv + Lr * Ssq + Lr * S ^ 2 + Lr * lr * Real.log lr * (lr + S) ^ 2 := by
      positivity
    have step1 : C * Lr ^ 2 * (T * Lr * Sdiv + Lr * Ssq + Lr * S ^ 2 + Lr * lr * Real.log lr * (lr + S) ^ 2)
        ≤ C' * Lr ^ 2 * (T * Lr * Sdiv + Lr * Ssq + Lr * S ^ 2 + Lr * lr * Real.log lr * (lr + S) ^ 2) := by
      gcongr
    refine step1.trans ?_
    -- the four terms
    have b1 : T * Lr * Sdiv ≤ T * Lr * (A₁ * ρ' * lr ^ 2 * (1 + Lr)) := by gcongr
    have b2 : Lr * Ssq ≤ Lr * (A₁ * ρ' * Xr * lr ^ 2) := by gcongr
    have b3 : Lr * S ^ 2 ≤ Lr * (A₁ ^ 2 * ρ' * Xr * lr ^ 2) := by gcongr
    have b4 : Lr * lr * Real.log lr * (lr + S) ^ 2 ≤ Lr * lr * lr * (2 * A₁ ^ 2 * lr ^ 2 * (1 + Xr)) := by
      gcongr
    have hsum : T * Lr * Sdiv + Lr * Ssq + Lr * S ^ 2 + Lr * lr * Real.log lr * (lr + S) ^ 2
        ≤ T * Lr * (A₁ * ρ' * lr ^ 2 * (1 + Lr)) + Lr * (A₁ * ρ' * Xr * lr ^ 2)
          + Lr * (A₁ ^ 2 * ρ' * Xr * lr ^ 2) + Lr * lr * lr * (2 * A₁ ^ 2 * lr ^ 2 * (1 + Xr)) := by
      linarith only [b1, b2, b3, b4]
    -- main ≤ A' ρ' L⁴ T l², end ≤ A' L³ l⁴ (1+X)
    have hXLT : Xr ≤ Lr * T := by nlinarith only [hXT, hL1, hTpos]
    have i1 : A₁ * (T * (1 + Lr)) ≤ A₁ * (T * (2 * Lr)) := by gcongr; linarith
    have i2 : (A₁ + A₁ ^ 2) * Xr ≤ (A₁ + A₁ ^ 2) * (Lr * T) := by gcongr
    have i3 : A₁ * (T * (1 + Lr)) + (A₁ + A₁ ^ 2) * Xr ≤ 4 * A₁ ^ 2 * (Lr * T) :=
      calc A₁ * (T * (1 + Lr)) + (A₁ + A₁ ^ 2) * Xr
          ≤ A₁ * (T * (2 * Lr)) + (A₁ + A₁ ^ 2) * (Lr * T) := add_le_add i1 i2
        _ = (3 * A₁ + A₁ ^ 2) * (Lr * T) := by ring
        _ ≤ (3 * A₁ ^ 2 + A₁ ^ 2) * (Lr * T) := by gcongr
        _ = 4 * A₁ ^ 2 * (Lr * T) := by ring
    have hpre : 0 ≤ C' * ρ' * lr ^ 2 * Lr ^ 3 := by positivity
    have main : C' * Lr ^ 2 * (T * Lr * (A₁ * ρ' * lr ^ 2 * (1 + Lr)) + Lr * (A₁ * ρ' * Xr * lr ^ 2)
        + Lr * (A₁ ^ 2 * ρ' * Xr * lr ^ 2)) ≤ A' * ρ' * (Lr ^ 4 * T * lr ^ 2) :=
      calc C' * Lr ^ 2 * (T * Lr * (A₁ * ρ' * lr ^ 2 * (1 + Lr)) + Lr * (A₁ * ρ' * Xr * lr ^ 2)
            + Lr * (A₁ ^ 2 * ρ' * Xr * lr ^ 2))
          = C' * ρ' * lr ^ 2 * Lr ^ 3 * (A₁ * (T * (1 + Lr)) + (A₁ + A₁ ^ 2) * Xr) := by ring
        _ ≤ C' * ρ' * lr ^ 2 * Lr ^ 3 * (4 * A₁ ^ 2 * (Lr * T)) := mul_le_mul_of_nonneg_left i3 hpre
        _ = A' * ρ' * (Lr ^ 4 * T * lr ^ 2) := by rw [hA']; ring
    have hpre2 : 0 ≤ C' * A₁ ^ 2 * (Lr ^ 3 * lr ^ 4 * (1 + Xr)) := by positivity
    have endt : C' * Lr ^ 2 * (Lr * lr * lr * (2 * A₁ ^ 2 * lr ^ 2 * (1 + Xr)))
        ≤ A' * (Lr ^ 3 * lr ^ 4 * (1 + Xr)) :=
      calc C' * Lr ^ 2 * (Lr * lr * lr * (2 * A₁ ^ 2 * lr ^ 2 * (1 + Xr)))
          = 2 * (C' * A₁ ^ 2 * (Lr ^ 3 * lr ^ 4 * (1 + Xr))) := by ring
        _ ≤ 4 * (C' * A₁ ^ 2 * (Lr ^ 3 * lr ^ 4 * (1 + Xr))) := by linarith only [hpre2]
        _ = A' * (Lr ^ 3 * lr ^ 4 * (1 + Xr)) := by rw [hA']; ring
    have hCL : 0 ≤ C' * Lr ^ 2 := by positivity
    calc C' * Lr ^ 2 * (T * Lr * Sdiv + Lr * Ssq + Lr * S ^ 2 + Lr * lr * Real.log lr * (lr + S) ^ 2)
        ≤ C' * Lr ^ 2 * (T * Lr * (A₁ * ρ' * lr ^ 2 * (1 + Lr)) + Lr * (A₁ * ρ' * Xr * lr ^ 2)
            + Lr * (A₁ ^ 2 * ρ' * Xr * lr ^ 2) + Lr * lr * lr * (2 * A₁ ^ 2 * lr ^ 2 * (1 + Xr))) :=
          mul_le_mul_of_nonneg_left hsum hCL
      _ = C' * Lr ^ 2 * (T * Lr * (A₁ * ρ' * lr ^ 2 * (1 + Lr)) + Lr * (A₁ * ρ' * Xr * lr ^ 2)
            + Lr * (A₁ ^ 2 * ρ' * Xr * lr ^ 2))
          + C' * Lr ^ 2 * (Lr * lr * lr * (2 * A₁ ^ 2 * lr ^ 2 * (1 + Xr))) := by ring
      _ ≤ A' * ρ' * (Lr ^ 4 * T * lr ^ 2) + A' * (Lr ^ 3 * lr ^ 4 * (1 + Xr)) := add_le_add main endt

/-! ## §5. The main theorem of this file -/

/-- **XiTraceTransfer** [XF′ Lemma 5.1 + Lemma 6.1] from the named inputs. -/
theorem xiTraceTransfer_of (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily)
    (P : Params) (hP : P.Valid) (hlam1 : P.lam < 1) (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w)
    {cϱ : ℝ} (hcore : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → LocalHypsCore cϱ ((Pf T).toSetting T) ((Pf T).localFun T))
    (hΓ : GammaFacts)
    (ha : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ᶠ T in atTop, a₀ ≤ (Pf T).a T)
    (hR : RiemannVonMangoldt Z) (hEF : XiEF Z Pf)
    {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hE : Reexpansion F e ρ₀ A T₀)
    (hPP : PPUpper cϱ P.lam) :
    XiTraceTransfer Z Pf F := by
  obtain ⟨A', T₀', hA', hG⟩ := reexpansionGeom_of Pf P hP hPf hcore hρ₀ hE.toAt hPP
  exact xiTraceTransfer_of_negligible Z Pf F
    (hatNegligible_entryError Z Pf P hP hPf ha hR hEF)
    (hatNegligible_entryDependence Z Pf F P hP hlam1 hPf hcore hΓ ha hR hρ₀ hA' hG)

/-! ## §6. The flat-window instance (Pf := fun _ => P): the family hypotheses discharged from the tree -/

/-- **XiTraceTransfer for the flat window family** Pf = fun _ => P: the taper facts (PrimeSide.localHypsEventually
+ LocalHyps.toCore) and a ≥ 1/2 (Params.half_le_a) come from the tree, so only the genuine inputs remain. -/
theorem xiTraceTransfer_of_flat (Z : ZeroConfig) (P : Params) (F : CoeffFamily) (hP : P.Valid)
    (hlam1 : P.lam < 1) (hΓ : GammaFacts) (hR : RiemannVonMangoldt Z) (hEF : XiEF Z (fun _ => P))
    {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hE : Reexpansion F e ρ₀ A T₀)
    (hPP : PPUpper P.crho P.lam) :
    XiTraceTransfer Z (fun _ => P) F := by
  obtain ⟨T₁, hT₁⟩ := PrimeSide.localHypsEventually hP
  refine xiTraceTransfer_of Z (fun _ => P) F P hP hlam1 (fun _ => ⟨rfl, rfl⟩)
    ⟨T₁, fun T hT => (hT₁ T hT).toCore⟩ hΓ ?_ hR hEF hρ₀ hE hPP
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)] with T hwL
  exact Params.half_le_a hP hwL

end XiPrime
end Zeta23
