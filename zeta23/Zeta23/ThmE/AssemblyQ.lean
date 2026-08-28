/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/AssemblyQ.lean — the §6 assembly generalized to conductor q.

Everything ζ-free in Zeta23/Assembly.lean that mentioned ℓ₁ = l + (2log2−1) is reproved here with
ℓ_{1,χ} = l + c_q, c_q := log q + 2log2 − 1 ([thm:E] proof (iii): "ℓ₁ replaced by ℓ_{1,χ} :=
log(qT/2π) + 2log2 − 1, and λ₁ = L/ℓ_{1,χ} → λ as q is fixed").  The matrix-level parts
(seamA, seamA_BC, BlockInputs, TailInputs), the H/F algebra and the ε-machinery of Zeta23/Assembly.lean
are reused verbatim — only the λ₁/ℓ₁-dependent steps and the prime-side identification change.
Every constant below may depend on q (q fixed; recorded for [rem:otherL](i)).
-/
import Zeta23.Assembly
import Zeta23.ThmE.TracesHypChi

open Filter Asymptotics Topology Real

noncomputable section

namespace Zeta23
namespace ThmE

open Assembly

/-! ## Q1. Scalars: ℓ_{1,χ} = l + c_q and λ_{1,χ} -/

/-- `c_q := log q + 2 log 2 − 1`; `c_1 = c₀`. -/
def cq (q : ℕ) : ℝ := Real.log q + Assembly.c₀

lemma cq_pos {q : ℕ} (hq : 1 ≤ q) : 0 < cq q :=
  add_pos_of_nonneg_of_pos (Real.log_nonneg (by exact_mod_cast hq)) c₀_pos

/-- `ℓ_{1,χ}(T) = l(T) + c_q` for `T > 0`. -/
lemma ell1q_eq {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT : 0 < T) : ell1q q T = l T + cq q := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  unfold ell1q cq Assembly.c₀ l
  rw [show (q : ℝ) * T / (2 * Real.pi) = (q : ℝ) * (T / (2 * Real.pi)) by ring,
    Real.log_mul hq0.ne' (by positivity)]
  ring

lemma ell1q_pos {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT : 0 < T) (hl : 0 < l T) : 0 < ell1q q T := by
  rw [ell1q_eq hq hT]; linarith [cq_pos hq]

lemma lam1q_eq (P : Params) {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT : 0 < T) :
    lam1q P q T = P.lam * l T / (l T + cq q) := by
  unfold lam1q Params.L
  rw [ell1q_eq hq hT]

section Lam1q
variable (P : Params) {q : ℕ} {T : ℝ}

lemma lam1q_le (hq : 1 ≤ q) (hT : 0 < T) (hlam : 0 ≤ P.lam) (hl : 0 < l T) :
    lam1q P q T ≤ P.lam := by
  rw [lam1q_eq P hq hT]
  have hc := cq_pos hq
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma sub_lam1q_le (hq : 1 ≤ q) (hT : 0 < T) (hlam : 0 ≤ P.lam) (hl : 0 < l T) :
    P.lam - lam1q P q T ≤ P.lam * cq q / l T := by
  rw [lam1q_eq P hq hT]
  have hc := cq_pos hq
  have h1 : P.lam - P.lam * l T / (l T + cq q) = P.lam * cq q / (l T + cq q) := by
    field_simp; ring
  rw [h1]
  apply div_le_div_of_nonneg_left (by positivity) hl
  linarith

lemma lam1q_pos (hq : 1 ≤ q) (hT : 0 < T) (hlam : 0 < P.lam) (hl : 0 < l T) :
    0 < lam1q P q T := by
  rw [lam1q_eq P hq hT]; have hc := cq_pos hq; positivity

/-- `H(λ_{1,χ}) ≥ H(λ) − c_q/(λ l)` (the §6 step "H(λ₁) ≥ H(λ) − 1/(λl)" with c₀ → c_q; exact
identity `H(λ) − H(λ₁) = c_q/(λl) − (λ−λ₁)/3`). -/
theorem Hfun_lam1q_ge (hq : 1 ≤ q) (hT : 0 < T) (hlam : 0 < P.lam) (hl : 0 < l T) :
    Hfun P.lam - cq q / (P.lam * l T) ≤ Hfun (lam1q P q T) := by
  have hc := cq_pos hq
  have hl1 : 0 < l T + cq q := by linarith
  have key : Hfun P.lam - Hfun (lam1q P q T)
      = cq q / (P.lam * l T) - (P.lam - lam1q P q T) / 3 := by
    rw [lam1q_eq P hq hT]
    simp only [Hfun]
    field_simp
    ring
  have hle := lam1q_le P hq hT hlam.le hl
  linarith

/-- `F(λ_{1,χ}) ≥ F(λ) − c_q/l`. -/
theorem Ffun_lam1q_ge (hq : 1 ≤ q) (hT : 0 < T) (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1)
    (hl : 0 < l T) :
    Ffun P.lam - cq q / l T ≤ Ffun (lam1q P q T) := by
  have hle := lam1q_le P hq hT hlam.le hl
  have hpos := lam1q_pos P hq hT hlam hl
  have hsub := sub_lam1q_le P hq hT hlam.le hl
  have h1 := Ffun_sub_le (lam1q P q T) P.lam hpos.le hle hlam1
  have h2 : P.lam * cq q / l T ≤ 1 * cq q / l T := by
    apply div_le_div_of_nonneg_right _ hl.le
    nlinarith [cq_pos hq]
  have h3 : (1 : ℝ) * cq q / l T = cq q / l T := by ring
  linarith

end Lam1q

/-! ## Q2. Growth under H-RvM(χ) -/

section GrowthQ
variable (q : ℕ) (Z : ZeroConfig)

/-- H-RvM(χ) ⇒ `N_χ(T,2T) ≥ T l /(4π)` eventually. -/
lemma eventually_N_ge_chi (hq : 1 ≤ q) (hR : RiemannVonMangoldtChi q Z) :
    ∀ᶠ T in atTop, T * l T / (4 * π) ≤ (Z.N T (2 * T) : ℝ) := by
  obtain ⟨C, T₀, h⟩ := hR.main
  filter_upwards [eventually_ge_atTop T₀, eventually_log_le_two_l, eventually_log_nonneg,
    eventually_l_pos, eventually_ge_atTop (16 * π * |C|), eventually_gt_atTop 0]
    with T hT hlog hlog0 hl hTC hT0
  have h1 := (abs_le.mp (h T hT)).1
  have hc := cq_pos hq
  have hℓ : l T ≤ ell1q q T := by rw [ell1q_eq hq hT0]; linarith
  have h2 : -(C * Real.log T) ≥ -(|C| * (2 * l T)) := by
    have : C * Real.log T ≤ |C| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
    nlinarith [abs_nonneg C]
  have h3 : T / (2 * π) * l T ≤ T / (2 * π) * ell1q q T :=
    mul_le_mul_of_nonneg_left hℓ (by positivity)
  have h4 : 2 * |C| * l T ≤ T * l T / (4 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [abs_nonneg C, Real.pi_pos]
  have h5 : T / (2 * π) * l T = 2 * (T * l T / (4 * π)) := by ring
  linarith

/-- H-RvM(χ) ⇒ `N_χ(T,2T) ≤ K_q · T l` eventually for some constant; `K_q = 1 + c_q` works
(ℓ_{1,χ} ≤ (1 + c_q) l once l ≥ 1). -/
lemma eventually_N_le_chi (hq : 1 ≤ q) (hR : RiemannVonMangoldtChi q Z) :
    ∀ᶠ T in atTop, (Z.N T (2 * T) : ℝ) ≤ (1 + cq q) * (T * l T) := by
  obtain ⟨C, T₀, h⟩ := hR.main
  filter_upwards [eventually_ge_atTop T₀, eventually_log_le_two_l, eventually_log_nonneg,
    eventually_one_le_l, eventually_ge_atTop (16 * |C| + 4), eventually_gt_atTop 0]
    with T hT hlog hlog0 hl hTC hT0
  have h1 := (abs_le.mp (h T hT)).2
  have hc := cq_pos hq
  have hℓ : ell1q q T ≤ (1 + cq q) * l T := by
    rw [ell1q_eq hq hT0]; nlinarith
  have h2 : C * Real.log T ≤ |C| * (2 * l T) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0).trans
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg C))
  have h3 : T / (2 * π) * ell1q q T ≤ T / (2 * π) * ((1 + cq q) * l T) :=
    mul_le_mul_of_nonneg_left hℓ (by positivity)
  have hlpos : (0:ℝ) < l T := by linarith
  have hY : (0:ℝ) ≤ (1 + cq q) * l T := by nlinarith
  have hdiv : T / (2 * π) ≤ T / 6 :=
    div_le_div_of_nonneg_left hT0.le (by norm_num) (by nlinarith [Real.pi_gt_three])
  have hπ : T / (2 * π) * ((1 + cq q) * l T) ≤ (1 + cq q) * (T * l T) / 6 := by
    calc T / (2 * π) * ((1 + cq q) * l T) ≤ T / 6 * ((1 + cq q) * l T) :=
          mul_le_mul_of_nonneg_right hdiv hY
      _ = (1 + cq q) * (T * l T) / 6 := by ring
  have h6 : 2 * |C| * l T ≤ (1 + cq q) * (T * l T) / 6 := by
    rw [le_div_iff₀ (by norm_num)]
    have e1 : (16 * |C| + 4) * l T ≤ T * l T := mul_le_mul_of_nonneg_right hTC hlpos.le
    have e2 : T * l T ≤ (1 + cq q) * (T * l T) := by
      nlinarith [cq_pos hq, mul_pos hT0 hlpos]
    nlinarith [abs_nonneg C, hlpos]
  have hnn : 0 ≤ (1 + cq q) * (T * l T) := by nlinarith [mul_pos hT0 hlpos, cq_pos hq]
  linarith

lemma tendsto_N_atTop_chi (hq : 1 ≤ q) (hR : RiemannVonMangoldtChi q Z) :
    Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop :=
  tendsto_atTop_mono' _ (eventually_N_ge_chi q Z hq hR)
    (tendsto_Tl_atTop.atTop_div_const (by positivity))

lemma isLittleO_N_of_isLittleO_Tl_chi (hq : 1 ≤ q) (hR : RiemannVonMangoldtChi q Z) {f : ℝ → ℝ}
    (hf : f =o[atTop] fun T => T * l T) : f =o[atTop] fun T => (Z.N T (2 * T) : ℝ) := by
  refine hf.trans_isBigO (IsBigO.of_bound (4 * π) ?_)
  filter_upwards [eventually_N_ge_chi q Z hq hR, eventually_ge_atTop 0, eventually_l_pos]
    with T h hT hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  have := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 4 * π)
  calc T * l T = 4 * π * (T * l T / (4 * π)) := by field_simp
    _ ≤ 4 * π * (Z.N T (2 * T) : ℝ) := this

/-- `cλ_χ = 1/λ_{1,χ} + λ_{1,χ}/3` eventually in `[0, 2/λ + 1/3]`. -/
lemma eventually_clam_bounds_chi (P : Params) (hq : 1 ≤ q) (hlam : 0 < P.lam)
    (hlam1 : P.lam ≤ 1) :
    ∀ᶠ T in atTop,
      0 ≤ 1 / lam1q P q T + lam1q P q T / 3 ∧
        1 / lam1q P q T + lam1q P q T / 3 ≤ 2 / P.lam + 1 / 3 := by
  filter_upwards [tendsto_l_atTop.eventually_ge_atTop (max 1 (cq q)), eventually_gt_atTop 0]
    with T hl hT0
  have hl1 : (1:ℝ) ≤ l T := le_trans (le_max_left _ _) hl
  have hlc : cq q ≤ l T := le_trans (le_max_right _ _) hl
  have hlpos : 0 < l T := by linarith
  have hc := cq_pos hq
  have hpos := lam1q_pos P hq hT0 hlam hlpos
  have hle := (lam1q_le P hq hT0 hlam.le hlpos).trans hlam1
  have hhalf : P.lam / 2 ≤ lam1q P q T := by
    rw [lam1q_eq P hq hT0, le_div_iff₀ (by linarith)]
    nlinarith
  refine ⟨by positivity, ?_⟩
  have h1 : 1 / lam1q P q T ≤ 2 / P.lam := by
    rw [div_le_div_iff₀ hpos hlam]; linarith
  linarith

end GrowthQ

/-! ## Q3. The prime-side identification and seam B for L(s,χ) -/

section UnitsChi
open Assembly

variable (P : Params) (κ q : ℕ) (c : ℕ → ℂ)

/-- The prime-side matrix for L(s,χ) ([eq:Gdef] second expression with ν_{X,χ}), as a complex
matrix (entries real). -/
def GpChi (T : ℝ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => (GentryChi P κ q c T (k : ℤ) (l : ℤ) : ℂ)

lemma GpChi_isHermitian (T : ℝ) : (GpChi P κ q c T).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro k l
  simp only [GpChi, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inj, GentryChi]
  congr 1; ext τ; ring

lemma rtrace_tilde_GpChi (T : ℝ) :
    RHLinalg.rtrace (P.tilde T (GpChi P κ q c T)) = trGtildeChi P κ q c T := by
  rw [Assembly.tilde_eq, Assembly.rtrace_smul_ofReal]
  simp [trGtildeChi, RHLinalg.rtrace, Matrix.trace, GpChi]

lemma frobSq_tilde_GpChi (T : ℝ) :
    RHLinalg.frobSq (P.tilde T (GpChi P κ q c T)) = trGtildeSqChi P κ q c T := by
  rw [Assembly.tilde_eq, Assembly.frobSq_smul_ofReal, Assembly.frobSq_eq_sum_norm_sq]
  simp [trGtildeSqChi, GpChi, sq_abs]

/-- **Seam B for L(s,χ)** (mirror of `Assembly.seamB` with ℓ₁ → ℓ_{1,χ}, λ₁ → λ_{1,χ}): given the
bridge `Z.Gz P T = GpChi`, [eq:tr1]/[eq:tr2]-χ at height T and RvM(χ) in the form
`T ℓ_{1,χ}/2π ≤ N + RN`:  `|tr Ĝ − N| ≤ C₁√X/a` and the ‖Ĝ‖_F² bound with `cλ = 1/λ_{1,χ} + λ_{1,χ}/3`. -/
theorem seamBChi {Z : ZeroConfig} {T : ℝ} (hGzGp : Z.Gz P T = GpChi P κ q c T)
    (ha : 0 < P.a T) (hL : 0 < P.L T) (hℓ₁ : 0 < ell1q q T)
    {C₁ C₂ ET RN : ℝ}
    (htr1 : |trGtildeChi P κ q c T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)|
      ≤ C₁ * (P.L T * Real.sqrt (P.X T)))
    (hK : 0 ≤ 1 + C₂ * ET)
    (htr2 : trGtildeSqChi P κ q c T - mainTr2Chi P q T ≤ C₂ * ET * mainTr2Chi P q T)
    (hRvM : T * ell1q q T / (2 * Real.pi) ≤ (Z.N T (2 * T) : ℝ) + RN) :
    |RHLinalg.rtrace (P.hat T (Z.Gz P T)) - (Z.N T (2 * T) : ℝ)|
        ≤ C₁ * Real.sqrt (P.X T) / P.a T ∧
    RHLinalg.frobSq (P.hat T (Z.Gz P T))
      ≤ (1 / lam1q P q T + lam1q P q T / 3) * (Z.N T (2 * T) : ℝ)
        + (1 / lam1q P q T + lam1q P q T / 3) * (((1 + C₂ * ET) / P.a T ^ 2 - 1)
            * (Z.N T (2 * T) : ℝ) + (1 + C₂ * ET) / P.a T ^ 2 * RN) := by
  rw [hGzGp, Assembly.rtrace_hat, Assembly.frobSq_hat, rtrace_tilde_GpChi, frobSq_tilde_GpChi]
  refine ⟨Assembly.trGhat_sub_N_le ha hL htr1, ?_⟩
  have h := Assembly.frobGhat_le (T := T) (trG2 := trGtildeSqChi P κ q c T)
    (N := (Z.N T (2 * T) : ℝ)) (ℓ₁ := ell1q q T) (C := C₂) (calE := ET) (RN := RN)
    ha hL hℓ₁ hK (by simpa [mainTr2Chi] using htr2) hRvM
  simpa [lam1q] using h

end UnitsChi

/-! ## Q4. Theorem E at fixed `λ < 1`, abstract zero configuration (mirror of Assembly Part F3/F4) -/

section MainChi
open Assembly Filter Asymptotics Topology

/-- **Theorem E first bound at fixed `λ ∈ (0,1)`, abstract zero configuration** ([thm:E] with §6's
proof; mirror of `Assembly.thmA_abstract` with ℓ₁ → ℓ_{1,χ}, λ₁ → λ_{1,χ}, ν_X → ν_{X,χ}).  Same
abstract inputs; all constants may depend on q. -/
theorem thmE_A_abstract (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q) (cf : ℕ → ℂ)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (hRvM : RiemannVonMangoldtChi q Z)
    (hTr : ThmTracesHypChi P κ q cf Z)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z P T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = GpChi P κ q cf T)
    (ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Hfun P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0star T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, htr2⟩ := hTr.tr2
  obtain ⟨CN, T₃, hRvM'⟩ := hRvM.main
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cl : ℝ → ℝ := fun T => 1 / lam1q P q T + lam1q P q T / 3 with hcl
  set K : ℝ → ℝ := fun T => (1 + C₂ * P.calE T) / P.a T ^ 2 with hK
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / P.a T with hR₁
  set R₂ : ℝ → ℝ := fun T => cl T * ((K T - 1) * N T + K T * (|CN| * Real.log T)) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (P.a T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cl T * N T + R₂ T) + B T)) + cq q / (P.lam * l T) * N T with herr
  have hLtop := tendsto_L_atTop P hlam0
  have ha1 := tendsto_a_one P hlam0 ha
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ P.a T := by
    filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hw := hP.one_le_w
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]
  have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
    simpa using hcalE.const_mul C₂
  have hKto : Tendsto K atTop (𝓝 1) := by
    have h1 : Tendsto (fun T => 1 + C₂ * P.calE T) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hcE0
    have h2 : Tendsto (fun T => P.a T ^ 2) atTop (𝓝 1) := by simpa using ha1.pow 2
    simpa [hK, Pi.div_def] using h1.div h2 one_ne_zero
  have hmain : ∀ᶠ T in atTop, Hfun P.lam * N T - err T ≤ (Z.N0star T (2 * T) : ℝ) := by
    filter_upwards [hBlock, hTail, hGzGp, hapos, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop T₃, eventually_gt_atTop (0:ℝ), eventually_l_pos,
      eventually_log_nonneg, hcE0.eventually (eventually_gt_nhds (show (-1:ℝ) < 0 by norm_num))]
      with T hB hTl hGG ha2 hT₁ hT₂ hT₃ hT0 hl hlog hcE
    have hapos' : 0 < P.a T := by linarith
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hℓ₁ : 0 < ell1q q T := ell1q_pos hq hT0 hl
    have hKnn : 0 ≤ 1 + C₂ * P.calE T := by linarith
    have hA := seamA hT0.le hB hTl hapos' hLpos
    have htr2' : trGtildeSqChi P κ q cf T - mainTr2Chi P q T
        ≤ C₂ * P.calE T * mainTr2Chi P q T := by
      have := htr2 T hT₂
      simp only at this
      rw [← mul_assoc] at this
      exact (le_abs_self _).trans this
    have htr1' : |trGtildeChi P κ q cf T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)|
        ≤ C₁ * (P.L T * Real.sqrt (P.X T)) := by
      have := htr1 T hT₁; simpa only using this
    have hRvM'' : T * ell1q q T / (2 * Real.pi) ≤ N T + |CN| * Real.log T := by
      have h1 := (abs_le.mp (hRvM' T hT₃)).1
      have h2 : CN * Real.log T ≤ |CN| * Real.log T :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlog
      have h3 : T / (2 * Real.pi) * ell1q q T = T * ell1q q T / (2 * Real.pi) := by ring
      simp only [hNdef]; linarith
    have hSB := seamBChi P κ q cf hGG hapos' hLpos hℓ₁ htr1' hKnn htr2' hRvM''
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := N0star_lower_H hB₀ hA hSB.1 hSB.2
    have hH := Hfun_lam1q_ge P hq hT0 hlam0 hl
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hHN : (Hfun P.lam - cq q / (P.lam * l T)) * N T ≤ Hfun (lam1q P q T) * N T :=
      mul_le_mul_of_nonneg_right hH hN0
    simp only [herr, hR₁, hR₂, hBdef, hcl, hK, hNdef] at h hHN ⊢
    linarith
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop_chi q Z hq hRvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / P.a T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [hapos] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith))]
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  have o2 : R₂ =o[atTop] N := by
    have hclO : cl =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 / P.lam + 1 / 3) ?_
      filter_upwards [eventually_clam_bounds_chi q P hq hlam0 hlam1] with T h
      rw [abs_of_nonneg h.1]; exact h.2
    have hK1 : Tendsto (fun T => K T - 1) atTop (𝓝 0) := by simpa using hKto.sub_const 1
    have hKO : K =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2) ?_
      filter_upwards [hKto.eventually (eventually_ge_nhds (show (0:ℝ) < 1 by norm_num)),
        hKto.eventually (eventually_le_nhds (show (1:ℝ) < 2 by norm_num))] with T h1 h2
      rw [abs_of_nonneg h1]; exact h2
    have i1 : (fun T => (K T - 1) * N T) =o[atTop] N := isLittleO_of_tendsto_zero_mul hK1
    have i2 : (fun T => K T * (|CN| * Real.log T)) =o[atTop] N :=
      isLittleO_of_bdd_mul hKO
        ((isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM isLittleO_log_Tl).const_mul_left _)
    exact isLittleO_of_bdd_mul hclO (i1.add i2)
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO
      (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM isLittleO_sqrt_mul_l_Tl)
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, hapos, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by positivity)
    · filter_upwards [hTail, hapos, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < P.a T := by linarith
      have hq' : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (P.a T * P.L T) := by
            have e : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
                = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
            rw [e]; gcongr
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cl) hNtop o1 o2 o3 o4 (eventually_clam_bounds_chi q P hq hlam0 hlam1)
  have o6 : (fun T => cq q / (P.lam * l T) * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have : Tendsto (fun T => P.lam * l T) atTop atTop := tendsto_l_atTop.const_mul_atTop hlam0
    simpa using tendsto_const_nhds.div_atTop this
  have herr_o : err =o[atTop] N := o5.add o6
  exact eps_form_of_isLittleO hmain (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o

end MainChi

/-! ## Q5. Theorem E bounds 2 and 3 (mirror of Assembly Part F4) -/

section MainBCChi
open Assembly Filter Asymptotics Topology

/-- **Theorems E.B / E.C core at fixed `λ ∈ (0,1)`, abstract zero configuration** (mirror of
`Assembly.thmBC_core` with the χ-scalars). -/
theorem thmE_BC_core (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q) (cf : ℕ → ℂ)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (hRvM : RiemannVonMangoldtChi q Z)
    (hTr : ThmTracesHypChi P κ q cf Z)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z P T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = GpChi P κ q cf T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∃ R : ℝ → ℝ, R =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) ∧
      ∀ᶠ T in atTop,
        (2 * Ffun P.lam - 1) * (Z.N T (2 * T) : ℝ) - 2 * R T ≤ Z.N0s T (2 * T) ∧
        Ffun P.lam * (Z.N T (2 * T) : ℝ) - R T ≤ Z.Nd T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₃, hC₃, T₃, hratio⟩ := hTr.ratio
  obtain ⟨C₄, hC₄, T₄, htr1'⟩ := hTr.tr1'
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set x : ℝ → ℝ := fun T => θ₀ T * (P.d T : ℝ) / trGtildeChi P κ q cf T with hxdef
  set R : ℝ → ℝ := fun T => (C₃ * P.calE T * (Ffun (lam1q P q T) * N T)
      + 2 * x T * ((1 + C₃ * P.calE T) * (Ffun (lam1q P q T) * N T)))
      + (NII Z T : ℝ) + cq q / l T * N T with hRdef
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop_chi q Z hq hRvM
  have hcE0 : Tendsto (fun T => C₃ * P.calE T) atTop (𝓝 0) := by simpa using hcalE.const_mul C₃
  have hcE4 : Tendsto (fun T => C₄ * P.calE T) atTop (𝓝 0) := by simpa using hcalE.const_mul C₄
  have hx : ∀ᶠ T in atTop, 0 < trGtildeChi P κ q cf T ∧ 0 ≤ x T ∧
      x T ≤ 4 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) ∧
      θ₀ T * (P.d T : ℝ) < trGtildeChi P κ q cf T := by
    filter_upwards [hTail, hθ, eventually_ge_atTop T₄, eventually_N_ge_chi q Z hq hRvM,
      eventually_l_pos, eventually_gt_atTop (0:ℝ),
      hcE4.eventually (eventually_lt_nhds (show (0:ℝ) < 1/2 by norm_num)),
      (tendsto_rpow_halflam_sub_one P hlam1).eventually
        (eventually_lt_nhds (show (0:ℝ) < 1 / (8 * (|Cθ| + 1)) by positivity))]
      with T hTl hθT hT₄ hNge hl hT0 hcE hTs
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have h1 := (abs_le.mp (by simpa only using htr1' T hT₄)).1
    have hLN : 0 < P.L T * N T := by
      have : 0 < T * l T / (4 * Real.pi) := by positivity
      exact mul_pos hLpos (this.trans_le hNge)
    have htrG : P.L T * N T / 2 ≤ trGtildeChi P κ q cf T := by
      have : C₄ * P.calE T * (P.L T * N T) ≤ 1 / 2 * (P.L T * N T) :=
        mul_le_mul_of_nonneg_right hcE.le hLN.le
      simp only [hNdef] at this h1 ⊢; linarith
    have htrGpos : 0 < trGtildeChi P κ q cf T := lt_of_lt_of_le (by positivity) htrG
    have hd : (P.d T : ℝ) ≤ P.L T * T / (2 * Real.pi) := d_le P (by positivity)
    have hθ' : θ₀ T ≤ (|Cθ| + 1) * l T * T ^ (P.lam / 2 - 1) := by
      refine hθT.trans ?_
      have : Cθ ≤ |Cθ| + 1 := by linarith [le_abs_self Cθ]
      gcongr
    have hθ0 := hTl.theta_nonneg
    have hnum : θ₀ T * (P.d T : ℝ)
        ≤ ((|Cθ| + 1) * l T * T ^ (P.lam / 2 - 1)) * (P.L T * T / (2 * Real.pi)) :=
      mul_le_mul hθ' hd (Nat.cast_nonneg _) (hθ0.trans hθ')
    have hden : P.L T * (T * l T / (4 * Real.pi)) / 2 ≤ trGtildeChi P κ q cf T :=
      le_trans (by gcongr) htrG
    have hxle : x T ≤ 4 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) := by
      simp only [hxdef]
      rw [div_le_iff₀ htrGpos]
      calc θ₀ T * (P.d T : ℝ)
          ≤ ((|Cθ| + 1) * l T * T ^ (P.lam / 2 - 1)) * (P.L T * T / (2 * Real.pi)) := hnum
        _ = 4 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) * (P.L T * (T * l T / (4 * Real.pi)) / 2) := by
            ring
        _ ≤ 4 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) * trGtildeChi P κ q cf T := by gcongr
    refine ⟨htrGpos, div_nonneg (mul_nonneg hθ0 (Nat.cast_nonneg _)) htrGpos.le, hxle, ?_⟩
    have hx1 : x T < 1 := by
      refine hxle.trans_lt ?_
      have := (lt_div_iff₀ (show (0:ℝ) < 8 * (|Cθ| + 1) by positivity)).mp hTs
      nlinarith [abs_nonneg Cθ, Real.rpow_nonneg hT0.le (P.lam / 2 - 1)]
    simp only [hxdef] at hx1
    rwa [div_lt_one htrGpos] at hx1
  refine ⟨R, ?_, ?_⟩
  · have hFN : (fun T => Ffun (lam1q P q T) * N T) =O[atTop] N := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_l_pos, eventually_gt_atTop 0] with T hl hT0
      have hb := Ffun_bounds (lam1q_pos P hq hT0 hlam0 hl).le
        ((lam1q_le P hq hT0 hlam0.le hl).trans hlam1)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb.1, one_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hb.2
    have o1 : (fun T => C₃ * P.calE T * (Ffun (lam1q P q T) * N T)) =o[atTop] N := by
      have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO hFN
      simpa using this
    have hxto : Tendsto x atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using (tendsto_rpow_halflam_sub_one P hlam1).const_mul (4 * (|Cθ| + 1)))
        (hx.mono fun T h => h.2.1) (hx.mono fun T h => h.2.2.1)
    have o2 : (fun T => 2 * x T * ((1 + C₃ * P.calE T) * (Ffun (lam1q P q T) * N T)))
        =o[atTop] N := by
      have h2x : Tendsto (fun T => 2 * x T) atTop (𝓝 0) := by simpa using hxto.const_mul 2
      have hK : (fun T => 1 + C₃ * P.calE T) =O[atTop] (fun _ => (1:ℝ)) := by
        refine isBigO_one_of_abs_le (C := 2) ?_
        filter_upwards [hcE0.eventually (eventually_ge_nhds (show (-1:ℝ) < 0 by norm_num)),
          hcE0.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))] with T h1 h2
        rw [abs_of_nonneg (by linarith)]; linarith
      have := ((isLittleO_one_iff ℝ).2 h2x).mul_isBigO (hK.mul hFN)
      simpa using this
    have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
      have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
        refine IsBigO.of_bound CII ?_
        filter_upwards [hII, eventually_l_pos] with T h hl
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
          abs_of_nonneg (by positivity)]
        simpa [mul_assoc] using h
      exact hO.trans_isLittleO
        (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM isLittleO_sqrt_mul_l_Tl)
    have o4 : (fun T => cq q / l T * N T) =o[atTop] N :=
      isLittleO_of_tendsto_zero_mul (tendsto_const_nhds.div_atTop tendsto_l_atTop)
    exact ((o1.add o2).add o3).add o4
  · filter_upwards [hBlock, hTail, hGzGp, hx, eventually_ge_atTop T₃, eventually_gt_atTop (0:ℝ),
      eventually_l_pos, eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w)]
      with T hB hTl hGG hxT hT₃ hT0 hl hE0
    have hGt : (P.tilde T (Z.Gz P T)).IsHermitian := by
      rw [hGG]; exact isHermitian_tilde P T (GpChi_isHermitian P κ q cf T)
    have hZ := seamA_BC hT0.le hB hTl le_rfl hGt
    have hθ0 := hTl.theta_nonneg
    have hrt : RHLinalg.rtrace (P.tilde T (Z.Gz P T)) = trGtildeChi P κ q cf T := by
      rw [hGG, rtrace_tilde_GpChi]
    have hfr : RHLinalg.frobSq (P.tilde T (Z.Gz P T)) = trGtildeSqChi P κ q cf T := by
      rw [hGG, frobSq_tilde_GpChi]
    have htr' : θ₀ T * (Fintype.card (Fin (P.d T)) : ℝ) < RHLinalg.rtrace (P.tilde T (Z.Gz P T)) := by
      rw [card_fin_d, hrt]; exact hxT.2.2.2
    have hCS := nplus_lower hGt hθ0 htr'
    rw [card_fin_d, hrt, hfr] at hCS
    have hratio' : |trGtildeChi P κ q cf T ^ 2 / trGtildeSqChi P κ q cf T
        - Ffun (lam1q P q T) * N T| ≤ C₃ * P.calE T * (Ffun (lam1q P q T) * N T) := by
      have := hratio T hT₃; simp only at this; rw [← mul_assoc] at this; exact this
    have htrG2 : 0 ≤ trGtildeSqChi P κ q cf T := by rw [← hfr]; exact frobSq_nonneg _
    have hnp := nplus_ge_explicit hCS hxT.1 (mul_nonneg hθ0 (Nat.cast_nonneg _)) htrG2 hratio'
    have hF := Ffun_lam1q_ge P hq hT0 hlam0 hlam1 hl
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hFN : (Ffun P.lam - cq q / l T) * N T ≤ Ffun (lam1q P q T) * N T :=
      mul_le_mul_of_nonneg_right hF hN0
    simp only [hRdef, hxdef, hNdef] at hnp hFN hZ ⊢
    constructor <;> nlinarith [hZ.1, hZ.2, hnp, hFN]

end MainBCChi

end ThmE
end Zeta23
