/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
import Zeta23.LinAlg
import Zeta23.Defs
import Zeta23.Defs.Counting
import Zeta23.Assembly.Inputs
import Zeta23.Hypotheses
import Zeta23.PrimeSideTemp
import Zeta23.TracesBoundsE
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# §4 "The counting inequalities" and §6 "Proofs of Theorems A, B, C" — assembly

Reference: the paper, labels `prop:zeroside-rank`, `eq:zeroside-rank`,
`prop:zeroside`, `eq:zeroside`, `eq:zeroside2`, and `sec:proofs` (proofs of `thm:A`, `thm:B`, `thm:C`).

Design:
* Parts A–E of this file are **ζ-free and Defs-free**: theorems about Hermitian matrices
  (Part A, consuming the `RHLinalg` §3 lemmas) and about real numbers / explicit real
  functions (Parts B–E).  Every analytic or combinatorial input produced elsewhere
  (prop:block — `ZeroSide.lean`; prop:tail — `Tail.lean`; thm:traces — `PrimeSideTemp.lean`'s
  `TracesBounds`; Riemann–von Mangoldt and the local count — `Hypotheses.lean`; taper facts —
  `Taper.lean`) enters as an explicit, named hypothesis whose docstring quotes the paper label.
* Part F instantiates A–E with the concrete objects of `Defs.lean`: `thmA_abstract`, `thmB_abstract`,
  `thmC_abstract` (Theorems A–C at fixed `λ < 1` for an abstract `ZeroConfig`, taking prop:block / prop:tail /
  the H-EF bridge / [eq:abdef] / thm:traces as named inputs).
* Error terms are explicit inequalities with named constants throughout Parts A–D; filters /
  `Tendsto` appear only in the final `ε`-wrappers (Part E).

## Units (paper §4, [eq:AE], [eq:hatunits])

Three normalisations of the same real-symmetric `d × d` matrix occur:
* `G` [eq:Gdef];
* `G̃ = G / L`, `Ã = A / L`, `Ẽ = E / L` ("tilde units") — lem:weyl and lem:CS are applied to
  `G̃ = Ã + Ẽ` with threshold `θ = θ₀ ≥ ‖Ẽ‖` (prop:zeroside);
* `Ĝ = G / (a L²)`, `Â`, `Ê` ("hat units", [eq:hatunits]) — lem:ranktrace is applied to `Â = P + Q`
  **only** in these units (paper, after prop:zeroside-rank: "Lemma lem:ranktrace is not
  scale-invariant: it must be applied in the units (eq:hatunits), in which tr P ≤ N_on(I′)").
The two systems meet only through the explicit conversion of Part D,
`tr Ĝ = tr G̃ /(aL)`, `‖Ĝ‖_F² = tr G̃² /(aL)²` (paper §6, first line of the proof of Thm A), and the
taper constant `a` must cancel in `tr Ĝ = N + O(√X / a)`.

Scalar field: `ZeroSide.lean` works over `ℂ` (the inertia argument lives on `ℂ^d`); Part A is kept
`RCLike`-generic like `RHLinalg` and is instantiated at `ℂ` in Part F.
-/

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace Assembly

/-! ## Part A.  Matrix-level counting inequalities (paper §4, "The counting inequalities") -/

section MatrixLevel

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For any Hermitian matrix, `n₊(A) ≤ rank A` (positive eigenvalues are nonzero eigenvalues).
Used in prop:zeroside: "`n₊^θ(G̃) ≤ n₊(Ã) ≤ rank Ã ≤ #𝒵(I′)`". -/
lemma posIndex_le_rank {A : Matrix n n 𝕜} (hA : A.IsHermitian) : posIndex hA ≤ A.rank := by
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  unfold posIndex
  apply card_le_card
  intro i
  simp only [mem_filter, mem_univ, true_and]
  exact ne_of_gt

/-- **prop:zeroside-rank, first assertion** (the paper, `prop:zeroside-rank`):
"`s₁ + s₂ ≥ 4 tr Â − 2 N(I′) − ‖Â‖_F²`".

Stated over the abstract output of prop:block(ii) — `Â = P + Q`, `P ⪰ 0`, `rank P ≤ r`
(paper: `r = s₁+s₂`), `tr P ≤ N_on(I′)`, `Q` Hermitian with `n₊(Q) ≤ b` (paper: `b = p`) — together
with the counting fact `N_on(I′) + 2p ≤ N(I′)` ([eq:Ncount] and the line after it).  Proof exactly as
in the paper: lem:ranktrace at `c = 2` (`RHLinalg.rank_trace_ineq_two`) gives
`r ≥ 2 tr P + 4 tr Q − 4b − ‖P+Q‖_F² = 4 tr Â − 2(tr P + 2b) − ‖Â‖_F²`, and `tr P + 2b ≤ N(I′)`.

UNITS: hat units `Â = A/(aL²)` only [eq:hatunits]. -/
theorem zeroside_rank_core {Ahat P Q : Matrix n n 𝕜}
    (hPQ : Ahat = P + Q) (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hrank : P.rank ≤ r) (hpos : posIndex hQ ≤ b)
    {Non NI' : ℝ} (htrP : rtrace P ≤ Non) (hNcount : Non + 2 * b ≤ NI') :
    4 * rtrace Ahat - 2 * NI' - frobSq Ahat ≤ r := by
  have h := rank_trace_ineq_two hP hQ hrank hpos
  subst hPQ
  rw [rtrace_add]
  linarith

end MatrixLevel

/-! ### Frobenius-norm bookkeeping

`RHLinalg.frobSq A = Re tr(Aᴴ A)`.  We identify it with the square of Mathlib's (scoped) Frobenius
norm, to get the triangle inequality `‖Ĝ − Ê‖_F ≤ ‖Ĝ‖_F + ‖Ê‖_F` used in prop:zeroside-rank. -/

section Frob
open scoped Matrix.Norms.Frobenius

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n]

lemma frobSq_eq_sum_norm_sq (A : Matrix n n 𝕜) : frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold frobSq
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, map_sum, RCLike.star_def]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- `RHLinalg.frobSq A = ‖A‖_F ²` (Mathlib's Frobenius norm, scoped instance). -/
lemma frobSq_eq_norm_sq (A : Matrix n n 𝕜) : frobSq A = ‖A‖ ^ 2 := by
  rw [frobSq_eq_sum_norm_sq, frobenius_norm_def]
  simp_rw [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]

lemma frobSq_nonneg (A : Matrix n n 𝕜) : 0 ≤ frobSq A := by
  rw [frobSq_eq_sum_norm_sq]; positivity

/-- `‖A‖_F = √(frobSq A)`. -/
lemma norm_eq_sqrt_frobSq (A : Matrix n n 𝕜) : ‖A‖ = Real.sqrt (frobSq A) := by
  rw [frobSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Triangle inequality in the form used by prop:zeroside-rank:
`‖G − E‖_F² ≤ (‖G‖_F + ‖E‖_F)²`, written with `frobSq` and `√`. -/
lemma frobSq_sub_le (G E : Matrix n n 𝕜) :
    frobSq (G - E) ≤ (Real.sqrt (frobSq G) + Real.sqrt (frobSq E)) ^ 2 := by
  rw [frobSq_eq_norm_sq, ← norm_eq_sqrt_frobSq, ← norm_eq_sqrt_frobSq]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le G E) 2

/-- **prop:zeroside-rank, perturbation step** (proof of `prop:zeroside-rank` in the paper):
"`Â = Ĝ − Ê` with `|tr Ê| ≤ ‖Ê‖₁` and `‖Â‖_F ≤ ‖Ĝ‖_F + ‖Ê‖_F ≤ ‖Ĝ‖_F + ‖Ê‖₁`, so …
`4 tr Â − ‖Â‖_F² ≥ 4 tr Ĝ − ‖Ĝ‖_F² − O(θ₀ L⁻¹ (1 + ‖Ĝ‖_F))`".

Here the `O(·)` is made explicit: with `B ≥ 0` any common bound for `|tr Ê|` and `‖Ê‖_F`
(prop:tail supplies `B = ‖Ê‖₁ ≤ 2θ₀/L`), the loss is exactly `B (4 + 2‖Ĝ‖_F + B)`.
UNITS: hat units. -/
theorem four_tr_sub_frobSq_perturb {Ghat Ahat Ehat : Matrix n n 𝕜}
    (hGAE : Ghat = Ahat + Ehat) {B : ℝ} (hB : 0 ≤ B)
    (htrE : |rtrace Ehat| ≤ B) (hfrE : frobSq Ehat ≤ B ^ 2) :
    4 * rtrace Ghat - frobSq Ghat - B * (4 + 2 * Real.sqrt (frobSq Ghat) + B)
      ≤ 4 * rtrace Ahat - frobSq Ahat := by
  have hA : Ahat = Ghat - Ehat := by rw [hGAE]; abel
  have htr : rtrace Ahat = rtrace Ghat - rtrace Ehat := by rw [hA, rtrace_sub]
  have hsqE : Real.sqrt (frobSq Ehat) ≤ B := Real.sqrt_le_iff.mpr ⟨hB, hfrE⟩
  have hsqG : 0 ≤ Real.sqrt (frobSq Ghat) := Real.sqrt_nonneg _
  have hfrA : frobSq Ahat ≤ (Real.sqrt (frobSq Ghat) + B) ^ 2 := by
    rw [hA]
    refine (frobSq_sub_le Ghat Ehat).trans ?_
    gcongr
  have hGG : Real.sqrt (frobSq Ghat) ^ 2 = frobSq Ghat := Real.sq_sqrt (frobSq_nonneg _)
  have htrE' : rtrace Ehat ≤ B := (le_abs_self _).trans htrE
  nlinarith [hfrA, hGG, htrE', htr]

end Frob

section MatrixLevel2

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **prop:zeroside, [eq:zeroside]** (the paper's `prop:zeroside`): "For every `θ ≥ θ₀`,
`s₁ ≥ 2 n₊^θ(G̃) − N(I′)` and `#𝒵(I′) ≥ n₊^θ(G̃)`."

Inputs, as in the paper's proof: lem:weyl (`RHLinalg.weyl_posIndexAbove_le`, needs
`|λᵢ(Ẽ)| ≤ θ` for all `i`, which is `‖Ẽ‖ ≤ θ₀ ≤ θ`), prop:block(i) (`n₊(Ã) ≤ s₁+s₂+p`,
`rank Ã ≤ #𝒵(I′)`), and [eq:Ncount] (`N(I′) ≥ s₁ + 2s₂ + 2p`).
UNITS: tilde units `G̃ = Ã + Ẽ`. -/
theorem zeroside_core {At Et : Matrix n n 𝕜}
    (hAt : At.IsHermitian) (hEt : Et.IsHermitian)
    {θ : ℝ} (hθ : ∀ i, |hEt.eigenvalues i| ≤ θ)
    {s₁ s₂ p cardZ : ℕ} (hblock_pos : posIndex hAt ≤ s₁ + s₂ + p) (hblock_rank : At.rank ≤ cardZ)
    {NI' : ℝ} (hNcount : (s₁ : ℝ) + 2 * s₂ + 2 * p ≤ NI') :
    2 * (posIndexAbove (hAt.add hEt) θ : ℝ) - NI' ≤ s₁ ∧
      posIndexAbove (hAt.add hEt) θ ≤ cardZ := by
  have hweyl : posIndexAbove (hAt.add hEt) θ ≤ posIndex hAt := weyl_posIndexAbove_le hAt hEt hθ
  refine ⟨?_, ?_⟩
  · have h1 : (posIndexAbove (hAt.add hEt) θ : ℝ) ≤ s₁ + s₂ + p := by
      exact_mod_cast hweyl.trans hblock_pos
    linarith
  · exact hweyl.trans ((posIndex_le_rank hAt).trans hblock_rank)

/-- `posIndexAbove` depends only on the matrix, not on the particular Hermitian-ness proof
(convenience for rewriting `G̃ = Ã + Ẽ`). -/
lemma posIndexAbove_congr {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) (θ : ℝ) : posIndexAbove hA θ = posIndexAbove hB θ := by
  subst h; rfl

/-- **[eq:nplus-lower]** (proof of `thm:B` in the paper): lem:CS (`RHLinalg.cauchySchwarz_count`)
applied to `R = G̃`, `θ = θ₀`: if `tr G̃ > θ₀ d` then
`n₊^{θ₀}(G̃) ≥ (tr G̃ − θ₀ d)² / tr G̃²`.  (`d = Fintype.card n`; `tr G̃² = ‖G̃‖_F² = frobSq G̃` for
Hermitian `G̃`.  This is `cauchySchwarz_count` verbatim, re-exported under the paper's equation
name.)  UNITS: tilde units. -/
theorem nplus_lower {Gt : Matrix n n 𝕜} (hGt : Gt.IsHermitian) {θ : ℝ} (hθ : 0 ≤ θ)
    (htr : θ * Fintype.card n < rtrace Gt) :
    (rtrace Gt - θ * Fintype.card n) ^ 2 / frobSq Gt ≤ (posIndexAbove hGt θ : ℝ) :=
  cauchySchwarz_count hGt hθ htr

end MatrixLevel2

/-! ## Part B.  The functions `H`, `F` and the `λ₁` versus `λ` step (paper [eq:Fdef], §6)

Vocabulary from `Zeta23/Defs.lean`: `l T = log(T/2π)`, `ell1 T = l T + 2 log 2 − 1`, `Hfun`, `Ffun`,
`P.L T = P.lam * l T`, `P.lam1 T = P.L T / ell1 T`. -/

section HF
open Real

/-- The constant `c₀ := 2 log 2 − 1 = ℓ₁ − l` (paper §1 Notation / [eq:RvM]); `0 < c₀ < 1`. -/
def c₀ : ℝ := 2 * Real.log 2 - 1

lemma c₀_pos : 0 < c₀ := by
  have := Real.log_two_gt_d9; unfold c₀; linarith

lemma c₀_lt_one : c₀ < 1 := by
  have := Real.log_two_lt_d9; unfold c₀; linarith

lemma ell1_eq (T : ℝ) : ell1 T = l T + c₀ := by simp only [ell1, c₀]; ring

lemma ell1_pos {T : ℝ} (hl : 0 < l T) : 0 < ell1 T := by
  rw [ell1_eq]; have := c₀_pos; linarith

/-- `λ₁ = λ l / (l + c₀)` — unfolded form of `Params.lam1` [eq:ratio]. -/
lemma lam1_eq (P : Params) (T : ℝ) : P.lam1 T = P.lam * l T / (l T + c₀) := by
  simp only [Params.lam1, Params.L, ell1_eq]

/-- `0 ≤ λ − λ₁`, i.e. `λ₁ ≤ λ` (paper §6: "`0 ≤ λ − λ₁ ≤ λ/l`"), for `l > 0`, `λ ≥ 0`. -/
lemma lam1_le (P : Params) (T : ℝ) (hlam : 0 ≤ P.lam) (hl : 0 < l T) : P.lam1 T ≤ P.lam := by
  rw [lam1_eq]
  have hc := c₀_pos
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `λ − λ₁ ≤ λ / l` (paper §6); indeed `λ − λ₁ = λ c₀/(l + c₀)` with `c₀ < 1`. -/
lemma sub_lam1_le (P : Params) (T : ℝ) (hlam : 0 ≤ P.lam) (hl : 0 < l T) :
    P.lam - P.lam1 T ≤ P.lam / l T := by
  rw [lam1_eq]
  have hc := c₀_pos; have hc1 := c₀_lt_one
  have h1 : P.lam - P.lam * l T / (l T + c₀) = P.lam * c₀ / (l T + c₀) := by
    field_simp; ring
  rw [h1, div_le_div_iff₀ (by linarith) hl]
  have h2 : c₀ * l T ≤ l T + c₀ := by nlinarith
  calc P.lam * c₀ * l T = P.lam * (c₀ * l T) := by ring
    _ ≤ P.lam * (l T + c₀) := mul_le_mul_of_nonneg_left h2 hlam

lemma lam1_pos (P : Params) (T : ℝ) (hlam : 0 < P.lam) (hl : 0 < l T) : 0 < P.lam1 T := by
  rw [lam1_eq]; have hc := c₀_pos; positivity

/-- **`H(λ₁) ≥ H(λ) − 1/(λ l)`** (the paper §6, proof of Thm A: "Since `H′(x) = x⁻² − 1/3 ∈ (0,∞)`
is decreasing on `(0,1]` and `0 ≤ λ − λ₁ ≤ λ/l`, we have `H(λ₁) ≥ H(λ) − 1/(λl)`").
We prove it via the exact identity `H(λ) − H(λ₁) = c₀/(λ l) − (λ − λ₁)/3` and `c₀ = 2 log 2 − 1 < 1`.
(Note `λ₁ = L/ℓ₁ ≠ λ`.) -/
theorem Hfun_lam1_ge (P : Params) (T : ℝ) (hlam : 0 < P.lam) (hl : 0 < l T) :
    Hfun P.lam - 1 / (P.lam * l T) ≤ Hfun (P.lam1 T) := by
  have hc := c₀_pos; have hc1 := c₀_lt_one
  have hl1 : 0 < l T + c₀ := by linarith
  have hle := lam1_le P T hlam.le hl
  have key : Hfun P.lam - Hfun (P.lam1 T) = c₀ / (P.lam * l T) - (P.lam - P.lam1 T) / 3 := by
    rw [lam1_eq]
    simp only [Hfun]
    field_simp
    ring
  have : c₀ / (P.lam * l T) ≤ 1 / (P.lam * l T) :=
    div_le_div_of_nonneg_right hc1.le (by positivity)
  linarith

/-- Lipschitz bound for `F` on `[0,1]`: `F(y) − F(x) ≤ y − x` for `0 ≤ x ≤ y ≤ 1`
(paper: "`F′(x) = (1−x²/3)/(1+x²/3)² ∈ (0,1]` on `[0,1]`"), proved by algebra. -/
lemma Ffun_sub_le (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (_hy : y ≤ 1) : Ffun y - Ffun x ≤ y - x := by
  simp only [Ffun]
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hx (sub_nonneg.2 hxy), mul_nonneg (mul_nonneg hx hx) (sub_nonneg.2 hxy),
    sq_nonneg x, sq_nonneg y, mul_nonneg hx (hx.trans hxy), mul_le_mul hxy hxy hx (hx.trans hxy)]

/-- **`F(λ₁) ≥ F(λ) − 1/l`** (the paper §6, proof of Thm B: "`F′(x) = (1−x²/3)/(1+x²/3)² ∈ (0,1]`
on `[0,1]` and `0 ≤ λ − λ₁ ≤ 1/l`, so `F(λ₁) ≥ F(λ) − 1/l`"). -/
theorem Ffun_lam1_ge (P : Params) (T : ℝ) (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) (hl : 0 < l T) :
    Ffun P.lam - 1 / l T ≤ Ffun (P.lam1 T) := by
  have hle := lam1_le P T hlam.le hl
  have hpos := lam1_pos P T hlam hl
  have hsub := sub_lam1_le P T hlam.le hl
  have h1 := Ffun_sub_le (P.lam1 T) P.lam hpos.le hle hlam1
  have h2 : P.lam / l T ≤ 1 / l T := div_le_div_of_nonneg_right hlam1 hl.le
  linarith

/-- `sup_{λ<1} H(λ) = 2/3`, in the quantitative form used for the `λ → 1⁻` step:
for `λ ∈ [1/2, 1]`, `H(λ) ≥ 2/3 − (5/3)(1 − λ)`. -/
lemma Hfun_ge_near_one (lam : ℝ) (h1 : 1 / 2 ≤ lam) (h2 : lam ≤ 1) :
    2 / 3 - 5 / 3 * (1 - lam) ≤ Hfun lam := by
  simp only [Hfun]
  have hlam : 0 < lam := by linarith
  have : 1 / lam ≤ 1 + 2 * (1 - lam) := by
    rw [div_le_iff₀ hlam]; nlinarith
  linarith

/-- For `λ ∈ [0, 1]`, `F(λ) ≥ 3/4 − (1 − λ)` (for the `λ → 1⁻` step of Thm B/C). -/
lemma Ffun_ge_near_one (lam : ℝ) (h1 : 0 ≤ lam) (h2 : lam ≤ 1) :
    3 / 4 - (1 - lam) ≤ Ffun lam := by
  have := Ffun_sub_le lam 1 h1 h2 le_rfl
  rw [Ffun_one] at this; linarith

end HF

/-! ## Part C.  §6 at fixed `T`: the explicit inequality for Theorem A

All quantities are real numbers attached to one fixed `T` (and fixed `λ`, `ϱ`); every error term is
explicit.  Dictionary (paper ↔ arguments): `N = N(T,2T)`, `NII = N(I′∖I) := N(T−D₀,T) + N(2T,2T+D₀)`,
`N0star = N₀*(T,2T)`, `s12 = s₁ + s₂`, `trGh = tr Ĝ`, `frGh = ‖Ĝ‖_F²`, `trAh = tr Â`,
`frAh = ‖Â‖_F²`, `B` = the prop:tail bound for `|tr Ê|` and `‖Ê‖_F` (`≤ 2θ₀/L`). -/

section FixedT

/-- **[eq:zeroside-rank] made explicit** (the paper `prop:zeroside-rank`, second assertion):
"`N₀*(T,2T) ≥ 4 tr Ĝ − ‖Ĝ‖_F² − 2N(T,2T) − O(θ₀L⁻¹(1+‖Ĝ‖_F) + D₀ l)`", here with the `O(·)`
replaced by the explicit `3 N(I′∖I) + B(4 + 2‖Ĝ‖_F + B)`.
Inputs: `hcount` = "`s₁+s₂ ≤ N₀*(T,2T) + N(I′∖I)`"; `hcore` = `zeroside_rank_core` with
`N(I′) = N(T,2T) + N(I′∖I)`; `hpert` = `four_tr_sub_frobSq_perturb`. -/
theorem N0star_lower_explicit
    {N0star s12 : ℕ} {N NII trGh frGh trAh frAh B : ℝ}
    (hcount : (s12 : ℝ) ≤ N0star + NII)
    (hcore : 4 * trAh - 2 * (N + NII) - frAh ≤ s12)
    (hpert : 4 * trGh - frGh - B * (4 + 2 * Real.sqrt frGh + B) ≤ 4 * trAh - frAh) :
    4 * trGh - frGh - 2 * N - 3 * NII - B * (4 + 2 * Real.sqrt frGh + B) ≤ N0star := by
  linarith

/-- **§6 proof of Thm A, the "`(H(λ₁) − O(𝓔′_T)) N`" line made explicit.**
With `cλ := 1/λ₁ + λ₁/3` (so `4 − cλ − 2 = H(λ₁)`), if `|tr Ĝ − N| ≤ R₁`
("`tr Ĝ = N + O(√X/a)`") and `‖Ĝ‖_F² ≤ cλ N + R₂` ("`‖Ĝ‖_F² ≤ (1/λ₁+λ₁/3)N(1+O(𝓔′_T))`"), then
`N₀*(T,2T) ≥ H(λ₁) N − [4R₁ + R₂ + 3N(I′∖I) + B(4 + 2√(cλ N + R₂) + B)]`. -/
theorem N0star_lower_H
    {N0star N NII trGh frGh B lam₁ R₁ R₂ : ℝ} (hB : 0 ≤ B)
    (h0 : 4 * trGh - frGh - 2 * N - 3 * NII - B * (4 + 2 * Real.sqrt frGh + B) ≤ N0star)
    (htr : |trGh - N| ≤ R₁) (hfr : frGh ≤ (1 / lam₁ + lam₁ / 3) * N + R₂) :
    Hfun lam₁ * N - (4 * R₁ + R₂ + 3 * NII
        + B * (4 + 2 * Real.sqrt ((1 / lam₁ + lam₁ / 3) * N + R₂) + B)) ≤ N0star := by
  have h1 : N - R₁ ≤ trGh := by have := (abs_le.mp htr).1; linarith
  have h2 : Real.sqrt frGh ≤ Real.sqrt ((1 / lam₁ + lam₁ / 3) * N + R₂) := Real.sqrt_le_sqrt hfr
  have h3 : Hfun lam₁ * N = 4 * N - (1 / lam₁ + lam₁ / 3) * N - 2 * N := by simp only [Hfun]; ring
  nlinarith [h0, h1, h2, h3, hB, mul_le_mul_of_nonneg_left h2 hB]

end FixedT

/-! ## Part D.  Unit conversion `Ĝ ↔ G̃` and the trace inputs
(paper §6, proof of Thm A, first lines: "In the units (eq:hatunits), `tr Ĝ = tr G̃/(aL)` and
`‖Ĝ‖_F² = tr G̃²/(aL)²`. By Proposition prop:trace, `tr Ĝ = N + O(√X/a)` … (note that the taper
constant `a` cancels). By (eq:tr2) … `‖Ĝ‖_F² ≤ … = (1/λ₁ + λ₁/3) N (1 + O(𝓔′_T))`") -/

section Units
open Complex

variable {m : Type*} [Fintype m]

lemma rtrace_smul_ofReal (c : ℝ) (M : Matrix m m ℂ) : rtrace ((c : ℂ) • M) = c * rtrace M := by
  unfold rtrace
  rw [Matrix.trace_smul, smul_eq_mul]
  simp

lemma frobSq_smul_ofReal (c : ℝ) (M : Matrix m m ℂ) :
    frobSq ((c : ℂ) • M) = c ^ 2 * frobSq M := by
  rw [frobSq_eq_sum_norm_sq, frobSq_eq_sum_norm_sq, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp [Matrix.smul_apply, mul_pow, sq_abs]

variable (P : Params) (T : ℝ)

omit [Fintype m] in
/-- `G̃ = L⁻¹ • G` with the scalar written as a real cast. -/
lemma tilde_eq (M : Matrix m m ℂ) : P.tilde T M = (((P.L T)⁻¹ : ℝ) : ℂ) • M := by
  simp [Params.tilde]

omit [Fintype m] in
/-- `Ĝ = (aL²)⁻¹ • G` with the scalar written as a real cast [eq:hatunits]. -/
lemma hat_eq (M : Matrix m m ℂ) : P.hat T M = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • M := by
  simp [Params.hat]

omit [Fintype m] in
/-- `Ĝ = (aL)⁻¹ • G̃`: hat units are tilde units divided by `aL` ([eq:hatunits] vs [eq:Gdef]). -/
lemma hat_eq_smul_tilde (M : Matrix m m ℂ) :
    P.hat T M = (((P.a T * P.L T)⁻¹ : ℝ) : ℂ) • P.tilde T M := by
  rw [hat_eq, tilde_eq, smul_smul, ← ofReal_mul]
  congr 1
  push_cast
  ring

/-- "`tr Ĝ = tr G̃ /(aL)`" (paper §6). -/
lemma rtrace_hat (M : Matrix m m ℂ) :
    rtrace (P.hat T M) = (P.a T * P.L T)⁻¹ * rtrace (P.tilde T M) := by
  rw [hat_eq_smul_tilde, rtrace_smul_ofReal]

/-- "`‖Ĝ‖_F² = tr G̃² /(aL)²`" (paper §6), with `tr G̃² = ‖G̃‖_F²`. -/
lemma frobSq_hat (M : Matrix m m ℂ) :
    frobSq (P.hat T M) = ((P.a T * P.L T)⁻¹) ^ 2 * frobSq (P.tilde T M) := by
  rw [hat_eq_smul_tilde, frobSq_smul_ofReal]

/-- The prime-side trace computed entrywise: `rtrace (G̃ᵖʳⁱᵐᵉ) = P.trGtilde T`
(Defs: `trGtilde := L⁻¹ Σ_k G_{kk}`). -/
lemma rtrace_tilde_Gp : rtrace (P.tilde T (P.Gp T)) = P.trGtilde T := by
  rw [tilde_eq, rtrace_smul_ofReal]
  simp [Params.trGtilde, rtrace, Matrix.trace, Params.Gp]

/-- The prime-side Frobenius norm computed entrywise: `frobSq (G̃ᵖʳⁱᵐᵉ) = P.trGtildeSq T`
(Defs: `trGtildeSq := (L⁻¹)² Σ_{k,l} G_{kl}²`). -/
lemma frobSq_tilde_Gp : frobSq (P.tilde T (P.Gp T)) = P.trGtildeSq T := by
  rw [tilde_eq, frobSq_smul_ofReal, frobSq_eq_sum_norm_sq]
  simp [Params.trGtildeSq, Params.Gp, sq_abs]

end Units

section TraceInputs

/-- **"`tr Ĝ = N + O(√X/a)` (note that the taper constant `a` cancels)"** (paper §6 / prop:trace).
From [eq:tr1] first form `|tr G̃ − a L N| ≤ C·L·√X`:
`|tr G̃/(aL) − N| ≤ C √X / a` — the main term is exactly `N`, independent of `a`. -/
theorem trGhat_sub_N_le {a L N trGt C sqX : ℝ} (ha : 0 < a) (hL : 0 < L)
    (h : |trGt - a * L * N| ≤ C * (L * sqX)) :
    |(a * L)⁻¹ * trGt - N| ≤ C * sqX / a := by
  have haL : 0 < a * L := mul_pos ha hL
  have e : (a * L)⁻¹ * trGt - N = (a * L)⁻¹ * (trGt - a * L * N) := by field_simp
  rw [e, abs_mul, abs_of_pos (inv_pos.2 haL), ← div_eq_inv_mul, div_le_iff₀ haL]
  calc |trGt - a * L * N| ≤ C * (L * sqX) := h
    _ = C * sqX / a * (a * L) := by field_simp

/-- The algebra behind "`‖Ĝ‖_F² ≤ (T/(2πLa²))(ℓ₁² + L²/3)(1+O(𝓔′)) = … = (1/λ₁ + λ₁/3) N (1+O(𝓔′))`":
`(aL)⁻² · (TL/2π)(ℓ₁² + L²/3) = a⁻² · (1/λ₁ + λ₁/3) · (Tℓ₁/2π)` exactly, where `λ₁ = L/ℓ₁`. -/
lemma mainTr2_hat_identity {a L T ℓ₁ : ℝ} (ha : a ≠ 0) (hL : L ≠ 0) (hℓ₁ : ℓ₁ ≠ 0) :
    ((a * L)⁻¹) ^ 2 * (T * L / (2 * Real.pi) * (ℓ₁ ^ 2 + L ^ 2 / 3))
      = (a ^ 2)⁻¹ * (1 / (L / ℓ₁) + (L / ℓ₁) / 3) * (T * ℓ₁ / (2 * Real.pi)) := by
  field_simp

/-- **"`‖Ĝ‖_F² ≤ (1/λ₁ + λ₁/3) N (1 + O(𝓔′_T))`" made explicit.**  From [eq:tr2] (second form,
upper half) `tr G̃² ≤ (1 + C𝓔)(TL/2π)(ℓ₁² + L²/3)` and Riemann–von Mangoldt in the form
`Tℓ₁/2π ≤ N + R_N` [eq:RvM], with `K := (1 + C𝓔)/a²` and `cλ := 1/λ₁ + λ₁/3`:
`‖Ĝ‖_F² = tr G̃²/(aL)² ≤ cλ N + cλ((K − 1) N + K R_N)`.  (The second summand is the explicit `R₂`.) -/
theorem frobGhat_le {a L T ℓ₁ trG2 C calE N RN : ℝ} (ha : 0 < a) (hL : 0 < L) (hℓ₁ : 0 < ℓ₁)
    (hK : 0 ≤ 1 + C * calE)
    (htr2 : trG2 - T * L / (2 * Real.pi) * (ℓ₁ ^ 2 + L ^ 2 / 3)
              ≤ C * calE * (T * L / (2 * Real.pi) * (ℓ₁ ^ 2 + L ^ 2 / 3)))
    (hRvM : T * ℓ₁ / (2 * Real.pi) ≤ N + RN) :
    ((a * L)⁻¹) ^ 2 * trG2
      ≤ (1 / (L / ℓ₁) + (L / ℓ₁) / 3) * N
        + (1 / (L / ℓ₁) + (L / ℓ₁) / 3) * (((1 + C * calE) / a ^ 2 - 1) * N
            + (1 + C * calE) / a ^ 2 * RN) := by
  set M := T * L / (2 * Real.pi) * (ℓ₁ ^ 2 + L ^ 2 / 3) with hM
  set cl := 1 / (L / ℓ₁) + (L / ℓ₁) / 3 with hcl
  have hcl0 : 0 ≤ cl := by rw [hcl]; positivity
  have h1 : trG2 ≤ (1 + C * calE) * M := by linarith
  have h2 : ((a * L)⁻¹) ^ 2 * trG2 ≤ ((a * L)⁻¹) ^ 2 * ((1 + C * calE) * M) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have h3 : ((a * L)⁻¹) ^ 2 * ((1 + C * calE) * M)
      = (1 + C * calE) / a ^ 2 * cl * (T * ℓ₁ / (2 * Real.pi)) := by
    have := mainTr2_hat_identity (T := T) ha.ne' hL.ne' hℓ₁.ne'
    rw [← hM, ← hcl] at this
    calc ((a * L)⁻¹) ^ 2 * ((1 + C * calE) * M) = (1 + C * calE) * (((a * L)⁻¹) ^ 2 * M) := by ring
      _ = (1 + C * calE) * ((a ^ 2)⁻¹ * cl * (T * ℓ₁ / (2 * Real.pi))) := by rw [this]
      _ = _ := by ring
  have hKa : 0 ≤ (1 + C * calE) / a ^ 2 := by positivity
  have h4 : (1 + C * calE) / a ^ 2 * cl * (T * ℓ₁ / (2 * Real.pi))
      ≤ (1 + C * calE) / a ^ 2 * cl * (N + RN) :=
    mul_le_mul_of_nonneg_left hRvM (mul_nonneg hKa hcl0)
  calc ((a * L)⁻¹) ^ 2 * trG2 ≤ (1 + C * calE) / a ^ 2 * cl * (N + RN) := by linarith
    _ = cl * N + cl * (((1 + C * calE) / a ^ 2 - 1) * N + (1 + C * calE) / a ^ 2 * RN) := by ring

end TraceInputs

/-! ## Part E.  The asymptotic wrappers (the only place filters appear)

E1: the explicit error of Parts C–D is `o(N)` given the growth facts;  E2: `o(N)` error ⇒ `ε`-form;
E3: `λ → 1⁻`;  E4: dyadic summation `N₀*(T,2T) ⇒ N₀*(T)` (paper §6, end of proof of Thm A). -/

section Asymptotic
open Filter Asymptotics Topology

/-- E2. An `o(N)` error term yields the `ε`-form. -/
theorem eps_form_of_isLittleO {H₀ : ℝ} {N lower err : ℝ → ℝ}
    (hmain : ∀ᶠ T in atTop, H₀ * N T - err T ≤ lower T)
    (hN : ∀ᶠ T in atTop, 0 ≤ N T) (herr : err =o[atTop] N) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (H₀ - ε) * N T ≤ lower T := by
  intro ε hε
  have h := (herr.def hε).and (hmain.and hN)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hT₀ T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3] at h1
  have : err T ≤ ε * N T := (le_abs_self _).trans h1
  linarith

/-- E1. The explicit error term of `N0star_lower_H` is `o(N)`, given:
`N → ∞`; `R₁, R₂, N(I′∖I) = o(N)`; `B → 0`; `cλ = 1/λ₁ + λ₁/3` eventually in `[0, K]`. -/
theorem err_isLittleO {N R₁ R₂ NII B cl : ℝ → ℝ} {K : ℝ}
    (hN : Tendsto N atTop atTop)
    (hR₁ : R₁ =o[atTop] N) (hR₂ : R₂ =o[atTop] N) (hNII : NII =o[atTop] N)
    (hB : Tendsto B atTop (𝓝 0))
    (hcl : ∀ᶠ T in atTop, 0 ≤ cl T ∧ cl T ≤ K) :
    (fun T => 4 * R₁ T + R₂ T + 3 * NII T
        + B T * (4 + 2 * Real.sqrt (cl T * N T + R₂ T) + B T)) =o[atTop] N := by
  have hB1 : B =o[atTop] (fun _ => (1:ℝ)) := (isLittleO_one_iff ℝ).2 hB
  -- the bracket is O(N)
  have hbr : (fun T => 4 + 2 * Real.sqrt (cl T * N T + R₂ T) + B T) =O[atTop] N := by
    have hK : 0 ≤ K := by
      obtain ⟨T, hT⟩ := hcl.exists; exact hT.1.trans hT.2
    refine IsBigO.of_bound (7 + 2 * K) ?_
    have hN1 : ∀ᶠ T in atTop, 1 ≤ N T := hN.eventually_ge_atTop 1
    have hR₂1 : ∀ᶠ T in atTop, ‖R₂ T‖ ≤ 1 * ‖N T‖ := hR₂.def one_pos
    have hBb : ∀ᶠ T in atTop, ‖B T‖ ≤ 1 * ‖(1:ℝ)‖ := hB1.def one_pos
    filter_upwards [hN1, hR₂1, hBb, hcl] with T h1 h2 h3 h4
    have hN0 : 0 ≤ N T := by linarith
    simp only [Real.norm_eq_abs, abs_of_nonneg hN0, one_mul] at h2
    simp only [norm_one, mul_one, Real.norm_eq_abs] at h3
    have hin : cl T * N T + R₂ T ≤ ((K + 1) * N T) ^ 2 := by
      have : R₂ T ≤ N T := (le_abs_self _).trans h2
      have hclN : cl T * N T ≤ K * N T := mul_le_mul_of_nonneg_right h4.2 hN0
      have hKN : 1 ≤ (K + 1) * N T := by nlinarith
      calc cl T * N T + R₂ T ≤ (K + 1) * N T := by linarith
        _ ≤ (K + 1) * N T * ((K + 1) * N T) :=
          le_mul_of_one_le_right (mul_nonneg (by linarith) hN0) hKN
        _ = ((K + 1) * N T) ^ 2 := by ring
    have hs : Real.sqrt (cl T * N T + R₂ T) ≤ (K + 1) * N T :=
      Real.sqrt_le_iff.mpr ⟨by positivity, hin⟩
    simp only [Real.norm_eq_abs, abs_of_nonneg hN0]
    refine (abs_le.mpr ⟨?_, ?_⟩)
    · nlinarith [Real.sqrt_nonneg (cl T * N T + R₂ T), abs_le.mp h3]
    · nlinarith [abs_le.mp h3]
  have hlast : (fun T => B T * (4 + 2 * Real.sqrt (cl T * N T + R₂ T) + B T)) =o[atTop] N := by
    simpa using hB1.mul_isBigO hbr
  exact (((hR₁.const_mul_left 4).add hR₂).add (hNII.const_mul_left 3)).add hlast

/-- **sup over λ ∈ [1/2, 1)** (the common `λ → 1⁻` step): if the `ε`-form holds with constant `c(λ)`
for every `λ ∈ [1/2, 1)` and `C − η ≤ c(λ)` for some such `λ`, for every `η > 0`, then it holds with constant `C`. -/
theorem eps_form_sup_half {c : ℝ → ℝ} {C : ℝ}
    (hc : ∀ η > (0:ℝ), ∃ lam : ℝ, 1 / 2 ≤ lam ∧ lam < 1 ∧ C - η ≤ c lam)
    {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c lam - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (C - ε) * N T ≤ lower T := by
  intro ε hε
  obtain ⟨lam, h0, h1, h2⟩ := hc (ε / 2) (by linarith)
  obtain ⟨T₀, hT₀⟩ := h lam h0 h1 (ε / 2) (by linarith)
  exact ⟨T₀, fun T hT => le_trans (mul_le_mul_of_nonneg_right (by linarith) (hN T)) (hT₀ T hT)⟩

/-- a point of `[1/2, 1)` within `δ` of `1`. -/
lemma exists_lam_near_one {δ : ℝ} (hδ : 0 < δ) : ∃ lam : ℝ, 1 / 2 ≤ lam ∧ lam < 1 ∧ 1 - lam ≤ δ :=
  ⟨max (1 / 2) (1 - δ), le_max_left _ _, max_lt (by norm_num) (by linarith),
    by have := le_max_right (1 / 2) (1 - δ); linarith⟩

/-- E3. The `λ → 1⁻` step: if for every `λ ∈ [1/2, 1)` the `ε`-form holds with
constant `H(λ)`, then it holds with constant `2/3 = sup_{λ<1} H(λ)`. -/
theorem eps_form_twoThirds {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (Hfun lam - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2 / 3 - ε) * N T ≤ lower T :=
  eps_form_sup_half (fun η hη => by
    obtain ⟨lam, h1, h2, h3⟩ := exists_lam_near_one (show 0 < 3 * η / 5 by linarith)
    exact ⟨lam, h1, h2, by linarith [Hfun_ge_near_one lam h1 h2.le]⟩) hN h

/-- Same for `F`: constant `3/4 = sup_{λ<1} F(λ)` (Thm C), given the `ε`-forms with `F(λ)`. -/
theorem eps_form_threeQuarters {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (Ffun lam - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (3 / 4 - ε) * N T ≤ lower T :=
  eps_form_sup_half (fun η hη => by
    obtain ⟨lam, h1, h2, h3⟩ := exists_lam_near_one hη
    exact ⟨lam, h1, h2, by linarith [Ffun_ge_near_one lam (by linarith) h2.le]⟩) hN h

/-- Same for `2F − 1`: constant `1/2 = sup_{λ<1} (2F(λ) − 1)` (Thm B). -/
theorem eps_form_half {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2 * Ffun lam - 1 - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (1 / 2 - ε) * N T ≤ lower T :=
  eps_form_sup_half (c := fun lam => 2 * Ffun lam - 1) (fun η hη => by
    obtain ⟨lam, h1, h2, h3⟩ := exists_lam_near_one (half_pos hη)
    exact ⟨lam, h1, h2, by linarith [Ffun_ge_near_one lam (by linarith) h2.le]⟩) hN h

/-- E4. **Dyadic summation** (the paper §6, end of the proof of Thm A: "the statement for
`N₀*(T)/N(T)` by summing over dyadic intervals: given `ε>0` choose `T₁` with
`N₀*(t,2t) ≥ (2/3−ε)N(t,2t)` for `t ≥ T₁`; for `T ≥ 2T₁` and `J` maximal with `T2^{−J} ≥ T₁`,
`N₀*(T) ≥ Σ_{j=1}^{J} N₀*(T2^{−j},T2^{−j+1}) ≥ (2/3−ε)(N(T)−N(T2^{−J})) ≥ (2/3−ε)N(T) − O_ε(1)`.")
Abstract form: `f, g` interval-additive and nonnegative, `g(0,T) → ∞`. -/
theorem dyadic {f g : ℝ → ℝ → ℝ} {c : ℝ}
    (hf_add : ∀ a b c : ℝ, a ≤ b → b ≤ c → f a c = f a b + f b c)
    (hg_add : ∀ a b c : ℝ, a ≤ b → b ≤ c → g a c = g a b + g b c)
    (hf_nn : ∀ a b, 0 ≤ f a b) (hg_nn : ∀ a b, 0 ≤ g a b)
    (hg_top : Tendsto (fun T => g 0 T) atTop atTop)
    (h : ∀ ε > 0, ∃ T₁, ∀ t ≥ T₁, (c - ε) * g t (2 * t) ≤ f t (2 * t)) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c - ε) * g 0 T ≤ f 0 T := by
  intro ε hε
  by_cases hc : c - ε / 2 < 0
  · refine ⟨0, fun T _ => ?_⟩
    have := hg_nn 0 T; have := hf_nn 0 T
    nlinarith
  have hc : 0 ≤ c - ε / 2 := not_lt.mp hc
  obtain ⟨T₁', hT₁'⟩ := h (ε / 2) (by linarith)
  -- WLOG T₁ ≥ 1
  set T₁ := max T₁' 1 with hT₁def
  have hT₁ : ∀ t ≥ T₁, (c - ε / 2) * g t (2 * t) ≤ f t (2 * t) :=
    fun t ht => hT₁' t ((le_max_left _ _).trans ht)
  have hT₁pos : 0 < T₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- g is monotone in the second argument
  have hg_mono : ∀ a b b', a ≤ b → b ≤ b' → g a b ≤ g a b' := by
    intro a b b' hab hbb'; rw [hg_add a b b' hab hbb']; linarith [hg_nn b b']
  -- induction: f(t, 2^n t) ≥ (c − ε/2) g(t, 2^n t) for t ≥ T₁
  have key : ∀ n : ℕ, ∀ t ≥ T₁, (c - ε / 2) * g t (2 ^ n * t) ≤ f t (2 ^ n * t) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have hf0 : f t t = 0 := by have := hf_add t t t le_rfl le_rfl; linarith
      have hg0 : g t t = 0 := by have := hg_add t t t le_rfl le_rfl; linarith
      simp [hf0, hg0]
    | succ n ih =>
      intro t ht
      have ht0 : 0 ≤ t := hT₁pos.le.trans ht
      have h2n : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hmid : t ≤ 2 ^ n * t := by nlinarith
      have hmid' : 2 ^ n * t ≤ 2 ^ (n + 1) * t := by rw [pow_succ]; nlinarith
      rw [hf_add t (2 ^ n * t) (2 ^ (n + 1) * t) hmid hmid',
        hg_add t (2 ^ n * t) (2 ^ (n + 1) * t) hmid hmid']
      have hstep := hT₁ (2 ^ n * t) (ht.trans hmid)
      have e : 2 * (2 ^ n * t) = 2 ^ (n + 1) * t := by rw [pow_succ]; ring
      rw [e] at hstep
      have := ih t ht
      linarith
  -- choose T₀ so that (ε/2) g(0,T) ≥ (c − ε/2) g(0, 2T₁) for T ≥ T₀, and T₀ ≥ T₁
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp
    (hg_top.eventually_ge_atTop ((c - ε / 2) * g 0 (2 * T₁) * (2 / ε)))
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 ≤ T := hT₁pos.le.trans hTT₁
  -- find n with 2^n T₁ ≤ T < 2^(n+1) T₁
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := T / T₁)
    ((one_le_div hT₁pos).2 hTT₁) one_lt_two
  set t := T / 2 ^ n with htdef
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  have htT₁ : T₁ ≤ t := by
    rw [htdef, le_div_iff₀ h2n]; rw [le_div_iff₀ hT₁pos] at hn1; linarith
  have ht2T₁ : t ≤ 2 * T₁ := by
    rw [htdef, div_le_iff₀ h2n]; rw [div_lt_iff₀ hT₁pos, pow_succ] at hn2; linarith
  have hTt : 2 ^ n * t = T := by rw [htdef]; field_simp
  have ht0 : 0 ≤ t := hT₁pos.le.trans htT₁
  have htT : t ≤ T := by rw [← hTt]; nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := n) (by norm_num)]
  have hk := key n t htT₁
  rw [hTt] at hk
  -- f(0,T) ≥ f(t,T) ≥ (c−ε/2) g(t,T) = (c−ε/2)(g(0,T) − g(0,t)) ≥ (c−ε/2) g(0,T) − (c−ε/2) g(0,2T₁)
  have hf0T : f t T ≤ f 0 T := by rw [hf_add 0 t T ht0 htT]; linarith [hf_nn 0 t]
  have hgsplit : g t T = g 0 T - g 0 t := by rw [hg_add 0 t T ht0 htT]; ring
  have hg0t : g 0 t ≤ g 0 (2 * T₁) := hg_mono 0 t (2 * T₁) ht0 ht2T₁
  have hbig : (c - ε / 2) * g 0 (2 * T₁) * (2 / ε) ≤ g 0 T := hT₂ T ((le_max_right _ _).trans hT)
  have hbig' : (c - ε / 2) * g 0 (2 * T₁) ≤ ε / 2 * g 0 T := by
    have := mul_le_mul_of_nonneg_left hbig (by linarith : 0 ≤ ε / 2)
    calc (c - ε / 2) * g 0 (2 * T₁) = ε / 2 * ((c - ε / 2) * g 0 (2 * T₁) * (2 / ε)) := by
          field_simp
      _ ≤ ε / 2 * g 0 T := this
  calc (c - ε) * g 0 T = (c - ε / 2) * g 0 T - ε / 2 * g 0 T := by ring
    _ ≤ (c - ε / 2) * g 0 T - (c - ε / 2) * g 0 (2 * T₁) := by linarith
    _ ≤ (c - ε / 2) * (g 0 T - g 0 t) := by nlinarith
    _ = (c - ε / 2) * g t T := by rw [hgsplit]
    _ ≤ f t T := hk
    _ ≤ f 0 T := hf0T

end Asymptotic

/-! ## Part F.  Instantiation with the concrete objects of `Defs.lean`

F2: growth lemmas for the explicit functions `l, L, X` and for `N(T,2T)` under H-RvM;
F3: `thmA_abstract` — Theorem A at fixed `λ < 1` for an abstract `ZeroConfig`, from the named inputs. -/

section Growth
open Filter Asymptotics Topology Real

/-- `l(T) = log(T/2π) → ∞`. -/
lemma tendsto_l_atTop : Tendsto l atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))

lemma eventually_l_pos : ∀ᶠ T in atTop, 0 < l T := tendsto_l_atTop.eventually_gt_atTop 0

lemma eventually_one_le_l : ∀ᶠ T in atTop, 1 ≤ l T := tendsto_l_atTop.eventually_ge_atTop 1

/-- `L = λ l → ∞` for `λ > 0`. -/
lemma tendsto_L_atTop (P : Params) (hlam : 0 < P.lam) : Tendsto P.L atTop atTop :=
  tendsto_l_atTop.const_mul_atTop hlam

/-- `log T = l T + log 2π` for `T > 0`. -/
lemma log_eq_l_add {T : ℝ} (hT : 0 < T) : Real.log T = l T + Real.log (2 * π) := by
  rw [l, Real.log_div hT.ne' (by positivity)]; ring

/-- `log T ≤ 2 l T` eventually. -/
lemma eventually_log_le_two_l : ∀ᶠ T in atTop, Real.log T ≤ 2 * l T := by
  filter_upwards [tendsto_l_atTop.eventually_ge_atTop (Real.log (2 * π)), eventually_gt_atTop 0]
    with T h1 h2
  rw [log_eq_l_add h2]; linarith

lemma eventually_log_nonneg : ∀ᶠ T in atTop, 0 ≤ Real.log T :=
  Real.tendsto_log_atTop.eventually_ge_atTop 0

/-- `T l(T) → ∞`. -/
lemma tendsto_Tl_atTop : Tendsto (fun T => T * l T) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ tendsto_l_atTop

/-- H-RvM ⇒ `N(T,2T) ≥ T l /(4π)` eventually.  ([eq:RvM]: `N = Tℓ₁/2π + O(log T)`, `ℓ₁ ≥ l`.) -/
lemma eventually_N_ge (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    ∀ᶠ T in atTop, T * l T / (4 * π) ≤ (Z.N T (2 * T) : ℝ) := by
  obtain ⟨C, T₀, h⟩ := hR.main
  filter_upwards [eventually_ge_atTop T₀, eventually_log_le_two_l, eventually_log_nonneg,
    eventually_l_pos, eventually_ge_atTop (16 * π * |C|), eventually_ge_atTop 0] with T hT hlog hlog0 hl hTC hT0
  have h1 := (abs_le.mp (h T hT)).1
  have hc := c₀_pos
  have hℓ : l T ≤ ell1 T := by rw [ell1_eq]; linarith
  have h2 : -(C * Real.log T) ≥ -(|C| * (2 * l T)) := by
    have : C * Real.log T ≤ |C| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
    nlinarith [abs_nonneg C]
  have h3 : T / (2 * π) * l T ≤ T / (2 * π) * ell1 T :=
    mul_le_mul_of_nonneg_left hℓ (by positivity)
  -- N ≥ T l/2π − 2|C| l ≥ T l/4π  once T ≥ 16π|C|... (T l/(4π) ≥ 2|C| l ⟸ T ≥ 8π|C|)
  have h4 : 2 * |C| * l T ≤ T * l T / (4 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [abs_nonneg C, Real.pi_pos]
  have : T / (2 * π) * l T = 2 * (T * l T / (4 * π)) := by ring
  linarith

/-- H-RvM ⇒ `N(T,2T) ≤ T l` eventually. -/
lemma eventually_N_le (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    ∀ᶠ T in atTop, (Z.N T (2 * T) : ℝ) ≤ T * l T := by
  obtain ⟨C, T₀, h⟩ := hR.main
  filter_upwards [eventually_ge_atTop T₀, eventually_log_le_two_l, eventually_log_nonneg,
    eventually_one_le_l, eventually_ge_atTop (16 * |C| + 4), eventually_ge_atTop 0]
    with T hT hlog hlog0 hl hTC hT0
  have h1 := (abs_le.mp (h T hT)).2
  have hc := c₀_lt_one
  have hℓ : ell1 T ≤ 2 * l T := by rw [ell1_eq]; linarith
  have h2 : C * Real.log T ≤ |C| * (2 * l T) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0).trans
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg C))
  have h3 : T / (2 * π) * ell1 T ≤ T / (2 * π) * (2 * l T) :=
    mul_le_mul_of_nonneg_left hℓ (by positivity)
  have hπ : T / (2 * π) * (2 * l T) = T * l T / π := by field_simp
  have h4 : T * l T / π ≤ T * l T / 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    linarith [Real.pi_gt_three]
  nlinarith [abs_nonneg C]

/-- H-RvM ⇒ `N(T,2T) → ∞`. -/
lemma tendsto_N_atTop (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop :=
  tendsto_atTop_mono' _ (eventually_N_ge Z hR) (tendsto_Tl_atTop.atTop_div_const (by positivity))

/-- `T l = O(N)` under H-RvM, so `o(T l) ⊆ o(N)`. -/
lemma isLittleO_N_of_isLittleO_Tl (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {f : ℝ → ℝ}
    (hf : f =o[atTop] fun T => T * l T) : f =o[atTop] fun T => (Z.N T (2 * T) : ℝ) := by
  refine hf.trans_isBigO (IsBigO.of_bound (4 * π) ?_)
  filter_upwards [eventually_N_ge Z hR, eventually_ge_atTop 0, eventually_l_pos] with T h hT hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  have := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 4 * π)
  calc T * l T = 4 * π * (T * l T / (4 * π)) := by field_simp
    _ ≤ 4 * π * (Z.N T (2 * T) : ℝ) := this

/-- `l = o(T l)`. -/
lemma isLittleO_l_Tl : l =o[atTop] fun T => T * l T := by
  refine (isLittleO_iff).2 fun c hc => ?_
  filter_upwards [eventually_ge_atTop c⁻¹, eventually_l_pos, eventually_gt_atTop 0] with T hT hl hT0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hl, abs_of_pos (by positivity)]
  have : 1 ≤ c * T := by
    have := mul_le_mul_of_nonneg_left hT hc.le; rwa [mul_inv_cancel₀ hc.ne'] at this
  nlinarith

/-- `log T = o(T l)`. -/
lemma isLittleO_log_Tl : Real.log =o[atTop] fun T => T * l T := by
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 2 ?_) isLittleO_l_Tl
  filter_upwards [eventually_log_le_two_l, eventually_log_nonneg, eventually_l_pos] with T h h0 hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_pos hl]; exact h

/-- `√T · l = o(T l)`. -/
lemma isLittleO_sqrt_mul_l_Tl : (fun T => Real.sqrt T * l T) =o[atTop] fun T => T * l T := by
  refine (isLittleO_iff).2 fun c hc => ?_
  filter_upwards [eventually_ge_atTop ((c⁻¹) ^ 2), eventually_l_pos, eventually_gt_atTop 0]
    with T hT hl hT0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
  have hs : c⁻¹ ≤ Real.sqrt T := by
    rw [show c⁻¹ = Real.sqrt ((c⁻¹) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hT
  have h1 : 1 ≤ c * Real.sqrt T := by
    have := mul_le_mul_of_nonneg_left hs hc.le; rwa [mul_inv_cancel₀ hc.ne'] at this
  have h2 : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  have h3 : Real.sqrt T ≤ c * T := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (Real.sqrt_nonneg T)]
  calc Real.sqrt T * l T ≤ c * T * l T := mul_le_mul_of_nonneg_right h3 hl.le
    _ = c * (T * l T) := by ring

/-- `√X = (T/2π)^{λ/2}` ("`X = e^L = (T/2π)^λ`", §1 Notation). -/
lemma sqrtX_eq (P : Params) {T : ℝ} (hT : 0 < T) :
    Real.sqrt (P.X T) = (T / (2 * π)) ^ (P.lam / 2) := by
  rw [Params.X, ← Real.exp_half, Params.L, l, Real.rpow_def_of_pos (by positivity)]
  congr 1; ring

lemma tendsto_rpow_halflam_sub_one (P : Params) (hlam1 : P.lam ≤ 1) :
    Tendsto (fun T : ℝ => T ^ (P.lam / 2 - 1)) atTop (𝓝 0) := by
  have : Tendsto (fun T : ℝ => T ^ (-(1 - P.lam / 2))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  simpa [neg_sub] using this

/-- `√X = (T/2π)^{λ/2} = o(T l)` for `λ ≤ 1` (indeed for `λ < 2`). -/
lemma isLittleO_sqrtX_Tl (P : Params) (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) :
    (fun T => Real.sqrt (P.X T)) =o[atTop] fun T => T * l T := by
  refine (isLittleO_iff).2 fun c hc => ?_
  filter_upwards [(tendsto_rpow_halflam_sub_one P hlam1).eventually (eventually_le_nhds hc),
    eventually_gt_atTop 0, eventually_one_le_l] with T hTc hT hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (by positivity), sqrtX_eq P hT]
  have h2π : T / (2 * π) ≤ T := div_le_self hT.le (by linarith [Real.pi_gt_three])
  calc (T / (2 * π)) ^ (P.lam / 2) ≤ T ^ (P.lam / 2) :=
        Real.rpow_le_rpow (by positivity) h2π (by linarith)
    _ = T * T ^ (P.lam / 2 - 1) := by
        conv_lhs => rw [show P.lam / 2 = 1 + (P.lam / 2 - 1) by ring]
        rw [Real.rpow_add hT, Real.rpow_one]
    _ ≤ T * c := mul_le_mul_of_nonneg_left hTc hT.le
    _ = c * T * 1 := by ring
    _ ≤ c * T * l T := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = c * (T * l T) := by ring

/-- `l · T^{λ/2−1} / L = T^{λ/2−1}/λ → 0` (the size of `θ₀/L`, prop:tail). -/
lemma tendsto_theta_over_L (P : Params) (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) :
    Tendsto (fun T => l T * T ^ (P.lam / 2 - 1) / P.L T) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_halflam_sub_one P hlam1
  have h2 : (fun T => l T * T ^ (P.lam / 2 - 1) / P.L T) =ᶠ[atTop]
      fun T => P.lam⁻¹ * T ^ (P.lam / 2 - 1) := by
    filter_upwards [eventually_l_pos] with T hl
    simp only [Params.L]; field_simp
  rw [tendsto_congr' h2]
  simpa using h1.const_mul P.lam⁻¹

/-- `cλ = 1/λ₁ + λ₁/3` is eventually in `[0, 2/λ + 1/3]` (since `λ/2 ≤ λ₁ ≤ λ ≤ 1` once `l ≥ c₀`). -/
lemma eventually_clam_bounds (P : Params) (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) :
    ∀ᶠ T in atTop, 0 ≤ 1 / P.lam1 T + P.lam1 T / 3 ∧ 1 / P.lam1 T + P.lam1 T / 3 ≤ 2 / P.lam + 1 / 3 := by
  filter_upwards [tendsto_l_atTop.eventually_ge_atTop 1] with T hl
  have hlpos : 0 < l T := by linarith
  have hc := c₀_pos; have hc1 := c₀_lt_one
  have hl1pos := lam1_pos P T hlam hlpos
  have hl1le := lam1_le P T hlam.le hlpos
  have hhalf : P.lam / 2 ≤ P.lam1 T := by
    rw [lam1_eq, le_div_iff₀ (by linarith)]; nlinarith
  refine ⟨by positivity, ?_⟩
  have : 1 / P.lam1 T ≤ 2 / P.lam := by
    rw [div_le_div_iff₀ hl1pos hlam]; linarith
  linarith

/-- `a → 1` from [eq:abdef] `1 − 2w/L ≤ a ≤ 1` and `L → ∞`. -/
lemma tendsto_a_one (P : Params) (hlam : 0 < P.lam)
    (ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1) :
    Tendsto P.a atTop (𝓝 1) := by
  have hlow : Tendsto (fun T => 1 - 2 * P.w / P.L T) atTop (𝓝 1) := by
    have : Tendsto (fun T => 2 * P.w / P.L T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_L_atTop P hlam)
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    (ha.mono fun T h => h.1) (ha.mono fun T h => h.2)

end Growth

/-! ### F0.  Window bookkeeping for an abstract `ZeroConfig` (interval additivity; the four
"set-level" facts of prop:zeroside-rank / prop:zeroside:
`s₁+s₂ ≤ N₀*(T,2T) + N(I′∖I)`, `s₁ ≤ N₀ˢ(T,2T) + N(I′∖I)`, `#𝒵(I′) ≤ N_d(T,2T) + N(I′∖I)`,
`N(I′) = N(T,2T) + N(I′∖I)`, where `N(I′∖I) := N(T−D₀,T) + N(2T,2T+D₀)`). -/

section Windows
open Set

variable (Z : ZeroConfig)

lemma window_union {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    Z.window a c = Z.window a b ∪ Z.window b c := by
  ext ρ
  simp only [ZeroConfig.window, mem_inter_iff, mem_setOf_eq, mem_union]
  constructor
  · rintro ⟨h, h1, h2⟩
    by_cases hb : ρ.im ≤ b
    · exact Or.inl ⟨h, h1, hb⟩
    · exact Or.inr ⟨h, lt_of_not_ge hb, h2⟩
  · rintro (⟨h, h1, h2⟩ | ⟨h, h1, h2⟩)
    · exact ⟨h, h1, h2.trans hbc⟩
    · exact ⟨h, lt_of_le_of_lt hab h1, h2⟩

lemma window_disjoint (a b c : ℝ) : Disjoint (Z.window a b) (Z.window b c) := by
  rw [Set.disjoint_left]
  rintro ρ ⟨_, _, h2⟩ ⟨_, h1, _⟩
  exact absurd h1 (not_lt.2 h2)

/-- Interval additivity of `N` (with multiplicity). -/
theorem N_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : Z.N a c = Z.N a b + Z.N b c := by
  unfold ZeroConfig.N
  rw [window_union Z hab hbc, finsum_mem_union (window_disjoint Z a b c)
    (Z.window_finite a b) (Z.window_finite b c)]

/-- Interval additivity of `N_d`. -/
theorem Nd_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : Z.Nd a c = Z.Nd a b + Z.Nd b c := by
  unfold ZeroConfig.Nd
  rw [window_union Z hab hbc, Set.ncard_union_eq (window_disjoint Z a b c)
    (Z.window_finite a b) (Z.window_finite b c)]

/-- Interval additivity of `N₀*`. -/
theorem N0star_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    Z.N0star a c = Z.N0star a b + Z.N0star b c := by
  unfold ZeroConfig.N0star
  rw [window_union Z hab hbc, Set.union_inter_distrib_right,
    Set.ncard_union_eq ((window_disjoint Z a b c).mono inter_subset_left inter_subset_left)
    ((Z.window_finite a b).subset inter_subset_left) ((Z.window_finite b c).subset inter_subset_left)]

/-- Interval additivity of `N₀ˢ`. -/
theorem N0s_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    Z.N0s a c = Z.N0s a b + Z.N0s b c := by
  unfold ZeroConfig.N0s
  rw [window_union Z hab hbc, Set.union_inter_distrib_right, Set.union_inter_distrib_right,
    Set.ncard_union_eq (((window_disjoint Z a b c).mono inter_subset_left inter_subset_left).mono
      inter_subset_left inter_subset_left)
    (((Z.window_finite a b).subset inter_subset_left).subset inter_subset_left)
    (((Z.window_finite b c).subset inter_subset_left).subset inter_subset_left)]

lemma N_self (a : ℝ) : Z.N a a = 0 := by
  have := N_add Z (le_refl a) (le_refl a); omega

lemma N0star_self (a : ℝ) : Z.N0star a a = 0 := by
  have := N0star_add Z (le_refl a) (le_refl a); omega

variable (T : ℝ)

lemma D0_nonneg : 0 ≤ D0 T := Real.sqrt_nonneg _

variable {T}

/-- "`N(I′) = N(T,2T) + N(I′∖I)`" (proof of prop:zeroside-rank). -/
theorem NIprime_eq (hT : 0 ≤ T) : Z.NIprime T = Z.N T (2 * T) + NII Z T := by
  unfold ZeroConfig.NIprime NII
  have h0 := D0_nonneg T
  rw [N_add Z (b := T) (by linarith) (by linarith), N_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  ring

/-- `𝒮₁ ∪ 𝒮₂ = 𝒵(I′) ∩ {β = 1/2}` (every zero has `m_ρ ≥ 1`), hence
"`s₁ + s₂` = number of distinct on-line zeros with ordinate in `I′`" `= N₀*(T−D₀, 2T+D₀)`. -/
theorem s1_add_s2_eq : Z.s1 T + Z.s2 T = Z.N0star (T - D0 T) (2 * T + D0 T) := by
  unfold ZeroConfig.s1 ZeroConfig.s2 ZeroConfig.N0star
  have hfin : (Z.ZIprime T ∩ ZeroConfig.onLine).Finite :=
    (Z.window_finite _ _).subset inter_subset_left
  have hdisj : Disjoint (Z.S1 T) (Z.S2 T) := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, h1⟩ ⟨_, h2⟩
    simp only [ZeroConfig.simple, mem_setOf_eq] at h1 h2
    omega
  have hunion : Z.S1 T ∪ Z.S2 T = Z.ZIprime T ∩ ZeroConfig.onLine := by
    ext ρ
    simp only [ZeroConfig.S1, ZeroConfig.S2, ZeroConfig.simple, mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · rintro ⟨h1, h2⟩
      have : 1 ≤ Z.mult ρ := Z.one_le_mult ρ (Z.window_subset_carrier _ _ h1)
      rcases this.eq_or_lt with h | h
      · exact Or.inl ⟨⟨h1, h2⟩, h.symm⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
  rw [← Set.ncard_union_eq hdisj (hfin.subset (hunion ▸ subset_union_left))
    (hfin.subset (hunion ▸ subset_union_right)), hunion]
  rfl

/-- "`s₁ + s₂ ≤ N₀*(T,2T) + N(I′∖I)`" (proof of prop:zeroside-rank). -/
theorem s1_add_s2_le (hT : 0 ≤ T) : Z.s1 T + Z.s2 T ≤ Z.N0star T (2 * T) + NII Z T := by
  rw [s1_add_s2_eq]
  have h0 := D0_nonneg T
  rw [N0star_add Z (b := T) (by linarith) (by linarith),
    N0star_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  unfold NII
  have h1 := (Z.N0star_le_Nd (T - D0 T) T).trans (Z.Nd_le_N _ _)
  have h2 := (Z.N0star_le_Nd (2 * T) (2 * T + D0 T)).trans (Z.Nd_le_N _ _)
  omega

/-- "`s₁ ≤ N₀ˢ(T,2T) + N(I′∖I)`" (proof of prop:zeroside); `s₁ = N₀ˢ` over `I′` by definition. -/
theorem s1_le (hT : 0 ≤ T) : Z.s1 T ≤ Z.N0s T (2 * T) + NII Z T := by
  have hs1 : Z.s1 T = Z.N0s (T - D0 T) (2 * T + D0 T) := rfl
  have h0 := D0_nonneg T
  rw [hs1, N0s_add Z (b := T) (by linarith) (by linarith),
    N0s_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  unfold NII
  have c1 := Z.trivial_chain (T - D0 T) T
  have c2 := Z.trivial_chain (2 * T) (2 * T + D0 T)
  have h1 : Z.N0s (T - D0 T) T ≤ Z.N (T - D0 T) T := c1.1.trans (c1.2.1.trans c1.2.2.1)
  have h2 : Z.N0s (2 * T) (2 * T + D0 T) ≤ Z.N (2 * T) (2 * T + D0 T) :=
    c2.1.trans (c2.2.1.trans c2.2.2.1)
  omega

/-- "`#𝒵(I′) ≤ N_d(T,2T) + N(I′∖I)`" (proof of prop:zeroside). -/
theorem card_ZIprime_le (hT : 0 ≤ T) : (Z.ZIprime T).ncard ≤ Z.Nd T (2 * T) + NII Z T := by
  have h : (Z.ZIprime T).ncard = Z.Nd (T - D0 T) (2 * T + D0 T) := rfl
  have h0 := D0_nonneg T
  rw [h, Nd_add Z (b := T) (by linarith) (by linarith),
    Nd_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  unfold NII
  have h1 := Z.Nd_le_N (T - D0 T) T
  have h2 := Z.Nd_le_N (2 * T) (2 * T + D0 T)
  omega

end Windows

/-! ### F1.  Fixed-`T` assembly with the concrete matrices `Ĝ = P.hat T (Z.Gz P T)` etc.

The inputs from prop:block (ZeroSide.lean) and prop:tail (Tail.lean) are packaged as the two
Prop-structures below, whose fields are exactly the statements those files announce; they are
discharged in those files' instantiation sections. -/

section FixedTConcrete

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

-- `BlockInputs`, `TailInputs`, `NII` live in `Zeta23/Assembly/Inputs.lean` (shared with ZeroSide/Tail).

variable {Z P T}

lemma hat_add {m : Type*} (M N : Matrix m m ℂ) : P.hat T (M + N) = P.hat T M + P.hat T N := by
  simp [Params.hat, smul_add]

/-- **Seam A — [eq:zeroside-rank], explicit, for the concrete matrices.**  For `T ≥ 0`, with
`Ĝ := P.hat T (Z.Gz P T)`, `B₀ := θ₀/(aL)`, `N(I′∖I) = NII Z T`:
`4 tr Ĝ − ‖Ĝ‖_F² − 2N(T,2T) − 3N(I′∖I) − B₀(4 + 2‖Ĝ‖_F + B₀) ≤ N₀*(T,2T)`. -/
theorem seamA (hT : 0 ≤ T) (hB : BlockInputs Z P T) {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀)
    (ha : 0 < P.a T) (hL : 0 < P.L T) :
    4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T) * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ Z.N0star T (2 * T) := by
  obtain ⟨Pm, Qm, p, hPm, hQm, hdec, hrank, htrP, hpos, hcount⟩ := hB.hat
  obtain ⟨B, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  -- Ĝ = Â + Ê
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := zeroside_rank_core hdec hPm hQm hrank hpos htrP hcount
  have hpert := four_tr_sub_frobSq_perturb hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hcount' : ((Z.s1 T + Z.s2 T : ℕ) : ℝ) ≤ (Z.N0star T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_add_s2_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  exact N0star_lower_explicit hcount' hcore hpert

/-- **Seam A for Theorems B, C — [eq:zeroside2], for the concrete matrices.**  For `T ≥ 0` and
`θ ≥ θ₀`: `2 n₊^θ(G̃) − N(T,2T) − 2N(I′∖I) ≤ N₀ˢ(T,2T)` and `n₊^θ(G̃) − N(I′∖I) ≤ N_d(T,2T)`. -/
theorem seamA_BC (hT : 0 ≤ T) (hB : BlockInputs Z P T) {θ₀ θ : ℝ} (hTl : TailInputs Z P T θ₀)
    (hθ : θ₀ ≤ θ) (hGt : (P.tilde T (Z.Gz P T)).IsHermitian) :
    2 * (posIndexAbove hGt θ : ℝ) - (Z.N T (2 * T) : ℝ) - 2 * (NII Z T : ℝ) ≤ Z.N0s T (2 * T) ∧
      (posIndexAbove hGt θ : ℝ) - (NII Z T : ℝ) ≤ Z.Nd T (2 * T) := by
  obtain ⟨p, hAt, hpos, hrank, hcount⟩ := hB.tilde
  obtain ⟨hEt, heig⟩ := hTl.tilde
  have hGAE : P.tilde T (Z.Gz P T) = P.tilde T (Z.Az P T) + P.tilde T (Z.Ez P T) := by
    simp [Params.tilde, ← smul_add, ZeroConfig.Ez]
  have heig' : ∀ i, |hEt.eigenvalues i| ≤ θ := fun i => (heig i).trans hθ
  have h := zeroside_core hAt hEt heig' hpos hrank hcount
  rw [← posIndexAbove_congr hGt (hAt.add hEt) hGAE θ] at h
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  have hs1 : (Z.s1 T : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by exact_mod_cast s1_le Z hT
  have hcard : ((Z.ZIprime T).ncard : ℝ) ≤ (Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast card_ZIprime_le Z hT
  have h2 : (posIndexAbove hGt θ : ℝ) ≤ ((Z.ZIprime T).ncard : ℝ) := by exact_mod_cast h.2
  constructor <;> linarith [h.1]

/-- **Seam B — the trace inputs in hat units, for the concrete matrices**, given the H-EF bridge
`Z.Gz P T = P.Gp T` (zero side = prime side, [eq:Gdef] "the two expressions agreeing by
Proposition prop:EF"), [eq:tr1]/[eq:tr2] at height `T` with constants `C₁, C₂`, and [eq:RvM] at `T`
in the form `Tℓ₁/2π ≤ N + R_N`:
`|tr Ĝ − N| ≤ C₁√X/a` (the taper constant cancels in the main term) and
`‖Ĝ‖_F² ≤ cλ N + cλ((K−1)N + K R_N)`, `K = (1 + C₂𝓔_T)/a²`, `cλ = 1/λ₁ + λ₁/3`. -/
theorem seamB (hGzGp : Z.Gz P T = P.Gp T) (ha : 0 < P.a T) (hL : 0 < P.L T) (hℓ₁ : 0 < ell1 T)
    {C₁ C₂ ET RN : ℝ}
    (htr1 : |P.trGtilde T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)| ≤ C₁ * (P.L T * Real.sqrt (P.X T)))
    (hK : 0 ≤ 1 + C₂ * ET)
    (htr2 : P.trGtildeSq T - P.mainTr2 T ≤ C₂ * ET * P.mainTr2 T)
    (hRvM : T * ell1 T / (2 * Real.pi) ≤ (Z.N T (2 * T) : ℝ) + RN) :
    |rtrace (P.hat T (Z.Gz P T)) - (Z.N T (2 * T) : ℝ)| ≤ C₁ * Real.sqrt (P.X T) / P.a T ∧
    frobSq (P.hat T (Z.Gz P T)) ≤ (1 / P.lam1 T + P.lam1 T / 3) * (Z.N T (2 * T) : ℝ)
      + (1 / P.lam1 T + P.lam1 T / 3) * (((1 + C₂ * ET) / P.a T ^ 2 - 1) * (Z.N T (2 * T) : ℝ)
          + (1 + C₂ * ET) / P.a T ^ 2 * RN) := by
  rw [hGzGp, rtrace_hat, frobSq_hat, rtrace_tilde_Gp, frobSq_tilde_Gp]
  refine ⟨trGhat_sub_N_le ha hL htr1, ?_⟩
  have := frobGhat_le (T := T) (trG2 := P.trGtildeSq T) (N := (Z.N T (2 * T) : ℝ)) ha hL hℓ₁ hK
    (by simpa [Params.mainTr2] using htr2) hRvM
  simpa [Params.lam1] using this

end FixedTConcrete

/-! ### F3.  Theorem A at fixed `λ < 1` for an abstract zero configuration

The theorems are proved over an abstract error function `Err` (only: eventually nonnegative and
`→ 0`) in place of the concrete `Params.calE` — the `_err` versions below — so that alternative
prime-side chains (e.g. an MV-free one with an enlarged error) plug in directly; the
`calE` statements are kept as specializations. -/

section Main
open Filter Asymptotics Topology

-- `TracesBoundsE` (abstract error rate) and `TracesBounds.toE` live in Zeta23/TracesBoundsE.lean


/-- little-o from a factor tending to zero. -/
lemma isLittleO_of_tendsto_zero_mul {f g : ℝ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    (fun T => f T * g T) =o[atTop] g := by
  simpa using ((isLittleO_one_iff ℝ).2 hf).mul_isBigO (isBigO_refl g atTop)

/-- `O(1)` from an eventual absolute bound. -/
lemma isBigO_one_of_abs_le {f : ℝ → ℝ} {C : ℝ} (h : ∀ᶠ T in atTop, |f T| ≤ C) :
    f =O[atTop] (fun _ => (1:ℝ)) :=
  IsBigO.of_bound C (by simpa using h)

/-- `O(1) · o(N) = o(N)`. -/
lemma isLittleO_of_bdd_mul {f g N : ℝ → ℝ} (hf : f =O[atTop] (fun _ => (1:ℝ)))
    (hg : g =o[atTop] N) : (fun T => f T * g T) =o[atTop] N := by
  simpa using hf.mul_isLittleO hg

/-- **Theorem A at fixed `λ ∈ (0,1)`, for an abstract zero configuration** ([thm:A] with
§6's proof, in `ε`-form):
for every `ε > 0`, `N₀*(T,2T) ≥ (H(λ) − ε) N(T,2T)` for all `T ≥ T₀`.

Genuine hypotheses: the published inputs `H : PaperInputs Z` (only H-RvM is used directly here;
the others enter through the inputs below) and the thm:traces package
`hTr : ThmTracesHyp P Z`.
Named inputs:
`hBlock` (prop:block, ZeroSide), `hTail`/`hθ₀` (prop:tail, Tail), `hNII` (boundary count
`N(I′∖I) ≪ D₀ l`, Tail), `hGzGp` (the H-EF bridge `G^{zero} = G^{prime}`, [eq:Gdef]), `ha` ([eq:abdef],
Taper), `hcalE` (`𝓔_T → 0`, PrimeSideB). -/
theorem thmA_abstract_err (Z : ZeroConfig) (hRvM : RiemannVonMangoldt Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) (Err : ℝ → ℝ)
    (hTr : TracesBoundsE P Err P.a P.trGtilde P.trGtildeSq (fun T => (Z.N T (2 * T) : ℝ)))
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z P T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = P.Gp T)
    (ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1)
    (hcalE : Tendsto Err atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Hfun P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0star T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, htr2⟩ := hTr.tr2
  obtain ⟨CN, T₃, hRvMmain⟩ := hRvM.main
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  -- the functions of T (abbreviations)
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cl : ℝ → ℝ := fun T => 1 / P.lam1 T + P.lam1 T / 3 with hcl
  set K : ℝ → ℝ := fun T => (1 + C₂ * Err T) / P.a T ^ 2 with hK
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / P.a T with hR₁
  set R₂ : ℝ → ℝ := fun T => cl T * ((K T - 1) * N T + K T * (|CN| * Real.log T)) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (P.a T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cl T * N T + R₂ T) + B T)) + 1 / (P.lam * l T) * N T with herr
  -- basic limits
  have hLtop := tendsto_L_atTop P hlam0
  have ha1 := tendsto_a_one P hlam0 ha
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ P.a T := by
    filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hw := hP.one_le_w
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]
  have hcE0 : Tendsto (fun T => C₂ * Err T) atTop (𝓝 0) := by
    simpa using hcalE.const_mul C₂
  have hKto : Tendsto K atTop (𝓝 1) := by
    have h1 : Tendsto (fun T => 1 + C₂ * Err T) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hcE0
    have h2 : Tendsto (fun T => P.a T ^ 2) atTop (𝓝 1) := by simpa using ha1.pow 2
    simpa [hK, Pi.div_def] using h1.div h2 one_ne_zero
  -- (1) the main inequality, eventually in T
  have hmain : ∀ᶠ T in atTop, Hfun P.lam * N T - err T ≤ (Z.N0star T (2 * T) : ℝ) := by
    filter_upwards [hBlock, hTail, hGzGp, hapos, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop T₃, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_log_nonneg, hcE0.eventually (eventually_gt_nhds (show (-1:ℝ) < 0 by norm_num))]
      with T hB hTl hGG ha2 hT₁ hT₂ hT₃ hT0 hl hlog hcE
    have hapos' : 0 < P.a T := by linarith
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hℓ₁ := ell1_pos hl
    have hKnn : 0 ≤ 1 + C₂ * Err T := by linarith
    have hA := seamA hT0 hB hTl hapos' hLpos
    have htr2' : P.trGtildeSq T - P.mainTr2 T ≤ C₂ * Err T * P.mainTr2 T := by
      have := htr2 T hT₂
      simp only at this
      rw [← mul_assoc] at this
      exact (le_abs_self _).trans this
    have htr1' : |P.trGtilde T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)|
        ≤ C₁ * (P.L T * Real.sqrt (P.X T)) := by
      have := htr1 T hT₁; simpa only using this
    have hRvM' : T * ell1 T / (2 * Real.pi) ≤ N T + |CN| * Real.log T := by
      have h1 := (abs_le.mp (hRvMmain T hT₃)).1
      have h2 : CN * Real.log T ≤ |CN| * Real.log T :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlog
      have h3 : T / (2 * Real.pi) * ell1 T = T * ell1 T / (2 * Real.pi) := by ring
      simp only [hNdef]; linarith
    have hSB := seamB hGG hapos' hLpos hℓ₁ htr1' hKnn htr2' hRvM'
    -- combine with N0star_lower_H and H(λ₁) ≥ H(λ) − 1/(λ l)
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := N0star_lower_H hB₀ hA hSB.1 hSB.2
    have hH := Hfun_lam1_ge P T hlam0 hl
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hHN : (Hfun P.lam - 1 / (P.lam * l T)) * N T ≤ Hfun (P.lam1 T) * N T :=
      mul_le_mul_of_nonneg_right hH hN0
    simp only [herr, hR₁, hR₂, hBdef, hcl, hK, hNdef] at h hHN ⊢
    linarith
  -- (2) err = o(N)
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z hRvM
  -- R₁ = o(N)
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / P.a T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [hapos] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith))]
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z hRvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  -- R₂ = o(N)
  have o2 : R₂ =o[atTop] N := by
    have hclO : cl =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 / P.lam + 1 / 3) ?_
      filter_upwards [eventually_clam_bounds P hlam0 hlam1] with T h
      rw [abs_of_nonneg h.1]; exact h.2
    have hK1 : Tendsto (fun T => K T - 1) atTop (𝓝 0) := by simpa using hKto.sub_const 1
    have hKO : K =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2) ?_
      filter_upwards [hKto.eventually (eventually_ge_nhds (show (0:ℝ) < 1 by norm_num)),
        hKto.eventually (eventually_le_nhds (show (1:ℝ) < 2 by norm_num))] with T h1 h2
      rw [abs_of_nonneg h1]; exact h2
    have i1 : (fun T => (K T - 1) * N T) =o[atTop] N := isLittleO_of_tendsto_zero_mul hK1
    have i2 : (fun T => K T * (|CN| * Real.log T)) =o[atTop] N :=
      isLittleO_of_bdd_mul hKO ((isLittleO_N_of_isLittleO_Tl Z hRvM isLittleO_log_Tl).const_mul_left _)
    exact isLittleO_of_bdd_mul hclO (i1.add i2)
  -- N(I′∖I) = o(N)
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z hRvM isLittleO_sqrt_mul_l_Tl)
  -- B → 0
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
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (P.a T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr
  -- the bracket and the 1/(λ l) term
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B) (cl := cl)
    hNtop o1 o2 o3 o4 (eventually_clam_bounds P hlam0 hlam1)
  have o6 : (fun T => 1 / (P.lam * l T) * N T) =o[atTop] N :=
    isLittleO_of_tendsto_zero_mul (tendsto_const_nhds.div_atTop (tendsto_l_atTop.const_mul_atTop hlam0))
  have herr_o : err =o[atTop] N := o5.add o6
  -- (3) conclude
  exact eps_form_of_isLittleO hmain (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o

/-- **Theorem A at fixed `λ ∈ (0,1)`, abstract zero configuration** — the `Err := P.calE`
specialization of `thmA_abstract_err`. -/
theorem thmA_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) (hTr : ThmTracesHyp P Z)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z P T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = P.Gp T)
    (ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Hfun P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0star T (2 * T) :=
  thmA_abstract_err Z H.RvM P hP hlam P.calE hTr.toE hBlock θ₀ hTail hθ₀ hNII hGzGp ha hcalE

end Main

/-! ### F4.  Theorems B and C at fixed `λ < 1` for an abstract zero configuration
(the paper §6, proofs of thm:B and thm:C: [eq:nplus-lower] + [eq:zeroside2]) -/

section MainBC
open Filter Asymptotics Topology

variable {m : Type*} [Fintype m]

omit [Fintype m] in
/-- A real-scalar multiple of a Hermitian matrix is Hermitian. -/
lemma isHermitian_ofReal_smul {M : Matrix m m ℂ} (hM : M.IsHermitian) (c : ℝ) :
    ((c : ℂ) • M).IsHermitian := by
  unfold Matrix.IsHermitian at *
  rw [Matrix.conjTranspose_smul, hM]
  simp

/-- The prime-side matrix `G^{prime}_{kl} = ∫ φ̂(τ−τ_k)φ̂(τ−τ_l)ν_X(τ)dτ` is real symmetric, hence Hermitian
(paper [eq:Gdef]: "The second expression shows that `G` is real symmetric"). -/
lemma Gp_isHermitian (P : Params) (T : ℝ) : (P.Gp T).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro k l
  simp only [Params.Gp, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inj, Params.Gentry]
  congr 1; ext τ; ring

omit [Fintype m] in
lemma isHermitian_tilde (P : Params) (T : ℝ) {M : Matrix m m ℂ} (hM : M.IsHermitian) :
    (P.tilde T M).IsHermitian := by
  rw [tilde_eq]; exact isHermitian_ofReal_smul hM _

lemma card_fin_d (P : Params) (T : ℝ) : (Fintype.card (Fin (P.d T)) : ℝ) = P.d T := by simp

lemma d_le (P : Params) {T : ℝ} (h : 0 ≤ P.L T * T / (2 * Real.pi)) :
    (P.d T : ℝ) ≤ P.L T * T / (2 * Real.pi) := Nat.floor_le h

/-- `𝓔_T ≥ 0` eventually (all three summands are nonnegative once `L > 0`, `l ≥ 1`, `T > 0`). -/
lemma eventually_calE_nonneg (P : Params) (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, 0 ≤ P.calE T := by
  filter_upwards [eventually_one_le_l, eventually_gt_atTop (0:ℝ)] with T hl hT
  have hL : 0 < P.L T := by simp only [Params.L]; nlinarith
  have hlog : 0 ≤ Real.log (l T) := Real.log_nonneg hl
  have hX : 0 < P.X T := Real.exp_pos _
  simp only [Params.calE]
  positivity

/-- `0 ≤ F(x) ≤ 1` for `0 ≤ x ≤ 1` (indeed `F(x) ≤ x`). -/
lemma Ffun_bounds {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ Ffun x ∧ Ffun x ≤ 1 := by
  simp only [Ffun]
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]; nlinarith

/-- The algebra of [eq:nplus-lower]: with `Q := (tr G̃)²/tr G̃²` and `x := θ₀ d / tr G̃`,
"`n₊^{θ₀}(G̃) ≥ (tr G̃ − θ₀ d)²/tr G̃² = Q (1 − x)²`" `≥ Q − 2xQ`; combined with [eq:ratio]
`|Q − F(λ₁)N| ≤ C𝓔F(λ₁)N` this gives `n₊^{θ₀}(G̃) ≥ F(λ₁)N − [C𝓔F(λ₁)N + 2x(1+C𝓔)F(λ₁)N]`. -/
theorem nplus_ge_explicit {nplus trG trG2 θd FN CE : ℝ}
    (hCS : (trG - θd) ^ 2 / trG2 ≤ nplus) (htr : 0 < trG) (hθd : 0 ≤ θd) (htrG2 : 0 ≤ trG2)
    (hratio : |trG ^ 2 / trG2 - FN| ≤ CE * FN) :
    FN - (CE * FN + 2 * (θd / trG) * ((1 + CE) * FN)) ≤ nplus := by
  set Q := trG ^ 2 / trG2 with hQ
  set x := θd / trG with hx
  have hx0 : 0 ≤ x := div_nonneg hθd htr.le
  have h1 : Q - 2 * x * Q ≤ (trG - θd) ^ 2 / trG2 := by
    have e : Q - 2 * x * Q = (trG ^ 2 - 2 * θd * trG) / trG2 := by
      simp only [hQ, hx]; field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ htrG2
    nlinarith [sq_nonneg θd]
  have hQlo : FN - CE * FN ≤ Q := by have := (abs_le.mp hratio).1; linarith
  have hQhi : Q ≤ (1 + CE) * FN := by have := (abs_le.mp hratio).2; linarith
  have : 2 * x * Q ≤ 2 * x * ((1 + CE) * FN) := mul_le_mul_of_nonneg_left hQhi (by positivity)
  linarith

/-- **Theorems B and C at fixed `λ ∈ (0,1)`, for an abstract zero configuration — common core.**
There is `R = o(N)` with, eventually in `T`:  `(2F(λ) − 1)N − 2R ≤ N₀ˢ(T,2T)` and
`F(λ)N − R ≤ N_d(T,2T)`  (paper §6, proofs of thm:B, thm:C: prop:tail `θ₀ ≪ lT^{λ/2−1}`, prop:trace
`tr G̃ ≫ dl` hence `tr G̃ > θ₀d`, lem:CS + [eq:ratio] ⇒ [eq:nplus-lower], then [eq:zeroside2] and
`F(λ₁) ≥ F(λ) − 1/l`).  Same displayed inputs as `thmA_abstract` (without `ha`). -/
theorem thmBC_core_err (Z : ZeroConfig) (hRvM : RiemannVonMangoldt Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) (Err : ℝ → ℝ)
    (hTr : TracesBoundsE P Err P.a P.trGtilde P.trGtildeSq (fun T => (Z.N T (2 * T) : ℝ)))
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z P T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = P.Gp T)
    (hErr0 : ∀ᶠ T in atTop, 0 ≤ Err T)
    (hcalE : Tendsto Err atTop (𝓝 0)) :
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
  set x : ℝ → ℝ := fun T => θ₀ T * (P.d T : ℝ) / P.trGtilde T with hxdef
  set R : ℝ → ℝ := fun T => (C₃ * Err T * (Ffun (P.lam1 T) * N T)
      + 2 * x T * ((1 + C₃ * Err T) * (Ffun (P.lam1 T) * N T)))
      + (NII Z T : ℝ) + 1 / l T * N T with hRdef
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z hRvM
  have hcE0 : Tendsto (fun T => C₃ * Err T) atTop (𝓝 0) := by simpa using hcalE.const_mul C₃
  have hcE4 : Tendsto (fun T => C₄ * Err T) atTop (𝓝 0) := by simpa using hcalE.const_mul C₄
  -- Step 0: eventually tr G̃ ≥ L N / 2 > 0 and x ≤ 8(|Cθ|+1) T^{λ/2−1} (so θ₀ d < tr G̃ and x → 0).
  have hx : ∀ᶠ T in atTop, 0 < P.trGtilde T ∧ 0 ≤ x T ∧
      x T ≤ 4 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) ∧ θ₀ T * (P.d T : ℝ) < P.trGtilde T := by
    filter_upwards [hTail, hθ, eventually_ge_atTop T₄, eventually_N_ge Z hRvM, eventually_l_pos,
      eventually_gt_atTop (0:ℝ), hcE4.eventually (eventually_lt_nhds (show (0:ℝ) < 1/2 by norm_num)),
      (tendsto_rpow_halflam_sub_one P hlam1).eventually
        (eventually_lt_nhds (show (0:ℝ) < 1 / (8 * (|Cθ| + 1)) by positivity))]
      with T hTl hθT hT₄ hNge hl hT0 hcE hTs
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have h1 := (abs_le.mp (by simpa only using htr1' T hT₄)).1
    have hLN : 0 < P.L T * N T := by
      have : 0 < T * l T / (4 * Real.pi) := by positivity
      exact mul_pos hLpos (this.trans_le hNge)
    have htrG : P.L T * N T / 2 ≤ P.trGtilde T := by
      have : C₄ * Err T * (P.L T * N T) ≤ 1 / 2 * (P.L T * N T) :=
        mul_le_mul_of_nonneg_right hcE.le hLN.le
      simp only [hNdef] at this h1 ⊢; linarith
    have htrGpos : 0 < P.trGtilde T := lt_of_lt_of_le (by positivity) htrG
    have hd : (P.d T : ℝ) ≤ P.L T * T / (2 * Real.pi) := d_le P (by positivity)
    have hθ' : θ₀ T ≤ (|Cθ| + 1) * l T * T ^ (P.lam / 2 - 1) := by
      refine hθT.trans ?_
      have : Cθ ≤ |Cθ| + 1 := by linarith [le_abs_self Cθ]
      gcongr
    have hθ0 := hTl.theta_nonneg
    -- θ₀ d ≤ (|Cθ|+1) l T^s · L T/(2π)  and  tr G̃ ≥ L N/2 ≥ L T l/(8π)
    have hnum : θ₀ T * (P.d T : ℝ) ≤ ((|Cθ| + 1) * l T * T ^ (P.lam / 2 - 1)) * (P.L T * T / (2 * Real.pi)) :=
      mul_le_mul hθ' hd (Nat.cast_nonneg _) (hθ0.trans hθ')
    have hden : P.L T * (T * l T / (4 * Real.pi)) / 2 ≤ P.trGtilde T :=
      le_trans (by gcongr) htrG
    have hxle : x T ≤ 4 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) := by
      simp only [hxdef]
      rw [div_le_iff₀ htrGpos]
      calc θ₀ T * (P.d T : ℝ) ≤ ((|Cθ| + 1) * l T * T ^ (P.lam / 2 - 1)) * (P.L T * T / (2 * Real.pi)) := hnum
        _ = 4 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) * (P.L T * (T * l T / (4 * Real.pi)) / 2) := by ring
        _ ≤ 4 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) * P.trGtilde T := by gcongr
    refine ⟨htrGpos, div_nonneg (mul_nonneg hθ0 (Nat.cast_nonneg _)) htrGpos.le, hxle, ?_⟩
    have hx1 : x T < 1 := by
      refine hxle.trans_lt ?_
      have := (lt_div_iff₀ (show (0:ℝ) < 8 * (|Cθ| + 1) by positivity)).mp hTs
      nlinarith [abs_nonneg Cθ, Real.rpow_nonneg hT0.le (P.lam / 2 - 1)]
    simp only [hxdef] at hx1
    rwa [div_lt_one htrGpos] at hx1
  refine ⟨R, ?_, ?_⟩
  -- R = o(N)
  · have hFN : (fun T => Ffun (P.lam1 T) * N T) =O[atTop] N := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_l_pos] with T hl
      have hb := Ffun_bounds (lam1_pos P T hlam0 hl).le ((lam1_le P T hlam0.le hl).trans hlam1)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb.1, one_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hb.2
    have o1 : (fun T => C₃ * Err T * (Ffun (P.lam1 T) * N T)) =o[atTop] N := by
      have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO hFN
      simpa using this
    have hxto : Tendsto x atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using (tendsto_rpow_halflam_sub_one P hlam1).const_mul (4 * (|Cθ| + 1)))
        (hx.mono fun T h => h.2.1) (hx.mono fun T h => h.2.2.1)
    have o2 : (fun T => 2 * x T * ((1 + C₃ * Err T) * (Ffun (P.lam1 T) * N T))) =o[atTop] N := by
      have h2x : Tendsto (fun T => 2 * x T) atTop (𝓝 0) := by simpa using hxto.const_mul 2
      have hK : (fun T => 1 + C₃ * Err T) =O[atTop] (fun _ => (1:ℝ)) := by
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
      exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z hRvM isLittleO_sqrt_mul_l_Tl)
    have o4 : (fun T => 1 / l T * N T) =o[atTop] N :=
      isLittleO_of_tendsto_zero_mul (tendsto_const_nhds.div_atTop tendsto_l_atTop)
    exact ((o1.add o2).add o3).add o4
  -- the inequalities, eventually
  · filter_upwards [hBlock, hTail, hGzGp, hx, eventually_ge_atTop T₃, eventually_ge_atTop (0:ℝ),
      eventually_l_pos, hErr0]
      with T hB hTl hGG hxT hT₃ hT0 hl hE0
    have hGt : (P.tilde T (Z.Gz P T)).IsHermitian := by
      rw [hGG]; exact isHermitian_tilde P T (Gp_isHermitian P T)
    -- [eq:zeroside2]
    have hZ := seamA_BC hT0 hB hTl le_rfl hGt
    -- lem:CS, [eq:nplus-lower]
    have hθ0 := hTl.theta_nonneg
    have hrt : rtrace (P.tilde T (Z.Gz P T)) = P.trGtilde T := by rw [hGG, rtrace_tilde_Gp]
    have hfr : frobSq (P.tilde T (Z.Gz P T)) = P.trGtildeSq T := by rw [hGG, frobSq_tilde_Gp]
    have htr' : θ₀ T * (Fintype.card (Fin (P.d T)) : ℝ) < rtrace (P.tilde T (Z.Gz P T)) := by
      rw [card_fin_d, hrt]; exact hxT.2.2.2
    have hCS := nplus_lower hGt hθ0 htr'
    rw [card_fin_d, hrt, hfr] at hCS
    have hratio' : |P.trGtilde T ^ 2 / P.trGtildeSq T - Ffun (P.lam1 T) * N T|
        ≤ C₃ * Err T * (Ffun (P.lam1 T) * N T) := by
      have := hratio T hT₃; simp only at this; rw [← mul_assoc] at this; exact this
    have htrG2 : 0 ≤ P.trGtildeSq T := by rw [← hfr]; exact frobSq_nonneg _
    have hnp := nplus_ge_explicit hCS hxT.1 (mul_nonneg hθ0 (Nat.cast_nonneg _)) htrG2 hratio'
    -- F(λ₁) ≥ F(λ) − 1/l
    have hF := Ffun_lam1_ge P T hlam0 hlam1 hl
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hFN : (Ffun P.lam - 1 / l T) * N T ≤ Ffun (P.lam1 T) * N T :=
      mul_le_mul_of_nonneg_right hF hN0
    simp only [hRdef, hxdef, hNdef] at hnp hFN hZ ⊢
    constructor <;> nlinarith [hZ.1, hZ.2, hnp, hFN]

/-- `thmBC_core`, the concrete-rate wrapper: `Err := P.calE`
(the `Err`-parametric generalization is `thmBC_core_err` above). -/
theorem thmBC_core (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) (hTr : ThmTracesHyp P Z)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z P T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = P.Gp T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∃ R : ℝ → ℝ, R =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) ∧
      ∀ᶠ T in atTop,
        (2 * Ffun P.lam - 1) * (Z.N T (2 * T) : ℝ) - 2 * R T ≤ Z.N0s T (2 * T) ∧
        Ffun P.lam * (Z.N T (2 * T) : ℝ) - R T ≤ Z.Nd T (2 * T) :=
  thmBC_core_err Z H.RvM P hP hlam P.calE hTr.toE hBlock θ₀ hTail hθ₀ hNII hGzGp
    (eventually_calE_nonneg P hP.lam_pos (zero_le_one.trans hP.one_le_w)) hcalE

/-- **Theorem B at fixed `λ ∈ (0,1)`, abstract zero configuration** (the paper [thm:B], `ε`-form):
`N₀ˢ(T,2T) ≥ (2F(λ) − 1 − ε) N(T,2T)` for `T ≥ T₀`. -/
theorem thmB_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) (hTr : ThmTracesHyp P Z)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z P T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = P.Gp T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * Ffun P.lam - 1 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
  obtain ⟨R, hR, hev⟩ := thmBC_core Z H P hP hlam hTr hBlock θ₀ hTail hθ₀ hNII hGzGp hcalE
  refine eps_form_of_isLittleO (err := fun T => 2 * R T) (hev.mono fun T h => ?_)
    (Eventually.of_forall fun T => Nat.cast_nonneg _) (hR.const_mul_left 2)
  linarith [h.1]

/-- **Theorem C at fixed `λ ∈ (0,1)`, abstract zero configuration** (the paper [thm:C], `ε`-form):
`N_d(T,2T) ≥ (F(λ) − ε) N(T,2T)` for `T ≥ T₀`. -/
theorem thmC_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) (hTr : ThmTracesHyp P Z)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z P T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = P.Gp T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Ffun P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nd T (2 * T) := by
  obtain ⟨R, hR, hev⟩ := thmBC_core Z H P hP hlam hTr hBlock θ₀ hTail hθ₀ hNII hGzGp hcalE
  exact eps_form_of_isLittleO (err := R) (hev.mono fun T h => h.2)
    (Eventually.of_forall fun T => Nat.cast_nonneg _) hR

end MainBC

/-! ### F5.  `𝓔_T → 0` (paper [thm:traces]: "`𝓔_T ≪_λ w/L + T^{λ−1} log l` (λ<1), `≪ w/L + log l/l` (λ=1)") -/

section CalE
open Filter Topology Real

/-- `X = (T/2π)^λ ≤ T` once `T ≥ 2π` (for `λ ≤ 1`). -/
lemma X_le_T (P : Params) (hlam1 : P.lam ≤ 1) {T : ℝ} (hT : 2 * π ≤ T) : P.X T ≤ T := by
  have hπ : 0 < 2 * π := by positivity
  have hb : 1 ≤ T / (2 * π) := by rwa [le_div_iff₀ hπ, one_mul]
  have hX : P.X T = (T / (2 * π)) ^ P.lam := by
    rw [Params.X, Params.L, l, Real.rpow_def_of_pos (by positivity)]; ring_nf
  rw [hX]
  calc (T / (2 * π)) ^ P.lam ≤ (T / (2 * π)) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hb hlam1
    _ = T / (2 * π) := Real.rpow_one _
    _ ≤ T := div_le_self (by linarith) (by linarith [Real.pi_gt_three])

/-- **`𝓔_T → 0`** as `T → ∞`, for fixed `0 < λ ≤ 1` and fixed `w ≥ 0`
(`𝓔_T := w/L + (l²+X) log l/(Tl) + T^{λ/2−1}`, [thm:traces]).  Bound used:
`𝓔_T ≤ w/L + (log T)²/T + log l/l + T^{λ/2−1}` for `T ≥ 2π`, `l ≥ 1`. -/
theorem calE_tendsto_zero (P : Params) (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) (hw : 0 ≤ P.w) :
    Tendsto P.calE atTop (𝓝 0) := by
  have h1 : Tendsto (fun T => P.w / P.L T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_L_atTop P hlam)
  have h2 : Tendsto (fun T : ℝ => Real.log T ^ 2 / T) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    simpa using this
  have h3 : Tendsto (fun T => Real.log (l T) / l T) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact this.comp tendsto_l_atTop
  have h4 := tendsto_rpow_halflam_sub_one P hlam1
  have hsum : Tendsto (fun T => P.w / P.L T + (Real.log T ^ 2 / T + Real.log (l T) / l T)
      + T ^ (P.lam / 2 - 1)) atTop (𝓝 0) := by
    simpa using (h1.add (h2.add h3)).add h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (eventually_calE_nonneg P hlam hw) ?_
  filter_upwards [eventually_one_le_l, eventually_ge_atTop (2 * π)] with T hl hT2π
  have hT : 0 < T := lt_of_lt_of_le (by positivity) hT2π
  have hlpos : 0 < l T := by linarith
  have hlogl : 0 ≤ Real.log (l T) := Real.log_nonneg hl
  have hlogl' : Real.log (l T) ≤ l T := by linarith [Real.log_le_sub_one_of_pos hlpos]
  have hllog : l T ≤ Real.log T := by
    rw [log_eq_l_add hT]
    have : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hX := X_le_T P hlam1 hT2π
  have hXpos : 0 ≤ P.X T := (Real.exp_pos _).le
  -- the middle term
  have hmid : (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T)
      ≤ Real.log T ^ 2 / T + Real.log (l T) / l T := by
    have e : (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T)
        = l T * Real.log (l T) / T + P.X T * Real.log (l T) / (T * l T) := by
      field_simp
    rw [e]
    gcongr ?_ + ?_
    · -- l log l / T ≤ (log T)²/T
      apply div_le_div_of_nonneg_right _ hT.le
      calc l T * Real.log (l T) ≤ l T * l T := mul_le_mul_of_nonneg_left hlogl' hlpos.le
        _ ≤ Real.log T * Real.log T := mul_le_mul hllog hllog hlpos.le (hlpos.le.trans hllog)
        _ = Real.log T ^ 2 := by ring
    · -- X log l /(T l) ≤ log l / l
      rw [div_le_div_iff₀ (by positivity) hlpos]
      calc P.X T * Real.log (l T) * l T ≤ T * Real.log (l T) * l T := by gcongr
        _ = Real.log (l T) * (T * l T) := by ring
  simp only [Params.calE]
  linarith

end CalE

end Assembly
end Zeta23

end
