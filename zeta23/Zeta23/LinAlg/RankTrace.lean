/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/
import Zeta23.LinAlg.PosIndex
import Zeta23.LinAlg.VonNeumann
import Zeta23.LinAlg.HermitianPosPart

/-!
# The rank–trace inequality (paper §3, `lem:ranktrace`)

Let `P, Q` be Hermitian `d × d` matrices with `P ⪰ 0`, `rank P ≤ r`, and
`n₊(Q) ≤ b`. Then for every `c > 0`,

  `‖P+Q‖_F² ≥ c · tr P − (c²/4) · r + 2c · tr Q − c² · b`.

## Proof structure (the paper's proof of [lem:ranktrace], §3)

Decompose `Q = Q₊ − Q₋` (spectral positive/negative parts). Expand
`‖P+Q‖_F² = ‖P‖_F² + 2 tr(PQ₊) − 2 tr(PQ₋) + ‖Q₊‖_F² + ‖Q₋‖_F²` (using
`Q₊Q₋ = 0`). Drop `tr(PQ₊) ≥ 0`. By von Neumann,
`‖P‖_F² − 2 tr(PQ₋) + ‖Q₋‖_F² ≥ ∑(pᵢ−nᵢ)²`. The two elementary estimates
`sum_sq_diff_lower` and `sum_sq_lower_of_card_pos_le` bound the remaining
pieces, and `linarith` assembles.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Elementary real-sequence estimates -/

section Elementary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Elementary scalar inequality `x² ≥ c·x − c²/4`, i.e. `(x − c/2)² ≥ 0`. -/
lemma sq_ge_linear (x c : ℝ) : c * x - c ^ 2 / 4 ≤ x ^ 2 := by
  nlinarith [sq_nonneg (x - c / 2)]

/-- Elementary scalar inequality `x² ≥ 2c·x − c²`, i.e. `(x − c)² ≥ 0`. -/
lemma sq_ge_linear' (x c : ℝ) : 2 * c * x - c ^ 2 ≤ x ^ 2 := by
  nlinarith [sq_nonneg (x - c)]

/-- **Sum estimate A** (first elementary estimate in the proof of [lem:ranktrace]). For `p, m ≥ 0` with at most `r`
indices where `p` is nonzero, and `c ≥ 0`:
`∑(pᵢ − mᵢ)² ≥ c·∑pᵢ − (c²/4)·r − 2c·∑mᵢ`. -/
lemma sum_sq_diff_lower {p m : ι → ℝ} (hm : ∀ i, 0 ≤ m i)
    {r : ℕ} (hr : #{i | p i ≠ 0} ≤ r) {c : ℝ} (hc : 0 ≤ c) :
    c * (∑ i, p i) - c ^ 2 / 4 * r - 2 * c * (∑ i, m i) ≤ ∑ i, (p i - m i) ^ 2 := by
  classical
  set s : Finset ι := {i | p i ≠ 0} with hs_def
  -- Pointwise: `(pᵢ−mᵢ)² ≥ c·pᵢ − 2c·mᵢ − (c²/4)·1_{i∈s}`.
  have hptwise : ∀ i ∈ (univ : Finset ι),
      c * p i - 2 * c * m i - (if i ∈ s then c ^ 2 / 4 else 0) ≤ (p i - m i) ^ 2 := by
    intro i _
    rcases eq_or_ne (p i) 0 with hi | hi
    · have his : i ∉ s := by simp [hs_def, mem_filter, hi]
      rw [if_neg his, hi]
      nlinarith [hm i, sq_nonneg (m i)]
    · have his : i ∈ s := by simp [hs_def, mem_filter, hi]
      rw [if_pos his]
      nlinarith [sq_ge_linear (p i - m i) c, hm i]
  have hsum := sum_le_sum hptwise
  simp only [sum_sub_distrib, ← mul_sum, sum_ite_mem, univ_inter, sum_const,
    nsmul_eq_mul] at hsum
  have hcard : (#s : ℝ) * (c ^ 2 / 4) ≤ r * (c ^ 2 / 4) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hr) (by positivity)
  linarith

/-- **Sum estimate B** (second elementary estimate in the proof of [lem:ranktrace]). For `q ≥ 0` with at most `b`
indices where `q` is nonzero: `∑qᵢ² ≥ 2c·∑qᵢ − c²·b`. -/
lemma sum_sq_lower_of_card_pos_le {q : ι → ℝ}
    {b : ℕ} (hb : #{i | q i ≠ 0} ≤ b) (c : ℝ) :
    2 * c * (∑ i, q i) - c ^ 2 * b ≤ ∑ i, (q i) ^ 2 := by
  classical
  set s : Finset ι := {i | q i ≠ 0} with hs_def
  have hptwise : ∀ i ∈ (univ : Finset ι),
      2 * c * q i - (if i ∈ s then c ^ 2 else 0) ≤ (q i) ^ 2 := by
    intro i _
    rcases eq_or_ne (q i) 0 with hi | hi
    · have his : i ∉ s := by simp [hs_def, mem_filter, hi]
      rw [if_neg his, hi]; simp
    · have his : i ∈ s := by simp [hs_def, mem_filter, hi]
      rw [if_pos his]; exact sq_ge_linear' (q i) c
  have hsum := sum_le_sum hptwise
  simp only [sum_sub_distrib, ← mul_sum, sum_ite_mem, univ_inter, sum_const,
    nsmul_eq_mul] at hsum
  have hcard : (#s : ℝ) * c ^ 2 ≤ b * c ^ 2 :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb) (sq_nonneg c)
  linarith

end Elementary

/-! ### Trace and Frobenius-norm identities -/

/-- `tr(AB) ≥ 0` when `A, B ⪰ 0`. Proof: diagonalise `A = U D Uᴴ`; then
`tr(AB) = tr((UᴴBU)D) = ∑ᵢ λᵢ · (UᴴBU)ᵢᵢ`, where each `λᵢ ≥ 0` (PSD
eigenvalues) and each `(UᴴBU)ᵢᵢ ≥ 0` (diagonal of a PSD matrix). -/
lemma trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ RCLike.re (A * B).trace := by
  -- Reduce `tr(AB)` to `tr((UᴴBU)D)` by the spectral theorem + trace cycling.
  rw [hA.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply, mul_assoc,
    trace_mul_comm, ← mul_assoc]
  set M := star (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) * B *
    (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) with hM_def
  -- `M = UᴴBU` is PSD.
  have hM : M.PosSemidef := hB.conjTranspose_mul_mul_same _
  -- Now `0 ≤ re tr(M * diag λ) = ∑ᵢ λᵢ · re Mᵢᵢ`.
  simp only [trace, diag_apply, mul_diagonal, Function.comp_apply, map_sum,
    RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, mul_zero, sub_zero]
  refine Finset.sum_nonneg fun i _ => ?_
  exact mul_nonneg (RCLike.nonneg_iff.mp hM.diag_nonneg).1 (hA.eigenvalues_nonneg i)

omit [DecidableEq n] in
/-- For Hermitian `A, B`: `Re tr(BA) = Re tr(AB)`. (In fact `tr(BA) = tr(AB)`.) -/
lemma re_trace_mul_comm (A B : Matrix n n 𝕜) :
    RCLike.re (B * A).trace = RCLike.re (A * B).trace := by
  rw [trace_mul_comm]

omit [DecidableEq n] in
/-- Frobenius-norm expansion for a sum of two Hermitian matrices. -/
lemma frobSq_add_hermitian {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    frobSq (A + B) = frobSq A + 2 * RCLike.re (A * B).trace + frobSq B := by
  unfold frobSq
  rw [(hA.add hB).eq, hA.eq, hB.eq, add_mul, mul_add, mul_add,
    trace_add, trace_add, trace_add, map_add, map_add, map_add,
    re_trace_mul_comm B A]
  ring

omit [DecidableEq n] in
lemma rtrace_add (A B : Matrix n n 𝕜) : rtrace (A + B) = rtrace A + rtrace B := by
  simp [rtrace, trace_add, map_add]

omit [DecidableEq n] in
lemma rtrace_sub (A B : Matrix n n 𝕜) : rtrace (A - B) = rtrace A - rtrace B := by
  simp [rtrace, trace_sub, map_sub]

/-! ### The main theorem -/

/-- **Rank–trace inequality** (paper `lem:ranktrace`, eq. `eq:ranktrace`).

Hypotheses: `P ⪰ 0` with `rank P ≤ r`; `Q` Hermitian with `n₊(Q) ≤ b`; `c > 0`.
Conclusion:
  `c · tr P − (c²/4) · r + 2c · tr Q − c² · b ≤ ‖P + Q‖_F²`.
-/
theorem rank_trace_ineq {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - c ^ 2 / 4 * r + 2 * c * rtrace Q - c ^ 2 * b
      ≤ frobSq (P + Q) := by
  classical
  -- Positive/negative parts of `Q`.
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  have hQmQp : Qm * Qp = 0 := hermNegPart_mul_hermPosPart hQ
  have hrkQp : Qp.rank ≤ b := by
    rw [hQp_def, rank_hermPosPart hQ]; exact hb
  -- Sorted eigenvalues on `Fin d`.
  set d := Fintype.card n
  set p : Fin d → ℝ := hP.isHermitian.eigenvalues₀
  set m : Fin d → ℝ := hQm_psd.isHermitian.eigenvalues₀
  have hp_nn : ∀ k, 0 ≤ p k := fun k => by
    rw [show p k = hP.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hP.isHermitian k).symm]
    exact hP.eigenvalues_nonneg _
  have hm_nn : ∀ k, 0 ≤ m k := fun k => by
    rw [show m k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _
  -- `#{k : pₖ ≠ 0} = rank P ≤ r`.
  have hp_card : #{k | p k ≠ 0} ≤ r := by
    calc #{k | p k ≠ 0}
        = #{i | hP.isHermitian.eigenvalues i ≠ 0} :=
          (card_eigenvalues_reindex hP.isHermitian (· ≠ 0)).symm
      _ = P.rank := by
          rw [hP.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
      _ ≤ r := hr
  -- Trace/frobSq identities reindexed to `Fin d`.
  have htraceP : rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian id
  have htraceQm : rtrace Qm = ∑ k, m k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobP : frobSq P = ∑ k, (p k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian (· ^ 2)
  have hfrobQm : frobSq Qm = ∑ k, (m k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  -- Step 1: Frobenius expansion.
  have hexpand : frobSq (P + Q)
      = frobSq P + 2 * RCLike.re (P * Qp).trace - 2 * RCLike.re (P * Qm).trace
        + frobSq Qp + frobSq Qm := by
    have h1 : frobSq (-Qm) = frobSq Qm := by
      unfold frobSq; rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by
      rw [mul_neg, hQpQm]; simp
    rw [hQdec, frobSq_add_hermitian hP.isHermitian
        (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm,
      frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  -- Step 2: drop `tr(PQ₊) ≥ 0`.
  have hPQp : 0 ≤ RCLike.re (P * Qp).trace := trace_mul_nonneg_of_posSemidef hP hQp_psd
  -- Step 3: von Neumann on `P, Q₋`.
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * m k :=
    vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  -- Step 4: the von Neumann step gives `frobSq P − 2 tr(PQ₋) + frobSq Q₋ ≥ ∑(pₖ−mₖ)²`.
  have hstep4 : ∑ k, (p k - m k) ^ 2
      ≤ frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - m k) ^ 2
        = ∑ k, (p k)^2 - 2 * ∑ k, p k * m k + ∑ k, (m k)^2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]; linarith
  -- Step 5: elementary estimate A.
  have hstep5 : c * rtrace P - c^2/4 * r - 2 * c * rtrace Qm
      ≤ ∑ k, (p k - m k) ^ 2 := by
    rw [htraceP, htraceQm]
    exact sum_sq_diff_lower hm_nn hp_card hc.le
  -- Step 6: elementary estimate B on `Q₊`.
  have hstep6 : 2 * c * rtrace Qp - c^2 * b ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ c
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0}
        = #{i | 0 < hQ.eigenvalues i} := by
          congr 1; ext i; simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  -- Step 7: combine. `rtrace Q = rtrace Qp − rtrace Qm`.
  have htraceQ : 2 * c * rtrace Q = 2 * c * rtrace Qp - 2 * c * rtrace Qm := by
    rw [hQdec, rtrace_sub]; ring
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ]

/-- **Rank–trace inequality, `c = 2` form** (paper `lem:ranktrace`,
"in particular"). Rearranged: `r ≥ 2 tr P + 4 tr Q − 4b − ‖P+Q‖_F²`. -/
theorem rank_trace_ineq_two {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * (b : ℝ) - frobSq (P + Q) ≤ (r : ℝ) := by
  have h := rank_trace_ineq hP hQ hr hb (c := 2) (by norm_num)
  linarith

end RHLinalg
