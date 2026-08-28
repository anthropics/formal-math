/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ZeroSide/RankTraceMult.lean — the multiplicity-aware rank–trace inequality ("Lemma R").
For P = Σ_j m_j v_j v_j* (m_j ≥ 0, v_j ∈ 𝕜ⁿ, x_j := ‖v_j‖²), Q Hermitian with n₊(Q) ≤ b, and c > 0:
   ‖P+Q‖_F² ≥ c·tr P + Σ_j g_c(m_j x_j) + 2c·tr Q − c²·b,     g_c(x) := x² − cx − ((x−c)₊)²
(g_c convex, C¹, g_c(0) = 0, g_c ≥ −c²/4; so with at most r nonzero terms this contains lem:ranktrace).
Proof: the paper's skeleton (Q = Q₊ − Q₋, drop tr(PQ₊) ≥ 0, von Neumann, ‖Q₊‖² ≥ 2c trQ₊ − c²b — reused verbatim from the
imported rank_trace_ineq) with the termwise scalar step (p−n)² ≥ cp + g_c(p) − 2cn, followed by tr g_c(P) ≥ Σ_j g_c(m_jx_j):
(Schur) for PSD M, Σ_j g_c(M_jj) ≤ Σ_i g_c(μ_i(M)) by Jensen along the doubly stochastic |U_ji|², and (transfer) the nonzero spectra
of WWᴴ and WᴴW agree — implemented as Σ_i g(λ_i(WWᴴ)) = Σ_j g(μ_j(WᴴW)) for g(0)=0 via traces of powers + Lagrange interpolation.
-/
import Zeta23.LinAlg
import Mathlib.LinearAlgebra.Lagrange

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.RankTraceMult

/-! ### (A) the scalar function g_c -/

/-- g_c(x) = x² − cx − ((x−c)₊)²:  = x² − cx for x ≤ c,  = cx − c² for x ≥ c. -/
def gc (c x : ℝ) : ℝ := x ^ 2 - c * x - (max (x - c) 0) ^ 2

lemma gc_of_le {c x : ℝ} (h : x ≤ c) : gc c x = x ^ 2 - c * x := by
  unfold gc; rw [max_eq_right (by linarith)]; ring

lemma gc_of_ge {c x : ℝ} (h : c ≤ x) : gc c x = c * x - c ^ 2 := by
  unfold gc; rw [max_eq_left (by linarith)]; ring

@[simp] lemma gc_zero {c : ℝ} (hc : 0 ≤ c) : gc c 0 = 0 := by
  rw [gc_of_le hc]; ring

lemma gc_ge {c x : ℝ} (hc : 0 ≤ c) : -(c ^ 2 / 4) ≤ gc c x := by
  rcases le_or_gt x c with h | h
  · rw [gc_of_le h]; nlinarith [sq_nonneg (x - c / 2)]
  · rw [gc_of_ge h.le]
    have : c * c ≤ c * x := mul_le_mul_of_nonneg_left h.le hc
    nlinarith

/-- the affine minorants: for t ∈ [0,c] and x ≥ 0, (2t − c)x − t² ≤ g_c(x). -/
lemma affine_le_gc {c t x : ℝ} (ht0 : 0 ≤ t) (htc : t ≤ c) (hx : 0 ≤ x) :
    (2 * t - c) * x - t ^ 2 ≤ gc c x := by
  rcases le_or_gt x c with h | h
  · rw [gc_of_le h]; nlinarith [sq_nonneg (x - t)]
  · rw [gc_of_ge h.le]; nlinarith [sq_nonneg (c - t)]

/-- … with equality at t = min(x, c). -/
lemma affine_eq_gc {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) :
    (2 * min x c - c) * x - (min x c) ^ 2 = gc c x := by
  rcases le_or_gt x c with h | h
  · rw [min_eq_left h, gc_of_le h]; ring
  · rw [min_eq_right h.le, gc_of_ge h.le]; ring

/-- **Jensen for g_c** via the affine representation: weights w ≥ 0 with Σw = 1, points μ ≥ 0. -/
theorem gc_sum_le {ι : Type*} (s : Finset ι) {c : ℝ} (hc : 0 ≤ c) (w μ : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    gc c (∑ i ∈ s, w i * μ i) ≤ ∑ i ∈ s, w i * gc c (μ i) := by
  set xbar := ∑ i ∈ s, w i * μ i with hx
  have hx0 : 0 ≤ xbar := Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hμ i hi)
  set t := min xbar c with ht
  have ht0 : 0 ≤ t := le_min hx0 hc
  have htc : t ≤ c := min_le_right _ _
  rw [← affine_eq_gc hc hx0]
  -- the affine function at xbar is the w-average of its values at μ_i, each ≤ g_c(μ_i)
  calc (2 * t - c) * xbar - t ^ 2 = (2 * t - c) * xbar - t ^ 2 * ∑ i ∈ s, w i := by rw [hw1, mul_one]
    _ = ∑ i ∈ s, w i * ((2 * t - c) * μ i - t ^ 2) := by
        rw [hx, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ s, w i * gc c (μ i) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (affine_le_gc ht0 htc (hμ i hi)) (hw i hi)

/-- the termwise step replacing the rank count:  (p − n)² ≥ c·p + g_c(p) − 2c·n  for p, n ≥ 0. -/
lemma sq_sub_ge_gc {c p n : ℝ} (hp : 0 ≤ p) (hn : 0 ≤ n) (hc : 0 ≤ c) :
    c * p + gc c p - 2 * c * n ≤ (p - n) ^ 2 := by
  rcases le_or_gt p c with h | h
  · rw [gc_of_le h]; nlinarith [mul_nonneg hn (sub_nonneg.mpr h)]
  · rw [gc_of_ge h.le]; nlinarith [sq_nonneg (p - n - c)]

lemma sum_sq_sub_ge_gc {ι : Type*} [Fintype ι] {p m : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, 0 ≤ m i)
    {c : ℝ} (hc : 0 ≤ c) :
    c * (∑ i, p i) + (∑ i, gc c (p i)) - 2 * c * (∑ i, m i) ≤ ∑ i, (p i - m i) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => sq_sub_ge_gc (hp i) (hm i) hc

/-! ### (B) the Schur step: the diagonal of a PSD matrix vs its spectrum, along the convex g_c -/

section Schur
open RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- diagonal entries through the spectral decomposition: re M_jj = Σ_i ‖U_ji‖²·μ_i. -/
lemma re_diag_eq_sum_normSq_eigenvalues {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (j : ι) :
    RCLike.re (M j j) = ∑ i, normSqMatrix (hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i * hM.eigenvalues i := by
  set U : Matrix ι ι 𝕜 := ↑hM.eigenvectorUnitary with hU
  have hMjj : M j j = ∑ i, U j i * (hM.eigenvalues i : 𝕜) * starRingEnd 𝕜 (U j i) := by
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_diagonal, star_apply, RCLike.star_def]
    simp only [Function.comp_apply]
    rfl
  rw [hMjj, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show U j i * (hM.eigenvalues i : 𝕜) * starRingEnd 𝕜 (U j i) = (hM.eigenvalues i : 𝕜) * (U j i * starRingEnd 𝕜 (U j i)) by ring,
    RCLike.mul_conj, show ((hM.eigenvalues i : 𝕜) * ((‖U j i‖ : 𝕜) ^ 2) : 𝕜) = ((hM.eigenvalues i * ‖U j i‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]
  simp [normSqMatrix, mul_comm]

/-- **Schur–Jensen for g_c**: Σ_j g_c(re M_jj) ≤ Σ_i g_c(μ_i(M)) for PSD M and c ≥ 0. -/
theorem sum_gc_diag_le_sum_gc_eigenvalues {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    ∑ j, gc c (RCLike.re (M j j)) ≤ ∑ i, gc c (hM.1.eigenvalues i) := by
  set S := normSqMatrix (hM.1.eigenvectorUnitary : Matrix ι ι 𝕜) with hS
  have hDS := normSqMatrix_mem_doublyStochastic_of_unitary (hM.1.eigenvectorUnitary).2
  rw [mem_doublyStochastic_iff_sum] at hDS
  obtain ⟨hnn, hrow, hcol⟩ := hDS
  have hμ : ∀ i, 0 ≤ hM.1.eigenvalues i := fun i => hM.eigenvalues_nonneg i
  calc ∑ j, gc c (RCLike.re (M j j)) = ∑ j, gc c (∑ i, S j i * hM.1.eigenvalues i) := by
        refine Finset.sum_congr rfl fun j _ => by rw [re_diag_eq_sum_normSq_eigenvalues hM.1 j]
    _ ≤ ∑ j, ∑ i, S j i * gc c (hM.1.eigenvalues i) :=
        Finset.sum_le_sum fun j _ => gc_sum_le Finset.univ hc (fun i => S j i) _
          (fun i _ => hnn j i) (hrow j) (fun i _ => hμ i)
    _ = ∑ i, (∑ j, S j i) * gc c (hM.1.eigenvalues i) := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    _ = ∑ i, gc c (hM.1.eigenvalues i) := by
        refine Finset.sum_congr rfl fun i _ => by rw [hcol i, one_mul]

end Schur

/-! ### (C) transfer of the nonzero spectrum: Σ_i g(λ_i(W Wᴴ)) = Σ_j g(μ_j(Wᴴ W)) whenever g(0) = 0 -/

section Transfer
open RHLinalg Polynomial

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A^k = specMap (·^k) for k ≥ 1, hence rtrace (A^k) = Σ λ_i^k. -/
lemma specMap_pow_succ {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    specMap hA (fun x => x ^ (k + 1)) = A ^ (k + 1) := by
  induction k with
  | zero => simp only [zero_add, pow_one]; exact specMap_id hA
  | succ k ih =>
    rw [pow_succ, ← ih, show (fun x : ℝ => x ^ (k + 1 + 1)) = (fun x : ℝ => x ^ (k + 1)) * id by
      funext x; simp [pow_succ], specMap_mul, specMap_id]

lemma rtrace_pow_succ {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    rtrace (A ^ (k + 1)) = ∑ i, hA.eigenvalues i ^ (k + 1) := by
  rw [← specMap_pow_succ hA k, rtrace_specMap]

/-- tr((W Wᴴ)^{k+1}) = tr((Wᴴ W)^{k+1}). -/
lemma trace_pow_succ_comm (W : Matrix n ι 𝕜) (k : ℕ) :
    ((W * Wᴴ) ^ (k + 1)).trace = ((Wᴴ * W) ^ (k + 1)).trace := by
  have key : ∀ k : ℕ, (W * Wᴴ) ^ (k + 1) = W * (Wᴴ * W) ^ k * Wᴴ := by
    intro k
    induction k with
    | zero => simp [Matrix.mul_assoc]
    | succ k ih => rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]
  rw [key, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-- for any real polynomial q with q(0) = 0:  Σ_i q(λ_i(WWᴴ)) = Σ_j q(μ_j(WᴴW)). -/
lemma sum_eval_eigenvalues_comm (W : Matrix n ι 𝕜) (q : ℝ[X]) (hq : q.eval 0 = 0) :
    ∑ i, q.eval ((Matrix.posSemidef_self_mul_conjTranspose W).1.eigenvalues i)
      = ∑ j, q.eval ((Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvalues j) := by
  set hP := (Matrix.posSemidef_self_mul_conjTranspose W).1
  set hM := (Matrix.posSemidef_conjTranspose_mul_self W).1
  have h0 : q.coeff 0 = 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset ι))]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rcases k with _ | k
  · simp [h0]
  · congr 1
    have h1 := rtrace_pow_succ hP k
    have h2 := rtrace_pow_succ hM k
    rw [← h1, ← h2]
    unfold rtrace
    rw [trace_pow_succ_comm]

/-- **Transfer**: for any g : ℝ → ℝ with g 0 = 0,  Σ_i g(λ_i(WWᴴ)) = Σ_j g(μ_j(WᴴW))  (interpolate g on the joint spectrum ∪ {0}). -/
theorem sum_eigenvalues_comm (W : Matrix n ι 𝕜) (g : ℝ → ℝ) (hg : g 0 = 0) :
    ∑ i, g ((Matrix.posSemidef_self_mul_conjTranspose W).1.eigenvalues i)
      = ∑ j, g ((Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvalues j) := by
  classical
  set lam := (Matrix.posSemidef_self_mul_conjTranspose W).1.eigenvalues
  set mu := (Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvalues
  set nodes : Finset ℝ := insert 0 ((Finset.univ.image lam) ∪ (Finset.univ.image mu)) with hnodes
  set q : ℝ[X] := Lagrange.interpolate nodes id g with hqdef
  have hinj : Set.InjOn (id : ℝ → ℝ) nodes := fun _ _ _ _ h => h
  have hq : ∀ x ∈ nodes, q.eval x = g x := fun x hx => by
    rw [hqdef]
    simpa only [id_eq] using Lagrange.eval_interpolate_at_node (r := g) hinj hx
  have hq0 : q.eval 0 = 0 := by rw [hq 0 (Finset.mem_insert_self _ _), hg]
  have hlam : ∀ i, lam i ∈ nodes := fun i =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hmu : ∀ j, mu j ∈ nodes := fun j =>
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  calc ∑ i, g (lam i) = ∑ i, q.eval (lam i) := Finset.sum_congr rfl fun i _ => (hq _ (hlam i)).symm
    _ = ∑ j, q.eval (mu j) := sum_eval_eigenvalues_comm W q hq0
    _ = ∑ j, g (mu j) := Finset.sum_congr rfl fun j _ => hq _ (hmu j)

end Transfer

/-! ### (D) Lemma R -/

section Main
open RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the d×s matrix with columns √m_j · v_j. -/
def Wmat (m : ι → ℝ) (v : ι → n → 𝕜) : Matrix n ι 𝕜 := fun a j => (Real.sqrt (m j) : 𝕜) * v j a

/-- P := W Wᴴ = Σ_j m_j v_j v_j*. -/
def Pmat (m : ι → ℝ) (v : ι → n → 𝕜) : Matrix n n 𝕜 := Wmat m v * (Wmat m v)ᴴ

/-- x_j := ‖v_j‖² = Σ_a ‖v_j a‖². -/
def xsq (v : ι → n → 𝕜) (j : ι) : ℝ := ∑ a, ‖v j a‖ ^ 2

lemma Pmat_apply {m : ι → ℝ} (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜) (a b : n) :
    Pmat m v a b = ∑ j, (m j : 𝕜) * (v j a * starRingEnd 𝕜 (v j b)) := by
  unfold Pmat
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply]
  simp only [Wmat]
  rw [RCLike.star_def, map_mul, RCLike.conj_ofReal]
  have : ((Real.sqrt (m j) : 𝕜)) * (Real.sqrt (m j) : 𝕜) = (m j : 𝕜) := by
    rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hm j)]
  calc (Real.sqrt (m j) : 𝕜) * v j a * ((Real.sqrt (m j) : 𝕜) * starRingEnd 𝕜 (v j b))
      = ((Real.sqrt (m j) : 𝕜) * (Real.sqrt (m j) : 𝕜)) * (v j a * starRingEnd 𝕜 (v j b)) := by ring
    _ = _ := by rw [this]

lemma Pmat_posSemidef (m : ι → ℝ) (v : ι → n → 𝕜) : (Pmat m v).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

/-- the Gram matrix M := Wᴴ W has diagonal m_j x_j. -/
lemma re_gram_diag {m : ι → ℝ} (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜) (j : ι) :
    RCLike.re (((Wmat m v)ᴴ * Wmat m v) j j) = m j * xsq v j := by
  unfold xsq
  rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_apply]
  simp only [Wmat]
  rw [RCLike.star_def, (starRingEnd 𝕜).map_mul, RCLike.conj_ofReal]
  rw [show (Real.sqrt (m j) : 𝕜) * starRingEnd 𝕜 (v j a) * ((Real.sqrt (m j) : 𝕜) * v j a)
      = ((Real.sqrt (m j) : 𝕜) * (Real.sqrt (m j) : 𝕜)) * (starRingEnd 𝕜 (v j a) * v j a) by ring,
    ← RCLike.ofReal_mul, Real.mul_self_sqrt (hm j), RCLike.conj_mul,
    show ((m j : 𝕜) * ((‖v j a‖ : 𝕜) ^ 2) : 𝕜) = ((m j * ‖v j a‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]

/-- tr P = Σ_j m_j x_j. -/
lemma rtrace_Pmat {m : ι → ℝ} (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜) :
    rtrace (Pmat m v) = ∑ j, m j * xsq v j := by
  unfold rtrace Pmat
  rw [trace_mul_comm]
  unfold Matrix.trace
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => re_gram_diag hm v j

/-- **tr g_c(P) ≥ Σ_j g_c(m_j x_j)** — Schur + transfer (this is where "per-zero integrality survives interaction"). -/
theorem sum_gc_eigenvalues_ge {m : ι → ℝ} (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜) {c : ℝ} (hc : 0 ≤ c) :
    ∑ j, gc c (m j * xsq v j) ≤ ∑ i, gc c ((Pmat_posSemidef m v).1.eigenvalues i) := by
  have hM : ((Wmat m v)ᴴ * Wmat m v).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  calc ∑ j, gc c (m j * xsq v j) = ∑ j, gc c (RCLike.re (((Wmat m v)ᴴ * Wmat m v) j j)) :=
        Finset.sum_congr rfl fun j _ => by rw [re_gram_diag hm v j]
    _ ≤ ∑ j, gc c (hM.1.eigenvalues j) := sum_gc_diag_le_sum_gc_eigenvalues hM hc
    _ = ∑ i, gc c ((Pmat_posSemidef m v).1.eigenvalues i) :=
        (sum_eigenvalues_comm (Wmat m v) (gc c) (gc_zero hc)).symm

/-- **Lemma R (multiplicity-aware rank–trace inequality).**  For P = Σ_j m_j v_jv_j* (m_j ≥ 0), Q Hermitian with n₊(Q) ≤ b,
and c > 0:   c·tr P + Σ_j g_c(m_j‖v_j‖²) + 2c·tr Q − c²·b ≤ ‖P + Q‖_F². -/
theorem rank_trace_mult {m : ι → ℝ} (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtrace (Pmat m v) + (∑ j, gc c (m j * xsq v j)) + 2 * c * rtrace Q - c ^ 2 * b
      ≤ frobSq (Pmat m v + Q) := by
  classical
  set P := Pmat m v with hPdef
  have hP : P.PosSemidef := Pmat_posSemidef m v
  -- Positive/negative parts of Q (verbatim from RHLinalg.rank_trace_ineq).
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  set d := Fintype.card n
  set p : Fin d → ℝ := hP.isHermitian.eigenvalues₀
  set mm : Fin d → ℝ := hQm_psd.isHermitian.eigenvalues₀
  have hp_nn : ∀ k, 0 ≤ p k := fun k => by
    rw [show p k = hP.isHermitian.eigenvalues (eigEquiv k) from (eigenvalues_eigEquiv hP.isHermitian k).symm]
    exact hP.eigenvalues_nonneg _
  have hm_nn : ∀ k, 0 ≤ mm k := fun k => by
    rw [show mm k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _
  have htraceP : rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]; exact sum_eigenvalues_reindex hP.isHermitian id
  have htraceQm : rtrace Qm = ∑ k, mm k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]; exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobP : frobSq P = ∑ k, (p k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hP.isHermitian]; exact sum_eigenvalues_reindex hP.isHermitian (· ^ 2)
  have hfrobQm : frobSq Qm = ∑ k, (mm k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  -- Step 1: Frobenius expansion.
  have hexpand : frobSq (P + Q)
      = frobSq P + 2 * RCLike.re (P * Qp).trace - 2 * RCLike.re (P * Qm).trace + frobSq Qp + frobSq Qm := by
    have h1 : frobSq (-Qm) = frobSq Qm := by unfold frobSq; rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by rw [mul_neg, hQpQm]; simp
    rw [hQdec, frobSq_add_hermitian hP.isHermitian (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm, frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  -- Step 2: drop tr(PQ₊) ≥ 0.
  have hPQp : 0 ≤ RCLike.re (P * Qp).trace := trace_mul_nonneg_of_posSemidef hP hQp_psd
  -- Step 3: von Neumann.
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * mm k := vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  have hstep4 : ∑ k, (p k - mm k) ^ 2 ≤ frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - mm k) ^ 2 = ∑ k, (p k)^2 - 2 * ∑ k, p k * mm k + ∑ k, (mm k)^2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]; linarith
  -- Step 5': the multiplicity-aware termwise estimate + Schur/transfer.
  have hgc_eig : ∑ j, gc c (m j * xsq v j) ≤ ∑ k, gc c (p k) := by
    calc ∑ j, gc c (m j * xsq v j) ≤ ∑ i, gc c (hP.1.eigenvalues i) := sum_gc_eigenvalues_ge hm v hc.le
      _ = ∑ k, gc c (p k) := sum_eigenvalues_reindex hP.isHermitian (gc c)
  have hstep5 : c * rtrace P + (∑ j, gc c (m j * xsq v j)) - 2 * c * rtrace Qm ≤ ∑ k, (p k - mm k) ^ 2 := by
    rw [htraceP, htraceQm]
    have := sum_sq_sub_ge_gc hp_nn hm_nn hc.le
    linarith
  -- Step 6: estimate on Q₊ (verbatim).
  have hstep6 : 2 * c * rtrace Qp - c^2 * b ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ c
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0} = #{i | 0 < hQ.eigenvalues i} := by
          congr 1; ext i; simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  have htraceQ : 2 * c * rtrace Q = 2 * c * rtrace Qp - 2 * c * rtrace Qm := by rw [hQdec, rtrace_sub]; ring
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ]

/-! ### the k_c form (leak-free target) and the integer specializations -/

/-- k_c(p) := c² − ((c−p)₊)²  (= 2cp − p² for p ≤ c, = c² for p ≥ c): nondecreasing, concave, k_c(0) = 0. -/
def kc (c p : ℝ) : ℝ := c ^ 2 - (max (c - p) 0) ^ 2

lemma kc_eq (c p : ℝ) : kc c p = c * p - gc c p := by
  unfold kc gc
  rcases le_or_gt p c with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring

lemma kc_mono {c p p' : ℝ} (hc : 0 ≤ c) (hpp : p ≤ p') : kc c p ≤ kc c p' := by
  unfold kc
  have h1 : max (c - p') 0 ≤ max (c - p) 0 := max_le_max (by linarith) le_rfl
  have h2 : 0 ≤ max (c - p') 0 := le_max_right _ _
  nlinarith [mul_le_mul h1 h1 h2 (le_trans h2 h1)]

lemma kc_of_le {c p : ℝ} (h : p ≤ c) : kc c p = 2 * c * p - p ^ 2 := by rw [kc_eq, gc_of_le h]; ring
lemma kc_of_ge {c p : ℝ} (h : c ≤ p) : kc c p = c ^ 2 := by rw [kc_eq, gc_of_ge h]; ring

/-- **Lemma R, k-form**:  2c·tr(P+Q) − ‖P+Q‖_F² ≤ Σ_j k_c(m_j‖v_j‖²) + c²·b. -/
theorem rank_trace_mult_k {m : ι → ℝ} (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    2 * c * rtrace (Pmat m v + Q) - frobSq (Pmat m v + Q) ≤ (∑ j, kc c (m j * xsq v j)) + c ^ 2 * b := by
  have h := rank_trace_mult hm v hQ hb hc
  have htr : rtrace (Pmat m v) = ∑ j, m j * xsq v j := rtrace_Pmat hm v
  have hk : ∑ j, kc c (m j * xsq v j) = c * ∑ j, m j * xsq v j - ∑ j, gc c (m j * xsq v j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => kc_eq c _
  rw [rtrace_add, hk, ← htr]
  linarith

/-- … and the **leak-free** form: with ‖v_j‖² ≤ 1 the right side only increases when x_j ↦ 1. -/
theorem rank_trace_mult_k_le {m : ι → ℝ} (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜) (hx : ∀ j, xsq v j ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    2 * c * rtrace (Pmat m v + Q) - frobSq (Pmat m v + Q) ≤ (∑ j, kc c (m j)) + c ^ 2 * b := by
  have h1 := rank_trace_mult_k hm v hQ hb hc
  have h2 : ∑ j, kc c (m j * xsq v j) ≤ ∑ j, kc c (m j) :=
    Finset.sum_le_sum fun j _ => kc_mono hc.le (by nlinarith [hm j, hx j])
  linarith

/-- integer values: k₂(0)=0, k₂(1)=3, k₂(m)=4 for m ≥ 2;  k₃(0)=0, k₃(1)=5, k₃(2)=8, k₃(m)=9 for m ≥ 3. -/
lemma kc_two_one : kc 2 1 = 3 := by rw [kc_of_le (by norm_num)]; norm_num
lemma kc_two_of_two_le {x : ℝ} (h : 2 ≤ x) : kc 2 x = 4 := by rw [kc_of_ge h]; norm_num
lemma kc_three_one : kc 3 1 = 5 := by rw [kc_of_le (by norm_num)]; norm_num
lemma kc_three_two : kc 3 2 = 8 := by rw [kc_of_le (by norm_num)]; norm_num
lemma kc_three_of_three_le {x : ℝ} (h : 3 ≤ x) : kc 3 x = 9 := by rw [kc_of_ge h]; norm_num

end Main

/-! ### integer bookkeeping for the assembly (c = 2: simple zeros; c = 3: distinct zeros) -/

section Counting
variable {ι : Type*} [Fintype ι]

/-- Σ_j k₂(m_j) = 3·#{m_j = 1} + 4·#{m_j ≥ 2} for positive integer multiplicities. -/
theorem sum_kc_two_nat [DecidableEq ι] (m : ι → ℕ) (hm : ∀ j, 1 ≤ m j) :
    ∑ j, kc 2 (m j : ℝ) = 3 * ((Finset.univ.filter (fun j => m j = 1)).card : ℝ)
      + 4 * ((Finset.univ.filter (fun j => 2 ≤ m j)).card : ℝ) := by
  classical
  have hsplit : ∀ j, kc 2 (m j : ℝ) = (if m j = 1 then 3 else 0) + (if 2 ≤ m j then 4 else 0) := by
    intro j
    rcases Nat.lt_or_ge (m j) 2 with h | h
    · have : m j = 1 := by have := hm j; omega
      simp [this, kc_two_one]
    · have hne : m j ≠ 1 := by omega
      rw [if_neg hne, if_pos h, kc_two_of_two_le (by exact_mod_cast h)]; ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite]
  simp [Finset.sum_const, mul_comm]

/-- Σ_j k₃(m_j) = 5·#{m_j = 1} + 8·#{m_j = 2} + 9·#{m_j ≥ 3}. -/
theorem sum_kc_three_nat [DecidableEq ι] (m : ι → ℕ) (hm : ∀ j, 1 ≤ m j) :
    ∑ j, kc 3 (m j : ℝ) = 5 * ((Finset.univ.filter (fun j => m j = 1)).card : ℝ)
      + 8 * ((Finset.univ.filter (fun j => m j = 2)).card : ℝ)
      + 9 * ((Finset.univ.filter (fun j => 3 ≤ m j)).card : ℝ) := by
  classical
  have hsplit : ∀ j, kc 3 (m j : ℝ)
      = (if m j = 1 then 5 else 0) + (if m j = 2 then 8 else 0) + (if 3 ≤ m j then 9 else 0) := by
    intro j
    rcases Nat.lt_or_ge (m j) 3 with h | h
    · rcases Nat.lt_or_ge (m j) 2 with h2 | h2
      · have : m j = 1 := by have := hm j; omega
        simp [this, kc_three_one]
      · have : m j = 2 := by omega
        simp [this, kc_three_two]
    · have h1 : m j ≠ 1 := by omega
      have h2 : m j ≠ 2 := by omega
      rw [if_neg h1, if_neg h2, if_pos h, kc_three_of_three_le (by exact_mod_cast h)]; ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_ite]
  simp [Finset.sum_const, mul_comm]

end Counting

end Zeta23.ZeroSide.RankTraceMult
