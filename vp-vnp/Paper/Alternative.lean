/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Curvature
import Nc.Flag.Exchange
import Nc.Flag.Cases

/-!
# The paper, section "Flat or contracting"

The definitions, then the steps of the proof of Theorem thm:alt in the order of the paper, then the theorem. The paper's
n_a(W) = |a, a+W|² is `nn w a W`, its B_a(W, W') is `BB w a W W'`, D(r)² is `meanSq w r`, and u xᵀ is `vecMulVec u x`.
-/

namespace Paper

open Finset Filter Topology Nc.Price Nc.Flag
open Matrix (vecMulVec)

variable {K : Type} [Field K] {μ : ℕ} {w : Mt μ → Mt μ → ℝ}

/-! ## Definitions -/

/-- The mean of |a, a+W|² over all matrices a and all matrices W of rank r: the square of the paper's D(r). -/
noncomputable def meanSq (w : Mt μ → Mt μ → ℝ) (r : ℕ) : ℝ :=
  (∑ a : Mt μ, ∑ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = r), w a (a + W) ^ 2) /
    ((Fintype.card (Mt μ) : ℝ) * ((univ : Finset (Mt μ)).filter (fun W => W.rank = r)).card)

/-- The paper's D(r). -/
noncomputable def distAtRank (w : Mt μ → Mt μ → ℝ) (r : ℕ) : ℝ := √(meanSq w r)

theorem distAtRank_sq (w : Mt μ → Mt μ → ℝ) (r : ℕ) : distAtRank w r ^ 2 = meanSq w r :=
  Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (by positivity))

theorem meanSq_nonneg (w : Mt μ → Mt μ → ℝ) (r : ℕ) : 0 ≤ meanSq w r :=
  div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

/-- The flat case: "all finite subsets of all Euclidean spaces, with their metrics, are prices". -/
def Flat (K : Type) [Field K] : Prop := CaseOne K

/-- The contracting case: "there are an integer μ ≥ 2 and a real s with 1 ≤ s, s² < μ, such that D(μ) ≤ sD(1) for all
prices on Mat_μ(F₂)". -/
def Contracting (K : Type) [Field K] : Prop :=
  ∃ (μ : ℕ) (s : ℝ), 2 ≤ μ ∧ 1 ≤ s ∧ s ^ 2 < μ ∧
    ∀ w : Mt μ → Mt μ → ℝ, IsPrice K w → distAtRank w μ ≤ s * distAtRank w 1

/-- **Paper: Definition def:cases.** "We are in the flat case if all finite subsets of all Euclidean spaces, with their
metrics, are prices. We are in the contracting case if there are an integer μ ≥ 2 and a real s with 1 ≤ s, s² < μ, such
that D(μ) ≤ sD(1) for all prices on Mat_μ(F₂)." Here D(r)² is "the mean of |a, a+W|² over all matrices a and all matrices
W of rank r". -/
theorem def_cases (K : Type) [Field K] :
    (Flat K ↔ ∀ (n : ℕ) (S : Finset (EuclideanSpace ℝ (Fin n))), IsPrice K fun x y : S => dist x y) ∧
    (Contracting K ↔ ∃ (μ : ℕ) (s : ℝ), 2 ≤ μ ∧ 1 ≤ s ∧ s ^ 2 < μ ∧ ∀ w : Mt μ → Mt μ → ℝ, IsPrice K w →
      √((∑ a : Mt μ, ∑ W : Mt μ with W.rank = μ, w a (a + W) ^ 2) /
          ((Fintype.card (Mt μ) : ℝ) * #{W : Mt μ | W.rank = μ})) ≤
        s * √((∑ a : Mt μ, ∑ W : Mt μ with W.rank = 1, w a (a + W) ^ 2) /
          ((Fintype.card (Mt μ) : ℝ) * #{W : Mt μ | W.rank = 1}))) := by
  classical
  refine ⟨⟨fun h n S => h n S fun x => (x : EuclideanSpace ℝ (Fin n)), fun h k V _ E => ?_⟩, Iff.rfl⟩
  have : Fintype V := Fintype.ofFinite V
  exact (h k (univ.image E)).comp fun v => (⟨E v, mem_image_of_mem E (mem_univ v)⟩ : univ.image E)

/-- "We call W₁, W₂, … transversal if both their column spaces and their row spaces are independent": this is the
definition `Nc.Flag.Transversal`, unfolded here. -/
theorem def_transversal {ι : Type} (W : ι → Mt μ) :
    Transversal W ↔ iSupIndep (fun k => Submodule.span F2 (Set.range (W k).col)) ∧
      iSupIndep fun k => Submodule.span F2 (Set.range (W k).row) := Iff.rfl

/-- Two matrices are transversal if and only if, after multiplication by invertible matrices p and q, they are diagonal
matrices with entries 0 and 1 and with disjoint supports. -/
theorem transversal_pair {W W' : Mt μ} : Transversal ![W, W'] ↔
    ∃ (p q : GLM (Fin μ)) (S T : Finset (Fin μ)), Disjoint S T ∧ W = X p q S ∧ W' = X p q T := by
  rw [transversal_iff]
  constructor
  · rintro ⟨p, q, S, hd, hW⟩
    exact ⟨p, q, S 0, S 1, hd 0 1 (by decide), hW 0, hW 1⟩
  · rintro ⟨p, q, S, T, hd, h1, h2⟩
    refine ⟨p, q, ![S, T], fun k l hkl => ?_, fun k => ?_⟩
    · fin_cases k <;> fin_cases l <;> first | exact absurd rfl hkl | exact hd | exact hd.symm
    · fin_cases k
      exacts [h1, h2]

/-- The same for three matrices. -/
theorem transversal_triple {W₁ W₂ W₃ : Mt μ} : Transversal ![W₁, W₂, W₃] ↔
    ∃ (p q : GLM (Fin μ)) (S₁ S₂ S₃ : Finset (Fin μ)), Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃ ∧
      W₁ = X p q S₁ ∧ W₂ = X p q S₂ ∧ W₃ = X p q S₃ := by
  rw [transversal_iff]
  constructor
  · rintro ⟨p, q, S, hd, hW⟩
    exact ⟨p, q, S 0, S 1, S 2, hd 0 1 (by decide), hd 0 2 (by decide), hd 1 2 (by decide), hW 0, hW 1, hW 2⟩
  · rintro ⟨p, q, S₁, S₂, S₃, h12, h13, h23, h1, h2, h3⟩
    refine ⟨p, q, ![S₁, S₂, S₃], fun k l hkl => ?_, fun k => ?_⟩
    · fin_cases k <;> fin_cases l <;>
        first | exact absurd rfl hkl | exact h12 | exact h13 | exact h23 | exact h12.symm | exact h13.symm | exact h23.symm
    · fin_cases k
      exacts [h1, h2, h3]

theorem transversal_symm {W W' : Mt μ} (h : Transversal ![W, W']) : Transversal ![W', W] := by
  obtain ⟨p, q, S, T, hd, h1, h2⟩ := transversal_pair.1 h
  exact transversal_pair.2 ⟨p, q, T, S, hd.symm, h2, h1⟩

theorem transversal_X (p q : GLM (Fin μ)) {S T : Finset (Fin μ)} (h : Disjoint S T) :
    Transversal ![X p q S, X p q T] :=
  transversal_pair.2 ⟨p, q, S, T, h, rfl, rfl⟩

theorem transversal_dg {S T : Finset (Fin μ)} (h : Disjoint S T) : Transversal ![(dg S : Mt μ), dg T] := by
  have := transversal_X 1 1 h
  rwa [X_one, X_one] at this

/-! ## Matrices of one rank -/

/-- Multiplication by invertible matrices keeps the rank. -/
theorem rank_units (p q : GLM (Fin μ)) (W : Mt μ) : ((p : Mt μ) * W * (q : Mt μ)).rank = W.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 q.isUnit),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 p.isUnit)]

theorem rank_dg (S : Finset (Fin μ)) : (dg S : Mt μ).rank = S.card := by
  rw [dg, Matrix.rank_diagonal, Fintype.card_subtype]
  congr 1
  ext i
  simp

/-- The sum of f(p·dg(S)·q)² over all invertible p and q (this is `DM f (dg S)`), divided by the number of these pairs, is the
mean of f(W)² over the matrices W of rank |S|. -/
theorem card_mul_DM (f : Mt μ → ℝ) (S : Finset (Fin μ)) :
    (((univ : Finset (Mt μ)).filter fun W => W.rank = S.card).card : ℝ) * DM f (dg S) =
      (Fintype.card (GLM (Fin μ)) : ℝ) ^ 2 *
        ∑ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = S.card), f W ^ 2 := by
  have h1 : ∀ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = S.card), DM f W = DM f (dg S) := by
    intro W hW
    obtain ⟨p, q, T, rfl⟩ := exists_factor W
    rw [mem_filter, rank_units, rank_dg] at hW
    rw [DM_mul, DM_dg_congr f hW.2]
  have h2 : ∀ p q : GLM (Fin μ), ∑ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = S.card),
      f ((p : Mt μ) * W * (q : Mt μ)) ^ 2 =
        ∑ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = S.card), f W ^ 2 := by
    intro p q
    rw [sum_filter, sum_filter]
    let E : Mt μ ≃ Mt μ := (Units.mulLeft p).trans (Units.mulRight q)
    refine Eq.trans (sum_congr rfl fun W _ => ?_) (Equiv.sum_comp E fun W => if W.rank = S.card then f W ^ 2 else 0)
    show _ = if ((p : Mt μ) * W * (q : Mt μ)).rank = S.card then f ((p : Mt μ) * W * (q : Mt μ)) ^ 2 else 0
    rw [rank_units]
  rw [← nsmul_eq_mul, ← sum_const, ← sum_congr rfl h1]
  unfold DM
  rw [sum_comm, sum_congr rfl fun p _ => sum_comm, sum_congr rfl fun p _ => sum_congr rfl fun q _ => h2 p q]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  ring

theorem rank_X (p q : GLM (Fin μ)) (S : Finset (Fin μ)) : (X p q S).rank = S.card := by
  rw [X, rank_units, rank_dg]

/-- The number of the triples (p, q, a). -/
noncomputable def frames (μ : ℕ) : ℝ := (Fintype.card (GLM (Fin μ)) : ℝ) ^ 2 * Fintype.card (Mt μ)

theorem frames_pos (μ : ℕ) : 0 < frames μ := by
  have h1 : (0 : ℝ) < Fintype.card (GLM (Fin μ)) := by exact_mod_cast Fintype.card_pos
  have h2 : (0 : ℝ) < Fintype.card (Mt μ) := by exact_mod_cast Fintype.card_pos
  unfold frames
  positivity

/-- For uniform invertible p and q the matrix p·dg(S)·q is uniform of rank |S|. -/
theorem MD_eq_meanSq (w : Mt μ → Mt μ → ℝ) (S : Finset (Fin μ)) : MD w (dg S) = frames μ * meanSq w S.card := by
  have hn : (0 : ℝ) < ((univ : Finset (Mt μ)).filter fun W => W.rank = S.card).card := by
    exact_mod_cast card_pos.2 ⟨dg S, mem_filter.2 ⟨mem_univ _, rank_dg S⟩⟩
  have hm : (0 : ℝ) < Fintype.card (Mt μ) := by exact_mod_cast Fintype.card_pos
  rw [frames, meanSq, ← mul_div_assoc, eq_div_iff (by positivity), MD, sum_mul, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  have h := card_mul_DM (fun M => w a (a + M)) S
  linear_combination (Fintype.card (Mt μ) : ℝ) * h

theorem exists_disjoint_card {i j : ℕ} (hij : i + j ≤ μ) :
    ∃ S T : Finset (Fin μ), Disjoint S T ∧ S.card = i ∧ T.card = j := by
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin μ))) (n := i) (by simp; omega)
  obtain ⟨T, hT, hT'⟩ := exists_subset_card_eq (s := (univ \ S : Finset (Fin μ))) (n := j)
    (by rw [card_sdiff_of_subset (subset_univ _)]; simp; omega)
  exact ⟨S, T, disjoint_of_subset_right hT disjoint_sdiff, hS, hT'⟩

theorem meanSq_smul (w : Mt μ → Mt μ → ℝ) (c : ℝ) (r : ℕ) :
    meanSq (fun a b => c * w a b) r = c ^ 2 * meanSq w r := by
  unfold meanSq
  simp only [mul_pow, ← mul_sum, mul_div_assoc]

theorem continuous_meanSq (r : ℕ) : Continuous fun w : Mt μ → Mt μ → ℝ => meanSq w r := by
  unfold meanSq
  refine Continuous.div_const (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun W _ => ?_) _
  exact (continuous_apply_apply _ _).pow 2

/-! ## The proof of Theorem thm:alt: equality -/

/-- "Every price is pulled back from the metric of a CAT(0) space, by Proposition prop:space." So Lemma lem:toolkit (b)
holds in every price: the squared diagonals of a quadrangle add up to at most its squared sides, and if there is
equality, opposite sides are equal. -/
theorem thm_alt_quadrangle {V : Type} {w : V → V → ℝ} (hw : IsPrice K w) (x v y u : V) :
    w x v ^ 2 + w y u ^ 2 ≤ w x y ^ 2 + w y v ^ 2 + w v u ^ 2 + w x u ^ 2 ∧
    (w x v ^ 2 + w y u ^ 2 = w x y ^ 2 + w y v ^ 2 + w v u ^ 2 + w x u ^ 2 → w x y = w v u ∧ w y v = w x u) := by
  obtain ⟨Y, _, _, f, -, hf⟩ := prop_space hw
  simp only [← hf]
  exact ((lem_toolkit (Y := Y)).2.1 (f x) (f v) (f y) (f u)).2

theorem defect_nonneg (hw : IsPrice K w) (a W W' : Mt μ) : 0 ≤ defect w a W W' := by
  have := (thm_alt_quadrangle hw a (a + W + W') (a + W) (a + W')).1
  unfold defect
  linarith

/-- "Let (W, W') be a random transversal pair of ranks i, j, i+j ≤ μ, and let a be uniform and independent of it; then W, W',
W+W' are uniform of ranks i, j, i+j. Both diagonals of a, a+W, a+W+W', a+W' have difference W+W'." The random pair is
(p·dg(S)·q, p·dg(T)·q) for disjoint sets S, T of i and j indices and uniform invertible p, q; that the three matrices are
uniform is `MD_eq_meanSq`. The statement is the consequence: the sum over p, q and a of the squared sides minus the squared
diagonals is the number of the (p, q, a) times 2(D(i)² + D(j)² − D(i+j)²). -/
theorem thm_alt_mean_defect (hw : IsPrice K w) {S T : Finset (Fin μ)} (h : Disjoint S T) :
    ∑ p : GLM (Fin μ), ∑ q : GLM (Fin μ), ∑ a, defect w a (X p q S) (X p q T) =
      2 * frames μ * (meanSq w S.card + meanSq w T.card - meanSq w (S.card + T.card)) := by
  rw [sum_all_defect hw.symm h, MD_eq_meanSq, MD_eq_meanSq, MD_eq_meanSq, card_union_of_disjoint h]
  ring

/-- "By Lemma lem:toolkit (b), D(i+j)² ≤ D(i)² + D(j)²", for i + j ≤ μ. -/
theorem thm_alt_subadditive (hw : IsPrice K w) {i j : ℕ} (hij : i + j ≤ μ) :
    meanSq w (i + j) ≤ meanSq w i + meanSq w j := by
  obtain ⟨S, T, hd, rfl, rfl⟩ := exists_disjoint_card hij
  have h1 := thm_alt_mean_defect hw hd
  have h2 : 0 ≤ ∑ p : GLM (Fin μ), ∑ q : GLM (Fin μ), ∑ a, defect w a (X p q S) (X p q T) :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => defect_nonneg hw _ _ _
  rw [h1] at h2
  have h3 := frames_pos μ
  by_contra hlt
  push Not at hlt
  nlinarith

theorem meanSq_zero (hw : IsPrice K w) : meanSq w 0 = 0 := by
  unfold meanSq
  rw [sum_eq_zero, zero_div]
  refine fun a _ => sum_eq_zero fun W hW => ?_
  obtain ⟨p, q, S, rfl⟩ := exists_X W
  rw [mem_filter, rank_X, card_eq_zero] at hW
  rw [hW.2, X_empty, add_zero, hw.self]
  norm_num

/-- D(r)² ≤ r·D(1)². -/
theorem meanSq_le (hw : IsPrice K w) {r : ℕ} (hr : r ≤ μ) : meanSq w r ≤ r * meanSq w 1 := by
  induction r with
  | zero => simp [meanSq_zero hw]
  | succ r ih =>
    have h1 := thm_alt_subadditive hw (i := r) (j := 1) hr
    have h2 := ih (by omega)
    push_cast
    linarith

/-- "Every distance is at most a constant, depending on μ, times D(1)." -/
theorem thm_alt_bounded (K : Type) [Field K] (μ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Mt μ → Mt μ → ℝ, IsPrice K w → ∀ a b, w a b ≤ C * distAtRank w 1 := by
  set c : ℝ := (Fintype.card (Mt μ) : ℝ) * ((univ : Finset (Mt μ)).filter (fun W => W.rank = 1)).card with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨μ * √c, by positivity, fun w hw a b => ?_⟩
  have hD : 0 ≤ distAtRank w 1 := Real.sqrt_nonneg _
  have hstep : ∀ (e R : Mt μ), R.rank = 1 → w e (e + R) ≤ √c * distAtRank w 1 := by
    intro e R hR
    have hpos : 0 < c := by
      have h1 : (0 : ℝ) < Fintype.card (Mt μ) := by exact_mod_cast Fintype.card_pos
      have h2 : (0 : ℝ) < ((univ : Finset (Mt μ)).filter (fun W => W.rank = 1)).card := by
        exact_mod_cast card_pos.2 ⟨R, mem_filter.2 ⟨mem_univ _, hR⟩⟩
      positivity
    have h1 : w e (e + R) ^ 2 ≤ ∑ a : Mt μ, ∑ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = 1),
        w a (a + W) ^ 2 := by
      refine le_trans ?_ (single_le_sum (f := fun a => ∑ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = 1),
        w a (a + W) ^ 2) (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_univ e))
      exact single_le_sum (f := fun W => w e (e + W) ^ 2) (fun _ _ => sq_nonneg _)
        (mem_filter.2 ⟨mem_univ _, hR⟩)
    have h2 : (∑ a : Mt μ, ∑ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = 1), w a (a + W) ^ 2) =
        c * meanSq w 1 := by
      rw [meanSq, ← hc, mul_div_cancel₀ _ hpos.ne']
    rw [distAtRank, ← Real.sqrt_mul hc0]
    exact Real.le_sqrt_of_sq_le (h1.trans h2.le)
  obtain ⟨p, q, S, hM⟩ := exists_X (a + b)
  have hS : ∀ S : Finset (Fin μ), w a (a + X p q S) ≤ S.card * (√c * distAtRank w 1) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [X_empty, hw.self]
    | insert i S hi ih =>
      have h2 := hw.triangle a (a + X p q S) (a + X p q S + X p q {i})
      have h4 := hstep (a + X p q S) (X p q {i}) (by rw [rank_X, card_singleton])
      rw [insert_eq, union_comm, X_union p q (by simpa using hi), ← add_assoc, card_union_of_disjoint (by simpa using hi),
        card_singleton]
      push_cast
      linarith
  have h2 := hS S
  rw [← hM, add_cancel_left] at h2
  have h3 : (S.card : ℝ) ≤ μ := by
    have := card_le_univ S
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  calc w a b ≤ S.card * (√c * distAtRank w 1) := h2
    _ ≤ μ * (√c * distAtRank w 1) := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = _ := by ring

/-- "A price with D(1) = 1 and D(μ)² = μ." -/
structure Extremal (K : Type) [Field K] (w : Mt μ → Mt μ → ℝ) : Prop where
  price : IsPrice K w
  one : meanSq w 1 = 1
  top : meanSq w μ = μ

/-- "As we are not in the contracting case, there are prices with D(μ) > sD(1) for every s < √μ. Every distance is at most
a constant, depending on μ, times D(1), so we may scale to D(1) = 1 and, by compactness, pass to a limit: a price with
D(1) = 1 and D(μ)² = μ." -/
theorem thm_alt_extremal (hK : ¬ Contracting K) (hμ : 2 ≤ μ) : ∃ w : Mt μ → Mt μ → ℝ, Extremal K w := by
  have hμ2 : (2 : ℝ) ≤ μ := by exact_mod_cast hμ
  obtain ⟨C, hC0, hC⟩ := thm_alt_bounded K μ
  have hstep : ∀ n : ℕ, ∃ w : Mt μ → Mt μ → ℝ, (IsPrice K w ∧ ∀ a b, w a b ≤ C) ∧
      meanSq w 1 = 1 ∧ (μ : ℝ) - 1 / ((n : ℝ) + 1) ≤ meanSq w μ := by
    intro n
    have hn : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hn0 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    set t : ℝ := (μ : ℝ) - 1 / ((n : ℝ) + 1) with ht
    have ht0 : 0 ≤ t := by linarith
    obtain ⟨w, hw, hlt⟩ : ∃ w : Mt μ → Mt μ → ℝ, IsPrice K w ∧ √t * distAtRank w 1 < distAtRank w μ := by
      by_contra hcon
      push Not at hcon
      refine hK ⟨μ, √t, hμ, ?_, ?_, hcon⟩
      · rw [Real.le_sqrt (by norm_num) ht0]
        linarith
      · rw [Real.sq_sqrt ht0]
        linarith
    rw [distAtRank, distAtRank, ← Real.sqrt_mul ht0,
      Real.sqrt_lt_sqrt_iff (mul_nonneg ht0 (meanSq_nonneg w 1))] at hlt
    set b := meanSq w 1 with hb
    have hb0 : 0 < b := by
      rcases (meanSq_nonneg w 1).eq_or_lt with h0 | h0
      · exfalso
        have h2 := meanSq_le hw (le_refl μ)
        have h0' : b = 0 := h0.symm
        rw [← h0, mul_zero] at h2
        rw [h0', mul_zero] at hlt
        linarith
      · exact h0
    have hc : (1 / √b) ^ 2 * b = 1 := by
      rw [div_pow, Real.sq_sqrt hb0.le]
      field_simp
    have hw' : IsPrice K fun a b' => 1 / √b * w a b' := hw.smul (one_div_nonneg.2 (Real.sqrt_nonneg b))
    have e1 : meanSq (fun a b' => 1 / √b * w a b') 1 = 1 := by rw [meanSq_smul, ← hb, hc]
    refine ⟨_, ⟨hw', fun a b' => ?_⟩, e1, ?_⟩
    · have := hC _ hw' a b'
      rwa [distAtRank, e1, Real.sqrt_one, mul_one] at this
    · rw [meanSq_smul]
      calc t = (1 / √b) ^ 2 * (t * b) := by rw [mul_left_comm, hc, mul_one]
        _ ≤ _ := mul_le_mul_of_nonneg_left hlt.le (sq_nonneg _)
  choose W hW1 hW2 hW3 using hstep
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_isPrice_le (K := K) fun _ _ : Mt μ => C).tendsto_subseq hW1
  have h1 : meanSq w 1 = 1 := by
    have h1 := ((continuous_meanSq (μ := μ) 1).tendsto w).comp hlim
    have h2 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (meanSq w 1)) := h1.congr fun n => hW2 (φ n)
    exact (tendsto_nhds_unique tendsto_const_nhds h2).symm
  refine ⟨w, hw.1, h1, le_antisymm ?_ ?_⟩
  · have := meanSq_le hw.1 (le_refl μ)
    rwa [h1, mul_one] at this
  · have h3 := ((continuous_meanSq (μ := μ) μ).tendsto w).comp hlim
    have h4 : Tendsto (fun n : ℕ => (μ : ℝ) - 1 / (((φ n : ℕ) : ℝ) + 1)) atTop (𝓝 ((μ : ℝ) - 0)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).const_sub _
    rw [sub_zero] at h4
    exact le_of_tendsto_of_tendsto' h4 h3 fun n => hW3 (φ n)

/-- "For it D(r)² = r for all r, as μ ≤ D(r)² + D(μ−r)²." -/
theorem thm_alt_ranks (hx : Extremal K w) {r : ℕ} (hr : r ≤ μ) : meanSq w r = r := by
  have h1 := meanSq_le hx.price hr
  have h2 := meanSq_le hx.price (Nat.sub_le μ r)
  have h3 := thm_alt_subadditive hx.price (i := r) (j := μ - r) (by omega)
  rw [Nat.add_sub_cancel' hr, hx.top] at h3
  rw [hx.one, mul_one] at h1 h2
  rw [Nat.cast_sub hr] at h2
  linarith

/-- "So equality holds for all these quadrangles, that is, for every a and every transversal pair": the squared sides of
a, a+W, a+W+W', a+W' add up to the squared diagonals. -/
theorem thm_alt_equality (hx : Extremal K w) {W W' : Mt μ} (h : Transversal ![W, W']) (a : Mt μ) :
    w a (a + W) ^ 2 + w (a + W) (a + W + W') ^ 2 + w (a + W + W') (a + W') ^ 2 + w a (a + W') ^ 2 =
      w a (a + W + W') ^ 2 + w (a + W) (a + W') ^ 2 := by
  obtain ⟨p, q, S, T, hd, rfl, rfl⟩ := transversal_pair.1 h
  have hq := hx.price
  have hc : S.card + T.card ≤ μ := by
    rw [← card_union_of_disjoint hd]
    simpa using card_le_univ (S ∪ T)
  have h4 := thm_alt_mean_defect hx.price hd
  rw [thm_alt_ranks hx hc, thm_alt_ranks hx (by omega : S.card ≤ μ), thm_alt_ranks hx (by omega : T.card ≤ μ)] at h4
  push_cast at h4
  rw [sub_self, mul_zero, sum_eq_zero_iff_of_nonneg (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    defect_nonneg hq _ _ _)] at h4
  have h5 := h4 p (mem_univ p)
  rw [sum_eq_zero_iff_of_nonneg (fun _ _ => sum_nonneg fun _ _ => defect_nonneg hq _ _ _)] at h5
  have h6 := h5 q (mem_univ q)
  rw [sum_eq_zero_iff_of_nonneg (fun _ _ => defect_nonneg hq _ _ _)] at h6
  have h7 := h6 a (mem_univ a)
  unfold defect at h7
  linarith

/-- "For transversal W, W', opposite sides are equal: n_{a+W'}(W) = n_a(W)." -/
theorem thm_alt_opposite (hx : Extremal K w) {W W' : Mt μ} (h : Transversal ![W, W']) (a : Mt μ) :
    nn w (a + W') W = nn w a W := by
  have h1 := ((thm_alt_quadrangle hx.price a (a + W + W') (a + W) (a + W')).2 (thm_alt_equality hx h a).symm).1
  unfold nn
  rw [add_right_comm, hx.price.symm, ← h1]

/-- "Also all quadrangles have equality, so |a+W, a+W'|² = 2n_a(W) + 2n_a(W') − n_a(W+W')." -/
theorem thm_alt_diagonal (hx : Extremal K w) {W W' : Mt μ} (h : Transversal ![W, W']) (a : Mt μ) :
    w (a + W) (a + W') ^ 2 = 2 * nn w a W + 2 * nn w a W' - nn w a (W + W') := by
  have h1 := thm_alt_equality hx h a
  have h2 := thm_alt_opposite hx (transversal_symm h) a
  have h3 := thm_alt_opposite hx h a
  unfold nn at h2 h3 ⊢
  rw [add_right_comm, hx.price.symm] at h3
  rw [← add_assoc]
  linarith

/-! ## The proof of Theorem thm:alt: rank one -/

/-- "Insert this into the quadrangle at a+W₂ with sides W₁, W₂+W₃, whose other vertices are a+W₁+W₂, a+W₃ and a+W₁+W₃. This
gives, for transversal W₁, W₂, W₃, … B_a(W₁, W₂+W₃) = B_a(W₁, W₂) + B_a(W₁, W₃)." -/
theorem thm_alt_additive (hx : Extremal K w) {W₁ W₂ W₃ : Mt μ} (h : Transversal ![W₁, W₂, W₃]) (a : Mt μ) :
    BB w a W₁ (W₂ + W₃) = BB w a W₁ W₂ + BB w a W₁ W₃ := by
  obtain ⟨p, q, S₁, S₂, S₃, h12, h13, h23, rfl, rfl, rfl⟩ := transversal_triple.1 h
  have t1 : Transversal ![X p q S₁, X p q S₂ + X p q S₃] := by
    rw [← X_union p q h23]
    exact transversal_X p q (disjoint_union_right.2 ⟨h12, h13⟩)
  have t2 : Transversal ![X p q S₂, X p q S₁ + X p q S₃] := by
    rw [← X_union p q h13]
    exact transversal_X p q (disjoint_union_right.2 ⟨h12.symm, h23⟩)
  have t3 : Transversal ![X p q S₁ + X p q S₂, X p q S₃] := by
    rw [← X_union p q h12]
    exact transversal_X p q (disjoint_union_left.2 ⟨h13, h23⟩)
  set M := X p q S₁
  set N := X p q S₂
  set P := X p q S₃
  have e1 := thm_alt_diagonal hx t1 (a + N)
  have e2 := thm_alt_diagonal hx t2 a
  have e3 := thm_alt_diagonal hx t3 a
  have e4 := thm_alt_diagonal hx (transversal_X p q h23) a
  have e5 := thm_alt_opposite hx (transversal_X p q h12) a
  have f1 : nn w (a + N) (N + P) = w (a + N) (a + P) ^ 2 := by
    unfold nn
    rw [add_assoc, add_cancel_left]
  have f2 : nn w (a + N) (M + (N + P)) = w (a + N) (a + (M + P)) ^ 2 := by
    unfold nn
    congr 2
    rw [add_assoc]
    congr 1
    rw [add_left_comm M N P, add_cancel_left]
  have f3 : w (a + N + M) (a + N + (N + P)) = w (a + (M + N)) (a + P) := by
    congr 1
    · rw [add_assoc, add_comm N M]
    · rw [add_assoc, add_cancel_left]
  have f4 : N + (M + P) = M + N + P := by rw [add_left_comm, add_assoc]
  rw [f3, f2, f1, e2, e3, e4, e5, f4] at e1
  unfold BB
  rw [← add_assoc]
  linarith

theorem exists_singleton {p q : GLM (Fin μ)} {S : Finset (Fin μ)} (h : (X p q S).rank = 1) : ∃ i, S = {i} := by
  rw [rank_X] at h
  exact card_eq_one.1 h

/-- A matrix of rank one is u xᵀ with vectors u, x ≠ 0. -/
theorem exists_vec {V : Mt μ} (h : V.rank = 1) : ∃ u x : Fin μ → F2, u ≠ 0 ∧ x ≠ 0 ∧ V = vecMulVec u x := by
  obtain ⟨p, q, S, rfl⟩ := exists_X V
  obtain ⟨i, rfl⟩ := exists_singleton h
  exact ⟨_, _, col_ne_zero p i, row_ne_zero q i, X_singleton p q i⟩

/-- "Now u₁x₁ᵀ + u₂x₂ᵀ = u₁(x₁+x₂)ᵀ + (u₁+u₂)x₂ᵀ." -/
theorem thm_alt_identity (u₁ u₂ x₁ x₂ : Fin μ → F2) :
    vecMulVec u₁ x₁ + vecMulVec u₂ x₂ = vecMulVec u₁ (x₁ + x₂) + vecMulVec (u₁ + u₂) x₂ := by
  rw [Matrix.vecMulVec_add, Matrix.add_vecMulVec, add_assoc, ← add_assoc (vecMulVec u₁ x₂), madd_self, zero_add]

section Exchange

/-! The exchange is used twice: for Φ = B_a(W, ·), which is additive by `thm_alt_additive`, and "with W = 0 and n_a in place of
B_a". So it is stated for a matrix W and any function Φ with Φ(V₁ + V₂) = Φ(V₁) + Φ(V₂) for transversal W, V₁, V₂; the paper's
χ(u, x) is Φ(u xᵀ). -/

variable {W : Mt μ} {Φ : Mt μ → ℝ}

/-- "Let W, u₁x₁ᵀ, u₂x₂ᵀ be transversal … For χ(u,x) = B_a(W, uxᵀ) this gives
χ(u₁,x₁) − χ(u₁,x₁+x₂) = χ(u₁+u₂,x₂) − χ(u₂,x₂). The right side does not depend on x₁, and the left side changes sign when x₁
becomes x₁+x₂; both vanish." The matrices u₁x₁ᵀ and u₂x₂ᵀ have rank one, that is, they are not zero. -/
theorem thm_alt_exchange (hΦ : ∀ V₁ V₂, Transversal ![W, V₁, V₂] → Φ (V₁ + V₂) = Φ V₁ + Φ V₂)
    {u₁ u₂ x₁ x₂ : Fin μ → F2} (h : Transversal ![W, vecMulVec u₁ x₁, vecMulVec u₂ x₂])
    (h1 : vecMulVec u₁ x₁ ≠ 0) (h2 : vecMulVec u₂ x₂ ≠ 0) :
    Φ (vecMulVec u₁ x₁) - Φ (vecMulVec u₁ (x₁ + x₂)) = 0 ∧
      Φ (vecMulVec (u₁ + u₂) x₂) - Φ (vecMulVec u₂ x₂) = 0 := by
  obtain ⟨hu, hx⟩ := (transversal_vec_iff h1 h2).1 h
  -- the displayed equation, for every x₁
  have key : ∀ {x₁ : Fin μ → F2}, Indep2 (rowSpace W) x₁ x₂ →
      Φ (vecMulVec u₁ x₁) - Φ (vecMulVec u₁ (x₁ + x₂)) = Φ (vecMulVec (u₁ + u₂) x₂) - Φ (vecMulVec u₂ x₂) := by
    intro x₁ hx
    have e1 := hΦ _ _ (transversal_of_indep2 hu hx)
    have e2 := hΦ _ _ (transversal_of_indep2 hu.add_right hx.add_left)
    rw [thm_alt_identity] at e1
    linarith
  have k1 := key hx
  have k2 := key hx.add_left
  rw [add_assoc, vadd_self, add_zero] at k2
  constructor <;> linarith

/-- "So x may be changed by any vector outside its span with the row space of W, and likewise u." Here u xᵀ ≠ 0 is
transversal to W, that is, u is outside the column space and x outside the row space of W, and rk W + 2 ≤ μ. -/
theorem thm_alt_move (hΦ : ∀ V₁ V₂, Transversal ![W, V₁, V₂] → Φ (V₁ + V₂) = Φ V₁ + Φ V₂) (hW : W.rank + 2 ≤ μ)
    {u x : Fin μ → F2} (hu : u ∉ colSpace W) (hx : x ∉ rowSpace W) :
    (∀ y, y ∉ rowSpace W ⊔ Submodule.span F2 {x} → Φ (vecMulVec u (x + y)) = Φ (vecMulVec u x)) ∧
      ∀ v, v ∉ colSpace W ⊔ Submodule.span F2 {u} → Φ (vecMulVec (u + v) x) = Φ (vecMulVec u x) := by
  constructor
  · intro y hy
    obtain ⟨v, hv⟩ := exists_indep2 (by rw [finrank_colSpace]; exact hW) hu
    have hxy : Indep2 (rowSpace W) x y := indep2_iff.2 ⟨hx, hy⟩
    have := (thm_alt_exchange hΦ (transversal_of_indep2 hv hxy) (vec_ne_zero.2 ⟨hv.ne_zero.1, hxy.ne_zero.1⟩)
      (vec_ne_zero.2 ⟨hv.ne_zero.2, hxy.ne_zero.2⟩)).1
    linarith
  · intro v hv
    obtain ⟨y, hy⟩ := exists_indep2 (by rw [finrank_rowSpace]; exact hW) hx
    have huv : Indep2 (colSpace W) u v := indep2_iff.2 ⟨hu, hv⟩
    have := (thm_alt_exchange hΦ (transversal_of_indep2 huv.symm hy.symm)
      (vec_ne_zero.2 ⟨huv.ne_zero.2, hy.ne_zero.2⟩) (vec_ne_zero.2 ⟨huv.ne_zero.1, hy.ne_zero.1⟩)).2
    rw [add_comm u v]
    linarith

/-- "As μ ≥ 3, such moves connect all vectors outside the column, respectively row space of a rank-one W": so Φ has one
value on the matrices of rank one that are transversal to W. (What is used of μ ≥ 3 and rk W = 1 is rk W + 2 ≤ μ.) -/
theorem thm_alt_connect (hΦ : ∀ V₁ V₂, Transversal ![W, V₁, V₂] → Φ (V₁ + V₂) = Φ V₁ + Φ V₂) (hW : W.rank + 2 ≤ μ)
    {V V' : Mt μ} (hV : Transversal ![W, V]) (hV' : Transversal ![W, V']) (h1 : V.rank = 1) (h2 : V'.rank = 1) :
    Φ V = Φ V' := by
  obtain ⟨u, x, hu, hx, rfl⟩ := exists_vec h1
  obtain ⟨u', x', hu', hx', rfl⟩ := exists_vec h2
  obtain ⟨cu, cx⟩ := (transversal_vec hu hx).1 hV
  obtain ⟨cu', cx'⟩ := (transversal_vec hu' hx').1 hV'
  calc Φ (vecMulVec u x) = Φ (vecMulVec u x') :=
        connect (by rw [finrank_rowSpace]; exact hW) (g := fun x => Φ (vecMulVec u x))
          (fun x y h => (thm_alt_move hΦ hW cu h.1).1 y (indep2_iff.1 h).2) cx cx'
    _ = Φ (vecMulVec u' x') :=
        connect (by rw [finrank_colSpace]; exact hW) (g := fun u => Φ (vecMulVec u x'))
          (fun u v h => (thm_alt_move hΦ hW h.1 cx').2 v (indep2_iff.1 h).2) cu cu'

end Exchange

/-- "… and any two matrices of rank one are both transversal to a third", as μ ≥ 3. -/
theorem thm_alt_third (hμ : 3 ≤ μ) {V W : Mt μ} (hV : V.rank = 1) (hW : W.rank = 1) :
    ∃ Z : Mt μ, Z.rank = 1 ∧ Transversal ![V, Z] ∧ Transversal ![W, Z] := by
  have hc : Module.finrank F2 (colSpace V ⊔ colSpace W : Submodule F2 (Fin μ → F2)) < μ := by
    have := Submodule.finrank_add_le_finrank_add_finrank (colSpace V) (colSpace W)
    rw [finrank_colSpace, finrank_colSpace] at this
    omega
  have hr : Module.finrank F2 (rowSpace V ⊔ rowSpace W : Submodule F2 (Fin μ → F2)) < μ := by
    have := Submodule.finrank_add_le_finrank_add_finrank (rowSpace V) (rowSpace W)
    rw [finrank_rowSpace, finrank_rowSpace] at this
    omega
  obtain ⟨u, hu⟩ := exists_notMem hc
  obtain ⟨x, hx⟩ := exists_notMem hr
  have hu0 : u ≠ 0 := fun e => hu (e ▸ Submodule.zero_mem _)
  have hx0 : x ≠ 0 := fun e => hx (e ▸ Submodule.zero_mem _)
  exact ⟨vecMulVec u x, rank_vec hu0 hx0,
    (transversal_vec hu0 hx0).2 ⟨fun h => hu (Submodule.mem_sup_left h), fun h => hx (Submodule.mem_sup_left h)⟩,
    (transversal_vec hu0 hx0).2 ⟨fun h => hu (Submodule.mem_sup_right h), fun h => hx (Submodule.mem_sup_right h)⟩⟩

/-- "As B_a is symmetric, it has one value λ(a) on all transversal pairs of rank one." -/
theorem thm_alt_lambda (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) {V V' W W' : Mt μ} (hV : Transversal ![V, V'])
    (hW : Transversal ![W, W']) (h1 : V.rank = 1) (h2 : V'.rank = 1) (h3 : W.rank = 1) (h4 : W'.rank = 1) :
    BB w a V V' = BB w a W W' := by
  have con : ∀ {Z U U' : Mt μ}, Z.rank = 1 → U.rank = 1 → U'.rank = 1 → Transversal ![Z, U] → Transversal ![Z, U'] →
      BB w a Z U = BB w a Z U' := fun hZ hU hU' t t' =>
    thm_alt_connect (Φ := BB w a _) (fun _ _ h => thm_alt_additive hx h a) (by omega) t t' hU hU'
  obtain ⟨Z, hZ, t1, t2⟩ := thm_alt_third hμ h1 h3
  calc BB w a V V' = BB w a V Z := con h1 h2 hZ hV t1
    _ = BB w a Z V := BB_comm _ _ _
    _ = BB w a Z W := con hZ h1 h3 (transversal_symm t1) (transversal_symm t2)
    _ = BB w a W Z := BB_comm _ _ _
    _ = BB w a W W' := con h3 hZ h4 t2 hW

/-- "Since n_{a+V}(V) = n_a(V), n_{a+V}(W') = n_a(W') and n_{a+V}(V+W') = |a+V, a+W'|², the display of the first step gives
B_{a+V}(V, W') = −B_a(V, W')", for transversal V, W'. -/
theorem thm_alt_reflect (hx : Extremal K w) {V W' : Mt μ} (h : Transversal ![V, W']) (a : Mt μ) :
    BB w (a + V) V W' = - BB w a V W' := by
  have e1 := thm_alt_diagonal hx h a
  have e2 := thm_alt_opposite hx (transversal_symm h) a
  have f1 : nn w (a + V) (V + W') = w (a + V) (a + W') ^ 2 := by
    unfold nn
    rw [add_assoc, add_cancel_left]
  have f2 : nn w (a + V) V = nn w a V := by
    unfold nn
    rw [add_assoc, madd_self, add_zero, hx.price.symm]
  unfold BB
  rw [f1, f2, e1, e2]
  ring

/-- "So λ = 0": B_a vanishes on the transversal pairs of rank one. The proof is the printed one, "By additivity this value is
2λ if V has rank two; so we get λ(a+V) = −λ(a) for V of rank one or two; but two steps of rank one give λ(a+V) = λ(a)", for
the matrices V = dg{i}, dg{j} and dg{i} + dg{j}. -/
theorem thm_alt_orthogonal (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) {W W' : Mt μ} (h : Transversal ![W, W'])
    (h1 : W.rank = 1) (h2 : W'.rank = 1) : BB w a W W' = 0 := by
  set i : Fin μ := ⟨0, by omega⟩ with hi
  set j : Fin μ := ⟨1, by omega⟩ with hj
  set k : Fin μ := ⟨2, by omega⟩ with hk
  have hij : i ≠ j := by simp [hi, hj, Fin.ext_iff]
  have hik : i ≠ k := by simp [hi, hk, Fin.ext_iff]
  have hjk : j ≠ k := by simp [hj, hk, Fin.ext_iff]
  have r1 : ∀ l : Fin μ, (dg {l} : Mt μ).rank = 1 := fun l => by rw [rank_dg, card_singleton]
  have tr : ∀ {l l' : Fin μ}, l ≠ l' → Transversal ![(dg {l} : Mt μ), dg {l'}] := fun h =>
    transversal_dg (by simpa using h)
  -- λ(b), and all transversal pairs of rank one have this value
  have lam : ∀ (b : Mt μ) {l l' : Fin μ}, l ≠ l' → BB w b (dg {l}) (dg {l'}) = BB w b (dg {i}) (dg {j}) :=
    fun b l l' h => thm_alt_lambda hx hμ b (tr h) (tr hij) (r1 _) (r1 _) (r1 _) (r1 _)
  have s1 : ∀ b, BB w (b + dg {i}) (dg {i}) (dg {j}) = - BB w b (dg {i}) (dg {j}) :=
    fun b => thm_alt_reflect hx (tr hij) b
  have s2 : ∀ b, BB w (b + dg {j}) (dg {i}) (dg {j}) = - BB w b (dg {i}) (dg {j}) := fun b => by
    rw [← lam _ hij.symm, ← lam b hij.symm]
    exact thm_alt_reflect hx (tr hij.symm) b
  have two : ∀ b, BB w b (dg {i} + dg {j}) (dg {k}) = 2 * BB w b (dg {i}) (dg {j}) := fun b => by
    rw [BB_comm, thm_alt_additive hx (transversal_triple.2 ⟨1, 1, {k}, {i}, {j}, by simpa using hik.symm,
      by simpa using hjk.symm, by simpa using hij, (X_one _).symm, (X_one _).symm, (X_one _).symm⟩), lam b hik.symm, lam b hjk.symm]
    ring
  have s3 := thm_alt_reflect hx (V := dg {i} + dg {j}) (W' := dg {k})
    (by rw [← dg_union (by simpa using hij)]; exact transversal_dg (by simp [hik.symm, hjk.symm])) a
  rw [two, two, ← add_assoc, s2, s1] at s3
  rw [thm_alt_lambda hx hμ a h (tr hij) h1 h2 (r1 _) (r1 _)]
  linarith

/-- By additivity, B_a vanishes on p·dg{i}·q and p·dg(S)·q if i is not in S. -/
theorem BB_singleton_set (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) (p q : GLM (Fin μ)) {i : Fin μ}
    {S : Finset (Fin μ)} (hi : i ∉ S) : BB w a (X p q {i}) (X p q S) = 0 := by
  induction S using Finset.induction_on with
  | empty => simp [BB, nn, X_empty, hx.price.self]
  | insert j S hj ih =>
    rw [mem_insert, not_or] at hi
    have hd : Disjoint {j} S := by simpa using hj
    have hij : Disjoint ({i} : Finset (Fin μ)) {j} := by simpa using hi.1
    rw [insert_eq, X_union p q hd, thm_alt_additive hx (transversal_triple.2 ⟨p, q, {i}, {j}, S, hij, by simpa using hi.2, hd, rfl, rfl, rfl⟩),
      ih hi.2, thm_alt_orthogonal hx hμ a (transversal_X p q hij) (by simp [rank_X]) (by simp [rank_X]), add_zero]

/-- So n_a(p·dg(S)·q) is the sum of the n_a(p·dg{i}·q) over i in S. -/
theorem nn_X (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) (p q : GLM (Fin μ)) (S : Finset (Fin μ)) :
    nn w a (X p q S) = ∑ i ∈ S, nn w a (X p q {i}) := by
  induction S using Finset.induction_on with
  | empty => simp [nn, X_empty, hx.price.self]
  | insert i S hi ih =>
    have h1 := BB_singleton_set hx hμ a p q hi
    unfold BB at h1
    rw [sum_insert hi, insert_eq, X_union p q (by simpa using hi), ← ih]
    linarith

/-- "By additivity n_a is additive on transversal sums." -/
theorem thm_alt_sum (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) {W W' : Mt μ} (h : Transversal ![W, W']) :
    nn w a (W + W') = nn w a W + nn w a W' := by
  obtain ⟨p, q, S, T, hd, rfl, rfl⟩ := transversal_pair.1 h
  rw [← X_union p q hd, nn_X hx hμ, nn_X hx hμ, nn_X hx hμ, sum_union hd]

/-- "The same exchange, with W = 0 and n_a in place of B_a, shows that n_a has one value on rank one". -/
theorem thm_alt_one_value (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) {V V' : Mt μ} (h1 : V.rank = 1)
    (h2 : V'.rank = 1) : nn w a V = nn w a V' :=
  thm_alt_connect (W := 0) (fun _ _ h => thm_alt_sum hx hμ a h.tail) (by rw [Matrix.rank_zero]; omega)
    (transversal_zero V) (transversal_zero V') h1 h2

/-- "… as n_{a+W'}(W) = n_a(W), it does not depend on a". -/
theorem thm_alt_base_point (hx : Extremal K w) (hμ : 3 ≤ μ) (a b : Mt μ) {V : Mt μ} (hV : V.rank = 1) :
    nn w a V = nn w b V := by
  -- a step of rank one
  have shift : ∀ (a : Mt μ) {Z : Mt μ}, Z.rank = 1 → nn w (a + Z) V = nn w a V := by
    intro a Z hZ
    obtain ⟨Z', hZ', t, -⟩ := thm_alt_third hμ hZ hZ
    rw [thm_alt_one_value hx hμ (a + Z) hV hZ', thm_alt_one_value hx hμ a hV hZ']
    exact thm_alt_opposite hx (transversal_symm t) a
  -- every matrix is a sum of matrices of rank one
  obtain ⟨p, q, S, hS⟩ := exists_X (b + a)
  have h1 : ∀ S : Finset (Fin μ), nn w (b + X p q S) V = nn w b V := by
    intro S
    induction S using Finset.induction_on with
    | empty => rw [X_empty, add_zero]
    | insert j S hj ih =>
      rw [insert_eq, union_comm, X_union p q (by simpa using hj), ← add_assoc, shift _ (by simp [rank_X]), ih]
  rw [← h1 S, ← hS, add_cancel_left]

/-- "… so it is 1": the mean of n_a(W) over all a and all W of rank one is D(1)² = 1. -/
theorem thm_alt_rank_one (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) {W : Mt μ} (hW : W.rank = 1) : nn w a W = 1 := by
  have all : ∀ (b V : Mt μ), V.rank = 1 → nn w b V = nn w a W := fun b V hV => by
    rw [thm_alt_one_value hx hμ b hV hW, thm_alt_base_point hx hμ b a hW]
  have hn : (0 : ℝ) < ((univ : Finset (Mt μ)).filter fun W => W.rank = 1).card := by
    exact_mod_cast card_pos.2 ⟨W, mem_filter.2 ⟨mem_univ _, hW⟩⟩
  have hm : (0 : ℝ) < Fintype.card (Mt μ) := by exact_mod_cast Fintype.card_pos
  have h1 := hx.one
  have h5 : ∑ b : Mt μ, ∑ V ∈ (univ : Finset (Mt μ)).filter (fun V => V.rank = 1), w b (b + V) ^ 2 =
      ∑ _b : Mt μ, ∑ _V ∈ (univ : Finset (Mt μ)).filter (fun V => V.rank = 1), nn w a W :=
    sum_congr rfl fun b _ => sum_congr rfl fun V hV => all b V (mem_filter.1 hV).2
  rw [meanSq, h5] at h1
  simp only [sum_const, card_univ, nsmul_eq_mul] at h1
  rw [← mul_assoc, mul_div_cancel_left₀ _ (by positivity)] at h1
  exact h1

/-- "Hence |a, a'|² = rk(a − a')." -/
theorem thm_alt_rank (hx : Extremal K w) (hμ : 3 ≤ μ) (a a' : Mt μ) : w a a' ^ 2 = (a - a').rank := by
  have e : a - a' = a + a' := by
    ext i j
    exact CharTwo.sub_eq_add _ _
  obtain ⟨p, q, S, hS⟩ := exists_X (a + a')
  have h1 : w a a' ^ 2 = nn w a (a + a') := by rw [nn, add_cancel_left]
  rw [h1, e, hS, rank_X, nn_X hx hμ, sum_congr rfl fun i _ => thm_alt_rank_one hx hμ a (by simp [rank_X])]
  simp

/-- "Suppose we are not in the contracting case and fix μ ≥ 3. We show that some price is exactly the square root of the
rank of the difference." -/
theorem thm_alt_rank_price (hK : ¬ Contracting K) (hμ : 3 ≤ μ) :
    ∃ w : Mt μ → Mt μ → ℝ, IsPrice K w ∧ ∀ a a', w a a' ^ 2 = (a - a').rank := by
  obtain ⟨w, hx⟩ := thm_alt_extremal hK (by omega : 2 ≤ μ)
  exact ⟨w, hx.price, thm_alt_rank hx hμ⟩

/-! ## The proof of Theorem thm:alt: a solid cube -/

section Cube

variable {Y : Type} [MetricSpace Y] [Cat.CN Y]

/-- Points of the solid cube [0,1]^μ whose coordinates from `k` on are 0 or 1. -/
def cubePts (μ k : ℕ) : Set (Fin μ → ℝ) :=
  {x | ∀ i, (0 ≤ x i ∧ x i ≤ 1) ∧ (k ≤ i.1 → x i = 0 ∨ x i = 1)}

theorem cubePts_update {k : ℕ} (hk : k < μ) {x : Fin μ → ℝ} (hx : x ∈ cubePts μ (k + 1)) {t : ℝ}
    (ht : t = 0 ∨ t = 1) : Function.update x ⟨k, hk⟩ t ∈ cubePts μ k := by
  intro i
  by_cases hi : i = ⟨k, hk⟩
  · subst hi
    rw [Function.update_self]
    rcases ht with rfl | rfl <;> simp
  · rw [Function.update_of_ne hi]
    refine ⟨(hx i).1, fun h => (hx i).2 ?_⟩
    have : i.1 ≠ k := fun h2 => hi (Fin.ext h2)
    omega

/-- "Fill it one coordinate at a time: Lemma lem:toolkit (f), applied to opposite edges in the new direction, shows that
the map stays isometric." A map F that is isometric on the points whose coordinates from k on are 0 or 1 has an extension F'
that is isometric on the points whose coordinates from k + 1 on are 0 or 1. -/
theorem thm_alt_fill {k : ℕ} (hk : k < μ) (F : (Fin μ → ℝ) → Y)
    (hF : ∀ x ∈ cubePts μ k, ∀ y ∈ cubePts μ k, dist (F x) (F y) ^ 2 = ∑ i, (x i - y i) ^ 2) :
    ∃ F' : (Fin μ → ℝ) → Y, (∀ x ∈ cubePts μ k, F' x = F x) ∧ ∀ x ∈ cubePts μ (k + 1), ∀ y ∈ cubePts μ (k + 1),
      dist (F' x) (F' y) ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  set c : Fin μ := ⟨k, hk⟩ with hc
  -- the point at z_c on the edge in the new direction, by Lemma lem:toolkit (a)
  have hγ : ∀ z : Fin μ → ℝ, ∃ γ : Y, 0 ≤ z c ∧ z c ≤ 1 →
      dist (F (Function.update z c 0)) γ =
        z c * dist (F (Function.update z c 0)) (F (Function.update z c 1)) ∧
      dist γ (F (Function.update z c 1)) =
        (1 - z c) * dist (F (Function.update z c 0)) (F (Function.update z c 1)) := by
    intro z
    by_cases hz : 0 ≤ z c ∧ z c ≤ 1
    · obtain ⟨γ, h, -⟩ := (lem_toolkit (Y := Y)).1 (F (Function.update z c 0)) (F (Function.update z c 1)) (z c) hz.1 hz.2
      exact ⟨γ, fun _ => h⟩
    · exact ⟨F z, fun h => absurd h hz⟩
  choose F' hF' using hγ
  refine ⟨F', fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨e1, e2⟩ := hF' x (hx c).1
    rcases (hx c).2 le_rfl with h0 | h1
    · rw [h0, zero_mul, dist_eq_zero] at e1
      rw [← e1, ← h0, Function.update_eq_self]
    · rw [h1, sub_self, zero_mul, dist_eq_zero] at e2
      rw [e2, ← h1, Function.update_eq_self]
  have hsum : ∀ (x y : Fin μ → ℝ) (s t : ℝ), ∑ i, (Function.update x c s i -
      Function.update y c t i) ^ 2 = (s - t) ^ 2 + ∑ i ∈ univ.erase c, (x i - y i) ^ 2 := by
    intro x y s t
    rw [← add_sum_erase univ _ (mem_univ c), Function.update_self, Function.update_self]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hi), Function.update_of_ne (ne_of_mem_erase hi)]
  have hD : ∀ {x y : Fin μ → ℝ} (_ : x ∈ cubePts μ (k + 1)) (_ : y ∈ cubePts μ (k + 1)) (s t : ℝ)
      (_ : s = 0 ∨ s = 1) (_ : t = 0 ∨ t = 1), dist (F (Function.update x c s))
        (F (Function.update y c t)) ^ 2 = (s - t) ^ 2 + ∑ i ∈ univ.erase c, (x i - y i) ^ 2 := by
    intro x y hx hy s t hs ht
    rw [hF _ (cubePts_update hk hx hs) _ (cubePts_update hk hy ht), hsum]
  set E := ∑ i ∈ univ.erase c, (x i - y i) ^ 2 with hE
  have d1 : dist (F (Function.update x c 0)) (F (Function.update x c 1)) ^ 2 = 1 := by
    rw [hD hx hx 0 1 (Or.inl rfl) (Or.inr rfl)]
    simp
  have d2 : dist (F (Function.update y c 0)) (F (Function.update y c 1)) ^ 2 = 1 := by
    rw [hD hy hy 0 1 (Or.inl rfl) (Or.inr rfl)]
    simp
  have d3 : dist (F (Function.update x c 1)) (F (Function.update y c 1)) ^ 2 = E := by
    rw [hD hx hy 1 1 (Or.inr rfl) (Or.inr rfl)]
    simp [hE]
  have d4 : dist (F (Function.update x c 0)) (F (Function.update y c 0)) ^ 2 = E := by
    rw [hD hx hy 0 0 (Or.inl rfl) (Or.inl rfl)]
    simp [hE]
  have d5 : dist (F (Function.update x c 0)) (F (Function.update y c 1)) ^ 2 = 1 + E := by
    rw [hD hx hy 0 1 (Or.inl rfl) (Or.inr rfl)]
    simp [hE]
  have d6 : dist (F (Function.update y c 0)) (F (Function.update x c 1)) ^ 2 = 1 + E := by
    rw [dist_comm, hD hx hy 1 0 (Or.inr rfl) (Or.inl rfl)]
    simp [hE]
  have h := (lem_toolkit (Y := Y)).2.2.2.2.2 (F (Function.update x c 0)) (F (Function.update y c 0)) (F (Function.update x c 1))
    (F (Function.update y c 1)) (F' x) (F' y) _ _ (x c) (y c) rfl
    ((pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 (d3.trans d4.symm)) rfl
    ((pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 (d2.trans d1.symm))
    (by rw [d5, d4, d1]; ring) (by rw [d6, d4, d1]; ring) (hx c).1.1 (hx c).1.2 (hy c).1.1 (hy c).1.2
    (hF' x (hx c).1).1 (hF' x (hx c).1).2 (hF' y (hy c).1).1 (hF' y (hy c).1).2
  rw [h, d4, d1, ← add_sum_erase univ _ (mem_univ c), ← hE]
  ring

/-- "Fill it one coordinate at a time": if points f(S) of a CAT(0) space have the distances of the vertices of the cube, then the map that sends the
vertex with the coordinates 1 on S and 0 elsewhere to f(S) extends to an isometric map F of the solid cube [0,1]^μ. -/
theorem thm_alt_cube (f : Finset (Fin μ) → Y) (hf : ∀ S T, dist (f S) (f T) ^ 2 = (symmDiff S T).card) :
    ∃ F : (Fin μ → ℝ) → Y, (∀ S : Finset (Fin μ), F (fun i => if i ∈ S then 1 else 0) = f S) ∧
      ∀ x y : Fin μ → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
        (∀ i, 0 ≤ y i ∧ y i ≤ 1) → dist (F x) (F y) ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  classical
  have key : ∀ k ≤ μ, ∃ F : (Fin μ → ℝ) → Y, (∀ x ∈ cubePts μ 0, F x = f (univ.filter fun i => x i = 1)) ∧
      ∀ x ∈ cubePts μ k, ∀ y ∈ cubePts μ k, dist (F x) (F y) ^ 2 = ∑ i, (x i - y i) ^ 2 := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun x => f (univ.filter fun i => x i = 1), fun _ _ => rfl, fun x hx y hy => ?_⟩
      rw [hf, card_eq_sum_ones, Nat.cast_sum, ← sum_filter_add_sum_filter_not univ
        (fun i => i ∈ symmDiff (univ.filter fun i => x i = 1) (univ.filter fun i => y i = 1))
        (fun i => (x i - y i) ^ 2)]
      rw [sum_eq_zero (s := univ.filter fun i => ¬ _), add_zero, filter_mem_eq_inter, univ_inter]
      · refine sum_congr rfl fun i hi => ?_
        simp only [mem_symmDiff, mem_filter, mem_univ, true_and] at hi
        rcases (hx i).2 (Nat.zero_le _) with h1 | h1 <;> rcases (hy i).2 (Nat.zero_le _) with h2 | h2
          <;> simp [h1, h2] at hi ⊢
      · intro i hi
        simp only [mem_filter, mem_univ, true_and, mem_symmDiff] at hi
        rcases (hx i).2 (Nat.zero_le _) with h1 | h1 <;> rcases (hy i).2 (Nat.zero_le _) with h2 | h2
          <;> simp [h1, h2] at hi ⊢
    | succ k ih =>
      intro hk
      obtain ⟨F, hF0, hF⟩ := ih (by omega)
      obtain ⟨F', hF'0, hF'⟩ := thm_alt_fill (by omega) F hF
      exact ⟨F', fun x hx => (hF'0 x fun i => ⟨(hx i).1, fun _ => (hx i).2 (Nat.zero_le _)⟩).trans (hF0 x hx), hF'⟩
  obtain ⟨F, hF0, hF⟩ := key μ le_rfl
  refine ⟨F, fun S => ?_, fun x y hx hy => hF x (fun i => ⟨hx i, fun h => ?_⟩) y (fun i => ⟨hy i, fun h => ?_⟩)⟩
  · rw [hF0 _ fun i => by by_cases hi : i ∈ S <;> simp [hi]]
    congr 1
    ext i
    by_cases hi : i ∈ S <;> simp [hi]
  · exact absurd i.2 (by omega)
  · exact absurd i.2 (by omega)

end Cube

theorem dg_sub_dg (S T : Finset (Fin μ)) : (dg S - dg T : Mt μ) = dg (symmDiff S T) := by
  ext i j
  simp only [dg, Matrix.sub_apply, Matrix.diagonal_apply, mem_symmDiff]
  by_cases hij : i = j
  · subst hij
    by_cases h3 : i ∈ S <;> by_cases h4 : i ∈ T <;> simp [h3, h4]
  · simp [hij]

/-- "The diagonal 0/1 matrices now form the vertices of a Euclidean cube [0,1]^μ in a price space." -/
theorem thm_alt_vertices (hrk : ∀ a a' : Mt μ, w a a' ^ 2 = (a - a').rank) (S T : Finset (Fin μ)) :
    w (dg S) (dg T) ^ 2 = (symmDiff S T).card := by
  rw [hrk, dg_sub_dg, rank_dg]

/-- "Every finite Euclidean configuration of dimension at most μ is, up to translation and scale, a subset of the cube,
hence a price." -/
theorem thm_alt_euclidean (hK : ¬ Contracting K) (hμ : 3 ≤ μ) {k : ℕ} (hk : k ≤ μ) (V : Type) [Finite V]
    (E : V → EuclideanSpace ℝ (Fin k)) : IsPrice K fun a b => dist (E a) (E b) := by
  obtain ⟨w, hw, hrk⟩ := thm_alt_rank_price hK hμ
  obtain ⟨Y, _, _, f, hY, hf⟩ := prop_space hw
  obtain ⟨F, -, hF⟩ := thm_alt_cube (Y := Y) (fun S => f (dg S))
    (fun S T => by rw [hf]; exact thm_alt_vertices hrk S T)
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ v i, |E v i| ≤ R := by
    cases nonempty_fintype V
    refine ⟨1 + ∑ v, ∑ i, |E v i|, ?_, fun v i => ?_⟩
    · have : 0 ≤ ∑ v, ∑ i, |E v i| := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
      linarith
    · have h1 := single_le_sum (f := fun i => |E v i|) (fun _ _ => abs_nonneg _) (mem_univ i)
      have h2 := single_le_sum (f := fun v => ∑ i, |E v i|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ v)
      simp only at h1 h2
      linarith
  let g : V → Fin μ → ℝ := fun v i => if hi : i.1 < k then (E v ⟨i.1, hi⟩ + R) / (2 * R) else 0
  have hg : ∀ v i, 0 ≤ g v i ∧ g v i ≤ 1 := by
    intro v i
    simp only [g]
    split_ifs with hi
    · have := abs_le.1 (hR v ⟨i.1, hi⟩)
      constructor
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]
        linarith
    · exact ⟨le_rfl, zero_le_one⟩
  have hdist : ∀ u v, dist (E u) (E v) = 2 * R * dist (F (g u)) (F (g v)) := by
    intro u v
    have h1 := hF (g u) (g v) (hg u) (hg v)
    have h2 : ∑ i, (g u i - g v i) ^ 2 = (1 / (2 * R)) ^ 2 * dist (E u) (E v) ^ 2 := by
      rw [EuclideanSpace.dist_eq, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _), mul_sum]
      have h3 : ∀ i : Fin μ, (g u i - g v i) ^ 2 = if hi : i.1 < k then
          (1 / (2 * R)) ^ 2 * dist (E u ⟨i.1, hi⟩) (E v ⟨i.1, hi⟩) ^ 2 else 0 := by
        intro i
        simp only [g]
        split_ifs with hi
        · rw [Real.dist_eq, sq_abs]
          field_simp
          ring
        · simp
      rw [sum_congr rfl fun i _ => h3 i]
      have h4 := Fin.sum_univ_eq_sum_range (fun j => if hj : j < k then
          (1 / (2 * R)) ^ 2 * dist (E u ⟨j, hj⟩) (E v ⟨j, hj⟩) ^ 2 else 0) μ
      have h5 := Fin.sum_univ_eq_sum_range (fun j => if hj : j < k then
          (1 / (2 * R)) ^ 2 * dist (E u ⟨j, hj⟩) (E v ⟨j, hj⟩) ^ 2 else 0) k
      rw [h4, sum_subset (s₁ := range k) (s₂ := range μ) (range_subset_range.2 hk)
        (fun j _ hj => by rw [mem_range] at hj; rw [dif_neg hj]) |>.symm, ← h5]
      refine sum_congr rfl fun i _ => ?_
      rw [dif_pos i.2]
    rw [h2] at h1
    have h3 : dist (F (g u)) (F (g v)) = 1 / (2 * R) * dist (E u) (E v) := by
      refine (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).1 ?_
      rw [h1, mul_pow]
    rw [h3]
    field_simp
  have h1 := (hY.comp fun v => F (g v)).smul (c := 2 * R) (by positivity)
  have e : (fun a b => dist (E a) (E b)) = fun a b => 2 * R * dist (F (g a)) (F (g b)) := by
    funext u v
    exact hdist u v
  rw [e]
  exact h1

/-- **Paper: Theorem thm:alt.** "One of the two cases occurs." -/
theorem thm_alt (K : Type) [Field K] : Flat K ∨ Contracting K := by
  by_cases hK : Contracting K
  · exact Or.inr hK
  · exact Or.inl fun k V _ E => thm_alt_euclidean hK (μ := k + 3) (by omega) (by omega) V E

end Paper
