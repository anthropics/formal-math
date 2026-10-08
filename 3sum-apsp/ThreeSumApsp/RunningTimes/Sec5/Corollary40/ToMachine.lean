/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Phases
public import ThreeSumApsp.Lang.RowMajor
public import ThreeSumApsp.Sec5.Corollary40

/-!
# The three hinted problems: from a program that runs in phases to the word RAM

`AchievesVHinted`, `AchievesMvHinted` and `AchievesUMvHinted` (Section 5.4) ask for one program of
the word RAM for each phase, a slope, a constant, and an exponent for the polynomial time of
Phase 1.  The three theorems of this file produce them from one program of the small language with
one procedure for each phase.  What is left to show for a concrete program is, for every n ≥ 1 and
all inputs, a run in phases (`LightPhases`) within limits that are polynomial in n, and bounds
A (n^a + 1) on the numbers of steps: the structure `PhaseRun`.

The route is `PhaseRun.compile`.  The phases are compiled (`runsPhases_start`), and a compiled phase
takes a constant times as long as the phase (`within_ramSteps`).  This needs that every number of
the inputs fits in a word, which is shown for each problem (`absLe_rowMajor_toInt`,
`absLe_ofFn_fin`, `absLe_singleton_fin`).
-/

public section

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.HintedMv

/-! ## The numbers of the inputs fit in a word -/

/-- The numbers of a Boolean matrix are 0 and 1. -/
theorem absLe_rowMajor_toInt {l m : ℕ} (M : Matrix (Fin l) (Fin m) Bool) {B : ℤ} (hB : 1 ≤ B) :
    AbsLe (rowMajor (toInt M)) B := by
  intro v hv
  obtain ⟨i, j, rfl⟩ := mem_rowMajor hv
  exact (Corollary40.abs_toInt_le M i j).trans hB

/-- An index is below `n`. -/
theorem absLe_singleton_fin {n : ℕ} (i : Fin n) {B : ℤ} (hB : (n : ℤ) ≤ B) :
    AbsLe [(i.val : ℤ)] B := by
  have : (i.val : ℤ) ≤ n := by exact_mod_cast i.isLt.le
  simpa [AbsLe] using this.trans hB

/-- The entries of a vector of indices are below `n`. -/
theorem absLe_ofFn_fin {t n : ℕ} (I : Fin t → Fin n) {B : ℤ} (hB : (n : ℤ) ≤ B) :
    AbsLe (List.ofFn fun k => ((I k).val : ℤ)) B := by
  intro v hv
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hv
  exact absLe_singleton_fin (I k) hB _ (List.mem_singleton.2 rfl)

/-! ## The three problems -/

/-- **v-hinted Mv.**  If for every n ≥ 1 and all inputs the procedures p₁, p₂, p₃ of P run the three
phases within limits that are polynomial in n, in at most A (n^a₁ + 1), A (n^a₂ + 1) and A (n^a₃ +
1) steps, and leave column i of M V in the output cells, then the compiled procedures solve the
problem with Phase 2 in O(n^a₂) and Phase 3 in O(n^a₃) time. -/
theorem achievesVHinted_of_light {τ a₁ a₂ a₃ A : ℝ} (P : Program) (p₁ p₂ p₃ s k : ℕ)
    (h : ∀ n : ℕ, 1 ≤ n → ∀ (M : Matrix (Fin n) (Fin (hintSize τ n)) Bool)
      (V : Matrix (Fin (hintSize τ n)) (Fin n) Bool) (i : Fin n),
      ∃ (lim : Limits) (c₁ c₂ c₃ : ℕ), PhaseRun lim P s k A n [n, hintSize τ n]
        (fun μ off => ∀ r : Fin n, μ (off + r.val) = bit (vHintedOutput M V i r))
        [(p₁, [(n : ℤ), (hintSize τ n : ℤ)] ++ rowMajor (toInt M), c₁),
          (p₂, rowMajor (toInt V), c₂), (p₃, [(i.val : ℤ)], c₃)] [a₁, a₂, a₃]) :
    AchievesVHinted τ a₂ a₃ := by
  refine ⟨compileProgram P p₁ false, compileProgram P p₂ false, compileProgram P p₃ false,
    slopeOf P false s k 1, (timeConst P false : ℝ) * (A + 1), a₁, fun n hn M V i bits hadm => ?_⟩
  obtain ⟨lim, c₁, c₂, c₃, hrun⟩ := h n hn M V i
  obtain ⟨hnw, htw⟩ : (n : ℤ) ≤ lim.word ∧ (hintSize τ n : ℤ) ≤ lim.word := by
    simpa using hrun.sizes_le
  have h1w : (1 : ℤ) ≤ lim.word := le_trans (by exact_mod_cast hn) hnw
  refine (hrun.compile hadm ?_ fun c off μ hg ho (r : Fin n) => (ho r).trans (hg r)).elim
    fun hsteps hphases => ?_
  · -- every number of the inputs fits in a word
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl)
    · exact .append (by simp [AbsLe, hnw, htw]) (absLe_rowMajor_toInt M h1w)
    · exact absLe_rowMajor_toInt V h1w
    · exact absLe_singleton_fin i hnw
  · simp only [List.forall₂_cons, List.forall₂_nil_left_iff, and_true] at hsteps
    obtain ⟨b₁, b₂, b₃⟩ := hsteps
    exact ⟨_, _, _, b₁, b₂, b₃, hphases⟩

/-- **Mv-hinted Mv.**  If the procedures p₁, p₂, p₃ of P run the three phases of Mv-hinted Mv as in
`achievesVHinted_of_light` and leave column j of N_{[n],I} V in the output cells, then the compiled
procedures solve the problem with Phase 2 in O(n^a₂) and Phase 3 in O(n^a₃) time. -/
theorem achievesMvHinted_of_light {τ a₁ a₂ a₃ A : ℝ} (P : Program) (p₁ p₂ p₃ s k : ℕ)
    (h : ∀ n : ℕ, 1 ≤ n → ∀ (N : Matrix (Fin n) (Fin n) Bool)
      (V : Matrix (Fin (hintSize τ n)) (Fin n) Bool) (I : Fin (hintSize τ n) → Fin n) (j : Fin n),
      ∃ (lim : Limits) (c₁ c₂ c₃ : ℕ), PhaseRun lim P s k A n [n, hintSize τ n]
        (fun μ off => ∀ r : Fin n, μ (off + r.val) = bit (MvHintedOutput N V I j r))
        [(p₁, [(n : ℤ), (hintSize τ n : ℤ)] ++ rowMajor (toInt N) ++ rowMajor (toInt V), c₁),
          (p₂, List.ofFn fun k => ((I k).val : ℤ), c₂), (p₃, [(j.val : ℤ)], c₃)] [a₁, a₂, a₃]) :
    AchievesMvHinted τ a₂ a₃ := by
  refine ⟨compileProgram P p₁ false, compileProgram P p₂ false, compileProgram P p₃ false,
    slopeOf P false s k 1, (timeConst P false : ℝ) * (A + 1), a₁, fun n hn N V I j bits hadm => ?_⟩
  obtain ⟨lim, c₁, c₂, c₃, hrun⟩ := h n hn N V I j
  obtain ⟨hnw, htw⟩ : (n : ℤ) ≤ lim.word ∧ (hintSize τ n : ℤ) ≤ lim.word := by
    simpa using hrun.sizes_le
  have h1w : (1 : ℤ) ≤ lim.word := le_trans (by exact_mod_cast hn) hnw
  refine (hrun.compile hadm ?_ fun c off μ hg ho (r : Fin n) => (ho r).trans (hg r)).elim
    fun hsteps hphases => ?_
  · -- every number of the inputs fits in a word
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl)
    · exact .append (.append (by simp [AbsLe, hnw, htw]) (absLe_rowMajor_toInt N h1w))
        (absLe_rowMajor_toInt V h1w)
    · exact absLe_ofFn_fin I hnw
    · exact absLe_singleton_fin j hnw
  · simp only [List.forall₂_cons, List.forall₂_nil_left_iff, and_true] at hsteps
    obtain ⟨b₁, b₂, b₃⟩ := hsteps
    exact ⟨_, _, _, b₁, b₂, b₃, hphases⟩

/-- **uMv-hinted uMv.**  If the procedures p₁, …, p₄ of P run the four phases of uMv-hinted uMv as
in `achievesVHinted_of_light` and leave the bit (U N_{I,J} V)_{i,j} in the first output cell, then
the compiled procedures solve the problem with Phases 2, 3, 4 in O(n^a₂), O(n^a₃), O(n^a₄) time. -/
theorem achievesUMvHinted_of_light {τ₁ τ₂ a₁ a₂ a₃ a₄ A : ℝ} (P : Program) (p₁ p₂ p₃ p₄ s k : ℕ)
    (h : ∀ n : ℕ, 1 ≤ n → ∀ (U : Matrix (Fin n) (Fin (hintSize τ₁ n)) Bool)
      (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin (hintSize τ₂ n)) (Fin n) Bool)
      (I : Fin (hintSize τ₁ n) → Fin n) (J : Fin (hintSize τ₂ n) → Fin n) (i j : Fin n),
      ∃ (lim : Limits) (c₁ c₂ c₃ c₄ : ℕ),
        PhaseRun lim P s k A n [n, hintSize τ₁ n, hintSize τ₂ n]
          (fun μ off => μ (off + 0) = bit (uMvHintedOutput U N V I J i j))
          [(p₁, [(n : ℤ), (hintSize τ₁ n : ℤ), (hintSize τ₂ n : ℤ)] ++ rowMajor (toInt U)
              ++ rowMajor (toInt N) ++ rowMajor (toInt V), c₁),
            (p₂, List.ofFn fun k => ((I k).val : ℤ), c₂),
            (p₃, List.ofFn fun k => ((J k).val : ℤ), c₃), (p₄, [(i.val : ℤ), (j.val : ℤ)], c₄)]
          [a₁, a₂, a₃, a₄]) :
    AchievesUMvHinted τ₁ τ₂ a₂ a₃ a₄ := by
  refine ⟨compileProgram P p₁ false, compileProgram P p₂ false, compileProgram P p₃ false,
    compileProgram P p₄ false, slopeOf P false s k 1, (timeConst P false : ℝ) * (A + 1), a₁,
    fun n hn U N V I J i j bits hadm => ?_⟩
  obtain ⟨lim, c₁, c₂, c₃, c₄, hrun⟩ := h n hn U N V I J i j
  obtain ⟨hnw, ht₁, ht₂⟩ : (n : ℤ) ≤ lim.word ∧ (hintSize τ₁ n : ℤ) ≤ lim.word ∧
      (hintSize τ₂ n : ℤ) ≤ lim.word := by simpa using hrun.sizes_le
  have h1w : (1 : ℤ) ≤ lim.word := le_trans (by exact_mod_cast hn) hnw
  refine (hrun.compile hadm ?_ fun c off μ hg ho => (ho 0).trans hg).elim fun hsteps hphases => ?_
  · -- every number of the inputs fits in a word
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl)
    · exact .append (.append (.append (by simp [AbsLe, hnw, ht₁, ht₂])
        (absLe_rowMajor_toInt U h1w)) (absLe_rowMajor_toInt N h1w)) (absLe_rowMajor_toInt V h1w)
    · exact absLe_ofFn_fin I hnw
    · exact absLe_ofFn_fin J hnw
    · exact .append (absLe_singleton_fin i hnw) (absLe_singleton_fin j hnw)
  · simp only [List.forall₂_cons, List.forall₂_nil_left_iff, and_true] at hsteps
    obtain ⟨b₁, b₂, b₃, b₄⟩ := hsteps
    exact ⟨_, _, _, _, b₁, b₂, b₃, b₄, hphases⟩

end Light.Sec5
