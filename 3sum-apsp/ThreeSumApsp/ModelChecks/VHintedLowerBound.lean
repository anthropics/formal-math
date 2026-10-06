/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Machine.Footprint
public import ThreeSumApsp.ModelChecks.Counting

/-!
# Phase 3 of v-hinted Mv needs linear time on the word RAM

A check of the definition of a problem that is solved in phases (Section 5.4): it cannot be met for
free. The `n` output cells depend on the index that arrives in Phase 3, and a step writes one cell
(`WordRam.changed_cells`).  Take all entries of `M` equal to 1, column 0 of `V` all 1 and its
other columns all 0.  For the indices 0 and 1 the first two phases are the same runs, and the
outputs differ in all `n` cells; but two runs of Phase 3 that together take fewer than `n` steps
leave one output cell as it was.
-/

public section

open ThreeSumApsp.WordRam

namespace ThreeSumApsp

/-- The hint dimension is at least 1. -/
private theorem one_le_hintSize {τ : ℝ} (h0 : 0 ≤ τ) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ hintSize τ n := by
  unfold hintSize
  rw [Nat.one_le_floor_iff]
  exact Real.one_le_rpow (by exact_mod_cast hn) h0

/-- All entries of `M` are 1 and column 0 of `V` is all 1: the output for the index 0 is all 1. -/
private theorem output_zero {n t : ℕ} (ht : 1 ≤ t) (h0 : 0 < n) (r : Fin n) :
    HintedMv.vHintedOutput (fun _ _ => true : Matrix (Fin n) (Fin t) Bool)
      (fun _ j => decide (j.val = 0)) ⟨0, h0⟩ r = true := by
  simp only [HintedMv.vHintedOutput, HintedMv.boolMul, decide_eq_true_eq]
  exact ⟨⟨0, by omega⟩, trivial, by simp⟩

/-- The other columns of `V` are all 0: the output for the index 1 is all 0. -/
private theorem output_one {n t : ℕ} (h1 : 1 < n) (r : Fin n) :
    HintedMv.vHintedOutput (fun _ _ => true : Matrix (Fin n) (Fin t) Bool)
      (fun _ j => decide (j.val = 0)) ⟨1, h1⟩ r = false := by
  simp only [HintedMv.vHintedOutput, HintedMv.boolMul, decide_eq_false_iff_not]
  rintro ⟨k, -, hk⟩
  simp at hk

/-- Whatever is prepared in Phases 1 and 2, Phase 3 of v-hinted Mv takes linear time. -/
theorem not_achievesVHinted (τ a₂ a₃ : ℝ) (hτ : 0 ≤ τ) (ha : a₃ < 1) :
    ¬ AchievesVHinted τ a₂ a₃ := by
  rintro ⟨P₁, P₂, P₃, b, C, a₁, h⟩
  -- a size at which twice the time bound of Phase 3 is below the number of output cells
  obtain ⟨n, hn3, hlt⟩ := WordRam.exists_sublinear_bound_lt ha 0 C
  have hn1 : 1 ≤ n := by omega
  have ht1 := one_le_hintSize hτ hn1
  set t := hintSize τ n with ht
  set bits : ℕ := b * (([n].map Nat.log2).sum + 1) with hbits
  -- all entries of M are 1; column 0 of V is all 1, the other columns are all 0
  let M : Matrix (Fin n) (Fin t) Bool := fun _ _ => true
  let V : Matrix (Fin t) (Fin n) Bool := fun _ j => decide (j.val = 0)
  obtain ⟨s₁, s₂, s₃, -, -, w₃, c₁, e₁, c₂, e₂, c₃, e₃, hout⟩ :=
    h n hn1 M V ⟨0, by omega⟩ bits le_rfl
  obtain ⟨s₁', s₂', s₃', -, -, w₃', c₁', e₁', c₂', e₂', c₃', e₃', hout'⟩ :=
    h n hn1 M V ⟨1, by omega⟩ bits le_rfl
  -- the first two phases are the same runs
  obtain rfl : c₁ = c₁' := (Prod.mk.inj (WordRam.exec_unique (c := ⟨0, _⟩) e₁ e₁')).2
  obtain rfl : c₂ = c₂' := (Prod.mk.inj (WordRam.exec_unique (c := ⟨0, _⟩) e₂ e₂')).2
  -- the cells that Phase 3 changes
  obtain ⟨S, hS, hkeep⟩ := WordRam.changed_cells P₃ s₃ ⟨0, withInput c₂ _ _⟩ _ _ e₃
  obtain ⟨S', hS', hkeep'⟩ := WordRam.changed_cells P₃ s₃' ⟨0, withInput c₂ _ _⟩ _ _ e₃'
  have hb : ∀ s : ℕ, Within s C n a₃ → 2 * (s : ℝ) + 2 < (n : ℝ) := fun s w => by
    have h2 : (s : ℝ) ≤ C * ((n : ℝ) ^ a₃ + 1) := w
    simp only [pow_zero, mul_one] at hlt
    linarith
  have hsum : s₃ + s₃' < n := by
    have h1 := hb s₃ w₃
    have h2 := hb s₃' w₃'
    have : (s₃ : ℝ) + (s₃' : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast this
  -- an output cell that neither run changes
  generalize hoff : 0 + ([(n : ℤ), (t : ℤ)] ++ rowMajor (HintedMv.toInt M)).length +
    (rowMajor (HintedMv.toInt V)).length = off at e₃ e₃' hout hout' hkeep hkeep'
  obtain ⟨r, hr, hnot⟩ := WordRam.exists_offset_notMem (S := S ∪ S') (n := n)
    ((Finset.card_union_le S S').trans_lt (by omega)) ((off + 1 : ℕ) : ℤ)
  obtain ⟨hnotS, hnotS'⟩ := not_or.1 (mt Finset.mem_union.2 hnot)
  have k1 : c₃ _ = withInput c₂ off _ _ := hkeep.cell (mt Finset.mem_coe.1 hnotS)
  have k2 : c₃' _ = withInput c₂ off _ _ := hkeep'.cell (mt Finset.mem_coe.1 hnotS')
  -- before Phase 3 the cell is the same in both runs: it is not the cell of the index
  have hsame :
      withInput c₂ off [((⟨0, by omega⟩ : Fin n).val : ℤ)] (((off + 1 : ℕ) : ℤ) + (r : ℤ)) =
        withInput c₂ off [((⟨1, by omega⟩ : Fin n).val : ℤ)] (((off + 1 : ℕ) : ℤ) + (r : ℤ)) := by
    unfold withInput
    simp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil]; push_cast; omega),
      if_neg (by simp only [List.length_cons, List.length_nil]; push_cast; omega)]
  have o1 := hout ⟨r, hr⟩
  have o2 := hout' ⟨r, hr⟩
  simp only [List.length_cons, List.length_nil, output] at o1 o2
  rw [k1] at o1
  rw [k2, ← hsame] at o2
  rw [o1] at o2
  -- the two outputs differ
  rw [show HintedMv.vHintedOutput M V ⟨0, by omega⟩ ⟨r, hr⟩ = true from output_zero ht1 _ _,
    show HintedMv.vHintedOutput M V ⟨1, by omega⟩ ⟨r, hr⟩ = false from output_one _ _] at o2
  simp [bit] at o2

end ThreeSumApsp
