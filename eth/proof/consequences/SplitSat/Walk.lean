/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitSat.Defs
import SplitSat.Leaf
import SplitSat.Sizes
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 5: s_3 = 0 implies s_k = 0 for every k ≥ 3, by the reduction that sparsifies and then splits every long clause into clauses of 3 literals with new variables, for machines cut into steps

`reduceCore_decides` holds for every step of a tree that sparsifies width k from the root `rootP`;
`stReduceCore` (= `SplitSat.StReduceCore`) is the case of the procedure behind the Lean form of
Lemma 4, run at width k.
The proof follows `Groundwork.Prog.SatTopK.sat_correct` (proof/consequences/WidthK/Top/Sat.lean)
with three changes. The nodes carry n in unary. There is no reader of the input, so all sizes are
bounded in n + 2; this uses that no clause is written twice. The cost of a leaf is given in n:
by `stLeaf` the 3-CNF of a leaf has N ≤ (1 + (k−3)·B)·n variables, so the procedure D takes at most
c·2^{δ₃N} ≤ c·2^{(δ/3)n} steps on it. There are at most 2^{(δ/3)n} leaves, so the walk takes at most
(c+2)·2^{(2δ/3)n} steps. -/

public section

namespace SplitSat

open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight.Width

/-- **The reduction is correct and fast, for every procedure D and every tree.** Let k ≥ 3 and δ >
0; let `step`, from the root `rootP`, sparsify width k with at most 2^{δn/3} leaves of at most B·n
clauses; let D decide 3-SAT with an exponent δ₃ ≥ 0 such that δ₃·(1 + (k−3)·B) ≤ δ/3. Then
`reduceCore step D` decides k-SAT with the exponent δ, in the sense of `DecidesW k`. -/
theorem reduceCore_decides {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {step : Fml → Option (Fml × Fml)} {Dd B Sk : ℕ}
    (hsp : Sparsifies k (δ / 3) step rootP Dd B Sk) (D : StepMachine (List Unit × Fml) Bool) {δ₃ : ℝ} {c : ℕ} (h0 : 0 ≤ δ₃)
    (hδB : δ₃ * (1 + ((k : ℝ) - 3) * B) ≤ δ / 3) (hD : Decides3 D δ₃ c) : ∃ c' : ℕ, DecidesW k (reduceCore step D) δ c' := by
  classical
  obtain ⟨R, hR⟩ : ∃ R, R = 1 + (k - 3) * B := ⟨_, rfl⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, P₀ = 2 ^ k * (2 * k + 1) + 3 := ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂, P₂ = (Dd + 1) * (2 ^ k * Sk * (2 * k + 1) + 4) + 1 := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = cOf P₂ P₀ R c (k + 2) := ⟨_, rfl⟩
  refine ⟨c', fun n ψ hψ hnd => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u : List Unit, u = List.replicate n () := ⟨_, rfl⟩
  obtain ⟨hb1, hb2⟩ := final_bound P₂ P₀ R c (k + 2) (n + 2) (by omega)
  rw [← hc'] at hb1 hb2
  have hm := length_le_of_nodup hψ hnd
  have hc2 : ((c : ℝ) + 2) ≤ (c' : ℝ) := by
    have : c + 2 ≤ c' := by rw [hc']; unfold cOf; omega
    exact_mod_cast this
  have hδn : 0 ≤ δ * (n : ℝ) := by positivity
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := Real.one_le_rpow one_le_two hδn
  have hnilψ : hasNil ψ = true ↔ [] ∈ ψ := by simp [hasNil, List.any_eq_true]
  by_cases hnil : [] ∈ ψ
  · refine ⟨1, false, ?_, ?_, ?_⟩
    · have r := Stepped.ite_runs_true (p := fun p : List Unit × Fml => hasNil p.2)
        (N := Stepped.walk (stepN step) (fun p : List Unit × Fml => ((p.1, rootP p.2) : NFml)) (Stepped.mapIn widthP D))
        (a := (List.replicate n (), ψ)) (hnilψ.2 hnil) (Stepped.const_runs false (List.replicate n (), ψ))
      refine r.mono le_rfl ?_
      have hs := size_node_le hm hψ
      have hp : (n + 2) ^ (k + 1) ≤ (n + 2) ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have hs2 := hs.trans (Nat.mul_le_mul_left _ hp)
      rw [← hP₀] at hs2
      rw [size_bool]
      omega
    · simp only [Bool.false_eq_true, false_iff]
      rintro ⟨a, ha⟩
      obtain ⟨l, hl, -⟩ := ha [] hnil
      simp at hl
    · have : (1 : ℝ) ≤ (c' : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) c]
      push_cast
      nlinarith
  · have hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
      intro C hC
      refine ⟨?_, hψ C hC⟩
      rintro rfl
      exact hnil hC
    obtain ⟨t1, t2, t3, t4⟩ := hsp n ψ hψne
    obtain ⟨L, hL⟩ : ∃ L, L = leaves step (Dd * n) (rootP ψ) := ⟨_, rfl⟩
    rw [← hL] at t1 t2 t3
    have hLN : leaves (stepN step) (Dd * n) ((u, rootP ψ) : NFml) = L.map fun y => ((u, y) : NFml) := by
      rw [hL]; exact leaves_stepN step u _ _
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 3 * n) := ⟨_, rfl⟩
    have hE0 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
    have hLE : (L.length : ℝ) ≤ E := by rw [hE]; exact t1
    have hA0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
    have hk' : ∀ y ∈ leaves (stepN step) (Dd * n) ((u, rootP ψ) : NFml), stepN step y = none := by
      rw [hLN]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      simp [stepN, (t2 x hx).1]
    have hT : ∀ y ∈ leaves (stepN step) (Dd * n) ((u, rootP ψ) : NFml),
        (Stepped.mapIn widthP D).Runs y ⌊(c : ℝ) * E⌋₊ (c * (R * (n + 2)) ^ c) (decide (Fml.Sat y.2)) := by
      rw [hLN]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      obtain ⟨-, hxl, hxc⟩ := t2 x hx
      rw [hu]
      obtain ⟨l1, l2, l3, l4⟩ := stLeaf k B n x hxc hxl
      obtain ⟨T, b, r, hb, hTle⟩ := hD _ _ l1 l2
      rw [← widthP_eq] at r
      have e : decide (Fml.Sat x) = b := by
        rw [Bool.eq_iff_iff, decide_eq_true_eq]
        exact (hb.trans l4).symm
      dsimp only
      rw [e]
      refine (Stepped.mapIn_runs r).mono (Nat.le_floor (hTle.trans ?_)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ c))
      · refine mul_le_mul_of_nonneg_left ?_ hA0
        rw [hE]
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have l3' : (((widthP (List.replicate n (), x)).1.length : ℕ) : ℝ) ≤ (1 + ((k : ℝ) - 3) * B) * n := by
          have := (Nat.cast_le (α := ℝ)).2 l3
          push_cast [Nat.cast_sub hk] at this
          exact this
        calc δ₃ * ((widthP (List.replicate n (), x)).1.length : ℕ) ≤ δ₃ * ((1 + ((k : ℝ) - 3) * B) * n) := mul_le_mul_of_nonneg_left l3' h0
          _ = δ₃ * (1 + ((k : ℝ) - 3) * B) * n := by ring
          _ ≤ δ / 3 * n := mul_le_mul_of_nonneg_right hδB (Nat.cast_nonneg n)
      · rw [← hR] at l3
        have hR1 : 1 ≤ R := by omega
        have a1 : R * (n + 2) = R * n + 2 * R := by ring
        omega
    have hS : ∀ i, size ((Sparsify.round (stepN step))^[i] ([((u, rootP ψ) : NFml)], [])).1 ≤ P₂ * (n + 2) ^ (k + 2) := by
      intro i
      obtain ⟨s1, s2⟩ := t4 i
      rw [stack_stepN, hu, hP₂]
      refine size_stack_le s1 fun x hx => ⟨(s2 x hx).1.trans ?_, (s2 x hx).2⟩
      calc ψ.length * Sk ≤ 2 ^ k * (n + 2) ^ k * Sk := Nat.mul_le_mul_right _ hm
        _ = 2 ^ k * Sk * (n + 2) ^ k := by ring
    have w := Stepped.walk_runs (stepN step) (root := fun p : List Unit × Fml => ((p.1, rootP p.2) : NFml)) (T := Stepped.mapIn widthP D)
      (Dd * n) (u, ψ) hk' (fun y => decide (Fml.Sat y.2)) ⌊(c : ℝ) * E⌋₊ (c * (R * (n + 2)) ^ c) (P₂ * (n + 2) ^ (k + 2)) hT hS
    rw [hLN] at w
    rw [hu] at w
    refine ⟨(L.map fun y => ((List.replicate n (), y) : NFml)).length * (⌊(c : ℝ) * E⌋₊ + 2), _,
      (Stepped.ite_runs_false (by simpa using fun h => hnil (hnilψ.1 h)) w).mono le_rfl (by omega), ?_, ?_⟩
    · simp only [List.any_map, List.any_eq_true, Function.comp_apply, decide_eq_true_eq]
      constructor
      · rintro ⟨x, hx, a, ha⟩
        exact ⟨a, (t3 fun l => a l.1 = l.2).2 ⟨x, hx, ha⟩⟩
      · rintro ⟨a, ha⟩
        obtain ⟨x, hx, h⟩ := (t3 fun l => a l.1 = l.2).1 ha
        exact ⟨x, hx, a, h⟩
    · have hfl : ((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (c : ℝ) * E := Nat.floor_le (by positivity)
      have hEE : E * E ≤ (2 : ℝ) ^ (δ * n) := by
        rw [hE, ← Real.rpow_add two_pos]
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        nlinarith
      have hE00 : 0 ≤ E := by linarith
      rw [List.length_map]
      push_cast
      calc (L.length : ℝ) * (((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) + 2)
          ≤ E * ((c : ℝ) * E + 2 * E) := mul_le_mul hLE (by linarith) (by positivity) hE00
        _ = ((c : ℝ) + 2) * (E * E) := by ring
        _ ≤ (c' : ℝ) * (2 : ℝ) ^ (δ * n) := mul_le_mul hc2 hEE (by positivity) (Nat.cast_nonneg _)

/-- **The reduction is correct and fast, for every procedure D**, on the tree of the procedure
behind the Lean form of Lemma 4, run at width k: the statement `SplitSat.StReduceCore`. -/
theorem stReduceCore : StReduceCore := fun _ hk _ hδ _ _ _ _ hsp D _ _ h0 hδB hD => reduceCore_decides hk hδ hsp D h0 hδB hD

end SplitSat
