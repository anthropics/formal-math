/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblems.Blocks

/-! # Corollary 7: the formula of the colorings

The satisfying assignments of `colorF k n (matrix G)` on n·k variables correspond to the proper
colorings of G with the colors 0 … k−1: the variable x_{v·k+c} is true if and only if the vertex v
has
the color c. That the entries of the matrix are the adjacencies of G is taken as a hypothesis
(`StAdj`). -/

public section

namespace GraphProblems

open Groundwork Groundwork.Prog CountKSat Finset

namespace Color

open Blocks

theorem mem_pairs {n : ℕ} {p : ℕ × ℕ} : p ∈ pairs n ↔ p.1 < n ∧ p.2 < n := by
  rw [pairs, List.mem_product, List.mem_range, List.mem_range]

theorem idx_lt {n k v c : ℕ} (hv : v < n) (hc : c < k) : v * k + c < n * k :=
  calc v * k + c < (v + 1) * k := by rw [Nat.succ_mul]; omega
    _ ≤ n * k := Nat.mul_le_mul_right k hv

/-- A clause of two literals. -/
theorem exists_mem_pair (f : ℕ → Bool) (l₁ l₂ : ℕ × Bool) : (∃ l ∈ [l₁, l₂], f l.1 = l.2) ↔ f l₁.1 = l₁.2 ∨ f l₂.1 = l₂.2 := by
  simp

/-- What `colorF k n m` says. -/
theorem sat_colorF (k n : ℕ) (m : List Bool) (f : ℕ → Bool) : Sat f (colorF k n m) ↔
    (∀ v < n, ∃ c < k, f (v * k + c) = true) ∧
    (∀ v < n, ∀ c₁ < k, ∀ c₂ < k, c₁ < c₂ → f (v * k + c₁) = false ∨ f (v * k + c₂) = false) ∧
    ∀ u < n, ∀ v < n, adjB n m u v = true → ∀ c < k, f (u * k + c) = false ∨ f (v * k + c) = false := by
  rw [colorF, sat_append, sat_append, and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro h v hv
      obtain ⟨l, hl, hfl⟩ := h _ (List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩)
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl
      exact ⟨c, List.mem_range.1 hc, hfl⟩
    · intro h C hC
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hC
      obtain ⟨c, hc, hf⟩ := h v (List.mem_range.1 hv)
      exact ⟨_, List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩, hf⟩
  · constructor
    · intro h v hv c₁ h1 c₂ h2 h12
      exact (exists_mem_pair f _ _).1 (h _ (List.mem_flatMap.2 ⟨v, List.mem_range.2 hv,
        List.mem_map.2 ⟨(c₁, c₂), List.mem_filter.2 ⟨mem_pairs.2 ⟨h1, h2⟩, decide_eq_true h12⟩, rfl⟩⟩))
    · intro h C hC
      obtain ⟨v, hv, hC⟩ := List.mem_flatMap.1 hC
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hC
      obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
      exact (exists_mem_pair f _ _).2 (h v (List.mem_range.1 hv) q.1 (mem_pairs.1 hq1).1 q.2 (mem_pairs.1 hq1).2 (of_decide_eq_true hq2))
  · constructor
    · intro h u hu v hv huv c hc
      exact (exists_mem_pair f _ _).1 (h _ (List.mem_flatMap.2 ⟨(u, v), List.mem_filter.2 ⟨mem_pairs.2 ⟨hu, hv⟩, huv⟩,
        List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩⟩))
    · intro h C hC
      obtain ⟨p, hp, hC⟩ := List.mem_flatMap.1 hC
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hC
      obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
      exact (exists_mem_pair f _ _).2 (h p.1 (mem_pairs.1 hp1).1 p.2 (mem_pairs.1 hp1).2 hp2 c (List.mem_range.1 hc))

/-- The assignment of a map from the vertices to the colors: x_{v·k+c} is true if and only if v has
the color c. -/
def asg {n k : ℕ} (col : Fin n → Fin k) (x : Fin (n * k)) : Bool :=
  decide ((col ⟨x.val / k, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq x.2 (mul_comm n k))⟩).val = x.val % k)

theorem ext_asg {n k : ℕ} (col : Fin n → Fin k) (v : Fin n) {c : ℕ} (hc : c < k) : ext (asg col) (v * k + c) = decide ((col v).val = c) := by
  have h1 : (v.val * k + c) / k = v.val := by
    rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hc, add_zero]
  have h2 : (v.val * k + c) % k = c := by
    rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
  rw [CountKSat.ext, dif_pos (idx_lt v.2 hc), asg]
  simp only [h1, h2]

/-- The assignment of a proper coloring satisfies the formula. -/
theorem sat_asg (hAdj : StAdj) {n k : ℕ} (G : SimpleGraph (Fin n)) (col : G.Coloring (Fin k)) : Sat (ext (asg col)) (colorF k n (matrix G)) := by
  rw [sat_colorF]
  refine ⟨fun v hv => ⟨col ⟨v, hv⟩, (col ⟨v, hv⟩).2, ?_⟩, fun v hv c₁ h1 c₂ h2 h12 => ?_, fun u hu v hv huv c hc => ?_⟩
  · rw [ext_asg col ⟨v, hv⟩ (col ⟨v, hv⟩).2, decide_eq_true rfl]
  · rw [ext_asg col ⟨v, hv⟩ h1, ext_asg col ⟨v, hv⟩ h2, decide_eq_false_iff_not, decide_eq_false_iff_not]
    omega
  · have h3 : col ⟨u, hu⟩ ≠ col ⟨v, hv⟩ := col.valid ((hAdj n G ⟨u, hu⟩ ⟨v, hv⟩).1 huv)
    have h4 : (col ⟨u, hu⟩).val ≠ (col ⟨v, hv⟩).val := fun h => h3 (Fin.ext h)
    rw [ext_asg col ⟨u, hu⟩ hc, ext_asg col ⟨v, hv⟩ hc, decide_eq_false_iff_not, decide_eq_false_iff_not]
    omega

/-- Different maps have different assignments. -/
theorem asg_injective {n k : ℕ} : Function.Injective (asg : (Fin n → Fin k) → Fin (n * k) → Bool) := by
  intro col col' h
  funext v
  have h1 := ext_asg col v (col v).2
  rw [h, ext_asg col' v (col v).2, decide_eq_true (rfl : (col v).val = (col v).val)] at h1
  exact (Fin.ext (of_decide_eq_true h1)).symm

/-- Every satisfying assignment is the assignment of a proper coloring. -/
theorem exists_coloring (hAdj : StAdj) {n k : ℕ} (G : SimpleGraph (Fin n)) (a : Fin (n * k) → Bool) (ha : Sat (ext a) (colorF k n (matrix G))) :
    ∃ col : G.Coloring (Fin k), asg col = a := by
  obtain ⟨h1, h2, h3⟩ := (sat_colorF k n (matrix G) (ext a)).1 ha
  choose c hc hf using fun v : Fin n => h1 v v.2
  have huniq : ∀ (v : Fin n) (c' : ℕ), c' < k → c' ≠ c v → ext a (v * k + c') = false := by
    intro v c' hc' hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · rcases h2 v v.2 c' hc' (c v) (hc v) hlt with h | h
      · exact h
      · rw [hf v] at h
        cases h
    · rcases h2 v v.2 (c v) (hc v) c' hc' hgt with h | h
      · rw [hf v] at h
        cases h
      · exact h
  refine ⟨SimpleGraph.Coloring.mk (fun v => ⟨c v, hc v⟩) ?_, ?_⟩
  · intro u v huv heq
    have h4 : c u = c v := congrArg Fin.val heq
    rcases h3 u u.2 v v.2 ((hAdj n G u v).2 huv) (c u) (hc u) with h | h
    · rw [hf u] at h
      cases h
    · rw [h4, hf v] at h
      cases h
  · funext x
    have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by
      have h4 := x.2
      have h5 : n * k = 0 := by rw [h0, mul_zero]
      omega
    have hv : x.val / k < n := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq x.2 (mul_comm n k))
    have hx : x.val = (⟨x.val / k, hv⟩ : Fin n).val * k + x.val % k := (Nat.div_add_mod' x.val k).symm
    have h5 := ext_asg (fun v => (⟨c v, hc v⟩ : Fin k)) ⟨x.val / k, hv⟩ (Nat.mod_lt x.val hk)
    rw [← hx, ext_val] at h5
    change asg (fun v => (⟨c v, hc v⟩ : Fin k)) x = a x
    rw [h5, ← ext_val a x]
    by_cases h6 : c ⟨x.val / k, hv⟩ = x.val % k
    · rw [decide_eq_true h6]
      have h7 := hf ⟨x.val / k, hv⟩
      rw [h6, ← hx] at h7
      exact h7.symm
    · rw [decide_eq_false h6]
      have h7 := huniq ⟨x.val / k, hv⟩ (x.val % k) (Nat.mod_lt x.val hk) (Ne.symm h6)
      rw [← hx] at h7
      exact h7.symm

end Color

open Blocks Color in
/-- The formula `colorF k n (matrix G)` has as many satisfying assignments as G has proper colorings
with k colors. -/
theorem stColor (hAdj : StAdj) : StColor := by
  intro k n G
  rw [numColorings, cntN, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  have hmem : ∀ col : G.Coloring (Fin k),
      asg col ∈ univ.filter fun a : Fin (n * k) → Bool => ∀ C ∈ colorF k n (matrix G), ∃ l ∈ C, CountKSat.ext a l.1 = l.2 :=
    fun col => mem_filter.2 ⟨mem_univ _, sat_asg hAdj G col⟩
  refine (Nat.card_congr (Equiv.ofBijective (fun col : G.Coloring (Fin k) => (⟨asg col, hmem col⟩ :
    {a // a ∈ univ.filter fun a : Fin (n * k) → Bool => ∀ C ∈ colorF k n (matrix G), ∃ l ∈ C, CountKSat.ext a l.1 = l.2})) ⟨?_, ?_⟩)).symm
  · intro col col' h
    exact DFunLike.coe_injective (asg_injective (congrArg Subtype.val h))
  · rintro ⟨a, ha⟩
    obtain ⟨col, hcol⟩ := exists_coloring hAdj G a (mem_filter.1 ha).2
    exact ⟨col, Subtype.ext hcol⟩

open Color in
/-- Width and variables of the formula of the colorings. -/
theorem stShapeColor : StShapeColor := by
  intro k n m C hC
  rw [colorF] at hC
  rcases List.mem_append.1 hC with hC | hC
  · rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hC
      refine ⟨by rw [List.length_map, List.length_range]; exact le_max_left _ _, fun l hl => ?_⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl
      exact idx_lt (List.mem_range.1 hv) (List.mem_range.1 hc)
    · obtain ⟨v, hv, hC⟩ := List.mem_flatMap.1 hC
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hC
      have hq1 := mem_pairs.1 (List.mem_filter.1 hq).1
      refine ⟨le_max_right _ _, fun l hl => ?_⟩
      rcases List.mem_pair.1 hl with rfl | rfl
      · exact idx_lt (List.mem_range.1 hv) hq1.1
      · exact idx_lt (List.mem_range.1 hv) hq1.2
  · obtain ⟨p, hp, hC⟩ := List.mem_flatMap.1 hC
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hC
    have hp1 := mem_pairs.1 (List.mem_filter.1 hp).1
    refine ⟨le_max_right _ _, fun l hl => ?_⟩
    rcases List.mem_pair.1 hl with rfl | rfl
    · exact idx_lt hp1.1 (List.mem_range.1 hc)
    · exact idx_lt hp1.2 (List.mem_range.1 hc)

/-- A graph can be colored with k colors if and only if its number of proper colorings with k colors
is not 0. -/
theorem stDecideColor : StDecideColor := by
  intro k n G
  have : Finite (G.Coloring (Fin k)) := Finite.of_injective (fun col : G.Coloring (Fin k) => (col : Fin n → Fin k)) DFunLike.coe_injective
  rw [numColorings, Nat.card_ne_zero]
  exact ⟨fun h => ⟨h, this⟩, fun h => h.1⟩

end GraphProblems
