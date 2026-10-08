/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary39.GraphH.Fill
public import ThreeSumApsp.Spec.Sec5.Corollary39.AuxiliaryGraph

/-!
# Corollary 39 in the light language: from the memory to the graph H

Proof of Corollary 39: "every edge of a k-clique is counted exactly once over the three edges of its
triangle". The program adds up cells of the memory over a list of pairs of numbers of parts, for a
choice of vertices that two odometers run through.  This file says what these sums are.  The list of
the program has the pairs of parts of the weight of an edge of H, the smaller part first (`pairsN`,
`pairsN_valid`).  If the weights of G stand in the memory (`WeightsAt`), the sum over this list is
the sum of the weights of G (`memSum_eq_pairSum`), and it is at most the number of pairs times the
bound on the weights (`memSum_abs_le`).  The choices that the odometers run through while one of the
three matrices is filled are the cliques given by four numbers (`choiceAt_AB`, `choiceAt_BC`,
`choiceAt_AC`, `withDigits_fixed`).
-/

@[expose] public section

open ThreeSumApsp.Spec

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.KClique

/-! ## The list of pairs in the text of the program -/

/-- The pairs of parts as pairs of numbers, for the text of the program, each with the smaller part
first: the program reads the weight between two parts p < q in the block (p, q) only. -/
def pairsN (k : ℕ) (i : Fin 3) : List (ℕ × ℕ) :=
  (pairsH k i).map fun pq => (min (pq.1 : ℕ) pq.2, max (pq.1 : ℕ) pq.2)

/-- The list of pairs, written with natural numbers, is as long as the list of pairs. -/
@[simp] theorem length_pairsN (k : ℕ) (i : Fin 3) :
    (pairsN k i).length = (pairsH k i).length := by
  simp [pairsN]

/-- The two parts of a pair are different. -/
theorem pairsH_ne (k : ℕ) (i : Fin 3) : ∀ pq ∈ pairsH k i, (pq.1 : ℕ) ≠ pq.2 := by
  intro pq hpq
  have hfixed (a : Fin (numFixed k)) : ((fixedPart a : Fin k) : ℕ) = a := rfl
  simp only [pairsH, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq] at hpq
  rcases hpq with ((⟨j, j', rfl⟩ | ⟨j, j', hlt, rfl⟩) | ⟨a, j, rfl⟩) | hpq
  · -- a part of group i and a part of group i + 1
    have := j.2
    have := j'.2
    fin_cases i <;> simp [groupPart] <;> omega
  · -- two parts of group i
    simp only [groupPart]
    omega
  · -- a fixed part and a part of group i
    have := a.2
    simp only [groupPart, hfixed]
    omega
  · -- two fixed parts
    split_ifs at hpq
    · simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq] at hpq
      obtain ⟨a, a', hlt, rfl⟩ := hpq
      simp only [hfixed]
      omega
    · simp at hpq

/-- The pairs are pairs of two parts, the smaller one first. -/
theorem pairsN_valid (k : ℕ) (i : Fin 3) :
    ∀ pq ∈ pairsN k i, pq.1 < k ∧ pq.2 < k ∧ pq.1 < pq.2 := by
  intro pq hpq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hpq
  have hne := pairsH_ne k i x hx
  have h₁ := x.1.2
  have h₂ := x.2.2
  exact ⟨by omega, by omega, by omega⟩

/-! ## The sums -/

/-- The weights of the graph G stand at g, in the blocks (p, q) with p < q.  Nothing is said about
the other blocks. -/
def WeightsAt {k n : ℕ} (μ : ℕ → ℤ) (g : ℕ) (G : KPartiteGraph k n) : Prop :=
  ∀ (p q : Fin k) (u v : Fin n), p < q → μ (g + widx k n p u q v) = G.w p u q v

/-- What sumPairs computes is the sum of the weights of G. -/
theorem memSum_eq_pairSum {k n : ℕ} {μ : ℕ → ℤ} {g : ℕ} {G : KPartiteGraph k n}
    (hG : WeightsAt μ g G) (hn : 0 < n) (F a b c : ℕ) (i : Fin 3) :
    memSum μ g k n (vtx k n F a b c) (pairsN k i) =
      pairSum G (cliqueOf hn k F a b c) (pairsH k i) := by
  unfold memSum pairSum pairsN
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun pq hpq => ?_
  simp only [Function.comp_apply]
  rcases Nat.lt_or_gt_of_ne (pairsH_ne k i pq hpq) with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    exact hG pq.1 pq.2 (cliqueOf hn k F a b c pq.1) (cliqueOf hn k F a b c pq.2) h
  · -- the graph is undirected
    rw [min_eq_right h.le, max_eq_left h.le, G.symm]
    exact hG pq.2 pq.1 (cliqueOf hn k F a b c pq.2) (cliqueOf hn k F a b c pq.1) h

/-- memSum only looks at the parts below kk. -/
theorem memSum_congr_vf {μ : ℕ → ℤ} {g kk n : ℕ} {vf vf' : ℕ → ℕ} (h : ∀ p < kk, vf p = vf' p)
    {L : List (ℕ × ℕ)} (hL : ∀ pq ∈ L, pq.1 < kk ∧ pq.2 < kk ∧ pq.1 < pq.2) :
    memSum μ g kk n vf L = memSum μ g kk n vf' L := by
  unfold memSum
  congr 1
  refine List.map_congr_left fun pq hpq => ?_
  obtain ⟨hp, hq, -⟩ := hL pq hpq
  rw [h _ hp, h _ hq]

/-- A sum of |L| weights is at most |L| U in absolute value. -/
theorem memSum_abs_le {μ : ℕ → ℤ} {g kk n U : ℕ} {vf : ℕ → ℕ} (hvf : ∀ p < kk, vf p < n)
    (hle : ∀ p q u v, p < kk → q < kk → p < q → u < n → v < n →
      |μ (g + widx kk n p u q v)| ≤ (U : ℤ))
    (L : List (ℕ × ℕ)) (hL : ∀ pq ∈ L, pq.1 < kk ∧ pq.2 < kk ∧ pq.1 < pq.2) :
    |memSum μ g kk n vf L| ≤ ((L.length * U : ℕ) : ℤ) := by
  induction L with
  | nil => simp [memSum]
  | cons pq L ih =>
    obtain ⟨hp, hq, hlt⟩ := hL pq (by simp)
    have hhead := hle _ _ _ _ hp hq hlt (hvf _ hp) (hvf _ hq)
    have htail := ih fun x hx => hL x (by simp [hx])
    rw [show memSum μ g kk n vf (pq :: L) =
      μ (g + widx kk n pq.1 (vf pq.1) pq.2 (vf pq.2)) + memSum μ g kk n vf L by simp [memSum]]
    refine (abs_add_le _ _).trans ?_
    simp only [List.length_cons]
    push_cast at htail ⊢
    linarith [hhead, htail]

/-! ## The choices that the odometers run through -/

/-- Only the choices in the k parts matter. -/
theorem ChoiceIs.congr {μ : ℕ → ℤ} {vt kk : ℕ} {vf vf' : ℕ → ℕ} (h : ChoiceIs μ vt kk vf)
    (he : ∀ p < kk, vf p = vf' p) : ChoiceIs μ vt kk vf' :=
  fun p hp => by rw [h p hp, he p hp]

/-- The choices of vertices while the matrix between the groups 0 and 1 is filled. -/
theorem choiceAt_AB (k n F r c : ℕ) : ∀ p < k,
    choiceAt (vtx k n F 0 0 0) n (width k) (numFixed k) (numFixed k + width k) r c p =
      vtx k n F r c 0 p := by
  intro p hp
  have hk := three_width_add k
  unfold choiceAt withDigits vtx
  split_ifs <;> first | rfl | omega | (congr 3; omega)

/-- The choices of vertices while the matrix between the groups 1 and 2 is filled. -/
theorem choiceAt_BC (k n F r c : ℕ) : ∀ p < k,
    choiceAt (vtx k n F 0 0 0) n (width k) (numFixed k + width k) (numFixed k + 2 * width k) r c p =
      vtx k n F 0 r c p := by
  intro p hp
  have hk := three_width_add k
  unfold choiceAt withDigits vtx
  split_ifs <;> first | rfl | omega | (congr 3; omega)

/-- The choices of vertices while the matrix between the groups 0 and 2 is filled. -/
theorem choiceAt_AC (k n F r c : ℕ) : ∀ p < k,
    choiceAt (vtx k n F 0 0 0) n (width k) (numFixed k) (numFixed k + 2 * width k) r c p =
      vtx k n F r 0 c p := by
  intro p hp
  have hk := three_width_add k
  unfold choiceAt withDigits vtx
  split_ifs <;> first | rfl | omega | (congr 3; omega)

/-- If all cells hold 0 and the digits of F in base n are written to the cells of the fixed
vertices, the choice of vertices is vtx k n F 0 0 0. -/
theorem withDigits_fixed (k n F : ℕ) : ∀ p < k,
    withDigits (fun _ => 0) n 0 (numFixed k) F p = vtx k n F 0 0 0 p := by
  intro p hp
  unfold withDigits vtx
  split_ifs <;> first | rfl | omega | simp

end Light.Sec5
