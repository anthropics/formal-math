/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Memory

/-!
# Theorem 30 in the light language: the tiles and a query against the expressions (8) and L ∑ α_d

Pure arithmetic. The routines of Section 4 have explicit time functions. This file and the next one
show that, under the hypotheses of Theorem 30 (`Hyp30`), time and space of the preprocessing are at
most a constant times the expression (8), and the time of a query is at most a constant times
L ∑_{d ≤ t} α_d.

`Within8 f` says that f is at most a constant times (8). Such bounds can be added, multiplied by a
number and passed to smaller functions. Four quantities are within (8) by the counts in the proof of
Theorem 30: the number 1, the number 10^L of leaves, the work 10^L + L 7^L for each band, and L for
each box of each tile (`within8_one` to `within8_boxes`); the next file adds a fifth, N (L + 1)
(`within8_N_mul`). Every other function is bounded by a multiple of a sum of these: here the time
for all tiles (`within8_tAllTiles`) and the space of their tries (`within8_trieSpace`). For a query
see `exists_tQueryCore_le`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-! ## The hypotheses of Theorem 30, and what lies within (8) -/

/-- The hypotheses of Theorem 30 on the parameters. -/
structure Hyp30 (p : Sec2.Par) (t : ℕ) : Prop where
  m_pos : 1 ≤ p.m
  L_ge : 10 * p.m ≤ p.L
  t_le : t ≤ p.m
  N_ge : sqrtKN0 p.L p.m ≤ (p.N : ℝ)

theorem Hyp30.m_le {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : p.m ≤ p.L := by
  have := h.L_ge
  omega

theorem Hyp30.L_pos {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : 1 ≤ p.L := by
  have := h.L_ge
  have := h.m_pos
  omega

/-- `10^L` is within (8): it is at most the last term. -/
theorem ten_pow_le_cost8 {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (10 : ℝ) ^ p.L ≤ cost8 p.L p.m t p.N := by
  have hfirst := cost8_first_term_nonneg t p.N h.L_ge
  have hlast := Theorem30.subsets_absorbed h.L_ge h.N_ge
  rw [cost8_eq]
  linarith

/-- The expression (8) is at least 1. -/
theorem one_le_cost8 (L m t N : ℕ) (hL : 10 * m ≤ L)
    (hN : sqrtKN0 L m ≤ (N : ℝ)) : 1 ≤ cost8 L m t N := by
  have hfirst := cost8_first_term_nonneg t N hL
  have hlast := Theorem30.subsets_absorbed hL hN
  have hone : (1 : ℝ) ≤ (10 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  rw [cost8_eq]
  linarith

/-- `f = O((8))`: at most a constant times the expression (8), for all parameters that satisfy the
hypotheses of Theorem 30. -/
def Within8 (f : Sec2.Par → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, Hyp30 p t → (f p t : ℝ) ≤ C * cost8 p.L p.m t p.N

namespace Within8

variable {f g : Sec2.Par → ℕ → ℕ}

/-- A smaller function. -/
theorem of_le (hg : Within8 g) (h : ∀ p t, Hyp30 p t → f p t ≤ g p t) : Within8 f :=
  let ⟨C, hC, hg⟩ := hg
  ⟨C, hC, fun p t hp => le_trans (by exact_mod_cast h p t hp) (hg p t hp)⟩

theorem add (hf : Within8 f) (hg : Within8 g) : Within8 fun p t => f p t + g p t := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  refine ⟨A + B, add_nonneg hA hB, fun p t hp => ?_⟩
  rw [Nat.cast_add, add_mul]
  exact add_le_add (hf p t hp) (hg p t hp)

theorem const_mul (c : ℕ) (hf : Within8 f) : Within8 fun p t => c * f p t := by
  obtain ⟨A, hA, hf⟩ := hf
  refine ⟨c * A, by positivity, fun p t hp => ?_⟩
  rw [Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf p t hp) (Nat.cast_nonneg c)

end Within8

theorem within8_one : Within8 fun _ _ => 1 :=
  ⟨1, zero_le_one, fun p t h => by simpa using one_le_cost8 p.L p.m t p.N h.L_ge h.N_ge⟩

theorem within8_ten_pow : Within8 fun p _ => 10 ^ p.L :=
  ⟨1, zero_le_one, fun p t h => by simpa using ten_pow_le_cost8 h⟩

/-- The work for the bands: `10^L + L 7^L` for each band. -/
theorem within8_bands : Within8 fun p _ => p.nB * (10 ^ p.L + p.L * 7 ^ p.L) := by
  refine ⟨13 / 2, by norm_num, fun p t h => ?_⟩
  have hsum := Theorem30.cost8_assembly h.m_pos h.L_ge h.t_le h.N_ge
  have hboxes :
      0 ≤ (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * ((boxes p.L p.m t).card : ℝ)) := by
    positivity
  have htable : 0 ≤ (K p.L p.m : ℝ) * (p.L : ℝ) := by positivity
  push_cast
  change (numBands p.L p.m p.N : ℝ) * _ ≤ _
  linarith

/-- The work for the boxes: `L` for each box of each tile. -/
theorem within8_boxes : Within8 fun p t => p.L * (p.nB ^ 2 * (boxes p.L p.m t).card) := by
  refine ⟨13, by norm_num, fun p t h => ?_⟩
  have hsum := Theorem30.cost8_assembly h.m_pos h.L_ge h.t_le h.N_ge
  have hbands :
      0 ≤ 2 * (numBands p.L p.m p.N : ℝ) * ((10 : ℝ) ^ p.L + (p.L : ℝ) * (7 : ℝ) ^ p.L) := by
    positivity
  have htable : 0 ≤ (K p.L p.m : ℝ) * (p.L : ℝ) := by positivity
  push_cast
  change (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * _) ≤ _
  linarith

/-! ## The tiles -/

/-- For every e ≤ m - t with e ≤ L there is a box with e stars. -/
theorem one_le_length_starBoxes {L m t e : ℕ} (he : e ≤ m - t) (hL : e ≤ L) :
    1 ≤ (starBoxes L m t e).length := by
  have hhead := head?_nineStrs (n := L) (lo := e) (hi := m - t) hL he
  rw [starBoxes, List.length_map]
  cases hl : nineStrs L e (m - t) with
  | nil => rw [hl] at hhead; simp at hhead
  | cons a l => simp

/-- There are at least m - t + 1 boxes: one for each number of stars. -/
theorem succ_le_card_boxes {L m t : ℕ} (hL : m ≤ L) : m - t + 1 ≤ (boxes L m t).card := by
  have hsum := List.length_le_sum_of_one_le
    ((List.range (m - t + 1)).map fun e => (starBoxes L m t e).length) fun n hn => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hn
      have := List.mem_range.1 he
      exact one_le_length_starBoxes (by omega) (by omega)
  rwa [sum_length_starBoxes, List.length_map, List.length_range] at hsum

/-- The time for a tile, in closed form. -/
theorem tTile_eq (L m t : ℕ) : tTile L m t
    = tNewRoot + (m - t + 1) * (tNineFirst L + 120) + (boxes L m t).card * tFillStep L + 60 := by
  have hrounds : ∀ k, ((List.range k).map fun e => tFillList L (starBoxes L m t e).length + 60).sum
      = k * (tNineFirst L + 120)
        + ((List.range k).map fun e => (starBoxes L m t e).length).sum * tFillStep L := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tFillList]
      ring
  rw [tTile, hrounds, sum_length_starBoxes]
  ring

/-- The time for a tile, and what the loop over the tiles adds to it, is O(L) for each box (Lemma
29). The enumeration of the boxes with e stars is started once for each e ≤ m - t, in O(L) steps
each time; these m - t + 1 starts are paid for by the boxes, of which there are at least m - t + 1
(succ_le_card_boxes). -/
private theorem exists_tTile_le : ∃ c : ℕ, ∀ L m t : ℕ, 1 ≤ L → m ≤ L →
    tTile L m t + 120 ≤ c * (L * (boxes L m t).card) := by
  refine ⟨2000, fun L m t hL1 hmL => ?_⟩
  have hcard := succ_le_card_boxes (t := t) hmL
  have hstarts : (m - t + 1) * (tNineFirst L + 120) ≤ (boxes L m t).card * (tNineFirst L + 120) :=
    Nat.mul_le_mul_right _ hcard
  rw [tTile_eq]
  simp only [tFillStep, tFillRound, tStarFirst, tHorner, tSumTen, tLookup, tInsert, tNineNext,
    tNewRoot, tNineFirst] at hstarts ⊢
  generalize (boxes L m t).card = b at *
  have hb : b ≤ L * b := Nat.le_mul_of_pos_left _ hL1
  rw [show b * (30 * L + 30 + 120) = 30 * (L * b) + 150 * b by ring] at hstarts
  rw [show b * (50 * L + 30 + (20 * L + 10) + (10 * (20 * L + 12 + 40) + 30) + (220 * L + 20)
    + (90 * L + 60) + 120) = 580 * (L * b) + 790 * b by ring]
  omega

/-- **The tries of all tiles** are built within (8). -/
theorem within8_tAllTiles : Within8 fun p t => tAllTiles p.L p.m t p.nB := by
  obtain ⟨c, hc⟩ := exists_tTile_le
  refine ((within8_boxes.const_mul c).add (within8_one.const_mul 30)).of_le fun p t h => ?_
  have htile := hc p.L p.m t h.L_pos h.m_le
  have hn : p.nB ≤ p.nB ^ 2 := Nat.le_self_pow (by norm_num) _
  calc tAllTiles p.L p.m t p.nB
      = p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB * 40 + 30 := by simp only [tAllTiles]; ring
    _ ≤ p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB ^ 2 * 40 + 30 := by gcongr
    _ = p.nB ^ 2 * (tTile p.L p.m t + 120) + 30 := by ring
    _ ≤ p.nB ^ 2 * (c * (p.L * (boxes p.L p.m t).card)) + 30 := by gcongr
    _ = c * (p.L * (p.nB ^ 2 * (boxes p.L p.m t).card)) + 30 * 1 := by ring

/-- **The space of the tries and of their roots** is within (8). -/
theorem within8_trieSpace : Within8 fun p t =>
    1 + p.nB * p.nB * (11 * (1 + p.L * (boxes p.L p.m t).card)) + p.nB * p.nB := by
  refine ((within8_boxes.const_mul 23).add within8_one).of_le fun p t h => ?_
  have hcard := succ_le_card_boxes (t := t) h.m_le
  generalize (boxes p.L p.m t).card = b at *
  have hb : b ≤ p.L * b := Nat.le_mul_of_pos_left _ h.L_pos
  have htries : p.nB * p.nB * (11 * (1 + p.L * b)) ≤ p.nB * p.nB * (22 * (p.L * b)) :=
    Nat.mul_le_mul_left _ (by omega)
  have hroots : p.nB * p.nB ≤ p.nB * p.nB * (p.L * b) := Nat.le_mul_of_pos_right _ (by omega)
  rw [show 23 * (p.L * (p.nB ^ 2 * b))
    = p.nB * p.nB * (22 * (p.L * b)) + p.nB * p.nB * (p.L * b) by ring]
  omega

/-! ## A query -/

/-- The query cost of Theorem 30 is at least L. -/
theorem cast_L_le_costQuery (L m t : ℕ) : (L : ℝ) ≤ costQuery L m t := by
  have hsum : (1 : ℝ) ≤ ∑ d ∈ range (t + 1), (alpha m d : ℝ) := by
    rw [show (1 : ℝ) = (alpha m 0 : ℝ) by simp [alpha]]
    exact single_le_sum (f := fun d => (alpha m d : ℝ)) (fun _ _ => by positivity) (by simp)
  exact le_mul_of_one_le_right (Nat.cast_nonneg L) hsum

/-- The query cost of Theorem 30 is at least 1. -/
theorem one_le_costQuery {L m t : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) : 1 ≤ costQuery L m t := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  exact hL1.trans (cast_L_le_costQuery L m t)

/-- **A query**, once the digits of its output string are known, takes O(L) steps for each number
that it reads. -/
theorem exists_tQueryCore_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ L m t : ℕ, 1 ≤ L → m ≤ L → t ≤ m →
    (tQueryCore L m t : ℝ) ≤ C * costQuery L m t := by
  refine ⟨900, by norm_num, fun L m t hL1 hmL ht => ?_⟩
  have hnat : tQueryCore L m t ≤ 900 * (L * ∑ d ∈ range (t + 1), alpha m d) := by
    have hpos : 1 ≤ alpha m t := Nat.mul_pos (Nat.choose_pos ht) (by positivity)
    rw [tQueryCore, length_lowList ht [], length_boxesOf ht [], sum_range_succ]
    simp only [tScatter, tHorner, tLookup, tNineNext, tNineFirst]
    generalize ∑ d ∈ range t, alpha m d = low
    generalize alpha m t = a at *
    have hlow : low * (60 * L + 30 + (20 * L + 10) + (90 * m + 60) + 90) ≤ low * (360 * L) :=
      Nat.mul_le_mul_left _ (by omega)
    have hboxes : a * (60 * L + 30 + (20 * L + 12) + (90 * m + 60) + 90) ≤ a * (362 * L) :=
      Nat.mul_le_mul_left _ (by omega)
    have hL : L ≤ a * L := Nat.le_mul_of_pos_left _ hpos
    rw [show 900 * (L * (low + a))
      = low * (360 * L) + a * (362 * L) + 540 * (low * L) + 538 * (a * L) by ring]
    omega
  unfold costQuery
  exact_mod_cast hnat

end Light.Sec4
