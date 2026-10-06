/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Ceil
public import ThreeSumApsp.Util.Counting

/-!
# Cutting a set of pairs into chunks

Corollary 15 splits the query pairs "into sets of at most n²/√D query pairs", and the proof of
Theorem 17 cuts each set `W_ϱ` "into chunks of at most n²/√D query pairs".  In both, the chunk
number `j` of `S` holds the pairs of `S` whose rank in row-major order, divided by `cap`, is `j`.

* A chunk has at most `cap` pairs (`card_chunk_le`), because different pairs of `S` have different
  ranks (`rankIn_injOn`).
* The first `⌈|S|/cap⌉` chunks cover `S` (`biUnion_chunk`).
* In both uses `cap = ⌊n²/√D⌋`, which is at least 1 for `1 ≤ D ≤ n` (`one_le_queryCap`).
-/

public section

namespace ThreeSumApsp

variable {n : ℕ} {S : Finset (Fin n × Fin n)} {cap : ℕ}

/-! ### Ranks -/

/-- The position in row-major order determines the pair. -/
private theorem pairIndex_injective : Function.Injective (pairIndex (n := n)) := fun q r h =>
  finProdFinEquiv.injective (Fin.ext (by simpa [pairIndex, add_comm, mul_comm] using h))

/-- Among the pairs of `S`, a pair that comes earlier in row-major order has a smaller rank. -/
private theorem rankIn_lt_rankIn {q r : Fin n × Fin n} (hq : q ∈ S)
    (h : pairIndex q < pairIndex r) : rankIn S q < rankIn S r := by
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h⟩
  · exact lt_irrefl _ (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hq, h⟩))).2

/-- Different pairs of `S` have different ranks. -/
private theorem rankIn_injOn (S : Finset (Fin n × Fin n)) : Set.InjOn (rankIn S) S := by
  intro q hq r hr h
  rcases lt_trichotomy (pairIndex q) (pairIndex r) with hlt | heq | hgt
  · exact absurd h (rankIn_lt_rankIn hq hlt).ne
  · exact pairIndex_injective heq
  · exact absurd h (rankIn_lt_rankIn hr hgt).ne'

/-- The rank of a pair of `S` is less than the number of pairs of `S`. -/
private theorem rankIn_lt_card {q : Fin n × Fin n} (hq : q ∈ S) : rankIn S q < S.card :=
  Finset.card_lt_card ⟨Finset.filter_subset _ _,
    fun hsub => lt_irrefl _ (Finset.mem_filter.mp (hsub hq)).2⟩

/-! ### Chunks -/

/-- A chunk has at most `cap` pairs: their ranks are different numbers in `[j cap, (j + 1) cap)`. -/
theorem card_chunk_le (S : Finset (Fin n × Fin n)) (hcap : 1 ≤ cap) (j : ℕ) :
    (chunk S cap j).card ≤ cap :=
  S.card_filter_div_eq_le (rankIn_injOn S) hcap j

/-- The first `⌈|S|/cap⌉` chunks cover `S`, because `|S| ≤ ⌈|S|/cap⌉ cap`. -/
theorem biUnion_chunk (S : Finset (Fin n × Fin n)) (hcap : 1 ≤ cap) :
    (Finset.range (numChunks S cap)).biUnion (fun j => chunk S cap j) = S := by
  have hcard : S.card ≤ numChunks S cap * cap := by
    rw [numChunks, Nat.ceil_div_eq_ceilDiv _ hcap]
    exact Nat.le_ceilDiv_mul hcap
  ext q
  simp only [Finset.mem_biUnion, Finset.mem_range, chunk, Finset.mem_filter]
  refine ⟨fun ⟨_, _, hq, _⟩ => hq, fun hq => ⟨rankIn S q / cap, ?_, hq, rfl⟩⟩
  exact (Nat.div_lt_iff_lt_mul hcap).mpr ((rankIn_lt_card hq).trans_le hcard)

/-! ### The size of the chunks in Corollary 15 and in Theorem 17 -/

/-- `√D ≤ D ≤ n`. -/
theorem sqrt_le_natCast {D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) : Real.sqrt D ≤ n :=
  calc Real.sqrt D ≤ Real.sqrt D * Real.sqrt D :=
        le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.one_le_sqrt.mpr (by exact_mod_cast hD))
    _ = D := Real.mul_self_sqrt (Nat.cast_nonneg D)
    _ ≤ n := by exact_mod_cast hDn

/-- The bound `⌊n²/√D⌋` on the size of a chunk is at least 1, because `√D ≤ n ≤ n²`. -/
theorem one_le_queryCap {D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) : 1 ≤ queryCap n D := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hD)), one_mul]
  exact (sqrt_le_natCast hD hDn).trans (le_self_pow₀ hn two_ne_zero)

end ThreeSumApsp
