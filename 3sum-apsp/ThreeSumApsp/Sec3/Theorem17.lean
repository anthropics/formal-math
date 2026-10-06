/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem17.Witnesses

/-!
# Theorem 17: Exact Triangle reduces to Lop-AE-SparseTri

The proof has three steps.

1. Hashing: a prime `p` in the range `[√D/2, √D)` with few false positives is selected
   (`TriangleInstance.exists_isSelectedPrime`, `Hashing.F_le_falsePositiveConst_mul`).
2. The instances: there are at most `4ng` of them (`TriangleInstance.card_instanceIndices_le`), each
   with a middle part of at most `D` vertices (`TriangleInstance.middleAtMost_lopInstance`) and at
   most `n²/√D` query pairs (`TriangleInstance.card_chunkOf_le`).
3. Witnesses: the scans of the accepted pairs find a zero triangle if there is one, and all but one
   of them contain a false positive of their own (`Theorem17.correctness`,
   `TriangleInstance.F_add_one_mul_pieceSize_le`).

`theorem_17` puts them together.  Before it stand three smaller statements: the arithmetic behind
the terms `n^{ω+o(1)} D^{3/2}` and `n² D g` of the additional time (`theorem_17_hashing_sum_sq_le`,
`theorem_17_write_cost`), and that the accepted pairs can be put in some order
(`theorem_17_scanOrder_exists`).  The file ends with the part of Remark 18 that is about these
instances (`remark_18_block`).
-/

public section

namespace ThreeSumApsp

/-! ### Two terms of the additional time, and the order of the scans -/

/-- Proof of Theorem 17: "each of them O(p²) word operations, so n^{ω+o(1)} D^{3/2} time over the
fewer than √D primes in the range": the sum of `p²` over the primes in the range is at most
`D^{3/2}`.  Only this sum is stated.  That the counts are read off a product of matrices over
ℤ[x]/(x^p − 1) (proof of Theorem 17) is a lemma of the library. -/
theorem theorem_17_hashing_sum_sq_le (D : ℕ) (hD : 16 ≤ D) :
    ((∑ p ∈ primesInRange D, p ^ 2 : ℕ) : ℝ) ≤ (D : ℝ) ^ (3 / 2 : ℝ) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  -- Each of the fewer than `√D` primes in the range has `p² < D`.
  have hterm : ∀ p ∈ primesInRange D, ((p ^ 2 : ℕ) : ℝ) ≤ D := by
    intro p hp
    push_cast
    exact ((Real.lt_sqrt (Nat.cast_nonneg p)).1 (mem_primesInRange.1 hp).2.2).le
  have hfew := (card_primesInRange_lt D hD).le
  rw [Nat.cast_sum]
  calc ∑ p ∈ primesInRange D, ((p ^ 2 : ℕ) : ℝ) ≤ ∑ _p ∈ primesInRange D, (D : ℝ) :=
        Finset.sum_le_sum hterm
    _ = ((primesInRange D).card : ℝ) * D := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.sqrt D * D := by gcongr
    _ = (D : ℝ) ^ (3 / 2 : ℝ) := by
        rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hD0, Real.rpow_one,
          ← Real.sqrt_eq_rpow]

/-- Proof of Theorem 17: "Writing them down costs O(n² D g): the two bipartite graphs of an instance
have O(nD) entries".  The two biadjacency matrices of an instance have `2nD` entries, and there are
at most `4ng` instances.  The statement is arithmetic on the number of instances: `2nD` is a number
here, not the size of an object.  The query pairs are not counted; the paper goes on "and the chunks
are computed once and shared by the pieces".

NOTE.
* `g ≤ √D` is not needed.
* `p` is any prime of the range, selected or not. -/
theorem theorem_17_write_cost {n D g p : ℕ} (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (T : TriangleInstance ℤ n) (hp : p ∈ primesInRange D) :
    ((T.instanceIndices D g p).card : ℝ) * (2 * (n : ℝ) * (D : ℝ))
      ≤ 8 * ((n : ℝ) ^ 2 * (D : ℝ) * (g : ℝ)) := by
  have hcard := T.card_instanceIndices_le hD hDn hg1 hp
  calc ((T.instanceIndices D g p).card : ℝ) * (2 * (n : ℝ) * (D : ℝ))
      ≤ 4 * (n : ℝ) * (g : ℝ) * (2 * (n : ℝ) * (D : ℝ)) := by gcongr
    _ = 8 * ((n : ℝ) ^ 2 * (D : ℝ) * (g : ℝ)) := by ring

/-- Proof of Theorem 17: the accepted pairs can be put in some order, so the statements about every
order of the scans are not empty. -/
theorem theorem_17_scanOrder_exists {n D g p : ℕ} (T : TriangleInstance ℤ n)
    (ans : InstanceIndex p → Fin n × Fin n → Bool) : ∃ L, T.IsScanOrder D g p ans L :=
  ⟨(T.acceptedPairs D g p ans).toList, Finset.nodup_toList _, fun _ => Finset.mem_toList⟩

/-! ### Theorem 17 -/

/-- **Theorem 17** (Exact Triangle to Lop-AE-SparseTri, deterministically), everything
except the running time: "Let 16 ≤ D ≤ n, and let 1 ≤ g ≤ √D be an integer.  Exact Triangle on n
vertices per part with weights of absolute value at most n^ν reduces deterministically to at most
4ng instances of Lop-AE-SparseTri(n, D), each with at most n²/√D query pairs [...].  The reduction
is non-adaptive: it produces all the instances before it makes any oracle call".

The reduction is defined step by step as in the proof: a selected prime `p`, the instances
`T.lopInstance D g p ι` for `ι ∈ T.instanceIndices D g p`, and the scans `T.runScans D g L` of the
accepted pairs in any order `L`.  Non-adaptivity is visible in the statement: the instances do not
depend on `ans`.  The answer is that of the search version (Section 3.2): a zero triangle, or the
report that there is none.  The last clause bounds the number of scans times the size of a piece, an
upper bound on the number of triples that the scans look at; this count is behind the term
`O(ν n³ log n/g)` of the additional time (`κ` is the paper's ν).  Its constant `C` depends on
nothing. Arithmetic behind the other two terms is in `theorem_17_hashing_sum_sq_le` and
`theorem_17_write_cost`.  For the time itself see `docs/REMARKS.md`, "Section 3: running times".

NOTE.  The paper does not say that `D` is an integer; here it is a natural number, as in every use
of the theorem, and the bound on the number of chunks uses this (see the library's lemma
`TriangleInstance.totalChunks_le`). -/
theorem theorem_17 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n D g : ℕ} {κ : ℝ}, 16 ≤ D → D ≤ n → 1 ≤ g → (g : ℝ) ≤ Real.sqrt D → 1 ≤ κ →
    ∀ T : TriangleInstance ℤ n, T.WeightsPolyBounded κ →
    (∃ p, T.IsSelectedPrime D p) ∧
    ∀ p, T.IsSelectedPrime D p →
      ((T.instanceIndices D g p).card : ℝ) ≤ 4 * (n : ℝ) * (g : ℝ) ∧
      (∀ ι ∈ T.instanceIndices D g p, (T.lopInstance D g p ι).MiddleAtMost D ∧
        ((T.lopInstance D g p ι).W.card : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt D) ∧
      ∀ ans : InstanceIndex p → Fin n × Fin n → Bool,
        (∀ ι ∈ T.instanceIndices D g p, (T.lopInstance D g p ι).IsDetectionAnswer (ans ι)) →
        ∀ L : List (InstanceIndex p × (Fin n × Fin n)), T.IsScanOrder D g p ans L →
          T.IsSearchAnswer (T.runScans D g L).1 ∧
          ((T.runScans D g L).2 : ℝ) * (pieceSize D g : ℝ)
            ≤ C * (κ * (n : ℝ) ^ 3 * Real.log n / (g : ℝ)) := by
  have hconst := Hashing.one_le_falsePositiveConst
  refine ⟨2 * Hashing.falsePositiveConst + 2, by linarith, fun {n D g κ} hD hDn hg1 hg hκ T hT =>
    ⟨T.exists_isSelectedPrime D hD,
      fun p hp => ⟨?_, fun ι _ => ⟨?_, ?_⟩, fun ans hans L hL => ?_⟩⟩⟩
  · exact T.card_instanceIndices_le hD hDn hg1 hp.1
  · exact T.middleAtMost_lopInstance hD hg1 hp.1 ι
  · exact T.card_chunkOf_le (by omega) hDn ι.1 ι.2.1
  · obtain ⟨hcorrect, hscans⟩ := Theorem17.correctness hD hDn hg1 T hp hans hL
    refine ⟨hcorrect, le_trans ?_ (T.F_add_one_mul_pieceSize_le hD hDn hg1 hg hκ hT hp)⟩
    gcongr
    exact_mod_cast hscans

/-! ### Remark 18 -/

/-- **Remark 18**: "With residues in place of their intervals, the block C_k × {−j} of our
instance for ϱ and C_k is their graph G_{−ϱ−j,j,ϱ}, and our instance puts the p graphs with the same
ϱ side by side."  The half of the sentence that is about our instance: a middle vertex `(c, σ)` with
`σ ≡ −j` is adjacent to `a` exactly if `w(a,c) ≡ −ϱ − j` and to `b` exactly if `w(b,c) ≡ j`, while
the query pairs have `w(a,b) ≡ ϱ`; these three residues, in this order, are the index of the graph.
The instance has the index `(ϱ, i, k)`: residue, chunk, piece.  The comparison with the graphs of
[VX20] is not formalized. -/
theorem remark_18_block {n D g p : ℕ} (T : TriangleInstance ℤ n) (ϱ : Fin p) (i k : ℕ)
    (c : {c : Fin n // c ∈ piece n D g k}) (σ : Fin p) (j : ℤ)
    (hσ : ((σ : ℕ) : ℤ) ≡ -j [ZMOD (p : ℤ)]) :
    (∀ a, (T.lopInstance D g p (ϱ, i, k)).adjA a (c, σ) ↔
      T.wAC a c ≡ -((ϱ : ℕ) : ℤ) - j [ZMOD (p : ℤ)]) ∧
    (∀ b, (T.lopInstance D g p (ϱ, i, k)).adjB (c, σ) b ↔ T.wBC b c ≡ j [ZMOD (p : ℤ)]) ∧
    (∀ q ∈ (T.lopInstance D g p (ϱ, i, k)).W, T.wAB q.1 q.2 ≡ ((ϱ : ℕ) : ℤ) [ZMOD (p : ℤ)]) := by
  have hdvd : (p : ℤ) ∣ -j - ((σ : ℕ) : ℤ) := Int.modEq_iff_dvd.mp hσ
  refine ⟨fun a => ?_, fun b => ?_, fun q hq => ?_⟩
  · -- `σ ≡ w(a,c) + ϱ` and `w(a,c) ≡ −ϱ − j` differ by the multiple `−j − σ` of `p`.
    change ((σ : ℕ) : ℤ) ≡ T.wAC a c + ((ϱ : ℕ) : ℤ) [ZMOD (p : ℤ)] ↔ _
    rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, ← dvd_neg (b := -((ϱ : ℕ) : ℤ) - j - T.wAC a c)]
    refine dvd_iff_dvd_of_dvd_sub ?_
    rwa [show T.wAC a c + ((ϱ : ℕ) : ℤ) - ((σ : ℕ) : ℤ) - -(-((ϱ : ℕ) : ℤ) - j - T.wAC a c)
      = -j - ((σ : ℕ) : ℤ) by ring]
  · -- `σ ≡ −w(b,c)` and `w(b,c) ≡ j` differ by the same multiple.
    change ((σ : ℕ) : ℤ) ≡ -T.wBC b c [ZMOD (p : ℤ)] ↔ _
    rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]
    refine dvd_iff_dvd_of_dvd_sub ?_
    rwa [show -T.wBC b c - ((σ : ℕ) : ℤ) - (j - T.wBC b c) = -j - ((σ : ℕ) : ℤ) by ring]
  · exact (Finset.mem_filter.mp (TriangleInstance.mem_lopInstance_W hq).1).2

end ThreeSumApsp
