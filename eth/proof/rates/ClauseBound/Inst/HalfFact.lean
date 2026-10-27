/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfIfc

/-! # The two programs of a factorization of a piece: the sum over the labels

The piece number i is A_s with s = i − 2h. With a pad that is long enough, the program for the upper
and the program for the lower function of a factorization return, at the label θ, the
entries of two matrices at the pair (j, τ) that θ stands for, and 0 if θ stands for no pair. So the
sum over all labels of the product of the two is the sum over the list of the pairs, which
is the double sum over j ≤ 2h and the monomials τ of weight s + j (row-wise) or 2h − s − j
(column-wise) in which the piece was written out. The lemmas on the words, the list of the
labels and the values enter as hypotheses. -/

public section

namespace ClauseBound.Inst.Half

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Finset

namespace Fact

/-- The number of all partitions of 0, …, 4h. -/
theorem deltaF_eq (h : ℕ) : deltaF h = ∑ E ∈ range (4 * h + 1), Partitions.p E := by
  rw [deltaF, pTab_eq, sum_map_range]

/-- s = i − 2h for the numbers of pieces. -/
theorem sOf_eq {h i : ℕ} (hi : i < 4 * h + 1) : sOf h i = (i : ℤ) - 2 * h := by
  rw [sOf, min_eq_left (by omega)]

theorem abs_le_of_lt {h i : ℕ} (hi : i < 4 * h + 1) : |(i : ℤ) - 2 * h| ≤ 2 * (h : ℤ) := abs_le.2 ⟨by omega, by omega⟩

/-- The number of bits of the labels: nothing is cut off. -/
theorem cap_eq {c₀ c lam : ℕ} (hC : Cst c₀ c lam) (tr : Bool) (h' : ℕ) {i : ℕ} (hi : i < 4 * ClauseBound.Part.hOf lam + 1) :
    (halfF c₀ c).cap tr h' lam i = Nat.clog 2 (bif tr then ClauseBound.Part.Rcol (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam)
      else ClauseBound.Part.Rrow (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam)) := by
  have hs := abs_le.1 (abs_le_of_lt hi)
  have hc := hC.caps _ (abs_le_of_lt hi)
  change min (2 * c * lam) (Nat.clog 2 (bif tr then RcolF (hF c₀ lam) (sOf (hF c₀ lam) i) else RrowF (hF c₀ lam) (sOf (hF c₀ lam) i))) = _
  rw [hF_eq hC.h_le, sOf_eq hi, RcolF_eq hs.1, RrowF_eq hs.2]
  cases tr
  · exact min_eq_right hc.1
  · exact min_eq_right hc.2.1

/-- The sum over all labels of the product of the two programs is the double sum over j and the
monomials of the weight that belongs to j. -/
theorem sum_words_eq (hW : StWords) (hL : StLabs) (hV : StVal) {c₀ c lam : ℕ} {pad : U} (hl : 1 ≤ lam) (hC : Cst c₀ c lam)
    (hp : 2 ^ (c * lam) ≤ pad.length) (tr : Bool) (h' : ℕ) {i : ℕ} (hi : i < 4 * ClauseBound.Part.hOf lam + 1) (a b a' b' : Pieces.Bits lam) :
    ∑ θ ∈ words ((halfF c₀ c).cap tr h' lam i),
        (halfF c₀ c).top ((pad, tr), (h', i), (bitsOf a, bitsOf b, θ)) * (halfF c₀ c).bot ((pad, tr), (h', i), (bitsOf a', bitsOf b', θ))
      = ∑ j ∈ range (2 * ClauseBound.Part.hOf lam + 1), ∑ τ ∈ ClauseBound.Boson.Pz (wOf tr (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam) j),
          (bif tr then ClauseBound.Boson.topK (ell (ClauseBound.Part.hOf lam) a) (ClauseBound.Part.hOf lam) j ((i : ℤ) - 2 * ClauseBound.Part.hOf lam - ClauseBound.Part.hOf lam + j)
              (ell (ClauseBound.Part.hOf lam) b : Multiset ℕ) τ
            else ClauseBound.Boson.topK (ell (ClauseBound.Part.hOf lam) a) (ClauseBound.Part.hOf lam) j ((i : ℤ) - 2 * ClauseBound.Part.hOf lam - ClauseBound.Part.hOf lam + j)
              τ (ell (ClauseBound.Part.hOf lam) b : Multiset ℕ)) *
          (bif tr then ClauseBound.Boson.botK (ell (ClauseBound.Part.hOf lam) b') (ClauseBound.Part.hOf lam) (ClauseBound.Part.hOf lam - ((i : ℤ) - 2 * ClauseBound.Part.hOf lam) - j)
              τ (ell (ClauseBound.Part.hOf lam) a' : Multiset ℕ)
            else ClauseBound.Boson.botK (ell (ClauseBound.Part.hOf lam) b') (ClauseBound.Part.hOf lam) (ClauseBound.Part.hOf lam - ((i : ℤ) - 2 * ClauseBound.Part.hOf lam) - j)
              (ell (ClauseBound.Part.hOf lam) a' : Multiset ℕ) τ) := by
  have hpad : padLen (ClauseBound.Part.hOf lam) ≤ pad.length := by
    rw [padLen, deltaF_eq]
    exact hC.pad.trans hp
  obtain ⟨hlen, hsum, -⟩ := hL tr (ClauseBound.Part.hOf lam) _ (abs_le_of_lt hi)
  rw [cap_eq hC tr h' hi, ← hsum]
  change ∑ θ ∈ words _, partH c₀ true _ * partH c₀ false _ = _
  simp_rw [hV c₀ lam pad hl hC.h_le hpad, sOf_eq hi]
  rw [hW _ _ _ _ _ (by rw [hlen]; exact Nat.le_pow_clog (by norm_num) _)]
  rfl

end Fact

end ClauseBound.Inst.Half
