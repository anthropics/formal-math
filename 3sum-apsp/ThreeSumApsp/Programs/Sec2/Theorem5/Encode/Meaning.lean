/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Recursion
public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Spec.Sec2.Theorem5.Arrays

/-!
# What encode computes, in the paper's terms

The result of encode is described by a recursion on positions in arrays (`encIdx`).  Here this is
linked with the definitions of the paper (Section 2.4.1) through arrays on strings as lists: if the
source holds an array on strings and the table holds the coefficients of the linear forms, then the
output holds the encoding of the array.

Both sides are treated at once, for an alphabet of seven variables with any coefficients:
`computeEncoding` is the procedure of Section 2.4.1 for such an alphabet,
`encIdx_eq_computeEncoding` says that the recursion on positions computes it, and `encode_str` is
the specification of encode in these terms. For the two alphabets of the paper the procedure gives
the two encodings (`computeEncoding_phi`, `computeEncoding_psi`).
-/

public section

open ThreeSumApsp

namespace Light.Sec2

open Finset ThreeSumApsp.Spec

/-! ## From positions to strings -/

section
variable {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)

/-- The recursion on positions computes the procedure of Section 2.4.1, if the array and the table
of coefficients are stored by digits. -/
private theorem encIdx_eq_computeEncoding {c : ℕ → ℤ}
    (hc : ∀ lam s, c (7 * (termIdx lam : ℕ) + (e s : ℕ)) = coef lam s) (L : ℕ)
    (A : (Fin L → α) → ℤ) {arr : ℕ → ℤ}
    (harr : ∀ j < 7 ^ L, arr j = A (decodeStr e L j)) {i : ℕ} (hi : i < 10 ^ L) :
    encIdx c L arr i = computeEncoding coef L A (decodeT L i) := by
  induction L generalizing arr i with
  | zero =>
    rw [encIdx, computeEncoding, harr 0 (by norm_num)]
    exact congrArg A (Subsingleton.elim _ _)
  | succ L ih =>
    -- The first digit of i is the digit of a term λ, and the rest of i is the code of a leaf below.
    have hpos : 0 < 10 ^ L := by positivity
    have hdigit : i / 10 ^ L < 10 := by rwa [Nat.div_lt_iff_lt_mul hpos, ← pow_succ']
    have hrest : i % 10 ^ L < 10 ^ L := Nat.mod_lt _ hpos
    obtain ⟨lam, hidx⟩ : ∃ lam : Term, ((termEquiv lam : Fin 10) : ℕ) = i / 10 ^ L :=
      ⟨termOfNat _, termIdx_termOfNat hdigit⟩
    have hleaf : decodeT (L + 1) i = Fin.cons lam (decodeT L (i % 10 ^ L)) := by
      have hcons := decodeStr_cons termEquiv lam hrest
      rwa [hidx, Nat.div_add_mod'] at hcons
    rw [encIdx, hleaf, computeEncoding, Fin.cons_zero, Fin.tail_cons]
    unfold encSlice
    -- Step (2) of the procedure of Section 2.4.1: the sum over the digits is the sum over the
    -- variables.
    refine ih _ (fun j hj => ?_) hrest
    rw [← Fin.sum_univ_eq_sum_range (fun s => c (7 * (i / 10 ^ L) + s) * arr (s * 7 ^ L + j)) 7,
      ← e.sum_comp fun s : Fin 7 => c (7 * (i / 10 ^ L) + (s : ℕ)) * arr ((s : ℕ) * 7 ^ L + j)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [sliceAt, ← hidx, show ((termEquiv lam : Fin 10) : ℕ) = termIdx lam from rfl, hc,
      harr _ (by rw [pow_succ']; exact Nat.mul_add_lt_mul (e s).isLt hj), decodeStr_cons e s hj]

end

/-! ## The specification of encode, on lists -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src out scr tab p7 p10 L : ℕ} {V : ℤ}

/-- The hypotheses of encode hold if the source, the table of coefficients and the two tables of
powers are in their places and the numbers obey the bounds. -/
private theorem EncodePre.of_seg {l T : List ℤ} (lay : EncodeLayout lim src out scr tab p7 p10 L)
    (hl : l.length = 7 ^ L) (hsrc : Seg μ src l) (hV : ∀ x ∈ l, -V ≤ x ∧ x ≤ V)
    (hT : T.length = 70) (htab : Seg μ tab T) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (h7 : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)) (h10 : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ))
    (hVB : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word) :
    EncodePre lim μ src out scr tab p7 p10 V L (fun j => l.getD j 0) (fun i => T.getD i 0) :=
  { lay := lay
    srcV := fun j hj => hsrc.getD (by omega) 0
    src_bound := fun j hj => by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hV _ (List.getElem_mem _)
    tabV := fun i hi => htab.getD (by omega) 0
    coef_bound := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hc _ (List.getElem_mem _)
    p7V := h7, p10V := h10, word_bound := hVB }

/-- **The encoding of an array on strings** (Section 2.4.1), for both alphabets at once.  If the
source holds the array A on the strings of length L, the table holds the coefficients, the tables of
powers are in their places and the numbers obey the bounds, then encode ends within `cEncode · 10^L`
steps, the output holds what the procedure of Section 2.4.1 computes, and only the output and the
scratch area have changed. -/
theorem encode_str {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ) {T : List ℤ}
    (hT : T.length = 70) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (hcoef : ∀ lam s, T.getD (7 * (termIdx lam : ℕ) + (e s : ℕ)) 0 = coef lam s) {pS pE : ℕ}
    (hS : P[pS]? = some encStepBody) (hE : P[pE]? = some (encodeBody pS pE))
    (lay : EncodeLayout lim src out scr tab p7 p10 L) (A : (Fin L → α) → ℤ)
    (hsrc : Seg μ src (arrStr e A)) (hV : ∀ u, |A u| ≤ V) (htab : Seg μ tab T)
    (h7 : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)) (h10 : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ))
    (hVB : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word) (hd : d + L ≤ lim.depth) :
    Ends lim P d (encodeBody pS pE) ⟨frame [L, src, out, scr, tab, p7, p10], μ⟩ (cEncode * 10 ^ L)
      fun σ' => Seg σ'.mem out (arrT (computeEncoding coef L A)) ∧
        SameOutside2 μ σ'.mem out (10 ^ L) scr (scrSize L) := by
  have hbound : ∀ x ∈ arrStr e A, -V ≤ x ∧ x ≤ V := fun x hx => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact abs_le.1 (hV _)
  have pre := EncodePre.of_seg lay (length_arrStr e A) hsrc hbound hT htab hc h7 h10 hVB
  refine (encode_spec hS hE hd pre).mono (by have := encTime_le L; omega) fun σ' h => ⟨?_, h.2⟩
  intro i hi
  rw [length_arrT] at hi
  rw [h.1 i hi,
    encIdx_eq_computeEncoding e coef hcoef L A (fun j hj => getD_arrStr_of_lt e A hj) hi,
    ← List.getD_eq_getElem _ 0, arrT, getD_arrStr_of_lt termEquiv _ hi]
  rfl

end Light.Sec2
