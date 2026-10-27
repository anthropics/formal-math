/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecCrossing_FactDefs
import Eight.SecCrossing_Blocks
import Eight.SecCrossing_Chunk
import Eight.SecCrossing_MulOut
import Mathlib.Tactic

/-! # Lemma 2(b): the programs `fTop` and `fBot` factorize the pieces

The proof of Lemma 2(b) in the section «Two crossing equalities as a sum of ⌈λ/3⌉ + 1 cheaper
functions», from «Now A_i is the sum, over the sets Q ⊆ [t] with |Q| = i» to «use the factorization
through 2λ bits instead».
`stFact_of` proves the statement `StFact` from three statements that other files prove: `StChunk`
(the factorization of the product that belongs to one Q), `StAMul` (the program `aMul` computes A_i)
and
`StSubsets` (A_i is the sum over the sets Q). `lemPieces_b_row` and `lemPieces_b_col` put `StFact`
in the form of the fields `b_row` and `b_col` of `Eight.LemPieces`.

* Factorization with θ = (Q, θ') (`Fact.long_sum`): a word of t + m bits is cut into Q and θ'; the
  words Q with another number of ones than i contribute 0; for the others θ' has the length that
  `StChunk` asks for; the words of t bits
  with i ones are the sets Q ⊆ {0, …, t − 1} with i elements (`Fact.sum_words_count`).
* Factorization through 2λ bits (`Fact.short_sum`): only θ = (the two strings of the first function)
  contributes.
* Bounds: `fTop` has values in {−1, 0, 1}; so has `fBot` with θ = (Q, θ'); otherwise `fBot` is a
  value of `aMul`, and |aMul| ≤ C(t, i) ≤ 2^t on all inputs, also on strings of unequal lengths
  (`abs_aMul_le`, proof/networks/Eight/SecCrossing_MulOut.lean). -/

public section

namespace Eight

open Groundwork Groundwork.Prog PaddedDescent.F Finset

/-- «Now A_i is the sum, over the sets Q ⊆ [t] with |Q| = i, of the product that takes C at the
blocks s ∈ Q and R at the others.» A statement only; it is proved in `SecCrossing_PiecesAC.lean`. -/
@[expose] def StSubsets : Prop := ∀ (lam i : ℕ) (x y u v : Pieces.Bits lam), A lam i x y u v =
  ∑ Q ∈ (range (tOf lam)).powersetCard i, ∏ s ∈ range (tOf lam),
    if s ∈ Q then Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) else Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)

namespace Fact

/-- A sum over θ ∈ {0,1}^c, written as functions, is the sum over the words of c bits. -/
theorem sum_ofFn (c : ℕ) (G : List Bool → ℤ) : ∑ θ : Pieces.Bits c, G (List.ofFn θ) = ∑ w ∈ words c, G w := by
  refine sum_bij (fun θ _ => List.ofFn θ) (fun θ _ => mem_words.2 List.length_ofFn) (fun θ _ θ' _ h => List.ofFn_injective h)
    (fun w hw => ?_) fun θ _ => rfl
  obtain rfl := mem_words.1 hw
  exact ⟨fun t => w[t], mem_univ _, List.ofFn_getElem⟩

/-- The number of s < t with p s, as the size of a set and as a count in the list 0, …, t − 1. -/
theorem card_filter_range (t : ℕ) (p : ℕ → Bool) : #((range t).filter fun s => p s = true) = (List.range t).countP p := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [range_add_one, filter_insert, List.range_succ, List.countP_append]
    by_cases h : p t = true
    · rw [if_pos h, card_insert_of_notMem (by simp), ih]; simp [h]
    · rw [if_neg h, ih]; simp [h]

/-- A word is the list of its bits. -/
theorem eq_map_getD (Q : List Bool) : Q = (List.range Q.length).map fun s => Q.getD s false := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp [List.getElem?_eq_getElem h1]

/-- The bit number s < t of the word f 0, …, f (t − 1) is f s. -/
theorem getD_map_range {t s : ℕ} (h : s < t) (f : ℕ → Bool) : ((List.range t).map f).getD s false = f s := by
  simp [List.getElem?_range h]

/-- The number of positions s < t with the bit 1 in a word of t bits is its number of ones. -/
theorem countP_getD {t : ℕ} {Q : List Bool} (h : Q.length = t) : (List.range t).countP (fun s => Q.getD s false) = Q.count true := by
  subst h
  conv_rhs => rw [eq_map_getD Q]
  rw [List.count, List.countP_map]
  refine List.countP_congr fun s _ => ?_
  simp

/-- The number of positions s < t with the bit 0 in a word of t bits is t minus its number of ones. -/
theorem countP_not_getD {t : ℕ} {Q : List Bool} (h : Q.length = t) : (List.range t).countP (fun s => !Q.getD s false) = t - Q.count true := by
  have := List.length_eq_countP_add_countP (fun s => Q.getD s false) (l := List.range t)
  rw [countP_getD h, List.length_range] at this
  have h2 : (List.range t).countP (fun s => !Q.getD s false) = (List.range t).countP (fun s => decide ¬ (Q.getD s false = true)) :=
    List.countP_congr fun s _ => by simp
  omega

/-- «A set Q ⊆ [t] is written as a string of t bits»: a sum over the words of t bits with i ones is
the sum over the subsets of {0, …, t − 1} with i elements. The summand is a product over the
positions s of a function of s and of «s ∈ Q». -/
theorem sum_words_count (t i : ℕ) (g : ℕ → Bool → ℤ) :
    ∑ Q ∈ words t, (if Q.count true = i then ∏ s ∈ range t, g s (Q.getD s false) else 0) =
      ∑ S ∈ (range t).powersetCard i, ∏ s ∈ range t, g s (decide (s ∈ S)) := by
  rw [← sum_filter]
  refine sum_nbij' (fun Q => (range t).filter fun s => Q.getD s false = true) (fun S => (List.range t).map fun s => decide (s ∈ S)) ?_ ?_ ?_ ?_ ?_
  · intro Q hQ
    rw [mem_filter, mem_words] at hQ
    rw [mem_powersetCard]
    exact ⟨filter_subset _ _, by rw [card_filter_range, countP_getD hQ.1, hQ.2]⟩
  · intro S hS
    rw [mem_powersetCard] at hS
    rw [mem_filter, mem_words]
    refine ⟨by simp, ?_⟩
    rw [List.count, List.countP_map, ← hS.2, ← card_filter_range]
    congr 1
    ext s
    simp only [mem_filter, mem_range, Function.comp, beq_true, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨mem_range.1 (hS.1 h), h⟩⟩
  · intro Q hQ
    rw [mem_filter, mem_words] at hQ
    obtain ⟨rfl, -⟩ := hQ
    conv_rhs => rw [eq_map_getD Q]
    refine List.map_congr_left fun s hs => ?_
    simp [List.mem_range.1 hs]
  · intro S hS
    rw [mem_powersetCard] at hS
    ext s
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      rw [getD_map_range h1] at h2
      simpa using h2
    · intro h
      have h1 := mem_range.1 (hS.1 h)
      exact ⟨h1, by rw [getD_map_range h1]; simpa using h⟩
  · intro Q _
    refine prod_congr rfl fun s hs => ?_
    congr 1
    simp [mem_range.1 hs]

/-- The bits of a string as a list, zeros appended, are those of the string as a function. -/
theorem getD_ofFn {lam : ℕ} (x : Pieces.Bits lam) (j : ℕ) : (List.ofFn x).getD j false = bitAt x j := by
  unfold bitAt
  split
  · rename_i h
    rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rename_i h
    rw [List.getD_eq_default _ _ (by simpa using h)]

/-- The blocks of a string as a list are those of the string as a function. -/
theorem blkL_ofFn {lam : ℕ} (x : Pieces.Bits lam) (s : ℕ) : blkL (List.ofFn x) s = blockAt x s := by
  simp only [blkL, blkAt, blockAt, getD_ofFn]

/-- A product of numbers in {−1, 0, 1} is at most 1 in absolute value. -/
theorem abs_prodL_le {t : ℕ} {f : ℕ → ℤ} (h : ∀ s, |f s| ≤ 1) : |prodL t f| ≤ 1 := by
  rw [prodL_eq, abs_prod]
  exact prod_le_one (fun _ _ => abs_nonneg _) fun s _ => h s

/-- The factor of a block in the first function is in {−1, 0, 1}. -/
theorem abs_topAt_le (tr : Bool) (Q w a b : List Bool) (s : ℕ) : |topAt tr Q w a b s| ≤ 1 := by
  unfold topAt
  split
  · split <;> simp
  · exact abs_psi_le _ _ _

/-- The factor of a block in the second function is in {−1, 0, 1}. -/
theorem abs_botAt_le (tr : Bool) (Q w a b : List Bool) (s : ℕ) : |botAt tr Q w a b s| ≤ 1 := by
  unfold botAt
  split
  · exact abs_Rb_le _ _ _ _
  · exact abs_psi_le _ _ _

/-- ⌈λ/3⌉ does not decrease with λ. -/
theorem tOf_mono {a b : ℕ} (h : a ≤ b) : tOf a ≤ tOf b := by
  unfold tOf
  omega

/-- All values of the first function are in {−1, 0, 1}, for every input. -/
theorem abs_fTop_le (q : Bool × ℕ × List Bool × List Bool × List Bool) : |fTop q| ≤ 1 := by
  unfold fTop
  split
  · split
    · exact abs_prodL_le (abs_topAt_le _ _ _ _ _)
    · simp
  · split <;> simp

/-- All values of the second function are at most 2^t in absolute value, t = ⌈λ/3⌉, λ the length of
its first string; θ is any list. -/
theorem abs_fBot_le (q : Bool × ℕ × List Bool × List Bool × List Bool) : |fBot q| ≤ 2 ^ tOf q.2.2.1.length := by
  have h1 : (1 : ℤ) ≤ 2 ^ tOf q.2.2.1.length := one_le_pow₀ (by norm_num)
  have h2 : ∀ r : FourL, r.1 = q.2.2.2.2.take q.2.2.1.length → ∀ i, |aMul (i, r)| ≤ 2 ^ tOf q.2.2.1.length := fun r hr i =>
    (abs_aMul_le (i, r)).trans (pow_le_pow_right₀ (by norm_num) (tOf_mono (by rw [hr, List.length_take]; exact min_le_left _ _)))
  unfold fBot
  split
  · split
    · exact (abs_prodL_le (abs_botAt_le _ _ _ _ _)).trans h1
    · simp
  · cases q.1
    · exact h2 _ rfl _
    · exact h2 _ rfl _

/-- The first function at θ = (Q, θ'): f(·,θ) = f_Q(·,θ') if |Q| = i, and 0 otherwise. -/
theorem fTop_long {tr : Bool} {i : ℕ} {a b Q w : List Bool} (hL : useLong tr a.length i = true) (hQ : Q.length = tOf a.length) :
    fTop (tr, i, a, b, Q ++ w) = if Q.count true = i then prodL (tOf a.length) (topAt tr Q w a b) else 0 := by
  simp [fTop, hL, ← hQ]

/-- The second function at θ = (Q, θ'): f'(·,θ) = f'_Q(·,θ') if |Q| = i, and 0 otherwise. -/
theorem fBot_long {tr : Bool} {i : ℕ} {a b Q w : List Bool} (hL : useLong tr a.length i = true) (hQ : Q.length = tOf a.length) :
    fBot (tr, i, a, b, Q ++ w) = if Q.count true = i then prodL (tOf a.length) (botAt tr Q w a b) else 0 := by
  simp [fBot, hL, ← hQ]

/-- For |Q| = i the index θ' has 3(t − i) + 6i = 3t + 3i bits row-wise and 6(t − i) + 3i = 3t + 3(t
− i) bits column-wise. -/
theorem lenW_eq {tr : Bool} {t i : ℕ} {Q : List Bool} (hQ : Q.length = t) (hc : Q.count true = i) :
    lenW tr Q t = 3 * t + 3 * (bif tr then t - i else i) := by
  subst hc
  cases tr
  · have : wide false Q = fun s => Q.getD s false := by funext s; simp [wide]
    rw [lenW, this, countP_getD hQ]; rfl
  · have : wide true Q = fun s => !Q.getD s false := by funext s; simp [wide]
    rw [lenW, this, countP_not_getD hQ]; rfl

/-- «This is a row-wise factorization of A_i through t + 3(t − i) + 6i = 4t + 3i bits. Column-wise
the roles of R and C are exchanged, which gives t + 6(t − i) + 3i = 7t − 3i bits.» Both directions
at once, for strings a, b (arguments of the first function) and a', b' (of the second): the sum over
all θ is the sum over the sets S with i elements of the product over the blocks, as in `StChunk`;
row-wise the blocks in S are wide, column-wise the others. -/
theorem long_sum (hC : StChunk) {tr : Bool} {lam i : ℕ} (hi : i ≤ tOf lam) {a b a' b' : List Bool} (ha : a.length = lam) (ha' : a'.length = lam)
    (hL : useLong tr lam i = true) :
    ∑ θ ∈ words (longCap tr (tOf lam) i), fTop (tr, i, a, b, θ) * fBot (tr, i, a', b', θ) =
      ∑ S ∈ (range (tOf lam)).powersetCard i, ∏ s ∈ range (tOf lam),
        if (decide (s ∈ S) != tr) = true then Rb (blkL a s) (blkL a' s) (blkL b s) (blkL b' s) else Rb (blkL a s) (blkL b s) (blkL a' s) (blkL b' s) := by
  have hcap : longCap tr (tOf lam) i = tOf lam + (3 * tOf lam + 3 * (bif tr then tOf lam - i else i)) := by
    cases tr <;> simp [longCap] <;> omega
  rw [hcap, sum_words_add, ← sum_words_count (tOf lam) i fun s β =>
    if (β != tr) = true then Rb (blkL a s) (blkL a' s) (blkL b s) (blkL b' s) else Rb (blkL a s) (blkL b s) (blkL a' s) (blkL b' s)]
  refine sum_congr rfl fun Q hQ => ?_
  have hQ := mem_words.1 hQ
  have e1 : ∀ w, fTop (tr, i, a, b, Q ++ w) = if Q.count true = i then prodL (tOf lam) (topAt tr Q w a b) else 0 := fun w => by
    subst ha; exact fTop_long hL hQ
  have e2 : ∀ w, fBot (tr, i, a', b', Q ++ w) = if Q.count true = i then prodL (tOf lam) (botAt tr Q w a' b') else 0 := fun w => by
    subst ha'; exact fBot_long hL hQ
  by_cases hc : Q.count true = i
  · rw [if_pos hc, ← lenW_eq hQ hc]
    refine Eq.trans (sum_congr rfl fun w _ => ?_) (hC tr (tOf lam) Q a b a' b')
    rw [e1, e2, if_pos hc, if_pos hc]
  · rw [if_neg hc]
    refine sum_eq_zero fun w _ => ?_
    rw [e1, if_neg hc, zero_mul]

/-- «Every function F : {0,1}^c × X' → ℤ factors through c bits, by F(z,z') = Σ_θ [z = θ]·F(θ,z')». -/
theorem short_sum {c : ℕ} {X : List Bool} (hX : X.length = c) (G : List Bool → ℤ) :
    ∑ θ ∈ words c, (if X = θ then 1 else 0) * G θ = G X := by
  simp [ite_mul, sum_ite_eq, hX]

/-- The two factorizations of A_i, over words; tr = false: row-wise, c_i^row = min{2λ, 4t + 3i}
bits; tr = true: column-wise, c_i^col = min{2λ, 7t − 3i} bits. «Whenever one of these numbers
exceeds 2λ, use the factorization through 2λ bits instead.» -/
theorem fact_sum (hC : StChunk) (hA : StAMul) (hS : StSubsets) (tr : Bool) {lam i : ℕ} (hi : i ≤ tOf lam) (x y u v : Pieces.Bits lam) :
    A lam i x y u v = ∑ θ ∈ words (min (2 * lam) (longCap tr (tOf lam) i)),
      fTop (tr, i, List.ofFn x, List.ofFn (bif tr then u else y), θ) * fBot (tr, i, List.ofFn (bif tr then y else u), List.ofFn v, θ) := by
  by_cases hL : useLong tr lam i = true
  · rw [min_eq_right (of_decide_eq_true hL), long_sum hC hi (by simp) (by simp) hL, hS]
    refine sum_congr rfl fun S _ => prod_congr rfl fun s _ => ?_
    simp only [blkL_ofFn]
    cases tr <;> by_cases h : s ∈ S <;> simp [h, Cb_eq_Rb]
  · have hlt : ¬ longCap tr (tOf lam) i ≤ 2 * lam := fun h => hL (decide_eq_true h)
    have e1 : ∀ θ, fTop (tr, i, List.ofFn x, List.ofFn (bif tr then u else y), θ) =
        if List.ofFn x ++ List.ofFn (bif tr then u else y) = θ then 1 else 0 := fun θ => by simp [fTop, hL]
    rw [min_eq_left (by omega), sum_congr rfl fun θ _ => by rw [e1 θ], short_sum (by simp; omega), ← hA]
    cases tr <;> simp [fBot, hL]

end Fact

/-- **Lemma 2(b)** for the programs `fTop` and `fBot`, from the factorization for one Q, the
correctness of `aMul` and the sum over the sets Q. The three hypotheses are filled in by `stFact`
(proof/networks/Eight/SecCrossing_LemPieces.lean). The bounds hold for every list θ, of any length,
which is more than the paper asks. -/
theorem stFact_of (hC : StChunk) (hA : StAMul) (hS : StSubsets) : StFact := by
  intro lam _ i hi
  refine ⟨fun x y u v => ?_, fun x y u v => ?_, fun tr a b θ => ⟨?_, ?_⟩⟩
  · rw [Fact.sum_ofFn (crow lam i) fun θ => fTop (false, i, List.ofFn x, List.ofFn y, θ) * fBot (false, i, List.ofFn u, List.ofFn v, θ)]
    exact Fact.fact_sum hC hA hS false hi x y u v
  · rw [Fact.sum_ofFn (ccol lam i) fun θ => fTop (true, i, List.ofFn x, List.ofFn u, θ) * fBot (true, i, List.ofFn y, List.ofFn v, θ)]
    exact Fact.fact_sum hC hA hS true hi x y u v
  · exact (Fact.abs_fTop_le _).trans (one_le_pow₀ (by norm_num))
  · simpa using Fact.abs_fBot_le (tr, i, List.ofFn a, List.ofFn b, θ)

/-- Lemma 2(b), row-wise half of its first sentence, with the bound of its second sentence: «As a
function of (x,y) and (u,v), A_i factors through c_i^row bits», with values at most 2^t in absolute
value. The field `b_row` of `Eight.LemPieces`. -/
theorem lemPieces_b_row (h : StFact) (lam i : ℕ) (hlam : 1 ≤ lam) (hi : i ≤ tOf lam) : FactorsLe (Pieces.rowwise (A lam i)) (crow lam i) (2 ^ tOf lam) :=
  ⟨fun p θ => fTop (false, i, List.ofFn p.1, List.ofFn p.2, List.ofFn θ), fun q θ => fBot (false, i, List.ofFn q.1, List.ofFn q.2, List.ofFn θ),
    fun p q => (h lam hlam i hi).1 p.1 p.2 q.1 q.2, fun p _ => ((h lam hlam i hi).2.2 false p.1 p.2 _).1, fun q _ => ((h lam hlam i hi).2.2 false q.1 q.2 _).2⟩

/-- Lemma 2(b), column-wise half of its first sentence, with the bound of its second sentence: «as a
function of (x,u) and (y,v), through c_i^col bits», with values at most 2^t in absolute value. The
field `b_col` of `Eight.LemPieces`. -/
theorem lemPieces_b_col (h : StFact) (lam i : ℕ) (hlam : 1 ≤ lam) (hi : i ≤ tOf lam) : FactorsLe (Pieces.colwise (A lam i)) (ccol lam i) (2 ^ tOf lam) :=
  ⟨fun p θ => fTop (true, i, List.ofFn p.1, List.ofFn p.2, List.ofFn θ), fun q θ => fBot (true, i, List.ofFn q.1, List.ofFn q.2, List.ofFn θ),
    fun p q => (h lam hlam i hi).2.1 p.1 q.1 p.2 q.2, fun p _ => ((h lam hlam i hi).2.2 true p.1 p.2 _).1, fun q _ => ((h lam hlam i hi).2.2 true q.1 q.2 _).2⟩

end Eight
