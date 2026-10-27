/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
import all StepMachines.Math.Formula

/-! # Marks and layers: the code of the labels

`enc β b x` of proof/rates/PaddedDescent/F/MarkNet.lean cuts the bit string x into blocks of b bits.
A block with j ones is written as j ones, a zero, and then the j positions of
its ones inside the block, β bits each. This file proves the two interface statements on it in
proof/rates/PaddedDescent/F/Interfaces.lean. For 0 < b the code has 1 + β bits for
every one of x and one bit for every block (`stEncLen`). For 0 < b ≤ 2^β a string of known length is
read back from its code, whatever follows the code
(`stEncInj`); so the codes of several strings of known lengths, laid end to end as in a label of the
network, are read back one after the other. At b = 0 there are
no blocks and every code is empty, so 0 < b cannot be left out. -/

namespace PaddedDescent.F.Mark.Code

open Groundwork

/-- The positions, inside block number o, of the ones of x. -/
def ones (b : ℕ) (x : List Bool) (o : ℕ) : List ℕ := (List.range b).filter fun p => x.getD (o * b + p) false

/-- The code of block number o of x. -/
def blkc (β b : ℕ) (x : List Bool) (o : ℕ) : List Bool :=
  (ones b x o).map (fun _ => true) ++ false :: (ones b x o).flatMap (toWord β)

/-- The code is the codes of the blocks, laid end to end. -/
theorem enc_eq (β b : ℕ) (x : List Bool) : enc β b x = (List.range ((x.length + b - 1) / b)).flatMap (blkc β b x) := rfl

/-- p is listed for block o exactly when p < b and x has a one at the place o·b + p. -/
theorem mem_ones {b : ℕ} {x : List Bool} {o p : ℕ} : p ∈ ones b x o ↔ p < b ∧ x.getD (o * b + p) false = true := by
  simp [ones]

/-- The blocks of b bits cover a string of t bits. -/
theorem le_blocks_mul {b : ℕ} (h0 : 0 < b) (t : ℕ) : t ≤ (t + b - 1) / b * b := by
  have h3 := Nat.mod_lt (t + b - 1) h0
  have h4 := Nat.div_add_mod (t + b - 1) b
  rw [Nat.mul_comm] at h4
  omega

/-! ### Reading the code back -/

/-- Words of β bits of numbers below 2^β, laid end to end, are read back one by one, whatever
follows them. -/
theorem eq_of_words {β : ℕ} : ∀ {P P' : List ℕ} {r r' : List Bool}, P.length = P'.length → (∀ p ∈ P, p < 2 ^ β) → (∀ p ∈ P', p < 2 ^ β) →
    P.flatMap (toWord β) ++ r = P'.flatMap (toWord β) ++ r' → P = P' ∧ r = r'
  | [], [], _, _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _ => by simp at hl
  | p :: P, p' :: P', r, r', hl, hP, hP', h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    have hp : p = p' := by
      rw [← ofWord_toWord (hP p (by simp)), h1, ofWord_toWord (hP' p' (by simp))]
    obtain ⟨h3, h4⟩ := eq_of_words (by simpa using hl) (fun q hq => hP q (List.mem_cons_of_mem _ hq))
      (fun q hq => hP' q (List.mem_cons_of_mem _ hq)) h2
    exact ⟨by rw [hp, h3], h4⟩

/-- One block is read back, whatever follows it. -/
theorem eq_of_blkc {β b : ℕ} (hb : b ≤ 2 ^ β) {x x' : List Bool} {o : ℕ} {r r' : List Bool}
    (h : blkc β b x o ++ r = blkc β b x' o ++ r') : ones b x o = ones b x' o ∧ r = r' := by
  simp only [blkc, List.map_const', List.append_assoc, List.cons_append] at h
  obtain ⟨h1, h2⟩ := Sat3.eq_of_header h
  exact eq_of_words h1 (fun p hp => (mem_ones.1 hp).1.trans_le hb) (fun p hp => (mem_ones.1 hp).1.trans_le hb) h2

/-- Several blocks are read back, whatever follows them. -/
theorem eq_of_blocks {β b : ℕ} (hb : b ≤ 2 ^ β) {x x' : List Bool} : ∀ (os : List ℕ) {r r' : List Bool},
    os.flatMap (blkc β b x) ++ r = os.flatMap (blkc β b x') ++ r' → (∀ o ∈ os, ones b x o = ones b x' o) ∧ r = r'
  | [], _, _, h => ⟨by simp, by simpa using h⟩
  | o :: os, r, r', h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨h1, h2⟩ := eq_of_blkc hb h
    obtain ⟨h3, h4⟩ := eq_of_blocks hb os h2
    exact ⟨by simpa [h1] using h3, h4⟩

/-- A string of known length is read back from its code, whatever follows the code. -/
theorem enc_append_inj {β b : ℕ} (h0 : 0 < b) (hb : b ≤ 2 ^ β) {x x' r r' : List Bool} (hl : x.length = x'.length)
    (h : enc β b x ++ r = enc β b x' ++ r') : x = x' ∧ r = r' := by
  rw [enc_eq, enc_eq, ← hl] at h
  obtain ⟨h1, h2⟩ := eq_of_blocks hb _ h
  refine ⟨List.ext_getElem hl fun i hi hi' => ?_, h2⟩
  have ho : i / b < (x.length + b - 1) / b := by
    rw [Nat.div_lt_iff_lt_mul h0]
    exact hi.trans_le (le_blocks_mul h0 _)
  have hm := h1 (i / b) (List.mem_range.2 ho)
  have hi2 : i / b * b + i % b = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i b
  have key : (x.getD i false = true) ↔ (x'.getD i false = true) := by
    have e1 := @mem_ones b x (i / b) (i % b)
    have e2 := @mem_ones b x' (i / b) (i % b)
    rw [hi2] at e1 e2
    rw [hm] at e1
    have hlt := Nat.mod_lt i h0
    exact ⟨fun hx => (e2.1 (e1.2 ⟨hlt, hx⟩)).2, fun hx => (e1.1 (e2.2 ⟨hlt, hx⟩)).2⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', Option.getD_some] at key
  exact Bool.eq_iff_iff.2 key

/-! ### The length of the code -/

/-- A block with j ones takes j·(1 + β) + 1 bits. -/
theorem length_blkc (β b : ℕ) (x : List Bool) (o : ℕ) : (blkc β b x o).length = (ones b x o).length * (1 + β) + 1 := by
  have : ∀ P : List ℕ, (P.flatMap (toWord β)).length = P.length * β := fun P => by
    induction P with
    | nil => simp
    | cons p P ih => simp [List.flatMap_cons, ih]; ring
  simp [blkc, this]; ring

/-- The places below M, where M is at least the length of x, that hold a one are as many as the ones
of x. -/
theorem length_filter_getD : ∀ (x : List Bool) (M : ℕ), x.length ≤ M → ((List.range M).filter fun i => x.getD i false).length = x.count true
  | [], M, _ => by simp
  | a :: x, 0, h => by simp at h
  | a :: x, M + 1, h => by
    have ih := length_filter_getD x M (by simpa using h)
    rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have e : ((fun i => (a :: x).getD i false) ∘ Nat.succ) = fun i => x.getD i false := by
      funext i; simp
    rw [e]
    simp only [List.getD_eq_getElem?_getD] at ih
    cases a <;> simp [ih]

/-- The ones of the first N blocks, with their places in x, are the places below N·b that hold a
one. -/
theorem flatMap_ones (b : ℕ) (x : List Bool) (N : ℕ) :
    (List.range N).flatMap (fun o => (ones b x o).map (o * b + ·)) = (List.range (N * b)).filter fun i => x.getD i false := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.filter_append, List.filter_map]
    simp [ones, Function.comp_def]

/-- The length of the code: 1 + β bits for every one, and one bit for every block. -/
theorem length_enc {β b : ℕ} (h0 : 0 < b) (x : List Bool) :
    (enc β b x).length = x.count true * (1 + β) + (x.length + b - 1) / b := by
  have h1 : ∀ N : ℕ, ((List.range N).flatMap (blkc β b x)).length =
      ((List.range N).flatMap fun o => (ones b x o).map (o * b + ·)).length * (1 + β) + N := fun N => by
    induction N with
    | zero => simp
    | succ N ih =>
      simp only [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        length_blkc, List.length_map]
      ring
  rw [enc_eq, h1, flatMap_ones, length_filter_getD x _ (le_blocks_mul h0 _)]

end PaddedDescent.F.Mark.Code

namespace PaddedDescent.F

/-- For 0 < b the code of x has 1 + β bits for every one of x and one bit for every block of b bits. -/
public theorem stEncLen : StEncLen := fun _ _ x h0 => Mark.Code.length_enc h0 x

/-- For 0 < b ≤ 2^β a string of known length is read back from its code, whatever follows the code. -/
public theorem stEncInj : StEncInj := fun _ _ _ _ _ _ h0 hb hl h => Mark.Code.enc_append_inj h0 hb hl h

end PaddedDescent.F
