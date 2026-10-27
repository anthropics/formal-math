/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Interfaces
public import ClauseBound.Grid.Size
public import ClauseBound.Grid.Expand
public import StepMachines.Math.SideNet

/-! # The network of one term on a grid with p rows and d columns, on words

The file follows proof/machines/StepMachines/Math/SideCodes.lean and SideNet.lean, which treat the
square grid and pieces made from single bits (Appendix H). Here the grid has p rows and d columns
and
the pieces are any `PiecesF`. A «part» is a row (tr = false) or a column (tr = true); there are
`nParts p d tr` parts with `nMemb p d tr` nodes each. The word of a state of a
part: for each of its nodes, the p·d half-edges that start there, in the order of the positions of
their other ends, ℓ bits each. A label of two parts: one block of ℓ bits for each
edge between nodes of the same number, then one chunk for each of their rectangles; the chunk of a
rectangle is any word of as many bits as its piece is charged.

`gridN` is the network; its value, its sizes and its total are computed here. -/

@[expose] public section

namespace ClauseBound.Alg.GridNet

open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

/-! ### The grid -/

/-- The p·d nodes of the instance on the grid: (part, number in the part). -/
def gridE (p d : ℕ) : (tr : Bool) → Fin (p * d) ≃ Fin (nParts p d tr) × Fin (nMemb p d tr)
  | false => finProdFinEquiv.symm
  | true => finProdFinEquiv.symm.trans (Equiv.prodComm _ _)

/-- The position of a node of the grid among the p·d nodes of the instance. -/
theorem gridE_symm_val (p d : ℕ) (tr : Bool) (w : Fin (nParts p d tr) × Fin (nMemb p d tr)) :
    ((gridE p d tr).symm w : ℕ) = nodeG d tr w.1 w.2 := by
  cases tr <;> rfl

/-- Positions are below p·d. -/
theorem nodeG_lt {p d : ℕ} (tr : Bool) {a i : ℕ} (ha : a < nParts p d tr) (hi : i < nMemb p d tr) : nodeG d tr a i < p * d := by
  have h := ((gridE p d tr).symm (⟨a, ha⟩, ⟨i, hi⟩)).2
  rwa [gridE_symm_val] at h

/-- There are p·d nodes. -/
theorem nParts_mul_nMemb (p d : ℕ) (tr : Bool) : nParts p d tr * nMemb p d tr = p * d := by
  cases tr
  · rfl
  · exact Nat.mul_comm d p

/-- A half-edge in the word of a state has ℓ bits. -/
theorem length_heG {p d ℓ : ℕ} {tr : Bool} {z : List Bool} (hz : z.length = nMemb p d tr * (p * d) * ℓ) {x u : ℕ}
    (hx : x < nMemb p d tr) (hu : u < p * d) : (heG p d ℓ z x u).length = ℓ := by
  have h1 : (block (p * d * ℓ) x z).length = p * d * ℓ := length_block (by
    rw [hz, Nat.mul_assoc (nMemb p d tr)]
    exact Nat.mul_le_mul_right _ hx)
  exact length_block (by rw [h1]; exact Nat.mul_le_mul_right _ hu)

/-! ### The codes of the states -/

/-- The code, on words of p·d·n bits, of the half-edges that start at one node. -/
def nodeC (p d : ℕ) (tr : Bool) (n : ℕ) : Code (univ : Finset (Fin (nParts p d tr) × Fin (nMemb p d tr) → Bits n)) (p * d * n) :=
  ((bitsC n).blocks (gridE p d tr).symm).cast Fintype.piFinset_univ rfl

/-- The code of a state of a part. -/
def stC (p d : ℕ) (tr : Bool) (n : ℕ) :
    Code (univ : Finset (RowSt (Fin (nParts p d tr)) (Fin (nMemb p d tr)) (Bits n))) (nMemb p d tr * (p * d) * n) :=
  ((nodeC p d tr n).blocks (Equiv.refl (Fin (nMemb p d tr)))).cast Fintype.piFinset_univ (Nat.mul_assoc _ _ _).symm

theorem nodeC_full (p d : ℕ) (tr : Bool) (n : ℕ) : (nodeC p d tr n).Full :=
  Code.full_cast _ _ _ (Code.full_blocks _ _ (bitsC_full n))

theorem stC_full (p d : ℕ) (tr : Bool) (n : ℕ) : (stC p d tr n).Full :=
  Code.full_cast _ _ _ (Code.full_blocks _ _ (nodeC_full p d tr n))

/-- The state named by a word, read half-edge by half-edge. -/
theorem stC_dec (p d : ℕ) (tr : Bool) (n : ℕ) (z : List Bool) (x : Fin (nMemb p d tr)) (w' : Fin (nParts p d tr) × Fin (nMemb p d tr)) :
    (stC p d tr n).dec z x w' = Grid.bitsOf n (heG p d n z x (nodeG d tr w'.1 w'.2)) := by
  rw [← gridE_symm_val]
  rfl

/-- The instance on words, carried to the grid; to the transposed grid if tr. -/
noncomputable def gridR (p d : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) :
    Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits n) :=
  onGrid (instW n Rm) (fun _ => false) (gridE p d tr)

/-! ### The cuts and the network -/

section Net
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)

/-- The piece number i, cut between the parts: the labels are all words of `cap` bits. -/
def cutG (i : ℕ) : Cut (Bits ℓ) (List Bool) where
  lab := words (P.cap tr h ℓ i)
  top x y θ := P.top ((pad, tr), (h, i), (bitsOf x, bitsOf y, θ))
  bot u v θ := P.bot ((pad, tr), (h, i), (bitsOf u, bitsOf v, θ))
  cap := P.cap tr h ℓ i

/-- The cuts of the rectangles of the grid (of the transposed grid if tr) for the pattern y. -/
def cutsG : Rect (Fin (nParts p d tr)) (Fin (nMemb p d tr)) → Cut (Bits ℓ) (List Bool) :=
  fun ω => cutG P pad tr h ℓ (digG P d tr h ℓ y (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2))

/-- The network of the term, with states and labels as in `rowNet`, before they are written as
words. -/
def gridNet (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) :
    Network (Fin (nParts p d tr)) (RowSt (Fin (nParts p d tr)) (Fin (nMemb p d tr)) (Bits ℓ)) (RowLab (Fin (nMemb p d tr)) (Bits ℓ) (List Bool)) :=
  rowNet R (cutsG P pad p d tr h ℓ y) [] ℓ

/-- The code of the labels of the rectangles of the parts a, b: their chunks one after the other,
every word being a label. -/
def rectsC (a b : Fin (nParts p d tr)) :
    Code (tuples (fun k : Fin (nMemb p d tr) × Fin (nMemb p d tr) => k.1 < k.2) (fun k => (cutsG P pad p d tr h ℓ y ((a, b), k)).lab) [])
      (∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ) :=
  Code.seq _ (fun k : Fin (nMemb p d tr) × Fin (nMemb p d tr) => tri k.1 k.2) (c2 (nMemb p d tr)) (tri_bijOn (nMemb p d tr))
    (lenG P d tr h ℓ y (tri a b)) (fun k => words (lenG P d tr h ℓ y (tri a b) (tri k.1 k.2))) (fun _ => id)
    (fun _ _ _ hw => mem_words.1 hw) (fun _ _ => Set.bijOn_id _) []

variable {P pad p d tr h ℓ y}

/-- The capacity (number of label bits) of the parts a < b. -/
theorem gridNet_c_eq (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b) :
    nMemb p d tr * ℓ + ∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ = (gridNet P pad p d tr h ℓ y R).c a b := by
  simp only [gridNet, rowNet, Fintype.card_fin, min_eq_left hab.le, max_eq_right hab.le]
  rw [← sum_pairs_tri]
  rfl

/-- The label set of the parts a < b: the edges between nodes of the same number, and a label for
each rectangle. -/
theorem gridNet_Θ (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b) :
    (univ : Finset (Fin (nMemb p d tr) → Bits ℓ)) ×ˢ
      tuples (fun k : Fin (nMemb p d tr) × Fin (nMemb p d tr) => k.1 < k.2) (fun k => (cutsG P pad p d tr h ℓ y ((a, b), k)).lab) []
      = (gridNet P pad p d tr h ℓ y R).Θ a b := by
  simp [gridNet, rowNet, rowΘ, hab]

/-- Label sets are kept at a < b only. -/
theorem gridNet_Θ_empty (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : ¬ a < b) :
    ∅ = (gridNet P pad p d tr h ℓ y R).Θ a b := by
  simp [gridNet, rowNet, hab]

variable (P pad p d tr h ℓ y)

/-- The code of the labels of two parts. -/
def gridCl (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) (a b : Fin (nParts p d tr)) :
    Code ((gridNet P pad p d tr h ℓ y R).Θ a b) ((gridNet P pad p d tr h ℓ y R).c a b) :=
  if hab : a < b then ((vC (nMemb p d tr) ℓ).prod (rectsC P pad p d tr h ℓ y a b)).cast (gridNet_Θ R hab) (gridNet_c_eq R hab)
  else (Code.empty ((fun _ _ => false), fun _ => []) _).cast (gridNet_Θ_empty R hab) rfl

/-- The network on words. -/
noncomputable def gridN (Rm : Inst (Fin (p * d)) (List Bool)) : Network (Fin (nParts p d tr)) (List Bool) (List Bool) :=
  (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).pull (fun _ => nMemb p d tr * (p * d) * ℓ) (fun _ => stC p d tr ℓ)
    (gridCl P pad p d tr h ℓ y (gridR p d tr ℓ Rm))

theorem gridN_S (Rm : Inst (Fin (p * d)) (List Bool)) (a : Fin (nParts p d tr)) :
    (gridN P pad p d tr h ℓ y Rm).S a = words (nMemb p d tr * (p * d) * ℓ) := rfl

/-- The capacity of two parts is the length of their labels. -/
theorem gridN_c (Rm : Inst (Fin (p * d)) (List Bool)) {a b : Fin (nParts p d tr)} (hab : a ≠ b) :
    (gridN P pad p d tr h ℓ y Rm).c a b = capG P p d tr h ℓ y a b := by
  have hlt : min a b < max a b := min_lt_max.2 hab
  have h1 := gridNet_c_eq (P := P) (pad := pad) (h := h) (y := y) (gridR p d tr ℓ Rm) hlt
  change (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).c a b = _
  have e : (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).c a b = (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).c (min a b) (max a b) := by
    simp only [gridNet, rowNet, min_eq_left hlt.le, max_eq_right hlt.le]
  rw [e, ← h1]
  rfl

/-- The labels of two parts are all words of that length. -/
theorem gridN_lab (Rm : Inst (Fin (p * d)) (List Bool)) {a b : Fin (nParts p d tr)} (hab : a ≠ b) :
    (gridN P pad p d tr h ℓ y Rm).lab a b = words (capG P p d tr h ℓ y a b) := by
  have hlt : min a b < max a b := min_lt_max.2 hab
  rw [← gridN_c P pad p d tr h ℓ y Rm hab]
  change words ((gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).c (min a b) (max a b)) =
    words ((gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).c a b)
  simp only [gridNet, rowNet, min_eq_left hlt.le, max_eq_right hlt.le]

end Net

/-! ### Numbering the rectangles; patterns as numbers -/

/-- The number of a rectangle of the grid with p rows and d columns. -/
def ixG (p d : ℕ) (ω : Rect (Fin p) (Fin d)) : ℕ := tri ω.1.1 ω.1.2 * c2 d + tri ω.2.1 ω.2.2

/-- The rectangles are numbered 0, …, R − 1, each number once. -/
theorem ixG_bijOn (p d : ℕ) : Set.BijOn (ixG p d) (Ω (Fin p) (Fin d)) (range (nRectG p d)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨a, b⟩, ⟨i, i'⟩⟩ h
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h
    simp only [coe_range, Set.mem_Iio, ixG]
    exact mixed_lt (tri_lt (Fin.lt_def.1 h.1) b.2) (tri_lt (Fin.lt_def.1 h.2) i'.2)
  · rintro ⟨⟨a, b⟩, ⟨i, i'⟩⟩ h ⟨⟨a₂, b₂⟩, ⟨i₂, i₂'⟩⟩ h₂ heq
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h h₂
    simp only [ixG] at heq
    obtain ⟨e1, e2⟩ := mixed_inj (n := c2 d) (tri_lt (Fin.lt_def.1 h.2) i'.2) (tri_lt (Fin.lt_def.1 h₂.2) i₂'.2) heq
    obtain ⟨e3, e4⟩ := tri_inj (Fin.lt_def.1 h.1) (Fin.lt_def.1 h₂.1) e1
    obtain ⟨e5, e6⟩ := tri_inj (Fin.lt_def.1 h.2) (Fin.lt_def.1 h₂.2) e2
    rw [Fin.ext e3, Fin.ext e4, Fin.ext e5, Fin.ext e6]
  · intro z hz
    simp only [coe_range, Set.mem_Iio] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mixed_surj hz
    obtain ⟨a, b, hab, hb, rfl⟩ := tri_surj (K := p) hx
    obtain ⟨i, i', hii, hi', rfl⟩ := tri_surj (K := d) hy
    refine ⟨((⟨a, by omega⟩, ⟨b, hb⟩), (⟨i, by omega⟩, ⟨i', hi'⟩)), ?_, rfl⟩
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Fin.lt_def]
    exact ⟨hab, hii⟩

/-- The number of rectangles. -/
theorem card_Ω_eq (p d : ℕ) : #(Ω (Fin p) (Fin d)) = nRectG p d := by
  rw [ClauseBound.Grid.card_Ω_pd (Fintype.card_fin p) (Fintype.card_fin d), Nat.choose_two_right, Nat.choose_two_right]
  rfl

/-- The pattern written by the number y: a rectangle gets the digit of y in base n + 1 at its
number. -/
def patG (p d n y : ℕ) : Rect (Fin p) (Fin d) → ℕ :=
  fun ω => if ω ∈ Ω (Fin p) (Fin d) then digit n y (ixG p d ω) else 0

/-- Summing over the numbers y < (n+1)^R is summing over the patterns. -/
theorem sum_patG (p d n : ℕ) (F : (Rect (Fin p) (Fin d) → ℕ) → ℤ) :
    ∑ y ∈ range ((n + 1) ^ nRectG p d), F (patG p d n y) =
      ∑ ι ∈ tuples (fun ω => ω ∈ Ω (Fin p) (Fin d)) (fun _ => range (n + 1)) 0, F ι := by
  have hlt : ∀ ω ∈ Ω (Fin p) (Fin d), ixG p d ω < nRectG p d := fun ω hω =>
    Finset.mem_range.1 (Finset.mem_coe.1 ((ixG_bijOn p d).mapsTo (Finset.mem_coe.2 hω)))
  set E : (Fin (nRectG p d) → ℕ) → Rect (Fin p) (Fin d) → ℕ :=
    fun φ ω => if h : ω ∈ Ω (Fin p) (Fin d) then φ ⟨ixG p d ω, hlt ω h⟩ else 0 with hE
  have h1 : ∀ y, patG p d n y = E fun q => digit n y q := by
    intro y
    funext ω
    simp only [patG, hE]
    split_ifs <;> rfl
  have hs : ∀ q : Fin (nRectG p d), ∃ ω ∈ Ω (Fin p) (Fin d), ixG p d ω = q := fun q => by
    obtain ⟨ω, hω, hq⟩ := (ixG_bijOn p d).surjOn (Finset.mem_coe.2 (Finset.mem_range.2 q.2))
    exact ⟨ω, Finset.mem_coe.1 hω, hq⟩
  choose inv hinv1 hinv2 using hs
  simp only [h1]
  rw [Prog.sum_digits n (nRectG p d) fun φ => F (E φ)]
  refine Finset.sum_nbij E ?_ ?_ ?_ fun _ _ => rfl
  · intro φ hφ
    rw [mem_tuples]
    refine fun ω => ⟨fun h => ?_, fun h => ?_⟩
    · simp only [hE, dif_pos h]
      exact Fintype.mem_piFinset.1 hφ _
    · simp only [hE, dif_neg h]
  · intro φ _ φ' _ heq
    funext q
    have h2 := congrFun heq (inv q)
    simp only [hE, dif_pos (hinv1 q)] at h2
    have hq : (⟨ixG p d (inv q), hlt _ (hinv1 q)⟩ : Fin (nRectG p d)) = q := Fin.ext (hinv2 q)
    rwa [hq] at h2
  · intro ι hι
    have hι' := (mem_tuples _ _ _ _).1 (Finset.mem_coe.1 hι)
    refine ⟨fun q => ι (inv q), Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun q => (hι' (inv q)).1 (hinv1 q)), ?_⟩
    funext ω
    by_cases h : ω ∈ Ω (Fin p) (Fin d)
    · simp only [hE, dif_pos h]
      exact congrArg ι ((ixG_bijOn p d).injOn (Finset.mem_coe.2 (hinv1 _)) (Finset.mem_coe.2 h) (hinv2 _))
    · simp only [hE, dif_neg h]
      exact ((hι' ω).2 h).symm

/-- A sum over the rectangles is the sum over their numbers. -/
theorem sum_Ω_ixG (p d : ℕ) (f : ℕ → ℕ) : ∑ ω ∈ Ω (Fin p) (Fin d), f (ixG p d ω) = ∑ q ∈ range (nRectG p d), f q :=
  Finset.sum_nbij (ixG p d) (fun _ hω => Finset.mem_coe.1 ((ixG_bijOn p d).mapsTo (Finset.mem_coe.2 hω)))
    (ixG_bijOn p d).injOn (ixG_bijOn p d).surjOn fun _ _ => rfl

/-- The same for the rectangles sorted by parts. -/
theorem sum_Ω_rectIxG (p d : ℕ) (tr : Bool) (f : ℕ → ℕ) :
    ∑ ω ∈ Ω (Fin (nParts p d tr)) (Fin (nMemb p d tr)), f (rectIxG d tr (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2)) =
      ∑ q ∈ range (nRectG p d), f q := by
  rw [← sum_Ω_ixG]
  cases tr
  · rfl
  · exact sum_Ω_swap (ρ := Fin p) (γ := Fin d) fun ω => f (ixG p d ω)

/-! ### The terms -/

/-- The instance on the grid with p rows and d columns. -/
noncomputable def gridR0 (p d n : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) : Inst (Fin p × Fin d) (Bits n) :=
  onGrid (instW n Rm) (fun _ => false) finProdFinEquiv.symm

/-- The term of the pattern written by y in base n + 1, for the pieces A. -/
noncomputable def termZ (p d ℓ : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) (A : ℕ → Pieces.Four ℓ) (n y : ℕ) : ℤ :=
  ZG (gridR0 p d ℓ Rm) fun ω => A (patG p d n y ω)

/-- The function [x = v][y = u], `Pieces.cross`, agrees with `Cross.X`. -/
theorem cross_eq {n : ℕ} (x y u v : Bits n) : Pieces.cross x y u v = Cross.X x y u v := by
  unfold Pieces.cross Cross.X
  split_ifs <;> rfl

/-- The identity D^|R|·Z = Σ_ι Z_ι of the proof of Theorem A(b), with D the multiplier of the pieces
and |R| the number of rectangles, on words. -/
theorem ZW_mul_eq_sum (p d ℓ : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) (A : ℕ → Pieces.Four ℓ) (n : ℕ) (D : ℤ)
    (hA : ∀ x y u v, ∑ i ∈ range (n + 1), A i x y u v = D * Pieces.cross x y u v) :
    D ^ nRectG p d * Inst.ZW ℓ [] Rm = ∑ y ∈ range ((n + 1) ^ nRectG p d), termZ p d ℓ Rm A n y := by
  rw [ZW_eq_Z ℓ Rm (fun _ => false), ← card_Ω_eq,
    ClauseBound.Grid.Z_mul_eq_sum (instW ℓ Rm) (fun _ => false) (finProdFinEquiv (m := p) (n := d)).symm (range (n + 1)) 0 A D
      (fun x y u v => by rw [hA, cross_eq]), card_Ω_eq, ← sum_patG]
  rfl

/-- A function of the four ends, read on the transposed grid if tr: transposing exchanges the ends y
and u. -/
def trA {ℓ : ℕ} : Bool → Pieces.Four ℓ → Pieces.Four ℓ
  | false, F => F
  | true, F => fun x y u v => F x u y v

/-- The sum over the grid, or over the transposed grid, is the term. -/
theorem ZG_gridR (p d : ℕ) (tr : Bool) (ℓ : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) (A : ℕ → Pieces.Four ℓ) (n y : ℕ) :
    ZG (gridR p d tr ℓ Rm) (fun ω => trA tr (A (digit n y (rectIxG d tr (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2))))) =
      termZ p d ℓ Rm A n y := by
  have hc : ZG (gridR0 p d ℓ Rm) (fun ω => A (digit n y (ixG p d ω))) = termZ p d ℓ Rm A n y :=
    ZG_congr _ fun ω hω => by simp [patG, hω]
  rw [← hc]
  cases tr
  · rfl
  · exact ZG_tr (gridR0 p d ℓ Rm) fun ω => A (digit n y (ixG p d ω))

/-- The bound 2^B on the instance at the queries that are asked passes to the grid. -/
theorem abs_gridR_le {p d n B : ℕ} (tr : Bool) {Rm : Inst (Fin (p * d)) (List Bool)} (hR : BoundedInst n B Rm)
    (w : Fin (nParts p d tr) × Fin (nMemb p d tr)) (h : Fin (nParts p d tr) × Fin (nMemb p d tr) → Bits n) :
    |gridR p d tr n Rm w h| ≤ 2 ^ B := by
  unfold gridR onGrid
  split_ifs
  · refine hR _ _ (fun u hu => ?_) (by simp)
    rw [if_neg hu]
    exact (bitsC n).length_enc (mem_univ _)
  · rw [abs_zero]
    positivity

/-! ### Value, sizes and total of the network -/

/-- What is used of the pieces: the pieces A i, i < cnt, are factorized by the cuts, and everything
is bounded. -/
structure CutsOK (P : PiecesF) (pad : U) (h ℓ : ℕ) (A : ℕ → Pieces.Four ℓ) : Prop where
  cnt_pos : 1 ≤ P.cnt h ℓ
  m_pos : 1 ≤ P.m
  factors : ∀ tr, ∀ i < P.cnt h ℓ, (cutG P pad tr h ℓ i).Factors (trA tr (A i))
  cap_le : ∀ tr, ∀ i < P.cnt h ℓ, P.cap tr h ℓ i ≤ 2 * P.m * ℓ
  abs_A : ∀ i < P.cnt h ℓ, ∀ x y u v, |A i x y u v| ≤ 2 ^ P.bits h ℓ
  abs_top : ∀ tr, ∀ i < P.cnt h ℓ, ∀ x y θ, |(cutG P pad tr h ℓ i).top x y θ| ≤ 2 ^ P.bits h ℓ
  abs_bot : ∀ tr, ∀ i < P.cnt h ℓ, ∀ x y θ, |(cutG P pad tr h ℓ i).bot x y θ| ≤ 2 ^ P.bits h ℓ

section Facts
variable {P : PiecesF} {pad : U} {h ℓ : ℕ} {A : ℕ → Pieces.Four ℓ}

/-- A digit of a pattern is the number of a piece. -/
theorem digG_lt (hP : 1 ≤ P.cnt h ℓ) (d : ℕ) (tr : Bool) (y q κ : ℕ) : digG P d tr h ℓ y q κ < P.cnt h ℓ := by
  have := Prog.digit_le (P.cnt h ℓ - 1) y (rectIxG d tr q κ)
  unfold digG
  omega

/-- Either network on words has the value of the term. -/
theorem value_gridN (hP : CutsOK P pad h ℓ A) (p d : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) :
    (gridN P pad p d tr h ℓ y Rm).value = termZ p d ℓ Rm A (P.cnt h ℓ - 1) y := by
  refine (Network.value_pull _ _ _ _ (fun _ => stC_full p d tr ℓ)).trans ?_
  rw [← ZG_gridR p d tr]
  exact value_rowNet (fun ω => hP.factors tr _ (digG_lt hP.cnt_pos d tr y _ _)) _ _ _

/-- The values of a piece read on the transposed grid. -/
theorem abs_trA_le {b : ℕ} {F : Pieces.Four ℓ} (hF : ∀ x y u v, |F x y u v| ≤ 2 ^ b) (tr : Bool) (x y u v : Bits ℓ) :
    |trA tr F x y u v| ≤ 2 ^ b := by
  cases tr
  · exact hF x y u v
  · exact hF x u y v

/-- The network on words has the size m·(parts·members²·ℓ), and values of at most members·B +
members²·bits bits. -/
theorem gridN_sized (hP : CutsOK P pad h ℓ A) (p d : ℕ) (tr : Bool) (y : ℕ) {B : ℕ} {Rm : Inst (Fin (p * d)) (List Bool)}
    (hR : BoundedInst ℓ B Rm) :
    (gridN P pad p d tr h ℓ y Rm).Sized (P.m * (nParts p d tr * nMemb p d tr ^ 2 * ℓ))
      (nMemb p d tr * B + nMemb p d tr ^ 2 * P.bits h ℓ) := by
  refine Network.sized_pull_of_le _ _ _ _ (ClauseBound.Grid.rowNet_sized_pd hP.m_pos (Fintype.card_fin _) (Fintype.card_fin _) (by simp) _
    (abs_gridR_le tr hR) _ _ (fun ω => hP.factors tr _ (digG_lt hP.cnt_pos d tr y _ _)) (fun ω => (card_words _).le)
    (fun ω => hP.cap_le tr _ (digG_lt hP.cnt_pos d tr y _ _)) (fun ω => hP.abs_top tr _ (digG_lt hP.cnt_pos d tr y _ _))
    (fun ω => hP.abs_bot tr _ (digG_lt hP.cnt_pos d tr y _ _))
    (fun ω => abs_trA_le (hP.abs_A _ (digG_lt hP.cnt_pos d tr y _ _)) tr)) fun _ => ?_
  rw [← nParts_mul_nMemb p d tr]
  refine le_trans (le_of_eq ?_) (Nat.le_mul_of_pos_left _ hP.m_pos)
  ring

/-- The total of the network. -/
theorem U_gridN (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) :
    (gridN P pad p d tr h ℓ y Rm).U = totalG P p d tr h ℓ y := by
  change (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).U = _
  unfold gridNet totalG priceG
  rw [ClauseBound.Grid.U_rowNet_pd (Fintype.card_fin _) (Fintype.card_fin _), ← sum_Ω_rectIxG p d tr]
  rfl

/-- Two parts share at most members²·mℓ bits. -/
theorem gridN_c_le (hP : CutsOK P pad h ℓ A) (p d : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (p * d)) (List Bool))
    (a b : Fin (nParts p d tr)) : (gridN P pad p d tr h ℓ y Rm).c a b ≤ nMemb p d tr ^ 2 * (P.m * ℓ) :=
  ClauseBound.Grid.rowNet_c_le_pd hP.m_pos (Fintype.card_fin _) (gridR p d tr ℓ Rm) (cutsG P pad p d tr h ℓ y) []
    (fun _ => hP.cap_le tr _ (digG_lt hP.cnt_pos d tr y _ _)) a b

end Facts

end ClauseBound.Alg.GridNet
