/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.GridNet
public import PaddedDescent.F.RebalF
public import StepMachines.Prog.SidePresents

/-! # The programs of a grid with p rows and d columns present its network

The file treats a grid with p rows and d columns in the way the square grid is treated in
Prog/SidePresents.lean. `gridW` and `gridFf` are written with tests on lists and with loops. First
they are rewritten as products over the nodes of a part and over the pairs of nodes of a part; then
the weights and the factors of the network `gridN` are brought to the same form;
`presents` puts the two together. -/

public section

namespace ClauseBound.Alg.GridPresents

open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet

/-- A test on all i < n holds if and only if it holds for all i in Fin n. -/
theorem all_range_fin (n : ℕ) (t : ℕ → Bool) : (List.range n).all t = true ↔ ∀ i : Fin n, t i = true := by
  rw [List.all_eq_true]
  exact ⟨fun h i => h i (List.mem_range.2 i.2), fun h i hi => h ⟨i, List.mem_range.1 hi⟩⟩

/-- A product of indicators is the indicator of the test on all i < n. -/
theorem prod_ind_range (n : ℕ) (t : ℕ → Bool) :
    ∏ i : Fin n, (if t i = true then (1 : ℤ) else 0) = if (List.range n).all t = true then 1 else 0 := by
  rw [Finset.prod_boole]
  simp only [mem_univ, true_imp_iff, all_range_fin]

/-- A word of n bits, read as a function and written again, is the word. -/
theorem bitsOf_bitsOf {n : ℕ} {w : List Bool} (h : w.length = n) : ClauseBound.Alg.bitsOf (Groundwork.Grid.bitsOf n w) = w := by
  subst h
  apply List.ext_getElem
  · simp [ClauseBound.Alg.bitsOf]
  · intro i h1 h2
    simp [ClauseBound.Alg.bitsOf, Groundwork.Grid.bitsOf, List.getElem?_eq_getElem h2]

/-- The test of `gridW`, spelled out. -/
theorem chkG_iff (p d : ℕ) (tr : Bool) (ℓ a : ℕ) (z : List Bool) :
    chkG p d tr ℓ (a, z) = true ↔
      (∀ i : Fin (nMemb p d tr), (heG p d ℓ z i (nodeG d tr a i)).all (!·) = true) ∧
      ∀ q ∈ pairs (Fin (nMemb p d tr)), heG p d ℓ z q.1 (nodeG d tr a q.2) = heG p d ℓ z q.2 (nodeG d tr a q.1) := by
  unfold chkG
  rw [Bool.and_eq_true, all_range_fin,
    all_pairs_iff (nMemb p d tr) fun i i' => heG p d ℓ z i (nodeG d tr a i') == heG p d ℓ z i' (nodeG d tr a i)]
  simp only [beq_iff_eq]

/-- The weight of the part a at the word z: the product of the entries of its nodes (0 unless the
half-edge of a node to itself is all zeros), times the tests that the two ends
of every edge inside the part agree. -/
theorem gridW_eq (p d : ℕ) (tr : Bool) (ℓ : ℕ) (T : Tab) (a : ℕ) (z : List Bool) :
    gridW p d tr ℓ T (a, z) =
      (∏ i : Fin (nMemb p d tr), if (heG p d ℓ z i (nodeG d tr a i)).all (!·) = true then
          look T (nodeG d tr a i, (List.range (p * d)).map fun u => if u = nodeG d tr a i then [] else heG p d ℓ z i u)
        else 0) *
      ∏ q ∈ pairs (Fin (nMemb p d tr)), if heG p d ℓ z q.1 (nodeG d tr a q.2) = heG p d ℓ z q.2 (nodeG d tr a q.1) then 1 else 0 := by
  unfold gridW
  by_cases hc : chkG p d tr ℓ (a, z) = true
  · obtain ⟨h1, h2⟩ := (chkG_iff p d tr ℓ a z).1 hc
    rw [hc, cond_true, Finset.prod_eq_one (s := pairs (Fin (nMemb p d tr))) fun q hq => if_pos (h2 q hq), mul_one, prodL_eq,
      Finset.prod_range]
    exact Finset.prod_congr rfl fun i _ => (if_pos (h1 i)).symm
  · rw [Bool.not_eq_true] at hc
    rw [hc, cond_false]
    have hc' : ¬ chkG p d tr ℓ (a, z) = true := by rw [hc]; exact Bool.false_ne_true
    rw [chkG_iff, not_and_or] at hc'
    rcases hc' with h | h
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (mem_univ i) (if_neg hi), zero_mul]
    · push Not at h
      obtain ⟨q, hq, hne⟩ := h
      rw [Finset.prod_eq_zero hq (if_neg hne), mul_zero]

/-- The factor of the rectangle on the nodes number i < i' of the parts a, b, on the side of a: z is
the word of the state of a and θ the label. -/
def item (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y a b : ℕ) (z θ : List Bool) (i i' : ℕ) : ℤ :=
  (if a < b then P.top else P.bot) ((pad, tr), (h, digG P d tr h ℓ y (tri (min a b) (max a b)) (tri i i')),
    (heG p d ℓ z i (nodeG d tr b i'), heG p d ℓ z i' (nodeG d tr b i),
      chunkAt (lenG P d tr h ℓ y (tri (min a b) (max a b))) (tri i i') (θ.drop (nMemb p d tr * ℓ))))

/-- The factor of the parts a, b on the side of a: the tests on the edges between nodes of equal
number, times the factors of the rectangles. -/
theorem gridFf_eq (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y a b : ℕ) (z θ : List Bool) :
    gridFf P pad p d tr h ℓ y ((a, b), (z, θ)) =
      (∏ i : Fin (nMemb p d tr), if heG p d ℓ z i (nodeG d tr b i) = block ℓ i θ then 1 else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2, item P pad p d tr h ℓ y a b z θ k.1 k.2 := by
  have h1 : ∏ i : Fin (nMemb p d tr), (if heG p d ℓ z i (nodeG d tr b i) = block ℓ i θ then (1 : ℤ) else 0) =
      if ((List.range (nMemb p d tr)).all fun i => heG p d ℓ z i (nodeG d tr b i) == block ℓ i θ) = true then 1 else 0 := by
    rw [← prod_ind_range]
    simp only [beq_iff_eq]
  rw [h1, ← prod_counter_pairs (nMemb p d tr) fun i i' => item P pad p d tr h ℓ y a b z θ i i']
  unfold gridFf
  simp only [prodL_eq]
  cases (List.range (nMemb p d tr)).all fun i => heG p d ℓ z i (nodeG d tr b i) == block ℓ i θ with
  | false => simp
  | true => simp [item]

/-! ### The weights of the network -/

/-- The tensor of a node of the grid, at the word of the half-edges that start at this node: 0
unless the block at the node's own position is all zeros. -/
theorem gridR_nodeC (p d : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) (w : Fin (nParts p d tr) × Fin (nMemb p d tr))
    {wn : List Bool} (h : wn.length = p * d * n) :
    gridR p d tr n Rm w ((nodeC p d tr n).dec wn) =
      if (block n ((gridE p d tr).symm w) wn).all (!·) = true then
        Rm ((gridE p d tr).symm w) (fun u => if u = (gridE p d tr).symm w then [] else block n u wn)
      else 0 := by
  have hl : ∀ u : Fin (p * d), (block n u wn).length = n := fun u =>
    length_block (by rw [h]; exact Nat.mul_le_mul_right _ u.2)
  have hd : ∀ w', (nodeC p d tr n).dec wn w' = Grid.bitsOf n (block n ((gridE p d tr).symm w') wn) := fun _ => rfl
  unfold gridR onGrid instW
  simp only [hd, bitsOf_eq_zero (hl _), Equiv.symm_apply_apply]
  refine if_congr Iff.rfl (congrArg _ (funext fun u => if_congr Iff.rfl rfl ?_)) rfl
  exact (bitsC n).enc_dec (by rw [bitsC_full]; exact mem_words.2 (hl u))

section Net
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)

/-- The weight of the part a at the word z of a state. -/
theorem gridN_W (Rm : Inst (Fin (p * d)) (List Bool)) (a : Fin (nParts p d tr)) {z : List Bool}
    (hz : z.length = nMemb p d tr * (p * d) * ℓ) :
    (gridN P pad p d tr h ℓ y Rm).W a z =
      (∏ i : Fin (nMemb p d tr), if (heG p d ℓ z i (nodeG d tr a i)).all (!·) = true then
          Rm ((gridE p d tr).symm (a, i)) (fun u => if u = (gridE p d tr).symm (a, i) then [] else heG p d ℓ z i u)
        else 0) *
      ∏ q ∈ pairs (Fin (nMemb p d tr)), if heG p d ℓ z q.1 (nodeG d tr a q.2) = heG p d ℓ z q.2 (nodeG d tr a q.1) then 1 else 0 := by
  have hn : ∀ i : Fin (nMemb p d tr), nodeG d tr a i < p * d := fun i => nodeG_lt tr a.2 i.2
  change rowW (gridR p d tr ℓ Rm) a ((stC p d tr ℓ).dec z) = _
  unfold rowW
  congr 1
  · refine prod_congr rfl fun i _ => ?_
    have h1 := gridR_nodeC p d tr ℓ Rm (a, i) (wn := block (p * d * ℓ) i z) (length_block (by
      rw [hz, Nat.mul_assoc (nMemb p d tr)]
      exact Nat.mul_le_mul_right _ i.2))
    rw [GridNet.gridE_symm_val] at h1
    exact h1
  · refine prod_congr rfl fun q _ => if_congr ?_ rfl rfl
    rw [GridNet.stC_dec, GridNet.stC_dec]
    exact bitsOf_inj (length_heG hz q.1.2 (hn q.2)) (length_heG hz q.2.2 (hn q.1))

/-- What `gridW` computes from a table is the weight of the network of the instance of the table. -/
theorem gridW_eq_W (T : Tab) (a : Fin (nParts p d tr)) {z : List Bool} (hz : z.length = nMemb p d tr * (p * d) * ℓ) :
    gridW p d tr ℓ T (a.val, z) = (gridN P pad p d tr h ℓ y (instOf (K := p * d) T)).W a z := by
  rw [gridW_eq, gridN_W P pad p d tr h ℓ y _ a hz]
  congr 1
  refine prod_congr rfl fun i _ => if_congr Iff.rfl ?_ rfl
  rw [instOf, GridNet.gridE_symm_val, map_range_eq_ofFn]
  congr 3
  funext u
  simp only [Fin.ext_iff, GridNet.gridE_symm_val]

/-! ### The factors of the network -/

variable {P pad p d tr h ℓ y}

theorem gridCl_D (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b) :
    (gridCl P pad p d tr h ℓ y R a b).D = ((vC (nMemb p d tr) ℓ).prod (rectsC P pad p d tr h ℓ y a b)).D := by
  unfold gridCl
  rw [dif_pos hab]
  rfl

theorem gridCl_dec (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b) :
    (gridCl P pad p d tr h ℓ y R a b).dec = ((vC (nMemb p d tr) ℓ).prod (rectsC P pad p d tr h ℓ y a b)).dec := by
  unfold gridCl
  rw [dif_pos hab]
  rfl

/-- Every word of the right length names a label of the parts a < b. -/
theorem mem_gridCl_D (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b)
    {θ : List Bool} (hθ : θ.length = nMemb p d tr * ℓ + ∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ) :
    θ ∈ (gridCl P pad p d tr h ℓ y R a b).D := by
  have hdrop : (θ.drop (nMemb p d tr * ℓ)).length = ∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ := by
    rw [List.length_drop, hθ]; omega
  rw [gridCl_D R hab]
  change θ ∈ (words _).filter _
  rw [mem_filter, mem_words, vC_full, mem_words]
  refine ⟨hθ, by rw [List.length_take, hθ]; omega, mem_filter.2 ⟨mem_words.2 hdrop, fun k hk => mem_words.2 ?_⟩⟩
  exact length_chunkAt _ (mem_range.1 ((tri_bijOn (nMemb p d tr)).mapsTo hk)) hdrop

/-- Both factors of two parts a < b at once: o is the other part, and top says whether the function
`top` or the function `bot` of the factorizations in `cutsG` is taken. -/
theorem grid_core (top : Bool) (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b)
    (o : Fin (nParts p d tr)) {z θ : List Bool} (hz : z.length = nMemb p d tr * (p * d) * ℓ)
    (hθ : θ.length = nMemb p d tr * ℓ + ∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ) :
    (if θ ∈ (gridCl P pad p d tr h ℓ y R a b).D then
      (∏ i : Fin (nMemb p d tr), if (stC p d tr ℓ).dec z i (o, i) = ((gridCl P pad p d tr h ℓ y R a b).dec θ).1 i then (1 : ℤ) else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2,
        if top = true then
          (cutsG P pad p d tr h ℓ y ((a, b), k)).top ((stC p d tr ℓ).dec z k.1 (o, k.2)) ((stC p d tr ℓ).dec z k.2 (o, k.1))
            (((gridCl P pad p d tr h ℓ y R a b).dec θ).2 k)
        else
          (cutsG P pad p d tr h ℓ y ((a, b), k)).bot ((stC p d tr ℓ).dec z k.1 (o, k.2)) ((stC p d tr ℓ).dec z k.2 (o, k.1))
            (((gridCl P pad p d tr h ℓ y R a b).dec θ).2 k)
      else 0) =
      (∏ i : Fin (nMemb p d tr), if heG p d ℓ z i (nodeG d tr o i) = block ℓ i θ then 1 else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2,
        (if top = true then P.top else P.bot) ((pad, tr), (h, digG P d tr h ℓ y (tri a b) (tri k.1 k.2)),
          (heG p d ℓ z k.1 (nodeG d tr o k.2), heG p d ℓ z k.2 (nodeG d tr o k.1),
            chunkAt (lenG P d tr h ℓ y (tri a b)) (tri k.1 k.2) (θ.drop (nMemb p d tr * ℓ)))) := by
  have hhe : ∀ x i : Fin (nMemb p d tr), (heG p d ℓ z x (nodeG d tr o i)).length = ℓ := fun x i =>
    length_heG hz x.2 (nodeG_lt tr o.2 i.2)
  rw [if_pos (mem_gridCl_D R hab hθ)]
  congr 1
  · refine prod_congr rfl fun i _ => ?_
    rw [gridCl_dec R hab, GridNet.stC_dec]
    change (if Grid.bitsOf ℓ (heG p d ℓ z i (nodeG d tr o i)) = Grid.bitsOf ℓ (block ℓ i (θ.take (nMemb p d tr * ℓ))) then (1 : ℤ) else 0) = _
    rw [block_take _ i.2]
    exact if_congr (bitsOf_inj (hhe i i)
      (length_block (by rw [hθ]; exact (Nat.mul_le_mul_right _ i.2).trans (Nat.le_add_right _ _)))) rfl rfl
  · refine prod_congr rfl fun k hk => ?_
    have hk' := (mem_filter.1 hk).2
    have hd : ((gridCl P pad p d tr h ℓ y R a b).dec θ).2 k =
        chunkAt (lenG P d tr h ℓ y (tri a b)) (tri k.1 k.2) (θ.drop (nMemb p d tr * ℓ)) := by
      rw [gridCl_dec R hab]
      change (if k.1 < k.2 then _ else _) = _
      rw [if_pos hk']
      rfl
    rw [hd, GridNet.stC_dec, GridNet.stC_dec]
    cases top
    · change P.bot ((pad, tr), (h, _), (ClauseBound.Alg.bitsOf (Grid.bitsOf ℓ _), ClauseBound.Alg.bitsOf (Grid.bitsOf ℓ _), _)) = _
      rw [bitsOf_bitsOf (hhe k.1 k.2), bitsOf_bitsOf (hhe k.2 k.1)]
      rfl
    · change P.top ((pad, tr), (h, _), (ClauseBound.Alg.bitsOf (Grid.bitsOf ℓ _), ClauseBound.Alg.bitsOf (Grid.bitsOf ℓ _), _)) = _
      rw [bitsOf_bitsOf (hhe k.1 k.2), bitsOf_bitsOf (hhe k.2 k.1)]
      rfl

variable (P pad p d tr h ℓ y)

/-- The factor of the parts a ≠ b on the side of a: the tests on the edges between nodes of equal
number, times the factors of the rectangles. -/
theorem gridN_f (Rm : Inst (Fin (p * d)) (List Bool)) {a b : Fin (nParts p d tr)} (hab : a ≠ b) {z θ : List Bool}
    (hz : z.length = nMemb p d tr * (p * d) * ℓ) (hθ : θ.length = capG P p d tr h ℓ y a b) :
    (gridN P pad p d tr h ℓ y Rm).f a b z θ =
      (∏ i : Fin (nMemb p d tr), if heG p d ℓ z i (nodeG d tr b i) = block ℓ i θ then 1 else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2, item P pad p d tr h ℓ y a b z θ k.1 k.2 := by
  have e : (gridN P pad p d tr h ℓ y Rm).f a b z θ =
      if θ ∈ (gridCl P pad p d tr h ℓ y (gridR p d tr ℓ Rm) (min a b) (max a b)).D then
        (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).f a b ((stC p d tr ℓ).dec z)
          ((gridCl P pad p d tr h ℓ y (gridR p d tr ℓ Rm) (min a b) (max a b)).dec θ) else 0 := rfl
  unfold capG at hθ
  simp only [item]
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have h' : (a : ℕ) < b := hlt
    rw [min_eq_left h'.le, max_eq_right h'.le] at hθ
    simp only [min_eq_left h'.le, max_eq_right h'.le, if_pos h']
    have hc := grid_core (P := P) (pad := pad) (h := h) (y := y) true (gridR p d tr ℓ Rm) hlt b hz hθ
    simp only [if_true] at hc
    rw [← hc, e, min_eq_left hlt.le, max_eq_right hlt.le]
    have e' : ∀ θ', (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).f a b ((stC p d tr ℓ).dec z) θ' =
        rowTop (cutsG P pad p d tr h ℓ y) a b ((stC p d tr ℓ).dec z) θ' := fun θ' => if_pos hlt
    rw [e']
    rfl
  · have h' : (b : ℕ) < a := hlt
    rw [min_eq_right h'.le, max_eq_left h'.le] at hθ
    simp only [min_eq_right h'.le, max_eq_left h'.le, if_neg (not_lt.2 h'.le)]
    have hc := grid_core (P := P) (pad := pad) (h := h) (y := y) false (gridR p d tr ℓ Rm) hlt b hz hθ
    simp only [Bool.false_eq_true, if_false] at hc
    rw [← hc, e, min_eq_right hlt.le, max_eq_left hlt.le]
    have e' : ∀ θ', (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).f a b ((stC p d tr ℓ).dec z) θ' =
        rowBot (cutsG P pad p d tr h ℓ y) b a ((stC p d tr ℓ).dec z) θ' := fun θ' => if_neg (not_lt.2 hlt.le)
    rw [e']
    rfl

end Net

/-! ### The programs present the network -/

/-- The functions of `gridF` are the weights and the factors of `gridN` for the instance of the
table, on all words of the right lengths. -/
theorem presents (P : PiecesF) (pad pu du hu ℓu : U) (tr : Bool) (y : ℕ) (T : Tab) :
    (gridF P).toP.Presents ((pad, (pu, du), tr, hu), (ℓu, y, T))
      (gridN P pad pu.length du.length tr hu.length ℓu.length y (instOf (K := pu.length * du.length) T)) 0 0 := by
  refine RebalF.presents (gridF P) _ _ (fun a => rfl) (fun a b hab => gridN_c _ _ _ _ _ _ _ _ _ hab)
    (fun a b hab => gridN_lab _ _ _ _ _ _ _ _ _ hab) (fun a z hz => ?_) (fun a b z θ hab hz hθ => ?_)
  · exact gridW_eq_W P pad pu.length du.length tr hu.length ℓu.length y T a hz
  · change gridFf P pad pu.length du.length tr hu.length ℓu.length y ((a.val, b.val), (z, θ)) = _
    rw [gridFf_eq, gridN_f P pad pu.length du.length tr hu.length ℓu.length y _ hab hz hθ]

end ClauseBound.Alg.GridPresents
