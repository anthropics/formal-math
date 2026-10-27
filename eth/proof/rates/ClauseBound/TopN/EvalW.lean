/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.TopN.Defs
import PaddedDescent.F.MarkProf
import all PaddedDescent.F.MarkPi

/-! # The sum over the profiles with a weight that depends on the numbers of marks per layer

In the network of ONE profile y the number of marks in layer i is fixed: it is `tl g Ls y i`, the
sum over the nodes of the numbers of marks that the profile lets them own. So a weight
and a condition that depend only on these numbers can stay outside the network.
`evalV_weight`: let G be a function of the numbers of marks of the layers. One evaluation in which
the value of the network of the profile y is multiplied by G (tl g Ls y) is the sum, over the
assignments σ and the sets P of clauses that σ violates, with at most w members in every layer, of G
(numbers of members of P in the layers) times the sign of P. The proof is that of
`Mark.Sum.stMarkSum`: exchange the sums, use the value of one network for each y and the sum over
the profiles for each P. The extra step is `tl_eq_card`: if P has the profile y then
tl g Ls y i is the number of members of P in layer i, because every clause has exactly one owner.
`evalV_truncW`: for the weight `GW`, which is ∏_i (ws_i·s_i)^(t_i) if lo_i ≤ t_i ≤ hi_i for all i
and 0 otherwise, with s_0 = 1 and s_i = −1 for i ≥ 1, and for hi_i ≤ w, that sum is
`truncW`: Σ_σ ∏_i Σ_{lo_i ≤ j ≤ hi_i} ws_i^j·C(number of violated clauses of layer i, j). The signs
s_i cancel the sign of P, and P is chosen layer by layer.
`evalV_truncW_ctx` is the same for an evaluator that reads the number of nodes and the number of
layers from the context of the network, so that one evaluator serves all lists of layers. -/

@[expose] public section

namespace ClauseBound.TopN.EvalW

open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark

/-! ### Definitions -/

/-- The number of marks in layer i that the profile y prescribes. -/
def tl (g : ℕ) (Ls : List Fml) (y i : ℕ) : ℕ := ((List.range g).map fun a => mu g Ls y a a i).sum

/-- The weight ∏_{i < R} (ws_i·s_i)^(t_i), s_0 = 1, s_i = −1 for i ≥ 1, if lo_i ≤ t_i ≤ hi_i for all
i < R; 0 otherwise. -/
def GW (R : ℕ) (ws : List ℤ) (lo hi : List ℕ) (t : ℕ → ℕ) : ℤ :=
  ∏ i ∈ range R, if lo.getD i 0 ≤ t i ∧ t i ≤ hi.getD i 0 then (ws.getD i 0 * (if i = 0 then 1 else -1)) ^ t i else 0

/-- Σ_σ ∏_i Σ_{lo_i ≤ j ≤ hi_i} ws_i^j·C(number of violated clauses of layer i, j). -/
def truncW (n : ℕ) (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) : ℤ :=
  ∑ σ : Fin n → Bool, ((List.range Ls.length).map fun i =>
    ∑ j ∈ Finset.Icc (lo.getD i 0) (hi.getD i 0), ws.getD i 0 ^ j * ((nvio (Mark.ext σ) (Ls.getD i [])).choose j : ℤ)).prod

/-! ### The sum over the profiles -/

/-- If P has the profile y, the profile prescribes for layer i the number of members of P in layer
i. -/
theorem tl_eq_card {k g n : ℕ} {Ls : List Fml} {y : ℕ} {P : Finset ℕ} (hg : 0 < g) (hW : WfL k n Ls) (hP : P ⊆ range (cls Ls).length)
    (hM : Match g n Ls y P) {i : ℕ} (hi : i < Ls.length) : tl g Ls y i = (layP Ls P i).card := by
  rw [tl, Prof.sum_map_range, ← Prof.sum_oc hg hW hP i]
  exact Finset.sum_congr rfl fun a ha => ((hM i hi a (mem_range.1 ha)).1).symm

/-- `evalV_weight` with the four parameters n, w, β, b named. -/
theorem evalV_weight_aux (hV : StMarkVal) (hP : StProfSum) (k : ℕ) (pad gu : U) (val : MCtx → ℤ) (nu wu βu bu : U) (Ls : List Fml) (G : (ℕ → ℕ) → ℤ)
    (hg : 0 < gu.length) (hb : 0 < bu.length) (hb' : bu.length ≤ 2 ^ βu.length) (hW : WfL k nu.length Ls)
    (hpad : nProf gu.length (cls Ls).length Ls.length ≤ pad.length)
    (hG : ∀ t t' : ℕ → ℕ, (∀ i < Ls.length, t i = t' i) → G t = G t')
    (hval : ∀ y, adm k gu.length nu.length wu.length Ls y = true → G (tl gu.length Ls y) ≠ 0 →
      val ((gu, nu, βu, bu), (Ls, y)) = (markN gu.length ((gu, nu, βu, bu), (Ls, y))).value) :
    evalV k pad gu (fun c => G (tl gu.length c.2.1 c.2.2) * val c) (nu, wu, βu, bu) Ls =
      ∑ σ : Fin nu.length → Bool, ∑ P ∈ (vset (Mark.ext σ) Ls).powerset,
        if ∀ i < Ls.length, (layP Ls P i).card ≤ wu.length then G (fun i => (layP Ls P i).card) * sgnP Ls P else 0 := by
  classical
  have h1 : ∀ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
      (bif adm k gu.length nu.length wu.length Ls y then G (tl gu.length Ls y) * val ((gu, nu, βu, bu), (Ls, y)) else 0) =
        ∑ σ : Fin nu.length → Bool, ∑ P ∈ (vset (Mark.ext σ) Ls).powerset,
          (G (fun i => (layP Ls P i).card) * sgnP Ls P) *
            (if adm k gu.length nu.length wu.length Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) := by
    intro y _
    by_cases h : adm k gu.length nu.length wu.length Ls y = true
    · rw [h, cond_true]
      have h2 : G (tl gu.length Ls y) * val ((gu, nu, βu, bu), (Ls, y)) =
          G (tl gu.length Ls y) * (markN gu.length ((gu, nu, βu, bu), (Ls, y))).value := by
        by_cases h0 : G (tl gu.length Ls y) = 0
        · rw [h0, zero_mul, zero_mul]
        · rw [hval y h h0]
      rw [h2, hV k gu nu βu bu Ls y hg hb hb' hW, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun P hPm => ?_
      have hsub : P ⊆ Finset.range (cls Ls).length := (Finset.mem_powerset.1 hPm).trans (Finset.filter_subset _ _)
      by_cases hm : Match gu.length nu.length Ls y P
      · have h3 : G (tl gu.length Ls y) = G (fun i => (layP Ls P i).card) := hG _ _ fun i hi => tl_eq_card hg hW hsub hm hi
        simp [hm, h3]
      · simp [hm]
    · have h' : adm k gu.length nu.length wu.length Ls y = false := by simpa using h
      rw [h', cond_false]
      simp
  unfold evalV
  rw [sumF_eq hpad]
  refine (Finset.sum_congr rfl h1).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P hPm => ?_
  have hsub : P ⊆ Finset.range (cls Ls).length := (Finset.mem_powerset.1 hPm).trans (Finset.filter_subset _ _)
  have h2 := hP k gu.length nu.length wu.length Ls P hg hW hsub
  rw [← Finset.mul_sum]
  by_cases hc : ∀ i < Ls.length, (layP Ls P i).card ≤ wu.length
  · rw [if_pos hc] at h2
    rw [if_pos hc]
    have h3 : (∑ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
        if adm k gu.length nu.length wu.length Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) = 1 := by
      convert h2
    rw [h3, mul_one]
  · rw [if_neg hc] at h2
    rw [if_neg hc]
    have h3 : (∑ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
        if adm k gu.length nu.length wu.length Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) = 0 := by
      convert h2
    rw [h3, mul_zero]

/-- One evaluation with the weight G of the numbers of marks per layer is the sum over the
assignments σ and the sets P of violated clauses with at most w members in every layer of
G (numbers of members of P in the layers) times the sign of P. -/
theorem evalV_weight (hV : StMarkVal) (hP : StProfSum) (k : ℕ) (pad gu : U) (val : MCtx → ℤ) (p : U × U × U × U) (Ls : List Fml) (G : (ℕ → ℕ) → ℤ)
    (hg : 0 < gu.length) (hb : 0 < p.2.2.2.length) (hb' : p.2.2.2.length ≤ 2 ^ p.2.2.1.length) (hW : WfL k p.1.length Ls)
    (hpad : nProf gu.length (cls Ls).length Ls.length ≤ pad.length)
    (hG : ∀ t t' : ℕ → ℕ, (∀ i < Ls.length, t i = t' i) → G t = G t')
    (hval : ∀ y, adm k gu.length p.1.length p.2.1.length Ls y = true → G (tl gu.length Ls y) ≠ 0 →
      val ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y)) = (markN gu.length ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y))).value) :
    evalV k pad gu (fun c => G (tl gu.length c.2.1 c.2.2) * val c) p Ls =
      ∑ σ : Fin p.1.length → Bool, ∑ P ∈ (vset (Mark.ext σ) Ls).powerset,
        if ∀ i < Ls.length, (layP Ls P i).card ≤ p.2.1.length then G (fun i => (layP Ls P i).card) * sgnP Ls P else 0 := by
  obtain ⟨nu, wu, βu, bu⟩ := p
  exact evalV_weight_aux hV hP k pad gu val nu wu βu bu Ls G hg hb hb' hW hpad hG hval

/-! ### The product form -/

/-- A product over `List.range` is the product over `Finset.range`. -/
theorem prod_map_range (f : ℕ → ℤ) (k : ℕ) : ((List.range k).map f).prod = ∏ a ∈ range k, f a := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

/-- The sum of s^|P| over the subsets P of S with lo ≤ |P| ≤ hi is Σ_{lo ≤ j ≤ hi} s^j·C(|S|, j). -/
theorem sum_powerset_Icc {ι : Type*} (S : Finset ι) (lo hi : ℕ) (s : ℤ) :
    ∑ P ∈ S.powerset, (if lo ≤ P.card ∧ P.card ≤ hi then s ^ P.card else 0) = ∑ j ∈ Icc lo hi, s ^ j * (S.card.choose j : ℤ) := by
  rw [sum_powerset_apply_card (fun m => if lo ≤ m ∧ m ≤ hi then s ^ m else 0)]
  have hL : ∑ m ∈ range (S.card + 1), S.card.choose m • (if lo ≤ m ∧ m ≤ hi then s ^ m else 0) =
      ∑ m ∈ (range (S.card + 1)).filter (fun m => lo ≤ m ∧ m ≤ hi), s ^ m * (S.card.choose m : ℤ) := by
    rw [sum_filter]
    refine sum_congr rfl fun m _ => ?_
    split_ifs <;> simp [mul_comm]
  have hR : ∑ j ∈ Icc lo hi, s ^ j * (S.card.choose j : ℤ) = ∑ j ∈ (Icc lo hi).filter (· ≤ S.card), s ^ j * (S.card.choose j : ℤ) := by
    rw [sum_filter]
    refine sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rfl
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [hL, hR]
  congr 1
  ext m
  simp only [mem_filter, mem_range, mem_Icc]
  omega

/-- The weight depends only on the numbers of the layers below R. -/
theorem GW_congr (R : ℕ) (ws : List ℤ) (lo hi : List ℕ) (t t' : ℕ → ℕ) (h : ∀ i < R, t i = t' i) : GW R ws lo hi t = GW R ws lo hi t' := by
  unfold GW
  refine prod_congr rfl fun i hi' => ?_
  rw [h i (mem_range.1 hi')]

/-- The weight times the sign of P is the product over the layers of ws_i^(members of P in layer i),
or 0 if some layer has too few or too many members. -/
theorem GW_mul_sgnP (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length) :
    GW Ls.length ws lo hi (fun i => (layP Ls P i).card) * sgnP Ls P =
      ∏ i ∈ range Ls.length, if lo.getD i 0 ≤ (layP Ls P i).card ∧ (layP Ls P i).card ≤ hi.getD i 0 then ws.getD i 0 ^ (layP Ls P i).card else 0 := by
  have h1 := Pi.prod_sign (fun e => (clAt Ls e).1) Ls.length P fun e he => Pi.layer_lt Ls (mem_range.1 (hP he))
  unfold GW sgnP
  rw [← h1, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  change (if lo.getD i 0 ≤ (layP Ls P i).card ∧ (layP Ls P i).card ≤ hi.getD i 0 then (ws.getD i 0 * (if i = 0 then 1 else -1)) ^ (layP Ls P i).card else 0) *
    (if i = 0 then (1 : ℤ) else -1) ^ (layP Ls P i).card = _
  by_cases hc : lo.getD i 0 ≤ (layP Ls P i).card ∧ (layP Ls P i).card ≤ hi.getD i 0
  · rw [if_pos hc, if_pos hc, ← mul_pow, mul_assoc]
    have h2 : (if i = 0 then (1 : ℤ) else -1) * (if i = 0 then (1 : ℤ) else -1) = 1 := by split_ifs <;> norm_num
    rw [h2, mul_one]
  · rw [if_neg hc, if_neg hc, zero_mul]

/-- For one assignment: the sum over the sets of violated clauses, with the weight `GW`, is the
product over the layers. -/
theorem sum_vset_GW (σ : ℕ → Bool) (w : ℕ) (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) (hw : ∀ i < Ls.length, hi.getD i 0 ≤ w) :
    (∑ P ∈ (vset σ Ls).powerset,
      if ∀ i < Ls.length, (layP Ls P i).card ≤ w then GW Ls.length ws lo hi (fun i => (layP Ls P i).card) * sgnP Ls P else 0) =
      ((List.range Ls.length).map fun i =>
        ∑ j ∈ Finset.Icc (lo.getD i 0) (hi.getD i 0), ws.getD i 0 ^ j * ((nvio σ (Ls.getD i [])).choose j : ℤ)).prod := by
  rw [prod_map_range]
  have h1 := Pi.sum_powerset_layers (fun e => (clAt Ls e).1)
    (fun i P => if lo.getD i 0 ≤ P.card ∧ P.card ≤ hi.getD i 0 then ws.getD i 0 ^ P.card else 0) Ls.length (vset σ Ls)
    fun e he => Pi.layer_lt Ls (mem_range.1 (mem_filter.1 he).1)
  have h2 : ∀ i ∈ range Ls.length, (∑ P ∈ ((vset σ Ls).filter fun e => (clAt Ls e).1 = i).powerset,
      if lo.getD i 0 ≤ P.card ∧ P.card ≤ hi.getD i 0 then ws.getD i 0 ^ P.card else 0) =
      ∑ j ∈ Finset.Icc (lo.getD i 0) (hi.getD i 0), ws.getD i 0 ^ j * ((nvio σ (Ls.getD i [])).choose j : ℤ) := by
    intro i _
    rw [sum_powerset_Icc, ← Pi.card_layP_vset σ Ls i]
    rfl
  rw [← prod_congr rfl h2, ← h1]
  refine sum_congr rfl fun P hPm => ?_
  have hsub : P ⊆ Finset.range (cls Ls).length := (Finset.mem_powerset.1 hPm).trans (Finset.filter_subset _ _)
  have h3 := GW_mul_sgnP ws lo hi Ls hsub
  by_cases hc : ∀ i < Ls.length, (layP Ls P i).card ≤ w
  · rw [if_pos hc, h3]
    rfl
  · rw [if_neg hc]
    simp only [not_forall] at hc
    obtain ⟨i, hi', hlt⟩ := hc
    refine (prod_eq_zero (mem_range.2 hi') (if_neg fun h => hlt (h.2.trans (hw i hi')))).symm

/-- One evaluation with the weight `GW` is `truncW`, if no upper limit exceeds w. -/
theorem evalV_truncW (hV : StMarkVal) (hP : StProfSum) (k : ℕ) (pad gu : U) (val : MCtx → ℤ) (p : U × U × U × U) (Ls : List Fml)
    (ws : List ℤ) (lo hi : List ℕ)
    (hg : 0 < gu.length) (hb : 0 < p.2.2.2.length) (hb' : p.2.2.2.length ≤ 2 ^ p.2.2.1.length) (hW : WfL k p.1.length Ls)
    (hpad : nProf gu.length (cls Ls).length Ls.length ≤ pad.length) (hw : ∀ i < Ls.length, hi.getD i 0 ≤ p.2.1.length)
    (hval : ∀ y, adm k gu.length p.1.length p.2.1.length Ls y = true → GW Ls.length ws lo hi (tl gu.length Ls y) ≠ 0 →
      val ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y)) = (markN gu.length ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y))).value) :
    evalV k pad gu (fun c => GW Ls.length ws lo hi (tl gu.length c.2.1 c.2.2) * val c) p Ls = truncW p.1.length ws lo hi Ls := by
  rw [evalV_weight hV hP k pad gu val p Ls (GW Ls.length ws lo hi) hg hb hb' hW hpad (GW_congr Ls.length ws lo hi) hval]
  unfold truncW
  exact sum_congr rfl fun σ _ => sum_vset_GW (Mark.ext σ) p.2.1.length ws lo hi Ls hw

/-- The same with an evaluator that does not mention the list of layers: the number of layers is
read from the context of the network. -/
theorem evalV_truncW_ctx (hV : StMarkVal) (hP : StProfSum) (k : ℕ) (pad gu : U) (val : MCtx → ℤ) (p : U × U × U × U) (Ls : List Fml)
    (ws : List ℤ) (lo hi : List ℕ)
    (hg : 0 < gu.length) (hb : 0 < p.2.2.2.length) (hb' : p.2.2.2.length ≤ 2 ^ p.2.2.1.length) (hW : WfL k p.1.length Ls)
    (hpad : nProf gu.length (cls Ls).length Ls.length ≤ pad.length) (hw : ∀ i < Ls.length, hi.getD i 0 ≤ p.2.1.length)
    (hval : ∀ y, adm k gu.length p.1.length p.2.1.length Ls y = true → GW Ls.length ws lo hi (tl gu.length Ls y) ≠ 0 →
      val ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y)) = (markN gu.length ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y))).value) :
    evalV k pad gu (fun c => GW c.2.1.length ws lo hi (tl c.1.1.length c.2.1 c.2.2) * val c) p Ls = truncW p.1.length ws lo hi Ls :=
  evalV_truncW hV hP k pad gu val p Ls ws lo hi hg hb hb' hW hpad hw hval

end ClauseBound.TopN.EvalW
