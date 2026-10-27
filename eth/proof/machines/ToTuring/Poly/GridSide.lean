/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.Cut
public import ToTuring.Poly.Grid
public import ToTuring.Poly.Words
public import ToTuring.Poly.Digits
public import StepMachines.Prog.SidePresents

/-! Polynomial time for the network of one side in Section 5 (One level of the recursion): one term
of the expansion over the rectangles of the g × g
grid, with all rows or all columns merged (the flag `tr` says which). Every plain function in a step
of the procedures of
this network is polynomial-time (`PolyT`), some of them when a length is given in unary (`Unary`),
and the procedures for the weights and the factors
are built from these functions and the procedure of one rectangle (`cutP`) by combinators that keep
`IsPolyT`. The procedures
are those of StepMachines/Prog/Side.lean; the functions on positions come from
StepMachines/Math/Side*.lean. -/

@[expose] public section

namespace Groundwork.Prog

open Stepped
open Groundwork.Grid (sideCnt he node c2 rectIx rectDig rectLen sideChunk sideCap sideCnt_rectDig_le rectLen_le)

/-! ### Positions in the words of the grid -/

section plain

variable {α : Type} [Enc α] (g : ℕ) (tr : Bool)

@[fun_prop] theorem he_polyT {ℓ x u : α → ℕ} {z : α → List Bool} (h1 : PolyT ℓ) (h2 : PolyT z) (h3 : PolyT x)
    (h4 : PolyT u) : PolyT fun a => he g (ℓ a) (z a) (x a) (u a) := by unfold he; fun_prop

@[fun_prop] theorem node_polyT {a i : α → ℕ} (h1 : PolyT a) (h2 : PolyT i) : PolyT fun x => node g tr (a x) (i x) := by
  unfold node; fun_prop

@[fun_prop] theorem rectIx_polyT {p κ : α → ℕ} (h1 : PolyT p) (h2 : PolyT κ) :
    PolyT fun x => rectIx g tr (p x) (κ x) := by unfold rectIx; fun_prop

@[fun_prop] theorem rectDig_polyT {n y p κ : α → ℕ} (h1 : PolyT n) (h2 : PolyT y) (h3 : PolyT p) (h4 : PolyT κ) :
    PolyT fun x => rectDig g tr (n x) (y x) (p x) (κ x) := by unfold rectDig; fun_prop

/-- The length of the chunk of a rectangle; the length n of the indices is given in unary. -/
theorem rectLen_polyT {n y p κ : α → ℕ} (hn : Unary n) (hy : PolyT y) (hp : PolyT p) (hκ : PolyT κ) :
    PolyT fun x => rectLen g tr (n x) (y x) (p x) (κ x) := by
  have := hn.poly
  unfold rectLen
  exact capW_polyT hn (by fun_prop) fun _ => sideCnt_rectDig_le _ _ _ _ _ _

theorem le_sum_range {f : ℕ → ℕ} (hf : ∀ k, 1 ≤ f k) (m : ℕ) : m ≤ ∑ k ∈ Finset.range m, f k := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; have := hf m; omega

/-- Where a chunk starts: only as many earlier chunks as the word has bits need to be added up,
since no chunk is empty. -/
theorem drop_sum_eq {f : ℕ → ℕ} (hf : ∀ k, 1 ≤ f k) (κ : ℕ) (w : List Bool) :
    w.drop (((List.range w.length).map fun κ' => if κ' < κ then f κ' else 0).sum) = w.drop (∑ κ' ∈ Finset.range κ, f κ') := by
  rw [← sum_range_eq_list]
  rcases le_or_gt κ w.length with h | h
  · congr 1
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · rw [List.drop_eq_nil_of_le, List.drop_eq_nil_of_le]
    · exact h.le.trans (le_sum_range hf κ)
    · refine (le_sum_range hf w.length).trans (Finset.sum_le_sum fun k hk => ?_)
      rw [if_pos ((Finset.mem_range.1 hk).trans h)]

theorem one_le_rectLen (n y p κ : ℕ) : 1 ≤ rectLen g tr n y p κ := by
  unfold rectLen capW tb
  have : 0 < Nat.size (3 ^ sideCnt tr n (rectDig g tr n y p κ)) := Nat.size_pos.2 (by positivity)
  omega

/-- The chunk of a rectangle in a label. -/
theorem sideChunk_polyT {n y a b κ : α → ℕ} {θ : α → List Bool} (hn : Unary n) (hy : PolyT y) (ha : PolyT a)
    (hb : PolyT b) (hθ : PolyT θ) (hκ : PolyT κ) :
    PolyT fun x => sideChunk g tr (n x) (y x) (a x) (b x) (θ x) (κ x) := by
  have hn' := hn.poly
  have h1 : PolyT fun p : α × ℕ =>
      rectLen g tr (n p.1) (y p.1) (tri (min (a p.1) (b p.1)) (max (a p.1) (b p.1))) p.2 :=
    rectLen_polyT g tr (hn.comp (by fun_prop)) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : PolyT fun x => rectLen g tr (n x) (y x) (tri (min (a x) (b x)) (max (a x) (b x))) (κ x) :=
    rectLen_polyT g tr hn hy (by fun_prop) hκ
  have h3 : PolyT fun x => List.range ((θ x).drop (g * n x)).length :=
    PolyT.range (Unary.of_length (w := fun x => (θ x).drop (g * n x)) (by fun_prop))
  have h : PolyT fun x =>
      (((θ x).drop (g * n x)).drop
        (((List.range ((θ x).drop (g * n x)).length).map fun κ' =>
          if κ' < κ x then rectLen g tr (n x) (y x) (tri (min (a x) (b x)) (max (a x) (b x))) κ' else 0).sum)).take
        (rectLen g tr (n x) (y x) (tri (min (a x) (b x)) (max (a x) (b x))) (κ x)) := by fun_prop
  exact h.congr fun x => by rw [drop_sum_eq (one_le_rectLen g tr _ _ _), sideChunk, chunkAt]

@[fun_prop] theorem sideLabels_polyT {ℓ a i u : α → ℕ} {z : α → List Bool} (h1 : PolyT ℓ) (h2 : PolyT a) (h3 : PolyT z)
    (h4 : PolyT i) (h5 : PolyT u) : PolyT fun x => sideLabels g tr (ℓ x) (a x) (z x) (i x) (u x) := by
  unfold sideLabels; fun_prop

/-- The input of the procedure of one rectangle; the length n is given in unary. -/
theorem viewAt_polyT {n y a b i i' : α → ℕ} {z θ : α → List Bool} (hn : Unary n) (hy : PolyT y) (ha : PolyT a)
    (hb : PolyT b) (hz : PolyT z) (hθ : PolyT θ) (hi : PolyT i) (hi' : PolyT i') :
    PolyT fun x => viewAt g tr (n x) (y x) (a x) (b x) (z x) (θ x) (i x) (i' x) := by
  have hn' := hn.poly
  have := sideChunk_polyT g tr hn hy ha hb hθ (κ := fun x => tri (i x) (i' x)) (by fun_prop)
  unfold viewAt; fun_prop

/-- A bound on the label bits of a pair of parts for every n (`Grid.sideCap_le` of
StepMachines/Math/SideNet.lean needs 1 ≤ n). -/
theorem sideCap_le' (n y a b : ℕ) : sideCap g tr n y a b ≤ g * n + c2 g * (3 * n + 1) := by
  unfold sideCap
  refine Nat.add_le_add_left ((Finset.sum_le_card_nsmul _ _ _ fun κ _ => rectLen_le g tr n y _ κ).trans ?_) _
  rw [Finset.card_range, smul_eq_mul]

end plain

section ctx

variable {C : Type} [Enc C] (g : ℕ) (tr : Bool) {lam : C → ℕ}

/-! ### The weights -/

theorem sideChk_polyT (hl : PolyT lam) : PolyT (sideChk g tr lam) := by unfold sideChk; fun_prop

theorem sideQuery_polyT (hl : PolyT lam) : PolyT (sideQuery g tr lam) := by unfold sideQuery; fun_prop

theorem sideG_polyT : PolyT (sideG g : (C × ℕ) × WQ → ℕ) := by unfold sideG; fun_prop

/-! ### The factors -/

theorem sideEdges_polyT (hl : PolyT lam) : PolyT (sideEdges g tr lam) := by unfold sideEdges; fun_prop

theorem sideIsRect_polyT : PolyT (sideIsRect g : ((C × ℕ) × FQ) × ℕ → Bool) := by unfold sideIsRect; fun_prop

theorem sideNN_polyT : PolyT (sideNN g : (C × ℕ) × FQ → ℕ) := by unfold sideNN; fun_prop

theorem sideView_polyT (hl : Unary lam) : PolyT (sideView g tr lam) := by
  unfold sideView
  exact viewAt_polyT g tr (hl.comp (by fun_prop)) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)

/-! ### The procedures -/

variable [HasSize C] [Carried C]

/-- Every step of the procedure for the weight of a merged node is polynomial-time, if this holds of
the procedure `R` for
the entries of the tensors. -/
@[instance_reducible] def IsPolyT.sideWP {R : Stepped (C × IQ) ℤ} [IsPolyT R] (hl : PolyT lam) :
    IsPolyT (sideWP g tr lam R) :=
  haveI := IsPolyT.mapIn (M := R) (sideQuery_polyT g tr hl)
  haveI := IsPolyT.prodRange (M := mapIn (sideQuery g tr lam) R) (N := sideG g) (sideG_polyT g)
  haveI : IsPolyT (Stepped.const 0 : Stepped ((C × ℕ) × WQ) ℤ) := IsPolyT.const 0
  IsPolyT.ite (sideChk_polyT g tr hl)

/-- Every step of the procedure for a factor of the interaction of two merged nodes, a product over
their rectangles, is
polynomial-time. -/
@[instance_reducible] def IsPolyT.sideFP (hl : Unary lam) : IsPolyT (sideFP g tr lam) :=
  haveI := IsPolyT.cutP tr
  haveI := IsPolyT.mapIn (M := Prog.cutP tr) (sideView_polyT g tr hl)
  haveI : IsPolyT (Stepped.const 1 : Stepped (((C × ℕ) × FQ) × ℕ) ℤ) := IsPolyT.const 1
  haveI := IsPolyT.ite (M := mapIn (sideView g tr lam) (Prog.cutP tr)) (N := Stepped.const 1) (sideIsRect_polyT (C := C) g)
  haveI := IsPolyT.prodRange (M := Stepped.ite (sideIsRect g) (mapIn (sideView g tr lam) (Prog.cutP tr)) (Stepped.const 1))
    (N := sideNN g) (sideNN_polyT g)
  haveI : IsPolyT (Stepped.const 0 : Stepped ((C × ℕ) × FQ) ℤ) := IsPolyT.const 0
  IsPolyT.ite (sideEdges_polyT g tr hl.poly)

end ctx

end Groundwork.Prog
