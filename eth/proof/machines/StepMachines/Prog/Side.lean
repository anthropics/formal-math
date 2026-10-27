/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.GridDefs
public import StepMachines.Prog.CutProg
public import StepMachines.Math.SideX

/-! Procedures on words for the weights and the factors of the row network (tr = false) or the
column network (tr = true) of a term Z_ι
in the proof of Proposition 3 (Section 5). A part is one merged row or column. Context (c, y): the
number y encodes ι. -/

@[expose] public section

namespace Groundwork.Prog

open Finset Stepped
open Groundwork.Grid (he node c2 rectDig sideChunk sideItem sideCap)

/-! ### The weights -/

section W

variable {C : Type} (g : ℕ) (tr : Bool) (lam : C → ℕ)

/-- The half-edges from a node to itself are 0…0 and the edges inside the part agree. -/
def sideChk (x : (C × ℕ) × WQ) : Bool :=
  ((List.range g).all fun i => (he g (lam x.1.1) x.2.2 i (node g tr x.2.1 i)).all (!·)) &&
    (List.range g).all fun i => (List.range g).all fun i' =>
      decide (i' ≤ i) ||
        (he g (lam x.1.1) x.2.2 i (node g tr x.2.1 i') == he g (lam x.1.1) x.2.2 i' (node g tr x.2.1 i))

/-- The labels at the node number i of the part a, as the state z has them. -/
def sideLabels (ℓ a : ℕ) (z : List Bool) (i u : ℕ) : List Bool :=
  if u = node g tr a i then [] else he g ℓ z i u

/-- The query to the instance at the node number p.2 of the part. -/
def sideQuery (p : ((C × ℕ) × WQ) × ℕ) : C × IQ :=
  (p.1.1.1, (node g tr p.1.2.1 p.2, (List.range (g * g)).map (sideLabels g tr (lam p.1.1.1) p.1.2.1 p.1.2.2 p.2)))

/-- The number of nodes of a part. -/
def sideG (_ : (C × ℕ) × WQ) : ℕ := g

/-- The weight of a part: the product of the tensors' entries at its g nodes, or 0 if sideChk fails. -/
def sideWP [HasSize C] (R : Stepped (C × IQ) ℤ) : Stepped ((C × ℕ) × WQ) ℤ :=
  ite (sideChk g tr lam) (prodRange (sideG g) (mapIn (sideQuery g tr lam) R)) (const 0)

/-- What sideWP computes. -/
def sideWv (ℓ : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (chk : Bool) (a : ℕ) (z : List Bool) : ℤ :=
  if chk then
    ∏ i ∈ range g, (if h : node g tr a i < g * g then Rm ⟨node g tr a i, h⟩ (fun u => sideLabels g tr ℓ a z i u) else 1)
  else 0

variable {g tr lam}

/-- sideWP computes sideWv; its steps and sizes, given those of the procedure R of the instance. -/
theorem sideWP_runs [HasSize C] {R : Stepped (C × IQ) ℤ} {c : C} {B t S : ℕ} {Rm : Inst (Fin (g * g)) (List Bool)}
    (hR : ServesInst R c (lam c) B t S Rm) (y : ℕ) {a : ℕ} (ha : a < g) {z : List Bool}
    (hz : z.length = g ^ 3 * lam c) :
    (sideWP g tr lam R).Runs ((c, y), (a, z)) (g * (t + 1))
      (size ((c, y), (a, z)) + size g + (B * g + 2) + S + 3)
      (sideWv g tr (lam c) Rm (sideChk g tr lam ((c, y), (a, z))) a z) := by
  unfold sideWv
  cases hc : sideChk g tr lam ((c, y), (a, z)) with
  | false =>
    refine (ite_runs_false hc (const_runs (0 : ℤ) _)).mono ?_ ?_
    · have : 1 ≤ g * (t + 1) := Nat.mul_pos (by omega) (by omega)
      exact this
    · have : size (0 : ℤ) = 1 := rfl
      omega
  | true =>
    have hq : ∀ i < g, R.Runs (sideQuery g tr lam (((c, y), (a, z)), i)) t S
        (if h : node g tr a i < g * g then Rm ⟨node g tr a i, h⟩ (fun u => sideLabels g tr (lam c) a z i u) else 1) ∧
        (if h : node g tr a i < g * g then Rm ⟨node g tr a i, h⟩ (fun u => sideLabels g tr (lam c) a z i u)
          else 1).natAbs ≤ 2 ^ B := by
      intro i hi
      have hn := Grid.node_lt tr ha hi
      rw [dif_pos hn]
      have h := hR ⟨node g tr a i, hn⟩ (fun u => sideLabels g tr (lam c) a z i u) (fun u hu => by
        have : (u : ℕ) ≠ node g tr a i := fun h => hu (Fin.ext h)
        simp only [sideLabels, if_neg this]
        exact Grid.length_he hz hi u.2) (by simp [sideLabels])
      have e : sideQuery g tr lam (((c, y), (a, z)), i) =
          (c, node g tr a i, List.ofFn fun u : Fin (g * g) => sideLabels g tr (lam c) a z i u) := by
        simp only [sideQuery, map_range_eq_ofFn]
      rw [e]
      refine ⟨h.1, ?_⟩
      have := h.2
      rw [Int.abs_eq_natAbs] at this
      exact_mod_cast this
    have h := prodRange_runs (N := sideG g) (M := mapIn (sideQuery g tr lam) R) (a := ((c, y), (a, z))) (fun _ => t)
      (fun i => if h : node g tr a i < g * g then Rm ⟨node g tr a i, h⟩ (fun u => sideLabels g tr (lam c) a z i u)
        else 1)
      (2 ^ B) S Nat.one_le_two_pow (fun i hi => mapIn_runs (hq i hi).1) (fun i hi => (hq i hi).2)
    refine (ite_runs_true hc h).mono (by simp [sideG]) ?_
    have : size ((2 ^ B) ^ sideG g ((c, y), (a, z))) = B * g + 2 := by rw [sideG, ← pow_mul, size_two_pow]
    simp only [sideG] at this ⊢
    omega

end W

/-! ### The factors -/

/-- The input of the procedure of one rectangle: the rectangle on the nodes number i, i' of the
parts a, b, seen from a. -/
def viewAt (g : ℕ) (tr : Bool) (n y a b : ℕ) (z θ : List Bool) (i i' : ℕ) : CutQ :=
  ((decide (a < b), rectDig g tr n y (tri (min a b) (max a b)) (tri i i')),
    (he g n z i (node g tr b i'), he g n z i' (node g tr b i), sideChunk g tr n y a b θ (tri i i')))

/-- A half-edge read off any word has at most ℓ bits. -/
theorem length_he_le (g ℓ : ℕ) (z : List Bool) (x u : ℕ) : (he g ℓ z x u).length ≤ ℓ := by
  unfold he block
  rw [List.length_take]
  exact Nat.min_le_left _ _

section F

variable {C : Type} (g : ℕ) (tr : Bool) (lam : C → ℕ)

/-- The edges between nodes of the same number agree with the label. -/
def sideEdges (x : (C × ℕ) × FQ) : Bool :=
  (List.range g).all fun i => he g (lam x.1.1) x.2.2.1 i (node g tr x.2.1.2 i) == block (lam x.1.1) i x.2.2.2

/-- The counter j stands for the pair i = j / g, i' = j % g; is i < i'? -/
def sideIsRect (p : ((C × ℕ) × FQ) × ℕ) : Bool := decide (p.2 / g < p.2 % g)

/-- The input of the procedure of the rectangle of the counter. (i is taken modulo g; for every
counter of the loop, j < g·g,
this changes nothing.) -/
def sideView (p : ((C × ℕ) × FQ) × ℕ) : CutQ :=
  viewAt g tr (lam p.1.1.1) p.1.1.2 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 (p.2 / g % g) (p.2 % g)

/-- The range of the counter. -/
def sideNN (_ : (C × ℕ) × FQ) : ℕ := g * g

/-- The factor of two parts: the product over their rectangles of the procedure cutP, or 0 if
sideEdges fails. -/
def sideFP [HasSize C] : Stepped ((C × ℕ) × FQ) ℤ :=
  ite (sideEdges g tr lam)
    (prodRange (sideNN g) (ite (sideIsRect g) (mapIn (sideView g tr lam) (cutP tr)) (const 1)))
    (const 0)

/-- The value meant for sideFP: the product of sideItem over the counters j < g·g with j / g < j %
g, or 0 if edges is false. -/
def sideFv (n y : ℕ) (edges : Bool) (a b : ℕ) (z θ : List Bool) : ℤ :=
  if edges then ∏ j ∈ range (g * g), (if j / g < j % g then sideItem g tr n y a b z θ (j / g) (j % g) else 1) else 0

variable {g tr lam}

end F

end Groundwork.Prog
