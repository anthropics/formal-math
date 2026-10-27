/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.CutWord
public import StepMachines.Math.Digits
public import StepMachines.Prog.Brute
public import Mathlib.Logic.Equiv.Fin.Basic

/-! The g × g grid of Section 2.5 of the paper, on words (lists of bits), for rows (tr = false) and
columns (tr = true) at once.
A «part» is a row, or a column if tr. The node number x of the part a is the node (a,x) of the grid,
or of the transposed
grid if tr; its position among the g² nodes of the instance is x + g·a, or a + g·x if tr. A
half-edge is one end's
copy of the label of an edge. The word of a state of a part: for each of its g nodes, the g²
half-edges that start there,
in the order of the positions of their other ends, n bits each. -/

@[expose] public section

namespace Groundwork.Grid

open Finset

/-- The g² nodes of the instance on the grid; transposed if tr. -/
def gridE (g : ℕ) (tr : Bool) : Fin (g * g) ≃ Fin g × Fin g :=
  if tr = true then finProdFinEquiv.symm.trans (Equiv.prodComm _ _) else finProdFinEquiv.symm

/-- The position of the node number i of the part a. -/
def node (g : ℕ) (tr : Bool) (a i : ℕ) : ℕ := if tr = true then a + g * i else i + g * a

/-- The position of a node of the grid among the g² nodes of the instance. -/
theorem gridE_symm_val (g : ℕ) (tr : Bool) (w : Fin g × Fin g) : ((gridE g tr).symm w : ℕ) = node g tr w.1 w.2 := by
  cases tr <;> rfl

/-- Positions are below g². -/
theorem node_lt {g : ℕ} (tr : Bool) {a i : ℕ} (ha : a < g) (hi : i < g) : node g tr a i < g * g := by
  have key : ∀ {a i : ℕ}, a < g → i < g → i + g * a < g * g := fun {a i} ha hi =>
    calc i + g * a < g + g * a := by omega
      _ = g * (a + 1) := by ring
      _ ≤ g * g := Nat.mul_le_mul_left _ ha
  cases tr
  · exact key ha hi
  · exact key hi ha

/-- In the word z of a state of a part: the half-edge from the node number x of the part to the node
at position u. -/
def he (g ℓ : ℕ) (z : List Bool) (x u : ℕ) : List Bool := block ℓ u (block (g * g * ℓ) x z)

/-- A half-edge in the word of a state has ℓ bits. -/
theorem length_he {g ℓ : ℕ} {z : List Bool} (hz : z.length = g ^ 3 * ℓ) {x u : ℕ} (hx : x < g) (hu : u < g * g) :
    (he g ℓ z x u).length = ℓ := by
  have h1 : (block (g * g * ℓ) x z).length = g * g * ℓ := length_block (by
    rw [hz, show g ^ 3 * ℓ = g * (g * g * ℓ) by ring]
    exact Nat.mul_le_mul_right _ hx)
  exact length_block (by rw [h1]; exact Nat.mul_le_mul_right _ hu)

/-- The code, on words of g·n bits, of the labels of the g edges between two parts that join nodes
of the same number. -/
def vC (g n : ℕ) : Code (univ : Finset (Fin g → Bits n)) (g * n) :=
  ((bitsC n).blocks (Equiv.refl (Fin g))).cast Fintype.piFinset_univ rfl

/-- The code, on words of g²·n bits, of the half-edges that start at one node. -/
def nodeC (g : ℕ) (tr : Bool) (n : ℕ) : Code (univ : Finset (Fin g × Fin g → Bits n)) (g * g * n) :=
  ((bitsC n).blocks (gridE g tr).symm).cast Fintype.piFinset_univ rfl

/-- The code, on words of g³·n bits, of a state of a part. -/
def stC (g : ℕ) (tr : Bool) (n : ℕ) : Code (univ : Finset (Fin g → Fin g × Fin g → Bits n)) (g ^ 3 * n) :=
  ((nodeC g tr n).blocks (Equiv.refl (Fin g))).cast Fintype.piFinset_univ (by ring)

theorem vC_full (g n : ℕ) : (vC g n).Full := Code.full_cast _ _ _ (Code.full_blocks _ _ (bitsC_full n))

theorem nodeC_full (g : ℕ) (tr : Bool) (n : ℕ) : (nodeC g tr n).Full :=
  Code.full_cast _ _ _ (Code.full_blocks _ _ (bitsC_full n))

theorem stC_full (g : ℕ) (tr : Bool) (n : ℕ) : (stC g tr n).Full :=
  Code.full_cast _ _ _ (Code.full_blocks _ _ (nodeC_full g tr n))

/-- The state named by a word, read half-edge by half-edge. -/
theorem stC_dec (g : ℕ) (tr : Bool) (n : ℕ) (z : List Bool) (x : Fin g) (w' : Fin g × Fin g) :
    (stC g tr n).dec z x w' = bitsOf n (he g n z x (node g tr w'.1 w'.2)) := by
  rw [← gridE_symm_val]
  rfl

/-- An instance on words of n bits, read as an instance with labels in Bits n; [] at the node
itself. -/
noncomputable def instW {K : ℕ} (n : ℕ) (Rm : Inst (Fin K) (List Bool)) : Inst (Fin K) (Bits n) :=
  fun v θ => Rm v fun u => if u = v then [] else (bitsC n).enc (θ u)

/-- The same, carried to the grid; to the transposed grid if tr. -/
noncomputable def sideR (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : Inst (Fin g × Fin g) (Bits n) :=
  onGrid (instW n Rm) (fun _ => false) (gridE g tr)

/-- The instance on the transposed grid is the transpose of the instance on the grid. -/
theorem sideR_true (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : sideR g true n Rm = trInst (sideR g false n Rm) := by
  rfl

/-- Z on words is Z with labels in Bits n. -/
theorem ZW_eq_Z {K : ℕ} (n : ℕ) (Rm : Inst (Fin K) (List Bool)) (d : Bits n) : Inst.ZW n [] Rm = (instW n Rm).Z d := by
  unfold Inst.ZW Inst.Z labellings
  have hb : Set.BijOn (bitsC n).enc (univ : Finset (Bits n)) (words n) := by
    have := (bitsC n).bijOn_enc
    rwa [bitsC_full] at this
  rw [sum_tuples_map (fun p : Fin K × Fin K => p.1 < p.2) (T := fun _ => words n)
    (T' := fun _ => (univ : Finset (Bits n))) [] d (fun _ => (bitsC n).enc) (fun _ _ => hb)]
  refine sum_congr rfl fun Λ _ => prod_congr rfl fun v _ => ?_
  unfold instW
  congr 1
  funext u
  unfold star pr
  by_cases h : u = v
  · subst h; simp
  · have : min v u < max v u := min_lt_max.2 (Ne.symm h)
    simp [h, this]

/-- The bound 2^B on the instance at the queries that are asked passes to the grid. -/
theorem abs_sideR_le {g n B : ℕ} (tr : Bool) {Rm : Inst (Fin (g * g)) (List Bool)} (hR : Prog.BoundedInst n B Rm)
    (w : Fin g × Fin g) (h : Fin g × Fin g → Bits n) : |sideR g tr n Rm w h| ≤ 2 ^ B := by
  unfold sideR onGrid
  split_ifs
  · refine hR _ _ (fun u hu => ?_) (by simp)
    rw [if_neg hu]
    exact (bitsC n).length_enc (mem_univ _)
  · rw [abs_zero]
    positivity

/-- The tensor of a node of the grid, at the word of the half-edges that start at this node: 0
unless the block at the
node's own position is all zeros. -/
theorem sideR_nodeC (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (w : Fin g × Fin g) {wn : List Bool}
    (h : wn.length = g * g * n) :
    sideR g tr n Rm w ((nodeC g tr n).dec wn) =
      if (block n ((gridE g tr).symm w) wn).all (!·) = true then
        Rm ((gridE g tr).symm w) (fun u => if u = (gridE g tr).symm w then [] else block n u wn)
      else 0 := by
  have hl : ∀ u : Fin (g * g), (block n u wn).length = n := fun u =>
    length_block (by rw [h]; exact Nat.mul_le_mul_right _ u.2)
  have hd : ∀ w', (nodeC g tr n).dec wn w' = bitsOf n (block n ((gridE g tr).symm w') wn) := fun _ => rfl
  unfold sideR onGrid instW
  simp only [hd, bitsOf_eq_zero (hl _), Equiv.symm_apply_apply]
  refine if_congr Iff.rfl (congrArg _ (funext fun u => if_congr Iff.rfl rfl ?_)) rfl
  exact (bitsC n).enc_dec (by rw [bitsC_full]; exact mem_words.2 (hl u))

end Groundwork.Grid
