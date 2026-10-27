/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfTab
public import PaddedDescent.F.FuelCert

/-! # The tables of the matrices of the operators are polynomial-time

Certificates (`PolyT`) for the functions of proof/rates/ClauseBound/Inst/HalfTab.lean, each with all
its arguments as functions of an input x. The numbers W and h are given in unary; the pad, the list
of
monomials, the partitions and all other numbers are data. The two folds (`tabOp`, `tabKF`) cut their
state off by the pad after every round, so they need no bound on its growth. The end
of the file: `topF_polyT` and `botF_polyT`. -/

public section

namespace ClauseBound.Inst.Half

open Groundwork PaddedDescent.F ClauseBound.Inst.Rec

variable {α : Type} [Enc α]

/-! ### Lists -/

/-- Erasing the first occurrence of a number. -/
@[fun_prop] theorem erase_polyT {l : α → List ℕ} {a : α → ℕ} (hl : PolyT l) (ha : PolyT a) : PolyT fun x => (l x).erase (a x) := by
  have h : PolyT fun x => (l x).take ((l x).idxOf (a x)) ++ (l x).drop ((l x).idxOf (a x) + 1) := by fun_prop
  exact h.congr fun x => by rw [List.erase_eq_eraseIdx_of_idxOf rfl, List.eraseIdx_eq_take_drop_succ]

/-- The number of occurrences in a list is given in unary. -/
@[fun_prop] theorem count_unary {l : α → List ℕ} {a : α → ℕ} (hl : PolyT l) (ha : PolyT a) : Unary fun x => (l x).count (a x) :=
  Unary.of_le (Unary.of_length hl) (by fun_prop) fun _ => List.count_le_length

/-! ### Entries and tables -/

/-- The coefficient of one term of the recursion. -/
@[fun_prop] theorem betF_polyT {W n : α → ℕ} {r : α → ℤ} (hW : Unary W) (hn : PolyT n) (hr : PolyT r) :
    PolyT fun x => betF (W x) (n x) (r x) := by
  unfold betF; fun_prop

/-- The table of a polynomial-time function of two listed monomials. -/
theorem tab_polyT {flat : α → List (List ℕ)} {f : α → List ℕ → List ℕ → ℤ} (hf : PolyT flat)
    (hg : PolyT fun p : α × List ℕ × List ℕ => f p.1 p.2.1 p.2.2) : PolyT fun x => tab (flat x) (f x) := by
  unfold tab
  refine PolyT.flatMap (f := fun x π => (flat x).map fun σ => f x π σ) ?_ hf
  refine PolyT.map (f := fun (p : α × List ℕ) σ => f p.1 p.2 σ) (l := fun p => flat p.1) ?_ (by fun_prop)
  exact PolyT.comp (g := fun q : (α × List ℕ) × List ℕ => (q.1.1, q.1.2, q.2)) hg (by fun_prop)

/-- Reading an entry of a table. -/
@[fun_prop] theorem lookT_polyT {flat : α → List (List ℕ)} {T : α → List ℤ} {π σ : α → List ℕ} (hf : PolyT flat) (hT : PolyT T)
    (hπ : PolyT π) (hσ : PolyT σ) : PolyT fun x => lookT (flat x) (T x) (π x) (σ x) := by
  unfold lookT; fun_prop

/-- One entry of the normally ordered product with a family given by its table. -/
@[fun_prop] theorem nopE_polyT {W n : α → ℕ} {flat : α → List (List ℕ)} {T : α → List ℤ} {π σ : α → List ℕ} (hW : Unary W) (hn : PolyT n)
    (hf : PolyT flat) (hT : PolyT T) (hπ : PolyT π) (hσ : PolyT σ) :
    PolyT fun x => nopE (W x) (n x) (flat x) (T x) (π x) (σ x) := by
  unfold nopE; fun_prop

/-- The table of the identity. -/
@[fun_prop] theorem oneT_polyT {flat : α → List (List ℕ)} (hf : PolyT flat) : PolyT fun x => oneT (flat x) := by
  unfold oneT
  exact tab_polyT (f := fun _ π σ => if π = σ then 1 else 0) hf (by fun_prop)

/-! ### The table of a[·] -/

/-- The table of a[·], built part by part and cut off by the pad after every round. -/
@[fun_prop] theorem tabOp_polyT {pad : α → U} {W : α → ℕ} {flat : α → List (List ℕ)} {a : α → List ℕ} (hp : PolyT pad) (hW : Unary W)
    (hf : PolyT flat) (ha : PolyT a) : PolyT fun x => tabOp (pad x) (W x) (flat x) (a x) := by
  unfold tabOp
  refine foldl_cap (pad := pad) (l := fun x => (a x).reverse) (a := fun x => oneT (flat x))
    (g := fun x T n => tab (flat x) (nopE (W x) n (flat x) T)) [] hp (by fun_prop) (by fun_prop) ?_
  exact tab_polyT (flat := fun p : α × List ℤ × ℕ => flat p.1) (f := fun p => nopE (W p.1) p.2.2 (flat p.1) p.2.1) (by fun_prop) (by fun_prop)

/-! ### The tables of the parts of a^μ -/

/-- The tables before the first round. -/
@[fun_prop] theorem kfInit_polyT {h : α → ℕ} {flat : α → List (List ℕ)} (hh : Unary h) (hf : PolyT flat) :
    PolyT fun x => kfInit (h x) (flat x) := by
  have h0 : PolyT fun p : α × ℕ => tab (flat p.1) fun _ _ => (0 : ℤ) :=
    tab_polyT (flat := fun p : α × ℕ => flat p.1) (f := fun _ _ _ => 0) (by fun_prop) (by fun_prop)
  unfold kfInit; fun_prop

/-- One entry of one table of the next round. -/
theorem kfEntry_polyT {W n w : α → ℕ} {flat : α → List (List ℕ)} {S : α → List (List ℤ)} {π σ : α → List ℕ} (hW : Unary W) (hn : PolyT n)
    (hw : PolyT w) (hf : PolyT flat) (hS : PolyT S) (hπ : PolyT π) (hσ : PolyT σ) :
    PolyT fun x => sumR (min (n x) (W x)) fun j =>
      if j + 1 ≤ w x then sgnZ ((n x - 1 : ℕ) : ℤ) * chooseZ (n x : ℤ) (j + 1) * nopE (W x) (j + 1) (flat x) ((S x).getD (w x - (j + 1)) []) (π x) (σ x)
      else 0 := by
  refine sumR_polyT (w := fun x => min (n x) (W x)) (f := fun x j =>
      if j + 1 ≤ w x then sgnZ ((n x - 1 : ℕ) : ℤ) * chooseZ (n x : ℤ) (j + 1) * nopE (W x) (j + 1) (flat x) ((S x).getD (w x - (j + 1)) []) (π x) (σ x)
      else 0) (by fun_prop) ?_
  have := hW.poly
  fun_prop

/-- One round: the tables for one more factor. -/
@[fun_prop] theorem kfStep_polyT {W h n : α → ℕ} {flat : α → List (List ℕ)} {S : α → List (List ℤ)} (hW : Unary W) (hh : Unary h) (hn : PolyT n)
    (hf : PolyT flat) (hS : PolyT S) : PolyT fun x => kfStep (W x) (h x) (n x) (flat x) (S x) := by
  unfold kfStep
  refine PolyT.map (l := fun x => List.range (h x + 1)) ?_ (by fun_prop)
  refine tab_polyT (flat := fun p : α × ℕ => flat p.1) (f := fun p π σ => sumR (min (n p.1) (W p.1)) fun j =>
      if j + 1 ≤ p.2 then sgnZ ((n p.1 - 1 : ℕ) : ℤ) * chooseZ (n p.1 : ℤ) (j + 1) *
        nopE (W p.1) (j + 1) (flat p.1) ((S p.1).getD (p.2 - (j + 1)) []) π σ
      else 0) (by fun_prop) ?_
  exact kfEntry_polyT (α := (α × ℕ) × List ℕ × List ℕ) (W := fun q => W q.1.1) (n := fun q => n q.1.1) (w := fun q => q.1.2)
    (flat := fun q => flat q.1.1) (S := fun q => S q.1.1) (π := fun q => q.2.1) (σ := fun q => q.2.2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-- The tables of the parts of weight 0, …, h of a^μ, cut off by the pad after every round. -/
@[fun_prop] theorem tabKF_polyT {pad : α → U} {W h : α → ℕ} {flat : α → List (List ℕ)} {μ : α → List ℕ} (hp : PolyT pad) (hW : Unary W)
    (hf : PolyT flat) (hh : Unary h) (hμ : PolyT μ) : PolyT fun x => tabKF (pad x) (W x) (flat x) (h x) (μ x) := by
  unfold tabKF
  exact foldl_cap (pad := pad) (l := fun x => (μ x).reverse) (a := fun x => kfInit (h x) (flat x))
    (g := fun x S n => kfStep (W x) (h x) n (flat x) S) [] hp (by fun_prop) (by fun_prop) (by fun_prop)

/-! ### The two functions of a factorization -/

/-- The number z_ν. -/
@[fun_prop] theorem zzF_polyT {ν : α → List ℕ} (hν : PolyT ν) : PolyT fun x => zzF (ν x) := by
  unfold zzF; fun_prop

/-- A binomial coefficient with a natural number on top vanishes when the lower number is larger. -/
theorem chooseZ_clip (a i : ℕ) : chooseZ (a : ℤ) i = if i ≤ a then chooseZ (a : ℤ) (min i a) else 0 := by
  split_ifs with h
  · rw [min_eq_left h]
  · rw [chooseZ_eq, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (not_le.1 h), Nat.cast_zero]

/-- A binomial coefficient with a natural number in unary on top; the lower number may be in binary. -/
theorem chooseZ_nat_polyT {a i : α → ℕ} (ha : Unary a) (hi : PolyT i) : PolyT fun x => chooseZ (a x : ℤ) (i x) := by
  have := ha.poly
  have h : PolyT fun x => if i x ≤ a x then chooseZ (a x : ℤ) (min (i x) (a x)) else 0 := by fun_prop
  exact h.congr fun x => (chooseZ_clip (a x) (i x)).symm

/-- The function on top of a factorization is polynomial-time; W and h are given in unary. -/
theorem topF_polyT {pad : α → U} {W h i : α → ℕ} {flat : α → List (List ℕ)} {μ π σ : α → List ℕ} {r : α → ℤ} (hp : PolyT pad) (hW : Unary W)
    (hf : PolyT flat) (hh : Unary h) (hμ : PolyT μ) (hi : PolyT i) (hr : PolyT r) (hπ : PolyT π) (hσ : PolyT σ) :
    PolyT fun x => topF (pad x) (W x) (flat x) (h x) (μ x) (i x) (r x) (π x) (σ x) := by
  have := hh.poly
  have hc : PolyT fun p : α × ℕ => chooseZ (((min p.2 (h p.1 + 1) : ℕ) : ℤ) + (h p.1 : ℤ)) (i p.1) := by
    have h1 := chooseZ_nat_polyT (α := α × ℕ) (a := fun p => min p.2 (h p.1 + 1) + h p.1) (i := fun p => i p.1) (by fun_prop) (by fun_prop)
    exact h1.congr fun p => by push_cast; rfl
  have hs : PolyT fun x => sumR (h x + 1) fun w =>
      chooseZ ((w : ℤ) + h x) (i x) * lookT (flat x) ((tabKF (pad x) (W x) (flat x) (h x) (μ x)).getD w []) (π x) (σ x) :=
    sumR_polyT (w := fun x => h x + 1) (f := fun x w =>
      chooseZ ((w : ℤ) + h x) (i x) * lookT (flat x) ((tabKF (pad x) (W x) (flat x) (h x) (μ x)).getD w []) (π x) (σ x)) (by fun_prop)
      (PolyT.mulZ hc (by fun_prop))
  unfold topF; fun_prop

/-- The function below of a factorization is polynomial-time; W and h are given in unary. -/
theorem botF_polyT {pad : α → U} {W h : α → ℕ} {flat : α → List (List ℕ)} {μ π σ : α → List ℕ} {r : α → ℤ} (hp : PolyT pad) (hW : Unary W)
    (hf : PolyT flat) (hh : Unary h) (hμ : PolyT μ) (hr : PolyT r) (hπ : PolyT π) (hσ : PolyT σ) :
    PolyT fun x => botF (pad x) (W x) (flat x) (h x) (μ x) (r x) (π x) (σ x) := by
  have hd : PolyT fun x => ((factN (h x) / zzF (μ x) : ℕ) : ℤ) := PolyT.natCast (PolyT.div (factN_polyT hh) (zzF_polyT hμ))
  unfold botF
  exact PolyT.ite' (PolyT.decide_eq hr (PolyT.subZ (PolyT.natCast (PolyT.sum hπ)) (PolyT.natCast (PolyT.sum hσ))))
    (PolyT.mulZ hd (lookT_polyT hf (tabOp_polyT hp hW hf hμ) hπ hσ)) (PolyT.const 0)

end ClauseBound.Inst.Half
