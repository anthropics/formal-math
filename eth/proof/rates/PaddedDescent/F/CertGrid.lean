/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import PaddedDescent.F.FuelCert
public import ToTuring.Poly.Digits
public import ToTuring.Poly.Words

/-! # Certificates for the loop over the patterns and for the bottom

Polynomial time (PolyT), with the side length g of the grid as DATA in unary, for: the number of
rectangles nRect g, the prices
priceRow and priceCol of a pattern, the context sideCtx of the cheaper side network and the list of
patterns. From these, the certificate of
one level (StCertExpand) follows from those of the rebalancing with a given label length
(StCertRebalG) and of the side network (StCertSide); the label
length lamNext K g n that one level hands to the rebalancing is given in unary when K, g and the
label length n are. The last theorem is the
certificate of brute force at the bottom (StCertBrute). The proofs of the prices follow useRow_polyT
(proof/machines/ToTuring/Poly/Grid.lean),
where g is a constant of the machine. -/

@[expose] public section

namespace PaddedDescent.F.CertGrid

open Groundwork Groundwork.Prog

variable {α : Type} [Enc α]

/-! ### The number of rectangles -/

/-- The number of rectangles is the square of g(g−1)/2. -/
theorem nRect_eq_mul (g : ℕ) : nRect g = g * (g - 1) / 2 * (g * (g - 1) / 2) := by
  unfold nRect
  rw [Nat.choose_two_right, sq]

/-- There are at most g⁴ rectangles. -/
theorem nRect_le_mul (g : ℕ) : nRect g ≤ g * g * (g * g) := by
  rw [nRect_eq_mul]
  have h : g * (g - 1) / 2 ≤ g * g := (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  exact Nat.mul_le_mul h h

/-- The number of rectangles is polynomial-time in g. -/
@[fun_prop] theorem nRect_polyT {g : α → ℕ} (hg : PolyT g) : PolyT fun x => nRect (g x) := by
  have h1 : PolyT fun x => g x * (g x - 1) / 2 := PolyT.div (by fun_prop) (by fun_prop)
  exact (h1.mul h1).congr fun x => (nRect_eq_mul (g x)).symm

/-- The number of rectangles is given in unary if g is. -/
@[fun_prop] theorem nRect_unary {g : α → ℕ} (hg : Unary g) : Unary fun x => nRect (g x) :=
  ((hg.mul hg).mul (hg.mul hg)).of_le (nRect_polyT hg.poly) fun x => nRect_le_mul (g x)

/-- The number of patterns, (n+1)^(nRect g) for the label length n, is polynomial-time if g is given
in unary. -/
theorem numPat_polyT {g n : α → ℕ} (hg : Unary g) (hn : PolyT n) : PolyT fun x => (n x + 1) ^ nRect (g x) :=
  PolyT.pow_unary (by fun_prop) (nRect_unary hg)

/-! ### The prices -/

/-- The price of a pattern with the rows merged is polynomial-time, for g and the label length in
unary. -/
@[fun_prop] theorem priceRow_polyT {g n y : α → ℕ} (hg : Unary g) (hn : Unary n) (hy : PolyT y) :
    PolyT fun x => priceRow (g x) (n x) (y x) := by
  have hp := hn.poly
  have hu : Unary fun p : α × ℕ => n p.1 := hn.comp (by fun_prop)
  have h1 : PolyT fun x : α => (List.range (nRect (g x))).map fun q => capW (n x) (n x - digit (n x) (y x) q) :=
    PolyT.map (f := fun (x : α) q => capW (n x) (n x - digit (n x) (y x) q))
      (capW_polyT hu (by fun_prop) fun _ => Nat.sub_le _ _) (PolyT.range (nRect_unary hg))
  refine ((PolyT.const 2).mul h1.sum).congr fun x => ?_
  simp only [priceRow, sum_range_eq_list]

/-- The price of a pattern with the columns merged is polynomial-time, for g and the label length in
unary. -/
@[fun_prop] theorem priceCol_polyT {g n y : α → ℕ} (hg : Unary g) (hn : Unary n) (hy : PolyT y) :
    PolyT fun x => priceCol (g x) (n x) (y x) := by
  have hp := hn.poly
  have hu : Unary fun p : α × ℕ => n p.1 := hn.comp (by fun_prop)
  have h1 : PolyT fun x : α => (List.range (nRect (g x))).map fun q => capW (n x) (digit (n x) (y x) q) :=
    PolyT.map (f := fun (x : α) q => capW (n x) (digit (n x) (y x) q))
      (capW_polyT hu (by fun_prop) fun _ => digit_le _ _ _) (PolyT.range (nRect_unary hg))
  refine ((PolyT.const 2).mul h1.sum).congr fun x => ?_
  simp only [priceCol, sum_range_eq_list]

/-! ### One level -/

/-- The context of the cheaper side network. -/
@[fun_prop] theorem sideCtx_polyT {pad gu : α → U} {I : α → PInst} {y : α → ℕ} (hp : PolyT pad) (hg : PolyT gu) (hI : PolyT I)
    (hy : PolyT y) : PolyT fun x => sideCtx (pad x) (gu x) (I x) (y x) := by
  have hgl : Unary fun x => (gu x).length := Unary.of_length hg
  have hnl : Unary fun x => (I x).1.length := Unary.of_length (by fun_prop)
  have hd : PolyT fun x => decide (priceCol (gu x).length (I x).1.length (y x) < priceRow (gu x).length (I x).1.length (y x)) :=
    PolyT.decide_lt (priceCol_polyT hgl hnl hy) (priceRow_polyT hgl hnl hy)
  exact (hp.prodMk (hg.prodMk hd)).prodMk (hI.fst.prodMk (hy.prodMk hI.snd))

/-- The list of the patterns, cut off by the pad. -/
theorem patterns_polyT {pad gu : α → U} {I : α → PInst} (hp : PolyT pad) (hg : PolyT gu) (hI : PolyT I) :
    PolyT fun x => rng (pad x) (((I x).1.length + 1) ^ nRect (gu x).length) :=
  rng_polyT hp (numPat_polyT (Unary.of_length hg) (by fun_prop))

/-- The bound on the label bits that two nodes of a side network share is given in unary (`Unary`)
if g and the label length are. -/
theorem capM_unary {g n : α → ℕ} (hg : Unary g) (hn : Unary n) : Unary fun x => capM (g x) (n x) := by
  unfold capM; fun_prop

/-- The bound on U of the cheaper side network is given in unary if g and the label length are. -/
theorem Ubar_unary {g n : α → ℕ} (hg : Unary g) (hn : Unary n) : Unary fun x => Ubar (g x) (n x) := by
  unfold Ubar; fun_prop

/-- The label length one level down, with any number D in place of Dcol, is given in unary if K, g
and the label length are. -/
theorem lamNext_unary_aux (D : ℕ) {K g n : α → ℕ} (hK : Unary K) (hg : Unary g) (hn : Unary n) :
    Unary fun x => (D * Ubar (g x) (n x) + 3 * g x ^ 2 * capM (g x) (n x)) / (D * K x ^ 2) + 1 := by
  have h1 := Ubar_unary hg hn
  have h2 := capM_unary hg hn
  have h3 := hK.poly
  fun_prop

/-- The label length one level down is given in unary if K, g and the label length are. -/
theorem lamNext_unary {K g n : α → ℕ} (hK : Unary K) (hg : Unary g) (hn : Unary n) :
    Unary fun x => lamNext (K x) (g x) (n x) := lamNext_unary_aux Dcol hK hg hn

/-- The child of one pattern. -/
theorem childF_polyT (hR : StCertRebalG) (hS : StCertSide) {pad : α → U} {L : α → Lvl} {I : α → PInst} {y : α → ℕ}
    (hp : PolyT pad) (hL : PolyT L) (hI : PolyT I) (hy : PolyT y) : PolyT fun x => childF (pad x) (L x) (I x) (y x) :=
  hR SideCtx sideF hS α pad (fun x => (L x).1.length) (fun x => (L x).2.length)
    (fun x => lamNext (L x).1.length (L x).2.length (I x).1.length) (fun x => sideCtx (pad x) (L x).2 (I x) (y x)) hp
    (Unary.of_length (by fun_prop)) (Unary.of_length (by fun_prop))
    (lamNext_unary (Unary.of_length (by fun_prop)) (Unary.of_length (by fun_prop)) (Unary.of_length (by fun_prop)))
    (sideCtx_polyT hp (by fun_prop) hI hy)

/-- One level is polynomial-time, given the certificates of the rebalancing with a given label
length and of the side network. -/
theorem certExpand (hR : StCertRebalG) (hS : StCertSide) : StCertExpand := by
  have h1 : PolyT fun q : (U × Lvl × PInst) × ℕ => childF q.1.1 q.1.2.1 q.1.2.2 q.2 :=
    childF_polyT hR hS (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : PolyT fun p : U × Lvl × PInst => rng p.1 ((p.2.2.1.length + 1) ^ nRect p.2.1.2.length) :=
    patterns_polyT (by fun_prop) (by fun_prop) (by fun_prop)
  exact PolyT.filterMap (f := fun (p : U × Lvl × PInst) y => childF p.1 p.2.1 p.2.2 y) h1 h2

/-! ### The bottom -/

/-- Looking up an entry of a table is polynomial-time. -/
@[fun_prop] theorem look_polyT {T : α → Tab} {q : α → IQ} (hT : PolyT T) (hq : PolyT q) : PolyT fun x => look (T x) (q x) := by
  unfold look; fun_prop

/-- Brute force on K nodes, K a constant. -/
theorem bruteF_polyT (K : ℕ) {pad : α → U} {I : α → PInst} (hp : PolyT pad) (hI : PolyT I) :
    PolyT fun x => bruteF (pad x) K (I x) := by
  have hb : Unary fun x => K * (K - 1) / 2 * (I x).1.length := (Unary.const _).mul (Unary.of_length (by fun_prop))
  have hw : PolyT fun p : (α × ℕ) × ℕ => toWord (K * (K - 1) / 2 * (I p.1.1).1.length) p.1.2 :=
    PolyT.toWord' (hb.comp (by fun_prop)) (by fun_prop)
  have hq : PolyT fun p : (α × ℕ) × ℕ => look (I p.1.1).2
      (query0 K (I p.1.1).1.length [] (toWord (K * (K - 1) / 2 * (I p.1.1).1.length) p.1.2) p.2) :=
    look_polyT (by fun_prop) (query0_polyT K (by fun_prop) (by fun_prop) hw (by fun_prop))
  have hin : PolyT fun p : α × ℕ => prodL K fun v => look (I p.1).2
      (query0 K (I p.1).1.length [] (toWord (K * (K - 1) / 2 * (I p.1).1.length) p.2) v) :=
    prodL_polyT (n := fun _ => K) (f := fun (p : α × ℕ) v => look (I p.1).2
      (query0 K (I p.1).1.length [] (toWord (K * (K - 1) / 2 * (I p.1).1.length) p.2) v)) (Unary.const K) hq
  exact sumF_polyT (f := fun (x : α) y => prodL K fun v => look (I x).2
      (query0 K (I x).1.length [] (toWord (K * (K - 1) / 2 * (I x).1.length) y) v))
    (PolyT.pow_unary (by fun_prop) hb) hp hin

/-- Brute force on 256 nodes is polynomial-time: the statement `StCertBrute`. -/
theorem certBrute : StCertBrute := bruteF_polyT 256 (by fun_prop) (by fun_prop)

end PaddedDescent.F.CertGrid
