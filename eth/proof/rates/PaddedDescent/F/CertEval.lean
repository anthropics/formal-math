/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import PaddedDescent.F.FuelCert
import PaddedDescent.F.CertTop

/-! # The evaluations and the choice of the layers are polynomial-time

Certificates (`PolyT`) for the part of the function `A` of proof/rates/PaddedDescent/F/Prog.lean
that works on one sparse formula: the value of a network (`valF`), one
evaluation (`evalF`), the test that puts a clause into a layer (`dropE`), the placing of a clause
(`placeAt`, `placeE`), the layers (`layersF`) and the count
(`countM`). They prove the interface statement `StCertValF` of
proof/rates/PaddedDescent/F/Interfaces.lean, and certificates for an evaluation, the layers and the
count
whose arguments are polynomial-time functions of a context; the certificates of the rebalancing, the
descent through the levels, the brute force at the bottom and the network of marks are hypotheses. -/

@[expose] public section

namespace PaddedDescent.F.CertEval

open Groundwork Groundwork.Prog
open PaddedDescent.F.Mark (Cl cls nProf adm markF dropE placeAt placeE)

variable {α : Type} [Enc α]

/-! ### The value of a network -/

/-- The top rebalancing, all levels and the brute force at the bottom are polynomial-time, for every
network whose four functions are. -/
theorem certValF (hR : StCertRebal) (hD : StCertDescend) (hB : StCertBrute) : StCertValF := by
  intro C _ F hF α _ pad S c hp hS hc
  have h1 : PolyT fun x => rebalF (pad x) (S x).2.length (gU (S x).2).length F (c x) :=
    hR _ F hF _ _ _ _ _ hp (by fun_prop) (by fun_prop) hc
  have h2 : PolyT fun q : α × PInst => descend (pad q.1) (S q.1).1 q.2 :=
    PolyT.comp (g := fun q : α × PInst => (pad q.1, (S q.1).1, q.2)) hD (by fun_prop)
  have h3 : PolyT fun q : (α × PInst) × PInst => bruteF (pad q.1.1) 256 q.2 :=
    PolyT.comp (g := fun q : (α × PInst) × PInst => (pad q.1.1, q.2)) hB (by fun_prop)
  unfold valF
  fun_prop

/-! ### One evaluation -/

/-- The list of all clauses with the index of their layer is polynomial-time. -/
theorem cls_polyT {Ls : α → List Fml} (hL : PolyT Ls) : PolyT fun x => cls (Ls x) := by
  unfold cls; fun_prop

/-- The number of profiles is polynomial-time, for g and the number of layers in unary and a
polynomial-time number of clauses. -/
theorem nProf_polyT {g M R : α → ℕ} (hg : Unary g) (hM : PolyT M) (hR : Unary R) : PolyT fun x => nProf (g x) (M x) (R x) := by
  unfold nProf; fun_prop

/-- One evaluation, with the pad, the schedule, the parameters and the layers as arbitrary functions
of a context. -/
theorem evalF_polyT (k : ℕ) (hV : StCertValF) (hM : StCertMark) (hA : StCertAdm) {pad : α → U} {S : α → List Lvl × U} {p : α → U × U × U × U}
    {Ls : α → List Fml} (hp : PolyT pad) (hS : PolyT S) (hq : PolyT p) (hL : PolyT Ls) :
    PolyT fun x => evalF k (pad x) (S x) (p x) (Ls x) := by
  have h0 : PolyT fun x => nProf (gU (S x).2).length (cls (Ls x)).length (Ls x).length :=
    nProf_polyT (by fun_prop) (PolyT.length (cls_polyT hL)) (by fun_prop)
  have h1 : PolyT fun r : α × ℕ => adm k (gU (S r.1).2).length (p r.1).1.length (p r.1).2.1.length (Ls r.1) r.2 :=
    PolyT.comp (g := fun r : α × ℕ => ((gU (S r.1).2, (p r.1).1, (p r.1).2.1), Ls r.1, r.2)) (hA k) (by fun_prop)
  have h2 : PolyT fun r : α × ℕ => valF (pad r.1) (S r.1) markF ((gU (S r.1).2, (p r.1).1, (p r.1).2.2.1, (p r.1).2.2.2), (Ls r.1, r.2)) :=
    hV _ markF hM _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  unfold evalF
  fun_prop

/-! ### The choice of the layers, for any polynomial-time evaluation function -/

section choice

variable {ev : α → List Fml → ℤ} {w : α → ℕ} {Ls : α → List Fml} {C : α → Cl}

/-- The test that puts a clause into layer i. -/
theorem dropE_polyT (hev : PolyT fun q : α × List Fml => ev q.1 q.2) (hw : Unary w) (hL : PolyT Ls) (hC : PolyT C) {i : α → ℕ}
    (hi : PolyT i) : PolyT fun x => dropE (ev x) (w x) (Ls x) (C x) (i x) := by
  have h1 : PolyT fun x => ev x ((C x :: (Ls x).getD (i x) []) :: (Ls x).drop (i x + 1)) :=
    PolyT.comp (g := fun x => (x, (C x :: (Ls x).getD (i x) []) :: (Ls x).drop (i x + 1))) hev (by fun_prop)
  have h2 : PolyT fun x => ev x ((Ls x).drop (i x)) := PolyT.comp (g := fun x => (x, (Ls x).drop (i x))) hev (by fun_prop)
  have u1 : Unary fun x => ((Ls x).drop (i x)).flatten.length + 3 := by fun_prop
  have u2 : Unary fun x => ((Ls x).drop (i x + 1)).flatten.length := by fun_prop
  have p1 : PolyT fun x => 2 ^ (((Ls x).drop (i x)).flatten.length + 3) := pow_polyT (PolyT.const 2) u1
  have p2 : PolyT fun x => 3 ^ ((Ls x).drop (i x + 1)).flatten.length * 2 ^ w x :=
    PolyT.mul (pow_polyT (PolyT.const 3) u2) (pow_polyT (PolyT.const 2) hw)
  exact PolyT.decide_leZ (PolyT.mulZ (PolyT.subZ h1 h2) (PolyT.natCast p1)) (PolyT.natCast p2)

/-- A clause added to layer i. -/
theorem placeAt_polyT (hL : PolyT Ls) (hC : PolyT C) {i : α → ℕ} (hi : PolyT i) : PolyT fun x => placeAt (Ls x) (C x) (i x) := by
  unfold placeAt; fun_prop

/-- A clause put into the first layer whose test holds. -/
theorem placeE_polyT (hev : PolyT fun q : α × List Fml => ev q.1 q.2) (hw : Unary w) (hL : PolyT Ls) (hC : PolyT C) :
    PolyT fun x => placeE (ev x) (w x) (Ls x) (C x) := by
  have h1 : PolyT fun r : α × ℕ => dropE (ev r.1) (w r.1) (Ls r.1) (C r.1) r.2 :=
    dropE_polyT (ev := fun r : α × ℕ => ev r.1) (PolyT.comp (g := fun q : (α × ℕ) × List Fml => (q.1.1, q.2)) hev (by fun_prop))
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : PolyT fun x => ((List.range ((Ls x).length - 1)).find? (dropE (ev x) (w x) (Ls x) (C x))).getD ((Ls x).length - 1) := by
    fun_prop
  unfold placeE
  exact placeAt_polyT hL hC h2

end choice

/-! ### The layers and the count -/

section count

variable {pad : α → U} {S : α → List Lvl × U} {p : α → U × U × U × U} {R : α → ℕ} {ψ : α → Fml}

/-- R + 1 empty layers. -/
theorem empty_polyT (hR : Unary R) : PolyT fun x => List.replicate (R x + 1) ([] : Fml) := by
  have h : PolyT fun x => (List.replicate (R x + 1) ()).map fun _ => ([] : Fml) := by fun_prop
  exact h.congr fun x => List.map_replicate

/-- The layers of a formula, with the number of layers in unary. -/
theorem layersF_polyT (k : ℕ) (hV : StCertValF) (hM : StCertMark) (hA : StCertAdm) (hp : PolyT pad) (hS : PolyT S) (hq : PolyT p) (hR : Unary R)
    (hψ : PolyT ψ) : PolyT fun x => layersF k (pad x) (S x) (p x) (R x) (ψ x) := by
  have hev : PolyT fun q : (α × List Fml × Cl) × List Fml => evalF k (pad q.1.1) (S q.1.1) (p q.1.1) q.2 :=
    evalF_polyT k hV hM hA (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hg : PolyT fun r : α × List Fml × Cl => placeE (evalF k (pad r.1) (S r.1) (p r.1)) (p r.1).2.1.length r.2.1 r.2.2 :=
    placeE_polyT (ev := fun r : α × List Fml × Cl => evalF k (pad r.1) (S r.1) (p r.1)) hev (by fun_prop) (by fun_prop) (by fun_prop)
  unfold layersF
  exact foldl_cap (pad := pad) (l := ψ) (a := fun x => List.replicate (R x + 1) ([] : Fml))
    (g := fun x Ls C => placeE (evalF k (pad x) (S x) (p x)) (p x).2.1.length Ls C) [] hp hψ (empty_polyT hR) hg

/-- The count of one sparse formula, with the number of layers in unary. -/
theorem countM_polyT (k : ℕ) (hV : StCertValF) (hM : StCertMark) (hA : StCertAdm) (hp : PolyT pad) (hS : PolyT S) (hq : PolyT p) (hR : Unary R)
    (hψ : PolyT ψ) : PolyT fun x => countM k (pad x) (S x) (p x) (R x) (ψ x) := by
  have h := layersF_polyT k hV hM hA hp hS hq hR hψ
  unfold countM
  exact evalF_polyT k hV hM hA hp hS hq (by fun_prop)

end count

end PaddedDescent.F.CertEval
