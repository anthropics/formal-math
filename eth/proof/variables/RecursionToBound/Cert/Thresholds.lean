/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Cert.Numbers
public import CountKSatRate.Cert
import StepSparsify.CertThCal
import UniformInK.Cert.Sparsify
import CountKSat.Poly
import PaddedDescent.F.FuelCert
import ClauseBound.ParityChecks.CertLib

/-! # The thresholds for a fraction ε, and the walk with them, are polynomial-time

Step 5 of Appendix D: «Take ε ≤ 1 between e and 2e». Here ε = min(a/b, 1) for a pair r = (a, b) of
natural numbers **written in binary**. So 1/ε may be exponential in the length of the input, but α =
⌈2(k−1)²·ε⁻¹·⌈log₂(32(k−1)²/ε)⌉⌉ still has polynomially many binary digits.

* `alphaC_polyT`: α is polynomial-time jointly in k and r, by the form without fractions
  (`alphaC_epsOf`).
* `thresholds_polyT`: the threshold θ_i of the sparsification (a number that the sparsification here
  uses and the paper does not print) is polynomial-time jointly in k, r and i, if i is given in
  unary (`StepSparsify.CertThCal.thetaC_polyT`, which takes α in binary).
* `occBound_polyT`: the bound on the occurrences, for k in unary.
* `stepC_polyT`: the two children of a node of the tree, for k and 2^k in unary and ε given by the
  pair r.
* `walkSG_polyT`: the walk that adds up. The state of the walk is cut off at the length of the
  padding string after every round, so there is no side condition.

Where a list is run through and its member must be given in unary (the index of a threshold), the
member j is replaced by min(j, k), which is in unary because k is; on the members of the list the
two agree. -/

public section

namespace RecursionToBound

open Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert UniformInK UniformInK.CertSparsify SparsificationLemma

variable {α : Type} [Enc α]

/-! ### α and the thresholds -/

/-- Division rounded up is polynomial-time. -/
theorem ceilDiv_polyT {m p : α → ℕ} (hm : PolyT m) (hp : PolyT p) : PolyT fun x => ceilDiv (m x) (p x) := by
  unfold ceilDiv; fun_prop

/-- (k − 1)² is polynomial-time. -/
theorem sqPred_polyT {k : α → ℕ} (hk : PolyT k) : PolyT fun x => sqPred (k x) := by
  unfold sqPred; fun_prop

/-- ⌈log₂(32(k−1)²/ε)⌉ is polynomial-time jointly in k and r. -/
theorem logN_polyT {k : α → ℕ} {r : α → ℕ × ℕ} (hk : PolyT k) (hr : PolyT r) : PolyT fun x => logN (k x) (r x) := by
  have h1 := sqPred_polyT hk
  unfold logN
  exact ClauseBound.ParityChecks.CertLib.clog_polyT (ceilDiv_polyT (by fun_prop) (by fun_prop))

/-- α without fractions is polynomial-time jointly in k and r. -/
theorem alphaN_polyT {k : α → ℕ} {r : α → ℕ × ℕ} (hk : PolyT k) (hr : PolyT r) : PolyT fun x => alphaN (k x) (r x) := by
  have h1 := sqPred_polyT hk
  have h2 := logN_polyT hk hr
  unfold alphaN
  exact ceilDiv_polyT (by fun_prop) (by fun_prop)

/-- α = ⌈2(k−1)²·ε⁻¹·⌈log₂(32(k−1)²/ε)⌉⌉, for ε = min(a/b, 1), is polynomial-time jointly in k and r =
(a, b). -/
theorem alphaC_polyT {k : α → ℕ} {r : α → ℕ × ℕ} (hk : PolyT k) (hr : PolyT r) : PolyT fun x => Cal.alphaC (k x) (epsOf (r x)) :=
  (alphaN_polyT hk hr).congr fun x => (alphaC_epsOf (k x) (r x)).symm

/-- The threshold θ_i is polynomial-time jointly in k, r and i, if i is given in unary. -/
theorem thresholds_polyT {k i : α → ℕ} {r : α → ℕ × ℕ} (hk : PolyT k) (hr : PolyT r) (hi : Unary i) : PolyT fun x => thresholds (k x) (r x) (i x) :=
  _root_.StepSparsify.CertThCal.thetaC_polyT (alphaC_polyT hk hr) hi

/-- The bound on the occurrences, 2·(θ₀ + … + θ_(k−1)) + 2, is polynomial-time jointly in k and r,
if k is given in unary. -/
theorem occBound_polyT {k : α → ℕ} {r : α → ℕ × ℕ} (hk : Unary k) (hr : PolyT r) : PolyT fun x => occBound (k x) (r x) := by
  have hk' := hk.poly
  have h1 : PolyT fun p : α × ℕ => thresholds (k p.1) (r p.1) (min p.2 (k p.1)) :=
    thresholds_polyT (by fun_prop) (by fun_prop) ((hk.comp (h := fun p : α × ℕ => p.1) (by fun_prop)).of_le (by fun_prop) fun p => Nat.min_le_right _ _)
  have h2 : PolyT fun x => List.range (k x) := PolyT.range hk
  have h : PolyT fun x => 2 * ((List.range (k x)).map fun j => thresholds (k x) (r x) (min j (k x))).sum + 2 := by fun_prop
  refine h.congr fun x => ?_
  rw [occBound_eq]
  have e : ((List.range (k x)).map fun j => thresholds (k x) (r x) (min j (k x))) = (List.range (k x)).map (thresholds (k x) (r x)) :=
    List.map_congr_left fun j hj => by rw [Nat.min_eq_left (List.mem_range.1 hj).le]
  rw [e]

/-! ### One step of the sparsification -/

/-- The list of the pairs (j, h), each with the threshold θ_(j−h), is polynomial-time jointly in k
and r, if k is given in unary. -/
theorem thrList_polyT {k : α → ℕ} {r : α → ℕ × ℕ} (hk : Unary k) (hr : PolyT r) :
    PolyT fun x => (pairsK (k x)).map fun jh => (jh, thresholds (k x) (r x) (jh.1 - jh.2)) := by
  have hk' := hk.poly
  have h1 := pairsK_polyT hk
  have h2 : PolyT fun p : α × ℕ × ℕ => thresholds (k p.1) (r p.1) (min (p.2.1 - p.2.2) (k p.1)) :=
    thresholds_polyT (by fun_prop) (by fun_prop) ((hk.comp (h := fun p : α × ℕ × ℕ => p.1) (by fun_prop)).of_le (by fun_prop) fun p => Nat.min_le_right _ _)
  have h : PolyT fun x => (pairsK (k x)).map fun jh => (jh, thresholds (k x) (r x) (min (jh.1 - jh.2) (k x))) := by fun_prop
  refine h.congr fun x => List.map_congr_left fun jh hjh => ?_
  rw [Nat.min_eq_left (by have := le_of_mem_pairsK hjh; omega)]

/-- The two children of a node of the tree of the sparsification with the thresholds for k and ε are
polynomial-time jointly in k, r and the node, if k and 2^k are given in unary. -/
theorem stepC_polyT {k : α → ℕ} {r : α → ℕ × ℕ} {x : α → CNode} (hk : Unary k) (h2 : Unary fun a => 2 ^ k a) (hr : PolyT r) (hx : PolyT x) :
    PolyT fun a => stepC (thresholds (k a) (r a)) (k a) (x a) := by
  have hp : PolyT fun a => pickK (thresholds (k a) (r a)) (k a) (x a).1 := by
    simp only [pickK_eq_pickL]
    exact polyT_pickL (masks_polyT hk h2) (thrList_polyT hk hr) (by fun_prop)
  exact PolyT.optionMap (f := fun (a : α) (HP : PCl × PFml) => ((addP [HP.1] (x a).1, (x a).2), (addP HP.2 (x a).1, negU HP.1 ++ (x a).2)))
    (by fun_prop) hp

/-! ### The walk -/

/-- «Run Steps 2 to 4 on each of the … outputs and add the results»: the walk that adds up is
polynomial-time jointly in k, r, the padding string, the root and whatever the value function
depends on, if k and 2^k are given in unary. -/
theorem walkSG_polyT {k : α → ℕ} {r : α → ℕ × ℕ} {pad : α → U} {val : α → CNode → ℕ} {root : α → CNode} (hk : Unary k) (h2 : Unary fun a => 2 ^ k a) (hr : PolyT r)
    (hp : PolyT pad) (hv : PolyT fun q : α × CNode => val q.1 q.2) (hroot : PolyT root) :
    PolyT fun x => _root_.StepSparsify.walkSG (thresholds (k x) (r x)) (k x) (pad x) (val x) (root x) := by
  have u1 : Unary fun q : (α × (List CNode × ℕ) × Unit) × CNode => k q.1.1 :=
    hk.comp (h := fun q : (α × (List CNode × ℕ) × Unit) × CNode => q.1.1) (by fun_prop)
  have u2 : Unary fun q : (α × (List CNode × ℕ) × Unit) × CNode => 2 ^ k q.1.1 :=
    h2.comp (h := fun q : (α × (List CNode × ℕ) × Unit) × CNode => q.1.1) (by fun_prop)
  have u3 : PolyT fun q : (α × (List CNode × ℕ) × Unit) × CNode => r q.1.1 := by fun_prop
  have hs : PolyT fun q : (α × (List CNode × ℕ) × Unit) × CNode => stepC (thresholds (k q.1.1) (r q.1.1)) (k q.1.1) q.2 :=
    stepC_polyT u1 u2 u3 (by fun_prop)
  have h := foldl_cap (pad := pad) (l := pad) (a := fun x => ([root x], 0))
    (g := fun x st _ => roundS (stepC (thresholds (k x) (r x)) (k x)) (val x) st) ([], 0) hp hp (by fun_prop)
    (polyT_roundS (step := fun p : α × (List CNode × ℕ) × Unit => stepC (thresholds (k p.1) (r p.1)) (k p.1)) (val := fun p => val p.1) (st := fun p => p.2.1)
      hs (by fun_prop) (by fun_prop))
  unfold _root_.StepSparsify.walkSG
  exact PolyT.snd h

end RecursionToBound
