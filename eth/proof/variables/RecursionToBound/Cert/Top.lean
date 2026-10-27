/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Cert.Exponent
import VariableBound.MainPrinted
import StepSparsify.CertWalk
import CountKSatRate.Cert
import CountKSat.Poly
import ClauseBound.Alg.Decode
import ToTuring.Poly.Sat
import ToTuring.Poly.NetFun

/-! # The function of Theorem D (a), with the sparsification of Step 5 of Appendix D, is polynomial-time

`countIsPolynomialTime : CountIsPolynomialTime`: for every polynomial-time solver S, every n₁ and
all polynomial-time `pick` and `num`, the function `count S n₁ pick num` of (input, padding string)
and its exponent `expo S n₁ pick num` (proof/variables/RecursionToBound/Defs.lean) are
polynomial-time, **on all inputs**, whether or not they are codes of formulas in the range of
Theorem D (a).

* `DeltaOf_unary`: «Δ the larger of 2 and the largest number of its clauses in which one variable
  occurs» (Step 5 of Appendix D) is the maximum of a list (`DeltaOf_eq`) and at most the number of
  clauses plus 2, so it is given in unary.
* `countOutput_polyT`: the count of one output. The output at a node is a list without repetitions
  made from the node; Steps 2 to 4 are polynomial-time jointly in k, n and Δ in unary, the padding
  string, the index and the formula (`VariableBound.StCertCountD`, proved as
  `VariableBound.certCountDc`).
* `countAll_polyT`: the walk that adds these counts (`walkSG_polyT`).
* `count_polyT`: without a plan, exhaustive counting (`CountKSatRate.Cert.bruteN_polyT_aux`); the
  result is written in n + 1 bits.

Here the pair r (the argument `r : ℕ × ℕ` of `countAll`, computed by `numU`) is given in binary,
each output has its own Δ, and the width is read from the formula. -/

public section

namespace RecursionToBound

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma

variable {α : Type} [Enc α]

/-! ### The Δ of an output -/

/-- The number of clauses in which a variable occurs is polynomial-time. -/
theorem occN_polyT {Φ : α → PFml} {v : α → ℕ} (hΦ : PolyT Φ) (hv : PolyT v) : PolyT fun x => occN (Φ x) (v x) := by
  unfold occN PaddedDescent.F.Mark.occ
  fun_prop

/-- The maximum of a list of values that are all at most b is at most b. -/
theorem foldr_max_map_le {β : Type} (f : β → ℕ) (l : List β) {b : ℕ} (h : ∀ a, f a ≤ b) : (l.map f).foldr max 0 ≤ b := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    rw [List.map_cons, List.foldr_cons]
    exact max_le (h a) ih

/-- The Δ of a formula is at most its number of clauses plus 2. -/
theorem DeltaOf_le (n : ℕ) (Φ : PFml) : SparsificationLemma.StepSparsify.DeltaOf n Φ ≤ Φ.length + 2 := by
  have h := foldr_max_map_le (occN Φ) (List.range n) (b := Φ.length) fun v => List.length_filter_le _ _
  rw [DeltaOf_eq]
  omega

/-- The Δ of a formula is polynomial-time jointly in n and the formula, if n is given in unary. -/
theorem DeltaOf_polyT {n : α → ℕ} {Φ : α → PFml} (hn : Unary n) (hΦ : PolyT Φ) : PolyT fun x => SparsificationLemma.StepSparsify.DeltaOf (n x) (Φ x) := by
  have h1 : PolyT fun p : α × ℕ => occN (Φ p.1) p.2 := occN_polyT (by fun_prop) (by fun_prop)
  have h3 : PolyT fun x => ((List.range (n x)).map fun v => occN (Φ x) v).foldr max 0 :=
    NetE.foldr_max_polyT (PolyT.map (f := fun x v => occN (Φ x) v) h1 (PolyT.range hn))
  exact (PolyT.max' (PolyT.const 2) h3).congr fun x => (DeltaOf_eq (n x) (Φ x)).symm

/-- The Δ of a formula is given in unary. -/
theorem DeltaOf_unary {n : α → ℕ} {Φ : α → PFml} (hn : Unary n) (hΦ : PolyT Φ) : Unary fun x => SparsificationLemma.StepSparsify.DeltaOf (n x) (Φ x) :=
  Unary.of_le (g := fun x => (Φ x).length + 2) ((Unary.of_length hΦ).add (Unary.const 2)) (DeltaOf_polyT hn hΦ) fun x => DeltaOf_le (n x) (Φ x)

/-- The output at a node is polynomial-time. -/
theorem out_polyT {x : α → CNode} (hx : PolyT x) : PolyT fun a => out (x a) := by
  unfold out
  exact PolyT.dedup (PolyT.comp leafM_polyT hx)

/-! ### The count -/

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The count of the output at a node is polynomial-time jointly in k, the padding string, the
index, n and the node, if k and n are given in unary; given the certificate of Steps 2 to 4. -/
theorem countOutput_polyT (hC : StCertCountD) (hP : S.Poly) {k n : α → ℕ} {pad : α → U} {i : α → Idx} {x : α → CNode} (hk : Unary k) (hp : PolyT pad) (hi : PolyT i) (hn : Unary n)
    (hx : PolyT x) : PolyT fun a => countOutput S (k a) (pad a) (i a) (n a) (x a) := by
  have ho := out_polyT hx
  have hD := DeltaOf_unary hn ho
  have hg : PolyT fun a => (List.replicate (k a) (), pad a, i a, (List.replicate (n a) (), List.replicate (SparsificationLemma.StepSparsify.DeltaOf (n a) (out (x a))) ()), out (x a)) :=
    PolyT.prodMk hk (PolyT.prodMk hp (PolyT.prodMk hi (PolyT.prodMk (PolyT.prodMk hn hD) ho)))
  have hc : PolyT fun a => countD S (k a) (pad a) (i a) (n a) (SparsificationLemma.StepSparsify.DeltaOf (n a) (out (x a))) (out (x a)) :=
    (PolyT.comp (hC Idx S hP) hg).congr fun a => by simp only [List.length_replicate]
  unfold countOutput
  exact PolyT.cond' (PolyT.isEmpty ho) (PolyT.two_pow hn) hc

/-- The sum of the counts of all outputs is polynomial-time jointly in k, r, the index, the decoded
formula and the padding string, if k and 2^k are given in unary. -/
theorem countAll_polyT (hC : StCertCountD) (hP : S.Poly) {k : α → ℕ} {r : α → ℕ × ℕ} {i : α → Idx} {d : α → U × Fml} {pad : α → U} (hk : Unary k) (h2 : Unary fun a => 2 ^ k a)
    (hr : PolyT r) (hi : PolyT i) (hd : PolyT d) (hp : PolyT pad) : PolyT fun a => countAll S (k a) (r a) (i a) (d a) (pad a) := by
  have hv : PolyT fun q : α × CNode => countOutput S (k q.1) (pad q.1) (i q.1) (d q.1).1.length q.2 :=
    countOutput_polyT S hC hP (hk.comp (h := fun q : α × CNode => q.1) PolyT.id'.fst) (by fun_prop) (by fun_prop) (Unary.of_length (by fun_prop)) PolyT.id'.snd
  have hroot : PolyT fun a => rootC ((d a).1, noTaut (d a).2) :=
    PolyT.comp rootC_polyT (PolyT.prodMk hd.fst (PolyT.comp _root_.StepSparsify.stCertNoTaut hd.snd))
  unfold countAll
  exact PolyT.cond' (PolyT.comp hasNil_polyT hd.snd) (PolyT.const 0) (walkSG_polyT hk h2 hr hp hv hroot)

/-- The function of (input, padding string) is polynomial-time, given the certificate of Steps 2 to 4. -/
theorem count_polyT (hC : StCertCountD) (hP : S.Poly) (n₁ : ℕ) {pick : U → U × Idx} {num : U × U → ℕ × ℕ} (hpick : PolyT pick) (hnum : PolyT num) : PolyT (count S n₁ pick num) := by
  have hfst : PolyT fun p : List Bool × U => p.1 := PolyT.id'.fst
  have hd : PolyT fun p : List Bool × U => fmlOf p.1 := PolyT.comp Decode.stCertDecM.2 hfst
  have hp : PolyT fun p : List Bool × U => p.2 := PolyT.id'.snd
  have hall : PolyT fun p : List Bool × U => countAll S (kcU (widthU p.1) (nU p.1)) (numU S pick num p.1) (idxU pick p.1) (fmlOf p.1) p.2 :=
    countAll_polyT S hC hP (widthCut_unary.comp hfst) (powWidthCut_unary.comp hfst) (PolyT.comp (numU_polyT S hP hpick hnum) hfst) (PolyT.comp (idxU_polyT hpick) hfst) hd hp
  have hbr : PolyT bruteU := by
    have h := bruteN_polyT_aux hd (pad := fun p : List Bool × U => p.2) hp
    unfold bruteU
    exact h
  have hno : PolyT fun p : List Bool × U => (plan S n₁ pick num p.1).isNone := PolyT.optionIsNone (PolyT.comp (plan_polyT S hP n₁ hpick hnum) hfst)
  unfold count
  exact PolyT.comp outW_polyT (PolyT.prodMk hd (PolyT.cond' hno hbr hall))

end

/-- The function and its exponent are polynomial-time in (input, padding string), on all inputs, for
every n₁, if the solver, `pick` and `num` are. -/
theorem countIsPolynomialTime : CountIsPolynomialTime :=
  fun _ _ S hP n₁ _ _ hpick hnum => ⟨count_polyT S certCountDc hP n₁ hpick hnum, expo_polyT S hP n₁ hpick hnum⟩

end RecursionToBound
