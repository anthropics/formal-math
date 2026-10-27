/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Top
public import ClauseBound.Alg.CertCount
public import PaddedDescent.BrutePad
public import CountKSat.Poly
public import ToTuring.Poly.Sat

/-! # The top level in m is polynomial-time

Polynomial-time certificates (`PolyT`) for the function `AM` of (input, pad) and for the exponent
function `eM` of the input (`stCertM`), and for the network `satFk` of a k-CNF in which
both the number g of groups and the width k are part of the data, in unary (`stCertSatK`). The
certificates of proof/machines/ToTuring/Poly/Count.lean have g and k as constants;
proof/rates/ClauseBound/Alg/CertCount.lean has those that do not depend on k, with g as data; this
file gives the others, with g as data and k a
function of the input. -/

public section

namespace ClauseBound.Alg.CertTop

open Groundwork Groundwork.Prog Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg.CertCount CountKSat CountKSat.Poly

variable {α : Type} [Enc α]

/-! ### The network of a k-CNF, with g and k as data -/

/-- The literal at a slot, jointly in k, the formula and the slot. -/
@[fun_prop] theorem litAt_polyT3 {k : α → ℕ} {φ : α → Fml} {i : α → ℕ} (hk : PolyT k) (hφ : PolyT φ) (hi : PolyT i) :
    PolyT fun x => litAt (k x) (φ x) (i x) := by
  unfold litAt; fun_prop

/-- The variable at a slot, jointly in k, the formula and the slot. -/
@[fun_prop] theorem varAt_polyT3 {k : α → ℕ} {φ : α → Fml} {i : α → ℕ} (hk : PolyT k) (hφ : PolyT φ) (hi : PolyT i) :
    PolyT fun x => varAt (k x) (φ x) (i x) := by
  unfold varAt; fun_prop

/-- The list of the slots of a formula, jointly in k, in unary, and the formula. -/
@[fun_prop] theorem slotsOf_polyT3 {k : α → ℕ} {φ : α → Fml} (hk : Unary k) (hφ : PolyT φ) : PolyT fun x => slotsOf (k x) (φ x) := by
  unfold slotsOf; fun_prop

/-- The test «slot i' is the next occurrence of the variable at slot i», jointly in k, in unary, the
formula and the two slots. -/
@[fun_prop] theorem linkB_polyT3 {k : α → ℕ} {φ : α → Fml} {i i' : α → ℕ} (hk : Unary k) (hφ : PolyT φ) (hi : PolyT i) (hi' : PolyT i') :
    PolyT fun x => linkB (k x) (φ x) (i x) (i' x) := by
  have hk' : PolyT k := hk.poly
  unfold linkB; fun_prop

/-- The list of the slots of a group, jointly in g, k in unary and the formula. -/
@[fun_prop] theorem locals_polyT3 {g k : α → ℕ} {φ : α → Fml} (hg : PolyT g) (hk : Unary k) (hφ : PolyT φ) :
    PolyT fun x => locals (g x) (k x) (φ x) := by
  have hk' : PolyT k := hk.poly
  unfold locals; fun_prop

/-- The list of the links between two groups, jointly in g, k in unary, the formula and the two
groups. -/
@[fun_prop] theorem links_polyT3 {g k : α → ℕ} {φ : α → Fml} {a b : α → ℕ} (hg : PolyT g) (hk : Unary k) (hφ : PolyT φ) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun x => links (g x) (k x) (φ x) (a x) (b x) := by
  have hk' : PolyT k := hk.poly
  have h : PolyT fun x => ((locals (g x) (k x) (φ x)).product (locals (g x) (k x) (φ x))).filter fun p =>
      linkB (k x) (φ x) (a x * (mu (g x) (φ x) * k x) + p.1) (b x * (mu (g x) (φ x) * k x) + p.2) := by fun_prop
  exact h

/-- The weight of a group of clauses at a state word, jointly in g, k in unary, the formula and the
query. -/
@[fun_prop] theorem wF_polyT3 {g k : α → ℕ} {q : α → Fml × WQ} (hg : PolyT g) (hk : Unary k) (hq : PolyT q) :
    PolyT fun x => wF (g x) (k x) (q x) := by
  have hk' : PolyT k := hk.poly
  unfold wF; fun_prop

/-- The factor of two groups of clauses at a state word and a label word, jointly in g, k in unary,
the formula and the query. -/
@[fun_prop] theorem fF_polyT3 {g k : α → ℕ} {q : α → Fml × FQ} (hg : PolyT g) (hk : Unary k) (hq : PolyT q) :
    PolyT fun x => fF (g x) (k x) (q x) := by
  unfold fF; fun_prop

/-- The number of label bits of two groups is given in unary, jointly in g, k in unary, the formula
and the two groups. -/
@[fun_prop] theorem capF_unary3 {g k : α → ℕ} {φ : α → Fml} {a b : α → ℕ} (hg : PolyT g) (hk : Unary k) (hφ : PolyT φ) (ha : PolyT a)
    (hb : PolyT b) : Unary fun x => capF (g x) (k x) (φ x) (a x) (b x) :=
  Unary.of_length (w := fun x => links (g x) (k x) (φ x) (min (a x) (b x)) (max (a x) (b x))) (by fun_prop)

/-- The four functions of the network of a k-CNF are polynomial-time, with the number of groups and
the width, both in unary, as data. -/
theorem stCertSatK : StCertSatK where
  n := by
    have h : Unary fun p : ((U × U) × Fml) × ℕ => mu p.1.1.1.length p.1.2 * p.1.1.2.length := by fun_prop
    exact h
  cap := by
    have h : Unary fun p : ((U × U) × Fml) × ℕ × ℕ => capF p.1.1.1.length p.1.1.2.length p.1.2 p.2.1 p.2.2 := by fun_prop
    exact h
  W := by
    have h : PolyT fun x : ((U × U) × Fml) × WQ => wF x.1.1.1.length x.1.1.2.length (x.1.2, x.2) := by fun_prop
    exact h
  f := by
    have h : PolyT fun x : ((U × U) × Fml) × FQ => fF x.1.1.1.length x.1.1.2.length (x.1.2, x.2) := by fun_prop
    exact h

/-! ### Numbers in unary -/

/-- The larger of two numbers given in unary is given in unary. -/
@[fun_prop] theorem unary_max {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun x => max (f x) (g x) :=
  (hf.add hg).of_le (PolyT.max' hf.poly hg.poly) fun x => by omega

/-- The number of binary digits of a number given in unary is given in unary. -/
@[fun_prop] theorem unary_size {f : α → ℕ} (hf : Unary f) : Unary fun x => Nat.size (f x) :=
  hf.of_le (PolyT.size' hf.poly) fun _ => Nat.size_le.2 Nat.lt_two_pow_self

/-- ⌊m^{1/9}⌋ is polynomial-time in m, when m is given in unary. -/
@[fun_prop] theorem root9_polyT {m : α → ℕ} (hm : Unary m) : PolyT fun x => root9 (m x) := by
  have hm' : PolyT m := hm.poly
  unfold root9; fun_prop

/-- The bound P of the network of a k-CNF is given in unary if g, k and m are. -/
@[fun_prop] theorem PtopK_unary {g k m : α → ℕ} (hg : Unary g) (hk : Unary k) (hm : Unary m) : Unary fun x => PtopK (g x) (k x) (m x) := by
  have hg' : PolyT g := hg.poly
  unfold PtopK; fun_prop

/-- The label length of the top instance is given in unary if K, g, k and m are. -/
@[fun_prop] theorem lamTopK_unary {K g k m : α → ℕ} (hK : Unary K) (hg : Unary g) (hk : Unary k) (hm : Unary m) :
    Unary fun x => lamTopK (K x) (g x) (k x) (m x) := by
  have hK' : PolyT K := hK.poly
  unfold lamTopK; fun_prop

/-- The bound on the size of the entries of the top instance is given in unary if K and P are. -/
theorem entry_unary {K P : α → ℕ} (hK : Unary K) (hP : Unary P) : Unary fun x => P x * (2 * (3 * K x ^ 8) / K x) := by
  have hK' : PolyT K := hK.poly
  fun_prop

/-- The largest of the four exponents of the top level is polynomial-time in the numbers K, P, λ and
the exponent v of the solver. -/
theorem maxFour_polyT {K P L v : α → ℕ} (hK : PolyT K) (hP : PolyT P) (hL : PolyT L) (hv : PolyT v) :
    PolyT fun x => max (max (3 * K x ^ 8 * Nat.size (K x)) (P x * (2 * (3 * K x ^ 8) / K x + 1))) (max ((K x - 1) * L x) (v x)) := by
  have hG : PolyT fun x => 3 * K x ^ 8 := PolyT.mul (PolyT.const 3) (PolyT.pow_const hK 8)
  exact PolyT.max' (PolyT.max' (PolyT.mul hG (PolyT.size' hK)) (PolyT.mul hP (PolyT.add (PolyT.div (PolyT.mul (PolyT.const 2) hG) hK) (PolyT.const 1))))
    (PolyT.max' (PolyT.mul (PolyT.sub hK (PolyT.const 1)) hL) hv)

/-! ### The function and its exponent -/

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The value of the network of a formula is polynomial-time jointly in the pad, the index, k in
unary and the formula. -/
theorem countG_polyT (hS : StCertSatK) (hR : StCertRebalG) (hP : S.Poly) {pad : α → U} {i : α → Idx} {ku : α → U} {ψ : α → Fml}
    (hp : PolyT pad) (hi : PolyT i) (hk : PolyT ku) (hψ : PolyT ψ) : PolyT fun x => countG S (pad x) (i x) (ku x) (ψ x) := by
  have hK : Unary fun x => S.K (i x) := hP.K.comp hi
  have hg : Unary fun x => 3 * S.K (i x) ^ 8 := by fun_prop
  have hl : Unary fun x => lamTopK (S.K (i x)) (3 * S.K (i x) ^ 8) (ku x).length (ψ x).length :=
    lamTopK_unary hK hg (by fun_prop) (by fun_prop)
  have h1 := hR _ satFk hS α pad _ _ _ (fun x => ((List.replicate (3 * S.K (i x) ^ 8) (), ku x), ψ x)) hp hK hg hl (by fun_prop)
  have h2 : PolyT fun q : α × PInst => S.run (pad q.1, i q.1, q.2) := PolyT.comp hP.run (by fun_prop)
  unfold countG
  exact PolyT.optionElim h1 (PolyT.const 0) h2

/-- The exponent of a pad that suffices at an index, computed under a bound, is polynomial-time
jointly in the bound, the index, k and m in unary. -/
theorem needTopC_polyT (hP : S.Poly) {b : α → U} {i : α → Idx} {k m : α → ℕ} (hb : PolyT b) (hi : PolyT i) (hk : Unary k) (hm : Unary m) :
    PolyT fun x => needTopC S (b x) (i x) (k x) (m x) := by
  have hK : Unary fun x => S.K (i x) := hP.K.comp hi
  have hK' : PolyT fun x => S.K (i x) := hK.poly
  have hg : Unary fun x => 3 * S.K (i x) ^ 8 := by fun_prop
  have hl : Unary fun x => lamTopK (S.K (i x)) (3 * S.K (i x) ^ 8) (k x) (m x) := lamTopK_unary hK hg hk hm
  have hl' := hl.poly
  have hq : Unary fun x => PtopK (3 * S.K (i x) ^ 8) (k x) (m x) := PtopK_unary hg hk hm
  have hq' := hq.poly
  have hn : PolyT fun x => S.needC (b x, i x, List.replicate (lamTopK (S.K (i x)) (3 * S.K (i x) ^ 8) (k x) (m x)) (),
      List.replicate (PtopK (3 * S.K (i x) ^ 8) (k x) (m x) * (2 * (3 * S.K (i x) ^ 8) / S.K (i x))) ()) :=
    PolyT.comp hP.needC (PolyT.prodMk hb (PolyT.prodMk hi (PolyT.prodMk hl (entry_unary hK hq))))
  have hv : PolyT fun q : α × ℕ =>
      max (max (3 * S.K (i q.1) ^ 8 * Nat.size (S.K (i q.1)))
          (PtopK (3 * S.K (i q.1) ^ 8) (k q.1) (m q.1) * (2 * (3 * S.K (i q.1) ^ 8) / S.K (i q.1) + 1)))
        (max ((S.K (i q.1) - 1) * lamTopK (S.K (i q.1)) (3 * S.K (i q.1) ^ 8) (k q.1) (m q.1)) q.2) := by
    have h1 : PolyT fun q : α × ℕ => S.K (i q.1) := PolyT.comp (f := fun x => S.K (i x)) hK' PolyT.id'.fst
    have h2 : PolyT fun q : α × ℕ => lamTopK (S.K (i q.1)) (3 * S.K (i q.1) ^ 8) (k q.1) (m q.1) := PolyT.comp (f := fun x => lamTopK (S.K (i x)) (3 * S.K (i x) ^ 8) (k x) (m x)) hl' PolyT.id'.fst
    have h3 : PolyT fun q : α × ℕ => PtopK (3 * S.K (i q.1) ^ 8) (k q.1) (m q.1) := PolyT.comp (f := fun x => PtopK (3 * S.K (i x) ^ 8) (k x) (m x)) hq' PolyT.id'.fst
    exact maxFour_polyT h1 h3 h2 PolyT.id'.snd
  have hb' : PolyT fun q : α × ℕ => (b q.1).length := by fun_prop
  unfold needTopC
  exact PolyT.optionBind (PolyT.ite' (PolyT.decide_le hv hb') (PolyT.some' hv) (PolyT.const none)) hn

/-- The choice between the clique algorithm and exhaustive counting is polynomial-time in the input. -/
theorem planM_polyT (hD : StCertDecM) (hP : S.Poly) {pick : U → U × Idx} (hpick : PolyT pick) : PolyT (planM S pick) := by
  obtain ⟨hk, hf⟩ := hD
  have hi : PolyT fun x : List Bool => (pick (root9 (fmlOf x).2.length)).2 :=
    (PolyT.comp hpick (root9_polyT (Unary.of_length hf.snd))).snd
  unfold planM
  exact needTopC_polyT S hP hf.fst hi (Unary.of_length hk) (Unary.of_length hf.snd)

end

/-- The function of (input, pad) and the exponent function of the input are polynomial-time. -/
theorem stCertM (hD : StCertDecM) (hS : StCertSatK) (hR : StCertRebalG) : StCertM := by
  intro Idx _ S hP pick hpick
  have hpl := planM_polyT S hD hP hpick
  obtain ⟨hk, hf⟩ := hD
  constructor
  · have hd : PolyT fun p : List Bool × U => fmlOf p.1 := PolyT.comp hf PolyT.id'.fst
    have hku : PolyT fun p : List Bool × U => kOf p.1 := PolyT.comp hk PolyT.id'.fst
    have hi : PolyT fun p : List Bool × U => (pick (root9 (fmlOf p.1).2.length)).2 :=
      (PolyT.comp hpick (root9_polyT (Unary.of_length hd.snd))).snd
    have hsat : PolyT fun q : (List Bool × U) × ℕ => satAt (fmlOf q.1.1).2 q.2 := 
      satAt_polyT (PolyT.comp (f := fun p : List Bool × U => (fmlOf p.1).2) hd.snd PolyT.id'.fst) PolyT.id'.snd
    have hb : PolyT fun p : List Bool × U => ((rng p.2 (2 ^ (fmlOf p.1).1.length)).filter fun y => satAt (fmlOf p.1).2 y).length :=
      (PolyT.filter hsat (rng_polyT PolyT.id'.snd (pow_polyT (PolyT.const 2) (Unary.of_length hd.fst)))).length
    have hc : PolyT fun p : List Bool × U => (countG S p.2 (pick (root9 (fmlOf p.1).2.length)).2 (kOf p.1) (fmlOf p.1).2).toNat :=
      PolyT.toNat (countG_polyT S hS hR hP PolyT.id'.snd hi hku hd.snd)
    have hnil : PolyT fun p : List Bool × U => hasNil (fmlOf p.1).2 := PolyT.comp hasNil_polyT hd.snd
    have hno : PolyT fun p : List Bool × U => (planM S pick p.1).isNone := PolyT.optionIsNone (PolyT.comp hpl PolyT.id'.fst)
    unfold AM
    exact PolyT.comp outW_polyT (PolyT.prodMk hd (PolyT.cond' hno hb (PolyT.cond' hnil (PolyT.const 0) hc)))
  · unfold eM
    exact PolyT.optionGetD hpl hf.fst.length

end ClauseBound.Alg.CertTop
