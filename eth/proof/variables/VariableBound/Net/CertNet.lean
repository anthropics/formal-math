/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
public import PaddedDescent.F.CertMark
public import ClauseBound.ParityChecks.CertLib

/-! # Step 3, «The parameters»: condition (iii) for the network with two kinds of marks

«Counting marks, multiplying powers of 2 and finding the position of a string among those with as
many ones take τ = n^O(1) operations, as condition (iii) requires.» Proved here: one polynomial-time
certificate (`PolyT`, or `Unary` for a number given in unary) for each function of
proof/variables/VariableBound/Net/Defs.lean out of which the network of one profile is made, for
arguments that depend on a context x, with the
number g of nodes in unary and the formula, the list of checks and the profile as data. An argument
of which a docstring says nothing is assumed to be polynomial-time in x. The ends are `stCertNet`
(the lengths of the network `netD` are given in unary and its two functions are
polynomial-time, given `StCertRank` (⌈log C(t, μ)⌉ in unary, positions of strings in polynomial
time)) and `stCertAdm` (the test for admissible profiles is polynomial-time).

The file is the counterpart of proof/rates/PaddedDescent/F/CertMark.lean. The test `okD` is cut into
its four conjuncts, and the weight `WD` into this test, the product of the σ and the exponent of the
sign; each is certified by itself. -/

@[expose] public section

namespace VariableBound.Net.CertNet

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)

variable {α : Type} [Enc α]

/-! ### Objects, touches, owners, tests, marks -/

/-- The list of the objects is polynomial-time in the formula and the list of checks. -/
@[fun_prop] theorem objs_polyT {D : α → Dat} (hD : PolyT D) : PolyT fun x => objs (D x) := by
  unfold objs; fun_prop

/-- The object at a position is polynomial-time. -/
@[fun_prop] theorem obAt_polyT {D : α → Dat} {o : α → ℕ} (hD : PolyT D) (ho : PolyT o) : PolyT fun x => obAt (D x) (o x) := by
  unfold obAt; fun_prop

/-- The clause of an object is polynomial-time. -/
@[fun_prop] theorem clOf_polyT {D : α → Dat} {o : α → ℕ} (hD : PolyT D) (ho : PolyT o) : PolyT fun x => clOf (D x) (o x) := by
  unfold clOf; fun_prop

/-- The home of a check is polynomial-time. -/
@[fun_prop] theorem home_polyT {g j : α → ℕ} (hg : PolyT g) (hj : PolyT j) : PolyT fun x => home (g x) (j x) := by
  unfold home; exact PolyT.mod hj hg

/-- The test «the object o touches the node a» is polynomial-time. -/
@[fun_prop] theorem tchB_polyT {g n a o : α → ℕ} {D : α → Dat} (hg : PolyT g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (ho : PolyT o) :
    PolyT fun x => tchB (g x) (n x) (D x) (a x) (o x) := by
  unfold tchB; fun_prop

/-- The list of the objects that touch a node is polynomial-time. -/
@[fun_prop] theorem tch_polyT {g n a : α → ℕ} {D : α → Dat} (hg : PolyT g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) :
    PolyT fun x => tch (g x) (n x) (D x) (a x) := by
  unfold tch; fun_prop

/-- The test «{a, b} is a test of the object o» is polynomial-time; g is in unary because the test
runs through all nodes. -/
@[fun_prop] theorem linkB_polyT {g n o a b : α → ℕ} {D : α → Dat} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (ho : PolyT o) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => linkB (g x) (n x) (D x) (o x) (a x) (b x) := by
  have := hg.poly
  unfold linkB; fun_prop

/-- The test «a is the owner of the object o» is polynomial-time, for g in unary. -/
@[fun_prop] theorem ownB_polyT {g n o a : α → ℕ} {D : α → Dat} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (ho : PolyT o) (ha : PolyT a) :
    PolyT fun x => ownB (g x) (n x) (D x) (o x) (a x) := by
  have := hg.poly
  unfold ownB; fun_prop

/-- The list of the objects of a kind with a given test is polynomial-time, for g in unary. -/
@[fun_prop] theorem tst_polyT {g n a b κ : α → ℕ} {D : α → Dat} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (hb : PolyT b) (hκ : PolyT κ) :
    PolyT fun x => tst (g x) (n x) (D x) (a x) (b x) (κ x) := by
  unfold tst; fun_prop

/-- The mark that a setting gives to an object is polynomial-time. -/
@[fun_prop] theorem mark_polyT {g n a o : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : PolyT g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (hz : PolyT z)
    (ho : PolyT o) : PolyT fun x => mark (g x) (n x) (D x) (a x) (z x) (o x) := by
  unfold mark
  exact PolyT.getD hz (PolyT.add (by fun_prop) (PolyT.idxOf ho (by fun_prop))) (PolyT.const false)

/-- The string of the marks of the objects of a kind with a given test is polynomial-time, for g in
unary. -/
@[fun_prop] theorem str_polyT {g n a b κ : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (hb : PolyT b)
    (hκ : PolyT κ) (hz : PolyT z) : PolyT fun x => str (g x) (n x) (D x) (a x) (b x) (κ x) (z x) := by
  have := hg.poly
  unfold str; fun_prop

/-- A number prescribed by the profile, one digit of y, is polynomial-time. -/
@[fun_prop] theorem mu_polyT {g y a b κ : α → ℕ} {D : α → Dat} (hg : PolyT g) (hD : PolyT D) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b) (hκ : PolyT κ) :
    PolyT fun x => mu (g x) (D x) (y x) (a x) (b x) (κ x) := by
  unfold mu; fun_prop

/-! ### Labels -/

/-- The number c_(a,b) of bits of a label is given in unary, for g in unary, given the certificate
that ⌈log C(t, μ)⌉ is given in unary (`StCertRank`). -/
theorem capD_unary (h : StCertRank) {g n y a b : α → ℕ} {D : α → Dat} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b) :
    Unary fun x => capD (g x) (n x) (D x) (y x) (a x) (b x) := by
  have := hg.poly
  unfold capD
  exact unary_sum_map (f := fun x κ => cw (tst (g x) (n x) (D x) (a x) (b x) κ).length (mu (g x) (D x) (y x) (a x) (b x) κ))
    (h.cw _ _ _ (by fun_prop) (by fun_prop)) (by fun_prop)

/-- The label that a setting shows to another node is polynomial-time, for g in unary, given
`StCertRank` (⌈log C(t, μ)⌉ in unary, positions of strings in polynomial time). -/
theorem labD_polyT (h : StCertRank) {g n y a b : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (hy : PolyT y) (ha : PolyT a)
    (hb : PolyT b) (hz : PolyT z) : PolyT fun x => labD (g x) (n x) (D x) (y x) (a x) (b x) (z x) := by
  have := hg.poly
  have h1 : Unary fun p : α × ℕ => cw (tst (g p.1) (n p.1) (D p.1) (a p.1) (b p.1) p.2).length (mu (g p.1) (D p.1) (y p.1) (a p.1) (b p.1) p.2) :=
    h.cw _ _ _ (by fun_prop) (by fun_prop)
  have h2 : PolyT fun p : α × ℕ => rank (str (g p.1) (n p.1) (D p.1) (a p.1) (b p.1) p.2 (z p.1)) := PolyT.comp h.rank (by fun_prop)
  unfold labD
  fun_prop

/-! ### The weight of a setting -/

/-- A choice between two integers by the test «i = 0» is polynomial-time. -/
theorem ite_zero_polyT {i : α → ℕ} {u v : α → ℤ} (hi : PolyT i) (hu : PolyT u) (hv : PolyT v) : PolyT fun x => if i x = 0 then u x else v x := by
  fun_prop

/-- σ_i is polynomial-time for i given in unary. -/
theorem sig_polyT {i : α → ℕ} (hi : Unary i) : PolyT fun x => ParityChecks.sig (i x) := by
  have h1 : PolyT fun x => (2 : ℤ) ^ (i x - 1) := powZ_polyT (PolyT.const 2) (unary_sub hi (PolyT.const 1))
  have h2 : PolyT fun x => (-1 : ℤ) ^ i x := Mark.Cert.sign_polyT hi.poly
  exact ite_zero_polyT hi.poly (PolyT.const 1) (PolyT.mulZ h2 h1)

/-- The number q_j of marked incidences of a check at a node is given in unary. -/
@[fun_prop] theorem qj_unary {g n a j : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : PolyT g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (hz : PolyT z) (hj : PolyT j) :
    Unary fun x => qj (g x) (n x) (D x) (a x) (z x) (j x) := by
  unfold qj; fun_prop

/-- The first conjunct of `okD`: the value bits of variables with numbers ≥ n are 0. -/
def ok1 (g n a : ℕ) (z : List Bool) : Bool := (List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)

/-- One literal in the second conjunct of `okD`: it is not at a, or it is false. -/
def ok2l (q a : ℕ) (z : List Bool) (l : ℕ × Bool) : Bool := !(l.1 / q == a) || (z.getD (l.1 % q) false != l.2)

/-- The second conjunct of `okD`: no marked object has a true literal at a. -/
def ok2 (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) : Bool :=
  (tch g n D a).all fun o => !(mark g n D a z o) || (clOf D o).all (ok2l (qv g n) a z)

/-- The third conjunct of `okD`: of each kind, the number of marked objects owned by a is that of
the profile. -/
def ok3 (g n : ℕ) (D : Dat) (y a : ℕ) (z : List Bool) : Bool :=
  (List.range 2).all fun κ => ((tch g n D a).filter fun o => (obAt D o).1 == κ && ownB g n D o a && mark g n D a z o).length == mu g D y a a κ

/-- The fourth conjunct of `okD`: for each other node b and each kind, the number of marked objects
with the test {a, b} is that of the profile. -/
def ok4 (g n : ℕ) (D : Dat) (y a : ℕ) (z : List Bool) : Bool :=
  (List.range g).all fun b => b == a || (List.range 2).all fun κ => (str g n D a b κ z).count true == mu g D y a b κ

/-- The product of the σ_(q_j) over the checks j with home a. -/
def sigP (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) : ℤ :=
  (((List.range D.2.length).filter fun j => home g j == a).map fun j => ParityChecks.sig (qj g n D a z j)).prod

/-- The number of marked clauses owned by a: the exponent of the sign in `WD`. -/
def sgE (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) : ℕ :=
  ((tch g n D a).filter fun o => (obAt D o).1 == 0 && ownB g n D o a && mark g n D a z o).length

/-- `WD` written with the four tests, the product and the exponent named above. -/
theorem WD_eq (g n : ℕ) (D : Dat) (y : ℕ) (fl : Bool) (a : ℕ) (z : List Bool) : WD g n D y fl a z =
    if ok1 g n a z && ok2 g n D a z && ok3 g n D y a z && ok4 g n D y a z then sigP g n D a z * (bif fl then (-1) ^ sgE g n D a z else 1) else 0 := rfl

/-- The first conjunct of `okD` is polynomial-time, for g and n in unary. -/
@[fun_prop] theorem ok1_polyT {g n a : α → ℕ} {z : α → List Bool} (hg : Unary g) (hn : Unary n) (ha : PolyT a) (hz : PolyT z) :
    PolyT fun x => ok1 (g x) (n x) (a x) (z x) := by
  have := hg.poly
  have := hn.poly
  unfold ok1; fun_prop

/-- The test of one literal is polynomial-time. -/
@[fun_prop] theorem ok2l_polyT {q a : α → ℕ} {z : α → List Bool} {l : α → ℕ × Bool} (hq : PolyT q) (ha : PolyT a) (hz : PolyT z) (hl : PolyT l) :
    PolyT fun x => ok2l (q x) (a x) (z x) (l x) := by
  have h1 : PolyT fun x => (l x).1 / q x := PolyT.div hl.fst hq
  have h2 : PolyT fun x => (l x).1 % q x := PolyT.mod hl.fst hq
  unfold ok2l; fun_prop

/-- The second conjunct of `okD` is polynomial-time. -/
@[fun_prop] theorem ok2_polyT {g n a : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : PolyT g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (hz : PolyT z) :
    PolyT fun x => ok2 (g x) (n x) (D x) (a x) (z x) := by
  unfold ok2; fun_prop

/-- The third conjunct of `okD` is polynomial-time, for g in unary. -/
@[fun_prop] theorem ok3_polyT {g n y a : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (hy : PolyT y) (ha : PolyT a)
    (hz : PolyT z) : PolyT fun x => ok3 (g x) (n x) (D x) (y x) (a x) (z x) := by
  have := hg.poly
  unfold ok3; fun_prop

/-- The fourth conjunct of `okD` is polynomial-time, for g in unary. -/
@[fun_prop] theorem ok4_polyT {g n y a : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (hy : PolyT y) (ha : PolyT a)
    (hz : PolyT z) : PolyT fun x => ok4 (g x) (n x) (D x) (y x) (a x) (z x) := by
  have := hg.poly
  unfold ok4; fun_prop

/-- «Multiplying powers of 2»: the product of the σ_(q_j) over the checks with home a is
polynomial-time. -/
@[fun_prop] theorem sigP_polyT {g n a : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : PolyT g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (hz : PolyT z) :
    PolyT fun x => sigP (g x) (n x) (D x) (a x) (z x) := by
  have h1 : PolyT fun p : α × ℕ => ParityChecks.sig (qj (g p.1) (n p.1) (D p.1) (a p.1) (z p.1) p.2) := sig_polyT (by fun_prop)
  unfold sigP; fun_prop

/-- «Counting marks»: the number of marked clauses owned by a is polynomial-time, for g in unary. -/
@[fun_prop] theorem sgE_polyT {g n a : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (hz : PolyT z) :
    PolyT fun x => sgE (g x) (n x) (D x) (a x) (z x) := by
  have := hg.poly
  unfold sgE; fun_prop

/-- The weight W_a(z_a) is polynomial-time, for g and n in unary. -/
@[fun_prop] theorem WD_polyT {g n y a : α → ℕ} {D : α → Dat} {fl : α → Bool} {z : α → List Bool} (hg : Unary g) (hn : Unary n) (hD : PolyT D) (hy : PolyT y)
    (hfl : PolyT fl) (ha : PolyT a) (hz : PolyT z) : PolyT fun x => WD (g x) (n x) (D x) (y x) (fl x) (a x) (z x) := by
  have := hg.poly
  have := hn.poly
  simp only [WD_eq]; fun_prop

/-! ### The network of one profile -/

/-- The lengths of the network of one profile are given in unary and its two functions are
polynomial-time, given `StCertRank` (⌈log C(t, μ)⌉ in unary, positions of strings in polynomial
time). -/
theorem netD_keeps (h : StCertRank) : FKeeps netD where
  n := by
    have h1 : Unary fun p : DCtx × ℕ => qv p.1.1.1.length p.1.1.2.length + (tch p.1.1.1.length p.1.1.2.length p.1.2.1 p.2).length := by fun_prop
    exact h1
  cap := by
    have h1 : Unary fun p : DCtx × ℕ × ℕ => capD p.1.1.1.length p.1.1.2.length p.1.2.1 p.1.2.2.1 p.2.1 p.2.2 :=
      capD_unary h (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    exact h1
  W := by
    have h1 : PolyT fun x : DCtx × WQ => WD x.1.1.1.length x.1.1.2.length x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.1 x.2.2 := by fun_prop
    exact h1
  f := by
    have h0 : PolyT fun x : DCtx × FQ => labD x.1.1.1.length x.1.1.2.length x.1.2.1 x.1.2.2.1 x.2.1.1 x.2.1.2 x.2.2.1 :=
      labD_polyT h (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    have h1 : PolyT fun x : DCtx × FQ =>
        if labD x.1.1.1.length x.1.1.2.length x.1.2.1 x.1.2.2.1 x.2.1.1 x.2.1.2 x.2.2.1 == x.2.2.2 then (1 : ℤ) else 0 := by fun_prop
    exact h1

/-! ### Admissible profiles -/

/-- The sum Σ_a μ_(a,κ) is polynomial-time, for g in unary. -/
@[fun_prop] theorem tot_polyT {g y κ : α → ℕ} {D : α → Dat} (hg : Unary g) (hD : PolyT D) (hy : PolyT y) (hκ : PolyT κ) : PolyT fun x => tot (g x) (D x) (y x) (κ x) := by
  have := hg.poly
  unfold tot; fun_prop

/-- The sum Σ_({a,b}) μ_(a,b,κ) is polynomial-time, for g in unary. -/
@[fun_prop] theorem totP_polyT {g y κ : α → ℕ} {D : α → Dat} (hg : Unary g) (hD : PolyT D) (hy : PolyT y) (hκ : PolyT κ) : PolyT fun x => totP (g x) (D x) (y x) (κ x) := by
  have := hg.poly
  unfold totP; simp only [Mark.Cert.sum_range_eq]; fun_prop

/-- The test «the profile y is admissible» is polynomial-time when g is given in unary and the other
arguments, the width k among them, are polynomial-time. -/
theorem admD_polyT {k g n nb M y : α → ℕ} {D : α → Dat} {fl : α → Bool} (hk : PolyT k) (hg : Unary g) (hn : PolyT n) (hnb : PolyT nb) (hM : PolyT M) (hD : PolyT D)
    (hfl : PolyT fl) (hy : PolyT y) : PolyT fun x => admD (k x) (g x) (n x) (nb x) (M x) (D x) (fl x) (y x) := by
  have := hg.poly
  unfold admD; fun_prop

end VariableBound.Net.CertNet

namespace VariableBound.Net

/-- Step 3, «The parameters»: «counting marks, multiplying powers of 2 and finding the position of a
string among those with as many ones take τ = n^O(1) operations, as condition (iii) requires». The
lengths of
the settings and of the labels of the network of one profile are given in unary, and W and f are
polynomial-time in the context (g and n in unary, the formula, the list of checks, the profile, and
the flag
that is true for the network of F, with the sign (-1)^q of the marked clauses owned by a, and false
for that of X) and their arguments. Needs the certificates of the binomial coefficients and of the
positions of strings. -/
theorem stCertNet (h : StCertRank) : StCertNet := CertNet.netD_keeps h

/-- Step 3, «Profiles»: the test «admissible» is polynomial-time jointly in all its arguments, for g
given in unary and k, n, n̄, M, the formula with the list of checks, the flag (F or X) and the
profile polynomial-time. -/
theorem stCertAdm : StCertAdm := fun _ _ _ _ _ _ _ _ _ _ hk hg hn hnb hM hD hfl hy => CertNet.admD_polyT hk hg hn hnb hM hD hfl hy

end VariableBound.Net
