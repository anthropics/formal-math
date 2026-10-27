/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import PaddedDescent.F.FuelCert
public import ToTuring.Poly.Digits

/-! Polynomial-time certificates (`PolyT`) for the network of marks of
proof/rates/PaddedDescent/F/MarkNet.lean, one lemma for each of its functions, with the numbers g,
n, β, b in unary
and the layers and the profile as data. Every certificate is stated for arguments that depend on a
context x. The last two theorems, `certMark` and `certAdm`, prove the interface statements
`StCertMark` and `StCertAdm` of proof/rates/PaddedDescent/F/Interfaces.lean. The proofs use the
closure
lemmas of proof/machines/ToTuring/Lib and proof/machines/ToTuring/Poly/Digits.lean and those of
proof/rates/PaddedDescent/F/FuelCert.lean. The weight `mW` is cut into its four tests and its sign,
which are
certified one by one. -/

@[expose] public section

namespace PaddedDescent.F.Mark.Cert

open Groundwork Groundwork.Prog Groundwork.Grid

variable {α : Type} [Enc α]

/-- The number of variables per node is polynomial-time in g and n. -/
@[fun_prop] theorem qv_polyT {g n : α → ℕ} (hg : PolyT g) (hn : PolyT n) : PolyT fun x => qv (g x) (n x) := by
  unfold qv; exact PolyT.div (by fun_prop) hg

/-- The list of all clauses with the index of their layer. -/
@[fun_prop] theorem cls_polyT {Ls : α → List Fml} (hL : PolyT Ls) : PolyT fun x => cls (Ls x) := by
  unfold cls; fun_prop

/-- Clause number e with the index of its layer. -/
@[fun_prop] theorem clAt_polyT {Ls : α → List Fml} {e : α → ℕ} (hL : PolyT Ls) (he : PolyT e) : PolyT fun x => clAt (Ls x) (e x) := by
  unfold clAt; fun_prop

/-- The test «clause e touches node a». -/
@[fun_prop] theorem tchB_polyT {g n a e : α → ℕ} {Ls : α → List Fml} (hg : PolyT g) (hn : PolyT n) (hL : PolyT Ls) (ha : PolyT a)
    (he : PolyT e) : PolyT fun x => tchB (g x) (n x) (Ls x) (a x) (e x) := by
  unfold tchB; fun_prop

/-- The list of the clauses that touch a node. -/
@[fun_prop] theorem tch_polyT {g n a : α → ℕ} {Ls : α → List Fml} (hg : PolyT g) (hn : PolyT n) (hL : PolyT Ls) (ha : PolyT a) :
    PolyT fun x => tch (g x) (n x) (Ls x) (a x) := by
  unfold tch; fun_prop


/-- The test «a and b are neighbours in the chain of clause e»; g is in unary because the test runs
through all nodes. -/
@[fun_prop] theorem linkB_polyT {g n e a b : α → ℕ} {Ls : α → List Fml} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls) (he : PolyT e)
    (ha : PolyT a) (hb : PolyT b) : PolyT fun x => linkB (g x) (n x) (Ls x) (e x) (a x) (b x) := by
  have := hg.poly
  unfold linkB; fun_prop

/-- The test «a is the least node that clause e touches». -/
@[fun_prop] theorem ownB_polyT {g n e a : α → ℕ} {Ls : α → List Fml} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls) (he : PolyT e)
    (ha : PolyT a) : PolyT fun x => ownB (g x) (n x) (Ls x) (e x) (a x) := by
  have := hg.poly
  unfold ownB; fun_prop

/-- The list of the clauses of a layer whose marks two nodes compare. -/
@[fun_prop] theorem tst_polyT {g n a b i : α → ℕ} {Ls : α → List Fml} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls)
    (ha : PolyT a) (hb : PolyT b) (hi : PolyT i) : PolyT fun x => tst (g x) (n x) (Ls x) (a x) (b x) (i x) := by
  unfold tst; fun_prop

/-- The mark that a state word gives to a clause. -/
@[fun_prop] theorem mark_polyT {g n a e : α → ℕ} {Ls : α → List Fml} {z : α → List Bool} (hg : PolyT g) (hn : PolyT n) (hL : PolyT Ls)
    (ha : PolyT a) (hz : PolyT z) (he : PolyT e) : PolyT fun x => mark (g x) (n x) (Ls x) (a x) (z x) (e x) := by
  unfold mark
  exact PolyT.getD hz (PolyT.add (by fun_prop) (PolyT.idxOf he (by fun_prop))) (PolyT.const false)

/-- The string of the marks that two nodes compare in a layer. -/
@[fun_prop] theorem str_polyT {g n a b i : α → ℕ} {Ls : α → List Fml} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls)
    (ha : PolyT a) (hb : PolyT b) (hi : PolyT i) (hz : PolyT z) : PolyT fun x => str (g x) (n x) (Ls x) (a x) (b x) (i x) (z x) := by
  have := hg.poly
  unfold str; fun_prop

/-- The block code is polynomial-time, with β and the block length b in unary. -/
@[fun_prop] theorem enc_polyT {β b : α → ℕ} {w : α → List Bool} (hβ : Unary β) (hb : Unary b) (hw : PolyT w) :
    PolyT fun x => enc (β x) (b x) (w x) := by
  have := hb.poly
  unfold enc; fun_prop

/-- A number prescribed by the profile: one digit of y. -/
@[fun_prop] theorem mu_polyT {g y a b i : α → ℕ} {Ls : α → List Fml} (hg : PolyT g) (hL : PolyT Ls) (hy : PolyT y) (ha : PolyT a)
    (hb : PolyT b) (hi : PolyT i) : PolyT fun x => mu (g x) (Ls x) (y x) (a x) (b x) (i x) := by
  unfold mu; fun_prop

/-- A number prescribed by the profile is at most the number of clauses. -/
theorem mu_le (g : ℕ) (Ls : List Fml) (y a b i : ℕ) : mu g Ls y a b i ≤ (cls Ls).length := by
  unfold mu digit; exact Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))

/-- A number prescribed by the profile is given in unary, since it is at most the number of clauses. -/
@[fun_prop] theorem mu_unary {g y a b i : α → ℕ} {Ls : α → List Fml} (hg : PolyT g) (hL : PolyT Ls) (hy : PolyT y) (ha : PolyT a)
    (hb : PolyT b) (hi : PolyT i) : Unary fun x => mu (g x) (Ls x) (y x) (a x) (b x) (i x) :=
  Unary.of_le (g := fun x => (cls (Ls x)).length) (by fun_prop) (by fun_prop) fun x => mu_le _ _ _ _ _ _

/-- The length of the label between two nodes is given in unary. -/
@[fun_prop] theorem mcap_unary {g n β b y a a' : α → ℕ} {Ls : α → List Fml} (hg : Unary g) (hn : PolyT n) (hβ : Unary β) (hb : Unary b)
    (hL : PolyT Ls) (hy : PolyT y) (ha : PolyT a) (ha' : PolyT a') :
    Unary fun x => mcap (g x) (n x) (β x) (b x) (Ls x) (y x) (a x) (a' x) := by
  have := hg.poly
  have := hb.poly
  unfold mcap; fun_prop

/-- The label that a state word sends to another node. -/
@[fun_prop] theorem mlab_polyT {g n β b a a' : α → ℕ} {Ls : α → List Fml} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hβ : Unary β)
    (hb : Unary b) (hL : PolyT Ls) (ha : PolyT a) (ha' : PolyT a') (hz : PolyT z) :
    PolyT fun x => mlab (g x) (n x) (β x) (b x) (Ls x) (a x) (a' x) (z x) := by
  unfold mlab; fun_prop


/-- (−1)^k by the parity of k. -/
theorem neg_one_pow_eq (k : ℕ) : (-1 : ℤ) ^ k = if k % 2 = 0 then 1 else -1 := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, if_pos (Nat.even_iff.1 h)]
  · rw [h.neg_one_pow, if_neg (by rw [Nat.odd_iff.1 h]; decide)]

/-- The sign (−1)^k is polynomial-time in k. -/
@[fun_prop] theorem sign_polyT {k : α → ℕ} (hk : PolyT k) : PolyT fun x => (-1 : ℤ) ^ k x := by
  simp only [neg_one_pow_eq]
  have : PolyT fun x => k x % 2 := PolyT.mod hk (PolyT.const 2)
  fun_prop

/-- The number of variables per node is given in unary if g and n are. -/
@[fun_prop] theorem qv_unary {g n : α → ℕ} (hg : Unary g) (hn : Unary n) : Unary fun x => qv (g x) (n x) := by
  unfold qv
  exact unary_div (unary_sub (unary_add hn hg) (PolyT.const 1)) hg.poly

/-- The first test of `mW`: the bits of absent variables are false. -/
def mW1 (g n a : ℕ) (z : List Bool) : Bool := (List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)

/-- One literal in the second test of `mW`. -/
def mW2l (q a : ℕ) (z : List Bool) (l : ℕ × Bool) : Bool := !(l.1 / q == a) || (z.getD (l.1 % q) false != l.2)

/-- The second test of `mW`: a marked clause has all its literals at a false. -/
def mW2 (g n : ℕ) (Ls : List Fml) (a : ℕ) (z : List Bool) : Bool :=
  (tch g n Ls a).all fun e => !(mark g n Ls a z e) || (clAt Ls e).2.all (mW2l (qv g n) a z)

/-- The third test of `mW`: the numbers of owned marked clauses are those of the profile. -/
def mW3 (g n : ℕ) (Ls : List Fml) (y a : ℕ) (z : List Bool) : Bool :=
  (List.range Ls.length).all fun i =>
    ((tch g n Ls a).filter fun e => (clAt Ls e).1 == i && ownB g n Ls e a && mark g n Ls a z e).length == mu g Ls y a a i

/-- The fourth test of `mW`: the weights of the strings are those of the profile. -/
def mW4 (g n : ℕ) (Ls : List Fml) (y a : ℕ) (z : List Bool) : Bool :=
  (List.range g).all fun a' => a' == a || (List.range Ls.length).all fun i => (str g n Ls a a' i z).count true == mu g Ls y a a' i

/-- The exponent of the sign in `mW`. -/
def mWs (g n : ℕ) (Ls : List Fml) (a : ℕ) (z : List Bool) : ℕ :=
  ((tch g n Ls a).filter fun e => decide (1 ≤ (clAt Ls e).1) && ownB g n Ls e a && mark g n Ls a z e).length

/-- `mW` written with the four tests and the exponent named above. -/
theorem mW_eq (g n : ℕ) (Ls : List Fml) (y a : ℕ) (z : List Bool) : mW g n Ls y a z =
    if mW1 g n a z && mW2 g n Ls a z && mW3 g n Ls y a z && mW4 g n Ls y a z then (-1) ^ mWs g n Ls a z else 0 := rfl

/-- The first test of `mW` is polynomial-time. -/
@[fun_prop] theorem mW1_polyT {g n a : α → ℕ} {z : α → List Bool} (hg : Unary g) (hn : Unary n) (ha : PolyT a) (hz : PolyT z) :
    PolyT fun x => mW1 (g x) (n x) (a x) (z x) := by
  have := hg.poly
  have := hn.poly
  unfold mW1; fun_prop

/-- The test of one literal is polynomial-time. -/
@[fun_prop] theorem mW2l_polyT {q a : α → ℕ} {z : α → List Bool} {l : α → ℕ × Bool} (hq : PolyT q) (ha : PolyT a) (hz : PolyT z)
    (hl : PolyT l) : PolyT fun x => mW2l (q x) (a x) (z x) (l x) := by
  have h1 : PolyT fun x => (l x).1 / q x := PolyT.div hl.fst hq
  have h2 : PolyT fun x => (l x).1 % q x := PolyT.mod hl.fst hq
  unfold mW2l; fun_prop

/-- The second test of `mW` is polynomial-time. -/
@[fun_prop] theorem mW2_polyT {g n a : α → ℕ} {Ls : α → List Fml} {z : α → List Bool} (hg : PolyT g) (hn : PolyT n) (hL : PolyT Ls)
    (ha : PolyT a) (hz : PolyT z) : PolyT fun x => mW2 (g x) (n x) (Ls x) (a x) (z x) := by
  unfold mW2; fun_prop

/-- The third test of `mW` is polynomial-time. -/
@[fun_prop] theorem mW3_polyT {g n y a : α → ℕ} {Ls : α → List Fml} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls)
    (hy : PolyT y) (ha : PolyT a) (hz : PolyT z) : PolyT fun x => mW3 (g x) (n x) (Ls x) (y x) (a x) (z x) := by
  have := hg.poly
  unfold mW3; fun_prop

/-- The fourth test of `mW` is polynomial-time. -/
@[fun_prop] theorem mW4_polyT {g n y a : α → ℕ} {Ls : α → List Fml} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls)
    (hy : PolyT y) (ha : PolyT a) (hz : PolyT z) : PolyT fun x => mW4 (g x) (n x) (Ls x) (y x) (a x) (z x) := by
  have := hg.poly
  unfold mW4; fun_prop

/-- The exponent of the sign in `mW` is polynomial-time. -/
@[fun_prop] theorem mWs_polyT {g n a : α → ℕ} {Ls : α → List Fml} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls)
    (ha : PolyT a) (hz : PolyT z) : PolyT fun x => mWs (g x) (n x) (Ls x) (a x) (z x) := by
  have := hg.poly
  unfold mWs; fun_prop

/-- The weight of a state word at a node is polynomial-time, with g and n in unary. -/
@[fun_prop] theorem mW_polyT {g n y a : α → ℕ} {Ls : α → List Fml} {z : α → List Bool} (hg : Unary g) (hn : Unary n) (hL : PolyT Ls)
    (hy : PolyT y) (ha : PolyT a) (hz : PolyT z) : PolyT fun x => mW (g x) (n x) (Ls x) (y x) (a x) (z x) := by
  have := hg.poly
  have := hn.poly
  simp only [mW_eq]; fun_prop


/-- The lengths of the network of marks are given in unary, and its two functions are
polynomial-time. -/
theorem markF_keeps : FKeeps markF where
  n := by
    have h : Unary fun p : MCtx × ℕ => qv p.1.1.1.length p.1.1.2.1.length + (tch p.1.1.1.length p.1.1.2.1.length p.1.2.1 p.2).length := by
      fun_prop
    exact h
  cap := by
    have h : Unary fun p : MCtx × ℕ × ℕ =>
        mcap p.1.1.1.length p.1.1.2.1.length p.1.1.2.2.1.length p.1.1.2.2.2.length p.1.2.1 p.1.2.2 p.2.1 p.2.2 := by fun_prop
    exact h
  W := by
    have h : PolyT fun x : MCtx × WQ => mW x.1.1.1.length x.1.1.2.1.length x.1.2.1 x.1.2.2 x.2.1 x.2.2 := by fun_prop
    exact h
  f := by
    have h : PolyT fun x : MCtx × FQ =>
        if mlab x.1.1.1.length x.1.1.2.1.length x.1.1.2.2.1.length x.1.1.2.2.2.length x.1.2.1 x.2.1.1 x.2.1.2 x.2.2.1 == x.2.2.2
        then (1 : ℤ) else 0 := by fun_prop
    exact h

/-- In a double sum over a' < a < g the inner range can be cut out of the outer one. -/
theorem sum_range_eq (g : ℕ) (F : ℕ → ℕ → ℕ) : ((List.range g).map fun a => ((List.range a).map fun a' => F a' a).sum).sum =
    ((List.range g).map fun a => (((List.range g).take a).map fun a' => F a' a).sum).sum := by
  congr 1
  refine List.map_congr_left fun a ha => ?_
  rw [List.take_range, min_eq_left (List.mem_range.1 ha).le]

/-- The test «the profile y is admissible» is polynomial-time, with g in unary, for every width k of
the clauses. -/
@[fun_prop] theorem adm_polyT (k : ℕ) {g n w y : α → ℕ} {Ls : α → List Fml} (hg : Unary g) (hn : PolyT n) (hw : PolyT w) (hL : PolyT Ls)
    (hy : PolyT y) : PolyT fun x => adm k (g x) (n x) (w x) (Ls x) (y x) := by
  have := hg.poly
  unfold adm; simp only [sum_range_eq]; fun_prop

end PaddedDescent.F.Mark.Cert

namespace PaddedDescent.F

open Groundwork Groundwork.Prog

/-- The network of marks has lengths in unary and polynomial-time functions. -/
theorem certMark : StCertMark := Mark.Cert.markF_keeps

/-- The test for admissible profiles is polynomial-time in (g, n, w in unary), the layers and the
profile. -/
theorem certAdm : StCertAdm := fun k =>
  Mark.Cert.adm_polyT k (g := fun q : (U × U × U) × List Fml × ℕ => q.1.1.length) (n := fun q => q.1.2.1.length) (w := fun q => q.1.2.2.length)
    (Ls := fun q => q.2.1) (y := fun q => q.2.2) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

end PaddedDescent.F
