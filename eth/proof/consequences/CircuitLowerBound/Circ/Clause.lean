/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Circ.Blocks
public import ToTuring.Poly.Sat
public import ToTuring.Poly.Words
import Mathlib.Tactic

/-! # The circuit that computes a clause of the formula of a table from the number of the clause

`stClauseCirc : StClauseCirc`. The inputs are the nb bits of the number j of a clause, lowest first:
the position q (bq bits), the time t (bt bits), the place r in the table (rb bits). The circuit has

* two wires with the constants 0 and 1;
* for every place k of the table a chain of rb gates for «r = k»;
* for each of the three literals and each bit that the table says about a literal (two bits for the
  way the time is formed, two for the way the position is formed, the sign, the bits of the kind,
  the bits of the
  number that is added to the position) a chain of gates for the OR, over the places k whose entry
  has this bit, of «r = k»; beyond the end of the table all these wires are 0, which is the clause
  `zeroCl`;
* for each of the three literals 3 gates for every bit of the time (a chain of half adders) and 7
  gates for every bit of the position (a choice between q and P, and a chain of full adders).

Only the last group grows with L: it has 3·(3·bt + 7·bq + 12) gates, which is at most 36·(L + 1).
The size of the others depends on the table only. All numbers of wires are written in closed form. -/

@[expose] public section

namespace CircuitLowerBound.Clause

open ENP Groundwork CircuitLowerBound.Blocks

/-! ### The circuit -/

/-- Literal number ι of a clause of a table. -/
def litI (c : TCl) (ι : ℕ) : TLit := if ι = 0 then c.1 else if ι = 1 then c.2.1 else c.2.2

/-- Bit number f of what the table says about a literal: two bits of the mode of the time, two bits
of the mode of the position, the sign, kbm bits of the kind, the bits of the number added to the
position. -/
def fbit (kbm : ℕ) (l : TLit) (f : ℕ) : Bool :=
  if f = 0 then l.2.1.testBit 0 else if f = 1 then l.2.1.testBit 1 else if f = 2 then l.2.2.1.testBit 0 else if f = 3 then l.2.2.1.testBit 1
  else if f = 4 then l.2.2.2.2 else if f < 5 + kbm then l.1.testBit (f - 5) else l.2.2.2.1.testBit (f - 5 - kbm)

/-- The wire «r = k»: the last wire of chain number k. -/
def Ew (n rb k : ℕ) : ℕ := prevW (n + 2 + rb * k) (n + 1) rb

/-- Gate i of the chain for «r = k»: the wire before, and «bit i of r is bit i of k». -/
def selGate (n bq bt rb k i : ℕ) : GateD := ((if k.testBit i then opAnd else opAndN), prevW (n + 2 + rb * k) (n + 1) i, bq + bt + i)

/-- The chain for «r = k». -/
def selChain (n bq bt rb k : ℕ) : List GateD := (List.range rb).map (selGate n bq bt rb k)

/-- The chains for «r = k», k < R. -/
def selG (n bq bt rb R : ℕ) : List GateD := (List.range R).flatMap (selChain n bq bt rb)

/-- The wire of bit f of literal ι; nf is the number of bits of a literal. -/
def Fw (n rb R nf ι f : ℕ) : ℕ := prevW (n + 2 + rb * R + R * (ι * nf + f)) n R

/-- Gate k of chain number a = ι·nf + f: the wire before, or «r = k» if the entry k of the table has
the bit f of literal ι. -/
def fldGate (n rb kbm nf : ℕ) (tb : List TCl) (a k : ℕ) : GateD :=
  ((if fbit kbm (litI (tb.getD k zeroCl) (a / nf)) (a % nf) then opOr else opFst), prevW (n + 2 + rb * tb.length + tb.length * a) n k, Ew n rb k)

/-- Chain number a. -/
def fldChain (n rb kbm nf : ℕ) (tb : List TCl) (a : ℕ) : List GateD := (List.range tb.length).map (fldGate n rb kbm nf tb a)

/-- The chains for the bits of the three literals. -/
def fldG (n rb kbm nf : ℕ) (tb : List TCl) : List GateD := (List.range (3 * nf)).flatMap (fldChain n rb kbm nf tb)

/-- The carry into bit i of the time; a is the first wire of the gates of the literal. -/
def cinT (a i : ℕ) : ℕ := if i = 0 then a + 1 else a + 3 + 3 * (i - 1) + 2

/-- The carry into bit i of the position; b is the first wire of the gates for the position, z the
wire with the constant 0. -/
def cinQ (z b i : ℕ) : ℕ := if i = 0 then z else b + 1 + 7 * (i - 1) + 6

/-- The three gates for bit i of the time: «the time is used» and bit i of t; the sum with the
carry; the next carry. -/
def timeBit (bq a i : ℕ) : List GateD := [(opAnd, a, bq + i), (opXor, a + 3 + 3 * i, cinT a i), (opAnd, a + 3 + 3 * i, cinT a i)]

/-- The gates for the time of a literal; m0, m1 are the wires of the mode. -/
def timeG (bq bt a m0 m1 : ℕ) : List GateD :=
  [(opXor, m0, m1), (opAndN, m1, m0), (opAnd, m0, m1)] ++ (List.range bt).flatMap (timeBit bq a) ++ [(opOr, cinT a bt, a + 2)]

/-- The seven gates for bit i of the position: bit i of q if q is used; or bit i of P if P is used;
then a full adder. -/
def posBit (z bq P b p1 : ℕ) (dW : ℕ → ℕ) (i : ℕ) : List GateD :=
  [(opAnd, b, if i < bq then i else z), ((if P.testBit i then opOr else opFst), b + 1 + 7 * i, p1), (opXor, b + 1 + 7 * i + 1, dW i),
   (opXor, b + 1 + 7 * i + 2, cinQ z b i), (opAnd, b + 1 + 7 * i + 1, dW i), (opAnd, b + 1 + 7 * i + 2, cinQ z b i),
   (opOr, b + 1 + 7 * i + 4, b + 1 + 7 * i + 5)]

/-- The gates for the position of a literal; p0, p1 are the wires of the mode, dW i the wire of bit
i of the number that is added. -/
def posG (z bq P b p0 p1 : ℕ) (dW : ℕ → ℕ) : List GateD := [(opAndN, p0, p1)] ++ (List.range (bq + 1)).flatMap (posBit z bq P b p1 dW)

/-- The number of gates for the time and the position of a literal. -/
def szL (bq bt : ℕ) : ℕ := 3 * bt + 7 * bq + 12

/-- The first wire of the gates for the time and the position of literal ι. -/
def offA (n bq bt rb R nf ι : ℕ) : ℕ := n + 2 + rb * R + R * (3 * nf) + szL bq bt * ι

/-- The wire of bit i of the number that is added to the position of literal ι. -/
def dWire (n rb R kbm Dq ι i : ℕ) : ℕ := if i < Dq then Fw n rb R (5 + kbm + Dq) ι (5 + kbm + i) else n

/-- The gates for the time and the position of literal ι. -/
def litG (n bq bt rb R kbm Dq P ι : ℕ) : List GateD :=
  timeG bq bt (offA n bq bt rb R (5 + kbm + Dq) ι) (Fw n rb R (5 + kbm + Dq) ι 0) (Fw n rb R (5 + kbm + Dq) ι 1) ++
    posG n bq P (offA n bq bt rb R (5 + kbm + Dq) ι + 4 + 3 * bt) (Fw n rb R (5 + kbm + Dq) ι 2) (Fw n rb R (5 + kbm + Dq) ι 3) (dWire n rb R kbm Dq ι)

/-- All gates. -/
def gatesC (n bq bt rb kbm Dq P : ℕ) (tb : List TCl) : List GateD :=
  [(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length ++ fldG n rb kbm (5 + kbm + Dq) tb ++
    (List.range 3).flatMap (litG n bq bt rb tb.length kbm Dq P)

/-- The output wires of literal ι: the position, the time, the kind, zeros up to L wires, the sign. -/
def outsL (n bq bt rb R kbm Dq L ι : ℕ) : List ℕ :=
  ((List.range (bq + 1)).map fun i => offA n bq bt rb R (5 + kbm + Dq) ι + 4 + 3 * bt + 1 + 7 * i + 3) ++
    ((List.range bt).map fun i => offA n bq bt rb R (5 + kbm + Dq) ι + 3 + 3 * i + 1) ++ [offA n bq bt rb R (5 + kbm + Dq) ι + 3 + 3 * bt] ++
    ((List.range kbm).map fun i => Fw n rb R (5 + kbm + Dq) ι (5 + i)) ++ ((List.range (L - (bq + bt + 2 + kbm))).map fun _ => n) ++
    [Fw n rb R (5 + kbm + Dq) ι 4]

/-- A number that is at least as large as every number that the table adds to a position. -/
def dSum (tb : List TCl) : ℕ := (tb.map fun c => c.1.2.2.2.1 + c.2.1.2.2.2.1 + c.2.2.2.2.2.1).sum

/-- The circuit and its output wires, from numbers that are cut off at L where they are lengths of
lists. -/
def coreB (n bq bt rb kbm Dq L P : ℕ) (tb : List TCl) : List GateD × List ℕ :=
  (gatesC n bq bt rb kbm Dq P tb, (List.range 3).flatMap (outsL n bq bt rb tb.length kbm Dq L))

/-- The circuit and its output wires. -/
def B (x : MCode × List Unit × ℕ) : List GateD × List ℕ :=
  coreB (nb x.1 x.2.1.length) (min (bq x.1 x.2.1.length) x.2.1.length) (bt x.1 x.2.1.length) (rb x.1) (min (kb x.1) x.2.1.length)
    (min (Nat.size (dSum (tab x.1))) (min (bq x.1 x.2.1.length) x.2.1.length + 1)) x.2.1.length x.2.2 (tab x.1)

/-! ### Lengths -/

theorem length_selG (n bq bt rb R : ℕ) : (selG n bq bt rb R).length = rb * R :=
  length_flatMap_const _ (fun _ => by simp [selChain]) R

theorem length_fldG (n rb kbm nf : ℕ) (tb : List TCl) : (fldG n rb kbm nf tb).length = tb.length * (3 * nf) :=
  length_flatMap_const _ (fun _ => by simp [fldChain]) _

theorem length_timeG (bq bt a m0 m1 : ℕ) : (timeG bq bt a m0 m1).length = 3 * bt + 4 := by
  simp only [timeG, List.length_append, length_flatMap_const (k := 3) (timeBit bq a) (fun _ => rfl) bt, List.length_cons, List.length_nil]
  omega

theorem length_posG (z bq P b p0 p1 : ℕ) (dW : ℕ → ℕ) : (posG z bq P b p0 p1 dW).length = 7 * (bq + 1) + 1 := by
  simp only [posG, List.length_append, length_flatMap_const (k := 7) (posBit z bq P b p1 dW) (fun _ => rfl) (bq + 1), List.length_cons, List.length_nil]
  omega

theorem length_litG (n bq bt rb R kbm Dq P ι : ℕ) : (litG n bq bt rb R kbm Dq P ι).length = szL bq bt := by
  rw [litG, List.length_append, length_timeG, length_posG, szL]
  omega

theorem length_gatesC (n bq bt rb kbm Dq P : ℕ) (tb : List TCl) :
    (gatesC n bq bt rb kbm Dq P tb).length = 2 + rb * tb.length + tb.length * (3 * (5 + kbm + Dq)) + szL bq bt * 3 := by
  simp only [gatesC, List.length_append, length_selG, length_fldG, length_flatMap_const _ (length_litG n bq bt rb tb.length kbm Dq P) 3,
    List.length_cons, List.length_nil]

theorem length_outsL {bq bt kbm L : ℕ} (hL : bq + bt + 2 + kbm ≤ L) (n rb R Dq ι : ℕ) : (outsL n bq bt rb R kbm Dq L ι).length = L + 1 := by
  simp only [outsL, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
  omega

/-! ### A gate whose function is chosen by a bit that is known when the circuit is written -/

theorem gval_ite (v : ℕ → Bool) (c : Bool) (o₁ o₂ : B4) (i j : ℕ) :
    gval v ((if c then o₁ else o₂), i, j) = if c then gval v (o₁, i, j) else gval v (o₂, i, j) := by
  cases c <;> rfl

/-- A number modulo 4 from its two lowest bits. -/
theorem mod_four (md : ℕ) : md % 4 = (md.testBit 0).toNat + 2 * (md.testBit 1).toNat := by
  have h0 : md.testBit 0 = decide (md % 2 = 1) := Nat.testBit_zero md
  have h1 : md.testBit 1 = decide (md / 2 % 2 = 1) := by rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.testBit_succ, Nat.testBit_zero]
  rw [h0, h1]
  rcases Nat.mod_two_eq_zero_or_one md with a | a <;> rcases Nat.mod_two_eq_zero_or_one (md / 2) with b | b <;> simp [a, b] <;> omega

/-! ### The time -/

theorem timeG_eqs {v : ℕ → Bool} {bq bt a m0 m1 : ℕ} (h : Obeys v a (timeG bq bt a m0 m1)) :
    v a = (v m0 ^^ v m1) ∧ v (a + 1) = (v m1 && !v m0) ∧ v (a + 2) = (v m0 && v m1) ∧
    (∀ i < bt, v (a + 3 + 3 * i) = (v a && v (bq + i)) ∧ v (a + 3 + 3 * i + 1) = (v (a + 3 + 3 * i) ^^ v (cinT a i)) ∧
      v (a + 3 + 3 * i + 2) = (v (a + 3 + 3 * i) && v (cinT a i))) ∧
    v (a + 3 + 3 * bt) = (v (cinT a bt) || v (a + 2)) := by
  rw [timeG, obeys_append, obeys_append, obeys_flatMap v _ (k := 3) (timeBit bq a) (fun _ => rfl) bt] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hl : a + ([(opXor, m0, m1), (opAndN, m1, m0), (opAnd, m0, m1)] ++ (List.range bt).flatMap (timeBit bq a)).length = a + 3 + 3 * bt := by
    rw [List.length_append, length_flatMap_const (k := 3) (timeBit bq a) (fun _ => rfl) bt]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [hl] at h3
  simp only [Obeys, gval_xor, gval_andN, gval_and, gval_or, and_true] at h1 h3
  refine ⟨h1.1, h1.2.1, h1.2.2, fun i hi => ?_, h3⟩
  have h4 := h2 i hi
  simp only [timeBit, Obeys, gval_xor, gval_and, and_true, List.length_cons, List.length_nil] at h4
  exact ⟨h4.1, h4.2.1, h4.2.2⟩

/-- The output wires for the time carry the time of the literal. -/
theorem time_val {v : ℕ → Bool} {bq bt a m0 m1 : ℕ} (h : Obeys v a (timeG bq bt a m0 m1)) {md t : ℕ} (hm0 : v m0 = md.testBit 0)
    (hm1 : v m1 = md.testBit 1) (ht : ∀ i < bt, v (bq + i) = t.testBit i) (htl : t < 2 ^ bt) :
    num (fun i => v (a + 3 + 3 * i + 1)) bt + 2 ^ bt * (v (a + 3 + 3 * bt)).toNat = tval bt t md := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := timeG_eqs h
  have hadd := half_adder (fun i => v (a + 3 + 3 * i)) (fun i => v (a + 3 + 3 * i + 1)) (fun i => v (cinT a i)) bt
    (fun i hi => (e3 i hi).2.1) (fun i hi => by
      have : cinT a (i + 1) = a + 3 + 3 * i + 2 := by simp [cinT]
      simp only [this]
      exact (e3 i hi).2.2) bt le_rfl
  have hc0 : cinT a 0 = a + 1 := by simp [cinT]
  simp only [hc0] at hadd
  have hA : num (fun i => v (a + 3 + 3 * i)) bt = if v a then t else 0 := by
    cases hu : v a
    · rw [num_congr (c := fun _ => false) fun i hi => by simp [(e3 i hi).1, hu], num_false]; rfl
    · rw [num_congr (c := t.testBit) fun i hi => by simp [(e3 i hi).1, hu, ht i hi], num_testBit, Nat.mod_eq_of_lt htl]; rfl
  rw [hA, e0, e1, hm0, hm1] at hadd
  rw [e4, e2, hm0, hm1]
  have h4 := mod_four md
  have hp : 0 < 2 ^ bt := by positivity
  unfold tval
  generalize num (fun i => v (a + 3 + 3 * i + 1)) bt = S at hadd ⊢
  generalize v (cinT a bt) = cb at hadd ⊢
  generalize 2 ^ bt = p at hadd hp ⊢
  generalize md.testBit 0 = b0 at h4 hadd ⊢
  generalize md.testBit 1 = b1 at h4 hadd ⊢
  generalize md % 4 = m4 at h4 ⊢
  subst h4
  cases b0 <;> cases b1 <;> cases cb <;> simp at hadd ⊢ <;> omega

/-! ### The position -/

theorem posG_eqs {v : ℕ → Bool} {z bq P b p0 p1 : ℕ} {dW : ℕ → ℕ} (h : Obeys v b (posG z bq P b p0 p1 dW)) :
    v b = (v p0 && !v p1) ∧ ∀ i < bq + 1,
      v (b + 1 + 7 * i) = (v b && v (if i < bq then i else z)) ∧
      v (b + 1 + 7 * i + 1) = (if P.testBit i then (v (b + 1 + 7 * i) || v p1) else v (b + 1 + 7 * i)) ∧
      v (b + 1 + 7 * i + 2) = (v (b + 1 + 7 * i + 1) ^^ v (dW i)) ∧
      v (b + 1 + 7 * i + 3) = (v (b + 1 + 7 * i + 2) ^^ v (cinQ z b i)) ∧
      v (b + 1 + 7 * i + 4) = (v (b + 1 + 7 * i + 1) && v (dW i)) ∧
      v (b + 1 + 7 * i + 5) = (v (b + 1 + 7 * i + 2) && v (cinQ z b i)) ∧
      v (b + 1 + 7 * i + 6) = (v (b + 1 + 7 * i + 4) || v (b + 1 + 7 * i + 5)) := by
  rw [posG, obeys_append, obeys_flatMap v _ (k := 7) (posBit z bq P b p1 dW) (fun _ => rfl) (bq + 1)] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Obeys, gval_andN, and_true] at h1
  refine ⟨h1, fun i hi => ?_⟩
  have h4 := h2 i hi
  simp only [posBit, Obeys, gval_xor, gval_and, gval_or, gval_ite, gval_fst, and_true, List.length_cons, List.length_nil] at h4
  exact ⟨h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, h4.2.2.2.2.1, h4.2.2.2.2.2.1, h4.2.2.2.2.2.2⟩

/-- The output wires for the position carry the position of the literal. -/
theorem pos_val {v : ℕ → Bool} {z bq P b p0 p1 : ℕ} {dW : ℕ → ℕ} (h : Obeys v b (posG z bq P b p0 p1 dW)) {md q dq : ℕ} (hz : v z = false)
    (hp0 : v p0 = md.testBit 0) (hp1 : v p1 = md.testBit 1) (hq : ∀ i < bq, v i = q.testBit i) (hql : q < 2 ^ bq)
    (hd : ∀ i < bq + 1, v (dW i) = dq.testBit i) :
    num (fun i => v (b + 1 + 7 * i + 3)) (bq + 1) = (qval P q md + dq) % 2 ^ (bq + 1) := by
  obtain ⟨e0, e⟩ := posG_eqs h
  have hadd := full_adder (fun i => v (b + 1 + 7 * i + 1)) (fun i => v (dW i)) (fun i => v (b + 1 + 7 * i + 3)) (fun i => v (cinQ z b i)) (bq + 1)
    (fun i hi => by
      obtain ⟨-, -, e2, e3, -⟩ := e i hi
      simp only [e3, e2])
    (fun i hi => by
      obtain ⟨-, -, e2, -, e4, e5, e6⟩ := e i hi
      have : cinQ z b (i + 1) = b + 1 + 7 * i + 6 := by simp [cinQ]
      simp only [this, e6, e4, e5, e2]) (bq + 1) le_rfl
  have hc0 : cinQ z b 0 = z := by simp [cinQ]
  simp only [hc0, hz] at hadd
  have hD : num (fun i => v (dW i)) (bq + 1) = dq % 2 ^ (bq + 1) := by rw [num_congr hd, num_testBit]
  have hqb : ∀ i < bq + 1, v (if i < bq then i else z) = q.testBit i := by
    intro i _
    split_ifs with hi
    · exact hq i hi
    · rw [hz]
      exact (Nat.testBit_eq_false_of_lt (hql.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm
  have hB : num (fun i => v (b + 1 + 7 * i + 1)) (bq + 1) = qval P q md % 2 ^ (bq + 1) := by
    have h4 := mod_four md
    have hb : ∀ i < bq + 1, v (b + 1 + 7 * i + 1) = (((md.testBit 0 && !md.testBit 1) && q.testBit i) || (P.testBit i && md.testBit 1)) := by
      intro i hi
      obtain ⟨e1, e2, -⟩ := e i hi
      rw [e2, e1, e0, hp0, hp1, hqb i hi]
      cases P.testBit i <;> simp
    rw [num_congr hb]
    unfold qval
    generalize md.testBit 0 = b0 at h4 ⊢
    generalize md.testBit 1 = b1 at h4 ⊢
    generalize md % 4 = m4 at h4 ⊢
    subst h4
    cases b0 <;> cases b1 <;> simp [num_false, num_testBit]
  rw [hD, hB] at hadd
  have hlt := num_lt (fun i => v (b + 1 + 7 * i + 3)) (bq + 1)
  rw [Nat.add_mod, ← Nat.add_zero (qval P q md % 2 ^ (bq + 1) + dq % 2 ^ (bq + 1))]
  have h0 : (false : Bool).toNat = 0 := rfl
  rw [h0] at hadd
  rw [← hadd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ### The place in the table -/

/-- The wire «r = k». -/
theorem sel_val {v : ℕ → Bool} {n bq bt rb R : ℕ} (h : Obeys v (n + 2) (selG n bq bt rb R)) (hO : v (n + 1) = true) {r : ℕ}
    (hr : ∀ i < rb, v (bq + bt + i) = r.testBit i) (hrl : r < 2 ^ rb) {k : ℕ} (hk : k < R) (hkl : k < 2 ^ rb) : v (Ew n rb k) = decide (r = k) := by
  rw [selG, obeys_flatMap v _ (k := rb) (selChain n bq bt rb) (fun _ => by simp [selChain]) R] at h
  have h1 := h k hk
  rw [selChain, obeys_map] at h1
  have h2 := chain_all v (n + 2 + rb * k) (n + 1) rb (fun i => decide (r.testBit i = k.testBit i)) (fun i hi => by
    rw [h1 i hi, selGate, gval_ite, gval_and, gval_andN, hr i hi]
    cases k.testBit i <;> cases r.testBit i <;> simp) rb le_rfl
  rw [Ew, h2, hO, Bool.true_and]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · intro h3
    have := num_congr (b := r.testBit) (c := k.testBit) (w := rb) h3
    rwa [num_testBit, num_testBit, Nat.mod_eq_of_lt hrl, Nat.mod_eq_of_lt hkl] at this
  · rintro rfl i _
    rfl

theorem litI_zeroCl (ι : ℕ) : litI zeroCl ι = (0, 0, 0, 0, false) := by
  unfold litI zeroCl
  split_ifs <;> rfl

theorem fbit_zero (kbm ι f : ℕ) : fbit kbm (litI zeroCl ι) f = false := by
  rw [litI_zeroCl]
  unfold fbit
  split_ifs <;> simp

/-- The wire of a bit of what the table says at the place r. -/
theorem fld_val {v : ℕ → Bool} {n rb kbm nf : ℕ} {tb : List TCl} (h : Obeys v (n + 2 + rb * tb.length) (fldG n rb kbm nf tb)) (hZ : v n = false) {r : ℕ}
    (hE : ∀ k < tb.length, v (Ew n rb k) = decide (r = k)) {a : ℕ} (ha : a < 3 * nf) :
    v (prevW (n + 2 + rb * tb.length + tb.length * a) n tb.length) = fbit kbm (litI (tb.getD r zeroCl) (a / nf)) (a % nf) := by
  rw [fldG, obeys_flatMap v _ (k := tb.length) (fldChain n rb kbm nf tb) (fun _ => by simp [fldChain]) (3 * nf)] at h
  have h1 := h a ha
  rw [fldChain, obeys_map] at h1
  have h2 := chain_any v (n + 2 + rb * tb.length + tb.length * a) n tb.length
    (fun k => fbit kbm (litI (tb.getD k zeroCl) (a / nf)) (a % nf) && decide (r = k)) (fun k hk => by
    rw [h1 k hk, fldGate, gval_ite, gval_or, gval_fst, hE k hk]
    cases fbit kbm (litI (tb.getD k zeroCl) (a / nf)) (a % nf) <;> simp) tb.length le_rfl
  rw [h2, hZ, Bool.false_or]
  by_cases hr : r < tb.length
  · rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨k, -, h3, rfl⟩
      exact h3
    · intro h3
      exact ⟨r, hr, h3, rfl⟩
  · rw [List.getD_eq_default _ _ (by omega), fbit_zero]
    simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq, not_exists, not_and]
    intro k hk _ hrk
    omega

/-- The wire of bit f of literal ι. -/
theorem Fw_val {v : ℕ → Bool} {n rb kbm nf : ℕ} {tb : List TCl} (h : Obeys v (n + 2 + rb * tb.length) (fldG n rb kbm nf tb)) (hZ : v n = false) {r : ℕ}
    (hE : ∀ k < tb.length, v (Ew n rb k) = decide (r = k)) {ι f : ℕ} (hι : ι < 3) (hf : f < nf) :
    v (Fw n rb tb.length nf ι f) = fbit kbm (litI (tb.getD r zeroCl) ι) f := by
  have ha : ι * nf + f < 3 * nf := by nlinarith
  have h1 := fld_val h hZ hE ha
  have e1 : (ι * nf + f) / nf = ι := by rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hf, Nat.add_zero]
  have e2 : (ι * nf + f) % nf = f := by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hf]
  rw [e1, e2] at h1
  exact h1

/-! ### Every gate reads earlier wires -/

theorem wfa_timeG {bq bt a m0 m1 : ℕ} (h0 : m0 < a) (h1 : m1 < a) (hin : bq + bt ≤ a) : WFa a (timeG bq bt a m0 m1) := by
  rw [timeG, wfa_append, wfa_append, wfa_flatMap _ (k := 3) (timeBit bq a) (fun _ => rfl) bt]
  refine ⟨⟨?_, fun i hi => ?_⟩, ?_⟩
  · simp only [WFa, and_true]
    and_intros <;> omega
  · simp only [timeBit, WFa, cinT, and_true, List.length_cons, List.length_nil]
    split_ifs <;> and_intros <;> omega
  · rw [List.length_append, length_flatMap_const (k := 3) (timeBit bq a) (fun _ => rfl) bt]
    simp only [WFa, cinT, and_true, List.length_cons, List.length_nil]
    split_ifs <;> and_intros <;> omega

theorem wfa_posG {z bq P b p0 p1 : ℕ} {dW : ℕ → ℕ} (h0 : p0 < b) (h1 : p1 < b) (hz : z < b) (hin : bq ≤ b) (hd : ∀ i, dW i < b) :
    WFa b (posG z bq P b p0 p1 dW) := by
  rw [posG, wfa_append, wfa_flatMap _ (k := 7) (posBit z bq P b p1 dW) (fun _ => rfl) (bq + 1)]
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [WFa, and_true]
    and_intros <;> omega
  · have := hd i
    simp only [posBit, WFa, cinQ, and_true, List.length_cons, List.length_nil]
    split_ifs <;> and_intros <;> omega

theorem wfa_selG {n bq bt rb : ℕ} (hn : bq + bt + rb ≤ n) (R : ℕ) : WFa (n + 2) (selG n bq bt rb R) := by
  rw [selG, wfa_flatMap _ (k := rb) (selChain n bq bt rb) (fun _ => by simp [selChain]) R]
  intro k _
  rw [selChain, wfa_map]
  intro i hi
  exact ⟨prevW_lt (by omega), by simp only [selGate]; omega⟩

theorem Ew_lt (n rb : ℕ) {R k : ℕ} (hk : k < R) : Ew n rb k < n + 2 + rb * R := by
  have h1 : Ew n rb k < n + 2 + rb * k + rb := prevW_lt (by omega)
  have h2 : rb * (k + 1) ≤ rb * R := Nat.mul_le_mul_left _ hk
  rw [Nat.mul_succ] at h2
  omega

theorem wfa_fldG (n rb kbm nf : ℕ) (tb : List TCl) : WFa (n + 2 + rb * tb.length) (fldG n rb kbm nf tb) := by
  rw [fldG, wfa_flatMap _ (k := tb.length) (fldChain n rb kbm nf tb) (fun _ => by simp [fldChain]) (3 * nf)]
  intro a _
  rw [fldChain, wfa_map]
  intro k hk
  have := Ew_lt n rb hk
  exact ⟨prevW_lt (by omega), by simp only [fldGate]; omega⟩

theorem Fw_lt (n rb R : ℕ) {nf ι f : ℕ} (hι : ι < 3) (hf : f < nf) : Fw n rb R nf ι f < n + 2 + rb * R + R * (3 * nf) := by
  have h1 : Fw n rb R nf ι f < n + 2 + rb * R + R * (ι * nf + f) + R := prevW_lt (by omega)
  have h2 : R * (ι * nf + f + 1) ≤ R * (3 * nf) := Nat.mul_le_mul_left _ (by nlinarith)
  rw [Nat.mul_succ] at h2
  omega

theorem offA_ge (n bq bt rb R nf ι : ℕ) : n + 2 + rb * R + R * (3 * nf) ≤ offA n bq bt rb R nf ι := Nat.le_add_right _ _

theorem dWire_lt (n rb R kbm Dq : ℕ) {ι : ℕ} (hι : ι < 3) (i : ℕ) : dWire n rb R kbm Dq ι i < n + 2 + rb * R + R * (3 * (5 + kbm + Dq)) := by
  unfold dWire
  split_ifs with h
  · exact Fw_lt n rb R hι (by omega)
  · omega

theorem wfa_litG {n bq bt rb : ℕ} (hn : bq + bt + rb ≤ n) (R kbm Dq P : ℕ) {ι : ℕ} (hι : ι < 3) :
    WFa (offA n bq bt rb R (5 + kbm + Dq) ι) (litG n bq bt rb R kbm Dq P ι) := by
  have hg := offA_ge n bq bt rb R (5 + kbm + Dq) ι
  have f0 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 0) hι (by omega)
  have f1 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 1) hι (by omega)
  have f2 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 2) hι (by omega)
  have f3 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 3) hι (by omega)
  rw [litG, wfa_append, length_timeG]
  refine ⟨wfa_timeG (by omega) (by omega) (by omega), ?_⟩
  rw [show offA n bq bt rb R (5 + kbm + Dq) ι + (3 * bt + 4) = offA n bq bt rb R (5 + kbm + Dq) ι + 4 + 3 * bt by omega]
  exact wfa_posG (by omega) (by omega) (by omega) (by omega) fun i => by have := dWire_lt n rb R kbm Dq hι i; omega

theorem wfa_gatesC {n bq bt rb : ℕ} (hn : bq + bt + rb ≤ n) (h1 : 1 ≤ n) (kbm Dq P : ℕ) (tb : List TCl) : WFa n (gatesC n bq bt rb kbm Dq P tb) := by
  rw [gatesC, wfa_append, wfa_append, wfa_append, wfa_flatMap _ (k := szL bq bt) _ (length_litG n bq bt rb tb.length kbm Dq P) 3]
  refine ⟨⟨⟨?_, wfa_selG hn _⟩, ?_⟩, fun ι hι => ?_⟩
  · simp only [WFa, and_true]
    and_intros <;> omega
  · have e : n + ([(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length).length = n + 2 + rb * tb.length := by
      rw [List.length_append, length_selG]
      simp only [List.length_cons, List.length_nil]
      omega
    rw [e]
    exact wfa_fldG n rb kbm _ tb
  · have e : n + ([(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length ++ fldG n rb kbm (5 + kbm + Dq) tb).length + szL bq bt * ι =
        offA n bq bt rb tb.length (5 + kbm + Dq) ι := by
      rw [List.length_append, List.length_append, length_selG, length_fldG, offA]
      simp only [List.length_cons, List.length_nil]
      omega
    rw [e]
    exact wfa_litG hn _ kbm Dq P hι

/-- The output wires are wires of the circuit. -/
theorem outsL_lt (n bq bt rb R kbm Dq L : ℕ) {ι : ℕ} (hι : ι < 3) :
    ∀ w ∈ outsL n bq bt rb R kbm Dq L ι, w < n + (2 + rb * R + R * (3 * (5 + kbm + Dq)) + szL bq bt * 3) := by
  have h1 : offA n bq bt rb R (5 + kbm + Dq) ι + szL bq bt ≤ n + 2 + rb * R + R * (3 * (5 + kbm + Dq)) + szL bq bt * 3 := by
    have : szL bq bt * (ι + 1) ≤ szL bq bt * 3 := Nat.mul_le_mul_left _ hι
    rw [Nat.mul_succ] at this
    unfold offA
    omega
  intro w hw
  simp only [outsL, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hw
  unfold szL at h1 ⊢
  rcases hw with ((((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | rfl) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | rfl
  · omega
  · omega
  · omega
  · have := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 5 + i) hι (by omega)
    omega
  · omega
  · have := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 4) hι (by omega)
    omega

/-! ### What the output wires carry -/

theorem fbit_kind {kbm i : ℕ} (l : TLit) (h : i < kbm) : fbit kbm l (5 + i) = l.1.testBit i := by
  unfold fbit
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem fbit_dq (kbm i : ℕ) (l : TLit) : fbit kbm l (5 + kbm + i) = l.2.2.2.1.testBit i := by
  unfold fbit
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

/-- The values of the output wires of literal ι, for the clause number j. -/
theorem core_val {n bq bt rb kbm Dq L P : ℕ} {tb : List TCl} (hn : n = rb + bt + bq) (hbt : 1 ≤ bt) (hR : tb.length < 2 ^ rb) (hL : bq + bt + 2 + kbm ≤ L)
    (hD : ∀ k ι i, Dq ≤ i → i < bq + 1 → (litI (tb.getD k zeroCl) ι).2.2.2.1.testBit i = false) {j : ℕ} (hj : j < 2 ^ n) {ι : ℕ} (hι : ι < 3)
    (v : ℕ → Bool) (hv : v = fun i => (wires (toWord n j) (toC (gatesC n bq bt rb kbm Dq P tb))).getD i false)
    (l : TLit) (hl : l = litI (tb.getD (j / 2 ^ (bt + bq)) zeroCl) ι) :
    ofWord (((outsL n bq bt rb tb.length kbm Dq L ι).take L).map v) =
      ((l.1 % 2 ^ kbm) * 2 ^ (bt + 1) + tval bt (j / 2 ^ bq % 2 ^ bt) l.2.1) * 2 ^ (bq + 1) + (qval P (j % 2 ^ bq) l.2.2.1 + l.2.2.2.1) % 2 ^ (bq + 1) ∧
    v ((outsL n bq bt rb tb.length kbm Dq L ι).getD L 0) = l.2.2.2.2 := by
  have hx : (toWord n j).length = n := length_toWord n j
  have hwf : WFa n (gatesC n bq bt rb kbm Dq P tb) := wfa_gatesC (by omega) (by omega) kbm Dq P tb
  have hob : Obeys v n (gatesC n bq bt rb kbm Dq P tb) := by
    have := obeys_wires (toWord n j) (gatesC n bq bt rb kbm Dq P tb) (by rw [hx]; exact hwf)
    rw [hx] at this
    rw [hv]
    exact this
  have hin : ∀ k < n, v k = j.testBit k := by
    intro k hk
    rw [hv]
    simp only
    rw [wires_input _ _ (by rw [hx]; exact hk), getD_toWord hk]
  rw [gatesC, obeys_append, obeys_append, obeys_append, obeys_flatMap v _ (k := szL bq bt) _ (length_litG n bq bt rb tb.length kbm Dq P) 3] at hob
  obtain ⟨⟨⟨hc, hsel⟩, hfld⟩, hlit⟩ := hob
  have e1 : n + ([(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length).length = n + 2 + rb * tb.length := by
    rw [List.length_append, length_selG]
    simp only [List.length_cons, List.length_nil]
    omega
  have e2 : n + ([(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length ++ fldG n rb kbm (5 + kbm + Dq) tb).length + szL bq bt * ι =
      offA n bq bt rb tb.length (5 + kbm + Dq) ι := by
    rw [List.length_append, List.length_append, length_selG, length_fldG, offA]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [e1] at hfld
  have hlit' := hlit ι hι
  rw [e2, litG, obeys_append, length_timeG,
    show offA n bq bt rb tb.length (5 + kbm + Dq) ι + (3 * bt + 4) = offA n bq bt rb tb.length (5 + kbm + Dq) ι + 4 + 3 * bt by omega] at hlit'
  obtain ⟨htime, hpos⟩ := hlit'
  simp only [Obeys, gval_zero, gval_one, and_true] at hc
  obtain ⟨hZ, hO⟩ := hc
  -- the three parts of j
  have hrl : j / 2 ^ (bt + bq) < 2 ^ rb := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, ← Nat.add_assoc, ← hn]
    exact hj
  have hrb : ∀ i < rb, v (bq + bt + i) = (j / 2 ^ (bt + bq)).testBit i := by
    intro i hi
    rw [hin _ (by omega), Nat.testBit_div_two_pow, Nat.add_comm bq bt, Nat.add_comm i]
  have htb : ∀ i < bt, v (bq + i) = (j / 2 ^ bq % 2 ^ bt).testBit i := by
    intro i hi
    rw [hin _ (by omega), Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i]
    simp [hi]
  have hqb : ∀ i < bq, v i = (j % 2 ^ bq).testBit i := by
    intro i hi
    rw [hin _ (by omega), Nat.testBit_mod_two_pow]
    simp [hi]
  have hE : ∀ k < tb.length, v (Ew n rb k) = decide (j / 2 ^ (bt + bq) = k) := fun k hk => sel_val hsel hO hrb hrl hk (hk.trans hR)
  have hF : ∀ f < 5 + kbm + Dq, v (Fw n rb tb.length (5 + kbm + Dq) ι f) = fbit kbm l f := fun f hf => by
    rw [hl]
    exact Fw_val hfld hZ hE hι hf
  have hT := time_val htime (md := l.2.1) (t := j / 2 ^ bq % 2 ^ bt) (by rw [hF 0 (by omega)]; rfl) (by rw [hF 1 (by omega)]; rfl) htb
    (Nat.mod_lt _ (by positivity))
  have hP := pos_val hpos (md := l.2.2.1) (q := j % 2 ^ bq) (dq := l.2.2.2.1) hZ (by rw [hF 2 (by omega)]; rfl) (by rw [hF 3 (by omega)]; rfl) hqb
    (Nat.mod_lt _ (by positivity)) (fun i hi => by
      unfold dWire
      split_ifs with h
      · rw [hF _ (by omega), fbit_dq]
      · rw [hZ, hl, hD _ _ i (by omega) hi])
  have hK : num (fun i => v (Fw n rb tb.length (5 + kbm + Dq) ι (5 + i))) kbm = l.1 % 2 ^ kbm := by
    rw [num_congr (c := l.1.testBit) fun i hi => by rw [hF _ (by omega), fbit_kind l hi], num_testBit]
  have hZs : num (fun _ => v n) (L - (bq + bt + 2 + kbm)) = 0 := by
    rw [hZ]
    exact num_false _
  unfold outsL
  constructor
  · rw [List.take_left' (by
      simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
      omega)]
    simp only [List.map_append, List.map_map, ofWord_append, List.length_append, List.length_map, List.length_range, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil]
    change num (fun i => v (offA n bq bt rb tb.length (5 + kbm + Dq) ι + 4 + 3 * bt + 1 + 7 * i + 3)) (bq + 1) +
      2 ^ (bq + 1) * num (fun i => v (offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * i + 1)) bt +
      2 ^ (bq + 1 + bt) * ofWord [v (offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * bt)] +
      2 ^ (bq + 1 + bt + (0 + 1)) * num (fun i => v (Fw n rb tb.length (5 + kbm + Dq) ι (5 + i))) kbm +
      2 ^ (bq + 1 + bt + (0 + 1) + kbm) * num (fun _ => v n) (L - (bq + bt + 2 + kbm)) = _
    rw [hP, hK, hZs, ← hT]
    simp only [ofWord]
    ring
  · rw [List.getD_append_right _ _ _ _ (by
      simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
      omega)]
    have e : L - ((((List.range (bq + 1)).map fun i => offA n bq bt rb tb.length (5 + kbm + Dq) ι + 4 + 3 * bt + 1 + 7 * i + 3) ++
        ((List.range bt).map fun i => offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * i + 1) ++ [offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * bt] ++
        ((List.range kbm).map fun i => Fw n rb tb.length (5 + kbm + Dq) ι (5 + i)) ++ ((List.range (L - (bq + bt + 2 + kbm))).map fun _ => n)).length) = 0 := by
      simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
      omega
    rw [e, List.getD_cons_zero, hF 4 (by omega)]
    rfl

/-! ### The circuit is written in polynomial time -/

section poly

variable {α : Type} [Enc α]

@[fun_prop] theorem prevW_polyT {off init i : α → ℕ} (h1 : PolyT off) (h2 : PolyT init) (h3 : PolyT i) :
    PolyT fun x => prevW (off x) (init x) (i x) := by unfold prevW; fun_prop

@[fun_prop] theorem litI_polyT {c : α → TCl} {ι : α → ℕ} (h1 : PolyT c) (h2 : PolyT ι) : PolyT fun x => litI (c x) (ι x) := by unfold litI; fun_prop

@[fun_prop] theorem fbit_polyT {kbm f : α → ℕ} {l : α → TLit} (h1 : PolyT kbm) (h2 : PolyT l) (h3 : PolyT f) :
    PolyT fun x => fbit (kbm x) (l x) (f x) := by unfold fbit; fun_prop

@[fun_prop] theorem Ew_polyT {n rb k : α → ℕ} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT k) : PolyT fun x => Ew (n x) (rb x) (k x) := by
  unfold Ew; fun_prop

@[fun_prop] theorem selGate_polyT {n bq bt rb k i : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT bt) (h4 : PolyT rb) (h5 : PolyT k) (h6 : PolyT i) :
    PolyT fun x => selGate (n x) (bq x) (bt x) (rb x) (k x) (i x) := by unfold selGate; fun_prop

theorem selChain_polyT {n bq bt rb k : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT bt) (h4 : Unary rb) (h5 : PolyT k) :
    PolyT fun x => selChain (n x) (bq x) (bt x) (rb x) (k x) :=
  PolyT.map (f := fun x i => selGate (n x) (bq x) (bt x) (rb x) (k x) i) (by have := h4.poly; fun_prop) (PolyT.range h4)

theorem selG_polyT {n bq bt rb R : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT bt) (h4 : Unary rb) (h5 : Unary R) :
    PolyT fun x => selG (n x) (bq x) (bt x) (rb x) (R x) :=
  PolyT.flatMap (f := fun x k => selChain (n x) (bq x) (bt x) (rb x) k)
    (selChain_polyT (by fun_prop) (by fun_prop) (by fun_prop) (h4.comp (h := Prod.fst) (by fun_prop)) (by fun_prop)) (PolyT.range h5)

@[fun_prop] theorem Fw_polyT {n rb R nf ι f : α → ℕ} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT R) (h4 : PolyT nf) (h5 : PolyT ι) (h6 : PolyT f) :
    PolyT fun x => Fw (n x) (rb x) (R x) (nf x) (ι x) (f x) := by unfold Fw; fun_prop

@[fun_prop] theorem fldGate_polyT {n rb kbm nf a k : α → ℕ} {tb : α → List TCl} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT kbm) (h4 : PolyT nf)
    (h5 : PolyT tb) (h6 : PolyT a) (h7 : PolyT k) : PolyT fun x => fldGate (n x) (rb x) (kbm x) (nf x) (tb x) (a x) (k x) := by
  unfold fldGate; fun_prop

theorem fldChain_polyT {n rb kbm nf a : α → ℕ} {tb : α → List TCl} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT kbm) (h4 : PolyT nf)
    (h5 : PolyT tb) (h6 : PolyT a) : PolyT fun x => fldChain (n x) (rb x) (kbm x) (nf x) (tb x) (a x) :=
  PolyT.map (f := fun x k => fldGate (n x) (rb x) (kbm x) (nf x) (tb x) (a x) k) (by fun_prop) (PolyT.range (Unary.of_length h5))

theorem fldG_polyT {n rb kbm nf : α → ℕ} {tb : α → List TCl} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT kbm) (h4 : Unary nf) (h5 : PolyT tb) :
    PolyT fun x => fldG (n x) (rb x) (kbm x) (nf x) (tb x) :=
  PolyT.flatMap (f := fun x a => fldChain (n x) (rb x) (kbm x) (nf x) (tb x) a)
    (fldChain_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by have := h4.poly; fun_prop) (by fun_prop) (by fun_prop))
    (PolyT.range ((Unary.const 3).mul h4))

@[fun_prop] theorem cinT_polyT {a i : α → ℕ} (h1 : PolyT a) (h2 : PolyT i) : PolyT fun x => cinT (a x) (i x) := by unfold cinT; fun_prop

@[fun_prop] theorem cinQ_polyT {z b i : α → ℕ} (h1 : PolyT z) (h2 : PolyT b) (h3 : PolyT i) : PolyT fun x => cinQ (z x) (b x) (i x) := by
  unfold cinQ; fun_prop

@[fun_prop] theorem timeBit_polyT {bq a i : α → ℕ} (h1 : PolyT bq) (h2 : PolyT a) (h3 : PolyT i) : PolyT fun x => timeBit (bq x) (a x) (i x) := by
  unfold timeBit; fun_prop

theorem timeG_polyT {bq bt a m0 m1 : α → ℕ} (h1 : PolyT bq) (h2 : Unary bt) (h3 : PolyT a) (h4 : PolyT m0) (h5 : PolyT m1) :
    PolyT fun x => timeG (bq x) (bt x) (a x) (m0 x) (m1 x) := by
  have h6 : PolyT fun x => (List.range (bt x)).flatMap (timeBit (bq x) (a x)) :=
    PolyT.flatMap (f := fun x i => timeBit (bq x) (a x) i) (by fun_prop) (PolyT.range h2)
  have := h2.poly
  unfold timeG
  fun_prop

@[fun_prop] theorem dWire_polyT {n rb R kbm Dq ι i : α → ℕ} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT R) (h4 : PolyT kbm) (h5 : PolyT Dq) (h6 : PolyT ι)
    (h7 : PolyT i) : PolyT fun x => dWire (n x) (rb x) (R x) (kbm x) (Dq x) (ι x) (i x) := by unfold dWire; fun_prop

theorem posBit_polyT {n bq P b p1 rb R kbm Dq ι i : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT P) (h4 : PolyT b) (h5 : PolyT p1) (h6 : PolyT rb)
    (h7 : PolyT R) (h8 : PolyT kbm) (h9 : PolyT Dq) (h10 : PolyT ι) (h11 : PolyT i) :
    PolyT fun x => posBit (n x) (bq x) (P x) (b x) (p1 x) (dWire (n x) (rb x) (R x) (kbm x) (Dq x) (ι x)) (i x) := by
  unfold posBit; fun_prop

theorem posG_polyT {n bq P b p0 p1 rb R kbm Dq ι : α → ℕ} (h1 : PolyT n) (h2 : Unary bq) (h3 : PolyT P) (h4 : PolyT b) (h0 : PolyT p0) (h5 : PolyT p1)
    (h6 : PolyT rb) (h7 : PolyT R) (h8 : PolyT kbm) (h9 : PolyT Dq) (h10 : PolyT ι) :
    PolyT fun x => posG (n x) (bq x) (P x) (b x) (p0 x) (p1 x) (dWire (n x) (rb x) (R x) (kbm x) (Dq x) (ι x)) := by
  have hq := h2.poly
  have h12 : PolyT fun x => (List.range (bq x + 1)).flatMap (posBit (n x) (bq x) (P x) (b x) (p1 x) (dWire (n x) (rb x) (R x) (kbm x) (Dq x) (ι x))) :=
    PolyT.flatMap (f := fun x i => posBit (n x) (bq x) (P x) (b x) (p1 x) (dWire (n x) (rb x) (R x) (kbm x) (Dq x) (ι x)) i)
      (posBit_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop)) (PolyT.range (h2.add (Unary.const 1)))
  unfold posG
  fun_prop

@[fun_prop] theorem szL_polyT {bq bt : α → ℕ} (h1 : PolyT bq) (h2 : PolyT bt) : PolyT fun x => szL (bq x) (bt x) := by unfold szL; fun_prop

@[fun_prop] theorem offA_polyT {n bq bt rb R nf ι : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT bt) (h4 : PolyT rb) (h5 : PolyT R) (h6 : PolyT nf)
    (h7 : PolyT ι) : PolyT fun x => offA (n x) (bq x) (bt x) (rb x) (R x) (nf x) (ι x) := by unfold offA; fun_prop

theorem litG_polyT {n bq bt rb R kbm Dq P ι : α → ℕ} (h1 : PolyT n) (h2 : Unary bq) (h3 : Unary bt) (h4 : PolyT rb) (h5 : PolyT R) (h6 : PolyT kbm)
    (h7 : PolyT Dq) (h8 : PolyT P) (h9 : PolyT ι) : PolyT fun x => litG (n x) (bq x) (bt x) (rb x) (R x) (kbm x) (Dq x) (P x) (ι x) := by
  have hq := h2.poly
  have ht := h3.poly
  exact PolyT.append (timeG_polyT hq h3 (by fun_prop) (by fun_prop) (by fun_prop))
    (posG_polyT h1 h2 h8 (by fun_prop) (by fun_prop) (by fun_prop) h4 h5 h6 h7 h9)

theorem gatesC_polyT {n bq bt rb kbm Dq P : α → ℕ} {tb : α → List TCl} (h1 : PolyT n) (h2 : Unary bq) (h3 : Unary bt) (h4 : Unary rb) (h6 : Unary kbm)
    (h7 : Unary Dq) (h8 : PolyT P) (h9 : PolyT tb) : PolyT fun x => gatesC (n x) (bq x) (bt x) (rb x) (kbm x) (Dq x) (P x) (tb x) := by
  have hq := h2.poly
  have ht := h3.poly
  have hr := h4.poly
  have hk := h6.poly
  have hd := h7.poly
  have g1 : PolyT fun x => selG (n x) (bq x) (bt x) (rb x) (tb x).length := selG_polyT h1 hq ht h4 (Unary.of_length h9)
  have g2 : PolyT fun x => fldG (n x) (rb x) (kbm x) (5 + kbm x + Dq x) (tb x) := fldG_polyT h1 hr hk (((Unary.const 5).add h6).add h7) h9
  have g3 : PolyT fun x => (List.range 3).flatMap (litG (n x) (bq x) (bt x) (rb x) (tb x).length (kbm x) (Dq x) (P x)) :=
    PolyT.flatMap (f := fun x ι => litG (n x) (bq x) (bt x) (rb x) (tb x).length (kbm x) (Dq x) (P x) ι)
      (litG_polyT (by fun_prop) (h2.comp (h := Prod.fst) (by fun_prop)) (h3.comp (h := Prod.fst) (by fun_prop)) (by fun_prop) (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop) (by fun_prop)) (PolyT.const _)
  unfold gatesC
  fun_prop

theorem outs_aux1 {a bt w : α → ℕ} (h1 : PolyT a) (h2 : PolyT bt) (h3 : Unary w) :
    PolyT fun x => (List.range (w x)).map fun i => a x + 4 + 3 * bt x + 1 + 7 * i + 3 :=
  PolyT.map (f := fun x i => a x + 4 + 3 * bt x + 1 + 7 * i + 3) (by fun_prop) (PolyT.range h3)

theorem outs_aux2 {a w : α → ℕ} (h1 : PolyT a) (h3 : Unary w) : PolyT fun x => (List.range (w x)).map fun i => a x + 3 + 3 * i + 1 :=
  PolyT.map (f := fun x i => a x + 3 + 3 * i + 1) (by fun_prop) (PolyT.range h3)

theorem outs_aux3 {a bt : α → ℕ} (h1 : PolyT a) (h2 : PolyT bt) : PolyT fun x => [a x + 3 + 3 * bt x] := by fun_prop

theorem outsL_polyT {n bq bt rb R kbm Dq L ι : α → ℕ} (h1 : PolyT n) (h2 : Unary bq) (h3 : Unary bt) (h4 : PolyT rb) (h5 : PolyT R) (h6 : Unary kbm)
    (h7 : PolyT Dq) (h8 : Unary L) (h9 : PolyT ι) : PolyT fun x => outsL (n x) (bq x) (bt x) (rb x) (R x) (kbm x) (Dq x) (L x) (ι x) := by
  have hq := h2.poly
  have ht := h3.poly
  have hk := h6.poly
  have hl := h8.poly
  have ha : PolyT fun x => offA (n x) (bq x) (bt x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) := by fun_prop
  have r1 : PolyT fun x => (List.range (bq x + 1)).map fun i => offA (n x) (bq x) (bt x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) + 4 + 3 * bt x + 1 + 7 * i + 3 :=
    outs_aux1 ha ht (h2.add (Unary.const 1))
  have r2 : PolyT fun x => (List.range (bt x)).map fun i => offA (n x) (bq x) (bt x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) + 3 + 3 * i + 1 := outs_aux2 ha h3
  have r3 : PolyT fun x => (List.range (kbm x)).map fun i => Fw (n x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) (5 + i) :=
    PolyT.map (f := fun x i => Fw (n x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) (5 + i)) (by fun_prop) (PolyT.range h6)
  have r4 : PolyT fun x => (List.range (L x - (bq x + bt x + 2 + kbm x))).map fun _ => n x :=
    PolyT.map (f := fun x _ => n x) (by fun_prop) (PolyT.range (Unary.of_le h8 (by fun_prop) fun x => Nat.sub_le _ _))
  have r5 : PolyT fun x => [offA (n x) (bq x) (bt x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) + 3 + 3 * bt x] := outs_aux3 ha ht
  have r6 : PolyT fun x => [Fw (n x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) 4] := by fun_prop
  exact PolyT.append (PolyT.append (PolyT.append (PolyT.append (PolyT.append r1 r2) r5) r3) r4) r6

theorem coreB_polyT {n bq bt rb kbm Dq L P : α → ℕ} {tb : α → List TCl} (h1 : PolyT n) (h2 : Unary bq) (h3 : Unary bt) (h4 : Unary rb) (h6 : Unary kbm)
    (h7 : Unary Dq) (h5 : Unary L) (h8 : PolyT P) (h9 : PolyT tb) :
    PolyT fun x => coreB (n x) (bq x) (bt x) (rb x) (kbm x) (Dq x) (L x) (P x) (tb x) := by
  have hr := h4.poly
  have hd := h7.poly
  exact PolyT.prodMk (gatesC_polyT h1 h2 h3 h4 h6 h7 h8 h9)
    (PolyT.flatMap (f := fun x ι => outsL (n x) (bq x) (bt x) (rb x) (tb x).length (kbm x) (Dq x) (L x) ι)
      (outsL_polyT (by fun_prop) (h2.comp (h := Prod.fst) (by fun_prop)) (h3.comp (h := Prod.fst) (by fun_prop)) (by fun_prop) (by fun_prop)
        (h6.comp (h := Prod.fst) (by fun_prop)) (by fun_prop) (h5.comp (h := Prod.fst) (by fun_prop)) (by fun_prop)) (PolyT.const _))

@[fun_prop] theorem kb_polyT {e : α → MCode} (h : PolyT e) : PolyT fun x => kb (e x) := by unfold kb; fun_prop

@[fun_prop] theorem lam_polyT {e : α → MCode} (h : PolyT e) : PolyT fun x => lam (e x) := by unfold lam; fun_prop

@[fun_prop] theorem tab_polyT {e : α → MCode} (h : PolyT e) : PolyT fun x => tab (e x) := by unfold tab; fun_prop

@[fun_prop] theorem bt_polyT {e : α → MCode} {L : α → ℕ} (h : PolyT e) (hL : PolyT L) : PolyT fun x => bt (e x) (L x) := by unfold bt; fun_prop

@[fun_prop] theorem bq_polyT {e : α → MCode} {L : α → ℕ} (h : PolyT e) (hL : PolyT L) : PolyT fun x => bq (e x) (L x) := by unfold bq; fun_prop

theorem size_aux {f : α → ℕ} (h : PolyT f) : PolyT fun x => Nat.size (f x) := by fun_prop

@[fun_prop] theorem rb_polyT {e : α → MCode} (h : PolyT e) : PolyT fun x => rb (e x) := size_aux (f := fun x => (tab (e x)).length) (by fun_prop)

@[fun_prop] theorem nb_polyT {e : α → MCode} {L : α → ℕ} (h : PolyT e) (hL : PolyT L) : PolyT fun x => nb (e x) (L x) := by unfold nb; fun_prop

@[fun_prop] theorem dSum_polyT {tb : α → List TCl} (h : PolyT tb) : PolyT fun x => dSum (tb x) := by unfold dSum; fun_prop

theorem B_polyT : PolyT B := by
  have hL : Unary fun x : MCode × List Unit × ℕ => x.2.1.length := Unary.of_length (by fun_prop)
  have hl := hL.poly
  have hbq : Unary fun x : MCode × List Unit × ℕ => min (bq x.1 x.2.1.length) x.2.1.length := Unary.of_le hL (by fun_prop) fun x => min_le_right _ _
  have hbt : Unary fun x : MCode × List Unit × ℕ => bt x.1 x.2.1.length :=
    Unary.of_le hL (by fun_prop) fun x => by
      unfold bt
      exact (Nat.div_le_self _ _).trans (by omega)
  have hrb : Unary fun x : MCode × List Unit × ℕ => rb x.1 :=
    Unary.of_le (Unary.of_length (w := fun x : MCode × List Unit × ℕ => tab x.1) (by fun_prop)) (by fun_prop) fun x => Nat.size_le.2 Nat.lt_two_pow_self
  have hkb : Unary fun x : MCode × List Unit × ℕ => min (kb x.1) x.2.1.length := Unary.of_le hL (by fun_prop) fun x => min_le_right _ _
  have hs : PolyT fun x : MCode × List Unit × ℕ => Nat.size (dSum (tab x.1)) := size_aux (by fun_prop)
  have hq := hbq.poly
  have hDq : Unary fun x : MCode × List Unit × ℕ => min (Nat.size (dSum (tab x.1))) (min (bq x.1 x.2.1.length) x.2.1.length + 1) :=
    Unary.of_le (hbq.add (Unary.const 1)) (by fun_prop) fun x => min_le_right _ _
  exact coreB_polyT (by fun_prop) hbq hbt hrb hkb hDq hL (by fun_prop) (by fun_prop)

end poly

/-! ### The statement -/

theorem pick3 (f : ℕ → List ℕ) {k : ℕ} (hf : ∀ i, (f i).length = k) {i : ℕ} (hi : i < 3) :
    ∃ rest, ((List.range 3).flatMap f).drop (i * k) = f i ++ rest := by
  have e : (List.range 3).flatMap f = f 0 ++ (f 1 ++ (f 2 ++ [])) := rfl
  rw [e]
  interval_cases i
  · exact ⟨f 1 ++ (f 2 ++ []), by simp⟩
  · exact ⟨_, by rw [Nat.one_mul]; exact List.drop_left' (hf 0)⟩
  · refine ⟨[], ?_⟩
    rw [← List.append_assoc]
    exact List.drop_left' (by rw [List.length_append, hf 0, hf 1]; omega)

theorem le_sum_map {α : Type} (f : α → ℕ) (l : List α) {c : α} (hc : c ∈ l) : f c ≤ (l.map f).sum := by
  induction l with
  | nil => simp at hc
  | cons d l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hc with rfl | h
    · omega
    · have := ih h
      omega

/-- No number that the table adds to a position is larger than `dSum`. -/
theorem dq_le_dSum (tb : List TCl) (k ι : ℕ) : (litI (tb.getD k zeroCl) ι).2.2.2.1 ≤ dSum tb := by
  by_cases hk : k < tb.length
  · rw [List.getD_eq_getElem _ _ hk]
    refine le_trans ?_ (le_sum_map (fun c : TCl => c.1.2.2.2.1 + c.2.1.2.2.2.1 + c.2.2.2.2.2.1) tb (List.getElem_mem hk))
    unfold litI
    split_ifs <;> omega
  · rw [List.getD_eq_default _ _ (by omega), litI_zeroCl]
    exact Nat.zero_le _

end CircuitLowerBound.Clause

namespace CircuitLowerBound

open ENP Groundwork CircuitLowerBound.Blocks CircuitLowerBound.Clause

/-- The circuit that computes clause number j of the formula of a table from the bits of j has at
most 36·(L+1) gates and a number of gates that depends on the table only. -/
theorem stClauseCirc : StClauseCirc := by
  refine ⟨36, fun e => 2 + rb e * (tab e).length + (tab e).length * (3 * (5 + kb e + Nat.size (dSum (tab e)))), B, B_polyT, fun e L P hF => ?_⟩
  obtain ⟨h1, h2⟩ := hF
  have hbt2 : 2 * bt e L ≤ L - kb e - lam e - 2 := by unfold bt; omega
  have hbt1 : 1 ≤ bt e L := by
    by_contra h
    have h0 : bt e L = 0 := by omega
    rw [h0] at h2
    simp at h2
  have hbq : bq e L = bt e L + lam e := rfl
  have hn : nb e L = rb e + bt e L + bq e L := rfl
  have hL' : bq e L + bt e L + 2 + kb e ≤ L := by omega
  have hR : (tab e).length < 2 ^ rb e := Nat.lt_size_self _
  have hB : B (e, List.replicate L (), P) =
      coreB (nb e L) (bq e L) (bt e L) (rb e) (kb e) (min (Nat.size (dSum (tab e))) (bq e L + 1)) L P (tab e) := by
    simp only [B, List.length_replicate]
    rw [min_eq_left (by omega : bq e L ≤ L), min_eq_left (by omega : kb e ≤ L)]
  rw [hB]
  simp only [coreB]
  obtain ⟨Dq, hDq⟩ : ∃ Dq, Dq = min (Nat.size (dSum (tab e))) (bq e L + 1) := ⟨_, rfl⟩
  rw [← hDq]
  have hD : ∀ k ι i, Dq ≤ i → i < bq e L + 1 → (litI ((tab e).getD k zeroCl) ι).2.2.2.1.testBit i = false := by
    intro k ι i hi1 hi2
    have hs : Nat.size (dSum (tab e)) ≤ i := by omega
    exact Nat.testBit_eq_false_of_lt (lt_of_le_of_lt (dq_le_dSum (tab e) k ι) ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by norm_num) hs)))
  have hlen := length_gatesC (nb e L) (bq e L) (bt e L) (rb e) (kb e) Dq P (tab e)
  have hol := length_outsL hL' (nb e L) (rb e) (tab e).length Dq
  refine ⟨wf_of_wfa (wfa_gatesC (by omega) (by omega) _ _ _ _), ?_, ?_, ?_, ?_⟩
  · rw [hlen]
    have g1 : (tab e).length * (3 * (5 + kb e + Dq)) ≤ (tab e).length * (3 * (5 + kb e + Nat.size (dSum (tab e)))) :=
      Nat.mul_le_mul_left _ (by omega)
    unfold szL
    omega
  · rw [length_flatMap_const _ hol 3]
    omega
  · intro w hw
    obtain ⟨ι, hι, hw⟩ := List.mem_flatMap.1 hw
    rw [hlen]
    exact outsL_lt _ _ _ _ _ _ _ _ (List.mem_range.1 hι) w hw
  · intro j hj i hi
    obtain ⟨rest, hr⟩ := pick3 (outsL (nb e L) (bq e L) (bt e L) (rb e) (tab e).length (kb e) Dq L) hol hi
    obtain ⟨c1, c2⟩ := core_val hn hbt1 hR hL' hD hj hi _ rfl _ rfl (P := P)
    have hg : ((List.range 3).flatMap (outsL (nb e L) (bq e L) (bt e L) (rb e) (tab e).length (kb e) Dq L)).getD (i * (L + 1) + L) 0 =
        (outsL (nb e L) (bq e L) (bt e L) (rb e) (tab e).length (kb e) Dq L i).getD L 0 := by
      have e1 : ((List.range 3).flatMap (outsL (nb e L) (bq e L) (bt e L) (rb e) (tab e).length (kb e) Dq L)).getD (i * (L + 1) + L) 0 =
          (((List.range 3).flatMap (outsL (nb e L) (bq e L) (bt e L) (rb e) (tab e).length (kb e) Dq L)).drop (i * (L + 1))).getD L 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
      rw [e1, hr, List.getD_append _ _ _ _ (by rw [hol]; omega)]
    rw [hr, List.take_append_of_le_length (by rw [hol]; omega), hg]
    have hcl : (clauseAt e L P j).getD i (0, false) =
        litAt e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) (litI ((tab e).getD (j / 2 ^ (bt e L + bq e L)) zeroCl) i) := by
      interval_cases i <;> rfl
    rw [hcl, litAt, vidx]
    exact Prod.ext c1 c2

end CircuitLowerBound
