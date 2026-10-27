/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.CertLib

/-! # Polynomial-time certificates for one decision of the choice of the checks

One decision compares two integers, the numerators of the truncated potential in the two states that
are tried (`Par.num`, proof/rates/ClauseBound/ParityChecks/RunDefs.lean). All their exponents are
numbers given in unary: the parameters m, nb, r, i₀, β, lengths of lists, and the number e of
clauses decided. So the integers have polynomially many bits and are computed in polynomial time.
The parameters
are never data: every certificate is stated for a function q of the context with `QU q`. For each
numerator there is an auxiliary lemma with generic functions in place of the components of q.
The result is `decide1_polyT`. -/

public section

namespace ClauseBound.ParityChecks.CertNum

open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib

variable {α : Type} [Enc α]

/-! ### The number of checks that contain a clause -/

/-- The number of checks among Ls and cur that contain the clause x is polynomial-time. -/
@[fun_prop] theorem colOf_polyT {Ls : α → List Chk} {cur : α → Chk} {x : α → ℕ} (hL : PolyT Ls) (hc : PolyT cur) (hx : PolyT x) :
    PolyT fun a => Par.colOf (Ls a) (cur a) (x a) := by
  unfold Par.colOf
  fun_prop

/-- It is given in unary: it is at most the number of the checks. -/
@[fun_prop] theorem colOf_unary {Ls : α → List Chk} {cur : α → Chk} {x : α → ℕ} (hL : PolyT Ls) (hc : PolyT cur) (hx : PolyT x) :
    Unary fun a => Par.colOf (Ls a) (cur a) (x a) := by
  refine Unary.of_le (g := fun a => (Ls a).length + 1) (by fun_prop) (colOf_polyT hL hc hx) fun a => ?_
  unfold Par.colOf
  have h1 := List.countP_le_length (p := fun L => decide (x a ∈ L)) (l := Ls a)
  split_ifs <;> omega

/-! ### The four numerators -/

theorem numP_aux {nb i₀ : α → ℕ} {A : α → ℤ} {B : α → ℕ → ℤ} (hnb : Unary nb) (hi : Unary i₀) (hA : PolyT A) (hB : PolyT fun p : α × ℕ => B p.1 p.2) :
    PolyT fun x => A x * (nb x : ℤ) ^ i₀ x + ((List.range (i₀ x + 1)).map fun i => (-2 : ℤ) ^ i * (nb x : ℤ) ^ (i₀ x - i) * B x i).sum := by
  have hn1 : Unary fun x => i₀ x + 1 := hi.add (Unary.const 1)
  have hmin : Unary fun p : α × ℕ => min p.2 (i₀ p.1 + 1) := CertLib.unary_min_right PolyT.id'.snd (hn1.comp PolyT.id'.fst)
  have hB' : PolyT fun p : α × ℕ => B p.1 (min p.2 (i₀ p.1 + 1)) :=
    PolyT.comp (g := fun p : α × ℕ => (p.1, min p.2 (i₀ p.1 + 1))) hB (PolyT.prodMk PolyT.id'.fst hmin.poly)
  have hnbZ : PolyT fun p : α × ℕ => (nb p.1 : ℤ) := PolyT.natCast (PolyT.comp hnb.poly PolyT.id'.fst)
  have h1 : PolyT fun p : α × ℕ => (-2 : ℤ) ^ min p.2 (i₀ p.1 + 1) * (nb p.1 : ℤ) ^ (i₀ p.1 - min p.2 (i₀ p.1 + 1)) * B p.1 (min p.2 (i₀ p.1 + 1)) :=
    PolyT.mulZ (PolyT.mulZ (powZ_polyT (PolyT.const (-2)) hmin) (powZ_polyT hnbZ (unary_sub (hi.comp PolyT.id'.fst) hmin.poly))) hB'
  have h2 : PolyT fun x => (List.range (i₀ x + 1)).map fun i => (-2 : ℤ) ^ i * (nb x : ℤ) ^ (i₀ x - i) * B x i :=
    map_range_polyT (f := fun x i => (-2 : ℤ) ^ i * (nb x : ℤ) ^ (i₀ x - i) * B x i) hn1 h1
  exact PolyT.addZ (PolyT.mulZ hA (powZ_polyT (PolyT.natCast hnb.poly) hi)) (sumZ_polyT h2)

/-- A·nb^{i₀} + Σ_{i ≤ i₀} (−2)^i·nb^{i₀−i}·B_i is polynomial-time. -/
theorem numP_polyT {q : α → Par} (hq : QU q) {A : α → ℤ} {B : α → ℕ → ℤ} (hA : PolyT A) (hB : PolyT fun p : α × ℕ => B p.1 p.2) :
    PolyT fun x => (q x).numP (A x) (B x) := by
  unfold Par.numP
  exact numP_aux hq.nb hq.i₀ hA hB

theorem numI_aux {m nb r : α → ℕ} {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hm : Unary m) (hnb : Unary nb) (hr : Unary r) (hL : PolyT Ls)
    (hc : PolyT cur) (he : PolyT e) :
    PolyT fun x => (((Ls x).map List.length).sum + (cur x).length) * nb x + ((m x - e x) + (r x - 1 - (Ls x).length) * m x) := by
  have := hm.poly
  have := hnb.poly
  have := hr.poly
  fun_prop

/-- I·nb + (number of undecided pairs) is polynomial-time. -/
theorem numI_polyT {q : α → Par} (hq : QU q) {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hL : PolyT Ls) (hc : PolyT cur) (he : PolyT e) :
    PolyT fun x => (q x).numI (Ls x) (cur x) (e x) := by
  unfold Par.numI Par.k
  exact numI_aux hq.m hq.nb hq.r hL hc he

theorem numR_aux {m nb r : α → ℕ} {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hm : Unary m) (hnb : Unary nb) (hr : Unary r) (hL : PolyT Ls)
    (hc : PolyT cur) (he : Unary e) :
    PolyT fun x => ((Ls x).map fun L => 2 ^ L.length * nb x ^ m x).sum + 2 ^ (cur x).length * nb x ^ e x * (nb x + 1) ^ (m x - e x) +
      (r x - 1 - (Ls x).length) * (nb x + 1) ^ m x := by
  have hn1 : PolyT fun x => nb x + 1 := PolyT.add hnb.poly (PolyT.const 1)
  have h1 : PolyT fun p : α × Chk => 2 ^ p.2.length * nb p.1 ^ m p.1 :=
    PolyT.mul (PolyT.pow_unary (PolyT.const 2) (Unary.of_length PolyT.id'.snd))
      (PolyT.pow_unary (PolyT.comp hnb.poly PolyT.id'.fst) (hm.comp PolyT.id'.fst))
  have h2 : PolyT fun x => (Ls x).map fun L => 2 ^ L.length * nb x ^ m x := PolyT.map h1 hL
  have t2 : PolyT fun x => 2 ^ (cur x).length * nb x ^ e x * (nb x + 1) ^ (m x - e x) :=
    PolyT.mul (PolyT.mul (PolyT.pow_unary (PolyT.const 2) (Unary.of_length hc)) (PolyT.pow_unary hnb.poly he)) (PolyT.pow_unary hn1 (unary_sub hm he.poly))
  have t3 : PolyT fun x => (r x - 1 - (Ls x).length) * (nb x + 1) ^ m x :=
    PolyT.mul (PolyT.sub (PolyT.sub hr.poly (PolyT.const 1)) (PolyT.length hL)) (PolyT.pow_unary hn1 hm)
  exact PolyT.add (PolyT.add (PolyT.sum h2) t2) t3

/-- The numerator of the term that sums over the checks (`Par.numR`), with 2 to the size of each
check, is polynomial-time, for e in unary. -/
theorem numR_polyT {q : α → Par} (hq : QU q) {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hL : PolyT Ls) (hc : PolyT cur) (he : Unary e) :
    PolyT fun x => (q x).numR (Ls x) (cur x) (e x) := by
  unfold Par.numR Par.k
  exact numR_aux hq.m hq.nb hq.r hL hc he

theorem numC_aux {m nb r : α → ℕ} {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hm : Unary m) (hnb : Unary nb) (hr : Unary r) (hL : PolyT Ls)
    (hc : PolyT cur) (he : PolyT e) :
    PolyT fun a => ((List.range (m a)).map fun x =>
      2 ^ Par.colOf (Ls a) (cur a) x * nb a ^ ((Ls a).length + if x < e a then 1 else 0) *
        (nb a + 1) ^ (r a - ((Ls a).length + if x < e a then 1 else 0))).sum := by
  have h0 : Unary fun p : α × ℕ => (Ls p.1).length + if p.2 < e p.1 then 1 else 0 :=
    (Unary.of_length (PolyT.comp hL PolyT.id'.fst)).add
      (unary_ite (PolyT.decide_lt PolyT.id'.snd (PolyT.comp he PolyT.id'.fst)) (Unary.const 1) (Unary.const 0))
  have hnb' : PolyT fun p : α × ℕ => nb p.1 := PolyT.comp hnb.poly PolyT.id'.fst
  have h1 : PolyT fun p : α × ℕ => 2 ^ Par.colOf (Ls p.1) (cur p.1) p.2 * nb p.1 ^ ((Ls p.1).length + if p.2 < e p.1 then 1 else 0) *
      (nb p.1 + 1) ^ (r p.1 - ((Ls p.1).length + if p.2 < e p.1 then 1 else 0)) :=
    PolyT.mul (PolyT.mul (PolyT.pow_unary (PolyT.const 2) (colOf_unary (PolyT.comp hL PolyT.id'.fst) (PolyT.comp hc PolyT.id'.fst) PolyT.id'.snd))
      (PolyT.pow_unary hnb' h0)) (PolyT.pow_unary (PolyT.add hnb' (PolyT.const 1)) (unary_sub (hr.comp PolyT.id'.fst) h0.poly))
  have h2 : PolyT fun a => (List.range (m a)).map fun x =>
      2 ^ Par.colOf (Ls a) (cur a) x * nb a ^ ((Ls a).length + if x < e a then 1 else 0) *
        (nb a + 1) ^ (r a - ((Ls a).length + if x < e a then 1 else 0)) := PolyT.map h1 (PolyT.range hm)
  exact PolyT.sum h2

/-- The numerator of the term that sums over the clauses (`Par.numC`), with 2 to the number of
checks that contain each clause, is polynomial-time. -/
theorem numC_polyT {q : α → Par} (hq : QU q) {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hL : PolyT Ls) (hc : PolyT cur) (he : PolyT e) :
    PolyT fun x => (q x).numC (Ls x) (cur x) (e x) := by
  unfold Par.numC
  exact numC_aux hq.m hq.nb hq.r hL hc he

/-! ### The numerator of the truncated potential -/

theorem num_aux {m nb r i₀ j nI nR nC : α → ℕ} {nP : α → ℤ} (hm : Unary m) (hnb : Unary nb) (hr : Unary r) (hi : Unary i₀) (hj : PolyT j) (hP : PolyT nP)
    (hI : PolyT nI) (hR : PolyT nR) (hC : PolyT nC) :
    PolyT fun x => (5 : ℤ) ^ (r x - 1 - j x) * nP x * ((8 * m x * r x * (nb x + 1) ^ (m x + r x) : ℕ) : ℤ) +
      ((nI x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * (nb x + 1) ^ (m x + r x)) +
        nR x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * m x * (nb x + 1) ^ r x) +
        nC x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * r x * (nb x + 1) ^ m x) : ℕ) : ℤ) := by
  have hk : Unary fun x => r x - 1 - j x := unary_sub (unary_sub hr (PolyT.const 1)) hj
  have hn1 : PolyT fun x => nb x + 1 := PolyT.add hnb.poly (PolyT.const 1)
  have h5 : PolyT fun x => (5 : ℤ) ^ (r x - 1 - j x) := powZ_polyT (PolyT.const 5) hk
  have h8 : PolyT fun x => 8 ^ (r x - 1 - j x) := PolyT.pow_unary (PolyT.const 8) hk
  have hni : PolyT fun x => nb x ^ i₀ x := PolyT.pow_unary hnb.poly hi
  have hmr : PolyT fun x => (nb x + 1) ^ (m x + r x) := PolyT.pow_unary hn1 (hm.add hr)
  have hnr : PolyT fun x => (nb x + 1) ^ r x := PolyT.pow_unary hn1 hr
  have hnm : PolyT fun x => (nb x + 1) ^ m x := PolyT.pow_unary hn1 hm
  have c0 : PolyT fun x => 2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x := PolyT.mul (PolyT.mul (PolyT.const 2) h8) hni
  have a1 : PolyT fun x => 8 * m x * r x * (nb x + 1) ^ (m x + r x) := PolyT.mul (PolyT.mul (PolyT.mul (PolyT.const 8) hm.poly) hr.poly) hmr
  have a2 : PolyT fun x => nI x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * (nb x + 1) ^ (m x + r x)) +
        nR x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * m x * (nb x + 1) ^ r x) +
        nC x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * r x * (nb x + 1) ^ m x) :=
    PolyT.add (PolyT.add (PolyT.mul hI (PolyT.mul c0 hmr)) (PolyT.mul hR (PolyT.mul (PolyT.mul c0 hm.poly) hnr)))
      (PolyT.mul hC (PolyT.mul (PolyT.mul c0 hr.poly) hnm))
  exact PolyT.addZ (PolyT.mulZ (PolyT.mulZ h5 hP) (PolyT.natCast a1)) (PolyT.natCast a2)

/-- The numerator of the truncated potential is polynomial-time, for e in unary. -/
theorem num_polyT {q : α → Par} (hq : QU q) {A : α → ℤ} {B : α → ℕ → ℤ} {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hA : PolyT A)
    (hB : PolyT fun p : α × ℕ => B p.1 p.2) (hL : PolyT Ls) (hc : PolyT cur) (he : Unary e) :
    PolyT fun x => (q x).num (A x) (B x) (Ls x) (cur x) (e x) := by
  unfold Par.num Par.k
  exact num_aux hq.m hq.nb hq.r hq.i₀ (PolyT.length hL) (numP_polyT hq hA hB) (numI_polyT hq hL hc he.poly) (numR_polyT hq hL hc he)
    (numC_polyT hq hL hc he.poly)

/-! ### Residues, the numerator with A and the B_i from the given functions `orcA` and `orcB`, one decision -/

/-- The representative of a modulo 2^β in [−2^{β−1}, 2^{β−1}) is polynomial-time, for β in unary. -/
theorem bal_polyT {β : α → ℕ} {a : α → ℤ} (hβ : Unary β) (ha : PolyT a) : PolyT fun x => bal (β x) (a x) := by
  unfold bal
  have h1 : PolyT fun x => (2 : ℤ) ^ (β x - 1) := powZ_polyT (PolyT.const 2) (unary_sub hβ (PolyT.const 1))
  exact PolyT.subZ (mod_two_pow_polyT (PolyT.addZ ha h1) hβ) h1

/-- The numerator with A and the B_i taken as the representatives modulo 2^β (`bal`) of the values
of the given functions `orcA` and `orcB` is polynomial-time, for e in unary. -/
theorem numO_polyT {q : α → Par} (hq : QU q) {orcA : α → List Chk → ℤ} {orcB : α → List Chk → Chk → ℕ → ℕ → ℤ} {Ls : α → List Chk} {cur : α → Chk}
    {e : α → ℕ} (hA : PolyT fun p : α × List Chk => orcA p.1 p.2)
    (hB : PolyT fun p : α × List Chk × Chk × ℕ × ℕ => orcB p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) (hL : PolyT Ls) (hc : PolyT cur) (he : Unary e) :
    PolyT fun x => (q x).numO (orcA x) (orcB x) (Ls x) (cur x) (e x) := by
  unfold Par.numO
  have he' := he.poly
  have h1 : PolyT fun x => orcA x (Ls x) := PolyT.comp (g := fun x => (x, Ls x)) hA (by fun_prop)
  have h2 : PolyT fun p : α × ℕ => orcB p.1 (Ls p.1) (cur p.1) (e p.1) p.2 :=
    PolyT.comp (g := fun p : α × ℕ => (p.1, Ls p.1, cur p.1, e p.1, p.2)) hB (by fun_prop)
  exact num_polyT hq (bal_polyT hq.β h1) (bal_polyT (β := fun p : α × ℕ => (q p.1).β) (hq.β.comp PolyT.id'.fst) h2) hL hc he

/-- One decision is polynomial-time, for e in unary. -/
theorem decide1_polyT {q : α → Par} (hq : QU q) {orcA : α → List Chk → ℤ} {orcB : α → List Chk → Chk → ℕ → ℕ → ℤ} {Ls : α → List Chk} {cur : α → Chk}
    {e : α → ℕ} (hA : PolyT fun p : α × List Chk => orcA p.1 p.2)
    (hB : PolyT fun p : α × List Chk × Chk × ℕ × ℕ => orcB p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) (hL : PolyT Ls) (hc : PolyT cur) (he : Unary e) :
    PolyT fun x => (q x).decide1 (orcA x) (orcB x) (Ls x) (cur x) (e x) := by
  unfold Par.decide1
  have he' := he.poly
  have hc1 : PolyT fun x => cur x ++ [e x] := by fun_prop
  have he1 : Unary fun x => e x + 1 := by fun_prop
  exact PolyT.ite' (PolyT.decide_leZ (numO_polyT hq hA hB hL hc1 he1) (numO_polyT hq hA hB hL hc he1)) hc1 hc

end ClauseBound.ParityChecks.CertNum
