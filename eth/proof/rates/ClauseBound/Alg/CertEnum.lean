/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Interfaces
public import PaddedDescent.F.CertNet
public import ToTuring.Poly.Digits
public import ToTuring.Poly.Words

/-! # Certificates: evaluation of a network by enumeration, and brute force with the number of nodes as data

Polynomial time (`PolyT`) in the pad and the data for

* `enumF`, the evaluation of a network on g nodes by enumeration of all labels, with g given in
  unary (`stCertEnum`);
* `bruteF`, brute force on K nodes, with K given in unary (`stCertBruteK`).

In `enumF` the label of the nodes a, b is the chunk number min a b · g + max a b of a word. The
position of a chunk is a sum over all earlier chunks, so its number has
to be given in unary; the loops only use numbers below g·g, and the certificate is proved for the
function in which the number of earlier chunks is cut off at g·g. -/

public section

namespace ClauseBound.Alg.CertEnum

open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertNet

variable {α : Type} [Enc α] {C : Type} [Enc C] {F : FNet C}

/-! ### Products that agree on the range of the loop -/

/-- A product over y < n only depends on the factors with y < n. -/
theorem prodL_congr {n : ℕ} {f f' : ℕ → ℤ} (h : ∀ y < n, f y = f' y) : prodL n f = prodL n f' := by
  rw [prodL_eq, prodL_eq]
  exact Finset.prod_congr rfl fun y hy => h y (Finset.mem_range.1 hy)

/-! ### The lengths of the chunks -/

/-- The length of a chunk is given in unary. -/
theorem enumLen_unary (hF : FKeeps F) {g j : α → ℕ} {c : α → C} (hg : PolyT g) (hc : PolyT c) (hj : PolyT j) :
    Unary fun t => enumLen (g t) F (c t) (j t) := by
  have h := keepsU hF
  have hd : PolyT fun t => j t / g t := PolyT.div hj hg
  have hm : PolyT fun t => j t % g t := PolyT.mod hj hg
  have hU : Unary fun t => F.toP.cap (c t) (j t / g t) (j t % g t) := capU h hc hd hm
  have hP := hU.poly
  refine Unary.of_le hU ?_ fun t => ?_
  · unfold enumLen
    change PolyT fun t => if j t / g t < j t % g t then F.toP.cap (c t) (j t / g t) (j t % g t) else 0
    fun_prop
  · unfold enumLen
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _

/-- The number of bits of the word of all labels is given in unary. -/
theorem enumBits_unary (hF : FKeeps F) {g : α → ℕ} {c : α → C} (hg : Unary g) (hc : PolyT c) :
    Unary fun t => enumBits (g t) F (c t) := by
  have hgp := hg.poly
  have h1 : Unary fun p : α × ℕ => enumLen (g p.1) F (c p.1) p.2 := enumLen_unary hF (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : Unary fun t => ((List.range (g t * g t)).map (enumLen (g t) F (c t))).sum :=
    unary_sum_map (f := fun t j => enumLen (g t) F (c t) j) h1 (by fun_prop)
  simpa only [enumBits, sum_range_eq_list] using h2

/-! ### The chunks -/

/-- The chunk number j, with the number of earlier chunks cut off at g·g. -/
def chunkCut (g : ℕ) (F : FNet C) (c : C) (j : ℕ) (w : List Bool) : List Bool :=
  (w.drop ((List.range (min j (g * g))).map (enumLen g F c)).sum).take (enumLen g F c j)

omit [Enc C] in
/-- Below g·g the cut-off does nothing. -/
theorem chunkCut_eq {g : ℕ} (F : FNet C) (c : C) {j : ℕ} (hj : j ≤ g * g) (w : List Bool) :
    chunkCut g F c j w = chunkAt (enumLen g F c) j w := by
  rw [chunkCut, chunkAt, min_eq_left hj, sum_range_eq_list]

/-- The number of the chunk of two nodes below g is below g·g. -/
theorem pair_le {g a b : ℕ} (ha : a < g) (hb : b < g) : min a b * g + max a b ≤ g * g := by
  have h1 : min a b + 1 ≤ g := by omega
  have h2 : max a b ≤ g := by omega
  calc min a b * g + max a b ≤ min a b * g + g := Nat.add_le_add_left h2 _
    _ = (min a b + 1) * g := by ring
    _ ≤ g * g := Nat.mul_le_mul_right _ h1

/-- A chunk, cut off, is polynomial-time. -/
theorem chunkCut_polyT (hF : FKeeps F) {g j : α → ℕ} {c : α → C} {w : α → List Bool} (hg : Unary g) (hc : PolyT c) (hj : PolyT j)
    (hw : PolyT w) : PolyT fun t => chunkCut (g t) F (c t) (j t) (w t) := by
  have hgp := hg.poly
  have h0 : Unary fun t => min (j t) (g t * g t) := Unary.of_le (hg.mul hg) (by fun_prop) fun t => Nat.min_le_right _ _
  have h1 : Unary fun p : α × ℕ => enumLen (g p.1) F (c p.1) p.2 := enumLen_unary hF (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : PolyT fun t => ((List.range (min (j t) (g t * g t))).map (enumLen (g t) F (c t))).sum :=
    (unary_sum_map (f := fun t j => enumLen (g t) F (c t) j) h1 (by fun_prop)).poly
  have h3 : PolyT fun t => enumLen (g t) F (c t) (j t) := (enumLen_unary hF hgp hc hj).poly
  unfold chunkCut
  fun_prop

/-! ### Enumeration -/

/-- `enumF` with the chunks cut off. -/
def enumCut (pad : U) (g : ℕ) (F : FNet C) (c : C) : ℤ :=
  sumF (2 ^ enumBits g F c) pad fun t =>
    prodL g fun a => sumF (2 ^ F.n c a) pad fun zi =>
      F.W (c, (a, toWord (F.n c a) zi)) * prodL g fun b =>
        if b = a then 1
        else F.f (c, ((a, b), (toWord (F.n c a) zi, chunkCut g F c (min a b * g + max a b) (toWord (enumBits g F c) t))))

omit [Enc C] in
/-- The cut-off does not change the value. -/
theorem enumCut_eq (pad : U) (g : ℕ) (F : FNet C) (c : C) : enumCut pad g F c = enumF pad g F c := by
  unfold enumCut enumF
  congr 1
  funext t
  refine prodL_congr fun a ha => ?_
  congr 1
  funext zi
  congr 1
  refine prodL_congr fun b hb => ?_
  rw [chunkCut_eq F c (pair_le ha hb)]

/-- Evaluation by enumeration is polynomial-time in the pad, g in unary and the context. -/
theorem enumF_polyT (hF : FKeeps F) {pad : α → U} {g : α → ℕ} {c : α → C} (hp : PolyT pad) (hg : Unary g) (hc : PolyT c) :
    PolyT fun t => enumF (pad t) (g t) F (c t) := by
  have h := keepsU hF
  have hW := hF.W
  have hf := hF.f
  have hgp := hg.poly
  have hB : Unary fun t => enumBits (g t) F (c t) := enumBits_unary hF hg hc
  have hn : Unary fun p : α × ℕ => F.n (c p.1) p.2 := nU h (c := fun p : α × ℕ => c p.1) (a := fun p => p.2) (by fun_prop) (by fun_prop)
  -- the state word of the node a
  have hz : PolyT fun q : α × ℕ × ℕ => toWord (F.n (c q.1) q.2.1) q.2.2 :=
    PolyT.toWord' (hn.comp (h := fun q : α × ℕ × ℕ => (q.1, q.2.1)) (by fun_prop)) (by fun_prop)
  -- the argument is ((((x, t), a), zi), b): input, number of the word of all labels, node, number
  -- of its state, second node
  have hch : PolyT fun q : (((α × ℕ) × ℕ) × ℕ) × ℕ =>
      chunkCut (g q.1.1.1.1) F (c q.1.1.1.1) (min q.1.1.2 q.2 * g q.1.1.1.1 + max q.1.1.2 q.2)
        (toWord (enumBits (g q.1.1.1.1) F (c q.1.1.1.1)) q.1.1.1.2) :=
    chunkCut_polyT hF (by fun_prop) (by fun_prop) (by fun_prop)
      (PolyT.toWord' (hB.comp (h := fun q : (((α × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.1) (by fun_prop)) (by fun_prop))
  have hz4 : PolyT fun q : (((α × ℕ) × ℕ) × ℕ) × ℕ => toWord (F.n (c q.1.1.1.1) q.1.1.2) q.1.2 :=
    PolyT.comp (g := fun q : (((α × ℕ) × ℕ) × ℕ) × ℕ => (q.1.1.1.1, q.1.1.2, q.1.2)) hz (by fun_prop)
  have h1 : PolyT fun q : (((α × ℕ) × ℕ) × ℕ) × ℕ =>
      if q.2 = q.1.1.2 then (1 : ℤ)
      else F.f (c q.1.1.1.1, ((q.1.1.2, q.2), (toWord (F.n (c q.1.1.1.1) q.1.1.2) q.1.2,
        chunkCut (g q.1.1.1.1) F (c q.1.1.1.1) (min q.1.1.2 q.2 * g q.1.1.1.1 + max q.1.1.2 q.2)
          (toWord (enumBits (g q.1.1.1.1) F (c q.1.1.1.1)) q.1.1.1.2)))) := by
    fun_prop
  have h2 : PolyT fun q : ((α × ℕ) × ℕ) × ℕ =>
      F.W (c q.1.1.1, (q.1.2, toWord (F.n (c q.1.1.1) q.1.2) q.2)) * prodL (g q.1.1.1) fun b =>
        if b = q.1.2 then (1 : ℤ)
        else F.f (c q.1.1.1, ((q.1.2, b), (toWord (F.n (c q.1.1.1) q.1.2) q.2,
          chunkCut (g q.1.1.1) F (c q.1.1.1) (min q.1.2 b * g q.1.1.1 + max q.1.2 b)
            (toWord (enumBits (g q.1.1.1) F (c q.1.1.1)) q.1.1.2)))) := by
    refine PolyT.mulZ (PolyT.comp hW ?_) (prodL_polyT (by fun_prop) h1)
    have : PolyT fun q : ((α × ℕ) × ℕ) × ℕ => toWord (F.n (c q.1.1.1) q.1.2) q.2 :=
      PolyT.comp (g := fun q : ((α × ℕ) × ℕ) × ℕ => (q.1.1.1, q.1.2, q.2)) hz (by fun_prop)
    fun_prop
  have h3 : PolyT fun q : (α × ℕ) × ℕ => sumF (2 ^ F.n (c q.1.1) q.2) (pad q.1.1) fun zi =>
      F.W (c q.1.1, (q.2, toWord (F.n (c q.1.1) q.2) zi)) * prodL (g q.1.1) fun b =>
        if b = q.2 then (1 : ℤ)
        else F.f (c q.1.1, ((q.2, b), (toWord (F.n (c q.1.1) q.2) zi,
          chunkCut (g q.1.1) F (c q.1.1) (min q.2 b * g q.1.1 + max q.2 b) (toWord (enumBits (g q.1.1) F (c q.1.1)) q.1.2)))) :=
    sumF_polyT (PolyT.pow_unary (by fun_prop) (hn.comp (h := fun q : (α × ℕ) × ℕ => (q.1.1, q.2)) (by fun_prop))) (by fun_prop) h2
  have h4 : PolyT fun q : α × ℕ => prodL (g q.1) fun a => sumF (2 ^ F.n (c q.1) a) (pad q.1) fun zi =>
      F.W (c q.1, (a, toWord (F.n (c q.1) a) zi)) * prodL (g q.1) fun b =>
        if b = a then (1 : ℤ)
        else F.f (c q.1, ((a, b), (toWord (F.n (c q.1) a) zi,
          chunkCut (g q.1) F (c q.1) (min a b * g q.1 + max a b) (toWord (enumBits (g q.1) F (c q.1)) q.2)))) :=
    prodL_polyT (by fun_prop) h3
  have h5 : PolyT fun t => enumCut (pad t) (g t) F (c t) := sumF_polyT (PolyT.pow_unary (by fun_prop) hB) hp h4
  exact h5.congr fun t => enumCut_eq _ _ _ _

/-- Evaluation of a network by enumeration is polynomial-time. -/
theorem stCertEnum : StCertEnum := fun _ _ _ hF _ _ _ _ _ hp hg hc => enumF_polyT hF hp hg hc

/-! ### Brute force -/

/-- The query at the node v, with the number K of nodes in unary. -/
theorem query0_polyT' {K ℓ v : α → ℕ} {d w : α → List Bool} (hK : Unary K) (h1 : PolyT ℓ) (h2 : PolyT d) (h3 : PolyT w) (h4 : PolyT v) :
    PolyT fun x => query0 (K x) (ℓ x) (d x) (w x) (v x) := by
  unfold query0; fun_prop

/-- Brute force on K nodes, K in unary. -/
theorem bruteF_polyT {pad : α → U} {K : α → ℕ} {I : α → PInst} (hp : PolyT pad) (hK : Unary K) (hI : PolyT I) :
    PolyT fun x => bruteF (pad x) (K x) (I x) := by
  have hKp := hK.poly
  have hb : Unary fun x => K x * (K x - 1) / 2 * (I x).1.length := by fun_prop
  have hw : PolyT fun p : (α × ℕ) × ℕ => toWord (K p.1.1 * (K p.1.1 - 1) / 2 * (I p.1.1).1.length) p.1.2 :=
    PolyT.toWord' (hb.comp (h := fun p : (α × ℕ) × ℕ => p.1.1) (by fun_prop)) (by fun_prop)
  have hq : PolyT fun p : (α × ℕ) × ℕ => look (I p.1.1).2
      (query0 (K p.1.1) (I p.1.1).1.length [] (toWord (K p.1.1 * (K p.1.1 - 1) / 2 * (I p.1.1).1.length) p.1.2) p.2) :=
    look_polyT (by fun_prop) (query0_polyT' (by fun_prop) (by fun_prop) (by fun_prop) hw (by fun_prop))
  have hin : PolyT fun p : α × ℕ => prodL (K p.1) fun v => look (I p.1).2
      (query0 (K p.1) (I p.1).1.length [] (toWord (K p.1 * (K p.1 - 1) / 2 * (I p.1).1.length) p.2) v) :=
    prodL_polyT (by fun_prop) hq
  exact sumF_polyT (PolyT.pow_unary (by fun_prop) hb) hp hin

/-- Brute force is polynomial-time in the pad, the number of nodes in unary and the instance. -/
theorem stCertBruteK : StCertBruteK := bruteF_polyT (by fun_prop) (by fun_prop) (by fun_prop)

end ClauseBound.Alg.CertEnum
