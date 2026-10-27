/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Interfaces
public import PaddedDescent.F.FuelCert
public import PaddedDescent.F.CertGrid
public import ToTuring.Poly.Digits
public import ToTuring.Poly.Words

/-! # Certificates for the grid

Polynomial time (PolyT) for the network `gridF P` of one term on a p × d grid and for the numbers
that one level computes from a step of the schedule. The sides p and d, the
parameter h of the pieces, the label length and the pad are data in unary; the flag «columns
merged», the pattern and the queries are data too. The pieces enter only through
their own certificates `P.Keeps`.

* `stCertGrid`: the lengths of the states and labels of `gridF P` are given in unary, its weights
  and factors are polynomial-time (the interface statement `StCertGrid P`).
* `stCertLam`: the label length one level down is given in unary (`StCertLam P`).
* For the certificates of a whole level: `capG_unary`, `priceG_unary`, `totalG_unary`,
  `capSum_unary`, `ubarG_unary`, `lamNextG_unary`, and `cnt_unary`, `cap_unary` for the
  pieces with h and the length of the strings as numbers in unary.
* Closure lemmas: the square root (`sqrt_polyT`, two binary digits at a time), the largest of
  finitely many numbers (`sup_range_polyT`), a chunk of a word whose chunks may be
  empty (`chunkAt_polyT`), and a product whose factors are only needed for small indices
  (`prodL_polyT_min`).

The chunks of a label may have the length 0 here, so the number of a chunk has to be given in unary.
In the product over the pairs of nodes of two parts the index j is therefore
replaced by min j m², which changes no factor of the product. -/

public section

namespace ClauseBound.Alg.CertGridG

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

variable {α : Type} [Enc α]

/-! ### More closure lemmas for numbers given in unary -/

/-- «Given in unary» passes to a function with the same values. -/
theorem unary_congr {f g : α → ℕ} (h : Unary f) (e : ∀ x, f x = g x) : Unary g := by
  obtain rfl : f = g := funext e
  exact h

/-- A case distinction between two numbers given in unary is given in unary. -/
@[fun_prop] theorem unary_ite {c : α → Prop} [DecidablePred c] {f g : α → ℕ} (hc : PolyT fun x => decide (c x)) (hf : Unary f) (hg : Unary g) :
    Unary fun x => if c x then f x else g x :=
  (PolyT.ite' hc hf hg).congr fun x => by by_cases h : c x <;> simp [h]

/-- The remainder of a number given in unary is given in unary. -/
@[fun_prop] theorem unary_mod {f g : α → ℕ} (hf : Unary f) (hg : PolyT g) : Unary fun x => f x % g x :=
  Unary.of_le hf (by have := hf.poly; fun_prop) fun _ => Nat.mod_le _ _

/-- The larger of two numbers given in unary is given in unary. -/
@[fun_prop] theorem unary_max {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun x => max (f x) (g x) :=
  Unary.of_le (hf.add hg) (by have := hf.poly; have := hg.poly; fun_prop) fun _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-- The smaller of two numbers given in unary is given in unary. -/
@[fun_prop] theorem unary_min {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun x => min (f x) (g x) :=
  Unary.of_le hf (by have := hf.poly; have := hg.poly; fun_prop) fun _ => min_le_left _ _

/-- The smaller of any number and a number given in unary is given in unary. -/
theorem unary_min_right {f g : α → ℕ} (hf : PolyT f) (hg : Unary g) : Unary fun x => min (f x) (g x) :=
  Unary.of_le hg (by have := hg.poly; fun_prop) fun _ => min_le_right _ _

/-- g(g − 1)/2 is given in unary if g is. -/
@[fun_prop] theorem c2_unary {g : α → ℕ} (hg : Unary g) : Unary fun x => c2 (g x) := by
  have := hg.poly
  unfold c2; fun_prop

/-- g(g − 1)/2 is polynomial-time. -/
@[fun_prop] theorem c2_polyT {g : α → ℕ} (hg : PolyT g) : PolyT fun x => c2 (g x) :=
  PolyT.div (PolyT.mul hg (PolyT.sub hg (PolyT.const 1))) (PolyT.const 2)

/-- The number of the pair a < b is given in unary if a and b are. -/
@[fun_prop] theorem tri_unary {a b : α → ℕ} (ha : Unary a) (hb : Unary b) : Unary fun x => tri (a x) (b x) := by
  have := hb.poly
  unfold tri; fun_prop

/-- A product over j < n only needs its factors for j ≤ n. -/
theorem prodL_min (n : ℕ) (f : ℕ → ℤ) : prodL n (fun j => f (min j n)) = prodL n f := by
  rw [prodL_eq, prodL_eq]
  exact Finset.prod_congr rfl fun j hj => by rw [min_eq_left (Finset.mem_range.1 hj).le]

/-- A product over j < n is polynomial-time if its factors are for indices given in unary. -/
theorem prodL_polyT_min {n : α → ℕ} {f : α → ℕ → ℤ} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => prodL (n x) (f x) :=
  (prodL_polyT (f := fun x j => f x (min j (n x))) hn hf).congr fun _ => prodL_min _ _

/-- A chunk of a word, for lengths that are polynomial-time and a chunk number given in unary. -/
theorem chunkAt_polyT {n : α → ℕ → ℕ} {κ : α → ℕ} {w : α → List Bool} (hn : PolyT fun p : α × ℕ => n p.1 p.2) (hκ : Unary κ) (hw : PolyT w) :
    PolyT fun x => chunkAt (n x) (κ x) (w x) := by
  have hκ' := hκ.poly
  have h1 : PolyT fun x => n x (κ x) := PolyT.comp₂ hn (by fun_prop) hκ'
  have h : PolyT fun x => ((w x).drop ((List.range (κ x)).map (n x)).sum).take (n x (κ x)) := by fun_prop
  exact h.congr fun x => by rw [chunkAt, sum_range_eq_list]

/-! ### Positions in the words of the p × d grid -/

/-- The number of rectangles is given in unary if p and d are. -/
@[fun_prop] theorem nRectG_unary {p d : α → ℕ} (hp : Unary p) (hd : Unary d) : Unary fun x => nRectG (p x) (d x) := by
  unfold nRectG; fun_prop

/-- The number of rectangles is polynomial-time. -/
@[fun_prop] theorem nRectG_polyT {p d : α → ℕ} (hp : PolyT p) (hd : PolyT d) : PolyT fun x => nRectG (p x) (d x) := by
  unfold nRectG; fun_prop

/-- The number of parts is given in unary if p and d are. -/
@[fun_prop] theorem nParts_unary {p d : α → ℕ} {tr : α → Bool} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) :
    Unary fun x => nParts (p x) (d x) (tr x) :=
  unary_ite (PolyT.decide_eq_true ht) hd hp

/-- The number of nodes of a part is given in unary if p and d are. -/
@[fun_prop] theorem nMemb_unary {p d : α → ℕ} {tr : α → Bool} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) :
    Unary fun x => nMemb (p x) (d x) (tr x) :=
  unary_ite (PolyT.decide_eq_true ht) hp hd

/-- The number of parts is polynomial-time. -/
@[fun_prop] theorem nParts_polyT {p d : α → ℕ} {tr : α → Bool} (hp : PolyT p) (hd : PolyT d) (ht : PolyT tr) :
    PolyT fun x => nParts (p x) (d x) (tr x) :=
  PolyT.ite' (PolyT.decide_eq_true ht) hd hp

/-- The number of nodes of a part is polynomial-time. -/
@[fun_prop] theorem nMemb_polyT {p d : α → ℕ} {tr : α → Bool} (hp : PolyT p) (hd : PolyT d) (ht : PolyT tr) :
    PolyT fun x => nMemb (p x) (d x) (tr x) :=
  PolyT.ite' (PolyT.decide_eq_true ht) hp hd

/-- The position of a node of a part is polynomial-time. -/
@[fun_prop] theorem nodeG_polyT {d a i : α → ℕ} {tr : α → Bool} (hd : PolyT d) (ht : PolyT tr) (ha : PolyT a) (hi : PolyT i) :
    PolyT fun x => nodeG (d x) (tr x) (a x) (i x) :=
  PolyT.ite' (PolyT.decide_eq_true ht) (ha.add (hd.mul hi)) (hi.add (hd.mul ha))

/-- The number of a rectangle is polynomial-time. -/
@[fun_prop] theorem rectIxG_polyT {d q κ : α → ℕ} {tr : α → Bool} (hd : PolyT d) (ht : PolyT tr) (hq : PolyT q) (hκ : PolyT κ) :
    PolyT fun x => rectIxG (d x) (tr x) (q x) (κ x) :=
  PolyT.ite' (PolyT.decide_eq_true ht) ((hκ.mul (c2_polyT hd)).add hq) ((hq.mul (c2_polyT hd)).add hκ)

/-- A half-edge in the word of a state is polynomial-time. -/
@[fun_prop] theorem heG_polyT {p d ℓ i u : α → ℕ} {z : α → List Bool} (hp : PolyT p) (hd : PolyT d) (hℓ : PolyT ℓ) (hz : PolyT z) (hi : PolyT i)
    (hu : PolyT u) : PolyT fun x => heG (p x) (d x) (ℓ x) (z x) (i x) (u x) := by
  unfold heG; fun_prop

/-- The test of the edges inside a part is polynomial-time, for p and d in unary. -/
@[fun_prop] theorem chkG_polyT {p d ℓ : α → ℕ} {tr : α → Bool} {q : α → WQ} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) (hℓ : PolyT ℓ)
    (hq : PolyT q) : PolyT fun x => chkG (p x) (d x) (tr x) (ℓ x) (q x) := by
  have := hp.poly
  have := hd.poly
  unfold chkG; fun_prop

/-- The weight of a part is polynomial-time, for p and d in unary. -/
theorem gridW_polyT {p d ℓ : α → ℕ} {tr : α → Bool} {T : α → Tab} {q : α → WQ} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) (hℓ : PolyT ℓ)
    (hT : PolyT T) (hq : PolyT q) : PolyT fun x => gridW (p x) (d x) (tr x) (ℓ x) (T x) (q x) := by
  have := hp.poly
  have := hd.poly
  unfold gridW; fun_prop

/-! ### The square root, and the largest of finitely many numbers -/

/-- The square root of m from that of m / 4. -/
theorem sqrt_eq_ite (m : ℕ) :
    Nat.sqrt m = if (2 * Nat.sqrt (m / 4) + 1) * (2 * Nat.sqrt (m / 4) + 1) ≤ m then 2 * Nat.sqrt (m / 4) + 1 else 2 * Nat.sqrt (m / 4) := by
  have h1 := Nat.sqrt_le (m / 4)
  have h2 := Nat.lt_succ_sqrt (m / 4)
  generalize Nat.sqrt (m / 4) = t at *
  have e1 : (t + 1) * (t + 1) = t * t + 2 * t + 1 := by ring
  have e2 : (2 * t + 1 + 1) * (2 * t + 1 + 1) = 4 * (t * t) + 8 * t + 4 := by ring
  have e3 : 2 * t * (2 * t) = 4 * (t * t) := by ring
  rw [Nat.succ_eq_add_one, e1] at h2
  split_ifs with h
  · exact (Nat.eq_sqrt.2 ⟨h, by omega⟩).symm
  · exact (Nat.eq_sqrt.2 ⟨by omega, by omega⟩).symm

/-- The square root, two binary digits of the number at a time. -/
theorem foldr_sqrt (n : ℕ) : ∀ k j : ℕ, n / 4 ^ (j + k) = 0 →
    (List.range' j k).foldr (fun i r => if (2 * r + 1) * (2 * r + 1) ≤ n / 4 ^ i then 2 * r + 1 else 2 * r) 0 = Nat.sqrt (n / 4 ^ j) := by
  intro k
  induction k with
  | zero => intro j h; rw [Nat.add_zero] at h; simp [h]
  | succ k ih =>
    intro j h
    rw [List.range'_succ, List.foldr_cons, ih (j + 1) (by rw [← h]; congr 2; omega), sqrt_eq_ite (n / 4 ^ j), Nat.div_div_eq_div_mul, ← pow_succ]

/-- The square root is polynomial-time. -/
@[fun_prop] theorem sqrt_polyT {f : α → ℕ} (hf : PolyT f) : PolyT fun x => Nat.sqrt (f x) := by
  have hl : PolyT fun x => List.range (Nat.bits (f x)).length := PolyT.range (Unary.of_length (by fun_prop))
  have h : PolyT fun x => (List.range (Nat.bits (f x)).length).foldr
      (fun i r => if (2 * r + 1) * (2 * r + 1) ≤ f x / 4 ^ i then 2 * r + 1 else 2 * r) 0 := by
    have h1 : PolyT fun p : α × ℕ × ℕ => 2 * p.2.2 + 1 := by fun_prop
    have h2 : PolyT fun p : α × ℕ × ℕ => f p.1 / 4 ^ p.2.1 := PolyT.div_pow (by fun_prop) (PolyT.const 4) (by fun_prop)
    refine PolyT.foldr_add (g := fun x i r => if (2 * r + 1) * (2 * r + 1) ≤ f x / 4 ^ i then 2 * r + 1 else 2 * r) hl (by fun_prop)
      (PolyT.ite' (PolyT.decide_le (h1.mul h1) h2) h1 (by fun_prop))
      ⟨fun _ => 3, PB.const 3, fun x c e _ => PolyT.len_le_of_le_dbl ?_⟩
    split_ifs <;> omega
  refine h.congr fun x => ?_
  rw [List.range_eq_range', foldr_sqrt (f x) _ 0, pow_zero, Nat.div_one]
  rw [Nat.zero_add, Nat.size_eq_bits_len]
  refine Nat.div_eq_of_lt ((Nat.lt_size_self _).trans_le ?_)
  exact Nat.pow_le_pow_left (by norm_num) _

/-- The square root of a number given in unary is given in unary. -/
@[fun_prop] theorem sqrt_unary {f : α → ℕ} (hf : Unary f) : Unary fun x => Nat.sqrt (f x) :=
  Unary.of_le hf (sqrt_polyT hf.poly) fun _ => Nat.sqrt_le_self _

/-- The largest of f 0, …, f (n − 1) as a fold. -/
theorem sup_range_eq_foldl (n : ℕ) (f : ℕ → ℕ) : (Finset.range n).sup f = (List.range n).foldl (fun c i => max c (f i)) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.sup_insert, List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    exact max_comm _ _

/-- The largest of f 0, …, f (n − 1) is polynomial-time, for n in unary. -/
theorem sup_range_polyT {n : α → ℕ} {f : α → ℕ → ℕ} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 p.2) :
    PolyT fun x => (Finset.range (n x)).sup (f x) := by
  have hr : PolyT fun x => List.range (n x) := PolyT.range hn
  obtain ⟨b, hb, hbl⟩ := PolyT.len_bound_mem hf hr
  have h : PolyT fun x => (List.range (n x)).foldl (fun c i => max c (f x i)) 0 := by
    refine PolyT.foldl_add (g := fun x c i => max c (f x i)) hr (by fun_prop) ?_ ⟨b, hb, fun x c e he => ?_⟩
    · have : PolyT fun p : α × ℕ × ℕ => f p.1 p.2.2 := PolyT.comp (g := fun p : α × ℕ × ℕ => (p.1, p.2.2)) hf (by fun_prop)
      fun_prop
    · have := hbl x e he
      rcases max_choice c (f x e) with h | h <;> rw [h] <;> omega
  exact h.congr fun x => (sup_range_eq_foldl _ _).symm

/-- The largest of f 0, …, f (n − 1) is given in unary if n and the numbers are. -/
theorem sup_range_unary {n : α → ℕ} {f : α → ℕ → ℕ} (hn : Unary n) (hf : Unary fun p : α × ℕ => f p.1 p.2) :
    Unary fun x => (Finset.range (n x)).sup (f x) :=
  Unary.of_le (g := fun x => ((List.range (n x)).map (f x)).sum) (by fun_prop) (sup_range_polyT hn hf.poly) fun x => by
    rw [← sum_range_eq_list]
    exact Finset.sup_le fun i hi => Finset.single_le_sum (f := f x) (fun _ _ => Nat.zero_le _) hi

/-! ### The parts of a step -/

section Step

variable {s : α → Step} (hs : PolyT s)
include hs

/-- K is given in unary. -/
@[fun_prop] theorem K_unary : Unary fun x => (s x).K := by unfold Step.K; fun_prop
/-- p is given in unary. -/
@[fun_prop] theorem p_unary : Unary fun x => (s x).p := by unfold Step.p; fun_prop
/-- d is given in unary. -/
@[fun_prop] theorem d_unary : Unary fun x => (s x).d := by unfold Step.d; fun_prop
/-- D is given in unary. -/
@[fun_prop] theorem D_unary : Unary fun x => (s x).D := by unfold Step.D; fun_prop
/-- h is given in unary. -/
@[fun_prop] theorem h_unary : Unary fun x => (s x).h := by unfold Step.h; fun_prop
/-- a is given in unary. -/
@[fun_prop] theorem a_unary : Unary fun x => (s x).a := by unfold Step.a; fun_prop
/-- b is given in unary. -/
@[fun_prop] theorem b_unary : Unary fun x => (s x).b := by unfold Step.b; fun_prop
/-- The flag «thin» is polynomial-time. -/
@[fun_prop] theorem thin_polyT : PolyT fun x => (s x).thin := by unfold Step.thin; fun_prop

/-- N = (pd)²λ is given in unary. -/
@[fun_prop] theorem Nof_unary {lam : α → ℕ} (hl : Unary lam) : Unary fun x => Nof (s x) (lam x) := by
  unfold Nof; fun_prop

end Step

/-! ### The arithmetic of one level, for any numbers -/

/-- The formula of the bound for U, for any numbers given in unary. -/
theorem ubarG_aux {thin : α → Bool} {N a p d lam R cs : α → ℕ} (h0 : PolyT thin) (h1 : Unary N) (h2 : PolyT a) (h3 : Unary p) (h4 : Unary d)
    (h5 : Unary lam) (h6 : Unary R) (h7 : Unary cs) :
    Unary fun x => if thin x = true then N x - N x / a x + (p x * d x) ^ 2 else p x * (p x - 1) * d x * lam x + R x * cs x :=
  unary_ite (PolyT.decide_eq_true h0) ((unary_sub h1 (PolyT.div h1.poly h2)).add (unary_pow_const (h3.mul h4) 2))
    ((((h3.mul (unary_sub h3 (PolyT.const 1))).mul h4).mul h5).add (h6.mul h7))

/-- The formula of the label length one level down, for any numbers given in unary. -/
theorem lamNextG_aux (m : ℕ) {D ub p d lam K : α → ℕ} (h1 : Unary D) (h2 : Unary ub) (h3 : Unary p) (h4 : Unary d) (h5 : Unary lam) (h6 : Unary K) :
    Unary fun x => (D x * ub x + 3 * p x ^ 2 * (d x ^ 2 * (m * lam x))) / (D x * K x ^ 2) + 1 := by
  have h7 : PolyT fun x => D x * K x ^ 2 := (h1.mul (unary_pow_const h6 2)).poly
  have h8 : Unary fun x => D x * ub x + 3 * p x ^ 2 * (d x ^ 2 * (m * lam x)) := by fun_prop
  exact (unary_div h8 h7).add (Unary.const 1)

/-! ### The pieces -/

section Pieces

variable {P : PiecesF} (K : P.Keeps)
include K

/-- The number of pieces is given in unary if h and the length of the strings are. -/
theorem cnt_unary {h ℓ : α → ℕ} (hh : Unary h) (hℓ : Unary ℓ) : Unary fun x => P.cnt (h x) (ℓ x) :=
  unary_congr (K.cnt.comp (h := fun x => (List.replicate (h x) (), List.replicate (ℓ x) ())) (by fun_prop)) fun x => by simp

/-- The number of bits through which a piece factors is given in unary. -/
theorem cap_unary {tr : α → Bool} {h ℓ i : α → ℕ} (ht : PolyT tr) (hh : Unary h) (hℓ : Unary ℓ) (hi : PolyT i) :
    Unary fun x => P.cap (tr x) (h x) (ℓ x) (i x) :=
  unary_congr (K.cap.comp (h := fun x => (tr x, List.replicate (h x) (), List.replicate (ℓ x) (), i x)) (by fun_prop)) fun x => by simp

/-- The digit of a pattern at a rectangle. -/
theorem digG_polyT {d h ℓ y q κ : α → ℕ} {tr : α → Bool} (hd : PolyT d) (ht : PolyT tr) (hh : Unary h) (hℓ : Unary ℓ) (hy : PolyT y) (hq : PolyT q)
    (hκ : PolyT κ) : PolyT fun x => digG P (d x) (tr x) (h x) (ℓ x) (y x) (q x) (κ x) := by
  have := (cnt_unary K hh hℓ).poly
  unfold digG; fun_prop

/-- The length of the chunk of a rectangle is given in unary. -/
theorem lenG_unary {d h ℓ y q κ : α → ℕ} {tr : α → Bool} (hd : PolyT d) (ht : PolyT tr) (hh : Unary h) (hℓ : Unary ℓ) (hy : PolyT y) (hq : PolyT q)
    (hκ : PolyT κ) : Unary fun x => lenG P (d x) (tr x) (h x) (ℓ x) (y x) (q x) (κ x) :=
  cap_unary K ht hh hℓ (digG_polyT K hd ht hh hℓ hy hq hκ)

/-- The length of the labels of two parts is given in unary. -/
theorem capG_unary {p d h ℓ y a b : α → ℕ} {tr : α → Bool} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) (hh : Unary h) (hℓ : Unary ℓ) (hy : PolyT y)
    (ha : PolyT a) (hb : PolyT b) : Unary fun x => capG P (p x) (d x) (tr x) (h x) (ℓ x) (y x) (a x) (b x) := by
  have h1 : Unary fun q : α × ℕ => lenG P (d q.1) (tr q.1) (h q.1) (ℓ q.1) (y q.1) (tri (min (a q.1) (b q.1)) (max (a q.1) (b q.1))) q.2 :=
    lenG_unary K (by have := hd.poly; fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : Unary fun x => nMemb (p x) (d x) (tr x) * ℓ x + ((List.range (c2 (nMemb (p x) (d x) (tr x)))).map fun κ =>
      lenG P (d x) (tr x) (h x) (ℓ x) (y x) (tri (min (a x) (b x)) (max (a x) (b x))) κ).sum := by fun_prop
  exact unary_congr h2 fun x => by rw [capG, sum_range_eq_list]

/-- What the rectangles cost is given in unary. -/
theorem priceG_unary {p d h ℓ y : α → ℕ} {tr : α → Bool} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) (hh : Unary h) (hℓ : Unary ℓ) (hy : PolyT y) :
    Unary fun x => priceG P (p x) (d x) (tr x) (h x) (ℓ x) (y x) := by
  have h0 := (cnt_unary K hh hℓ).poly
  have h1 : Unary fun q : α × ℕ => P.cap (tr q.1) (h q.1) (ℓ q.1) (digit (P.cnt (h q.1) (ℓ q.1) - 1) (y q.1) q.2) :=
    cap_unary K (by fun_prop) (by fun_prop) (by fun_prop)
      (digit_polyT (PolyT.sub (h0.comp (g := fun q : α × ℕ => q.1) (by fun_prop)) (by fun_prop)) (by fun_prop) (by fun_prop))
  have h2 : Unary fun x => 2 * ((List.range (nRectG (p x) (d x))).map fun q =>
      P.cap (tr x) (h x) (ℓ x) (digit (P.cnt (h x) (ℓ x) - 1) (y x) q)).sum := by fun_prop
  exact unary_congr h2 fun x => by rw [priceG, sum_range_eq_list]

/-- U of the network of a pattern is given in unary. -/
theorem totalG_unary {p d h ℓ y : α → ℕ} {tr : α → Bool} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) (hh : Unary h) (hℓ : Unary ℓ) (hy : PolyT y) :
    Unary fun x => totalG P (p x) (d x) (tr x) (h x) (ℓ x) (y x) := by
  have := priceG_unary K hp hd ht hh hℓ hy
  unfold totalG; fun_prop

/-- The factor of the rectangle of the nodes i < i' of the two parts in `gridFf`. -/
def rectG (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ) (q : FQ) (i i' : ℕ) : ℤ :=
  (if q.1.1 < q.1.2 then P.top else P.bot) ((pad, tr),
    (h, digG P d tr h ℓ y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) (tri i i')),
    (heG p d ℓ q.2.1 i (nodeG d tr q.1.2 i'), heG p d ℓ q.2.1 i' (nodeG d tr q.1.2 i),
     chunkAt (lenG P d tr h ℓ y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2))) (tri i i') (q.2.2.drop (nMemb p d tr * ℓ))))

/-- The factor of a rectangle is polynomial-time, for the numbers of the two nodes in unary. -/
theorem rectG_polyT {pad : α → U} {p d h ℓ y i i' : α → ℕ} {tr : α → Bool} {q : α → FQ} (hpad : PolyT pad) (hp : Unary p) (hd : Unary d) (ht : PolyT tr)
    (hh : Unary h) (hℓ : Unary ℓ) (hy : PolyT y) (hq : PolyT q) (hi : Unary i) (hi' : Unary i') :
    PolyT fun x => rectG P (pad x) (p x) (d x) (tr x) (h x) (ℓ x) (y x) (q x) (i x) (i' x) := by
  have hp' := hp.poly
  have hd' := hd.poly
  have hℓ' := hℓ.poly
  have hi1 := hi.poly
  have hi2 := hi'.poly
  have hκ : Unary fun x => tri (i x) (i' x) := tri_unary hi hi'
  have ht2 : PolyT fun x => tri (min (q x).1.1 (q x).1.2) (max (q x).1.1 (q x).1.2) := by fun_prop
  have hdig := digG_polyT K hd' ht hh hℓ hy ht2 hκ.poly
  have hlen : PolyT fun r : α × ℕ => lenG P (d r.1) (tr r.1) (h r.1) (ℓ r.1) (y r.1) (tri (min (q r.1).1.1 (q r.1).1.2) (max (q r.1).1.1 (q r.1).1.2)) r.2 :=
    (lenG_unary K (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).poly
  have hw : PolyT fun x => (q x).2.2.drop (nMemb (p x) (d x) (tr x) * ℓ x) := by fun_prop
  have hch := chunkAt_polyT (n := fun x => lenG P (d x) (tr x) (h x) (ℓ x) (y x) (tri (min (q x).1.1 (q x).1.2) (max (q x).1.1 (q x).1.2))) hlen hκ hw
  have he1 := heG_polyT hp' hd' hℓ' hq.snd.fst hi1 (nodeG_polyT hd' ht hq.fst.snd hi2)
  have he2 := heG_polyT hp' hd' hℓ' hq.snd.fst hi2 (nodeG_polyT hd' ht hq.fst.snd hi1)
  have harg := (hpad.prodMk ht).prodMk ((hh.poly.prodMk hdig).prodMk (he1.prodMk (he2.prodMk hch)))
  refine (PolyT.ite' (c := fun x => (q x).1.1 < (q x).1.2) (by fun_prop) (K.top.comp harg) (K.bot.comp harg)).congr fun x => ?_
  unfold rectG
  by_cases h1 : (q x).1.1 < (q x).1.2 <;> simp only [h1, if_true, if_false]

/-- One factor of the product in `gridFf` is polynomial-time, for a number j given in unary. -/
theorem itemG_polyT {pad : α → U} {p d h ℓ y j : α → ℕ} {tr : α → Bool} {q : α → FQ} (hpad : PolyT pad) (hp : Unary p) (hd : Unary d) (ht : PolyT tr)
    (hh : Unary h) (hℓ : Unary ℓ) (hy : PolyT y) (hq : PolyT q) (hj : Unary j) :
    PolyT fun x => if j x / nMemb (p x) (d x) (tr x) < j x % nMemb (p x) (d x) (tr x) then
      rectG P (pad x) (p x) (d x) (tr x) (h x) (ℓ x) (y x) (q x) (j x / nMemb (p x) (d x) (tr x)) (j x % nMemb (p x) (d x) (tr x)) else 1 := by
  have hm : PolyT fun x => nMemb (p x) (d x) (tr x) := nMemb_polyT hp.poly hd.poly ht
  have h1 : Unary fun x => j x / nMemb (p x) (d x) (tr x) := unary_div hj hm
  have h2 : Unary fun x => j x % nMemb (p x) (d x) (tr x) := unary_mod hj hm
  exact PolyT.ite' (PolyT.decide_lt h1.poly h2.poly) (rectG_polyT K hpad hp hd ht hh hℓ hy hq h1 h2) (PolyT.const 1)

/-- The factor of two parts is polynomial-time, for p, d, h and the label length in unary. -/
theorem gridFf_polyT {pad : α → U} {p d h ℓ y : α → ℕ} {tr : α → Bool} {q : α → FQ} (hpad : PolyT pad) (hp : Unary p) (hd : Unary d) (ht : PolyT tr)
    (hh : Unary h) (hℓ : Unary ℓ) (hy : PolyT y) (hq : PolyT q) :
    PolyT fun x => gridFf P (pad x) (p x) (d x) (tr x) (h x) (ℓ x) (y x) (q x) := by
  have hp' := hp.poly
  have hd' := hd.poly
  have hℓ' := hℓ.poly
  have hmm : Unary fun x => nMemb (p x) (d x) (tr x) * nMemb (p x) (d x) (tr x) := by fun_prop
  have h1 : PolyT fun x => prodL (nMemb (p x) (d x) (tr x) * nMemb (p x) (d x) (tr x)) fun j =>
      if j / nMemb (p x) (d x) (tr x) < j % nMemb (p x) (d x) (tr x) then
        rectG P (pad x) (p x) (d x) (tr x) (h x) (ℓ x) (y x) (q x) (j / nMemb (p x) (d x) (tr x)) (j % nMemb (p x) (d x) (tr x)) else 1 :=
    prodL_polyT_min hmm (itemG_polyT K (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (unary_min_right (by fun_prop) (by fun_prop)))
  have h2 : PolyT fun x => (List.range (nMemb (p x) (d x) (tr x))).all fun i =>
      heG (p x) (d x) (ℓ x) (q x).2.1 i (nodeG (d x) (tr x) (q x).1.2 i) == block (ℓ x) i (q x).2.2 := by fun_prop
  exact PolyT.cond' h2 h1 (PolyT.const 0)

/-- The network of one term keeps polynomial time: lengths in unary, weights and factors
polynomial-time. -/
theorem gridF_keeps : FKeeps (gridF P) where
  n := by
    have h : Unary fun c : GridCtx × ℕ => nMemb c.1.1.2.1.1.length c.1.1.2.1.2.length c.1.1.2.2.1 * (c.1.1.2.1.1.length * c.1.1.2.1.2.length) * c.1.2.1.length := by
      fun_prop
    exact h
  cap := capG_unary K (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  W := gridW_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  f := gridFf_polyT K (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-! ### One level -/

/-- The largest sum of the two numbers of bits of a piece is given in unary. -/
theorem capSum_unary {h lam : α → ℕ} (hh : Unary h) (hl : Unary lam) : Unary fun x => capSum P (h x) (lam x) :=
  sup_range_unary (f := fun x i => P.cap false (h x) (lam x) i + P.cap true (h x) (lam x) i) (cnt_unary K hh hl)
    ((cap_unary K (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).add (cap_unary K (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)))

/-- The bound for U of the networks that are rebalanced is given in unary. -/
theorem ubarG_unary {s : α → Step} {lam : α → ℕ} (hs : PolyT s) (hl : Unary lam) : Unary fun x => ubarG P (s x) (lam x) := by
  unfold ubarG
  exact ubarG_aux (thin_polyT hs) (Nof_unary hs hl) (a_unary hs).poly (p_unary hs) (d_unary hs) hl (nRectG_unary (p_unary hs) (d_unary hs))
    (capSum_unary K (h_unary hs) hl)

/-- The label length one level down is given in unary. -/
theorem lamNextG_unary {s : α → Step} {lam : α → ℕ} (hs : PolyT s) (hl : Unary lam) : Unary fun x => lamNextG P (s x) (lam x) := by
  unfold lamNextG
  exact lamNextG_aux P.m (D_unary hs) (ubarG_unary K hs hl) (p_unary hs) (d_unary hs) hl (K_unary hs)

end Pieces

/-- The network of one term on a p × d grid keeps polynomial time, for pieces that do. -/
theorem stCertGrid (P : PiecesF) : StCertGrid P := fun K => gridF_keeps K

/-- The label length one level down is given in unary, for pieces that keep polynomial time. -/
theorem stCertLam (P : PiecesF) : StCertLam P := fun K => lamNextG_unary K (by fun_prop) (by fun_prop)

end ClauseBound.Alg.CertGridG
