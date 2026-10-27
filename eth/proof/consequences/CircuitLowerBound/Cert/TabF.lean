/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Cert.Sched
public import CircuitLowerBound.Small
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): the formulas are written out in polynomial time

`stCertTabF`: the formula of a table is written out in time polynomial in the table, L in unary, P
and a list that is at least as long as the formula has clauses. The two numbers of a table are
data in binary and occur in exponents, so the program cuts them off at L; where there is room
(`Fits`) this changes nothing.

`stFlip`: write a = `nu m` and L = 2^a. When `pos m` equals `top a`, which is 2^2^L, the formula of
the table `codeOf a`, cut off at L, has variables below 2^L, so all its 2^2^L assignments are tried
in time polynomial in m. -/

public section

namespace CircuitLowerBound.TabF

open ENP Groundwork Sched

variable {α : Type} [Enc α]

/-! ### The table with its two numbers cut off -/

/-- The table with its two numbers cut off at L. -/
@[expose] def clipE (e : MCode) (L : ℕ) : MCode := (min (kb e) L, min (lam e) L, tab e)

/-- Where there is room, the cut-off changes nothing. -/
theorem clipE_eq {e : MCode} {L P : ℕ} (h : Fits e L P) : clipE e L = e := by
  obtain ⟨h1, -⟩ := h
  unfold clipE
  rw [min_eq_left (by omega), min_eq_left (by omega)]
  rfl

/-- The table, cut off, is polynomial-time. -/
theorem clipE_polyT {e : α → MCode} {L : α → ℕ} (he : PolyT e) (hL : PolyT L) : PolyT fun x => clipE (e x) (L x) :=
  (PolyT.min' (kb_polyT he) hL).prodMk ((PolyT.min' (lam_polyT he) hL).prodMk (tab_polyT he))

/-- The first number of a table that is cut off at a number in unary is given in unary. -/
theorem kb_clipE_unary {e : α → MCode} {L : α → ℕ} (he : PolyT e) (hL : Unary L) : Unary fun x => kb (clipE (e x) (L x)) :=
  Unary.of_le hL (PolyT.min' (kb_polyT he) hL.poly) fun _ => Nat.min_le_right _ _

/-- The same for the second number. -/
theorem lam_clipE_unary {e : α → MCode} {L : α → ℕ} (he : PolyT e) (hL : Unary L) : Unary fun x => lam (clipE (e x) (L x)) :=
  Unary.of_le hL (PolyT.min' (lam_polyT he) hL.poly) fun _ => Nat.min_le_right _ _

/-! ### One clause, for a table whose two numbers are given in unary -/

/-- A number has at most as many binary digits as its value. -/
theorem size_le_self (n : ℕ) : Nat.size n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self

/-- The number of bits for the place of a clause in the table is given in unary. -/
theorem rb_unary {e : α → MCode} (he : PolyT e) : Unary fun x => rb (e x) :=
  Unary.of_le (Unary.of_length (tab_polyT he)) (PolyT.size' (PolyT.length (tab_polyT he))) fun _ => size_le_self _

/-- The time of a literal. -/
theorem tval_polyT {b t mode : α → ℕ} (hb : Unary b) (ht : PolyT t) (hm : PolyT mode) : PolyT fun x => tval (b x) (t x) (mode x) := by
  have h1 : PolyT fun x => 2 ^ b x := PolyT.two_pow hb
  have h2 : PolyT fun x => mode x % 4 := PolyT.mod hm (PolyT.const 4)
  have key : ∀ p r : α → ℕ, PolyT p → PolyT r → PolyT fun x => if r x = 0 then 0 else if r x = 1 then t x else if r x = 2 then t x + 1 else p x := by
    intro p r _ _
    fun_prop
  exact key _ _ h1 h2

/-- The position of a literal. -/
theorem qval_polyT {P q mode : α → ℕ} (hP : PolyT P) (hq : PolyT q) (hm : PolyT mode) : PolyT fun x => qval (P x) (q x) (mode x) := by
  have h2 : PolyT fun x => mode x % 4 := PolyT.mod hm (PolyT.const 4)
  have key : ∀ r : α → ℕ, PolyT r → PolyT fun x => if r x = 0 then 0 else if r x = 1 then q x else P x := by
    intro r _
    fun_prop
  exact key _ h2

section
variable {e : α → MCode} {L P : α → ℕ} (he : PolyT e) (hk : Unary fun x => kb (e x)) (hl : Unary fun x => lam (e x)) (hL : Unary L) (hP : PolyT P)
include he hk hl hL

omit hk in
/-- The number of bits of a position is given in unary. -/
theorem bq_unary : Unary fun x => bq (e x) (L x) := (bt_unary he hL).add hl

omit hk in
/-- The number of bits of the number of a clause is given in unary. -/
theorem nb_unary : Unary fun x => nb (e x) (L x) := ((rb_unary he).add (bt_unary he hL)).add (bq_unary he hl hL)

include hP

/-- A literal of the formula. -/
theorem litAt_polyT {t q : α → ℕ} {l : α → TLit} (ht : PolyT t) (hq : PolyT q) (hlit : PolyT l) :
    PolyT fun x => litAt (e x) (L x) (P x) (t x) (q x) (l x) := by
  have p1 : PolyT fun x => 2 ^ kb (e x) := PolyT.two_pow hk
  have p2 : PolyT fun x => 2 ^ (bt (e x) (L x) + 1) := PolyT.two_pow ((bt_unary he hL).add (Unary.const 1))
  have p3 : PolyT fun x => 2 ^ (bq (e x) (L x) + 1) := PolyT.two_pow ((bq_unary he hl hL).add (Unary.const 1))
  have tv : PolyT fun x => tval (bt (e x) (L x)) (t x) (l x).2.1 := tval_polyT (bt_unary he hL) ht (by fun_prop)
  have qv : PolyT fun x => qval (P x) (q x) (l x).2.2.1 := qval_polyT hP hq (by fun_prop)
  have l1 : PolyT fun x => (l x).1 := by fun_prop
  have l4 : PolyT fun x => (l x).2.2.2.1 := by fun_prop
  have l5 : PolyT fun x => (l x).2.2.2.2 := by fun_prop
  exact (PolyT.add (PolyT.mul (PolyT.add (PolyT.mul (PolyT.mod l1 p1) p2) tv) p3) (PolyT.mod (PolyT.add qv l4) p3)).prodMk l5

/-- A clause of the formula. -/
theorem clauseAt_polyT {j : α → ℕ} (hj : PolyT j) : PolyT fun x => clauseAt (e x) (L x) (P x) (j x) := by
  have p1 : PolyT fun x => 2 ^ bq (e x) (L x) := PolyT.two_pow (bq_unary he hl hL)
  have p2 : PolyT fun x => 2 ^ bt (e x) (L x) := PolyT.two_pow (bt_unary he hL)
  have p3 : PolyT fun x => 2 ^ (bt (e x) (L x) + bq (e x) (L x)) := PolyT.two_pow ((bt_unary he hL).add (bq_unary he hl hL))
  have ht : PolyT fun x => j x / 2 ^ bq (e x) (L x) % 2 ^ bt (e x) (L x) := PolyT.mod (PolyT.div hj p1) p2
  have hq : PolyT fun x => j x % 2 ^ bq (e x) (L x) := PolyT.mod hj p1
  have hc : PolyT fun x => (tab (e x)).getD (j x / 2 ^ (bt (e x) (L x) + bq (e x) (L x))) zeroCl :=
    PolyT.getD (tab_polyT he) (PolyT.div hj p3) (PolyT.const _)
  have a1 := litAt_polyT he hk hl hL hP ht hq (l := fun x => ((tab (e x)).getD (j x / 2 ^ (bt (e x) (L x) + bq (e x) (L x))) zeroCl).1) hc.fst
  have a2 := litAt_polyT he hk hl hL hP ht hq (l := fun x => ((tab (e x)).getD (j x / 2 ^ (bt (e x) (L x) + bq (e x) (L x))) zeroCl).2.1) hc.snd.fst
  have a3 := litAt_polyT he hk hl hL hP ht hq (l := fun x => ((tab (e x)).getD (j x / 2 ^ (bt (e x) (L x) + bq (e x) (L x))) zeroCl).2.2) hc.snd.snd
  have key : ∀ a b c : α → ℕ × Bool, PolyT a → PolyT b → PolyT c → PolyT fun x => [a x, b x, c x] := by
    intro a b c _ _ _
    fun_prop
  exact key _ _ _ a1 a2 a3

end

/-! ### The formula -/

/-- The formula of a table, cut off by a pad, with the two numbers of the table cut off at L. -/
@[expose] def G (p : (MCode × List Unit × ℕ) × List Unit) : Cnf :=
  (List.range (min (2 ^ nb (clipE p.1.1 p.1.2.1.length) p.1.2.1.length) p.2.length)).map
    (clauseAt (clipE p.1.1 p.1.2.1.length) p.1.2.1.length p.1.2.2)

/-- The program is polynomial-time. -/
theorem G_polyT : PolyT G := by
  have hL : Unary fun p : (MCode × List Unit × ℕ) × List Unit => p.1.2.1.length := Unary.of_length (by fun_prop)
  have he : PolyT fun p : (MCode × List Unit × ℕ) × List Unit => clipE p.1.1 p.1.2.1.length := clipE_polyT (by fun_prop) hL.poly
  have hk := kb_clipE_unary (e := fun p : (MCode × List Unit × ℕ) × List Unit => p.1.1) (by fun_prop) hL
  have hl := lam_clipE_unary (e := fun p : (MCode × List Unit × ℕ) × List Unit => p.1.1) (by fun_prop) hL
  have hn : PolyT fun p : (MCode × List Unit × ℕ) × List Unit => 2 ^ nb (clipE p.1.1 p.1.2.1.length) p.1.2.1.length :=
    PolyT.two_pow (nb_unary he hl hL)
  have hr := PolyT.range (PolyT.unary_min_length hn (l := fun p : (MCode × List Unit × ℕ) × List Unit => p.2) (by fun_prop))
  refine PolyT.map (f := fun (p : (MCode × List Unit × ℕ) × List Unit) j => clauseAt (clipE p.1.1 p.1.2.1.length) p.1.2.1.length p.1.2.2 j) ?_ hr
  exact clauseAt_polyT (e := fun q : ((MCode × List Unit × ℕ) × List Unit) × ℕ => clipE q.1.1.1 q.1.1.2.1.length) (L := fun q => q.1.1.2.1.length)
    (P := fun q => q.1.1.2.2) (PolyT.comp he PolyT.id'.fst) (hk.comp PolyT.id'.fst) (hl.comp PolyT.id'.fst) (hL.comp PolyT.id'.fst) (by fun_prop) (by fun_prop)

/-- Where there is room and the pad is long enough, the program writes the formula of the table. -/
theorem G_eq {e : MCode} {L P : ℕ} {pad : List Unit} (hF : Fits e L P) (hp : 2 ^ nb e L ≤ pad.length) :
    G ((e, List.replicate L (), P), pad) = tabF e L P := by
  simp only [G, List.length_replicate, clipE_eq hF, min_eq_left hp, tabF]

/-! ### All assignments of a formula with few variables -/

/-- A formula with variables below M is satisfiable if and only if the binary digits of some number
below 2^M satisfy it. -/
theorem sat_iff_testBit (φ : Cnf) (M : ℕ) (hv : ∀ C ∈ φ, ∀ l ∈ C, l.1 < M) :
    Sat φ ↔ ∃ α < 2 ^ M, ∀ C ∈ φ, ∃ l ∈ C, α.testBit l.1 = l.2 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨Nat.ofBits fun i : Fin M => f i, Nat.ofBits_lt_two_pow _, fun C hC => ?_⟩
    obtain ⟨l, hl, h⟩ := hf C hC
    exact ⟨l, hl, by rw [Nat.testBit_ofBits_lt _ _ (hv C hC l hl)]; exact h⟩
  · rintro ⟨α, -, h⟩
    exact ⟨fun i => α.testBit i, h⟩

/-- «Some number below N satisfies φ», as a program. -/
@[expose] def tryAll (N : ℕ) (φ : Cnf) : Bool := (List.range N).any fun α => φ.all fun D => D.any fun l => α.testBit l.1 == l.2

/-- What the program decides. -/
theorem tryAll_iff (N : ℕ) (φ : Cnf) : tryAll N φ = true ↔ ∃ α < N, ∀ C ∈ φ, ∃ l ∈ C, α.testBit l.1 = l.2 := by
  simp only [tryAll, List.any_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]

/-- Trying all numbers below a number in unary is polynomial-time. -/
theorem tryAll_polyT {N : α → ℕ} {φ : α → Cnf} (hN : Unary N) (hφ : PolyT φ) : PolyT fun x => tryAll (N x) (φ x) := by
  have hr := PolyT.range hN
  unfold tryAll
  fun_prop

/-! ### Sizes when `pos m` equals `top (nu m)` -/

/-- 2 to the number of binary digits of n is at most 2n + 1. -/
theorem two_pow_size_le (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos (Nat.size n) with h | h
  · rw [h]; omega
  · have h1 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.1 (by omega)
    have h2 : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega

/-- The rest of a word is no longer than the word. -/
theorem length_rest_le (x : List Bool) : (rest x).length ≤ x.length := by
  unfold rest
  rw [List.length_tail]
  have := (List.dropWhile_sublist (l := x) id).length_le
  omega

/-- The table with the number a has at most a clauses. -/
theorem length_tab_codeOf_le (a : ℕ) : (tab (codeOf a)).length ≤ a := by
  have h1 : (tab (codeOf a)).length ≤ (rest (rest (Nat.bits a))).length := by
    simp only [tab, codeOf, codeOfWord, List.length_map, List.length_range]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have h2 := length_rest_le (rest (Nat.bits a))
  have h3 := length_rest_le (Nat.bits a)
  have h4 : (Nat.bits a).length = Nat.size a := Nat.size_eq_bits_len a
  have h5 := size_le_self a
  omega

/-- Where there is room, the formula of a table has at most (2·(number of clauses of the table) + 1)·2^L
clauses. -/
theorem two_pow_nb_le {e : MCode} {L P : ℕ} (hF : Fits e L P) : 2 ^ nb e L ≤ (2 * (tab e).length + 1) * 2 ^ L := by
  obtain ⟨h1, -⟩ := hF
  have h2 : bt e L + bq e L ≤ L := by
    unfold bq bt
    omega
  calc 2 ^ nb e L = 2 ^ rb e * 2 ^ (bt e L + bq e L) := by rw [nb, add_assoc, pow_add]
    _ ≤ (2 * (tab e).length + 1) * 2 ^ L := Nat.mul_le_mul (two_pow_size_le _) (Nat.pow_le_pow_right (by norm_num) h2)

/-! ### The flip -/

/-- The answer for m, given in unary: the table `codeOf (nu m)` fits, and some number below `pos m`
satisfies its formula, cut off at L. -/
@[expose] def fb (u : List Unit) : Bool :=
  decide (Fits (codeOf (nu u.length)) (min (2 ^ nu u.length) u.length) (2 ^ nu u.length)) &&
    tryAll (pos u.length)
      (G ((codeOf (nu u.length), List.replicate (min (2 ^ nu u.length) u.length) (), 2 ^ nu u.length), List.replicate ((2 * u.length + 1) * u.length) ()))

/-- The answer is computed in polynomial time. -/
theorem fb_polyT : PolyT fb := by
  have hm : PolyT fun u : List Unit => u.length := by fun_prop
  have hmu : Unary fun u : List Unit => u.length := Unary.of_length PolyT.id'
  have ha := nu_unary hm
  have hp : PolyT fun u : List Unit => 2 ^ nu u.length := PolyT.two_pow ha
  have hL : Unary fun u : List Unit => min (2 ^ nu u.length) u.length := PolyT.unary_min_length hp PolyT.id'
  have he : PolyT fun u : List Unit => codeOf (nu u.length) := codeOf_polyT ha.poly
  have hpos : Unary fun u : List Unit => pos u.length :=
    Unary.of_le hmu (pos_polyT hm) fun u => (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
  have hpad : Unary fun u : List Unit => (2 * u.length + 1) * u.length := (((Unary.const 2).mul hmu).add (Unary.const 1)).mul hmu
  have hG : PolyT fun u : List Unit => G ((codeOf (nu u.length), List.replicate (min (2 ^ nu u.length) u.length) (), 2 ^ nu u.length),
      List.replicate ((2 * u.length + 1) * u.length) ()) :=
    PolyT.comp G_polyT ((he.prodMk (PolyT.prodMk hL hp)).prodMk hpad)
  exact PolyT.and' (fits_polyT he hL hp) (tryAll_polyT hpos hG)

/-- When `pos m` equals `top (nu m)`, the answer is right, given that the variables of the formula
of a table have L bits. -/
theorem fb_iff (hV : StVars) (m : ℕ) (hm : pos m = top (nu m)) :
    fb (List.replicate m ()) = true ↔ Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m)) := by
  obtain ⟨a, ha⟩ : ∃ a, a = nu m := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = 2 ^ a := ⟨_, rfl⟩
  have htop : top a = 2 ^ 2 ^ L := by rw [top, hL]
  -- m is at least 2·2^a times `pos m`
  have h1 : 2 ^ a * 2 * pos m ≤ m := by
    rw [pos, ← ha, Nat.div_div_eq_div_mul]
    exact Nat.mul_div_le _ _
  have h2 : 2 ^ L < 2 ^ 2 ^ L := Nat.pow_lt_pow_right (by norm_num) Nat.lt_two_pow_self
  have h3 : 1 ≤ L := hL ▸ Nat.one_le_two_pow
  have h4 : 2 ^ 2 ^ L ≤ m := by
    rw [← ha, htop] at hm
    rw [hm, ← hL] at h1
    nlinarith
  have h5 : L ≤ m := by
    have : L < 2 ^ L := Nat.lt_two_pow_self
    omega
  have h6 : a ≤ m := by
    have : a < 2 ^ a := Nat.lt_two_pow_self
    omega
  simp only [fb, List.length_replicate, ← ha, ← hL, min_eq_left h5, Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr_right fun hF => ?_
  have hpad : 2 ^ nb (codeOf a) L ≤ (List.replicate ((2 * m + 1) * m) ()).length := by
    rw [List.length_replicate]
    refine (two_pow_nb_le hF).trans (Nat.mul_le_mul ?_ (by omega))
    have := length_tab_codeOf_le a
    omega
  rw [G_eq hF hpad, tryAll_iff, sat_iff_testBit _ (2 ^ L) (hV _ _ _ hF), hm, ← ha, htop]

end CircuitLowerBound.TabF

namespace CircuitLowerBound

open ENP Groundwork TabF

/-- The formula of a table is written out in polynomial time. -/
theorem stCertTabF : StCertTabF := ⟨G, G_polyT, fun _ _ _ _ hF hp => G_eq hF hp⟩

/-- When `pos m` equals `top (nu m)`, whether the table `codeOf (nu m)` fits and its formula, with L =
2^(nu m), is satisfiable is decided in time polynomial in m, given that the variables of a formula
of a table have L bits. -/
theorem stFlip_of (hV : StVars) : StFlip := ⟨fb, fb_polyT, fun m hm => fb_iff hV m hm⟩

/-- When `pos m` equals `top (nu m)`, whether the table `codeOf (nu m)` fits and its formula, with L =
2^(nu m), is satisfiable is decided in time polynomial in m. -/
theorem stFlip : StFlip := stFlip_of stVars

end CircuitLowerBound
