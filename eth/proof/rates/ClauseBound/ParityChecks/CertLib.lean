/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.RunDefs
public import ClauseBound.Alg.CertGridG

/-! # More closure lemmas for polynomial-time functions

Polynomial time (PolyT) for operations on numbers that the closure lemmas of
proof/machines/ToTuring/Lib and proof/rates/PaddedDescent/F/FuelCert.lean do not cover: the
remainder of an integer modulo a natural number, powers of an
integer with the exponent in unary, products over a range, binomial coefficients with the lower
number in unary, factorials, and the two logarithms to base 2. The parameters of the choice of the
checks are a structure, `Par`, which is never passed as data: a certificate is stated for a function
q of the context whose five components are given in unary (`QU q`). -/

public section

namespace ClauseBound.ParityChecks.CertLib

open Groundwork PaddedDescent.F

variable {α : Type} [Enc α]

/-- «Given in unary» passes to a function with the same values. -/
theorem unary_congr {f g : α → ℕ} (h : Unary f) (e : ∀ x, f x = g x) : Unary g := by
  obtain rfl : f = g := funext e
  exact h

/-- The smaller of any number and a number given in unary is given in unary. -/
theorem unary_min_right {f g : α → ℕ} (hf : PolyT f) (hg : Unary g) : Unary fun x => min (f x) (g x) :=
  Unary.of_le hg (PolyT.min' hf hg.poly) fun _ => min_le_right _ _

/-! ### Integers -/

/-- The remainder of an integer modulo a natural number, by cases on the sign. -/
theorem emod_natCast (a : ℤ) (b : ℕ) :
    a % (b : ℤ) = if 0 ≤ a then ((a.toNat % b : ℕ) : ℤ) else if b = 0 then a else ((b - 1 - (a.natAbs - 1) % b : ℕ) : ℤ) := by
  cases a with
  | ofNat m =>
    have h0 : (0 : ℤ) ≤ Int.ofNat m := Int.natCast_nonneg m
    rw [if_pos h0]
    simp
  | negSucc m =>
    have h0 : ¬ (0 : ℤ) ≤ Int.negSucc m := by simp
    rw [if_neg h0]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · rw [if_neg (by omega), Int.negSucc_emod m (by exact_mod_cast hb), ← Int.natCast_mod]
      have h1 := Nat.mod_lt m hb
      have h2 : (Int.negSucc m).natAbs - 1 = m := by simp
      rw [h2]
      omega

/-- The remainder of an integer modulo a natural number is polynomial-time. -/
theorem modZ_polyT {a : α → ℤ} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => a x % (b x : ℤ) := by
  have h1 : PolyT fun x => (a x).toNat % b x := PolyT.mod (PolyT.toNat ha) hb
  have h2 : PolyT fun x => b x - 1 - ((a x).natAbs - 1) % b x :=
    PolyT.sub (PolyT.sub hb (PolyT.const 1)) (PolyT.mod (PolyT.sub (PolyT.natAbs ha) (PolyT.const 1)) hb)
  exact (PolyT.ite' (PolyT.decide_leZ (PolyT.const 0) ha) (PolyT.natCast h1)
    (PolyT.ite' (PolyT.decide_eq hb (PolyT.const 0)) ha (PolyT.natCast h2))).congr fun x => (emod_natCast _ _).symm

/-- The quotient of an integer by a natural number, rounded down, by cases on the sign. -/
theorem ediv_natCast (a : ℤ) (b : ℕ) :
    a / (b : ℤ) = if 0 ≤ a then ((a.toNat / b : ℕ) : ℤ) else if b = 0 then 0 else -(((a.natAbs - 1) / b + 1 : ℕ) : ℤ) := by
  cases a with
  | ofNat m =>
    have h0 : (0 : ℤ) ≤ Int.ofNat m := Int.natCast_nonneg m
    rw [if_pos h0]
    simp
  | negSucc m =>
    have h0 : ¬ (0 : ℤ) ≤ Int.negSucc m := by simp
    rw [if_neg h0]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have h2 : (Int.negSucc m).natAbs - 1 = m := by simp
      rw [if_neg (by omega), Int.negSucc_ediv m (by exact_mod_cast hb), h2]
      push_cast
      rfl

/-- The quotient of an integer by a natural number is polynomial-time. -/
theorem divZ_polyT {a : α → ℤ} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => a x / (b x : ℤ) := by
  have h1 : PolyT fun x => (a x).toNat / b x := PolyT.div (PolyT.toNat ha) hb
  have h2 : PolyT fun x => ((a x).natAbs - 1) / b x + 1 := PolyT.add (PolyT.div (PolyT.sub (PolyT.natAbs ha) (PolyT.const 1)) hb) (PolyT.const 1)
  exact (PolyT.ite' (PolyT.decide_leZ (PolyT.const 0) ha) (PolyT.natCast h1)
    (PolyT.ite' (PolyT.decide_eq hb (PolyT.const 0)) (PolyT.const 0) (PolyT.negZ (PolyT.natCast h2)))).congr fun x => (ediv_natCast _ _).symm

/-- The quotient of an integer by a power of 2 is polynomial-time, for the exponent in unary. -/
theorem div_two_pow_polyT {a : α → ℤ} {k : α → ℕ} (ha : PolyT a) (hk : Unary k) : PolyT fun x => a x / 2 ^ k x :=
  (divZ_polyT ha (PolyT.pow_unary (PolyT.const 2) hk)).congr fun x => by push_cast; rfl

/-- The remainder of an integer modulo a power of 2 is polynomial-time, for the exponent in unary. -/
theorem mod_two_pow_polyT {a : α → ℤ} {k : α → ℕ} (ha : PolyT a) (hk : Unary k) : PolyT fun x => a x % 2 ^ k x :=
  (modZ_polyT ha (PolyT.pow_unary (PolyT.const 2) hk)).congr fun x => by push_cast; rfl

/-- A power of an integer is polynomial-time, for the exponent in unary. -/
theorem powZ_polyT {b : α → ℤ} {k : α → ℕ} (hb : PolyT b) (hk : Unary k) : PolyT fun x => b x ^ k x :=
  (prodL_polyT (f := fun x _ => b x) hk (PolyT.comp hb PolyT.id'.fst)).congr fun x => by
    rw [prodL_eq, Finset.prod_const, Finset.card_range]

/-- A product of integers over i < n is polynomial-time, for n in unary; the factors are only needed
for indices given in unary. -/
theorem prod_range_polyT {n : α → ℕ} {f : α → ℕ → ℤ} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => ∏ i ∈ Finset.range (n x), f x i :=
  (prodL_polyT (f := fun x j => f x (min j (n x))) hn hf).congr fun x => by
    rw [prodL_eq]
    exact Finset.prod_congr rfl fun j hj => by rw [min_eq_left (Finset.mem_range.1 hj).le]

/-- A list of values at i < n is polynomial-time, for n in unary; the values are only needed for
indices given in unary. -/
theorem map_range_polyT {β : Type} [Enc β] {n : α → ℕ} {f : α → ℕ → β} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => (List.range (n x)).map (f x) :=
  (PolyT.map (f := fun x k => f x (min k (n x))) hf (PolyT.range hn)).congr fun x =>
    List.map_congr_left fun k hk => by rw [min_eq_left (List.mem_range.1 hk).le]

/-! ### Natural numbers -/

/-- k! is polynomial-time, for k in unary. -/
theorem factorial_polyT {k : α → ℕ} (hk : Unary k) : PolyT fun x => (k x).factorial := by
  have h : PolyT fun x => (prodL (k x) fun i => ((i + 1 : ℕ) : ℤ)).toNat :=
    PolyT.toNat (prodL_polyT (f := fun _ i => ((i + 1 : ℕ) : ℤ)) hk (PolyT.natCast (PolyT.add PolyT.id'.snd (PolyT.const 1))))
  refine h.congr fun x => ?_
  rw [prodL_eq, ← Nat.cast_prod, Int.toNat_natCast, Finset.prod_range_add_one_eq_factorial]

/-- n(n − 1)⋯(n − k + 1) is polynomial-time, for k in unary. -/
theorem descFactorial_polyT {n k : α → ℕ} (hn : PolyT n) (hk : Unary k) : PolyT fun x => (n x).descFactorial (k x) := by
  have h : PolyT fun x => (prodL (k x) fun i => ((n x - i : ℕ) : ℤ)).toNat :=
    PolyT.toNat (prodL_polyT (f := fun x i => ((n x - i : ℕ) : ℤ)) hk (PolyT.natCast (PolyT.sub (PolyT.comp hn PolyT.id'.fst) PolyT.id'.snd)))
  refine h.congr fun x => ?_
  rw [prodL_eq, ← Nat.cast_prod, Int.toNat_natCast, Nat.descFactorial_eq_prod_range]

/-- The binomial coefficient C(n, k) is polynomial-time, for k in unary. -/
theorem choose_polyT {n k : α → ℕ} (hn : PolyT n) (hk : Unary k) : PolyT fun x => (n x).choose (k x) :=
  (PolyT.div (descFactorial_polyT hn hk) (factorial_polyT hk)).congr fun _ => (Nat.choose_eq_descFactorial_div_factorial _ _).symm

/-- ⌈log₂ n⌉ is the number of binary digits of n − 1. -/
theorem clog_two_eq (n : ℕ) : Nat.clog 2 n = Nat.size (n - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [Nat.clog_of_right_le_one (by omega)]
    have : n - 1 = 0 := by omega
    rw [this, Nat.size_zero]
  · refine le_antisymm ?_ ?_
    · rw [Nat.clog_le_iff_le_pow (by norm_num)]
      have := Nat.lt_size_self (n - 1)
      omega
    · rw [Nat.size_le]
      have := Nat.le_pow_clog (b := 2) (by norm_num) n
      omega

/-- ⌈log₂ n⌉ is polynomial-time. -/
theorem clog_polyT {n : α → ℕ} (hn : PolyT n) : PolyT fun x => Nat.clog 2 (n x) :=
  (PolyT.size' (PolyT.sub hn (PolyT.const 1))).congr fun _ => (clog_two_eq _).symm

/-- ⌈log₂ n⌉ is given in unary, for any polynomial-time n. -/
theorem clog_unary {n : α → ℕ} (hn : PolyT n) : Unary fun x => Nat.clog 2 (n x) :=
  unary_congr (Unary.of_length (PolyT.bits (PolyT.sub hn (PolyT.const 1)))) fun x => by rw [Nat.size_eq_bits_len, clog_two_eq]

/-- ⌊log₂ n⌋ is polynomial-time. -/
theorem log_polyT {n : α → ℕ} (hn : PolyT n) : PolyT fun x => Nat.log 2 (n x) :=
  (PolyT.log2' hn).congr fun _ => Nat.log2_eq_log_two

/-- ⌊log₂ n⌋ is given in unary if n is. -/
theorem log_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => Nat.log 2 (n x) :=
  Unary.of_le hn (log_polyT hn.poly) fun _ => Nat.log_le_self _ _

/-- The largest of f 0, …, f (n − 1) is given in unary if n and the numbers are; the numbers are
only needed for indices given in unary. -/
theorem sup_range_unary_min {n : α → ℕ} {f : α → ℕ → ℕ} (hn : Unary n) (hf : Unary fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    Unary fun x => (Finset.range (n x)).sup (f x) :=
  unary_congr (ClauseBound.Alg.CertGridG.sup_range_unary (f := fun x i => f x (min i (n x))) hn hf) fun x =>
    Finset.sup_congr rfl fun i hi => by rw [min_eq_left (Finset.mem_range.1 hi).le]

/-- A fold over 0, …, n − 1 only needs its step for indices at most n. -/
theorem foldl_range_min {γ : Type} (n : ℕ) (g : γ → ℕ → γ) (a : γ) : (List.range n).foldl (fun c i => g c (min i n)) a = (List.range n).foldl g a :=
  List.foldl_ext _ _ _ fun c i hi => by rw [min_eq_left (List.mem_range.1 hi).le]

/-! ### The parameters of the choice of the checks -/

/-- The five parameters are given in unary. -/
structure QU (q : α → Par) : Prop where
  m : Unary fun x => (q x).m
  nb : Unary fun x => (q x).nb
  r : Unary fun x => (q x).r
  i₀ : Unary fun x => (q x).i₀
  β : Unary fun x => (q x).β

/-- The property passes to a polynomial-time change of the context. -/
theorem QU.comp {β : Type} [Enc β] {q : α → Par} (hq : QU q) {g : β → α} (hg : PolyT g) : QU fun y => q (g y) :=
  ⟨hq.m.comp hg, hq.nb.comp hg, hq.r.comp hg, hq.i₀.comp hg, hq.β.comp hg⟩

end ClauseBound.ParityChecks.CertLib
