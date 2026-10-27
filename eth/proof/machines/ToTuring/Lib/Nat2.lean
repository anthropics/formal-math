/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.Nat1b

/-! Polynomial time for binary numbers: product, quotient, remainder, powers. Product, quotient and
remainder are each one fold
over the binary digits, and a power with a unary exponent is one fold over a list of that length. In
every round the
intermediate values grow by at most a polynomial in the length of the input. -/

@[expose] public section

namespace Groundwork.PolyT

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

/-! ### Lengths of sums, doubles and products -/

/-- The word of c + c + z is longer than those of c and z together by at most 4. -/
theorem len_dbl_add_le (c z : ℕ) : len (c + c + z) ≤ len c + len z + 4 := by
  have h : Nat.size (c + c + z) ≤ Nat.size c + Nat.size z + 2 := by
    rw [Nat.size_le]
    have hc := Nat.lt_size_self c
    have hz := Nat.lt_size_self z
    have h1 : 2 ^ Nat.size c ≤ 2 ^ (Nat.size c + Nat.size z) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ Nat.size z ≤ 2 ^ (Nat.size c + Nat.size z) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ (Nat.size c + Nat.size z + 2) = 4 * 2 ^ (Nat.size c + Nat.size z) := by ring
    omega
  simp only [len_nat]
  omega

/-- A number that is at most 2c + 1 has at most one binary digit more than c. -/
theorem len_le_of_le_dbl {a c : ℕ} (h : a ≤ c + c + 1) : len a ≤ len c + 3 := by
  have h' : Nat.size a ≤ Nat.size c + 1 := by
    rw [Nat.size_le]
    have hc := Nat.lt_size_self c
    have h3 : 2 ^ (Nat.size c + 1) = 2 * 2 ^ Nat.size c := by ring
    omega
  simp only [len_nat]
  omega

/-- The word of a product is at most as long as the words of the factors together. -/
theorem len_mul_le (a b : ℕ) : len (a * b) ≤ len a + len b := by
  have h : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
    rw [Nat.size_le, pow_add]
    exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)
  simp only [len_nat]
  omega

/-! ### Product -/

/-- The product, read off the binary digits of the second factor from the top: double, and add m if
the digit is 1. -/
theorem foldr_bits_mul (m n : ℕ) :
    (Nat.bits n).foldr (fun b acc => acc + acc + bif b then m else 0) 0 = m * n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
    rw [Nat.bits_append_bit _ _ h, List.foldr_cons, ih]
    cases b <;> simp [Nat.bit] <;> ring

/-- The product of two numbers in binary is polynomial-time. -/
@[fun_prop] theorem mul {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x * g x) := by
  obtain ⟨_, t, ht, _, _, hlen⟩ := hf.elim
  have h : PolyT (fun x => (Nat.bits (g x)).reverse.foldl (fun acc b => acc + acc + bif b then f x else 0) 0) := by
    refine foldl_add (l := fun x => (Nat.bits (g x)).reverse) (a := fun _ => 0)
      (g := fun x acc b => acc + acc + bif b then f x else 0) (by fun_prop) (by fun_prop) (by fun_prop)
      ⟨fun n => t n + 4, ht.add (PB.const 4), fun x c e _ => ?_⟩
    have h1 := len_dbl_add_le c (bif e then f x else 0)
    have h2 : len (bif e then f x else 0) ≤ len (f x) := len_nat_mono (by cases e <;> simp)
    have h3 := hlen x
    show len (c + c + bif e then f x else 0) ≤ len c + (t (len x) + 4)
    omega
  exact h.congr fun x => by rw [List.foldl_reverse]; exact foldr_bits_mul _ _

/-! ### Quotient and remainder -/

/-- One round of the division by d taught at school, in base 2: s is (quotient, remainder) of the
digits read so far, b is the
next digit. -/
def divStep (d : ℕ) (s : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  if d ≤ s.2 + s.2 + b.toNat then (s.1 + s.1 + 1, s.2 + s.2 + b.toNat - d) else (s.1 + s.1, s.2 + s.2 + b.toNat)

/-- A round takes quotient and remainder of n to those of 2n + b. -/
theorem divStep_spec {d : ℕ} (hd : 0 < d) (b : Bool) (n : ℕ) :
    divStep d (n / d, n % d) b = (Nat.bit b n / d, Nat.bit b n % d) := by
  have h1 := Nat.div_add_mod n d
  have h2 := Nat.mod_lt n hd
  have hb : Nat.bit b n = n + n + b.toNat := by cases b <;> simp [Nat.bit] <;> omega
  have hb1 : b.toNat ≤ 1 := Bool.toNat_le b
  have key : ∀ q' r', r' + d * q' = Nat.bit b n → r' < d → (q', r') = (Nat.bit b n / d, Nat.bit b n % d) := by
    intro q' r' e l
    obtain ⟨e1, e2⟩ := (Nat.div_mod_unique hd).2 ⟨e, l⟩
    rw [e1, e2]
  generalize n / d = q at *
  generalize n % d = r at *
  unfold divStep
  dsimp only
  split_ifs with h
  · apply key
    · have : d * (q + q + 1) = d * q + d * q + d := by ring
      omega
    · omega
  · apply key
    · have : d * (q + q) = d * q + d * q := by ring
      omega
    · omega

/-- The rounds over all digits of n, from the top, give quotient and remainder of n. -/
theorem foldr_bits_divStep {d : ℕ} (hd : 0 < d) (n : ℕ) :
    (Nat.bits n).foldr (fun b s => divStep d s b) (0, 0) = (n / d, n % d) := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
    rw [Nat.bits_append_bit _ _ h, List.foldr_cons, ih, divStep_spec hd]

/-- A round makes the word of the pair longer by at most 6. -/
theorem len_divStep_le (d : ℕ) (s : ℕ × ℕ) (b : Bool) : len (divStep d s b) ≤ len s + 6 := by
  obtain ⟨q, r⟩ := s
  have hb1 : b.toNat ≤ 1 := Bool.toNat_le b
  unfold divStep
  split_ifs with h
  · have h1 := len_le_of_le_dbl (a := q + q + 1) (c := q) le_rfl
    have h2 := len_le_of_le_dbl (a := r + r + b.toNat - d) (c := r) (by omega)
    simp only [len_pair]
    omega
  · have h1 := len_le_of_le_dbl (a := q + q) (c := q) (by omega)
    have h2 := len_le_of_le_dbl (a := r + r + b.toNat) (c := r) (by omega)
    simp only [len_pair]
    omega

/-- Quotient and remainder together, as one fold. -/
theorem divFold {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => (Nat.bits (f x)).reverse.foldl (divStep (g x)) (0, 0)) := by
  refine foldl_add (l := fun x => (Nat.bits (f x)).reverse) (a := fun _ => ((0, 0) : ℕ × ℕ))
    (g := fun x => divStep (g x)) (by fun_prop) (by fun_prop) (by unfold divStep; fun_prop)
    ⟨fun _ => 6, PB.const 6, fun x c e _ => len_divStep_le _ _ _⟩

/-- The quotient is polynomial-time; the divisor 0 is a separate case (the quotient is then 0). -/
@[fun_prop] theorem div {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x / g x) := by
  have h := divFold hf hg
  have h' : PolyT (fun x => if g x = 0 then 0 else ((Nat.bits (f x)).reverse.foldl (divStep (g x)) (0, 0)).1) := by
    fun_prop
  refine h'.congr fun x => ?_
  split_ifs with h0
  · rw [h0, Nat.div_zero]
  · rw [List.foldl_reverse, foldr_bits_divStep (Nat.pos_of_ne_zero h0)]

/-- The remainder is polynomial-time; the divisor 0 is a separate case (the remainder is then the
number itself). -/
@[fun_prop] theorem mod {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x % g x) := by
  have h := divFold hf hg
  have h' : PolyT (fun x => if g x = 0 then f x else ((Nat.bits (f x)).reverse.foldl (divStep (g x)) (0, 0)).2) := by
    fun_prop
  refine h'.congr fun x => ?_
  split_ifs with h0
  · rw [h0, Nat.mod_zero]
  · rw [List.foldl_reverse, foldr_bits_divStep (Nat.pos_of_ne_zero h0)]

/-! ### Powers -/

/-- A power with a fixed exponent is polynomial-time: k products. -/
@[fun_prop] theorem pow_const {f : α → ℕ} (hf : PolyT f) (k : ℕ) :
    PolyT (fun x => f x ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using const (α := α) 1
  | succ k ih => simpa only [pow_succ] using mul ih hf

/-- Multiplying n times by b multiplies by b ^ n. -/
theorem foldl_replicate_mul (b n a : ℕ) :
    (List.replicate n ()).foldl (fun acc _ => acc * b) a = a * b ^ n := by
  induction n generalizing a with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.foldl_cons, ih, pow_succ']; ring

/-- A power is polynomial-time if its exponent can be written in unary: every round makes the word
longer by at most the
length of the word of the base. -/
theorem pow_unary {b e : α → ℕ} (hb : PolyT b) (he : Unary e) :
    PolyT (fun x => b x ^ e x) := by
  obtain ⟨_, t, ht, _, _, hlen⟩ := hb.elim
  have h : PolyT (fun x => (List.replicate (e x) ()).foldl (fun acc _ => acc * b x) 1) := by
    refine foldl_add (l := fun x => List.replicate (e x) ()) (a := fun _ => 1)
      (g := fun x acc _ => acc * b x) he (by fun_prop) (by fun_prop)
      ⟨t, ht, fun x c e _ => ?_⟩
    have h1 := len_mul_le c (b x)
    have h3 := hlen x
    omega
  exact h.congr fun x => by rw [foldl_replicate_mul, one_mul]

/-- The case of `pow_unary` with base 2. -/
theorem two_pow {e : α → ℕ} (he : Unary e) :
    PolyT (fun x => 2 ^ e x) :=
  pow_unary (const 2) he

/-! ### a / b ^ q with q in binary -/

/-- Counting up to q along a list. -/
theorem foldl_count_min {ι : Type} (q : ℕ) (l : List ι) (k : ℕ) (hk : k ≤ q) :
    l.foldl (fun (acc : List Unit) _ => if acc.length < q then () :: acc else acc) (List.replicate k ()) =
      List.replicate (min q (k + l.length)) () := by
  induction l generalizing k with
  | nil => simp [hk]
  | cons e l ih =>
    rw [List.foldl_cons, List.length_replicate]
    split_ifs with h
    · rw [← List.replicate_succ, ih (k + 1) h, List.length_cons]
      congr 2
      omega
    · rw [ih k hk, List.length_cons]
      congr 1
      omega

/-- The smaller of a number in binary and the length of a list can be written in unary. -/
theorem unary_min_length {q : α → ℕ} {l : α → List β} (hq : PolyT q) (hl : PolyT l) :
    Unary (fun x => min (q x) (l x).length) := by
  have h : PolyT (fun x => (l x).foldl (fun (acc : List Unit) _ => if acc.length < q x then () :: acc else acc) []) := by
    refine foldl_add (l := l) (a := fun _ => ([] : List Unit))
      (g := fun x (acc : List Unit) _ => if acc.length < q x then () :: acc else acc) hl (by fun_prop) (by fun_prop)
      ⟨fun _ => 4, PB.const 4, fun x c e _ => ?_⟩
    split_ifs
    · simp only [len_units, List.length_cons]
      omega
    · omega
  refine h.congr fun x => ?_
  have := foldl_count_min (q x) (l x) 0 (Nat.zero_le _)
  simpa using this

/-- In a / b ^ q the exponent may be cut off at the number of binary digits of a. -/
theorem div_pow_min_size (a b q : ℕ) : a / b ^ min q (Nat.size a) = a / b ^ q := by
  rcases le_total q (Nat.size a) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    rcases Nat.lt_or_ge b 2 with hb | hb
    · interval_cases b
      · rcases Nat.eq_zero_or_pos (Nat.size a) with h0 | h0
        · rw [Nat.size_eq_zero.1 h0]; simp
        · rw [zero_pow (by omega), zero_pow (by omega)]
      · simp
    · have h1 : a < b ^ Nat.size a :=
        lt_of_lt_of_le (Nat.lt_size_self a) (Nat.pow_le_pow_left hb _)
      have h2 : a < b ^ q := lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) h)
      rw [Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2]

/-- a / b ^ q is polynomial-time with all three numbers in binary: the exponent is first cut off at
the number of binary
digits of a, which can be written in unary. -/
@[fun_prop] theorem div_pow {a b q : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hq : PolyT q) :
    PolyT (fun x => a x / b x ^ q x) := by
  have hu : Unary (fun x => min (q x) (Nat.bits (a x)).length) := unary_min_length hq (by fun_prop)
  have h := div ha (pow_unary hb hu)
  exact h.congr fun x => by rw [Nat.size_eq_bits_len, div_pow_min_size]

end Groundwork.PolyT
