/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import EightSquareStatement
public import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The eight-square identity (Degen 1818, Graves 1843): the rule of signs

This file proves `Eight.signs : Eight.Signs` (the rule of signs, the first display of the
statement), along the appendix «Proof of the eight-square identity» of the paper (Appendix F). In
quotations, [the rule of signs] stands for the number of that display.
Every step of that proof is a lemma here, with its sentence quoted, and the lemmas are put together
as in the text. Each step is proved by the reason that the text gives for it; no step runs through
the values of a block. Only two facts on single bits are read off their values: a ⊕ b ≡ a + b modulo
2 (`toNat_xor`, the four values of two bits) and b² = b (`toNat_mul_self`).
At the head of the file are small facts on ⊕ for the other files: the laws of ⊕ on blocks, which
come bit by bit from the laws of ⊕ on a bit. -/

public section

namespace Eight

open Finset

/-! ## Small facts on ⊕ -/

/-- Two blocks with the same three bits are equal. -/
theorem block_ext {p q : Block} (h1 : p.1 = q.1) (h2 : p.2.1 = q.2.1) (h3 : p.2.2 = q.2.2) : p = q := Prod.ext h1 (Prod.ext h2 h3)

/-- The three bits of p ⊕ q (by definition). -/
theorem bxor_bit1 (p q : Block) : (bxor p q).1 = (p.1 ^^ q.1) := rfl
@[inherit_doc bxor_bit1] theorem bxor_bit2 (p q : Block) : (bxor p q).2.1 = (p.2.1 ^^ q.2.1) := rfl
@[inherit_doc bxor_bit1] theorem bxor_bit3 (p q : Block) : (bxor p q).2.2 = (p.2.2 ^^ q.2.2) := rfl

/-- p ⊕ q = q ⊕ p: the same law in each bit. -/
theorem bxor_comm (p q : Block) : bxor p q = bxor q p := block_ext (Bool.xor_comm _ _) (Bool.xor_comm _ _) (Bool.xor_comm _ _)

/-- (p ⊕ q) ⊕ r = p ⊕ (q ⊕ r): the same law in each bit. -/
theorem bxor_assoc (p q r : Block) : bxor (bxor p q) r = bxor p (bxor q r) := block_ext (Bool.xor_assoc _ _ _) (Bool.xor_assoc _ _ _) (Bool.xor_assoc _ _ _)

/-- p ⊕ p = 000: the same law in each bit. -/
theorem bxor_self (p : Block) : bxor p p = (false, false, false) := block_ext (Bool.xor_self _) (Bool.xor_self _) (Bool.xor_self _)

/-- p ⊕ 000 = p: the same law in each bit. -/
theorem bxor_zero (p : Block) : bxor p (false, false, false) = p := block_ext (Bool.xor_false _) (Bool.xor_false _) (Bool.xor_false _)

/-- (p ⊕ d) ⊕ d = p. -/
theorem bxor_bxor_cancel (p d : Block) : bxor (bxor p d) d = p := by rw [bxor_assoc, bxor_self, bxor_zero]

/-- p ⊕ (p ⊕ q) = q. -/
theorem bxor_cancel_left (p q : Block) : bxor p (bxor p q) = q := by rw [← bxor_assoc, bxor_self, bxor_comm, bxor_zero]

/-! ## The rule of signs -/

/-- «Let d = q ⊕ q'; it is not 000 because q ≠ q'»: if d were 000, then q' = q ⊕ (q ⊕ q') = q ⊕ 000 =
q. -/
theorem d_ne_zero {q q' : Block} (h : q ≠ q') : bxor q q' ≠ (false, false, false) := fun h0 =>
  h (by rw [← bxor_cancel_left q q', h0, bxor_zero])

/-- «and it equals p ⊕ p' because p ⊕ q = p' ⊕ q'»: q ⊕ q' = p ⊕ (p ⊕ q) ⊕ q' = p ⊕ (p' ⊕ q') ⊕ q' =
p ⊕ p'. -/
theorem d_eq {p q p' q' : Block} (h : bxor p q = bxor p' q') : bxor q q' = bxor p p' :=
  calc bxor q q' = bxor (bxor p (bxor p q)) q' := by rw [bxor_cancel_left]
    _ = bxor p (bxor (bxor p' q') q') := by rw [h, bxor_assoc]
    _ = bxor p p' := by rw [bxor_bxor_cancel]

/-- «So p' = p ⊕ d». -/
theorem p'_eq {p q p' q' : Block} (h : bxor p q = bxor p' q') : p' = bxor p (bxor q q') := by
  rw [d_eq h, bxor_cancel_left]

/-- «and q' = q ⊕ d». -/
theorem q'_eq (q q' : Block) : q' = bxor q (bxor q q') := (bxor_cancel_left q q').symm

/-- «and compute modulo 2»: on bits, a ⊕ b ≡ a + b. (The definition of ⊕ on a bit: the four values
of (a,b).) -/
theorem toNat_xor (a b : Bool) : (a ^^ b).toNat ≡ a.toNat + b.toNat [MOD 2] := by revert a b; decide

/-- Equal numbers are congruent modulo 2. -/
theorem modEq_of_eq {a b : ℕ} (h : a = b) : a ≡ b [MOD 2] := h ▸ Nat.ModEq.rfl

/-- What stands beside q₁, q₂ and q₃ in φ(p,q): p₁ + p₂p₃, p₁ + p₂ + p₁p₃ and p₁ + p₂ + p₃ + p₁p₂. -/
@[expose] def lin1 (p : Block) : ℕ := p.1.toNat + p.2.1.toNat * p.2.2.toNat
@[expose, inherit_doc lin1] def lin2 (p : Block) : ℕ := p.1.toNat + p.2.1.toNat + p.1.toNat * p.2.2.toNat
@[expose, inherit_doc lin1] def lin3 (p : Block) : ℕ := p.1.toNat + p.2.1.toNat + p.2.2.toNat + p.1.toNat * p.2.1.toNat

/-- «Every term of φ(p,q) contains exactly one bit of q»: collected by that bit, φ(p,q) = (p₁ +
p₂p₃)·q₁ + (p₁ + p₂ + p₁p₃)·q₂ + (p₁ + p₂ + p₃ + p₁p₂)·q₃. -/
theorem phi_linear (p q : Block) : phi p q = lin1 p * q.1.toNat + lin2 p * q.2.1.toNat + lin3 p * q.2.2.toNat := by
  unfold phi lin1 lin2 lin3; ring

/-- For one bit: c·a + c·(a ⊕ b) ≡ c·a + c·(a + b) = 2·c·a + c·b ≡ c·b (modulo 2). -/
theorem mul_add_mul_xor (c : ℕ) (a b : Bool) : c * a.toNat + c * (a ^^ b).toNat ≡ c * b.toNat [MOD 2] := by
  have h : c * a.toNat + c * (a ^^ b).toNat ≡ c * a.toNat + c * (a.toNat + b.toNat) [MOD 2] := ((toNat_xor a b).mul_left c).add_left _
  have e : c * a.toNat + c * (a.toNat + b.toNat) = 2 * (c * a.toNat) + c * b.toNat := by ring
  rw [e] at h
  unfold Nat.ModEq at *
  omega

/-- «so φ(p,q) + φ(p,q ⊕ d) ≡ φ(p,d) for all p» (modulo 2): the line before for each of the three
bits of q. -/
theorem phi_add_phi_bxor (p q d : Block) : phi p q + phi p (bxor q d) ≡ phi p d [MOD 2] := by
  have h1 := mul_add_mul_xor (lin1 p) q.1 d.1
  have h2 := mul_add_mul_xor (lin2 p) q.2.1 d.2.1
  have h3 := mul_add_mul_xor (lin3 p) q.2.2 d.2.2
  rw [phi_linear p q, phi_linear p (bxor q d), phi_linear p d, bxor_bit1, bxor_bit2, bxor_bit3]
  unfold Nat.ModEq at *
  omega

/-- «and the sum is φ(p,d) + φ(p ⊕ d,d)»: the line before, used for p and for p ⊕ d. -/
theorem four_phi (p q d : Block) :
    phi p q + phi (bxor p d) (bxor q d) + phi p (bxor q d) + phi (bxor p d) q ≡ phi p d + phi (bxor p d) d [MOD 2] := by
  have h1 := phi_add_phi_bxor p q d
  have h2 := phi_add_phi_bxor (bxor p d) q d
  unfold Nat.ModEq at *
  omega

/-- The first part of φ: Σ_{1 ≤ i ≤ j ≤ 3} p_i q_j. -/
@[expose] def phiQ (p q : Block) : ℕ :=
  p.1.toNat * q.1.toNat + p.1.toNat * q.2.1.toNat + p.1.toNat * q.2.2.toNat + p.2.1.toNat * q.2.1.toNat + p.2.1.toNat * q.2.2.toNat
    + p.2.2.toNat * q.2.2.toNat

/-- The three other terms of φ: q₁p₂p₃, p₁q₂p₃ and p₁p₂q₃. -/
@[expose] def phi1 (p q : Block) : ℕ := q.1.toNat * p.2.1.toNat * p.2.2.toNat
@[expose, inherit_doc phi1] def phi2 (p q : Block) : ℕ := p.1.toNat * q.2.1.toNat * p.2.2.toNat
@[expose, inherit_doc phi1] def phi3 (p q : Block) : ℕ := p.1.toNat * p.2.1.toNat * q.2.2.toNat

/-- φ is the sum of its four parts (by definition). -/
theorem phi_parts (p q : Block) : phi p q = phiQ p q + phi1 p q + phi2 p q + phi3 p q := rfl

/-- The changes of the three terms of degree 3: d₁(p₂d₃ + d₂p₃ + d₂d₃), d₂(p₁d₃ + d₁p₃ + d₁d₃) and
d₃(p₁d₂ + d₁p₂ + d₁d₂). -/
@[expose] def chg1 (p d : Block) : ℕ := d.1.toNat * (p.2.1.toNat * d.2.2.toNat + d.2.1.toNat * p.2.2.toNat + d.2.1.toNat * d.2.2.toNat)
@[expose, inherit_doc chg1] def chg2 (p d : Block) : ℕ := d.2.1.toNat * (p.1.toNat * d.2.2.toNat + d.1.toNat * p.2.2.toNat + d.1.toNat * d.2.2.toNat)
@[expose, inherit_doc chg1] def chg3 (p d : Block) : ℕ := d.2.2.toNat * (p.1.toNat * d.2.1.toNat + d.1.toNat * p.2.1.toNat + d.1.toNat * d.2.1.toNat)

/-- «Replacing p by p ⊕ d changes Σ_{1 ≤ i ≤ j ≤ 3} p_i d_j by Σ_{1 ≤ i ≤ j ≤ 3} d_i d_j» (modulo 2).
In this and the next three: put p_i + d_i for each bit of p ⊕ d (toNat_xor) and multiply out. -/
theorem change_Q (p d : Block) : phiQ (bxor p d) d ≡ phiQ p d + phiQ d d [MOD 2] := by
  have h1 := toNat_xor p.1 d.1
  have h2 := toNat_xor p.2.1 d.2.1
  have h3 := toNat_xor p.2.2 d.2.2
  have h := (((((h1.mul_right d.1.toNat).add (h1.mul_right d.2.1.toNat)).add (h1.mul_right d.2.2.toNat)).add (h2.mul_right d.2.1.toNat)).add
    (h2.mul_right d.2.2.toNat)).add (h3.mul_right d.2.2.toNat)
  refine Nat.ModEq.trans h (modEq_of_eq ?_)
  unfold phiQ; ring

/-- «and it changes d₁p₂p₃ by d₁(p₂d₃ + d₂p₃ + d₂d₃)»: d₁(p₂ + d₂)(p₃ + d₃) = d₁p₂p₃ + d₁(p₂d₃ +
d₂p₃ + d₂d₃). -/
theorem change_1 (p d : Block) : phi1 (bxor p d) d ≡ phi1 p d + chg1 p d [MOD 2] := by
  refine Nat.ModEq.trans (((toNat_xor p.2.1 d.2.1).mul_left d.1.toNat).mul (toNat_xor p.2.2 d.2.2)) (modEq_of_eq ?_)
  unfold phi1 chg1; ring

/-- «p₁d₂p₃ by d₂(p₁d₃ + d₁p₃ + d₁d₃)»: (p₁ + d₁)d₂(p₃ + d₃) = p₁d₂p₃ + d₂(p₁d₃ + d₁p₃ + d₁d₃). -/
theorem change_2 (p d : Block) : phi2 (bxor p d) d ≡ phi2 p d + chg2 p d [MOD 2] := by
  refine Nat.ModEq.trans (((toNat_xor p.1 d.1).mul_right d.2.1.toNat).mul (toNat_xor p.2.2 d.2.2)) (modEq_of_eq ?_)
  unfold phi2 chg2; ring

/-- «and p₁p₂d₃ by d₃(p₁d₂ + d₁p₂ + d₁d₂)»: (p₁ + d₁)(p₂ + d₂)d₃ = p₁p₂d₃ + d₃(p₁d₂ + d₁p₂ + d₁d₂). -/
theorem change_3 (p d : Block) : phi3 (bxor p d) d ≡ phi3 p d + chg3 p d [MOD 2] := by
  refine Nat.ModEq.trans (((toNat_xor p.1 d.1).mul (toNat_xor p.2.1 d.2.1)).mul_right d.2.2.toNat) (modEq_of_eq ?_)
  unfold phi3 chg3; ring

/-- «In these three changes each of p₁d₂d₃, p₂d₁d₃, p₃d₁d₂ occurs twice and d₁d₂d₃ three times». -/
theorem three_changes (p d : Block) : chg1 p d + chg2 p d + chg3 p d
    = 2 * (p.1.toNat * d.2.1.toNat * d.2.2.toNat + p.2.1.toNat * d.1.toNat * d.2.2.toNat + p.2.2.toNat * d.1.toNat * d.2.1.toNat)
      + 3 * (d.1.toNat * d.2.1.toNat * d.2.2.toNat) := by
  unfold chg1 chg2 chg3; ring

/-- «So φ(p,d) + φ(p ⊕ d,d) is congruent to the sum of the four changes». -/
theorem phi_add_phi_shift (p d : Block) : phi p d + phi (bxor p d) d ≡ phiQ d d + chg1 p d + chg2 p d + chg3 p d [MOD 2] := by
  have h0 := change_Q p d
  have h1 := change_1 p d
  have h2 := change_2 p d
  have h3 := change_3 p d
  rw [phi_parts, phi_parts]
  unfold Nat.ModEq at *
  omega

/-- «d_i² = d_i»: the square of a bit is the bit (0² = 0 and 1² = 1). -/
theorem toNat_mul_self (b : Bool) : b.toNat * b.toNat = b.toNat := by cases b <;> rfl

/-- «With d_i² = d_i», for the first change: Σ_{1 ≤ i ≤ j ≤ 3} d_i d_j = d₁ + d₂ + d₃ + d₁d₂ + d₁d₃ +
d₂d₃. -/
theorem phiQ_self (d : Block) : phiQ d d
    = d.1.toNat + d.2.1.toNat + d.2.2.toNat + d.1.toNat * d.2.1.toNat + d.1.toNat * d.2.2.toNat + d.2.1.toNat * d.2.2.toNat := by
  unfold phiQ
  rw [toNat_mul_self d.1, toNat_mul_self d.2.1, toNat_mul_self d.2.2]
  ring

/-- «in which the terms that occur twice cancel. With d_i² = d_i this is d₁ + d₂ + d₃ + d₁d₂ + d₁d₃ +
d₂d₃ + d₁d₂d₃». -/
theorem four_changes (p d : Block) : phiQ d d + chg1 p d + chg2 p d + chg3 p d
    ≡ d.1.toNat + d.2.1.toNat + d.2.2.toNat + d.1.toNat * d.2.1.toNat + d.1.toNat * d.2.2.toNat + d.2.1.toNat * d.2.2.toNat
      + d.1.toNat * d.2.1.toNat * d.2.2.toNat [MOD 2] := by
  have h := three_changes p d
  rw [phiQ_self]
  unfold Nat.ModEq
  omega

/-- «≡ 1 + (1 + d₁)(1 + d₂)(1 + d₃)». -/
theorem seven_terms (d : Block) :
    d.1.toNat + d.2.1.toNat + d.2.2.toNat + d.1.toNat * d.2.1.toNat + d.1.toNat * d.2.2.toNat + d.2.1.toNat * d.2.2.toNat
      + d.1.toNat * d.2.1.toNat * d.2.2.toNat ≡ 1 + (1 + d.1.toNat) * (1 + d.2.1.toNat) * (1 + d.2.2.toNat) [MOD 2] := by
  have h : 1 + (1 + d.1.toNat) * (1 + d.2.1.toNat) * (1 + d.2.2.toNat)
      = 2 + (d.1.toNat + d.2.1.toNat + d.2.2.toNat + d.1.toNat * d.2.1.toNat + d.1.toNat * d.2.2.toNat + d.2.1.toNat * d.2.2.toNat
        + d.1.toNat * d.2.1.toNat * d.2.2.toNat) := by ring
  rw [h]
  unfold Nat.ModEq
  omega

/-- «some d_i is 1», since d is not 000. -/
theorem exists_bit {d : Block} (h : d ≠ (false, false, false)) : d.1 = true ∨ d.2.1 = true ∨ d.2.2 = true := by
  by_contra hn
  simp only [not_or, Bool.not_eq_true] at hn
  exact h (block_ext hn.1 hn.2.1 hn.2.2)

/-- «which is 1 because some d_i is 1»: the factor 1 + d_i is then 2, so the product is even. -/
theorem one_add_prod {d : Block} (h : d ≠ (false, false, false)) :
    1 + (1 + d.1.toNat) * (1 + d.2.1.toNat) * (1 + d.2.2.toNat) ≡ 1 [MOD 2] := by
  have e : ∃ n, (1 + d.1.toNat) * (1 + d.2.1.toNat) * (1 + d.2.2.toNat) = 2 * n := by
    rcases exists_bit h with h1 | h1 | h1
    · exact ⟨(1 + d.2.1.toNat) * (1 + d.2.2.toNat), by rw [h1, Bool.toNat_true]; ring⟩
    · exact ⟨(1 + d.1.toNat) * (1 + d.2.2.toNat), by rw [h1, Bool.toNat_true]; ring⟩
    · exact ⟨(1 + d.1.toNat) * (1 + d.2.1.toNat), by rw [h1, Bool.toNat_true]; ring⟩
  obtain ⟨n, hn⟩ := e
  rw [hn]
  unfold Nat.ModEq
  omega

/-- «We have to show that φ(p,q) + φ(p ⊕ d,q ⊕ d) + φ(p,q ⊕ d) + φ(p ⊕ d,q) is odd»: the chain of
the congruences above. -/
theorem four_phi_odd (p q : Block) {d : Block} (h : d ≠ (false, false, false)) :
    Odd (phi p q + phi (bxor p d) (bxor q d) + phi p (bxor q d) + phi (bxor p d) q) :=
  Nat.odd_iff.2 ((four_phi p q d).trans ((phi_add_phi_shift p d).trans ((four_changes p d).trans ((seven_terms d).trans (one_add_prod h)))))

/-- Why oddness is what «we have to show»: (−1)^m + (−1)^n = 0 if m + n is odd. -/
theorem neg_one_pow_add_neg_one_pow {m n : ℕ} (h : Odd (m + n)) : (-1 : ℤ) ^ m + (-1) ^ n = 0 := by
  rcases Nat.even_or_odd m with hm | hm
  · have hn : Odd n := by
      rcases Nat.even_or_odd n with hn | hn
      · exact absurd h (Nat.not_odd_iff_even.2 (hm.add hn))
      · exact hn
    rw [hm.neg_one_pow, hn.neg_one_pow]; norm_num
  · have hn : Even n := by
      rcases Nat.even_or_odd n with hn | hn
      · exact hn
      · exact absurd h (Nat.not_odd_iff_even.2 (hm.add_odd hn))
    rw [hm.neg_one_pow, hn.neg_one_pow]; norm_num

/-- **The eight-square identity, first form** (the rule of signs): for all blocks p, q, p', q' with
p ⊕ q = p' ⊕ q' and q ≠ q', σ(p,q)σ(p',q') + σ(p,q')σ(p',q) = 0. Same proof as in the paper, step by
step. -/
theorem signs : Signs := by
  intro p q p' q' h hq
  have hodd := four_phi_odd p q (d_ne_zero hq)
  rw [← p'_eq h, ← q'_eq q q'] at hodd
  unfold sigma
  rw [← pow_add, ← pow_add]
  exact neg_one_pow_add_neg_one_pow (by rwa [← add_assoc])


variable {S : Type} [CommRing S]

end Eight
