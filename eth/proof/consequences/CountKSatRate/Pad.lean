/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatRate.Interfaces
import CountKSat.Host
import ToTuring.Lib.Nat1b
import ToTuring.Lib.Nat2

/-! # Padding, for a function whose value is a word

Let B be a polynomial-time function of a bit string x and a list of units («the pad») whose value is
a bit string, and let e be a polynomial-time function from
bit strings to numbers. Then one Turing machine of Mathlib computes x ↦ B (x, pad of length 2^(e x))
within q·(|x| + 2^(e x) + 1)^q steps, for one constant q
(`stPaddedW`, which proves the interface statement `StPaddedW`). The stepped machine `padMW` starts
with a pad of length 1, doubles it e x times, one doubling per step,
and then applies B in a single step. The file follows proof/rates/PaddedDescent/Pad.lean, where the
value is one bit. The difference: the last state holds the value, so its size has
to be bounded, and the bound comes from the certificate of B. The host machine is that of
proof/consequences/CountKSat/Host.lean. -/

namespace CountKSatRate.Pad

open Groundwork PaddedDescent Turing

variable {e : List Bool → ℕ} {B : List Bool × List Unit → List Bool}

/-- Every part of the padding machine is polynomial-time if e and B are. -/
@[instance_reducible] def padMW_isPolyT (he : PolyT e) (hB : PolyT B) : IsPolyT (padMW e B) where
  enc := (inferInstance : Enc ((List Bool × List Unit) ⊕ List Bool))
  carried := (inferInstance : Carried ((List Bool × List Unit) ⊕ List Bool))
  init := (by fun_prop : PolyT fun x : List Bool => (.inl (x, [()]) : (List Bool × List Unit) ⊕ List Bool))
  step := (by fun_prop : PolyT fun s : (List Bool × List Unit) ⊕ List Bool =>
    s.elim (fun p => bif decide (e p.1 ≤ Nat.log2 p.2.length) then
      (.inr (B p) : (List Bool × List Unit) ⊕ List Bool) else .inl (p.1, p.2 ++ p.2)) fun w => .inr w)
  out := (by fun_prop : PolyT fun s : (List Bool × List Unit) ⊕ List Bool => s.elim (fun _ => none) fun w => some w)

/-- The size of a bit string. -/
theorem size_bools (x : List Bool) : size x = 2 * x.length + 1 := by
  induction x with
  | nil => rfl
  | cons b x ih => simp only [size_list, List.map_cons, List.sum_cons, size_bool, List.length_cons] at ih ⊢; omega

/-- The size of the pad of length 2^k. -/
theorem size_pad (k : ℕ) : size (pad k) = 2 * 2 ^ k + 1 := by
  simp [pad, size_list, Nat.mul_comm]

/-- Doubling the pad. -/
theorem pad_append (k : ℕ) : pad k ++ pad k = pad (k + 1) := by
  simp only [pad, List.replicate_append_replicate, pow_succ, Nat.mul_two]

/-- The length of the pad. -/
theorem length_pad (k : ℕ) : (pad k).length = 2 ^ k := List.length_replicate

/-- From the pad of length 2^k, k ≤ e x: the remaining doublings and the last step. -/
theorem padMW_reaches (x : List Bool) : ∀ (d k : ℕ), k + d = e x →
    (padMW e B).Reaches (2 * x.length + 2 * 2 ^ e x + 3 + (2 * (B (x, pad (e x))).length + 2)) (B (x, pad (e x))) (.inl (x, pad k)) (d + 1)
  | 0, k, h => by
    obtain rfl : k = e x := by omega
    refine .step rfl ?_ ?_
    · change size x + size (pad (e x)) + 1 ≤ _
      rw [size_bools, size_pad]; omega
    · have hs : (padMW e B).step (.inl (x, pad (e x))) = .inr (B (x, pad (e x))) := by
        simp [padMW, length_pad, Nat.log2_two_pow]
      rw [hs]
      refine .halt rfl ?_
      change size (B (x, pad (e x))) + 1 ≤ _
      rw [size_bools]; omega
  | d + 1, k, h => by
    refine .step rfl ?_ ?_
    · change size x + size (pad k) + 1 ≤ _
      have : 2 ^ k ≤ 2 ^ e x := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [size_bools, size_pad]; omega
    · have hs : (padMW e B).step (.inl (x, pad k)) = .inl (x, pad (k + 1)) := by
        have : ¬ e x ≤ k := by omega
        simp [padMW, length_pad, Nat.log2_two_pow, this, pad_append]
      rw [hs]
      exact padMW_reaches x d (k + 1) (by omega)

/-- The padding machine ends after e x + 1 steps with w = B (x, pad of length 2^(e x)); its states
have size at most 2|x| + 2·2^(e x) + 2|w| + 5. -/
theorem padMW_runs (e : List Bool → ℕ) (B : List Bool × List Unit → List Bool) (x : List Bool) :
    (padMW e B).Runs x (e x + 1) (2 * x.length + 2 * 2 ^ e x + 3 + (2 * (B (x, pad (e x))).length + 2)) (B (x, pad (e x))) :=
  padMW_reaches x (e x) 0 (by omega)

/-- The word of (x, pad of length 2^k) has 3|x| + 4·2^k + 6 symbols. -/
theorem len_padded (x : List Bool) (k : ℕ) : len (x, pad k) = 3 * x.length + 4 * 2 ^ k + 6 := by
  rw [len_pair, len_bools, len_units, length_pad]; omega

end CountKSatRate.Pad

namespace CountKSatRate

open Groundwork PaddedDescent Turing Pad

/-- Polynomial time in the padded input gives a Turing machine with time polynomial in |x| + 2^(e
x), for a function whose value is a word. -/
public theorem stPaddedW : StPaddedW := by
  intro e B he hB
  have hI := padMW_isPolyT he hB
  obtain ⟨N, q₀, hfin, hN⟩ := CountKSat.stHostW (padMW e B)
  obtain ⟨-, tB, pB, mB, -, lB⟩ := hB.elim
  have pW : PB fun m => 2 * tB (4 * m + 6) + 2 :=
    ((PB.const 2).mul (pB.comp (((PB.const 4).mul PB.id').add (PB.const 6)))).add (PB.const 2)
  have pQ : PB fun m => q₀ * (m + 2) * (m + (2 * m + 3 + (2 * tB (4 * m + 6) + 2)) + 1) ^ q₀ :=
    ((PB.const q₀).mul (PB.id'.add (PB.const 2))).mul
      (((PB.id'.add ((((PB.const 2).mul PB.id').add (PB.const 3)).add pW)).add (PB.const 1)).pow q₀)
  obtain ⟨q, hq⟩ := pQ
  refine ⟨N, q, hfin, fun x => ?_⟩
  obtain ⟨ev⟩ := hN x _ _ _ (padMW_runs e B x)
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, m = x.length + 2 ^ e x := ⟨_, rfl⟩
  have h0 : e x < 2 ^ e x := Nat.lt_two_pow_self
  have hw : (B (x, pad (e x))).length ≤ tB (4 * m + 6) := by
    have a1 := lB (x, pad (e x))
    rw [len_bools, len_padded] at a1
    have a2 : tB (3 * x.length + 4 * 2 ^ e x + 6) ≤ tB (4 * m + 6) := mB (by omega)
    omega
  have h1 : e x + 1 + 1 ≤ m + 2 := by omega
  have h2 : x.length + (2 * x.length + 2 * 2 ^ e x + 3 + (2 * (B (x, pad (e x))).length + 2)) + 1 ≤
      m + (2 * m + 3 + (2 * tB (4 * m + 6) + 2)) + 1 := by omega
  rw [← hm]
  exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (Nat.pow_le_pow_left h2 q₀)).trans (hq m)

end CountKSatRate
