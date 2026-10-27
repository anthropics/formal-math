/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatStatement
public import ToTuring.PolyT
import PaddedDescent.Host
import ToTuring.Lib.Nat1b
import ToTuring.Lib.Nat2
import StepMachines.Prog.Decode

/-! Padding. Let A be a polynomial-time function of a bit string x and a list of units («the pad»),
and let e be a polynomial-time
function from bit strings to numbers. Then ONE Turing machine of Mathlib computes x ↦ A (x, pad of
length 2^(e x)) within
q·(|x| + 2^(e x) + 1)^q steps, for ONE constant q (`exists_tm_padded`). In words: polynomial time
(`PolyT`) in the padded input gives a
Turing machine with time polynomial in |x| + 2^(e x). `decidesTM_of_padded` is the same for 3-SAT.
The stepped machine `padM` starts with a pad of length 1, doubles it e x times, one doubling per
step, and then applies A in a single step. -/

namespace PaddedDescent

open Groundwork Sat3 Turing

/-- The pad of length 2^k. -/
@[expose] public def pad (k : ℕ) : List Unit := List.replicate (2 ^ k) ()

/-- The stepped machine: the state is the input with the present pad, or the result. One step
doubles the pad, or, once the
pad has length at least 2^(e x), applies A. -/
@[expose] public def padM (e : List Bool → ℕ) (A : List Bool × List Unit → Bool) : Stepped (List Bool) Bool where
  σ := (List Bool × List Unit) ⊕ Bool
  init x := .inl (x, [()])
  step s := s.elim (fun p => bif decide (e p.1 ≤ Nat.log2 p.2.length) then .inr (A p) else .inl (p.1, p.2 ++ p.2))
    fun b => .inr b
  out s := s.elim (fun _ => none) fun b => some b

variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}

/-- Every part of the padding machine is polynomial-time if e and A are. -/
@[instance_reducible] public def padM_isPolyT (he : PolyT e) (hA : PolyT A) : IsPolyT (padM e A) where
  enc := (inferInstance : Enc ((List Bool × List Unit) ⊕ Bool))
  carried := (inferInstance : Carried ((List Bool × List Unit) ⊕ Bool))
  init := (by fun_prop : PolyT fun x : List Bool => (.inl (x, [()]) : (List Bool × List Unit) ⊕ Bool))
  step := (by fun_prop : PolyT fun s : (List Bool × List Unit) ⊕ Bool =>
    s.elim (fun p => bif decide (e p.1 ≤ Nat.log2 p.2.length) then
      (.inr (A p) : (List Bool × List Unit) ⊕ Bool) else .inl (p.1, p.2 ++ p.2)) fun b => .inr b)
  out := (by fun_prop : PolyT fun s : (List Bool × List Unit) ⊕ Bool => s.elim (fun _ => none) fun b => some b)

theorem size_bools (x : List Bool) : size x = 2 * x.length + 1 := by
  induction x with
  | nil => rfl
  | cons b x ih => simp only [size_list, List.map_cons, List.sum_cons, size_bool, List.length_cons] at ih ⊢; omega

theorem size_pad (k : ℕ) : size (pad k) = 2 * 2 ^ k + 1 := by
  simp [pad, size_list, Nat.mul_comm]

theorem pad_append (k : ℕ) : pad k ++ pad k = pad (k + 1) := by
  simp only [pad, List.replicate_append_replicate, pow_succ, Nat.mul_two]

theorem length_pad (k : ℕ) : (pad k).length = 2 ^ k := List.length_replicate

/-- From the pad of length 2^k, k ≤ e x: the remaining doublings and the last step. -/
theorem padM_reaches (x : List Bool) : ∀ (d k : ℕ), k + d = e x →
    (padM e A).Reaches (2 * x.length + 2 * 2 ^ e x + 3) (A (x, pad (e x))) (.inl (x, pad k)) (d + 1)
  | 0, k, h => by
    obtain rfl : k = e x := by omega
    refine .step rfl ?_ ?_
    · change size x + size (pad (e x)) + 1 ≤ _
      rw [size_bools, size_pad]; omega
    · have hs : (padM e A).step (.inl (x, pad (e x))) = .inr (A (x, pad (e x))) := by
        simp [padM, length_pad, Nat.log2_two_pow]
      rw [hs]
      exact .halt rfl (by change 1 + 1 ≤ _; omega)
  | d + 1, k, h => by
    refine .step rfl ?_ ?_
    · change size x + size (pad k) + 1 ≤ _
      have : 2 ^ k ≤ 2 ^ e x := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [size_bools, size_pad]; omega
    · have hs : (padM e A).step (.inl (x, pad k)) = .inl (x, pad (k + 1)) := by
        have : ¬ e x ≤ k := by omega
        simp [padM, length_pad, Nat.log2_two_pow, this, pad_append]
      rw [hs]
      exact padM_reaches x d (k + 1) (by omega)

/-- The padding machine ends after e x + 1 steps with A (x, pad of length 2^(e x)); its states have
size at most
2|x| + 2·2^(e x) + 3. -/
public theorem padM_runs (e : List Bool → ℕ) (A : List Bool × List Unit → Bool) (x : List Bool) :
    (padM e A).Runs x (e x + 1) (2 * x.length + 2 * 2 ^ e x + 3) (A (x, pad (e x))) :=
  padM_reaches x (e x) 0 (by omega)

/-- Arithmetic: the bound of the host for the padding machine is a polynomial in |x| + 2^e + 1. -/
theorem pad_bound (q l e : ℕ) : q * (e + 1 + 1) * (l + (2 * l + 2 * 2 ^ e + 3) + 1) ^ q ≤
    (q * 4 ^ (q + 1) + (q + 1)) * (l + 2 ^ e + 1) ^ (q * 4 ^ (q + 1) + (q + 1)) := by
  obtain ⟨m, hm⟩ : ∃ m, m = l + 2 ^ e + 1 := ⟨_, rfl⟩
  have h0 : e < 2 ^ e := Nat.lt_two_pow_self
  have h1 : e + 1 + 1 ≤ 4 * m := by omega
  have h2 : l + (2 * l + 2 * 2 ^ e + 3) + 1 ≤ 4 * m := by omega
  have hm1 : 1 ≤ m := by omega
  rw [← hm]
  calc q * (e + 1 + 1) * (l + (2 * l + 2 * 2 ^ e + 3) + 1) ^ q ≤ q * (4 * m) * (4 * m) ^ q :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (Nat.pow_le_pow_left h2 q)
    _ = q * 4 ^ (q + 1) * m ^ (q + 1) := by rw [Nat.mul_assoc, ← pow_succ', Nat.mul_pow, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right hm1 (Nat.le_add_left _ _))

/-- Let `e` (from bit strings to numbers) and `A` (from a bit string and a list of units to a bit)
be polynomial-time. There are a
Turing machine `N` with finite alphabets and a number `q` such that on every bit string `x` the
machine halts with the output
A (x, the list of 2^(e x) units) within q · (|x| + 2^(e x) + 1)^q steps. -/
public theorem exists_tm_padded (he : PolyT e) (hA : PolyT A) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ x : List Bool,
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
          (some ([A (x, pad (e x))].map N.outputAlphabet.invFun)) (q * (x.length + 2 ^ e x + 1) ^ q)) := by
  have := padM_isPolyT he hA
  obtain ⟨N, q, hfin, hN⟩ := exists_tm' (padM e A)
  refine ⟨N, q * 4 ^ (q + 1) + (q + 1), hfin, fun x => ?_⟩
  obtain ⟨ev⟩ := hN x _ _ _ (padM_runs e A x)
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (pad_bound q x.length (e x))⟩⟩

/-- The same for 3-SAT. Let `e` and `A` be polynomial-time. There are a Turing machine `N` with
finite alphabets and a number `q`,
depending on `e` and `A` only, such that for every function `E` of the number n of variables: if on
the code x of every instance of
3-SAT e x ≤ E n, and A (x, the list of 2^(e x) units) is the bit «satisfiable», then `N` decides
3-SAT within
q · (25 (n + 2)^4 + 2^(E n))^q steps. -/
public theorem decidesTM_of_padded (he : PolyT e) (hA : PolyT A) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ E : ℕ → ℕ,
        (∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
          e (enc φ) ≤ E n ∧ (A (enc φ, pad (e (enc φ))) = true ↔ Satisfiable φ)) →
        DecidesTM N fun n => q * (25 * (n + 2) ^ 4 + 2 ^ E n) ^ q := by
  obtain ⟨N, q, hfin, hN⟩ := exists_tm_padded he hA
  refine ⟨N, q, hfin, fun E h n φ h3 => ?_⟩
  obtain ⟨hE, hb⟩ := h n φ h3
  obtain ⟨ev⟩ := hN (enc φ)
  have h5 : (enc φ).length + 1 ≤ 25 * (n + 2) ^ 4 := Groundwork.Decode.length_enc_succ_le h3
  have h6 : 2 ^ e (enc φ) ≤ 2 ^ E n := Nat.pow_le_pow_right (by norm_num) hE
  have hle : q * ((enc φ).length + 2 ^ e (enc φ) + 1) ^ q ≤ q * (25 * (n + 2) ^ 4 + 2 ^ E n) ^ q :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) q)
  exact ⟨_, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩⟩

end PaddedDescent
