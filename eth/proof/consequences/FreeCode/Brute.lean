/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FreeCode.Defs
import FreeCode.Code
import FreeCode.ReaderCert
import FreeCode.Behind
import SplitSat.Leaf
import SplitSat.Sizes
import SplitSat.Simulate
import ToTuring.Poly.Range
import ToTuring.Poly.Basic
import Batteries.Data.Nat.Lemmas
import Mathlib.Tactic

/-! # After Definition 6: «Trying all assignments gives s_k ≤ 1»

`bruteCore` (proof/consequences/FreeCode/Defs.lean) tests, for each number y < 2^n, in one step,
whether the assignment that gives xᵢ the i-th binary digit of y satisfies the formula, and adds up.
* `bruteCore_runs`: on (n in unary, φ with numbers as variables) it ends after 2·2^n steps with the
  bit that says whether φ is satisfiable, on states of size at most twice the size of the input plus
  3n + 12.
* `bruteCore_polyTimeSteps`: its steps are polynomial time.
* `stBrute` (= `FreeCode.StBrute`): exhaustive search behind the reader `readFree` decides k-SAT for
  every k, and one Turing machine with finite alphabets simulates it with polynomial overhead. -/

public section

namespace FreeCode

open Groundwork Groundwork.Prog Paper SplitSat

/-- The assignment that gives xᵢ the i-th binary digit of y passes the test of exhaustive search
exactly if it makes a literal of every clause true. -/
theorem satAt_toN {n : ℕ} (φ : Sat3.CNF n) (y : ℕ) : PaddedDescent.satAt (Decode.toN φ) y = true ↔ ∀ C ∈ φ, ∃ l ∈ C, y.testBit l.1.val = l.2 := by
  simp [PaddedDescent.satAt, Decode.toN]

/-- The number of y < 2^n that pass the test is positive exactly if φ is satisfiable. -/
theorem sum_satAt_pos {n : ℕ} (φ : Sat3.CNF n) :
    0 < ∑ y ∈ Finset.range (2 ^ n), ((PaddedDescent.satAt (Decode.toN φ) y).toNat : ℤ) ↔ Sat3.Satisfiable φ := by
  constructor
  · intro hpos
    obtain ⟨y, -, hy⟩ := Finset.exists_lt_of_sum_lt (s := Finset.range (2 ^ n)) (f := fun _ => (0 : ℤ))
      (g := fun y => ((PaddedDescent.satAt (Decode.toN φ) y).toNat : ℤ)) (by simpa using hpos)
    have h1 : PaddedDescent.satAt (Decode.toN φ) y = true := by
      cases h : PaddedDescent.satAt (Decode.toN φ) y
      · simp [h] at hy
      · rfl
    exact ⟨fun i => y.testBit i, (satAt_toN φ y).1 h1⟩
  · rintro ⟨a, ha⟩
    have hy : PaddedDescent.satAt (Decode.toN φ) (Nat.ofBits a) = true := (satAt_toN φ _).2 fun C hC => by
      obtain ⟨l, hl, h⟩ := ha C hC
      exact ⟨l, hl, by rw [Nat.testBit_ofBits_lt a _ l.1.2]; exact h⟩
    refine Finset.sum_pos' (fun y _ => by positivity) ⟨Nat.ofBits a, Finset.mem_range.2 (Nat.ofBits_lt_two_pow a), ?_⟩
    rw [hy]
    norm_num

/-- **Exhaustive search**: on (n in unary, φ with numbers as variables) `bruteCore` ends after 2·2^n
steps with the bit that says whether φ is satisfiable, on states of size at most 2·(size of the
input) + 3n + 12. -/
theorem bruteCore_runs {n : ℕ} (φ : Sat3.CNF n) : ∃ b : Bool,
    bruteCore.Runs (List.replicate n (), Decode.toN φ) (2 * 2 ^ n) (2 * size ((List.replicate n (), Decode.toN φ) : List Unit × Fml) + 3 * n + 12) b ∧
      (b = true ↔ Sat3.Satisfiable φ) := by
  obtain ⟨a, ha⟩ : ∃ a : List Unit × Fml, a = (List.replicate n (), Decode.toN φ) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : (List Unit × Fml) × ℕ → ℤ, f = fun q => ((PaddedDescent.satAt q.1.2 q.2).toNat : ℤ) := ⟨_, rfl⟩
  have hN : 2 ^ a.1.length = 2 ^ n := by rw [ha]; simp
  have hv : ∀ y, f (a, y) = ((PaddedDescent.satAt (Decode.toN φ) y).toNat : ℤ) := fun y => by rw [hf, ha]
  have hv1 : ∀ y, (f (a, y)).natAbs ≤ 1 := fun y => by rw [hv]; cases PaddedDescent.satAt (Decode.toN φ) y <;> simp
  have hs2 : size (2 ^ n) = n + 2 := by rw [size_nat, Nat.size_pow]
  have hM : ∀ y < (fun p : List Unit × Fml => 2 ^ p.1.length) a, (Stepped.ofFun f).Runs (a, y) 1 (size a + n + 3) (f (a, y)) := by
    intro y hy
    have hy' : y < 2 ^ n := hN ▸ hy
    refine (Stepped.ofFun_runs f (a, y)).mono le_rfl ?_
    have s1 : size y ≤ n + 1 := by rw [size_nat]; exact Nat.succ_le_succ (Nat.size_le.2 hy')
    have s2 : size (f (a, y)) ≤ 2 := by
      rw [size_int]
      have : (f (a, y)).natAbs.size ≤ 1 := Nat.size_le.2 (by have := hv1 y; omega)
      omega
    have s3 : size (a, y) = size a + size y := rfl
    rw [s3]
    omega
  have hr := Stepped.mapOut_runs (f := fun v : ℤ => decide (0 < v)) (Stepped.sumRange_runs (N := fun p : List Unit × Fml => 2 ^ p.1.length)
    (M := Stepped.ofFun f) (a := a) (fun _ => 1) (fun y => f (a, y)) 1 (size a + n + 3) hM fun y _ => hv1 y)
  rw [hN] at hr
  refine ⟨decide (0 < ∑ y ∈ Finset.range (2 ^ n), f (a, y)), ?_, ?_⟩
  · have hB : bruteCore = Stepped.mapOut (Stepped.sumRange (fun p : List Unit × Fml => 2 ^ p.1.length) (Stepped.ofFun f)) fun v => decide (0 < v) := by
      rw [hf]
      rfl
    rw [hB, ← ha]
    refine hr.mono ?_ ?_
    · simp [Finset.sum_const, Finset.card_range, mul_comm]
    · rw [mul_one, hs2]
      omega
  · rw [decide_eq_true_iff, ← sum_satAt_pos φ]
    simp only [hv]

/-- The steps of exhaustive search are polynomial time. -/
theorem bruteCore_polyTimeSteps : PolyTimeSteps bruteCore := by
  have h1 : PolyT fun p : List Unit × Fml => 2 ^ p.1.length := PolyT.pow_unary (PolyT.const 2) (Unary.of_length (by fun_prop))
  have h2 : PolyT fun q : (List Unit × Fml) × ℕ => PaddedDescent.satAt q.1.2 q.2 := PaddedDescent.satAt_polyT (by fun_prop) (by fun_prop)
  have h3 : PolyT fun q : (List Unit × Fml) × ℕ => ((PaddedDescent.satAt q.1.2 q.2).toNat : ℤ) := by fun_prop
  have := IsPolyT.ofFun h3
  have := IsPolyT.sumRange (M := Stepped.ofFun fun q : (List Unit × Fml) × ℕ => ((PaddedDescent.satAt q.1.2 q.2).toNat : ℤ)) h1
  exact ⟨IsPolyT.mapOut (M := Stepped.sumRange (fun p : List Unit × Fml => 2 ^ p.1.length) (Stepped.ofFun fun q : (List Unit × Fml) × ℕ => ((PaddedDescent.satAt q.1.2 q.2).toNat : ℤ)))
    (f := fun v : ℤ => decide (0 < v)) (by fun_prop)⟩

/-- Exhaustive search behind any reader of the code: on the code of a k-CNF on n variables it ends
after 2·2^n steps with the bit that says whether φ is satisfiable, on states of size at most
c·(n+2)^c, where c = 2·(2^k·(2k+1) + 3) + k + 16. -/
theorem brute_behind {dec : List Bool → List Unit × Fml} (hdec : Reads dec) (k : ℕ) (n : ℕ) (φ : Sat3.CNF n) (h3 : SatK.IsKCNF k φ) :
    ∃ b : Bool, (Stepped.mapIn dec bruteCore).Runs (SatFree.enc φ) (2 * 2 ^ n)
      ((2 * (2 ^ k * (2 * k + 1) + 3) + k + 16) * (n + 2) ^ (2 * (2 ^ k * (2 * k + 1) + 3) + k + 16)) b ∧ (b = true ↔ Sat3.Satisfiable φ) := by
  obtain ⟨b, r, hb⟩ := bruteCore_runs φ
  refine ⟨b, Stepped.mapIn_runs ?_, hb⟩
  rw [hdec n φ]
  refine r.mono le_rfl ?_
  have hψ : ∀ D ∈ Decode.toN φ, D.length ≤ k ∧ ∀ l ∈ D, l.1 < n := fun D hD => by
    obtain ⟨⟨C, hC, hl⟩, h'⟩ := Decode.mem_toN hD
    exact ⟨hl ▸ h3.1 C hC, h'⟩
  have hs := SplitSat.size_node_le (SplitSat.length_le_of_nodup hψ (SplitSat.nodup_toN h3.2)) hψ
  obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ k * (2 * k + 1) + 3 := ⟨_, rfl⟩
  rw [← hP] at hs ⊢
  have e1 : n + 2 ≤ (n + 2) ^ (k + 1) := Nat.le_self_pow (by omega) _
  have e2 : (n + 2) ^ (k + 1) ≤ (n + 2) ^ (2 * P + k + 16) := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : (2 * P + k + 16) * (n + 2) ^ (k + 1) ≤ (2 * P + k + 16) * (n + 2) ^ (2 * P + k + 16) := Nat.mul_le_mul_left _ e2
  have e4 : (2 * P + k + 16) * (n + 2) ^ (k + 1) = 2 * (P * (n + 2) ^ (k + 1)) + k * (n + 2) ^ (k + 1) + 16 * (n + 2) ^ (k + 1) := by ring
  omega

/-- **«Trying all assignments».** The reader `readFree` and one Turing machine with finite
alphabets: exhaustive search behind the reader has polynomial-time steps and decides k-SAT, for
every k, within c·2^n steps on states of size at most c·(n+2)^c; the Turing machine simulates it
with polynomial overhead, and decides k-SAT, for every k, within c·(n+2)^c·2^n steps. This is the
statement `FreeCode.StBrute`. -/
theorem stBrute : StBrute := by
  have hp : PolyTimeSteps (Stepped.mapIn readFree bruteCore) := by
    obtain ⟨h⟩ := bruteCore_polyTimeSteps
    exact ⟨IsPolyT.mapIn readFree_polyT⟩
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp
  refine ⟨readFree, M, q, readFree_polyT, reads_readFree, hfin, hp, fun k => ?_, hs, fun k => ?_⟩
  · refine ⟨2 * (2 ^ k * (2 * k + 1) + 3) + k + 16, fun n φ h3 => ?_⟩
    obtain ⟨b, r, hb⟩ := brute_behind reads_readFree k n φ h3
    exact ⟨2 * 2 ^ n, b, r, hb, Nat.mul_le_mul_right _ (by omega)⟩
  · obtain ⟨c, hc⟩ : ∃ c, c = 2 * (2 ^ k * (2 * k + 1) + 3) + k + 16 := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G, G = (2 ^ k * (k + 1) + 2 + c) ^ q := ⟨_, rfl⟩
    refine ⟨3 * q * G + (k + 1 + c) * q, fun n φ h3 => ?_⟩
    obtain ⟨b, r, hb⟩ := brute_behind reads_readFree k n φ h3
    rw [← hc] at r
    obtain ⟨ev⟩ := hs _ b _ _ r
    refine ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩⟩
    have hpow := overhead_le h3 c q
    rw [← hG] at hpow
    have e0 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have e1 : 2 * 2 ^ n + 1 ≤ 3 * 2 ^ n := by omega
    have e2 : (n + 2) ^ ((k + 1 + c) * q) ≤ (n + 2) ^ (3 * q * G + (k + 1 + c) * q) := Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _)
    calc q * (2 * 2 ^ n + 1) * ((SatFree.enc φ).length + c * (n + 2) ^ c + 1) ^ q
        ≤ q * (3 * 2 ^ n) * (G * (n + 2) ^ (3 * q * G + (k + 1 + c) * q)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) (hpow.trans (Nat.mul_le_mul_left _ e2))
      _ = 3 * q * G * (n + 2) ^ (3 * q * G + (k + 1 + c) * q) * 2 ^ n := by ring
      _ ≤ (3 * q * G + (k + 1 + c) * q) * (n + 2) ^ (3 * q * G + (k + 1 + c) * q) * 2 ^ n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

end FreeCode
