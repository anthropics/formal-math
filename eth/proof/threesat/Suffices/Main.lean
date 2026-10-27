/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Suffices.Loop
public import Suffices.Total
public import Exits.Poly
import CountKSat.InOut
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! # The reduction to sparse formulas by Lemma 4 with ε = δ/3 (deciding form)

The sentence of the proof of Theorem 2, with both of its printed clauses: the machine for sparse
formulas is asked to work only for m ≤ Mn clauses, and it may take «a polynomial in n» more.
`stSufficesOf` proves it from its three hypotheses. The run of lines 1 to 4 of Algorithm 1
(`StLoopRuns`) is applied with t = ⌈A·2^{δn/3} + A(n+1)^A⌉: every formula that Lemma 4 produces is a
3-CNF on the same n variables with at most M·n clauses (field `sparse`), so the machine for sparse
formulas answers on it within t steps, because δ'·m ≤ δ'·M·n = δn/3.
The answer is right because φ is satisfiable if and only if at least one of them is (field `sat`).
There are at most 2^{δn/3} formulas (field `few`), so the count of the total time (`StTotal`) gives
c·2^{δn} steps. A formula with an empty clause is answered «unsatisfiable» at once.
`stPrintedGivesSparse`: the printed property gives the property `Eight.SufficesSparse`, on which the
proofs of Theorem 2 in this development stand. -/

public section

namespace Suffices

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits

/-- **By Lemma 4 with ε = δ/3, it suffices to decide whether a 3-CNF Φ with m ≤ Mn clauses is
satisfiable, in time O(2^{δ'm}) plus a polynomial in n (the deciding form of the paper's sentence,
which counts)** (proof of Theorem 2), from the run of the loop, the count of the total time and the
polynomial-time steps of the loop. -/
theorem stSufficesOf : StSufficesOf := by
  intro HL HT HP δ M τ hδ hM hE
  refine ⟨fun Mc hMc => satLoop_polyTimeSteps_of HP hE Mc hMc, fun Mc A hMc => ?_⟩
  classical
  obtain ⟨c₁, hc₁⟩ := HL (δ / 3) M τ hE
  obtain ⟨c₂, hc₂⟩ := HT δ A (UniformInK.bsumU τ 3) hδ
  obtain ⟨c, hc⟩ : ∃ c, c = c₁ + A * (14 * M + 2) ^ A + 2 * A + c₂ + 22 := ⟨_, rfl⟩
  refine ⟨c, fun n φ h3 => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, N = (Sat3.enc φ).length + 1 := ⟨_, rfl⟩
  obtain ⟨hn, hm⟩ := le_length_enc φ
  rw [← hN] at hn hm ⊢
  have h1 : 1 ≤ N := by omega
  obtain ⟨hb1, hb2⟩ := main_bound hc h1
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := Real.one_le_rpow one_le_two (by positivity)
  have hcc : (c₂ : ℝ) ≤ c := by exact_mod_cast (by omega : c₂ ≤ c)
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast (by omega : 1 ≤ c)
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  by_cases hnil : [] ∈ φ
  · -- a formula with an empty clause is unsatisfiable, and is answered at once
    refine ⟨1, false, ?_, ?_, ?_⟩
    · have hdec : decU 3 (Sat3.enc φ) = (List.replicate n (), Decode.toN φ) := stDecU 3 n φ (by norm_num) h3.1
      have hn' : hasNil (Decode.toN φ) = true := by
        rw [hasNil, List.any_eq_true]
        exact ⟨[], (Decode.nil_mem_toN φ).2 hnil, rfl⟩
      have hs : size (List.replicate n (), Decode.toN φ) ≤ 18 * N ^ 2 := size_input_le (by rw [Decode.length_toN]; exact hm)
        (fun D hD => by obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN hD; exact ⟨hl ▸ h3.1 C hC, h⟩) hn h1
      have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ h1
      have r := (Stepped.ite_runs_true (p := fun p : List Unit × Fml => hasNil p.2) (N := walkUntil (rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ)))
        (a := (List.replicate n (), Decode.toN φ)) hn' (Stepped.const_runs false (List.replicate n (), Decode.toN φ))).mono le_rfl
        (show max (size (List.replicate n (), Decode.toN φ)) (size false) + 1 + 1 ≤ c * N ^ c by rw [size_bool]; omega)
      rw [← hdec] at r
      exact Stepped.mapIn_runs r
    · simp only [Bool.false_eq_true, false_iff]
      rintro ⟨a, ha⟩
      obtain ⟨l, hl, -⟩ := ha [] hnil
      simp at hl
    · push_cast
      nlinarith
  · have hk := isKCNF_toN h3 hnil
    obtain ⟨t, ht⟩ : ∃ t : ℕ, t = ⌈(A : ℝ) * (2 : ℝ) ^ (δ / 3 * n) + A * ((n : ℝ) + 1) ^ A⌉₊ := ⟨_, rfl⟩
    obtain ⟨Sm, hSm⟩ : ∃ Sm, Sm = A * ((14 * M + 2) * N ^ 2) ^ A := ⟨_, rfl⟩
    -- «each with at most M(ε)·n clauses»: the machine for sparse formulas answers on every formula
    -- produced, within t steps
    have hex : ∀ Φ : Formula, ∃ v : ℤ, Φ ∈ produced τ n (Decode.toN φ) → Mc.Runs Φ t Sm v ∧ (0 < v ↔ Φ.Sat) := by
      intro Φ
      by_cases hΦ : Φ ∈ produced τ n (Decode.toN φ)
      · obtain ⟨p1, -, p3⟩ := hE.sparse n _ hk Φ hΦ
        obtain ⟨T, v, r, hv, hT⟩ := hMc n Φ p1 p3
        refine ⟨v, fun _ => ⟨r.mono ?_ ?_, hv⟩⟩
        · have hexp : δ / (3 * M) * Φ.length ≤ δ / 3 * n := by
            have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
            have hl : (Φ.length : ℝ) ≤ M * n := by exact_mod_cast p3
            calc δ / (3 * M) * Φ.length ≤ δ / (3 * M) * (M * n) := mul_le_mul_of_nonneg_left hl (by positivity)
              _ = δ / 3 * n := by field_simp
          have hTt : (T : ℝ) ≤ (t : ℝ) := by
            rw [ht]
            refine (hT.trans ?_).trans (Nat.le_ceil _)
            have h2 := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two hexp) hA0
            linarith
          exact_mod_cast hTt
        · rw [hSm]
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (size_sparse_le p3 (fun C hC => (p1 C hC).2) hn h1) A)
      · exact ⟨0, fun h => absurd h hΦ⟩
    choose v hv using hex
    have run := hc₁ Mc n φ h3 hnil v t Sm fun Φ hΦ => (hv Φ (mem_of_mem_tested hΦ)).1
    obtain ⟨L, hL⟩ : ∃ L, L = (tested (fun Φ => posZ (v Φ)) (produced τ n (Decode.toN φ))).length := ⟨_, rfl⟩
    rw [← hN, ← hL] at run
    refine ⟨_, _, run.mono le_rfl (by rw [hSm]; exact hb1), ?_, ?_⟩
    · -- φ is satisfiable if and only if at least one of them is (field `sat`)
      have hs := hE.sat n _ hk
      rw [← Decode.satN_toN, List.any_eq_true]
      constructor
      · rintro ⟨Φ, hΦ, hp⟩
        have h0 : 0 < v Φ := by simpa [posZ] using hp
        exact hs.2 ⟨Φ, hΦ, (hv Φ hΦ).2.1 h0⟩
      · intro h
        obtain ⟨Φ, hΦ, hb⟩ := hs.1 h
        exact ⟨Φ, hΦ, by simpa [posZ] using (hv Φ hΦ).2.2 hb⟩
    · -- «at most 2^{δn/3} such formulas … so the total time is O(2^{δn})»
      have hLE : (L : ℝ) ≤ (2 : ℝ) ^ (δ / 3 * n) := by
        rw [hL]
        exact (Nat.cast_le.2 (length_tested_le _ _)).trans (hE.few n _ hk)
      have tot := hc₂ n L (δ / 3 * n) hLE le_rfl
      have htc : (t : ℝ) ≤ (A : ℝ) * (2 : ℝ) ^ (δ / 3 * n) + A * ((n : ℝ) + 1) ^ A + 1 := by
        rw [ht]
        exact (Nat.ceil_lt_add_one (by positivity)).le
      have h2 := mul_le_mul_of_nonneg_left (show (t : ℝ) + 2 ≤ (A : ℝ) * (2 : ℝ) ^ (δ / 3 * n) + A * ((n : ℝ) + 1) ^ A + 3 by linarith) (Nat.cast_nonneg (α := ℝ) L)
      rw [show depth τ n = UniformInK.bsumU τ 3 * n from rfl]
      push_cast
      calc (L : ℝ) * ((t : ℝ) + 2) + (UniformInK.bsumU τ 3 : ℝ) * n + 2
          ≤ (L : ℝ) * ((A : ℝ) * (2 : ℝ) ^ (δ / 3 * n) + A * ((n : ℝ) + 1) ^ A + 3) + (UniformInK.bsumU τ 3 : ℝ) * n + 2 := by linarith
        _ ≤ c₂ * (2 : ℝ) ^ (δ * n) := tot
        _ ≤ c * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hcc (by positivity)

/-- **By Lemma 4 with ε = δ/3, it suffices to decide whether a 3-CNF Φ with m ≤ Mn clauses is
satisfiable, in time O(2^{δ'm}) plus a polynomial in n (the deciding form of the paper's sentence,
which counts)** (proof of Theorem 2), for every enumeration for ε = δ/3: its constant M, and lines 1
to 4 of Algorithm 1 with its parameter τ. -/
theorem stSuffices : StSuffices := stSufficesOf stLoopRuns stTotal stFoldUntilPoly

/-- The printed sentence, «… with m ≤ Mn clauses …, in time O(2^{δ'm}) plus a polynomial in n»,
gives the property used elsewhere in this development: a machine that works for every number of
clauses, with no polynomial added, does what the deciding form of the printed sentence asks. -/
theorem stPrintedGivesSparse : StPrintedGivesSparse := by
  intro δ M S h
  refine ⟨h.1, fun Mc A hMc => h.2 Mc A fun n Φ h3 _ => ?_⟩
  obtain ⟨T, v, r, hv, hT⟩ := hMc Φ fun C hC => (h3 C hC).2.1
  refine ⟨T, v, r.mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_add_right _ _) A)), hv, hT.trans ?_⟩
  have h0 : (0 : ℝ) ≤ (A : ℝ) * ((n : ℝ) + 1) ^ A := by positivity
  linarith

end Suffices
