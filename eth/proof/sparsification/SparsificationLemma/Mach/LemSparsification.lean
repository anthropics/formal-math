/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Mach.Defs
import SparsificationLemma.Mach.Full
import SparsificationLemma.Len
import WidthK.Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Lemma 4 in its form for deciding

`lemSparsification_of` derives `LemSparsification` from `SparsABCD`, the theorem on sparsification
with parts (a) to (d), at width k = 3. Given a real ε > 0 take a rational q with 0 < q < min(ε, 1)
and s = `precE C 3 q`.
* The time: the input has s + 5 bits and the code of φ, which has at most 25(n+2)^4 bits because no
  clause is written twice. So C·(length of the input + 8)^C is at most c·(n+1)^c with
  c = C·(s+412)^C + 4C, and 2^(qn) ≤ 2^(εn).
* The number of clauses: a variable occurs in at most (3C/q)^48 clauses of an output, and every
  clause has a variable, so M(ε) = ⌈(3C/q)^48⌉ + 1 will do (`stLenOfOcc`).
* Satisfiability: an assignment that satisfies φ satisfies one of the outputs, and an assignment
  that does not satisfies none.
`lemSparsification` takes only the statement `Prints` on the machine as a hypothesis. -/

public section

namespace SparsificationLemma.Mach

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing

/-- The length of the input plus 8 is at most (s+412)·(n+1)^4, for a 3-CNF on n variables in which
no clause is written twice. -/
theorem length_encIn_le (s : ℕ) {n : ℕ} {φ : Sat3.CNF n} (h3 : SatK.IsKCNF 3 φ) :
    (encIn s 3 φ).length + 2 ^ 3 ≤ (s + 412) * (n + 1) ^ 4 := by
  have h1 := DecodeK.length_enc_succ_le h3
  have h2 : (n + 2) ^ 4 ≤ (2 * (n + 1)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h3 : (2 * (n + 1)) ^ 4 = 16 * (n + 1) ^ 4 := by ring
  have h4 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h5 : (encIn s 3 φ).length = s + 5 + (SatK.enc 3 φ).length := by
    simp only [encIn, SatM.enc, List.length_append, List.length_replicate, List.length_cons]; omega
  have h6 : (s + 412) * (n + 1) ^ 4 = s * (n + 1) ^ 4 + 412 * (n + 1) ^ 4 := by ring
  have h7 : s ≤ s * (n + 1) ^ 4 := Nat.le_mul_of_pos_right _ h4
  norm_num at h1
  omega

/-- C·(length of the input + 8)^C ≤ c·(n+1)^c with c = C·(s+412)^C + 4C. -/
theorem poly_le (C s : ℕ) {n : ℕ} {φ : Sat3.CNF n} (h3 : SatK.IsKCNF 3 φ) :
    C * ((encIn s 3 φ).length + 2 ^ 3) ^ C ≤ (C * (s + 412) ^ C + 4 * C) * (n + 1) ^ (C * (s + 412) ^ C + 4 * C) := by
  calc C * ((encIn s 3 φ).length + 2 ^ 3) ^ C ≤ C * ((s + 412) * (n + 1) ^ 4) ^ C :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (length_encIn_le s h3) C)
    _ = C * (s + 412) ^ C * (n + 1) ^ (4 * C) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ (C * (s + 412) ^ C + 4 * C) * (n + 1) ^ (C * (s + 412) ^ C + 4 * C) :=
        Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))

/-- Lemma 4 from the theorem on sparsification, parts (a) to (d). -/
theorem lemSparsification_of (h : SparsABCD) : LemSparsification := by
  obtain ⟨M, C, hfin, hM⟩ := h
  refine ⟨M, hfin, fun ε hε => ?_⟩
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (lt_min hε one_pos)
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have hqε : (q : ℝ) ≤ ε := (hq1.trans_le (min_le_left _ _)).le
  have hq1' : q ≤ 1 := by exact_mod_cast (hq1.trans_le (min_le_right _ _)).le
  refine ⟨⌈((C : ℝ) * ((3 : ℕ) : ℝ) / (q : ℝ)) ^ (16 * 3)⌉₊ + 1, precE C 3 q, C * (precE C 3 q + 412) ^ C + 4 * C, by omega,
    fun n φ h3 hne => ?_⟩
  have h3' : SatK.IsKCNF 3 φ := ⟨h3.1, h3.2⟩
  obtain ⟨Φ, T, hrun, g1, g2, g3, g4, g5⟩ := hM 3 n q φ (by norm_num) hq0' hq1' h3' hne
  have hmono : (2 : ℝ) ^ ((q : ℝ) * (n : ℝ)) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hqε (Nat.cast_nonneg _))
  refine ⟨Φ, T, hrun, ?_, g2.trans hmono, fun Ψ hΨ => ⟨(g1 Ψ hΨ).1, (g1 Ψ hΨ).2, ?_⟩, ?_⟩
  · have hN := poly_le C (precE C 3 q) h3'
    have hR : (C : ℝ) * (((encIn (precE C 3 q) 3 φ).length : ℝ) + 2 ^ 3) ^ C
        ≤ ((C * (precE C 3 q + 412) ^ C + 4 * C : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (C * (precE C 3 q + 412) ^ C + 4 * C) := by
      exact_mod_cast hN
    calc (T : ℝ) ≤ (C : ℝ) * (((encIn (precE C 3 q) 3 φ).length : ℝ) + 2 ^ 3) ^ C * (2 : ℝ) ^ ((q : ℝ) * (n : ℝ)) := g5
      _ ≤ ((C * (precE C 3 q + 412) ^ C + 4 * C : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (C * (precE C 3 q + 412) ^ C + 4 * C)
            * (2 : ℝ) ^ (ε * (n : ℝ)) := mul_le_mul hR hmono (by positivity) (by positivity)
      _ = _ := by ring
  · refine stLenOfOcc 3 n _ Ψ (g1 Ψ hΨ).1 fun v => ?_
    have h1 : (occN Ψ v : ℝ) ≤ (⌈((C : ℝ) * ((3 : ℕ) : ℝ) / (q : ℝ)) ^ (16 * 3)⌉₊ : ℝ) := (g4 Ψ hΨ v).trans (Nat.le_ceil _)
    have h2 : occN Ψ v ≤ ⌈((C : ℝ) * ((3 : ℕ) : ℝ) / (q : ℝ)) ^ (16 * 3)⌉₊ := by exact_mod_cast h1
    omega
  · rw [← Decode.satN_toN]
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hi, -⟩ := (g3 b).1 hb
      exact ⟨Φ.get i, List.get_mem _ _, b, hi⟩
    · rintro ⟨Ψ, hΨ, b, hb⟩
      by_contra hno
      exact (g3 b).2 (fun hs => hno ⟨b, hs⟩) Ψ hΨ hb

/-- Lemma 4 from a machine that prints the outputs. -/
theorem lemSparsification (hP : Prints) : LemSparsification := lemSparsification_of (sparsABCD hP)

end SparsificationLemma.Mach
