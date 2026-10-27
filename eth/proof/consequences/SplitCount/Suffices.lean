/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
import SplitCount.Sizes
import SplitCount.Leaf
import CountKSat.Walk
import GraphProblems.Engine
import WidthK.Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Proof of Corollary 6: «By the work of Dell et al. … this case suffices»

`engineBy step D`: on (n in unary, ψ), 0 if there is an empty clause; otherwise walk the tree of the
sparsification for counting, at each leaf apply the width reduction and then D, and add up; write
the sum in n + 1 bits.
`engineBy_runs`: it returns the number of satisfying assignments of ψ on n variables within c·2^{δn}
steps, on states of size at most c·M^c, for every M ≥ 1 that bounds n and the number of clauses of
ψ.
There are at most 2^{(δ/3)n} leaves, whose numbers add up (`SparsifiesPlain`), and each leaf takes
at most A·2^{(δ/3)n} steps (`leaf_runs`); the run of the walk that adds up is `CountKSat.stWalkSum`.
`stSuffices`: a formula with at most k literals per clause, variables below N and no clause twice
has polynomially many clauses, which gives `Eight.Serves`. -/

public section

namespace SplitCount

open Groundwork Groundwork.Prog Groundwork.Sparsify Paper CountKSat Eight Eight.Width Occ

/-- There is an empty clause exactly if `hasNil` says so. -/
theorem hasNil_iff (ψ : Fml) : hasNil ψ = true ↔ [] ∈ ψ := by
  simp [hasNil, List.any_eq_true]

/-- The procedure counts: under the hypotheses of `StSuffices` there is a constant c such that, on
(n in unary, ψ) for ψ with clauses of at most k literals on x₀ … xₙ₋₁, `engineBy step D` returns the
number of satisfying assignments of ψ on n variables in n + 1 bits within c·2^{δn} steps, on states
of size at most c·M^c, for every M ≥ 1 with n ≤ M and at most M clauses in ψ. -/
theorem engineBy_runs {k : ℕ} {δ : ℝ} (hδ : 0 < δ) {step : CNode → Option (CNode × CNode)} {Dd Bl Sk : ℕ} (hsp : SparsifiesPlain k (δ / 3) step Dd Bl Sk)
    {D : StepMachine (List Unit × Fml) ℕ} {δ' : ℝ} {A : ℕ} (hδ' : 0 ≤ δ') (hδB : δ' * ((1 + 3 * (((max k 3 : ℕ) : ℝ) - 3)) * ((Bl : ℝ) + 1)) ≤ δ / 3) (hD : CountsThree D δ' A) :
    ∃ c : ℕ, ∀ (n : ℕ) (ψ : Fml) (M : ℕ), (∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) → n ≤ M → ψ.length ≤ M → 1 ≤ M →
      ∃ T : ℕ, (engineBy step D).Runs (List.replicate n (), ψ) T (c * M ^ c) (SatK.binary n (cntN n ψ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by
  obtain ⟨P₁, hP₁⟩ : ∃ P₁, P₁ = leafConst k Bl := ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂, P₂ = stackConst k Dd Sk := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 4 * max k 2 + 2 := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = P₂ + 2 * (Q + 4) + 12 := ⟨_, rfl⟩
  refine ⟨B₀ + 3 + A * P₁ ^ A + 2 * A, fun n ψ M hψ hn hm h1 => ?_⟩
  obtain ⟨a, ha⟩ : ∃ a : List Unit × Fml, a = (List.replicate n (), ψ) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = cntN n ψ := ⟨_, rfl⟩
  rw [← ha, ← hv]
  have hv2 : v < 2 ^ (n + 1) := hv ▸ (cntN_le n ψ).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have h1M2 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ h1
  have hM23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := Real.one_le_rpow one_le_two (by positivity)
  have hsa : size a ≤ (Q + 4) * M ^ 2 := by
    have s1 := size_unary n
    have s2 := size_fml_le (k := max k 2) hm fun C hC => ⟨(hψ C hC).1.trans (le_max_left _ _), (hψ C hC).2⟩
    have s3 : M * (max k 2 * (n + 2 + 1) + 1 + 1) ≤ Q * M ^ 2 := by
      calc M * (max k 2 * (n + 2 + 1) + 1 + 1) ≤ M * (Q * M) := Nat.mul_le_mul_left _ (hQ ▸ clause_bound hn h1)
        _ = Q * M ^ 2 := by ring
    have s4 : (Q + 4) * M ^ 2 = Q * M ^ 2 + 4 * M ^ 2 := by ring
    rw [ha, size_prod]
    show size (List.replicate n ()) + size ψ ≤ _
    omega
  -- the count, before it is written in binary
  have main : ∃ T S : ℕ, (Stepped.ite (fun p : List Unit × Fml => hasNil p.2) (Stepped.const 0)
      (walkSum (stepPlain step) rootPlain (Stepped.mapIn leafPlain (Stepped.mapIn widthP D)))).Runs a T S v ∧
      S ≤ P₂ * M ^ 3 + A * (P₁ * M ^ 2) ^ A + (Q + 4) * M ^ 2 + M + 10 ∧ (T : ℝ) ≤ ((A : ℝ) + 2) * (2 : ℝ) ^ (δ * n) := by
    by_cases hnil : [] ∈ ψ
    · refine ⟨1, _, Stepped.ite_runs_true (by rw [ha]; exact (hasNil_iff ψ).2 hnil) (by rw [hv, cntN_of_nil hnil]; exact Stepped.const_runs 0 a), ?_, ?_⟩
      · have : size (0 : ℕ) = 1 := by simp
        rw [this]
        omega
      · push_cast
        nlinarith
    · have hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
        intro C hC
        refine ⟨?_, hψ C hC⟩
        rintro rfl
        exact hnil hC
      -- the sparsification for counting
      obtain ⟨t1, t2, t3, t4⟩ := hsp n ψ hψne
      rw [← ha] at t1 t2 t3 t4
      obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepPlain step) (Dd * n) (rootPlain a) := ⟨_, rfl⟩
      obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 3 * n) := ⟨_, rfl⟩
      have hE0 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
      have hLE : (L.length : ℝ) ≤ E := by rw [hE, hL]; exact t1
      -- the width reduction and then D, at each leaf
      have hT : ∀ x ∈ leaves (stepPlain step) (Dd * n) (rootPlain a),
          (Stepped.mapIn leafPlain (Stepped.mapIn widthP D)).Runs x ⌊(A : ℝ) * E⌋₊ (A * (P₁ * M ^ 2) ^ A) (cntN n (leafF x.2)) := fun x hx => by
        rw [hE, hP₁]
        exact leaf_runs hδ' hδB hD hn h1 (t2 x hx).2.1 (t2 x hx).2.2.1 (t2 x hx).2.2.2
      have hS : ∀ i, size ((round (stepPlain step))^[i] ([rootPlain a], [])).1 ≤ P₂ * M ^ 3 := fun i => by
        rw [hP₂]
        exact stack_size hn hm h1 (t4 i).1 (t4 i).2
      have wr := stWalkSum _ _ (stepPlain step) rootPlain (Stepped.mapIn leafPlain (Stepped.mapIn widthP D)) (Dd * n) a
        (fun x hx => (t2 x hx).1) (fun x => cntN n (leafF x.2)) ⌊(A : ℝ) * E⌋₊ (A * (P₁ * M ^ 2) ^ A) (P₂ * M ^ 3) (n + 1) hT hS (by rw [← t3, ← hv]; exact hv2)
      rw [← t3, ← hv, ← hL] at wr
      refine ⟨_, _, Stepped.ite_runs_false (by rw [ha]; simpa using fun h => hnil ((hasNil_iff ψ).1 h)) wr, by omega, ?_⟩
      have hfl : ((⌊(A : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (A : ℝ) * E := Nat.floor_le (by positivity)
      have hEE : E * E ≤ (2 : ℝ) ^ (δ * n) := by
        rw [hE, ← Real.rpow_add two_pos]
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have : (0 : ℝ) ≤ δ * n := by positivity
        linarith
      have hE00 : 0 ≤ E := by linarith
      push_cast
      calc (L.length : ℝ) * (((⌊(A : ℝ) * E⌋₊ : ℕ) : ℝ) + 2) ≤ E * ((A : ℝ) * E + 2 * E) := mul_le_mul hLE (by linarith) (by positivity) hE00
        _ = ((A : ℝ) + 2) * (E * E) := by ring
        _ ≤ ((A : ℝ) + 2) * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_left hEE (by positivity)
  obtain ⟨T, S, r, hS, hT⟩ := main
  have ro := Stepped.ofFun_runs outW (a, v)
  have hout : outW (a, v) = SatK.binary n v := by rw [ha]; exact outW_eq n ψ v
  rw [hout] at ro
  refine ⟨T + 1 + 1, (Stepped.bind_runs r ro).mono le_rfl (poly_le h1 ?_), ?_⟩
  · have sv : size v ≤ n + 2 := size_nat_le hv2
    have sb := size_binary n v
    have sp : size (a, v) = size a + size v := size_prod _
    have e1 : B₀ * M ^ 3 = P₂ * M ^ 3 + 2 * ((Q + 4) * M ^ 3) + 12 * M ^ 3 := by rw [hB₀]; ring
    have e2 : (Q + 4) * M ^ 2 ≤ (Q + 4) * M ^ 3 := Nat.mul_le_mul_left _ hM23
    rw [sp]
    omega
  · have hc : (A : ℝ) + 4 ≤ ((B₀ + 3 + A * P₁ ^ A + 2 * A : ℕ) : ℝ) := by
      have : A + 4 ≤ B₀ + 3 + A * P₁ ^ A + 2 * A := by omega
      exact_mod_cast this
    calc ((T + 1 + 1 : ℕ) : ℝ) = (T : ℝ) + 2 := by push_cast; ring
      _ ≤ ((A : ℝ) + 2) * (2 : ℝ) ^ (δ * n) + 2 * (2 : ℝ) ^ (δ * n) := by linarith
      _ = ((A : ℝ) + 4) * (2 : ℝ) ^ (δ * n) := by ring
      _ ≤ ((B₀ + 3 + A * P₁ ^ A + 2 * A : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hc (by positivity)

/-- **«By the work of Dell et al. … this case suffices», for every procedure D that counts the
satisfying assignments of a 3-CNF as `CountsThree` says.** Under the hypotheses of `StSuffices`,
`engineBy step D` serves as the procedure for #k-SAT with the exponent δ. -/
theorem stSuffices : StSuffices := by
  intro k hk δ hδ step Dd Bl Sk hsp D δ' A hδ' hδB hD
  obtain ⟨c, h⟩ := engineBy_runs hδ hsp hδ' hδB hD
  refine ⟨c * (k * 2 ^ k + 1) ^ c + (k + 1) * c, fun N ψ hψ hnd => ?_⟩
  obtain ⟨φ, rfl⟩ := GraphProblems.exists_toN fun C hC => (hψ C hC).2
  have h3 : SatK.IsKCNF k φ := by
    refine ⟨fun C hC => ?_, List.Nodup.of_map _ hnd⟩
    have := (hψ (C.map fun l => (l.1.val, l.2)) (List.mem_map_of_mem hC)).1
    simpa using this
  have hlen := DecodeK.length_enc k φ
  have hm : φ.length ≤ (SatK.enc k φ).length + 1 := by
    have hB : 0 < k * (Nat.log2 (2 * N) + 1) := Nat.mul_pos hk (by omega)
    have := Nat.le_mul_of_pos_right φ.length hB
    omega
  obtain ⟨T, hr, hT⟩ := h N (Decode.toN φ) ((SatK.enc k φ).length + 1) hψ (by omega) (by rw [Decode.length_toN]; exact hm) (by omega)
  refine ⟨T, hr.mono le_rfl ?_, hT.trans ?_⟩
  · have hl := DecodeK.length_enc_succ_le h3
    calc c * ((SatK.enc k φ).length + 1) ^ c ≤ c * ((k * 2 ^ k + 1) * (N + 2) ^ (k + 1)) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl c)
      _ = (c * (k * 2 ^ k + 1) ^ c) * (N + 2) ^ ((k + 1) * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ (c * (k * 2 ^ k + 1) ^ c + (k + 1) * c) * (N + 2) ^ (c * (k * 2 ^ k + 1) ^ c + (k + 1) * c) :=
          Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))
  · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h1 : 1 ≤ (k * 2 ^ k + 1) ^ c := Nat.one_le_pow _ _ (by omega)
    have h2 : c ≤ c * (k * 2 ^ k + 1) ^ c + (k + 1) * c := (Nat.le_mul_of_pos_right c h1).trans (Nat.le_add_right _ _)
    exact_mod_cast h2

end SplitCount
