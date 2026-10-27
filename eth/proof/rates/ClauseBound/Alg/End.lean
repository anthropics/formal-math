/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Top
import CountKSat.InOut
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Lemmas on codes, logarithms and time, for bounds in m

This file holds lemmas for bounding, in the number m of clauses, the number of steps of the padding
machine on the code x of (k, φ).
That machine runs for q·(|x| + 2^(e x) + 1)^q steps on the input x. For the code x of (k, φ), with m
clauses, all variables occurring, |x| + 1 ≤ 8·(k·m)² (`length_enc_succ_le`).
The exponent e x is at most n ≤ k·m and at most the exponent of the clique algorithm at the level
picked for m (`eM_enc_le`). If r(m) ≥ 1/(c₁·(log₂(m+2))^c₁), then log₂(k·m) = O(k·m·r(m))
(`mul_le_two_rpow`),
and `time_le` turns such bounds into a bound C·2^(C·X) on q·(|x| + 2^E + 1)^q. -/

public section

namespace ClauseBound.Alg.End

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat

/-! ### What the readers return on a code -/

/-- The leading 1s of the code of (k, φ) are k in number. -/
theorem kOf_enc (k : ℕ) {n : ℕ} (φ : Sat3.CNF n) : kOf (SatM.enc k φ) = List.replicate k () := by
  simp [kOf, SatM.enc]

/-- After 1ᵏ 0 comes the code of φ as an instance of k-SAT. -/
theorem restOf_enc (k : ℕ) {n : ℕ} (φ : Sat3.CNF n) : restOf (SatM.enc k φ) = SatK.enc k φ := by
  simp [restOf, SatM.enc]

/-- The reader returns n in unary and the formula. -/
theorem fmlOf_enc {k n : ℕ} {φ : Sat3.CNF n} (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) :
    fmlOf (SatM.enc k φ) = (List.replicate n (), Decode.toN φ) := by
  rw [fmlOf, kOf_enc, restOf_enc, List.length_replicate]
  exact stDecU k n φ hk hφ

/-! ### The exponent function -/

/-- The exponent computed under the bound b, or else b, is at most b and at most the exponent of the
clique algorithm. -/
theorem needTopC_getD_le {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (b : U) (i : Idx) (k m : ℕ) :
    (needTopC S b i k m).getD b.length ≤ b.length ∧ (needTopC S b i k m).getD b.length ≤ needTop S i k m := by
  unfold needTopC needTop
  set x : Idx × U × U := (i, List.replicate (lamTopK (S.K i) (3 * S.K i ^ 8) k m) (),
    List.replicate (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i)) ()) with hx
  set a := max (3 * S.K i ^ 8 * Nat.size (S.K i)) (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i + 1))
  set c := (S.K i - 1) * lamTopK (S.K i) (3 * S.K i ^ 8) k m
  cases h : S.needC (b, x) with
  | none =>
    refine ⟨by simp, ?_⟩
    simp only [Option.bind_none, Option.getD_none]
    by_contra hlt
    have h1 : S.need x ≤ b.length := by
      have : S.need x ≤ max a (max c (S.need x)) := (le_max_right _ _).trans (le_max_right _ _)
      omega
    rw [hS.needC_some b x h1] at h
    cases h
  | some v =>
    have hv := hS.needC_eq b x v h
    subst hv
    simp only [Option.bind_some]
    split_ifs with h1
    · exact ⟨by simpa using h1, by simp⟩
    · exact ⟨by simp, by simpa using (not_le.1 h1).le⟩

/-- On the code of (k, φ) the exponent is at most n and at most the exponent of the clique algorithm
at the level picked for m. -/
theorem eM_enc_le {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (pick : U → U × Idx) {k n : ℕ} {φ : Sat3.CNF n} (hk : 1 ≤ k)
    (hφ : ∀ C ∈ φ, C.length ≤ k) :
    eM S pick (SatM.enc k φ) ≤ n ∧ eM S pick (SatM.enc k φ) ≤ needTop S (pick (root9 φ.length)).2 k φ.length := by
  have h := needTopC_getD_le hS (List.replicate n ()) (pick (root9 φ.length)).2 k φ.length
  simpa [eM, planM, fmlOf_enc hk hφ, kOf_enc, Decode.length_toN] using h

/-! ### The length of a code -/

/-- The code of (k, φ) has k + n + 2 + m·k·(⌊log₂ 2n⌋ + 1) symbols. -/
theorem length_enc (k : ℕ) {n : ℕ} (φ : Sat3.CNF n) :
    (SatM.enc k φ).length = k + n + 2 + φ.length * (k * (Nat.log2 (2 * n) + 1)) := by
  simp [SatM.enc, SatK.enc, List.length_flatMap]
  omega

/-- If every variable occurs in a k-CNF with m clauses then n ≤ k·m. -/
theorem n_le {k n : ℕ} {φ : Sat3.CNF n} (h : SatK.IsKCNF k φ) (ho : SatM.AllOccur φ) : n ≤ k * φ.length := by
  classical
  have h1 : (Finset.univ : Finset (Fin n)) ⊆ (φ.flatten.map Prod.fst).toFinset := by
    intro i _
    obtain ⟨C, hC, l, hl, rfl⟩ := ho i
    simp only [List.mem_toFinset, List.mem_map, List.mem_flatten]
    exact ⟨l, ⟨C, hC, hl⟩, rfl⟩
  have h2 := Finset.card_le_card h1
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : (φ.flatten.map Prod.fst).toFinset.card ≤ φ.flatten.length := (List.toFinset_card_le _).trans (le_of_eq (List.length_map _))
  have h4 : ∀ ψ : List (List (Sat3.Lit n)), (∀ C ∈ ψ, C.length ≤ k) → ψ.flatten.length ≤ k * ψ.length := by
    intro ψ
    induction ψ with
    | nil => simp
    | cons C ψ ih =>
      intro hh
      have a := hh C (by simp)
      have b := ih fun D hD => hh D (by simp [hD])
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.mul_succ]
      omega
  have := h4 φ h.1
  omega

/-- The length of the code, plus one, is at most 8·(k·m)². -/
theorem length_enc_succ_le {k n : ℕ} {φ : Sat3.CNF n} (hk : 1 ≤ k) (hm : 1 ≤ φ.length) (hn : n ≤ k * φ.length) :
    (SatM.enc k φ).length + 1 ≤ 8 * (k * φ.length) ^ 2 := by
  rw [length_enc]
  set m := φ.length
  have h1 : Nat.log2 (2 * n) ≤ 2 * n := by rw [Nat.log2_eq_log_two]; exact Nat.log_le_self _ _
  have h2 : k ≤ k * m := Nat.le_mul_of_pos_right _ hm
  have h3 : 1 ≤ k * m := Nat.mul_pos hk hm
  have h4 : m * (k * (Nat.log2 (2 * n) + 1)) ≤ k * m * (2 * (k * m) + 1) := by
    calc m * (k * (Nat.log2 (2 * n) + 1)) = k * m * (Nat.log2 (2 * n) + 1) := by ring
      _ ≤ k * m * (2 * (k * m) + 1) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-! ### Logarithms -/

/-- log₂(m+2) ≥ 1. -/
theorem one_le_log (m : ℕ) : (1 : ℝ) ≤ Real.logb 2 ((m : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  norm_num

/-- log₂(m+2) ≤ m + 2. -/
theorem log_le_self (m : ℕ) : Real.logb 2 ((m : ℝ) + 2) ≤ (m : ℝ) + 2 := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
  have h : ((m + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + 2 : ℕ) := by exact_mod_cast (Nat.lt_two_pow_self (n := m + 2)).le
  have e : (2 : ℝ) ^ ((m : ℝ) + 2) = (2 : ℝ) ^ (m + 2 : ℕ) := by rw [← Real.rpow_natCast]; push_cast; rfl
  rw [e]; exact_mod_cast h

/-- (log₂(m+2))^j ≤ 3·j!·2^j·m for m ≥ 1. -/
theorem log_pow_le (j : ℕ) {m : ℕ} (hm : 1 ≤ m) : Real.logb 2 ((m : ℝ) + 2) ^ j ≤ ((3 * j.factorial * 2 ^ j : ℕ) : ℝ) * m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hx : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith)
  have h1 := Real.pow_div_factorial_le_exp _ hx j
  rw [Real.exp_log hpos] at h1
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  rw [div_le_iff₀ hf] at h1
  have l2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2 : Real.logb 2 ((m : ℝ) + 2) ≤ 2 * Real.log ((m : ℝ) + 2) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h0 : 0 ≤ Real.logb 2 ((m : ℝ) + 2) := by linarith [one_le_log m]
  calc Real.logb 2 ((m : ℝ) + 2) ^ j ≤ (2 * Real.log ((m : ℝ) + 2)) ^ j := pow_le_pow_left₀ h0 h2 j
    _ = 2 ^ j * Real.log ((m : ℝ) + 2) ^ j := mul_pow _ _ _
    _ ≤ 2 ^ j * (((m : ℝ) + 2) * j.factorial) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 2 ^ j * ((3 * (m : ℝ)) * j.factorial) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hf.le) (by positivity)
    _ = ((3 * j.factorial * 2 ^ j : ℕ) : ℝ) * m := by push_cast; ring

/-- If r ≥ 1/(c·y^c) with c ≥ 1 and y ≥ 1 then c·y^c·r ≥ 1. -/
theorem one_le_mul_of_div_le {c : ℕ} {y r : ℝ} (hc : 1 ≤ c) (hy : 1 ≤ y) (h : 1 / ((c : ℝ) * y ^ c) ≤ r) : 1 ≤ (c : ℝ) * y ^ c * r := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hp : 0 < (c : ℝ) * y ^ c := by positivity
  rw [div_le_iff₀ hp] at h
  linarith

/-- k·m ≤ 2^(2·c·D·k·m·r), where D = 3·(c+1)!·2^(c+1), if r ≥ 1/(c·(log₂(m+2))^c). -/
theorem mul_le_two_rpow {c k m : ℕ} {r : ℝ} (hc : 1 ≤ c) (hk : 1 ≤ k) (hm : 1 ≤ m) (h : 1 / ((c : ℝ) * Real.logb 2 ((m : ℝ) + 2) ^ c) ≤ r) :
    ((k * m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((2 * c * (3 * (c + 1).factorial * 2 ^ (c + 1)) : ℕ) : ℝ) * ((k : ℝ) * m * r)) := by
  have hy := one_le_log m
  have h1 := one_le_mul_of_div_le hc hy h
  have h2 := log_pow_le (c + 1) hm
  set y := Real.logb 2 ((m : ℝ) + 2) with hyd
  set D : ℕ := 3 * (c + 1).factorial * 2 ^ (c + 1)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hr : 0 ≤ r := le_trans (by positivity) h
  -- y ≤ c·D·m·r
  have h3 : y ≤ (c : ℝ) * D * (m * r) := by
    calc y = y * 1 := (mul_one y).symm
      _ ≤ y * ((c : ℝ) * y ^ c * r) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = (c : ℝ) * r * y ^ (c + 1) := by ring
      _ ≤ (c : ℝ) * r * ((D : ℝ) * m) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (c : ℝ) * D * (m * r) := by ring
  have h4 : (k : ℝ) + y ≤ 2 * ((k : ℝ) * y) := by nlinarith
  have h5 : (k : ℝ) * y ≤ (c : ℝ) * D * ((k : ℝ) * m * r) := by
    calc (k : ℝ) * y ≤ (k : ℝ) * ((c : ℝ) * D * (m * r)) := mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = _ := by ring
  have h6 : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have h7 : (m : ℝ) ≤ (2 : ℝ) ^ y := by
    rw [hyd, Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]; linarith
  calc ((k * m : ℕ) : ℝ) = (k : ℝ) * m := by push_cast; ring
    _ ≤ (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ y := mul_le_mul h6 h7 (by positivity) (by positivity)
    _ = (2 : ℝ) ^ ((k : ℝ) + y) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)

/-! ### The time -/

/-- If L + 1 ≤ 8T², T ≤ 2^(H·X) and E ≤ G·X then q·(L + 2^E + 1)^q ≤ C·2^(C·X) with C = q·9^q +
q·(2H + G). -/
theorem time_le (q L E T H G : ℕ) {X : ℝ} (hX : 0 ≤ X) (hT1 : 1 ≤ T) (hL : L + 1 ≤ 8 * T ^ 2) (hT : (T : ℝ) ≤ (2 : ℝ) ^ ((H : ℝ) * X))
    (hE : (E : ℝ) ≤ (G : ℝ) * X) :
    ((q * (L + 2 ^ E + 1) ^ q : ℕ) : ℝ) ≤ ((q * 9 ^ q + q * (2 * H + G) : ℕ) : ℝ) * (2 : ℝ) ^ (((q * 9 ^ q + q * (2 * H + G) : ℕ) : ℝ) * X) := by
  have h1 : L + 2 ^ E + 1 ≤ 9 * (T ^ 2 * 2 ^ E) := by
    have a : 1 ≤ 2 ^ E := Nat.one_le_two_pow
    have b : 1 ≤ T ^ 2 := Nat.one_le_pow _ _ hT1
    nlinarith
  have h2 : ((T ^ 2 * 2 ^ E : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((2 * H + G : ℕ) : ℝ) * X) := by
    have e1 : ((2 : ℝ) ^ ((H : ℝ) * X)) ^ 2 = (2 : ℝ) ^ (2 * (H : ℝ) * X) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
    have e2 : ((2 : ℝ) ^ E) ≤ (2 : ℝ) ^ ((G : ℝ) * X) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
    calc ((T ^ 2 * 2 ^ E : ℕ) : ℝ) = (T : ℝ) ^ 2 * (2 : ℝ) ^ E := by push_cast; ring
      _ ≤ ((2 : ℝ) ^ ((H : ℝ) * X)) ^ 2 * (2 : ℝ) ^ ((G : ℝ) * X) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hT 2) e2 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (((2 * H + G : ℕ) : ℝ) * X) := by
          rw [e1, ← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring
  have h3 : ((L + 2 ^ E + 1 : ℕ) : ℝ) ≤ 9 * (2 : ℝ) ^ (((2 * H + G : ℕ) : ℝ) * X) := by
    calc ((L + 2 ^ E + 1 : ℕ) : ℝ) ≤ ((9 * (T ^ 2 * 2 ^ E) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = 9 * ((T ^ 2 * 2 ^ E : ℕ) : ℝ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h4 : ((2 : ℝ) ^ (((2 * H + G : ℕ) : ℝ) * X)) ^ q = (2 : ℝ) ^ (((q * (2 * H + G) : ℕ) : ℝ) * X) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
  have h5 : (2 : ℝ) ^ (((q * (2 * H + G) : ℕ) : ℝ) * X) ≤ (2 : ℝ) ^ (((q * 9 ^ q + q * (2 * H + G) : ℕ) : ℝ) * X) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right ?_ hX)
    exact_mod_cast Nat.le_add_left _ _
  have h6 : ((q * 9 ^ q : ℕ) : ℝ) ≤ ((q * 9 ^ q + q * (2 * H + G) : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
  calc ((q * (L + 2 ^ E + 1) ^ q : ℕ) : ℝ) = (q : ℝ) * ((L + 2 ^ E + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (9 * (2 : ℝ) ^ (((2 * H + G : ℕ) : ℝ) * X)) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3 q) (by positivity)
    _ = ((q * 9 ^ q : ℕ) : ℝ) * (2 : ℝ) ^ (((q * (2 * H + G) : ℕ) : ℝ) * X) := by rw [mul_pow, h4]; push_cast; ring
    _ ≤ _ := mul_le_mul h6 h5 (by positivity) (by positivity)

end ClauseBound.Alg.End
