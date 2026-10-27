/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.TopDefs
import ClauseBound.TopN.End
import ClauseBound.Alg.End
import WidthK.Decode
import CountKSat.InOut

/-! # From the function of the padded input to the Turing machine, for the bound in n of Theorem D (exponent k²·n·log log n/√(log n))

`stEndO : StEndO`, from `StPaddedW` (the padding machine), `StCorrectO`, `StCertO` and `StArithO`.
The two constants of the function are chosen in this order: c from `StArithO`, then n₀ from
`StCorrectO` for this c, then the constant A of `StArithO` for c and n₀. The padding machine runs
for q·(|x| + 2^(e x) + 1)^q steps on the input x. For the code x of an instance of k-SAT on n
variables |x| + 1 ≤ (k·2^k+1)·(n+2)^(k+1). Let r be the function in the hypotheses of `StEndO`, e_l
the exponent `e` of the level l chosen for n, and s the length of the list `slU` at that level. The
exponent e x is at most n,
which is used if n is below a constant, and at most A·n·e_l·(s+1) otherwise, so it is O(n·r(n)) in
both cases. Because r(n) ≥ 1/(c₁·(log₂(n+2))^c₁), also log₂(n+2) = O(n·r(n)). The same argument is
used in proof/rates/ClauseBound/TopN/End.lean. -/

public section

namespace ClauseBound.ParityChecks.EndOL

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End ClauseBound.ParityChecks

/-- The exponent of a plan, or else n, is at most n. -/
theorem planAtO_getD_le {Idx : Type} [Enc Idx] (S : Solver Idx) (c n₀ k n : ℕ) (i : Idx) (s : ℕ) : (planAtO S c n₀ k n i s).getD n ≤ n := by
  unfold planAtO
  split_ifs with hc
  · cases h : needNetC S (List.replicate n ()) i (UbOL k (S.K i) n (blockN k n s)) (PbOL (S.K i) n (blockN k n s)) 0 with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      split_ifs with h2
      · simpa using h2
      · simp
  · simp

/-- The padding machine, run on the function and the exponent function of a solver with a sequence
of levels, counts within C·2^(C·n·r(n)) steps. -/
theorem stEndO (hP : StPaddedW) (hC : StCorrectO) (hK : StCertO) (hA : StArithO) : StEndO := by
  intro Idx _ S e C₀ Q hS slU C hsl h1 h2 k r c₁ hk hr he
  set K₀ := S.K (Q.idx 0) with hK₀
  obtain ⟨c, hA⟩ := hA Idx S e C₀ Q hS slU C k hk h1 h2
  obtain ⟨n₀, hC⟩ := hC c
  obtain ⟨A, hA⟩ := hA n₀
  obtain ⟨hAN, heN⟩ := hK Idx S hS c n₀ k Q.pick slU Q.pick_poly hsl
  obtain ⟨N, q, hfin, hN⟩ := hP (eO S c n₀ k Q.pick slU) (AO S c n₀ k Q.pick slU) heN hAN
  -- c₁ ≥ 1, because e is positive
  have hc : 1 ≤ c₁ := by
    rcases Nat.eq_zero_or_pos c₁ with h0 | h0
    · exfalso
      have g1 := he (K₀ ^ 17) le_rfl
      have g2 := Q.e_ge (Q.pick (root17 (K₀ ^ 17))).1.length
      have g3 : (2 : ℝ) ≤ S.K (Q.idx (Q.pick (root17 (K₀ ^ 17))).1.length) := by exact_mod_cast Q.K_two _
      have g4 : 0 < Real.logb 2 (S.K (Q.idx (Q.pick (root17 (K₀ ^ 17))).1.length)) := Real.logb_pos (by norm_num) (by linarith)
      have g5 : 0 < 1 / Real.logb 2 (S.K (Q.idx (Q.pick (root17 (K₀ ^ 17))).1.length)) ^ C₀ := by positivity
      have g6 : 0 < e (Q.pick (root17 (K₀ ^ 17))).1.length * (((slU (Q.pick (root17 (K₀ ^ 17))).1).length : ℝ) + 1) := by
        have : 0 < e (Q.pick (root17 (K₀ ^ 17))).1.length := lt_of_lt_of_le g5 g2
        positivity
      rw [h0] at g1
      simp only [Nat.cast_zero, zero_mul] at g1
      linarith
    · exact h0
  set D : ℕ := c₁ * (3 * (c₁ + 1).factorial * 2 ^ (c₁ + 1))
  set H : ℕ := (k + 1) * D
  set G : ℕ := A * c₁ + c₁ * (K₀ ^ 17 + 2) ^ c₁
  set a : ℕ := (k * 2 ^ k + 1) * 2 ^ (k + 1)
  refine ⟨N, q * (a + 1) ^ q + q * (H + G), hfin, fun n φ hφ => ?_⟩
  have hdec : decU k (SatK.enc k φ) = (List.replicate n (), Decode.toN φ) := stDecU k n φ hk hφ.1
  have hnK : nK k (SatK.enc k φ) = n := by rw [nK, hdec, List.length_replicate]
  have heq : eO S c n₀ k Q.pick slU (SatK.enc k φ) = (planAtO S c n₀ k n (Q.pick (root17 n)).2 (slU (Q.pick (root17 n)).1).length).getD n := by
    rw [eO, planO, idxN, precN, hnK]
  have hEn : eO S c n₀ k Q.pick slU (SatK.enc k φ) ≤ n := heq ▸ planAtO_getD_le S c n₀ k n _ _
  have hlen : (SatK.enc k φ).length + 1 ≤ (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) := DecodeK.length_enc_succ_le (φ := φ) hφ
  have hx := hN (SatK.enc k φ)
  rw [hC Idx S e C₀ Q hS slU k n φ hk hφ (pad (eO S c n₀ k Q.pick slU (SatK.enc k φ))) (by simp [pad])] at hx
  obtain ⟨ev⟩ := hx
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  unfold SatK.boundN
  refine Nat.le_floor ?_
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · -- n = 0
    subst hn0
    have hE0 : eO S c n₀ k Q.pick slU (SatK.enc k φ) = 0 := Nat.le_zero.1 hEn
    have ht := time_le' q (SatK.enc k φ).length (eO S c n₀ k Q.pick slU (SatK.enc k φ)) a H G (X := 0) le_rfl
      (by
        simp only [mul_zero, Real.rpow_zero, mul_one]
        exact_mod_cast hlen)
      (by rw [hE0]; simp)
    refine ht.trans (le_of_eq ?_)
    simp
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hrn := hr n hn1
    have hr0 : 0 ≤ r n := le_trans (by have := one_le_log n; positivity) hrn
    have hX : 0 ≤ (n : ℝ) * r n := by positivity
    -- the length of the code
    have hlog := log_le_mul hc hn1 hrn
    have hL : (((SatK.enc k φ).length + 1 : ℕ) : ℝ) ≤ (a : ℝ) * (2 : ℝ) ^ ((H : ℝ) * ((n : ℝ) * r n)) := by
      have p1 : ((n : ℝ) + 2) ^ (k + 1) ≤ (2 : ℝ) ^ ((H : ℝ) * ((n : ℝ) * r n)) := by
        have p0 : (n : ℝ) + 2 = (2 : ℝ) ^ Real.logb 2 ((n : ℝ) + 2) := (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
        calc ((n : ℝ) + 2) ^ (k + 1) = ((2 : ℝ) ^ Real.logb 2 ((n : ℝ) + 2)) ^ (k + 1) := by rw [← p0]
          _ = (2 : ℝ) ^ (Real.logb 2 ((n : ℝ) + 2) * ((k + 1 : ℕ) : ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          _ ≤ (2 : ℝ) ^ ((H : ℝ) * ((n : ℝ) * r n)) := by
              refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
              calc Real.logb 2 ((n : ℝ) + 2) * ((k + 1 : ℕ) : ℝ) ≤ ((D : ℕ) : ℝ) * ((n : ℝ) * r n) * ((k + 1 : ℕ) : ℝ) :=
                    mul_le_mul_of_nonneg_right hlog (by positivity)
                _ = (H : ℝ) * ((n : ℝ) * r n) := by simp only [H]; push_cast; ring
      have p2 : ((k * 2 ^ k + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by
        have : k * 2 ^ k + 1 ≤ a := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
        exact_mod_cast this
      calc (((SatK.enc k φ).length + 1 : ℕ) : ℝ) ≤ (((k * 2 ^ k + 1) * (n + 2) ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hlen
        _ = ((k * 2 ^ k + 1 : ℕ) : ℝ) * ((n : ℝ) + 2) ^ (k + 1) := by push_cast; ring
        _ ≤ (a : ℝ) * (2 : ℝ) ^ ((H : ℝ) * ((n : ℝ) * r n)) := mul_le_mul p2 p1 (by positivity) (by positivity)
    -- the exponent
    have hE : (eO S c n₀ k Q.pick slU (SatK.enc k φ) : ℝ) ≤ (G : ℝ) * ((n : ℝ) * r n) := by
      have hGa : ((A * c₁ : ℕ) : ℝ) * ((n : ℝ) * r n) ≤ (G : ℝ) * ((n : ℝ) * r n) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right _ _) hX
      have hGb : ((c₁ * (K₀ ^ 17 + 2) ^ c₁ : ℕ) : ℝ) * ((n : ℝ) * r n) ≤ (G : ℝ) * ((n : ℝ) * r n) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left _ _) hX
      by_cases hs : n < K₀ ^ 17
      · refine le_trans ?_ hGb
        have g1 := one_le_mul_of_div_le hc (one_le_log n) hrn
        have g2 : Real.logb 2 ((n : ℝ) + 2) ≤ ((K₀ ^ 17 + 2 : ℕ) : ℝ) := by
          refine (log_le_self n).trans ?_
          have : n + 2 ≤ K₀ ^ 17 + 2 := by omega
          exact_mod_cast this
        have g3 : Real.logb 2 ((n : ℝ) + 2) ^ c₁ ≤ ((K₀ ^ 17 + 2 : ℕ) : ℝ) ^ c₁ := pow_le_pow_left₀ (by linarith [one_le_log n]) g2 _
        have g4 : 1 ≤ ((c₁ * (K₀ ^ 17 + 2) ^ c₁ : ℕ) : ℝ) * r n := by
          refine g1.trans (mul_le_mul_of_nonneg_right ?_ hr0)
          rw [Nat.cast_mul, Nat.cast_pow]
          exact mul_le_mul_of_nonneg_left g3 (by positivity)
        calc (eO S c n₀ k Q.pick slU (SatK.enc k φ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hEn
          _ = (n : ℝ) * 1 := (mul_one _).symm
          _ ≤ (n : ℝ) * (((c₁ * (K₀ ^ 17 + 2) ^ c₁ : ℕ) : ℝ) * r n) := mul_le_mul_of_nonneg_left g4 (by positivity)
          _ = _ := by ring
      · refine le_trans ?_ hGa
        have g1 := hA n (not_lt.1 hs)
        have g2 := he n (not_lt.1 hs)
        rw [heq]
        calc _ ≤ A * n * e (Q.pick (root17 n)).1.length * (((slU (Q.pick (root17 n)).1).length : ℝ) + 1) := g1
          _ = A * n * (e (Q.pick (root17 n)).1.length * (((slU (Q.pick (root17 n)).1).length : ℝ) + 1)) := by ring
          _ ≤ A * n * (c₁ * r n) := mul_le_mul_of_nonneg_left g2 (by positivity)
          _ = _ := by push_cast; ring
    have ht := time_le' q (SatK.enc k φ).length (eO S c n₀ k Q.pick slU (SatK.enc k φ)) a H G hX hL hE
    refine ht.trans (le_of_eq ?_)
    congr 2
    ring

end ClauseBound.ParityChecks.EndOL
