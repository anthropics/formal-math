/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Tied.Defs
public import ClauseBound.Alg.End
public import CountKSatRate.Interfaces
import CountKSat.InOut

/-! # From the top level in m to the machine, for the named function and exponent

`topM_of_arith` states the top level in m with a conclusion that names what the machine computes
(`GeneralPieces.Tied.TopM`): the padding machine, made from the exponent `eM S pick` and the
function `AM S pick`, computes that function on
every input; on the code of a k-CNF the function is the number of satisfying assignments; the
exponent is O(k·m·r(m)). `countInRate_of_topM` derives from it the form with "there is a machine". -/

public section

namespace GeneralPieces.Top

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat ClauseBound.Alg ClauseBound.Alg.End

/-- The padding machine, run on the function and the exponent function of a solver with a sequence
of indices, computes that function and counts within C·2^(C·k·m·r(m)) steps. The inequality from the
proof of Theorem A(c), that the exponent at the level picked for m is
O(k·m·e_ℓ), is the hypothesis `hA`, for this sequence. -/
theorem topM_of_arith (hP : CountKSatRate.StPaddedW) (hC : StCorrectM) (hK : StCertM) {Idx : Type} [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ)
    (Q : S.Seq e C₀) (hA : ∃ A : ℕ, ∀ k m : ℕ, 1 ≤ k → S.K (Q.idx 0) ^ 9 ≤ m → (needTop S (Q.pick (root9 m)).2 k m : ℝ) ≤ A * k * m * e (Q.pick (root9 m)).1.length)
    (hS : S.Poly) (r : ℕ → ℝ) (c₁ : ℕ) (hr : ∀ m : ℕ, 1 ≤ m → 1 / (c₁ * Real.logb 2 ((m : ℝ) + 2) ^ c₁) ≤ r m)
    (he : ∀ m : ℕ, S.K (Q.idx 0) ^ 9 ≤ m → e (Q.pick (root9 m)).1.length ≤ c₁ * r m) : Tied.TopM S Q.pick r := by
  set K₀ := S.K (Q.idx 0) with hK₀
  obtain ⟨hAM, heM⟩ := hK Idx S hS Q.pick Q.pick_poly
  obtain ⟨N, q, hfin, hN⟩ := hP (eM S Q.pick) (AM S Q.pick) heM hAM
  obtain ⟨A, hA⟩ := hA
  -- c₁ ≥ 1, because e is positive
  have hc : 1 ≤ c₁ := by
    rcases Nat.eq_zero_or_pos c₁ with h0 | h0
    · exfalso
      have h1 := he (K₀ ^ 9) le_rfl
      have h2 := Q.e_ge (Q.pick (root9 (K₀ ^ 9))).1.length
      have h3 : (2 : ℝ) ≤ S.K (Q.idx (Q.pick (root9 (K₀ ^ 9))).1.length) := by exact_mod_cast Q.K_two _
      have h4 : 0 < Real.logb 2 (S.K (Q.idx (Q.pick (root9 (K₀ ^ 9))).1.length)) := Real.logb_pos (by norm_num) (by linarith)
      have h5 : 0 < 1 / Real.logb 2 (S.K (Q.idx (Q.pick (root9 (K₀ ^ 9))).1.length)) ^ C₀ := by positivity
      rw [h0] at h1
      simp only [Nat.cast_zero, zero_mul] at h1
      linarith
    · exact h0
  set H : ℕ := 2 * c₁ * (3 * (c₁ + 1).factorial * 2 ^ (c₁ + 1))
  set G : ℕ := A * c₁ + c₁ * (K₀ ^ 9 + 2) ^ c₁
  have hEall : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
      (eM S Q.pick (SatM.enc k φ) : ℝ) ≤ (G : ℝ) * ((k : ℝ) * φ.length * r φ.length) := by
    intro k n φ hk hm hφ ho
    set m := φ.length with hmd
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hrm := hr m hm
    have hr0 : 0 ≤ r m := le_trans (by have := one_le_log m; positivity) hrm
    have hX : 0 ≤ (k : ℝ) * m * r m := by positivity
    have hn := n_le hφ ho
    obtain ⟨hEn, hEt⟩ := eM_enc_le hS Q.pick hk hφ.1
    have hGa : ((A * c₁ : ℕ) : ℝ) * ((k : ℝ) * m * r m) ≤ (G : ℝ) * ((k : ℝ) * m * r m) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right _ _) hX
    have hGb : ((c₁ * (K₀ ^ 9 + 2) ^ c₁ : ℕ) : ℝ) * ((k : ℝ) * m * r m) ≤ (G : ℝ) * ((k : ℝ) * m * r m) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left _ _) hX
    by_cases hs : m < K₀ ^ 9
    · refine le_trans ?_ hGb
      have h1 := one_le_mul_of_div_le hc (one_le_log m) hrm
      have h2 : Real.logb 2 ((m : ℝ) + 2) ≤ ((K₀ ^ 9 + 2 : ℕ) : ℝ) := by
        refine (log_le_self m).trans ?_
        have : m + 2 ≤ K₀ ^ 9 + 2 := by omega
        exact_mod_cast this
      have h3 : Real.logb 2 ((m : ℝ) + 2) ^ c₁ ≤ ((K₀ ^ 9 + 2 : ℕ) : ℝ) ^ c₁ := pow_le_pow_left₀ (by linarith [one_le_log m]) h2 _
      have h4 : 1 ≤ ((c₁ * (K₀ ^ 9 + 2) ^ c₁ : ℕ) : ℝ) * r m := by
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ hr0)
        rw [Nat.cast_mul, Nat.cast_pow]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      calc (eM S Q.pick (SatM.enc k φ) : ℝ) ≤ ((k * m : ℕ) : ℝ) := by exact_mod_cast hEn.trans hn
        _ = (k : ℝ) * m * 1 := by push_cast; ring
        _ ≤ (k : ℝ) * m * (((c₁ * (K₀ ^ 9 + 2) ^ c₁ : ℕ) : ℝ) * r m) := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring
    · refine le_trans ?_ hGa
      have h1 := hA k m hk (not_lt.1 hs)
      have h2 := he m (not_lt.1 hs)
      calc (eM S Q.pick (SatM.enc k φ) : ℝ) ≤ (needTop S (Q.pick (root9 m)).2 k m : ℝ) := by exact_mod_cast hEt
        _ ≤ A * k * m * e (Q.pick (root9 m)).1.length := h1
        _ ≤ A * k * m * (c₁ * r m) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by push_cast; ring
  refine ⟨hAM, heM, fun k n φ hk hm hφ ho pad hpad => hC Idx S e C₀ Q hS k n φ hk hm hφ ho pad hpad, ⟨G, hEall⟩,
    N, q, q * 9 ^ q + q * (2 * H + G), hfin, hN, fun k n φ hk hm hφ ho => ?_⟩
  have hE := hEall k n φ hk hm hφ ho
  set m := φ.length with hmd
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrm := hr m hm
  have hr0 : 0 ≤ r m := le_trans (by have := one_le_log m; positivity) hrm
  have hX : 0 ≤ (k : ℝ) * m * r m := by positivity
  have hn := n_le hφ ho
  have hx := hN (SatM.enc k φ)
  rw [hC Idx S e C₀ Q hS k n φ hk hm hφ ho (pad (eM S Q.pick (SatM.enc k φ))) (by simp [pad])] at hx
  obtain ⟨ev⟩ := hx
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  unfold SatM.bound
  refine Nat.le_floor ?_
  have ht := time_le q (SatM.enc k φ).length (eM S Q.pick (SatM.enc k φ)) (k * m) H G hX (Nat.mul_pos hk hm)
    (length_enc_succ_le hk hm hn) (mul_le_two_rpow hc hk hm hrm) hE
  refine ht.trans (le_of_eq ?_)
  congr 2
  ring

/-- The form with "there is a machine" follows; it does not name what the machine computes. -/
theorem countInRate_of_topM {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} {r : ℕ → ℝ} (h : Tied.TopM S pick r) : SatM.CountInRate r :=
  let ⟨N, _, C, hfin, _, hc⟩ := h.machine
  ⟨N, C, hfin, hc⟩

end GeneralPieces.Top
