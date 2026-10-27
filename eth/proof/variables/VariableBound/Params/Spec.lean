/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Params.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Setting and parameters of Appendix D: the computed parameters are those of the text

Each of `nbD`, `rbD`, `tbD` is made from a count: the number of the numbers below a bound at which a
property that is closed upwards does not hold yet (r̄ and t̄ are this count c, and n̄ = 2^(c − 1)).
If the
property holds somewhere up to the bound, the count is the least number with the property
(`count_spec`). For n̄ the property is (2Δ)^(2^a) > 2^n, which holds at a = ⌊log₂ n⌋ + 1; for r̄ it
is 3^j·2^β < 4^j, which holds at j = 3β + 1 because 54 < 64; for t̄ it is
m·(15n̄+16)^r̄ ≤ 2^c·(15n̄)^r̄, which holds at c = size m + r̄ if n̄ ≥ 2, because then 15n̄ + 16 ≤
2·15n̄. -/

public section

namespace VariableBound

open AppVariables

namespace Spec

/-- If p holds below N exactly at the numbers below k, it holds at min N k numbers below N. -/
theorem length_filter_range (p : ℕ → Bool) (N k : ℕ) (h : ∀ j < N, (p j = true ↔ j < k)) : ((List.range N).filter p).length = min N k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih fun j hj => h j (Nat.lt_succ_of_lt hj)]
    have hN := h N (Nat.lt_succ_self N)
    by_cases hk : N < k
    · rw [List.filter_singleton, hN.2 hk]
      simp only [cond_true, List.length_singleton]
      omega
    · have hf : p N = false := by
        rcases hb : p N with _ | _
        · rfl
        · exact absurd (hN.1 hb) hk
      rw [List.filter_singleton, hf]
      simp only [cond_false, List.length_nil]
      omega

/-- Let P be closed upwards and hold at some number j ≤ N, and let p decide «not P». Then the number
of j < N with p j is the least number at which P holds. -/
theorem count_spec (P : ℕ → Prop) (p : ℕ → Bool) (N : ℕ) (hp : ∀ j, p j = true ↔ ¬ P j) (up : ∀ j, P j → P (j + 1)) (hN : ∃ j ≤ N, P j) :
    P ((List.range N).filter p).length ∧ ∀ j < ((List.range N).filter p).length, ¬ P j := by
  classical
  obtain ⟨j₀, hj₀, hP⟩ := hN
  have hex : ∃ j, P j := ⟨j₀, hP⟩
  have hk : Nat.find hex ≤ N := (Nat.find_min' hex hP).trans hj₀
  have hmono : ∀ j, Nat.find hex ≤ j → P j := fun j hj => Nat.le_induction (Nat.find_spec hex) (fun i _ hi => up i hi) j hj
  have hlen : ((List.range N).filter p).length = Nat.find hex := by
    rw [length_filter_range p N (Nat.find hex) fun j _ => (hp j).trans ⟨fun h => not_le.1 fun hle => h (hmono j hle), fun h => Nat.find_min hex h⟩]
    exact min_eq_right hk
  rw [hlen]
  exact ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩

/-- What `count_spec` gives for n̄: the count a of `nbD` is the least number with 2^n < (2Δ)^(2^a),
for Δ ≥ 1. -/
theorem nb_count (n Δ : ℕ) (hΔ : 1 ≤ Δ) :
    2 ^ n < (2 * Δ) ^ 2 ^ ((List.range (Nat.log 2 n + 1)).filter fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)).length ∧
      ∀ a < ((List.range (Nat.log 2 n + 1)).filter fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)).length, (2 * Δ) ^ 2 ^ a ≤ 2 ^ n := by
  have h := count_spec (fun a => 2 ^ n < (2 * Δ) ^ 2 ^ a) (fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)) (Nat.log 2 n + 1)
    (fun a => by simp only [decide_eq_true_eq, not_lt])
    (fun a ha => ha.trans_le (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ a))))
    ⟨Nat.log 2 n + 1, le_rfl, by
      calc 2 ^ n < 2 ^ 2 ^ (Nat.log 2 n + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_pow_succ_log_self (by norm_num) n)
        _ ≤ (2 * Δ) ^ 2 ^ (Nat.log 2 n + 1) := Nat.pow_le_pow_left (by omega) _⟩
  exact ⟨h.1, fun a ha => not_lt.1 (h.2 a ha)⟩

/-- The computed n̄ is the n̄ of the text, if Δ ≥ 1 and 2Δ ≤ 2^n. -/
theorem isNb_nbD (n Δ : ℕ) (hΔ : 1 ≤ Δ) (h : 2 * Δ ≤ 2 ^ n) : IsNb n Δ (nbD n Δ) := by
  obtain ⟨h1, h2⟩ := nb_count n Δ hΔ
  unfold nbD
  generalize ((List.range (Nat.log 2 n + 1)).filter fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)).length = c at h1 h2
  have hc : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp only [pow_zero, pow_one] at h1
      omega
    · exact hc
  refine ⟨⟨c - 1, rfl⟩, h2 (c - 1) (by omega), ?_⟩
  rwa [← pow_succ', Nat.sub_add_cancel hc]

/-- The computed n̄ is at least 2, if Δ ≥ 1 and (2Δ)² ≤ 2^n. -/
theorem two_le_nbD (n Δ : ℕ) (hΔ : 1 ≤ Δ) (h : (2 * Δ) ^ 2 ≤ 2 ^ n) : 2 ≤ nbD n Δ := by
  obtain ⟨h1, -⟩ := nb_count n Δ hΔ
  unfold nbD
  generalize ((List.range (Nat.log 2 n + 1)).filter fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)).length = c at h1
  have hc : 2 ≤ c := by
    by_contra hlt
    have h3 : (2 * Δ) ^ 2 ^ c ≤ (2 * Δ) ^ 2 :=
      Nat.pow_le_pow_right (by omega) (by calc 2 ^ c ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
                                            _ = 2 := by norm_num)
    omega
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (c - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The computed r̄ is the r̄ of the text. -/
theorem isRb_rbD (β : ℕ) : IsRb β (rbD β) := by
  refine count_spec (fun j => 3 ^ j * 2 ^ β < 4 ^ j) _ (3 * β + 2) (fun j => by simp only [decide_eq_true_eq]) (fun j hj => ?_) ⟨3 * β + 1, by omega, ?_⟩
  · rw [pow_succ, pow_succ]
    have : 0 < 4 ^ j := by positivity
    nlinarith
  · have h : (54 : ℕ) ^ β ≤ 64 ^ β := Nat.pow_le_pow_left (by norm_num) β
    have e1 : 3 ^ (3 * β + 1) * 2 ^ β = 3 * 54 ^ β := by
      rw [pow_succ, pow_mul, show (54 : ℕ) = 3 ^ 3 * 2 by norm_num, mul_pow]; ring
    have e2 : 4 ^ (3 * β + 1) = 4 * 64 ^ β := by
      rw [pow_succ, pow_mul]; norm_num [mul_comm]
    have : 0 < 64 ^ β := by positivity
    rw [e1, e2]
    omega

/-- The condition on c in the definition of t̄, with the denominators cleared; for n̄ ≥ 1. -/
theorem tb_iff (m nb rb c : ℕ) (hnb : 1 ≤ nb) : (m : ℚ) * (1 + pp nb) ^ rb ≤ 2 ^ c ↔ m * (15 * nb + 16) ^ rb ≤ 2 ^ c * (15 * nb) ^ rb := by
  have h0 : (0 : ℚ) < 15 * nb := by
    have : (1 : ℚ) ≤ nb := by exact_mod_cast hnb
    linarith
  have e : 1 + pp nb = (15 * nb + 16) / (15 * nb) := by
    unfold pp
    field_simp
  rw [e, div_pow, mul_div_assoc', div_le_iff₀ (pow_pos h0 rb)]
  exact_mod_cast Iff.rfl

/-- The computed t̄ is the t̄ of the text, if n̄ ≥ 2. -/
theorem isTb_tbD (m nb rb : ℕ) (hnb : 2 ≤ nb) : IsTb m nb rb (tbD m nb rb) := by
  have h := count_spec (fun c => m * (15 * nb + 16) ^ rb ≤ 2 ^ c * (15 * nb) ^ rb) (fun c => decide (¬ m * (15 * nb + 16) ^ rb ≤ 2 ^ c * (15 * nb) ^ rb))
    (Nat.size m + rb + 1) (fun j => by simp only [decide_eq_true_eq])
    (fun c hc => hc.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ c))))
    ⟨Nat.size m + rb, Nat.le_succ _, by
      calc m * (15 * nb + 16) ^ rb ≤ 2 ^ Nat.size m * (2 * (15 * nb)) ^ rb :=
            Nat.mul_le_mul (Nat.lt_size_self m).le (Nat.pow_le_pow_left (by omega) rb)
        _ = 2 ^ (Nat.size m + rb) * (15 * nb) ^ rb := by rw [mul_pow, pow_add, mul_assoc]⟩
  exact ⟨(tb_iff m nb rb _ (by omega)).2 h.1, fun c hc => fun hq => h.2 c hc ((tb_iff m nb rb c (by omega)).1 hq)⟩

end Spec

/-- «Setting and parameters»: the computed n̄ (for Δ ≥ 1 and 2Δ ≤ 2^n; it is at least 2 if (2Δ)² ≤
2^n), r̄ and t̄ (for n̄ ≥ 2) are the numbers that the text defines. -/
theorem stParamSpec : StParamSpec := ⟨Spec.isNb_nbD, Spec.two_le_nbD, Spec.isRb_rbD, Spec.isTb_tbD⟩

end VariableBound
