/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Params.Defs
import ClauseBound.ParityChecks.CertLib

/-! # Setting and parameters of Appendix D: certificates

The numbers n̄, β, r̄, t̄ of proof/variables/VariableBound/Params/Defs.lean are given in unary when
their arguments are. Each of n̄, r̄, t̄ is made from the length of a list: the numbers below a bound
given in unary that pass a test.
The test compares products of powers whose exponents are given in unary, because the index is below
that bound (for n̄ the exponent is 2^a ≤ 2(n + 1)); so it is polynomial-time
(`filter_range_polyT`). For n̄ = 2^(length − 1) the bound n̄ ≤ n + 1 is used as well. The class
PolyT of polynomial-time functions and its closure lemmas come from proof/machines/ToTuring and
proof/rates/ClauseBound/ParityChecks/CertLib.lean. -/

public section

namespace VariableBound

open Groundwork AppVariables PaddedDescent.F ClauseBound.ParityChecks.CertLib

namespace Cert

variable {α : Type} [Enc α]

/-- The list of the i < n that pass a test is polynomial-time, for n in unary; the test is only
needed for indices given in unary. -/
theorem filter_range_polyT {n : α → ℕ} {f : α → ℕ → Bool} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => (List.range (n x)).filter (f x) :=
  (PolyT.filter (f := fun x k => f x (min k (n x))) hf (PolyT.range hn)).congr fun x =>
    List.filter_congr fun k hk => by rw [min_eq_left (List.mem_range.1 hk).le]

/-- 2^⌊log₂ n⌋ ≤ n + 1. -/
theorem two_pow_log_le (n : ℕ) : 2 ^ Nat.log 2 n ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · exact (Nat.pow_log_le_self 2 h.ne').trans (Nat.le_succ n)

/-- n̄ ≤ n + 1. -/
theorem nbD_le (n Δ : ℕ) : nbD n Δ ≤ n + 1 := by
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) (two_pow_log_le n)
  have h := List.length_filter_le (fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)) (List.range (Nat.log 2 n + 1))
  rw [List.length_range] at h
  omega

/-- n̄ is given in unary if n is and Δ is polynomial-time. -/
theorem nbD_unary {n Δ : α → ℕ} (hn : Unary n) (hΔ : PolyT Δ) : Unary fun x => nbD (n x) (Δ x) := by
  have hN : Unary fun x => Nat.log 2 (n x) + 1 := (log_unary hn).add (Unary.const 1)
  have hmin : Unary fun p : α × ℕ => min p.2 (Nat.log 2 (n p.1) + 1) := unary_min_right PolyT.id'.snd (hN.comp PolyT.id'.fst)
  have hexp : Unary fun p : α × ℕ => 2 ^ min p.2 (Nat.log 2 (n p.1) + 1) :=
    Unary.of_le (((Unary.const 2).mul ((hn.comp PolyT.id'.fst).add (Unary.const 1)))) (PolyT.two_pow hmin) fun p =>
      calc 2 ^ min p.2 (Nat.log 2 (n p.1) + 1) ≤ 2 ^ (Nat.log 2 (n p.1) + 1) := Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)
        _ = 2 * 2 ^ Nat.log 2 (n p.1) := pow_succ' _ _
        _ ≤ 2 * (n p.1 + 1) := Nat.mul_le_mul_left 2 (two_pow_log_le _)
  have hl : PolyT fun x => (List.range (Nat.log 2 (n x) + 1)).filter fun a => decide ((2 * Δ x) ^ 2 ^ a ≤ 2 ^ n x) :=
    filter_range_polyT (f := fun x a => decide ((2 * Δ x) ^ 2 ^ a ≤ 2 ^ n x)) hN
      (PolyT.decide_le (PolyT.pow_unary ((PolyT.const 2).mul (PolyT.comp hΔ PolyT.id'.fst)) hexp) (PolyT.two_pow (hn.comp PolyT.id'.fst)))
  exact Unary.of_le (hn.add (Unary.const 1)) (PolyT.two_pow (unary_sub (Unary.of_length hl) (PolyT.const 1))) fun x => nbD_le _ _

/-- β is given in unary if n and n̄ are and m is polynomial-time. -/
theorem beta_unary {n m nb : α → ℕ} (hn : Unary n) (hm : PolyT m) (hnb : Unary nb) : Unary fun x => beta (n x) (m x) (nb x) :=
  (hn.add (clog_unary (choose_polyT hm (hnb.add (Unary.const 1))))).add (Unary.const 1)

/-- r̄ is given in unary if β is. -/
theorem rbD_unary {β : α → ℕ} (hβ : Unary β) : Unary fun x => rbD (β x) := by
  have hN : Unary fun x => 3 * β x + 2 := ((Unary.const 3).mul hβ).add (Unary.const 2)
  have hmin : Unary fun p : α × ℕ => min p.2 (3 * β p.1 + 2) := unary_min_right PolyT.id'.snd (hN.comp PolyT.id'.fst)
  exact Unary.of_length (filter_range_polyT (f := fun x j => decide (¬ 3 ^ j * 2 ^ β x < 4 ^ j)) hN
    (PolyT.decide_not (PolyT.decide_lt ((PolyT.pow_unary (PolyT.const 3) hmin).mul (PolyT.two_pow (hβ.comp PolyT.id'.fst))) (PolyT.pow_unary (PolyT.const 4) hmin))))

/-- The number of binary digits of m is given in unary if m is polynomial-time. -/
theorem size_unary {m : α → ℕ} (hm : PolyT m) : Unary fun x => Nat.size (m x) :=
  unary_congr (clog_unary (hm.add (PolyT.const 1))) fun x => by rw [clog_two_eq, Nat.add_sub_cancel]

/-- t̄ is given in unary if r̄ is and m and n̄ are polynomial-time. -/
theorem tbD_unary {m nb rb : α → ℕ} (hm : PolyT m) (hnb : PolyT nb) (hrb : Unary rb) : Unary fun x => tbD (m x) (nb x) (rb x) := by
  have hN : Unary fun x => Nat.size (m x) + rb x + 1 := ((size_unary hm).add hrb).add (Unary.const 1)
  have hmin : Unary fun p : α × ℕ => min p.2 (Nat.size (m p.1) + rb p.1 + 1) := unary_min_right PolyT.id'.snd (hN.comp PolyT.id'.fst)
  have hnb' : PolyT fun p : α × ℕ => 15 * nb p.1 := (PolyT.const 15).mul (PolyT.comp hnb PolyT.id'.fst)
  have hrb' : Unary fun p : α × ℕ => rb p.1 := hrb.comp PolyT.id'.fst
  exact Unary.of_length (filter_range_polyT (f := fun x c => decide (¬ m x * (15 * nb x + 16) ^ rb x ≤ 2 ^ c * (15 * nb x) ^ rb x)) hN
    (PolyT.decide_not (PolyT.decide_le ((PolyT.comp hm PolyT.id'.fst).mul (PolyT.pow_unary (hnb'.add (PolyT.const 16)) hrb'))
      ((PolyT.two_pow hmin).mul (PolyT.pow_unary hnb' hrb')))))

end Cert

/-- «Setting and parameters»: the computed n̄, β, r̄, t̄ are given in unary if n, Δ, m, β, n̄, r̄
are. -/
theorem stCertParam : StCertParam := fun _ _ _ _ _ _ _ _ hn hΔ hm hβ hnb hrb =>
  ⟨Cert.nbD_unary hn hΔ.poly, Cert.beta_unary hn hm.poly hnb, Cert.rbD_unary hβ, Cert.tbD_unary hm.poly hnb.poly hrb⟩

end VariableBound
