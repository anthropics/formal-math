/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PairsToBound.Width
import VariableBound.Paper.Forms
import ClauseBound.Alg.Decode
import ClauseBound.Alg.End
import CountKSat.InOut
import CountKSat.Poly
import CountKSatRate.Brute
import CountKSatRate.Cert
import CountKSatRate.Pad
import Wrap.Sim
import ToTuring.Closure.Basic
import ToTuring.Lib.List1b
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The machine that tries all assignments

**The sentence answered** (Step 6 of Appendix D). «In the other cases … the algorithm tries all
assignments; as there are fewer than (2n+1)^k ≤ n^(2k) clauses, this takes time 2^n·n^{O(k)},
reading the input included.»

**What is proved.**
* `everyExhaustiveMachineTriesAll : EveryExhaustiveMachineTriesAll`: EVERY machine that computes the
  named function `exhaust` (exhaustive counting) with a padding string of 2ⁿ units, within q·(|x| +
  2ⁿ + 1)^q steps, counts the satisfying assignments of every k-CNF on n ≥ 2 variables, k ≥ 1,
  within 2^{c·n}·n^{c·k} steps, for c = 8q.
* `exhaustiveMachineExists : ExhaustiveMachineExists`: there is such a machine, with finite
  alphabets.

**How.**
* The value (`exhaust_enc`). On the code of (k, φ) the reader returns n and φ
  (`ClauseBound.Alg.Decode.stDecM`); with 2ⁿ units nothing is cut off, so the count is the number of
  satisfying assignments (`CountKSatRate.stBruteC`); it is written in n + 1 bits.
* The length of the input (`length_enc_succ_le`), by the printed reason. The code of (k, φ) has k +
  n + 2 + m·k·(⌊log₂ 2n⌋ + 1) symbols. There are m ≤ (2n+1)^k clauses
  (`VariableBound.Paper.clauseCount`), and (2n+1)^k ≤ n^(2k) for n ≥ 3 (`clauseCountPowStmt`), while
  5^k ≤ 2^(3k) for n = 2. With k ≤ n^k and ⌊log₂ 2n⌋ + 1 ≤ n², the length plus one is at most
  n^(8k).
* The time (`steps_le`). |x| + 2ⁿ + 1 ≤ n^(8k) + 2ⁿ ≤ n^(8k)·2ⁿ, and q ≤ 2^q.
* The machine. `exhaust` and x ↦ n are polynomial-time, so the padding machine of this development
  (`CountKSatRate.stPaddedW`) computes `exhaust` in the sense of `Computes`. -/

public section

namespace PairsToBound

open Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg Wrap MainTheoremForms
open Sat3 (CNF)

/-! ### The value -/

/-- The word of ℓ bits of y, lowest bit first, lists the binary digits number 0, …, ℓ − 1 of y. -/
theorem toWord_eq_map (l y : ℕ) : toWord l y = (List.range l).map y.testBit := by
  induction l generalizing y with
  | zero => rfl
  | succ l ih =>
    rw [toWord, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp [Nat.testBit_zero]
    · refine List.map_congr_left fun i _ => ?_
      simp [Nat.testBit_succ]

/-- The last step writes the number v in n + 1 bits, as the statements of the theorems ask. -/
theorem outW_replicate (n : ℕ) (ψ : Fml) (v : ℕ) : outW ((List.replicate n (), ψ), v) = SatK.binary n v := by
  rw [outW, List.length_replicate, toWord_eq_map]
  rfl

/-- On the code of (k, φ), for k ≥ 1 and a k-CNF φ on n variables, with a padding string of 2ⁿ
units, exhaustive counting returns the number of satisfying assignments of φ in n + 1 bits. -/
theorem exhaust_enc {k n : ℕ} (φ : CNF n) (hk : 1 ≤ k) (hφ : SatK.IsKCNF k φ) : exhaust (SatM.enc k φ, pad n) = SatK.binary n (SatK.numSat φ) := by
  obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk hφ.1
  have hb := stBruteC k n φ hk hφ (pad n) (by rw [pad, List.length_replicate])
  rw [bruteN, nK, stDecU k n φ hk hφ.1] at hb
  simp only [List.length_replicate] at hb
  simp only [exhaust, UniformInK.bruteU, hdec, List.length_replicate]
  rw [hb, outW_replicate]

/-! ### The length of the input -/

/-- (2n+1)^k ≤ n^(3k) for n ≥ 2: for n ≥ 3 by the printed (2n+1)^k ≤ n^(2k), for n = 2 because 5 ≤
2³. -/
theorem clauseCountPow_of_two_le (k : ℕ) {n : ℕ} (hn : 2 ≤ n) : (2 * n + 1) ^ k ≤ n ^ (3 * k) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) k
  · exact (clauseCountPowStmt k n h).trans (Nat.pow_le_pow_right (by omega) (by omega))

/-- «… as there are fewer than (2n+1)^k ≤ n^(2k) clauses …, reading the input included»: the code of
(k, φ), for k ≥ 1 and a k-CNF φ on n ≥ 2 variables, has fewer than n^(8k) symbols. -/
theorem length_enc_succ_le {k n : ℕ} {φ : CNF n} (hk : 1 ≤ k) (hn : 2 ≤ n) (hφ : SatK.IsKCNF k φ) : (SatM.enc k φ).length + 1 ≤ n ^ (8 * k) := by
  rw [End.length_enc]
  obtain ⟨a, ha⟩ : ∃ a, a = n ^ k := ⟨_, rfl⟩
  have e2 : n ^ (2 * k) = a ^ 2 := by rw [ha, ← pow_mul, Nat.mul_comm]
  have e3 : n ^ (3 * k) = a ^ 3 := by rw [ha, ← pow_mul, Nat.mul_comm]
  have e8 : n ^ (8 * k) = a ^ 8 := by rw [ha, ← pow_mul, Nat.mul_comm]
  have hna : n ≤ a := by
    rw [ha]
    exact Nat.le_self_pow (by omega) n
  have hka : k ≤ a := by
    rw [ha]
    exact (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hn k)
  have hm : φ.length ≤ a ^ 3 := e3 ▸ (VariableBound.Paper.clauseCount k n φ hφ).trans (clauseCountPow_of_two_le k hn)
  have hL : Nat.log2 (2 * n) + 1 ≤ a ^ 2 := by
    have h1 : Nat.log2 (2 * n) < 2 * n := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_lt_self 2 (by omega)
    have h2 : 2 * n ≤ n * n := Nat.mul_le_mul_right n hn
    have h3 : n * n ≤ a * a := Nat.mul_le_mul hna hna
    rw [pow_two]
    omega
  have h6 : φ.length * (k * (Nat.log2 (2 * n) + 1)) ≤ a ^ 6 :=
    calc φ.length * (k * (Nat.log2 (2 * n) + 1)) ≤ a ^ 3 * (a * a ^ 2) := Nat.mul_le_mul hm (Nat.mul_le_mul hka hL)
      _ = a ^ 6 := by ring
  have h5 : 2 ^ 5 ≤ a ^ 5 := Nat.pow_le_pow_left (hn.trans hna) 5
  have h7 : k + n + 3 ≤ a ^ 6 :=
    calc k + n + 3 ≤ 2 ^ 5 * a := by omega
      _ ≤ a ^ 5 * a := Nat.mul_le_mul_right a h5
      _ = a ^ 6 := by ring
  have h8 : 2 * a ^ 6 ≤ a ^ 8 :=
    calc 2 * a ^ 6 ≤ a ^ 2 * a ^ 6 := Nat.mul_le_mul_right _ ((by norm_num : 2 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left (hn.trans hna) 2))
      _ = a ^ 8 := by ring
  rw [e8]
  omega

/-! ### The time -/

/-- If L + 1 ≤ n^(8k) and n ≥ 2, k ≥ 1, then q·(L + 2ⁿ + 1)^q ≤ 2^(8q·n)·n^(8q·k). -/
theorem steps_le (q : ℕ) {k n L : ℕ} (hk : 1 ≤ k) (hn : 2 ≤ n) (hL : L + 1 ≤ n ^ (8 * k)) : q * (L + 2 ^ n + 1) ^ q ≤ 2 ^ (8 * q * n) * n ^ (8 * q * k) := by
  have hA : 2 ≤ n ^ (8 * k) := hn.trans (Nat.le_self_pow (by omega) n)
  have hB : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  have h1 : L + 2 ^ n + 1 ≤ n ^ (8 * k) * 2 ^ n := le_trans (by omega) (Nat.add_le_mul hA hB)
  have h2 : q * 1 ≤ q * n := Nat.mul_le_mul_left q (by omega)
  calc q * (L + 2 ^ n + 1) ^ q ≤ 2 ^ q * (n ^ (8 * k) * 2 ^ n) ^ q := Nat.mul_le_mul (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left h1 q)
    _ = 2 ^ (q + n * q) * n ^ (8 * q * k) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, pow_add]
      ring
    _ ≤ 2 ^ (8 * q * n) * n ^ (8 * q * k) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by nlinarith))

/-- «… the algorithm tries all assignments; … this takes time 2^n·n^{O(k)}, reading the input
included.» Every machine that computes exhaustive counting with a padding string of 2ⁿ units, with
the constant q, tries all assignments within 2^{c·n}·n^{c·k} steps for c = 8q. -/
theorem triesAllWithin_of_computes {Mb : TM2ComputableAux Bool Bool} {qb : ℕ} (h : Computes Mb exhaust (fun x => (fmlOf x).1.length) qb) : TriesAllWithin Mb (8 * qb) := by
  intro k n φ hk hn hφ
  obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk hφ.1
  have h1 := h (SatM.enc k φ)
  simp only [hdec, List.length_replicate] at h1
  rw [exhaust_enc φ hk hφ] at h1
  exact Outputs.mono h1 (steps_le qb hk hn (length_enc_succ_le hk hn hφ))

/-- Every machine that computes exhaustive counting with a padding string of 2ⁿ units tries all
assignments within 2^{c·n}·n^{c·k} steps, for some c. -/
theorem everyExhaustiveMachineTriesAll : EveryExhaustiveMachineTriesAll :=
  fun _ qb h => ⟨8 * qb, triesAllWithin_of_computes h⟩

/-! ### The machine -/

/-- Exhaustive counting is polynomial-time in the input and the padding string. -/
theorem exhaust_polyT : PolyT exhaust := by
  have hd : PolyT fun p : List Bool × U => fmlOf p.1 := PolyT.comp Decode.stCertDecM.2 PolyT.id'.fst
  have hbr : PolyT UniformInK.bruteU := by
    have h := Cert.bruteN_polyT_aux hd (pad := fun p : List Bool × U => p.2) PolyT.id'.snd
    unfold UniformInK.bruteU
    exact h
  unfold exhaust
  exact PolyT.comp Poly.outW_polyT (PolyT.prodMk hd hbr)

/-- There is a machine with finite alphabets that computes exhaustive counting with a padding string
of 2ⁿ units on every bit string, and so tries all assignments within 2^{c·n}·n^{c·k} steps. -/
theorem exhaustiveMachineExists : ExhaustiveMachineExists := by
  obtain ⟨Mb, q, hfin, hM⟩ := stPaddedW (fun x => (fmlOf x).1.length) exhaust (PolyT.length Decode.stCertDecM.2.fst) exhaust_polyT
  exact ⟨Mb, 8 * q, q, hfin, triesAllWithin_of_computes hM, hM⟩

end PairsToBound
