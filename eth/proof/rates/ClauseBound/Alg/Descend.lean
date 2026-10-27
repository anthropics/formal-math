/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Interfaces
public import PaddedDescent.F.Descend
public import PaddedDescent.F.Table

/-! # Lemmas for the descent through all levels

`descendG P pad sched I` starts from the state «sum 0, factor 1, work list [I]» and applies the
steps of the schedule. A step multiplies the sum and the factor by the factor d^R of its
level, adds the terms that are evaluated at once, and replaces every instance of the work list by
its children. `solveG` evaluates the instances that are left by brute force, adds
the sum, and divides by the factor. This file holds lemmas for the bookkeeping of these steps: two
facts on sums over lists, a bound on the length of the word of a state
(whose first budget in `FitsG` says that the current state fits under the pad), and bounds on the
sizes of the sum and of the factor after a step.
-/

public section

namespace ClauseBound.Alg.Descend

open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists

/-! ### Lists -/

/-- A sum of k integers of absolute value at most c has absolute value at most k·c. -/
theorem natAbs_sum_map_le {α : Type} (w : List α) (f : α → ℤ) (c : ℕ) (h : ∀ a ∈ w, (f a).natAbs ≤ c) :
    (w.map f).sum.natAbs ≤ w.length * c := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have h1 := h a (by simp)
    have h2 := ih fun b hb => h b (by simp [hb])
    have h3 := Int.natAbs_add_le (f a) (w.map f).sum
    rw [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- If D·Z(a) is the first component of e(a) plus the sum of z over the second, for every member a
of w, then D times the sum of Z over w is the sum of all first components
plus the sum of z over all second components. -/
theorem sum_fst_add_sum_snd {α β : Type} (w : List α) (e : α → ℤ × List β) (Z : α → ℤ) (z : β → ℤ) (D : ℤ)
    (h : ∀ a ∈ w, D * Z a = (e a).1 + ((e a).2.map z).sum) :
    ((w.map e).map Prod.fst).sum + (((w.map e).flatMap Prod.snd).map z).sum = D * (w.map Z).sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have h1 := h a (by simp)
    have h2 := ih fun b hb => h b (by simp [hb])
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append, mul_add]
    rw [h1, ← h2]
    ring

/-! ### The length of the word of a state -/

/-- The first budget of `FitsG`: the current state fits under the pad. -/
theorem fitsG_head {P : PiecesF} {F : ℕ} : ∀ {sched : List Step} {Kup lam B cnt z : ℕ}, FitsG P F Kup lam B cnt z sched →
    cnt * instLen Kup lam B + 8 * z + 4 * lam + 40 ≤ F
  | [], _, _, _, _, _, h => h.1
  | _ :: _, _, _, _, _, _, h => h.1

/-- The word of a state with at most cnt well-formed instances, and a sum and a factor below 2^z. -/
theorem len_state_le (st : DState) {K lam B cnt z : ℕ} (hl : st.2.1.length = lam) (hc : st.2.2.length ≤ cnt)
    (hw : ∀ I ∈ st.2.2, WFe K lam B I) (hs : st.1.1.natAbs < 2 ^ z) (hf : st.1.2 < 2 ^ z) :
    len st ≤ cnt * instLen K lam B + 8 * z + 4 * lam + 40 := by
  obtain ⟨⟨a, f⟩, u, w⟩ := st
  simp only at hl hc hw hs hf
  rw [len_pair, len_pair, len_pair, len_int, len_nat, len_units]
  have h1 := len_list_le' w (instLen K lam B) hc fun J hJ => Table.stT3b _ _ _ J (hw J hJ).1
  have h2 : Nat.size a.natAbs ≤ z := Nat.size_le.2 hs
  have h3 : Nat.size f ≤ z := Nat.size_le.2 hf
  omega

/-! ### The sizes of the sum and of the factor after a step -/

/-- d^R ≤ 2^(R · number of binary digits of d). -/
theorem pow_le_two_pow_size (d R : ℕ) : d ^ R ≤ 2 ^ (R * Nat.size d) := by
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_size_self d).le R

/-- 2^(number of binary digits of n) ≤ 2n for n ≥ 1. -/
theorem two_pow_size_le {n : ℕ} (h : 1 ≤ n) : 2 ^ Nat.size n ≤ 2 * n := by
  have h0 : 0 < Nat.size n := Nat.size_pos.2 h
  have h1 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.1 (by omega)
  calc 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by rw [← pow_succ']; congr 1; omega
    _ ≤ 2 * n := Nat.mul_le_mul_left _ h1

/-- The factor after a step. -/
theorem factor_lt {f D z r x : ℕ} (hf : f < 2 ^ z) (hD : D ≤ 2 ^ r) : f * D < 2 ^ (z + r + x) := by
  calc f * D ≤ f * 2 ^ r := Nat.mul_le_mul_left _ hD
    _ < 2 ^ z * 2 ^ r := Nat.mul_lt_mul_of_pos_right hf (by positivity)
    _ = 2 ^ (z + r) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (z + r + x) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)

/-- The sum after a step: the old sum a times D, plus b, the sum of at most cnt terms below
2^(digits of n + E). -/
theorem sum_lt {a b : ℤ} {D z r cnt n E : ℕ} (ha : a.natAbs < 2 ^ z) (hD : D ≤ 2 ^ r) (hn : 1 ≤ n)
    (hb : b.natAbs ≤ cnt * 2 ^ (Nat.size n + E)) : (a * (D : ℕ) + b).natAbs < 2 ^ (z + r + Nat.size (cnt * n) + E + 2) := by
  have h1 : (a * (D : ℕ)).natAbs < 2 ^ (z + r + (Nat.size (cnt * n) + E + 1)) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact factor_lt ha hD
  have h2 : b.natAbs < 2 ^ (z + r + (Nat.size (cnt * n) + E + 1)) := by
    calc b.natAbs ≤ cnt * (2 ^ Nat.size n * 2 ^ E) := by rw [← pow_add]; exact hb
      _ ≤ cnt * (2 * n * 2 ^ E) := by gcongr; exact two_pow_size_le hn
      _ = cnt * n * (2 * 2 ^ E) := by ring
      _ < 2 ^ Nat.size (cnt * n) * (2 * 2 ^ E) := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity)
      _ = 2 ^ (Nat.size (cnt * n) + E + 1) := by ring
      _ ≤ 2 ^ (z + r + (Nat.size (cnt * n) + E + 1)) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  have h3 := Int.natAbs_add_le (a * (D : ℕ)) b
  have h4 : 2 ^ (z + r + Nat.size (cnt * n) + E + 2) = 2 * 2 ^ (z + r + (Nat.size (cnt * n) + E + 1)) := by
    rw [← pow_succ']; congr 1; omega
  omega

end ClauseBound.Alg.Descend
