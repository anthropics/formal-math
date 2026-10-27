/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.ArithStack
public import PaddedDescent.F.ArithCol

/-! # The schedule (`StSched`, the chain condition, and the second part of `StA`)

`schedF pad t` computes the list of levels (K_j, g_j), j < t, in unary, together with K_t and L_t,
under the cut-off by the pad. Here: if the pad has
length at least `schedLen t`, no cut-off is active and the result is the mathematical schedule
`schedL t` with K_t and L_t (`stSched`); the schedule is
a chain of steps g·g → K that ends at 256 nodes (`chain_schedL`); and for t = `depthOf (sOf n)`,
`sOf n` ≥ 1, the length `schedLen t` is below the pad
(`schedLen_le`). -/

public section

namespace PaddedDescent.F

open Groundwork PaddedDescent.F.Lists

namespace Arith

/-- L_{j+1} = L_j + L_j. -/
theorem Lseq_succ (j : ℕ) : Lseq (j + 1) = Lseq j + Lseq j := by
  rw [Lseq, Lseq, ← add_assoc, pow_succ]; ring

/-- L_j grows with j. -/
theorem Lseq_mono {i j : ℕ} (h : i ≤ j) : Lseq i ≤ Lseq j :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The state of `schedF` after j rounds when no cut-off is active. -/
def schedState (j : ℕ) : List Lvl × U × U := (schedL j, List.replicate (Kseq j) (), List.replicate (Lseq j) ())

/-- One round of `schedF` without its cut-off takes the state after j rounds to the state after j +
1 rounds. -/
theorem schedState_succ (j : ℕ) :
    (((schedState j).2.1, mulU (schedState j).2.1 (schedState j).2.2) :: (schedState j).1,
      sqU (mulU (schedState j).2.1 (schedState j).2.2), (schedState j).2.2 ++ (schedState j).2.2) = schedState (j + 1) := by
  simp only [schedState, mulU, sqU, schedL, List.length_replicate, List.replicate_append_replicate, Lseq_succ, Kseq_succ_eq_mul, gseq]

/-- The word of the schedule of depth j has length at most j·(8·K_j + 8) + 2. -/
theorem len_schedL_le (j : ℕ) : len (schedL j) ≤ j * (8 * Kseq j + 8) + 2 := by
  induction j with
  | zero => simp [schedL, len_nil]
  | succ j ih =>
    have h1 : Kseq j ≤ gseq j := Kseq_le_gseq j
    have h2 : gseq j ≤ Kseq (j + 1) := by
      rw [Kseq_succ_eq_mul]
      exact Nat.le_mul_self _
    have h3 : j * (8 * Kseq j + 8) ≤ j * (8 * Kseq (j + 1) + 8) := Nat.mul_le_mul_left _ (by omega)
    rw [schedL, len_cons, len_pair, len_units, len_units, List.length_replicate, List.length_replicate]
    nlinarith

/-- The word of the state after j rounds has length at most `schedLen j`. -/
theorem len_schedState_le (j : ℕ) : len (schedState j) ≤ schedLen j := by
  have := len_schedL_le j
  rw [schedState, len_pair, len_pair, len_units, len_units, List.length_replicate, List.length_replicate, schedLen]
  nlinarith

/-- `schedLen` grows with the depth. -/
theorem schedLen_mono {i j : ℕ} (h : i ≤ j) : schedLen i ≤ schedLen j := by
  have h1 := Kseq_strictMono.monotone h
  have h2 := Lseq_mono h
  unfold schedLen
  gcongr

/-- The schedule is a chain of steps g·g → K that ends at 256 nodes. -/
theorem chain_schedL : ∀ t, Chain (Kseq t) (schedL t)
  | 0 => Kseq_zero
  | j + 1 => by
    have h := chain_schedL j
    have h2 := Kseq_ge j
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.length_replicate]; exact Kseq_succ_eq_mul j
    · simp only [List.length_replicate]; omega
    · simp only [List.length_replicate]; exact colOK_seq j
    · simpa only [List.length_replicate] using h

end Arith

open Arith

/-- `StSched`: with a pad of length at least `schedLen t`, `schedF pad t` is the schedule of depth t
together with K_t and L_t in unary. -/
theorem stSched : StSched := by
  intro pad t ht
  have key : ∀ j ≤ t, (List.replicate j ()).foldl
      (fun st _ => cap pad ([], [], []) ((st.2.1, mulU st.2.1 st.2.2) :: st.1, sqU (mulU st.2.1 st.2.2), st.2.2 ++ st.2.2))
      (cap pad ([], [], []) ([], List.replicate 256 (), List.replicate (Lseq 0) ())) = schedState j := by
    intro j
    induction j with
    | zero =>
      intro _
      have e : (([], List.replicate 256 (), List.replicate (Lseq 0) ()) : List Lvl × U × U) = schedState 0 := by
        rw [schedState, schedL, Kseq_zero]
      rw [List.replicate_zero, List.foldl_nil, e]
      exact cap_eq ((len_schedState_le 0).trans ((schedLen_mono (Nat.zero_le t)).trans ht))
    | succ j ih =>
      intro hj
      rw [List.replicate_succ' (n := j), List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil, schedState_succ]
      exact cap_eq ((len_schedState_le (j + 1)).trans ((schedLen_mono hj).trans ht))
  exact key t le_rfl

namespace Arith

/-- The second part of `StA`: the computation of the schedule fits under the pad. -/
theorem schedLen_le {n C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) :
    schedLen (depthOf (sOf n)) ≤ F := by
  refine le_pad_of_le hs hC hF ?_
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Ytop (sOf n) := ⟨_, rfl⟩
  have h1 : depthOf (sOf n) + 1 ≤ Y := by
    have := lin_lt_Ytop (sOf n)
    unfold depthOf
    omega
  have h2 : Kseq (depthOf (sOf n)) ≤ Y := hY ▸ Ktop_le_Ytop (sOf n)
  have h2' : Lseq (depthOf (sOf n)) ≤ Y := by
    obtain ⟨u, hu, hu'⟩ : ∃ u, depthOf (sOf n) = u + 1 ∧ 46 ≤ u := ⟨19 * sOf n / 3 + 699, rfl, by omega⟩
    have e0 : 47 + depthOf (sOf n) ≤ 2 ^ depthOf (sOf n) := by
      have : u + 1 ≤ 2 ^ u := Nat.lt_two_pow_self
      rw [hu, pow_succ]
      omega
    exact hY ▸ (two_pow_le_Ktop e0).trans (Ktop_le_Ytop (sOf n))
  have h3 : Y ^ 2 ≤ n := hY ▸ Ytop_sOf_pow_le (p := 2) (by norm_num) hs
  have h4 : 1 ≤ Y := by omega
  have h5 : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have h6 : schedLen (depthOf (sOf n)) ≤ 28 * n := by
    unfold schedLen
    calc (depthOf (sOf n) + 1) * (8 * Kseq (depthOf (sOf n)) + 8) + 4 * Lseq (depthOf (sOf n)) + 8 ≤ Y * (8 * Y + 8) + 4 * Y + 8 := by gcongr
      _ ≤ 28 * Y ^ 2 := by nlinarith
      _ ≤ 28 * n := by omega
  have h7 : 2 ^ (9 * Nat.size n + 30) = 2 ^ 30 * (2 ^ Nat.size n) ^ 9 := by rw [← pow_mul, ← pow_add]; congr 1; ring
  have h8 : 2 ^ Nat.size n ≤ (2 ^ Nat.size n) ^ 9 := Nat.le_self_pow (by norm_num) _
  rw [h7]
  norm_num
  omega

end Arith

end PaddedDescent.F
