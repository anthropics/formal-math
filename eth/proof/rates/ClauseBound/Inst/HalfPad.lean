/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfVal
public import ClauseBound.Inst.HalfEnc
public import ClauseBound.Inst.HalfTabKF
public import ClauseBound.Inst.HalfTabBot

/-! # The list of all partitions of 0, …, 4h, and the pad for the tables

The functions that read the tables of the operators take, besides their input, a pad. The flattened
table of the partitions of 0, …, W has Σ_{E ≤ W} p(E) members, which for W = 4h is the number
`deltaF h`. For a partition μ of h, the two lengths of the pad that suffice for the tables, `padOp`
(the table of the operators (t^μ)[·]) and `padKF` (the tables of the parts of a^μ), are at most
`padLen h`. So the two functions that read the tables give the entries of the matrices as soon as
the
pad has length at least `padLen h` (`stTopF`, `stBotF`), by the correctness of the tables for a
general list of monomials. -/

public section

namespace ClauseBound.Inst.Half

open Groundwork PaddedDescent.F ClauseBound.Part Partitions

namespace Pad

/-- The flattened table has Σ_{E ≤ W} p(E) members. -/
theorem length_flatten_allTab (W : ℕ) : (allTab W).flatten.length = ∑ E ∈ Finset.range (W + 1), p E := by
  have h : allTab W = tabK W W := foldl_roundT W W
  rw [h, tabK, List.length_flatten, List.map_map, sum_map_range]
  refine Finset.sum_congr rfl fun E hE => ?_
  have hE' : E ≤ W := Nat.lt_succ_iff.1 (Finset.mem_range.1 hE)
  rw [Function.comp_apply, partsLe_of_le hE', length_partsOf]

/-- deltaF h = Σ_{E ≤ 4h} p(E). -/
theorem deltaF_eq (h : ℕ) : deltaF h = ∑ E ∈ Finset.range (4 * h + 1), p E := by
  rw [deltaF, pTab_eq, sum_map_range]

/-- The flattened table of the partitions of 0, …, 4h has deltaF h members. -/
theorem length_flatten_allTab_four (h : ℕ) : (allTab (4 * h)).flatten.length = deltaF h := by
  rw [length_flatten_allTab, deltaF_eq]

/-- The pad for the table of a[·] is shorter than the pad for the tables of the parts of a^μ. -/
theorem padOp_le_padKF (W Δ h s L : ℕ) : padOp W Δ L ≤ padKF W Δ h s L := by
  unfold padOp padKF
  have h1 : Δ ^ 2 * (3 * ((4 * W + 1) * L) + 10) ≤ Δ ^ 2 * (3 * (s + (4 * W + 1) * L) + 10) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : Δ ^ 2 * (3 * (s + (4 * W + 1) * L) + 10) + 4 ≤ (h + 1) * (Δ ^ 2 * (3 * (s + (4 * W + 1) * L) + 10) + 4) :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The pad for the tables of the parts of a^μ, for W = 4h, the sum h and at most h parts. -/
theorem padKF_le (h Δ L : ℕ) (hL : L ≤ h) : padKF (4 * h) Δ h h L ≤ 2 ^ 10 * (h + 2) ^ 4 * (Δ + 1) ^ 2 := by
  unfold padKF
  have h1 : 3 * (h + (4 * (4 * h) + 1) * L) + 10 ≤ 48 * (h + 2) ^ 2 := by
    have : (4 * (4 * h) + 1) * L ≤ (4 * (4 * h) + 1) * h := Nat.mul_le_mul_left _ hL
    nlinarith
  have h2 : Δ ^ 2 ≤ (Δ + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : 1 ≤ (Δ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨A, hA⟩ : ∃ A, A = h + 2 := ⟨_, rfl⟩
  have hA2 : 2 ≤ A := by omega
  have hh : h + 1 ≤ A := by omega
  rw [← hA] at h1 ⊢
  generalize (Δ + 1) ^ 2 = D at *
  generalize Δ ^ 2 = X at *
  generalize 3 * (h + (4 * (4 * h) + 1) * L) + 10 = Y at *
  have hAA : A ≤ A ^ 3 := Nat.le_self_pow (by norm_num) A
  have hZ : A ≤ A ^ 3 * D := le_trans hAA (Nat.le_mul_of_pos_right _ h3)
  calc (h + 1) * (X * Y + 4) + 2 ≤ A * (D * (48 * A ^ 2) + 4) + 2 := by gcongr
    _ = 48 * (A ^ 3 * D) + 4 * A + 2 := by ring
    _ ≤ 48 * (A ^ 3 * D) + 4 * (A ^ 3 * D) + A ^ 3 * D := by omega
    _ = 53 * (1 * (A ^ 3 * D)) := by ring
    _ ≤ 2 ^ 10 * (A * (A ^ 3 * D)) := by gcongr <;> omega
    _ = 2 ^ 10 * A ^ 4 * D := by ring

/-- A partition μ of h in the list: at most h parts, each at most 4h. -/
theorem parts_of_mem {h : ℕ} {μ : List ℕ} (hμ : μ ∈ (allTab (4 * h)).flatten) (hs : μ.sum = h) :
    μ.length ≤ h ∧ ∀ n ∈ μ, n ≤ 4 * h := by
  obtain ⟨_, h2, _⟩ := mem_flatten_allTab.1 hμ
  refine ⟨hs ▸ List.length_le_sum_of_one_le μ h2, fun n hn => ?_⟩
  have := List.le_sum_of_mem hn
  omega

/-- The pad of length padLen h suffices for the tables of the parts of a^μ, μ a partition of h. -/
theorem padKF_le_padLen {h : ℕ} {μ : List ℕ} (hμ : μ ∈ (allTab (4 * h)).flatten) (hs : μ.sum = h) :
    padKF (4 * h) (allTab (4 * h)).flatten.length h μ.sum μ.length ≤ padLen h := by
  rw [length_flatten_allTab_four, hs, padLen]
  exact padKF_le h (deltaF h) μ.length (parts_of_mem hμ hs).1

/-- The pad of length padLen h suffices for the table of the operators (t^μ)[·], μ a partition of h. -/
theorem padOp_le_padLen {h : ℕ} {μ : List ℕ} (hμ : μ ∈ (allTab (4 * h)).flatten) (hs : μ.sum = h) :
    padOp (4 * h) (allTab (4 * h)).flatten.length μ.length ≤ padLen h :=
  le_trans (padOp_le_padKF _ _ h μ.sum _) (padKF_le_padLen hμ hs)

end Pad

open Pad

/-- With a pad of length padLen h, `topF` on the list of all partitions of 0, …, 4h gives the
entries of the matrix. -/
theorem stTopF : StTopF := fun _pad h hh hp _μ hμ hs i _ r _π hπ _σ hσ =>
  topF_eq (by omega) (flatOK_allTab _) (parts_of_mem hμ hs).2 hs (le_trans (padKF_le_padLen hμ hs) hp) i r hπ hσ

/-- With a pad of length padLen h, `botF` on the list of all partitions of 0, …, 4h gives the
entries of the matrix. -/
theorem stBotF : StBotF := fun _pad h hh hp _μ hμ hs r _π hπ _σ hσ =>
  botF_eq (by omega) (flatOK_allTab _) (parts_of_mem hμ hs).2 (le_trans (padOp_le_padLen hμ hs) hp) h r hπ hσ

end ClauseBound.Inst.Half
