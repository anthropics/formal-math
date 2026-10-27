/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecNetworks_Defs
public import StepMachines.Prog.NetVal
import Mathlib.Tactic

/-! # Section 3 «Networks»: lemmas on the (K, λ)-clique of Definition 3

Lemmas on the (K, λ)-clique of Definition 3, which is defined in `Eight/SecNetworks_Defs.lean`: the
places of the copies z_w(w') in a setting of node w, sums over the encoded settings of a node,
the strings at one node of a choice of one string per edge, the tables as functions of the encoded
settings, and bounds on the sizes of strings, nodes and the values 0 and 1. -/

public section

namespace Eight.SecNetworks

open Groundwork Groundwork.Prog Finset

/-! ### The copies held at a node -/

/-- z_w(w') is the block number `place w w'` of the λ-bit blocks of z_w. -/
theorem copyAt_eq_block (lam w w' : ℕ) (z : List Bool) : copyAt lam w w' z = block lam (place w w') z := rfl

/-- The places of the nodes other than w are below K − 1. -/
theorem place_lt {K : ℕ} (w w' : Fin K) (h : w' ≠ w) : place w w' < K - 1 := by
  have := Fin.val_ne_of_ne h
  unfold place
  split_ifs <;> omega

/-- Two nodes other than w have different places. -/
theorem place_inj {K : ℕ} (w a b : Fin K) (ha : a ≠ w) (hb : b ≠ w) (h : place w a = place w b) : a = b := by
  have := Fin.val_ne_of_ne ha
  have := Fin.val_ne_of_ne hb
  apply Fin.ext
  unfold place at h
  split_ifs at h <;> omega

/-- Every place below K − 1 is taken by a node other than w. -/
theorem place_surj {K : ℕ} (w : Fin K) (j : ℕ) (hj : j < K - 1) : ∃ a : Fin K, a ≠ w ∧ place w a = j := by
  by_cases h : j < w.1
  · exact ⟨⟨j, by omega⟩, fun e => by rw [← e] at h; exact lt_irrefl _ h, by simp [place, h]⟩
  · refine ⟨⟨j + 1, by omega⟩, fun e => ?_, ?_⟩
    · rw [← e] at h; simp at h
    · have : ¬ j + 1 < w.1 := by omega
      simp [place, this]

/-- In a setting of (K − 1)λ bits every copy has λ bits. -/
theorem length_copyAt {K lam : ℕ} (w w' : Fin K) (h : w' ≠ w) {z : List Bool} (hz : z.length = (K - 1) * lam) :
    (copyAt lam w w' z).length = lam := by
  refine length_block ?_
  rw [hz]
  exact Nat.mul_le_mul_right _ (place_lt w w' h)

/-- Definition 3, «A setting z_w is encoded by concatenating its K − 1 strings z_w(w')»: a sum over
all strings of (K − 1)λ bits of a function of the K − 1 copies is the sum over all (K − 1)-tuples of
strings of λ bits.
A tuple is a function on all K nodes with the empty string at w itself. -/
theorem sum_settings {K : ℕ} (lam : ℕ) (w : Fin K) (F : (Fin K → List Bool) → ℤ) :
    ∑ z ∈ words ((K - 1) * lam), F (fun w' => if w' = w then [] else copyAt lam w w' z)
      = ∑ t ∈ tuples (fun w' => w' ≠ w) (fun _ => words lam) [], F t := by
  rw [← sum_blocks (fun w' : Fin K => w' ≠ w) (fun w' => place w w') (K - 1) lam (fun a b => place_inj w a b)
    (fun a => place_lt w a) (fun j => place_surj w j) [] F]
  refine sum_congr rfl fun z _ => congrArg F (funext fun w' => ?_)
  by_cases h : w' = w <;> simp [h, copyAt_eq_block]

/-! ### A choice of one string per edge -/

/-- The strings of a choice of one string per edge on the edges at v form a (K − 1)-tuple of strings
of λ bits. -/
theorem star_mem {K lam : ℕ} {Λ : Fin K × Fin K → List Bool}
    (hΛ : Λ ∈ tuples (fun p : Fin K × Fin K => p.1 < p.2) (fun _ => words lam) []) (v : Fin K) :
    star Λ v ∈ tuples (fun w' => w' ≠ v) (fun _ => words lam) [] := by
  rw [mem_tuples] at hΛ ⊢
  refine fun w => ⟨fun hw => (hΛ _).1 (min_lt_max.2 hw.symm), fun hw => (hΛ _).2 ?_⟩
  have : w = v := not_not.1 hw
  simp [pr, this]

/-! ### The tables as functions of the encoded settings, and sizes -/

section Procedures

open Stepped

variable {C : Type}

/-- The tables as functions of the encoded settings: W_w(z_w) is the entry at the K − 1 copies cut
out of z_w. -/
@[expose] def tablesOn {K : ℕ} (lam : ℕ) (W : Paper.Tables K) (w : Fin K) (z : List Bool) : ℤ :=
  W w fun w' => if w' = w then [] else copyAt lam w w' z

/-- The size of a string of n bits is 2n + 1. -/
theorem size_word (l : List Bool) : size l = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [size_list, List.map_cons, List.sum_cons, size_bool, List.length_cons] at ih ⊢
    omega

/-- A node of [K] is not larger than K. -/
theorem size_fin {K : ℕ} (a : Fin K) : size a.val ≤ size K := by
  simp only [size_nat]
  exact Nat.succ_le_succ (Nat.size_le_size a.2.le)

/-- The numbers 0 and 1 have size at most 2. -/
theorem size_ite_le (p : Prop) [Decidable p] : size (if p then (1 : ℤ) else 0) ≤ 2 := by
  split_ifs <;> simp

end Procedures

end Eight.SecNetworks
