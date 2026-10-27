/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.MarkSums
public import PaddedDescent.F.Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! # The choice of the layers

The clauses of a formula ψ are divided into R + 1 layers, one clause at a time, so that the layers
are good (`Good`): an assignment that satisfies all later layers violates
at most w clauses of a layer. A clause C is offered to the layers in turn. Layer Λ, with the later
layers `rest`, takes C («drops» it) if the sum `BB`, over the assignments that
satisfy `rest` and violate C, of 2^(number of violated clauses of Λ) is small enough (`dropC`);
otherwise C is passed on, and the last layer takes whatever reaches it.

* `Inv` is the inequality that this rule keeps (`Inv.placeM`), in natural numbers: X·2^(κ+d+2) +
  3^κ·2^w ≤ 2^(w+κ+d+1), where X = `XX` is the sum of
  2^(number of violated clauses of Λ) over the assignments that satisfy `rest`, κ is the number of
  clauses in `rest` and d the number in Λ. It holds at the start if n + 2 ≤ w.
* It gives goodness (`InvS.nvio_lt`, `Inv.good`) and 3κ ≤ 2(κ+d) + 5 (`InvS.size`), so the last of R +
  1 layers has at most (2/3)^R·|ψ| + 5 clauses (`Inv.last_le`).
* The sum `BB` is the difference of two evaluations `trunc`, with and without C in the layer
  (`trunc_sub_trunc`).
* `layersE` (`proof/rates/PaddedDescent/F/MarkMath.lean`) is the same procedure with any function
  `ev` in place of `trunc`. If `ev` agrees with `trunc` on the lists of layers
  described by `Asked`, then the procedure builds the same layers (`layersE_eq_layersM`), and `ev`
  of these layers, with an empty layer in front, is the number of
  assignments that satisfy ψ (`ev_layersE`). This is `StLayersE`, one of the interface statements of
  `proof/rates/PaddedDescent/F/Interfaces.lean`. -/

@[expose] public section

namespace PaddedDescent.F.Mark

open Finset Groundwork.Prog

/-! ### Small facts on lists and powers -/

namespace Layers

/-- One more clause in a layer: one more violated clause if σ violates it. -/
theorem nvio_cons (σ : ℕ → Bool) (C : Cl) (L : Fml) : nvio σ (C :: L) = nvio σ L + if vio σ C = true then 1 else 0 := by
  simp [nvio, List.countP_cons]

/-- The arithmetic of a drop: X grows by B and d by 1. -/
theorem drop_step (X B κ d w : ℕ) (h : X * 2 ^ (κ + d + 2) + 3 ^ κ * 2 ^ w ≤ 2 ^ (w + κ + d + 1))
    (hB : B * 2 ^ (κ + d + 3) ≤ 3 ^ κ * 2 ^ w) :
    (X + B) * 2 ^ (κ + (d + 1) + 2) + 3 ^ κ * 2 ^ w ≤ 2 ^ (w + κ + (d + 1) + 1) := by
  have e1 : 2 ^ (κ + (d + 1) + 2) = 2 * 2 ^ (κ + d + 2) := by ring
  have e2 : 2 ^ (w + κ + (d + 1) + 1) = 2 * 2 ^ (w + κ + d + 1) := by ring
  have e3 : 2 ^ (κ + d + 3) = 2 * 2 ^ (κ + d + 2) := by ring
  rw [e1, e2]; rw [e3] at hB
  nlinarith

/-- The arithmetic of passing on: X falls by B and κ grows by 1. -/
theorem keep_step (Y B κ d w : ℕ) (h : (Y + B) * 2 ^ (κ + d + 2) + 3 ^ κ * 2 ^ w ≤ 2 ^ (w + κ + d + 1))
    (hB : 3 ^ κ * 2 ^ w < B * 2 ^ (κ + d + 3)) :
    Y * 2 ^ (κ + 1 + d + 2) + 3 ^ (κ + 1) * 2 ^ w ≤ 2 ^ (w + (κ + 1) + d + 1) := by
  have e1 : 2 ^ (κ + 1 + d + 2) = 2 * 2 ^ (κ + d + 2) := by ring
  have e2 : 2 ^ (w + (κ + 1) + d + 1) = 2 * 2 ^ (w + κ + d + 1) := by ring
  have e3 : 2 ^ (κ + d + 3) = 2 * 2 ^ (κ + d + 2) := by ring
  have e4 : 3 ^ (κ + 1) = 3 * 3 ^ κ := by ring
  rw [e1, e2, e4]; rw [e3] at hB
  nlinarith

/-- 3^κ ≤ 2^N gives 3κ ≤ 2N + 3, because 8 ≤ 9. -/
theorem size_step (κ N : ℕ) (h : 3 ^ κ ≤ 2 ^ N) : 3 * κ ≤ 2 * N + 3 := by
  have h1 : (2:ℕ) ^ (3 * (κ / 2)) ≤ 3 ^ (2 * (κ / 2)) := by
    rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left (by norm_num) _
  have h2 : (3:ℕ) ^ (2 * (κ / 2)) ≤ 3 ^ κ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2:ℕ) ^ (3 * (κ / 2)) ≤ 2 ^ N := h1.trans (h2.trans h)
  have h4 : 3 * (κ / 2) ≤ N := (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  omega

/-- The layers from number i on begin with layer number i. -/
theorem drop_eq_cons {Ls : List Fml} {i : ℕ} (hi : i < Ls.length) : Ls.drop i = Ls.getD i [] :: Ls.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- The layers from number i on have the same last layer. -/
theorem getLastD_drop {Ls : List Fml} {i : ℕ} (hi : i < Ls.length) : (Ls.drop i).getLastD [] = Ls.getLastD [] := by
  have h1 : Ls.drop i ≠ [] := by simpa using hi
  have h2 : Ls ≠ [] := by rintro rfl; simp at hi
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h1, List.getLast?_eq_some_getLast h2, List.getLast_drop]

/-- The clauses of the layers from number i on are among the clauses of all layers. -/
theorem flatten_drop_sublist (Ls : List Fml) (i : ℕ) : (Ls.drop i).flatten.Sublist Ls.flatten :=
  (List.drop_sublist i Ls).flatten

end Layers

open Layers

/-! ### The rule and its invariant -/

/-- σ satisfies all layers. -/
def satL (σ : ℕ → Bool) (Ls : List Fml) : Prop := ∀ L ∈ Ls, nvio σ L = 0

/-- Whether σ satisfies all layers can be decided. -/
instance decSatL (σ : ℕ → Bool) (Ls : List Fml) : Decidable (satL σ Ls) := by unfold satL; infer_instance

/-- Σ over the assignments that satisfy rest of 2^(violated clauses of Λ). -/
def XX (n : ℕ) (Λ : Fml) (rest : List Fml) : ℕ :=
  ∑ σ : Fin n → Bool, if satL (ext σ) rest then 2 ^ nvio (ext σ) Λ else 0

/-- Σ over the assignments that satisfy rest and violate C of 2^(violated clauses of Λ). -/
def BB (n : ℕ) (C : Cl) (Λ : Fml) (rest : List Fml) : ℕ :=
  ∑ σ : Fin n → Bool, if satL (ext σ) rest ∧ vio (ext σ) C = true then 2 ^ nvio (ext σ) Λ else 0

/-- The inequality kept for a layer Λ and the layers after it: κ clauses after it, d in it. -/
def InvS (n w : ℕ) (Λ : Fml) (rest : List Fml) : Prop :=
  XX n Λ rest * 2 ^ (rest.flatten.length + Λ.length + 2) + 3 ^ rest.flatten.length * 2 ^ w ≤ 2 ^ (w + rest.flatten.length + Λ.length + 1)

/-- The inequality for every layer but the last. -/
def Inv (n w : ℕ) : List Fml → Prop
  | [] => True
  | [_] => True
  | Λ :: L :: rest => InvS n w Λ (L :: rest) ∧ Inv n w (L :: rest)

/-- Is C dropped into Λ? -/
def dropC (n w : ℕ) (C : Cl) (Λ : Fml) (rest : List Fml) : Prop :=
  BB n C Λ rest * 2 ^ (rest.flatten.length + Λ.length + 3) ≤ 3 ^ rest.flatten.length * 2 ^ w

/-- The test can be decided. -/
instance decDropC (n w : ℕ) (C : Cl) (Λ : Fml) (rest : List Fml) : Decidable (dropC n w C Λ rest) := by unfold dropC; infer_instance

/-- C goes into the first layer that drops it, else into the last. -/
def placeM (n w : ℕ) (C : Cl) : List Fml → List Fml
  | [] => []
  | [Λ] => [C :: Λ]
  | Λ :: L :: rest => if dropC n w C Λ (L :: rest) then (C :: Λ) :: L :: rest else Λ :: placeM n w C (L :: rest)

/-- The placement does not remove layers. -/
theorem placeM_ne_nil {n w : ℕ} {C : Cl} : ∀ {Ls : List Fml}, Ls ≠ [] → placeM n w C Ls ≠ []
  | [_], _ => by simp [placeM]
  | Λ :: L :: rest, _ => by
    rw [placeM]; split_ifs <;> simp

/-- σ satisfies L :: Ls exactly if it violates no clause of L and satisfies Ls. -/
theorem satL_cons {σ : ℕ → Bool} {L : Fml} {Ls : List Fml} : satL σ (L :: Ls) ↔ nvio σ L = 0 ∧ satL σ Ls := by
  simp [satL]

/-- After the placement of C the layers are satisfied exactly if they were before and C is not
violated. -/
theorem satL_placeM {n w : ℕ} {C : Cl} (σ : ℕ → Bool) : ∀ {Ls : List Fml}, Ls ≠ [] →
    (satL σ (placeM n w C Ls) ↔ satL σ Ls ∧ vio σ C = false)
  | [Λ], _ => by
    simp only [placeM, satL_cons, nvio_cons]
    cases vio σ C <;> simp [satL]
  | Λ :: L :: rest, _ => by
    rw [placeM]
    split_ifs
    · simp only [satL_cons, nvio_cons]
      cases vio σ C <;> simp
    · rw [satL_cons, satL_placeM σ (by simp), satL_cons (L := Λ)]
      tauto

/-- The placement adds one clause. -/
theorem length_flatten_placeM {n w : ℕ} {C : Cl} : ∀ {Ls : List Fml}, Ls ≠ [] →
    (placeM n w C Ls).flatten.length = Ls.flatten.length + 1
  | [Λ], _ => by simp [placeM]
  | Λ :: L :: rest, _ => by
    rw [placeM]
    split_ifs
    · simp only [List.flatten_cons, List.length_append, List.length_cons]; omega
    · rw [List.flatten_cons, List.length_append, length_flatten_placeM (by simp), List.flatten_cons (l := Λ), List.length_append]
      omega

/-- The placement keeps the number of layers. -/
theorem length_placeM {n w : ℕ} {C : Cl} : ∀ (Ls : List Fml), (placeM n w C Ls).length = Ls.length
  | [] => rfl
  | [_] => rfl
  | Λ :: L :: rest => by
    rw [placeM]
    split_ifs
    · rfl
    · simp only [List.length_cons, length_placeM (L :: rest)]

/-- Dropping C into Λ adds B. -/
theorem XX_cons (n : ℕ) (C : Cl) (Λ : Fml) (rest : List Fml) : XX n (C :: Λ) rest = XX n Λ rest + BB n C Λ rest := by
  unfold XX BB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [nvio_cons]
  by_cases h : satL (ext σ) rest <;> cases hv : vio (ext σ) C <;> simp [h, pow_succ, mul_two]

/-- Keeping C, that is passing it on to the later layers, subtracts B. -/
theorem XX_keep (n : ℕ) (C : Cl) (Λ : Fml) {rest rest' : List Fml}
    (h : ∀ σ : Fin n → Bool, satL (ext σ) rest' ↔ satL (ext σ) rest ∧ vio (ext σ) C = false) :
    XX n Λ rest' + BB n C Λ rest = XX n Λ rest := by
  unfold XX BB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h1 : satL (ext σ) rest <;> cases hv : vio (ext σ) C <;> simp [h σ, h1, hv]

/-- Placing a clause keeps the invariant. -/
theorem Inv.placeM {n w : ℕ} (C : Cl) : ∀ {Ls : List Fml}, Inv n w Ls → Inv n w (placeM n w C Ls)
  | [], _ => trivial
  | [_], _ => trivial
  | Λ :: L :: rest, h => by
    rw [Mark.placeM]
    split_ifs with hd
    · refine ⟨?_, h.2⟩
      have := drop_step _ _ _ _ _ h.1 hd
      unfold InvS
      rw [XX_cons, List.length_cons]
      exact this
    · obtain ⟨L', rest', e⟩ : ∃ L' rest', Mark.placeM n w C (L :: rest) = L' :: rest' :=
        List.exists_cons_of_ne_nil (placeM_ne_nil (by simp))
      have ih := Inv.placeM C h.2
      have hl := length_flatten_placeM (n := n) (w := w) (C := C) (Ls := L :: rest) (by simp)
      have hx := XX_keep n C Λ (rest := L :: rest) (rest' := Mark.placeM n w C (L :: rest)) fun σ => satL_placeM _ (by simp)
      rw [e] at ih hl hx ⊢
      refine ⟨?_, ih⟩
      unfold InvS
      rw [hl]
      have h1 := h.1
      unfold InvS at h1
      rw [← hx] at h1
      exact keep_step _ _ _ _ _ h1 (not_le.1 hd)

/-- The start: empty layers. -/
theorem inv_replicate {n w : ℕ} (hw : n + 2 ≤ w) : ∀ R : ℕ, Inv n w (List.replicate R [])
  | 0 => trivial
  | 1 => trivial
  | R + 2 => by
    refine ⟨?_, inv_replicate hw (R + 1)⟩
    have hf : (([] : Fml) :: List.replicate R []).flatten.length = 0 := by simp
    have hX : XX n [] (([] : Fml) :: List.replicate R []) = 2 ^ n := by
      have : ∀ σ : ℕ → Bool, satL σ (([] : Fml) :: List.replicate R []) := by
        intro σ L hL
        have : L = [] := by
          rcases List.mem_cons.1 hL with h | h
          · exact h
          · exact List.eq_of_mem_replicate h
        subst this; rfl
      simp [XX, this, nvio]
    unfold InvS
    rw [hf, hX]
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add, pow_zero, one_mul]
    have : 2 ^ n * 2 ^ 2 ≤ 2 ^ w := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) hw
    rw [pow_succ]; omega

/-- From the inequality: an assignment that satisfies the later layers violates fewer than w clauses
of Λ. -/
theorem InvS.nvio_lt {n w : ℕ} {Λ : Fml} {rest : List Fml} (h : InvS n w Λ rest) (σ : Fin n → Bool) (hs : satL (ext σ) rest) :
    nvio (ext σ) Λ < w := by
  have h1 : 2 ^ nvio (ext σ) Λ ≤ XX n Λ rest := by
    unfold XX
    have := Finset.single_le_sum (f := fun σ : Fin n → Bool => if satL (ext σ) rest then 2 ^ nvio (ext σ) Λ else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)
    simpa [hs] using this
  unfold InvS at h
  have h2 : 2 ^ nvio (ext σ) Λ * 2 ^ (rest.flatten.length + Λ.length + 2) < 2 ^ (w + rest.flatten.length + Λ.length + 1) := by
    have h3 : 0 < 3 ^ rest.flatten.length * 2 ^ w := by positivity
    have := Nat.mul_le_mul_right (2 ^ (rest.flatten.length + Λ.length + 2)) h1
    omega
  rw [← pow_add] at h2
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h2
  omega

/-- The invariant and a short last layer make the layers good. -/
theorem Inv.good {n w : ℕ} : ∀ {Ls : List Fml}, Inv n w Ls → (Ls.getLastD []).length ≤ w → Good n w Ls
  | [], _, _ => trivial
  | [Λ], _, hl => ⟨fun σ _ => (List.countP_le_length).trans hl, trivial⟩
  | Λ :: L :: rest, h, hl => ⟨fun σ hs => (h.1.nvio_lt σ hs).le, Inv.good h.2 (by simpa using hl)⟩

/-- From the inequality: the later layers hold at most about two thirds of the clauses. -/
theorem InvS.size {n w : ℕ} {Λ : Fml} {rest : List Fml} (h : InvS n w Λ rest) :
    3 * rest.flatten.length ≤ 2 * (rest.flatten.length + Λ.length) + 5 := by
  unfold InvS at h
  have h1 : 3 ^ rest.flatten.length * 2 ^ w ≤ 2 ^ (rest.flatten.length + Λ.length + 1) * 2 ^ w := by
    rw [← pow_add]
    refine le_trans (Nat.le_add_left _ _) (h.trans (le_of_eq ?_))
    congr 1; omega
  have h2 := Nat.le_of_mul_le_mul_right h1 (by positivity)
  have := size_step _ _ h2
  omega

/-- The last of R + 1 layers holds at most (2/3)^R of all clauses, and 5 more. -/
theorem Inv.last_le {n w : ℕ} : ∀ {Ls : List Fml}, Inv n w Ls → Ls ≠ [] →
    3 ^ (Ls.length - 1) * (Ls.getLastD []).length + 5 * 2 ^ (Ls.length - 1) ≤ 2 ^ (Ls.length - 1) * Ls.flatten.length + 5 * 3 ^ (Ls.length - 1)
  | [Λ], _, _ => by simp
  | Λ :: L :: rest, h, _ => by
    have ih := Inv.last_le h.2 (by simp)
    have hs := h.1.size
    have e1 : (Λ :: L :: rest).length - 1 = ((L :: rest).length - 1) + 1 := by simp
    have e2 : (Λ :: L :: rest).getLastD [] = (L :: rest).getLastD [] := by simp
    have e3 : (Λ :: L :: rest).flatten.length = (L :: rest).flatten.length + Λ.length := by
      rw [List.flatten_cons, List.length_append]; omega
    rw [e1, e2, e3]
    generalize (L :: rest).length - 1 = R at ih ⊢
    generalize ((L :: rest).getLastD []).length = a at ih ⊢
    generalize (L :: rest).flatten.length = κ at ih hs ⊢
    generalize Λ.length = d at hs ⊢
    rw [pow_succ, pow_succ]
    have h2 := Nat.mul_le_mul_left (2 ^ R) hs
    nlinarith

/-! ### What the test evaluates -/

/-- One evaluation on good layers, as a natural number. -/
theorem trunc_eq_XX {n w : ℕ} {Λ : Fml} {rest : List Fml} (h : Good n w (Λ :: rest)) : trunc n w (Λ :: rest) = (XX n Λ rest : ℤ) := by
  rw [trunc_of_good h, XX, Nat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hs : satL (ext σ) rest
  · rw [if_pos hs, if_pos (show ∀ L ∈ rest, nvio (ext σ) L = 0 from hs)]; norm_cast
  · rw [if_neg hs, if_neg (show ¬ ∀ L ∈ rest, nvio (ext σ) L = 0 from hs)]; norm_cast

/-- The layers with C on trial in the first of them are good. -/
theorem Inv.good_trial {n w : ℕ} (C : Cl) {Λ L : Fml} {rest : List Fml} (h : Inv n w (Λ :: L :: rest))
    (hl : ((Λ :: L :: rest).getLastD []).length ≤ w) : Good n w ((C :: Λ) :: L :: rest) := by
  refine ⟨fun σ hs => ?_, (h.good hl).2⟩
  have h1 := h.1.nvio_lt σ hs
  rw [nvio_cons]
  split_ifs <;> omega

/-- The quantity of a decision: the difference of two evaluations is the sum BB. -/
theorem trunc_sub_trunc {n w : ℕ} (C : Cl) {Λ L : Fml} {rest : List Fml} (h : Inv n w (Λ :: L :: rest))
    (hl : ((Λ :: L :: rest).getLastD []).length ≤ w) :
    trunc n w ((C :: Λ) :: L :: rest) - trunc n w (Λ :: L :: rest) = (BB n C Λ (L :: rest) : ℤ) := by
  rw [trunc_eq_XX (h.good_trial C hl), trunc_eq_XX (h.good hl), XX_cons]
  push_cast; ring

/-! ### Suffixes -/

/-- The invariant passes to the layers from number i on. -/
theorem Inv.drop {n w : ℕ} : ∀ {Ls : List Fml} (i : ℕ), Inv n w Ls → Inv n w (Ls.drop i)
  | _, 0, h => h
  | [], _ + 1, _ => trivial
  | [_], _ + 1, _ => by simp [Inv]
  | _ :: L :: rest, i + 1, h => by
    rw [List.drop_succ_cons]
    exact Inv.drop i h.2

/-! ### The placement by position -/

/-- The placement by recursion is the placement into the first layer whose test holds, or else the
last. -/
theorem placeM_eq_placeAt {n w : ℕ} (C : Cl) : ∀ {Ls : List Fml}, Ls ≠ [] → ∀ test : ℕ → Bool,
    (∀ i, i + 1 < Ls.length → (test i = true ↔ dropC n w C (Ls.getD i []) (Ls.drop (i + 1)))) →
    placeM n w C Ls = placeAt Ls C (((List.range (Ls.length - 1)).find? test).getD (Ls.length - 1))
  | [], h, _, _ => absurd rfl h
  | [Λ], _, _, _ => by simp [placeM, placeAt]
  | Λ :: L :: rest, _, test, ht => by
    have e : (Λ :: L :: rest).length - 1 = ((L :: rest).length - 1) + 1 := by simp
    rw [e, List.range_succ_eq_map, List.find?_cons, placeM]
    have h0 := ht 0 (by simp)
    simp only [List.getD_cons_zero, Nat.zero_add, List.drop_succ_cons, List.drop_zero] at h0
    by_cases hd : dropC n w C Λ (L :: rest)
    · rw [if_pos hd, h0.2 hd]
      simp [placeAt]
    · have hf : test 0 = false := by
        cases ht0 : test 0
        · rfl
        · exact absurd (h0.1 ht0) hd
      rw [if_neg hd, hf]
      have ih := placeM_eq_placeAt (n := n) (w := w) C (List.cons_ne_nil L rest) (fun i => test (i + 1)) (fun i hi => by
        have := ht (i + 1) (by simpa using hi)
        simpa using this)
      rw [ih, List.find?_map]
      cases hfind : (List.range ((L :: rest).length - 1)).find? (test ∘ Nat.succ) with
      | none =>
        have : (List.range ((L :: rest).length - 1)).find? (fun i => test (i + 1)) = none := hfind
        rw [this]
        simp [placeAt]
      | some j =>
        have : (List.range ((L :: rest).length - 1)).find? (fun i => test (i + 1)) = some j := hfind
        rw [this]
        simp [placeAt]

/-! ### All clauses -/

/-- The layers of ψ: R + 1 of them. -/
def layersM (n w R : ℕ) (ψ : Fml) : List Fml := ψ.foldl (fun Ls C => placeM n w C Ls) (List.replicate (R + 1) [])

/-- One more clause at the end of ψ is placed last. -/
theorem layersM_append (n w R : ℕ) (ψ : Fml) (C : Cl) : layersM n w R (ψ ++ [C]) = placeM n w C (layersM n w R ψ) := by
  simp [layersM]

/-- There are R + 1 layers. -/
theorem length_layersM (n w R : ℕ) (ψ : Fml) : (layersM n w R ψ).length = R + 1 := by
  induction ψ using List.reverseRecOn with
  | nil => simp [layersM]
  | append_singleton ψ C ih => rw [layersM_append, length_placeM, ih]

/-- There is at least one layer. -/
theorem layersM_ne_nil (n w R : ℕ) (ψ : Fml) : layersM n w R ψ ≠ [] := by
  intro h
  have := length_layersM n w R ψ
  rw [h] at this
  simp at this

/-- The layers of ψ satisfy the invariant. -/
theorem inv_layersM {n w : ℕ} (hw : n + 2 ≤ w) (R : ℕ) (ψ : Fml) : Inv n w (layersM n w R ψ) := by
  induction ψ using List.reverseRecOn with
  | nil => exact inv_replicate hw (R + 1)
  | append_singleton ψ C ih => rw [layersM_append]; exact ih.placeM C

/-- The layers of ψ have as many clauses as ψ. -/
theorem length_flatten_layersM (n w R : ℕ) (ψ : Fml) : (layersM n w R ψ).flatten.length = ψ.length := by
  induction ψ using List.reverseRecOn with
  | nil => simp [layersM]
  | append_singleton ψ C ih => rw [layersM_append, length_flatten_placeM (layersM_ne_nil n w R ψ), ih]; simp

/-- The layers of ψ are satisfied exactly if no clause of ψ is violated. -/
theorem satL_layersM (n w R : ℕ) (σ : ℕ → Bool) (ψ : Fml) : satL σ (layersM n w R ψ) ↔ nvio σ ψ = 0 := by
  induction ψ using List.reverseRecOn with
  | nil =>
    simp only [layersM, List.foldl_nil, nvio, List.countP_nil, iff_true]
    intro L hL
    rw [List.eq_of_mem_replicate hL]; rfl
  | append_singleton ψ C ih =>
    rw [layersM_append, satL_placeM σ (layersM_ne_nil n w R ψ), ih]
    simp only [nvio, List.countP_append, List.countP_cons, List.countP_nil]
    cases vio σ C <;> simp

/-- If 2^R·|ψ| + 5·3^R ≤ 3^R·c, the last layer has at most c clauses. -/
theorem last_layersM_le {n w : ℕ} (hw : n + 2 ≤ w) {R c : ℕ} {ψ : Fml} (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * c) :
    ((layersM n w R ψ).getLastD []).length ≤ c := by
  have h := (inv_layersM hw R ψ).last_le (layersM_ne_nil n w R ψ)
  rw [length_layersM, Nat.add_sub_cancel, length_flatten_layersM] at h
  have h2 : 3 ^ R * ((layersM n w R ψ).getLastD []).length ≤ 3 ^ R * c := by omega
  exact Nat.le_of_mul_le_mul_left h2 (by positivity)

/-- The layers of ψ are good. -/
theorem good_layersM {n w : ℕ} (hw : n + 2 ≤ w) {R : ℕ} {ψ : Fml} (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * w) :
    Good n w (layersM n w R ψ) := (inv_layersM hw R ψ).good (last_layersM_le hw hR)

/-- The final evaluation is the number of assignments that satisfy ψ. -/
theorem trunc_layersM {n w : ℕ} (hw : n + 2 ≤ w) {R : ℕ} {ψ : Fml} (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * w) :
    trunc n w ([] :: layersM n w R ψ) = (nSat n ψ : ℤ) := by
  rw [trunc_nil_cons (good_layersM hw hR), nSat]
  congr 2
  refine Finset.filter_congr fun σ _ => ?_
  rw [← nvio_eq_zero]
  exact satL_layersM n w R (ext σ) ψ

/-! ### The same with an evaluation function in place of the sums -/

/-- With the invariant, a short last layer and exact evaluations, the placement by evaluations is
the placement by sums. -/
theorem placeE_eq_placeM {n w : ℕ} {ev : List Fml → ℤ} {Ls : List Fml} (C : Cl) (h0 : Ls ≠ []) (hI : Inv n w Ls)
    (hl : (Ls.getLastD []).length ≤ w)
    (hev : ∀ i, i + 1 < Ls.length → ev (Ls.drop i) = trunc n w (Ls.drop i) ∧
      ev ((C :: Ls.getD i []) :: Ls.drop (i + 1)) = trunc n w ((C :: Ls.getD i []) :: Ls.drop (i + 1))) :
    placeE ev w Ls C = placeM n w C Ls := by
  rw [placeE, placeM_eq_placeAt C h0 (dropE ev w Ls C)]
  intro i hi
  obtain ⟨e1, e2⟩ := hev i hi
  have hd := drop_eq_cons (show i < Ls.length by omega)
  have hd' := drop_eq_cons hi
  have hIi : Inv n w (Ls.getD i [] :: Ls.getD (i + 1) [] :: Ls.drop (i + 1 + 1)) := by
    rw [← hd', ← hd]; exact hI.drop i
  have hli : ((Ls.getD i [] :: Ls.getD (i + 1) [] :: Ls.drop (i + 1 + 1)).getLastD []).length ≤ w := by
    rw [← hd', ← hd, getLastD_drop (by omega)]; exact hl
  have hB := trunc_sub_trunc C hIi hli
  rw [← hd'] at hB
  rw [dropE, e1, e2, decide_eq_true_iff, hd, hB, dropC, List.flatten_cons, List.length_append]
  rw [show (Ls.getD i []).length + (Ls.drop (i + 1)).flatten.length + 3 = (Ls.drop (i + 1)).flatten.length + (Ls.getD i []).length + 3 by omega]
  norm_cast

/-- After the placement of C the clauses of the layers are C and the clauses before, in some order. -/
theorem perm_flatten_placeM {n w : ℕ} (C : Cl) : ∀ {Ls : List Fml}, Ls ≠ [] → (placeM n w C Ls).flatten.Perm (C :: Ls.flatten)
  | [], h => absurd rfl h
  | [Λ], _ => by simp [placeM]
  | Λ :: L :: rest, _ => by
    rw [placeM]
    split_ifs
    · simp
    · rw [List.flatten_cons, List.flatten_cons (l := Λ)]
      exact ((perm_flatten_placeM C (List.cons_ne_nil L rest)).append_left Λ).trans List.perm_middle

/-- The clauses of the layers of ψ are the clauses of ψ, in some order. -/
theorem perm_flatten_layersM (n w R : ℕ) (ψ : Fml) : (layersM n w R ψ).flatten.Perm ψ := by
  induction ψ using List.reverseRecOn with
  | nil => simp [layersM]
  | append_singleton ψ C ih =>
    rw [layersM_append]
    exact (perm_flatten_placeM C (layersM_ne_nil n w R ψ)).trans ((ih.cons C).trans (List.perm_append_singleton C ψ).symm)

/-- One more clause at the end of ψ is placed last. -/
theorem layersE_append (ev : List Fml → ℤ) (w R : ℕ) (ψ : Fml) (C : Cl) : layersE ev w R (ψ ++ [C]) = placeE ev w (layersE ev w R ψ) C := by
  simp [layersE]

/-- If the evaluation is exact on the lists on which it is used, the layers by evaluations are the
layers by sums. -/
theorem layersE_eq_layersM {n w R : ℕ} {ev : List Fml → ℤ} {ψ : Fml} (hw : n + 2 ≤ w) (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * w)
    (hev : ∀ Ls, Asked n w R ψ Ls → ev Ls = trunc n w Ls) : ∀ ψ' : Fml, ψ' <+: ψ → layersE ev w R ψ' = layersM n w R ψ' := by
  intro ψ'
  induction ψ' using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton ψ' C ih =>
    intro hp
    have hp' : ψ' <+: ψ := (List.prefix_append ψ' [C]).trans hp
    have hlen : ψ'.length ≤ ψ.length := hp'.length_le
    have hR' : 2 ^ R * ψ'.length + 5 * 3 ^ R ≤ 3 ^ R * w := le_trans (by gcongr) hR
    have hI := inv_layersM hw R ψ'
    have hl := last_layersM_le hw hR'
    rw [layersE_append, ih hp', layersM_append]
    refine placeE_eq_placeM C (layersM_ne_nil n w R ψ') hI hl fun i hi => ?_
    have hL := length_layersM n w R ψ'
    have hd := drop_eq_cons (show i < (layersM n w R ψ').length by omega)
    have hd' := drop_eq_cons hi
    have hIi : Inv n w ((layersM n w R ψ').getD i [] :: (layersM n w R ψ').getD (i + 1) [] :: (layersM n w R ψ').drop (i + 1 + 1)) := by
      rw [← hd', ← hd]; exact hI.drop i
    have hli : (((layersM n w R ψ').getD i [] :: (layersM n w R ψ').getD (i + 1) [] :: (layersM n w R ψ').drop (i + 1 + 1)).getLastD []).length ≤ w := by
      rw [← hd', ← hd, getLastD_drop (by omega)]; exact hl
    have hsub : ((layersM n w R ψ').drop i).flatten.Subperm ψ' :=
      (flatten_drop_sublist _ i).subperm.trans (perm_flatten_layersM n w R ψ').subperm
    constructor
    · refine hev _ ⟨?_, ?_, hsub.trans hp'.sublist.subperm⟩
      · rw [hd, hd']; exact hIi.good hli
      · rw [List.length_drop]; omega
    · refine hev _ ⟨?_, ?_, ?_⟩
      · rw [hd']; exact hIi.good_trial C hli
      · rw [List.length_cons, List.length_drop]; omega
      · have h1 : ((C :: (layersM n w R ψ').getD i []) :: (layersM n w R ψ').drop (i + 1)).flatten = C :: ((layersM n w R ψ').drop i).flatten := by
          rw [hd]; simp
        rw [h1]
        exact ((List.subperm_cons C).2 hsub).trans ((List.perm_append_singleton C ψ').symm.subperm.trans hp.sublist.subperm)

/-- If the evaluation is exact on the lists on which it is used, the last evaluation is the number
of assignments that satisfy ψ. -/
theorem ev_layersE {n w R : ℕ} {ev : List Fml → ℤ} {ψ : Fml} (hw : n + 2 ≤ w) (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * w)
    (hev : ∀ Ls, Asked n w R ψ Ls → ev Ls = trunc n w Ls) :
    ev ([] :: layersE ev w R ψ) = (nSat n ψ : ℤ) := by
  rw [layersE_eq_layersM hw hR hev ψ (List.prefix_refl ψ), ← trunc_layersM hw hR]
  refine hev _ ⟨⟨fun σ _ => by simp [nvio], good_layersM hw hR⟩, ?_, ?_⟩
  · rw [List.length_cons, length_layersM]
  · rw [List.flatten_cons, List.nil_append]; exact (perm_flatten_layersM n w R ψ).subperm

end PaddedDescent.F.Mark

namespace PaddedDescent.F

/-- `Mark.ev_layersE`, in the form of the interface statements of
`proof/rates/PaddedDescent/F/Interfaces.lean`. -/
theorem stLayersE : StLayersE := fun _ _ _ _ _ hw hR hev => Mark.ev_layersE hw hR hev

end PaddedDescent.F
