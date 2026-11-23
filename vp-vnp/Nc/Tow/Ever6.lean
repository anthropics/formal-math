/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Ever4
import Nc.Tow.Tree

/-!
# The units that a party ever holds, by the loads at its chamber
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000

namespace Nc.Tow

open Finset Nc.G

section Tree

variable {h b D J r AA : ℕ} {T : Tower h b D J r} {hh : 0 < h} {Lf : ∀ j, T.Ed j → ℕ}

/-- Units between the children of a chamber and the chamber. -/
noncomputable def chF (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) : ∀ j, T.X j → ℕ
  | 0, _ => 0
  | j + 1, c => chs hh Lf j c

end Tree

section Ever

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}
  {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}

variable (hh : 0 < h) (hr : 0 < r) (hb : 0 < b)
  (hgR : ∀ (x : {x : RM T m AA // okR T R ch x}) (ν : Bool),
    oo R FL Pl o ⟨.inl x, ν⟩ = num R ch FL lhat (nn n) (oo R FL Pl o) (.inl x))
  (hgL : ∀ l : LMv T FL, GoodL R ch FL (oo R FL Pl o) l (num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l)) ∧
    ∀ ν, num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) ≤ oo R FL Pl o ⟨.inr l, ν⟩)
  (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f)

variable (R ch FL Pl lhat n o) in
/-- The loads. -/
noncomputable abbrev LfO : ∀ j, T.Ed j → ℕ := ldL R ch FL lhat (nn n) (oo R FL Pl o)

variable (ch) in
open Classical in
/-- Is the node a base party? -/
noncomputable def isB (P : Nd T) : ℕ := if ∃ a, P = nd T 0 (Nat.zero_le _) (ch a) then 1 else 0

include hh hr hb hgR in
open Classical in
theorem NR_onN (P : Nd T) : NR R ch FL lhat (nn n) (oo R FL Pl o) P ≤ isB ch P * (2 * m * lhat) +
    onN (fun j x => 8 * fb (LfO R ch FL Pl lhat n o) j x + 3 * chF hh (LfO R ch FL Pl lhat n o) j x)
      (∑ e : T.Ed J, LfO R ch FL Pl lhat n o J e) P := by
  rcases nd_cases P with rfl | ⟨j, hj, c, rfl⟩
  · exact (NR_none hh hr hb hgR).trans (Nat.le_add_left _ _)
  · rw [onN_nd]
    cases j with
    | zero =>
      refine (NR_zero hh hr hb hgR c).trans (add_le_add ?_ ?_)
      · unfold isB
        by_cases hc : ∃ a, ch a = c
        · obtain ⟨a, rfl⟩ := hc
          rw [if_pos ⟨a, rfl⟩, if_pos ⟨a, rfl⟩, Nat.one_mul]
        · rw [if_neg hc]
          exact Nat.zero_le _
      · change 7 * fb (LfO R ch FL Pl lhat n o) 0 c ≤ 8 * fb (LfO R ch FL Pl lhat n o) 0 c +
          3 * chF hh (LfO R ch FL Pl lhat n o) 0 c
        omega
    | succ j =>
      refine (NR_succ hh hr hb hgR hj c).trans (le_trans (le_of_eq ?_) (Nat.le_add_left _ _))
      rfl

include hh hr hb hgL hnr in
open Classical in
theorem NL_onN (P : Nd T) : NL R ch FL lhat (nn n) (oo R FL Pl o) P ≤ Fintype.card FL.Di *
    onN (fun j x => 8 * fb (LfO R ch FL Pl lhat n o) j x + 3 * chF hh (LfO R ch FL Pl lhat n o) j x)
      (∑ e : T.Ed J, LfO R ch FL Pl lhat n o J e) P := by
  rcases nd_cases P with rfl | ⟨j, hj, c, rfl⟩
  · rw [NL_none]
    exact Nat.zero_le _
  · rw [onN_nd]
    cases j with
    | zero =>
      rw [NL_zero]
      exact Nat.zero_le _
    | succ j =>
      refine (NL_succ hh hr hb hgL hnr hj c).trans (Nat.mul_le_mul_left _ ?_)
      change fb (LfO R ch FL Pl lhat n o) (j + 1) c ≤ 8 * fb (LfO R ch FL Pl lhat n o) (j + 1) c +
        3 * chF hh (LfO R ch FL Pl lhat n o) (j + 1) c
      omega

open Classical in
theorem initN_le {ℓf : ℕ} (P : Nd T) (hP : ∀ a, P = nd T 0 (Nat.zero_le _) (ch a) →
    ∑ c, ((n a c).1 + (n c a).1) ≤ ℓf) : initN (A' := A') n (Pl.pt P) ≤ isB ch P * ℓf := by
  unfold isB
  split_ifs with hB
  · obtain ⟨a, rfl⟩ := hB
    rw [Nat.one_mul]
    refine le_trans (le_of_eq ?_) (hP a rfl)
    rw [Pl.pt_base]
    unfold initN
    have h1 : ∀ a' c : Fin AA, (if Fin.castAdd A' a' = Fin.castAdd A' a then (n a' c).1 else 0) =
        if a' = a then (n a c).1 else 0 := by
      intro a' c
      by_cases ha : a' = a
      · subst ha; simp
      · rw [if_neg fun he => ha (Fin.castAdd_injective _ _ he), if_neg ha]
    have h2 : ∀ a' c : Fin AA, (if Fin.castAdd A' c = Fin.castAdd A' a then (n a' c).1 else 0) =
        if c = a then (n a' a).1 else 0 := by
      intro a' c
      by_cases ha : c = a
      · subst ha; simp
      · rw [if_neg fun he => ha (Fin.castAdd_injective _ _ he), if_neg ha]
    simp only [h1, h2, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_ite_eq', if_pos (mem_univ _)]
    · refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.sum_ite_eq', if_pos (mem_univ _)]
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    unfold initN
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
    have hne : ∀ a, Fin.castAdd A' a ≠ Pl.pt P := by
      intro a ha
      rw [← Pl.pt_base] at ha
      exact hB ⟨a, (Pl.pt.injective ha).symm⟩
    rw [if_neg (hne a), if_neg (hne c), Nat.add_zero]

end Ever

end Nc.Tow
