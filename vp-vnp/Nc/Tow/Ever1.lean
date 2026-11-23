/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Load0
import Nc.Tow.Tree

/-!
# The units given at a node: relays of the stages
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r}

/-- Sums over relays. -/
theorem sum_RM {M : Type*} [AddCommMonoid M] (g : RM T m AA → M) : ∑ x, g x =
    (∑ a, ∑ c, ∑ γ, ∑ s, g (.start a c γ s)) + ((∑ j, ∑ i, ∑ e, g (.inn j i e)) +
      ((∑ j, ∑ e, ∑ s, g (.mid j e s)) + ∑ e, g (.fin e))) := by
  rw [← (rmEquiv T m AA).symm.sum_comp g]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma]
  rfl

section Levels

open Classical in
/-- Sums over the nodes of the levels before the last one. -/
theorem sum_level (g : ∀ j : Fin J, T.X j → ℕ) (j0 : ℕ) (hj0 : j0 ≤ J) (c : T.X j0) :
    (∑ j : Fin J, ∑ x, if nd T j j.2.le x = nd T j0 hj0 c then g j x else 0) =
      if hlt : j0 < J then g ⟨j0, hlt⟩ c else 0 := by
  by_cases hlt : j0 < J
  · rw [dif_pos hlt, Finset.sum_eq_single ⟨j0, hlt⟩, Finset.sum_eq_single c]
    · rw [if_pos rfl]
    · intro x _ hx
      rw [if_neg fun he => hx (nd_inj.1 he)]
    · intro hn; exact absurd (mem_univ _) hn
    · intro j _ hj
      refine Finset.sum_eq_zero fun x _ => if_neg ?_
      exact nd_ne fun he => hj (Fin.ext he)
    · intro hn; exact absurd (mem_univ _) hn
  · rw [dif_neg hlt]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x _ => if_neg ?_
    exact nd_ne fun he : j.1 = j0 => hlt (he ▸ j.2)

open Classical in
/-- Sums over the nodes of the levels after the first one. -/
theorem sum_level_zero (g : ∀ j : Fin J, T.X (j + 1) → ℕ) (c : T.X 0) :
    (∑ j : Fin J, ∑ x, if nd T (j + 1) j.2 x = nd T 0 (Nat.zero_le _) c then g j x else 0) = 0 := by
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x _ => if_neg ?_
  exact nd_ne (Nat.succ_ne_zero _)

open Classical in
/-- Sums over the nodes of the levels after the first one. -/
theorem sum_level_succ (g : ∀ j : Fin J, T.X (j + 1) → ℕ) (k : ℕ) (hk : k + 1 ≤ J) (c : T.X (k + 1)) :
    (∑ j : Fin J, ∑ x, if nd T (j + 1) j.2 x = nd T (k + 1) hk c then g j x else 0) = g ⟨k, hk⟩ c := by
  rw [Finset.sum_eq_single ⟨k, hk⟩, Finset.sum_eq_single c]
  · rw [if_pos rfl]
  · intro x _ hx
    rw [if_neg fun he => hx (nd_inj.1 he)]
  · intro hn; exact absurd (mem_univ _) hn
  · intro j _ hj
    refine Finset.sum_eq_zero fun x _ => if_neg ?_
    exact nd_ne fun he => hj (Fin.ext (Nat.succ_injective he))
  · intro hn; exact absurd (mem_univ _) hn

/-- A sum over edges by one of their ends. -/
theorem sum_end {κ X : Type*} [Fintype κ] [Fintype X] [DecidableEq X] (w : κ → X) (p : X → Prop) [DecidablePred p]
    (f : κ → ℕ) :
    (∑ e, if p (w e) then f e else 0) = ∑ x, if p x then ∑ e, (if w e = x then f e else 0) else 0 := by
  have h1 : ∀ e, (if p (w e) then f e else 0) = ∑ x, if p x then (if w e = x then f e else 0) else 0 := by
    intro e
    rw [Finset.sum_eq_single (w e)]
    · rw [if_pos rfl]
    · intro x _ hx
      rw [if_neg (Ne.symm hx)]
      split_ifs <;> rfl
    · intro hn; exact absurd (mem_univ _) hn
  rw [Finset.sum_congr rfl fun e _ => h1 e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rfl
  · simp

end Levels

variable (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ)

open Classical in
/-- Units between the children of a chamber and their parent. -/
noncomputable def chs (j : ℕ) (x : T.X (j + 1)) : ℕ := ∑ c : T.X j, if hostj hh Lf c = x then fb Lf j c else 0

open Classical in
theorem fb_eq (j : ℕ) (c : T.X j) : fb Lf j c = (∑ e, if T.e0 e = c then Lf j e else 0) +
    ∑ e, if T.e1 e = c then Lf j e else 0 := by
  unfold fb Tower.bet
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hne := T.e_ne e
  by_cases h0 : T.e0 e = c
  · have h1 : ¬ T.e1 e = c := fun hc => hne (h0.trans hc.symm)
    simp [h0, h1]
  · by_cases h1 : T.e1 e = c <;> simp [h0, h1]

open Classical in
theorem chs_eq (j : ℕ) (x : T.X (j + 1)) : chs hh Lf j x =
    (∑ e, if hostj hh Lf (T.e0 e) = x then Lf j e else 0) + ∑ e, if hostj hh Lf (T.e1 e) = x then Lf j e else 0 := by
  unfold chs
  rw [sum_end (fun e => T.e0 e) (fun c => hostj hh Lf c = x), sum_end (fun e => T.e1 e) (fun c => hostj hh Lf c = x),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · exact fb_eq Lf j c
  · rfl

section Num

variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

variable (R ch FL lhat n o) in
open Classical in
/-- The number of units given in a relay (0 if the relay does not exist). -/
noncomputable def nR (x : RM T m AA) : ℕ := if hx : okR T R ch x then num R ch FL lhat n o (.inl ⟨x, hx⟩) else 0

variable (R ch FL lhat n o) in
/-- The loads of the edges. -/
noncomputable abbrev ldL : ∀ j, T.Ed j → ℕ := lev (load R ch FL lhat n o)

theorem lev_castSucc (j : Fin J) (e : T.Ed j) : load R ch FL lhat n o (.edge j.castSucc e) =
    ldL R ch FL lhat n o j e := by
  unfold ldL lev
  rw [dif_pos (Nat.lt_succ_of_lt j.2)]
  rfl

theorem lev_succ (j : Fin J) (e : T.Ed (j + 1)) : load R ch FL lhat n o (.edge j.succ e) =
    ldL R ch FL lhat n o (j + 1) e := by
  unfold ldL lev
  rw [dif_pos (Nat.succ_lt_succ j.2)]
  rfl

theorem lev_last (e : T.Ed J) : load R ch FL lhat n o (.edge (Fin.last J) e) = ldL R ch FL lhat n o J e := by
  unfold ldL lev
  rw [dif_pos (Nat.lt_succ_self J)]
  rfl

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

theorem nR_inn (j : Fin J) (i : Fin h) (e : T.Ed j) : nR R ch FL lhat n o (.inn j i e) ≤
    if i = imin hh (ldL R ch FL lhat n o) j then ldL R ch FL lhat n o j e else 0 := by
  classical
  unfold nR
  split_ifs with hx h1 h1
  · refine (num_inl hr hb _).trans (le_of_eq ?_)
    exact lev_castSucc j e
  · rw [num_eq hr hb, numF, if_neg]
    intro ha
    exact h1 ((isMin_iff hh _ j.castSucc i).1 ha)
  · exact Nat.zero_le _
  · exact le_rfl

theorem nR_mid (j : Fin J) (e : T.Ed j) (s : Fin 4) : nR R ch FL lhat n o (.mid j e s) ≤
    if T.ty e = imin hh (ldL R ch FL lhat n o) j then ldL R ch FL lhat n o j e else 0 := by
  classical
  unfold nR
  split_ifs with hx h1 h1
  · obtain ⟨hx0, h2⟩ := num_mid_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e s hx
    refine h2.trans ((num_mid0 hr hb j e hx0).1.trans (le_of_eq ?_))
    exact lev_castSucc j e
  · obtain ⟨hx0, h2⟩ := num_mid_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e s hx
    refine h2.trans (le_of_eq ?_)
    refine (num_mid0 hr hb j e hx0).2 fun hm => h1 ?_
    exact (isMin_iff hh _ j.castSucc _).1 hm
  · exact Nat.zero_le _
  · exact le_rfl

theorem nR_fin (e : T.Ed J) : nR R ch FL lhat n o (.fin e) ≤ ldL R ch FL lhat n o J e := by
  classical
  unfold nR
  split_ifs with hx
  · refine (num_inl hr hb _).trans (le_of_eq ?_)
    exact lev_last e
  · exact Nat.zero_le _

end Num

end Nc.Tow
