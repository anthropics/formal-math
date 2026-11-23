/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Plan
import Nc.G.Defs

/-!
# Cardinalities of the tower plan
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

section General

theorem sum_inj_le {α β : Type*} [Fintype α] [Fintype β] {g : α → β} (hg : Function.Injective g) (f : β → ℕ) :
    ∑ a, f (g a) ≤ ∑ b, f b := by
  classical
  rw [← Finset.sum_image (f := f) (g := g) (s := univ) fun x _ y _ h => hg h]
  exact Finset.sum_le_sum_of_subset (subset_univ _)

end General

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r}

namespace Tower

/-- The levels shrink. -/
theorem card_X_le (hD : 0 < D) : ∀ j ≤ J, Fintype.card (T.X j) ≤ Fintype.card (T.X 0) := by
  intro j
  induction j with
  | zero => exact fun _ => le_rfl
  | succ j ih =>
    intro hj
    refine le_trans ?_ (ih (by omega))
    rw [T.card_X j (by omega)]
    exact Nat.le_mul_of_pos_left _ hD

theorem two_card_ed {j : ℕ} (hj : j ≤ J) : 2 * Fintype.card (T.Ed j) = h * (r * Fintype.card (T.X j)) := by
  have h1 : Fintype.card (T.Ed j) = ∑ i : Fin h, (univ.filter fun e : T.Ed j => T.ty e = i).card := by
    rw [← card_univ]
    exact card_eq_sum_card_fiberwise (fun _ _ => mem_coe.2 (mem_univ _))
  rw [h1, Finset.mul_sum, Finset.sum_congr rfl fun i _ => T.card_ed j hj i]
  simp

theorem card_ed_le (hD : 0 < D) {j : ℕ} (hj : j ≤ J) : Fintype.card (T.Ed j) ≤ h * r * Fintype.card (T.X 0) := by
  have h1 := two_card_ed (T := T) hj
  have h2 : h * (r * Fintype.card (T.X j)) ≤ h * r * Fintype.card (T.X 0) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (card_X_le hD j hj)
  omega

theorem card_V_le (hD : 0 < D) (hb : 0 < b) {j : ℕ} (hj : j ≤ J) (i : Fin h) :
    Fintype.card (T.V j i) ≤ Fintype.card (T.X 0) := by
  have h1 : Fintype.card (T.V j i) * b = Fintype.card (T.X j) := by
    rw [Fintype.card_of_bijective (T.vx_co hj i), Fintype.card_prod, T.card_fl]
  refine le_trans ?_ (card_X_le hD j hj)
  rw [← h1]
  exact Nat.le_mul_of_pos_right _ hb

theorem card_V_Nr {j : ℕ} (hj : j ≤ J) (i : Fin h) :
    Fintype.card (T.V j i) * Fintype.card T.Nr ≤ Fintype.card (T.Ed j) := by
  rw [← Fintype.card_prod, ← Fintype.card_congr (T.nr hj i)]
  exact Fintype.card_subtype_le _

end Tower

/-- The bound for the number of relays. -/
def rmN (h r m J AA X0 : ℕ) : ℕ := AA * (AA * (X0 * (2 * m))) + (J * (h + 4) + 1) * (h * r * X0)

/-- The bound for the number of law moves. -/
def lmN (h J X0 dd : ℕ) : ℕ := J * (h * (X0 * dd))

theorem card_RM_le (hD : 0 < D) : Fintype.card (RM T m AA) ≤ rmN h r m J AA (Fintype.card (T.X 0)) := by
  rw [Fintype.card_congr (rmEquiv T m AA)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  have h1 : ∀ j : Fin J, Fintype.card (T.Ed j) ≤ h * r * Fintype.card (T.X 0) := fun j => Tower.card_ed_le hD j.2.le
  have h2 := Tower.card_ed_le (T := T) hD (le_refl J)
  have h3 : ∑ j : Fin J, h * Fintype.card (T.Ed j) ≤ J * (h * (h * r * Fintype.card (T.X 0))) := by
    calc ∑ j : Fin J, h * Fintype.card (T.Ed j) ≤ ∑ _j : Fin J, h * (h * r * Fintype.card (T.X 0)) :=
          Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (h1 j)
      _ = _ := by simp
  have h4 : ∑ j : Fin J, Fintype.card (T.Ed j) * 4 ≤ J * (h * r * Fintype.card (T.X 0) * 4) := by
    calc ∑ j : Fin J, Fintype.card (T.Ed j) * 4 ≤ ∑ _j : Fin J, h * r * Fintype.card (T.X 0) * 4 :=
          Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (h1 j)
      _ = _ := by simp
  unfold rmN
  refine Nat.add_le_add_left ?_ _
  calc _ ≤ J * (h * (h * r * Fintype.card (T.X 0))) + (J * (h * r * Fintype.card (T.X 0) * 4) +
        h * r * Fintype.card (T.X 0)) := Nat.add_le_add h3 (Nat.add_le_add h4 h2)
    _ = _ := by ring

section Moves

variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'}

theorem card_LMv_le (hD : 0 < D) (hb : 0 < b) :
    Fintype.card (LMv T FL) ≤ lmN h J (Fintype.card (T.X 0)) (Fintype.card FL.Di) := by
  simp only [Fintype.card_sigma, Fintype.card_prod]
  unfold lmN
  calc ∑ j : Fin J, ∑ i : Fin h, Fintype.card (T.V (j + 1) i) * Fintype.card FL.Di ≤
      ∑ _j : Fin J, ∑ _i : Fin h, Fintype.card (T.X 0) * Fintype.card FL.Di :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
          Nat.mul_le_mul_right _ (Tower.card_V_le hD hb j.2 i)
    _ = _ := by simp

/-- Sums over moves. -/
theorem sum_mv_le (f : Mv T R ch FL → ℕ) {a : ℕ} {g : LMv T FL → ℕ} (h1 : ∀ x, f (.inl x) ≤ a)
    (h2 : ∀ l, f (.inr l) ≤ g l) : ∑ mv, f mv ≤ Fintype.card (RM T m AA) * a + ∑ l, g l := by
  have hinj : Function.Injective (Sum.map Subtype.val id : Mv T R ch FL → RM T m AA ⊕ LMv T FL) :=
    Function.Injective.sumMap Subtype.val_injective Function.injective_id
  have h3 : ∀ mv : Mv T R ch FL, f mv ≤ Sum.elim (fun _ => a) g (Sum.map Subtype.val id mv) := by
    rintro (x | l)
    · exact h1 x
    · exact h2 l
  refine (Finset.sum_le_sum fun mv _ => h3 mv).trans ((sum_inj_le hinj (Sum.elim (fun _ => a) g)).trans ?_)
  rw [Fintype.sum_sum_type]
  simp

theorem sum_moves (f : Mv T R ch FL → ℕ) : ∑ x, f (eE R FL x) = ∑ mv, f mv := Equiv.sum_comp (eE R FL) f

theorem card_Mv_le (hD : 0 < D) (hb : 0 < b) : Fintype.card (Mv T R ch FL) ≤
    rmN h r m J AA (Fintype.card (T.X 0)) + lmN h J (Fintype.card (T.X 0)) (Fintype.card FL.Di) := by
  have h1 := sum_mv_le (R := R) (ch := ch) (FL := FL) (fun _ => 1) (a := 1) (g := fun _ => 1) (fun _ => le_rfl)
    fun _ => le_rfl
  simp only [Finset.sum_const, card_univ, smul_eq_mul, Nat.mul_one] at h1
  exact h1.trans (Nat.add_le_add (card_RM_le hD) (card_LMv_le hD hb))

/-- Channels. -/
theorem card_N_le (hD : 0 < D) : Fintype.card (sys R FL Pl).N ≤ rmN h r m J AA (Fintype.card (T.X 0)) * 2 +
    J * (h * (h * r * Fintype.card (T.X 0) * Fintype.card FL.Di)) := by
  have e : Fintype.card (sys R FL Pl).N = ∑ mv : Mv T R ch FL, Fintype.card (kindM R ch FL mv).Cn := by
    rw [Fintype.card_sigma]
    exact sum_moves fun mv => Fintype.card (kindM R ch FL mv).Cn
  rw [e]
  refine (sum_mv_le (a := 2) (g := fun _ => Fintype.card T.Nr) _ (fun x => ?_) fun l => ?_).trans ?_
  · exact le_of_eq (Fintype.card_congr (Equiv.refl Bool))
  · exact le_of_eq (Fintype.card_congr (FL.cn l.2.2.2))
  · refine Nat.add_le_add (Nat.mul_le_mul_right _ (card_RM_le hD)) ?_
    have h1 : ∑ _l : LMv T FL, Fintype.card T.Nr =
        ∑ j : Fin J, ∑ i : Fin h, Fintype.card (T.V (j + 1) i) * Fintype.card T.Nr * Fintype.card FL.Di := by
      rw [Finset.sum_const, card_univ, smul_eq_mul, Fintype.card_sigma, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fintype.card_sigma, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.card_prod]
      ring
    rw [h1]
    calc _ ≤ ∑ _j : Fin J, ∑ _i : Fin h, h * r * Fintype.card (T.X 0) * Fintype.card FL.Di :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _
            ((Tower.card_V_Nr j.2 i).trans (Tower.card_ed_le hD j.2))
      _ = _ := by simp

/-- Slots. -/
theorem card_Z_le (hD : 0 < D) (hb : 0 < b) {S : ℕ} (hS : ∀ d, Fintype.card (FL.L d).Sl ≤ S) :
    Fintype.card (sys R FL Pl).Z ≤ rmN h r m J AA (Fintype.card (T.X 0)) +
      lmN h J (Fintype.card (T.X 0)) (Fintype.card FL.Di) * S := by
  have e : Fintype.card (sys R FL Pl).Z = ∑ mv : Mv T R ch FL, Fintype.card (kindM R ch FL mv).Sl := by
    rw [Fintype.card_sigma]
    exact sum_moves fun mv => Fintype.card (kindM R ch FL mv).Sl
  rw [e]
  refine (sum_mv_le (a := 1) (g := fun _ => S) _ (fun x => ?_) fun l => hS l.2.2.2).trans ?_
  · exact le_of_eq (Fintype.card_congr (Equiv.refl Unit))
  · rw [Nat.mul_one, Finset.sum_const, card_univ, smul_eq_mul]
    exact Nat.add_le_add (card_RM_le hD) (Nat.mul_le_mul_right _ (card_LMv_le hD hb))

/-- Roles. -/
theorem card_R_le (hD : 0 < D) (hb : 0 < b) : Fintype.card (sys R FL Pl).R ≤
    rmN h r m J AA (Fintype.card (T.X 0)) * 3 + lmN h J (Fintype.card (T.X 0)) (Fintype.card FL.Di) * b := by
  have e : Fintype.card (sys R FL Pl).R = ∑ mv : Mv T R ch FL, Fintype.card (kindM R ch FL mv).Ro := by
    rw [Fintype.card_sigma]
    exact sum_moves fun mv => Fintype.card (kindM R ch FL mv).Ro
  rw [e]
  refine (sum_mv_le (a := 3) (g := fun _ => b) _ (fun x => ?_) fun l => ?_).trans ?_
  · exact le_of_eq ((Fintype.card_congr (Equiv.refl (Fin 3))).trans (Fintype.card_fin 3))
  · exact le_of_eq ((Fintype.card_congr (FL.ro l.2.2.2)).trans T.card_fl)
  · rw [Finset.sum_const, card_univ, smul_eq_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (card_RM_le hD)) (Nat.mul_le_mul_right _ (card_LMv_le hD hb))

/-- Units. -/
theorem card_Un : Fintype.card (Un R FL Pl U0 U1) = AA * AA * U0 + Fintype.card (sys R FL Pl).N * U1 := by
  let e : Un R FL Pl U0 U1 ≃ (Fin AA × Fin AA × Fin U0) ⊕ ((sys R FL Pl).N × Fin U1) :=
    { toFun := fun u => match u with
        | .init a c k => .inl (a, c, k)
        | .new ν k => .inr (ν, k)
      invFun := fun s => match s with
        | .inl q => .init q.1 q.2.1 q.2.2
        | .inr q => .new q.1 q.2
      left_inv := fun u => by cases u <;> rfl
      right_inv := fun s => by rcases s with ⟨a, c, k⟩ | ⟨ν, k⟩ <;> rfl }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  simp only [Fintype.card_fin]
  ring

end Moves

/-- Nodes. -/
theorem card_Nd_le (hD : 0 < D) : Fintype.card (Nd T) ≤ (J + 1) * Fintype.card (T.X 0) + 1 := by
  rw [Fintype.card_option, Fintype.card_sigma]
  refine Nat.add_le_add_right ?_ _
  calc ∑ j : Fin (J + 1), Fintype.card (T.X j) ≤ ∑ _j : Fin (J + 1), Fintype.card (T.X 0) :=
        Finset.sum_le_sum fun j _ => Tower.card_X_le hD j.1 (Nat.le_of_lt_succ j.2)
    _ = _ := by simp

/-- Parties. -/
theorem card_party {ch : Fin AA ↪ T.X 0} (Pl : Place T ch A') : AA + A' = Fintype.card (Nd T) := by
  rw [Fintype.card_congr Pl.pt, Fintype.card_fin]

/-! ### Powers of one bound -/

section Powers

variable {V : ℕ}

theorem rmN_le {X0 : ℕ} (hV : 1 ≤ V) (hh : h ≤ V) (hr : r ≤ V) (hm : m ≤ V) (hJ : J ≤ V) (hAA : AA ≤ V) (hX : X0 ≤ V) :
    rmN h r m J AA X0 ≤ 8 * V ^ 5 := by
  have h1 : rmN h r m J AA X0 ≤ V * (V * (V * (2 * V))) + (V * (V + 4) + 1) * (V * V * V) := by
    unfold rmN
    gcongr
  refine h1.trans ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hV
  ring_nf
  omega

theorem lmN_le {X0 dd : ℕ} (hh : h ≤ V) (hJ : J ≤ V) (hX : X0 ≤ V) (hdd : dd ≤ V) : lmN h J X0 dd ≤ V ^ 4 := by
  have h1 : lmN h J X0 dd ≤ V * (V * (V * V)) := by
    unfold lmN
    gcongr
  exact h1.trans (le_of_eq (by ring))

variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'}

/-- Channels, slots, roles, names of units. -/
theorem cards_le (hD : 0 < D) (hb : 0 < b) (hV : 1 ≤ V) (hh : h ≤ V) (hr : r ≤ V) (hm : m ≤ V) (hJ : J ≤ V)
    (hAA : AA ≤ V) (hX : Fintype.card (T.X 0) ≤ V) (hdd : Fintype.card FL.Di ≤ V) (hbV : b ≤ V)
    (hS : ∀ d, Fintype.card (FL.L d).Sl ≤ V) (hU0 : U0 ≤ V) (hU1 : U1 ≤ V) :
    Fintype.card (sys R FL Pl).N ≤ 17 * V ^ 6 ∧ Fintype.card (sys R FL Pl).Z ≤ 9 * V ^ 5 ∧
      Fintype.card (sys R FL Pl).R ≤ 25 * V ^ 5 ∧ Fintype.card (Un R FL Pl U0 U1) ≤ 18 * V ^ 7 ∧
      Fintype.card (Mv T R ch FL) ≤ 9 * V ^ 5 ∧ Fintype.card (Nd T) ≤ 3 * V ^ 2 := by
  have h1 := rmN_le (X0 := Fintype.card (T.X 0)) hV hh hr hm hJ hAA hX
  have h2 := lmN_le (X0 := Fintype.card (T.X 0)) hh hJ hX hdd
  have p45 : V ^ 4 ≤ V ^ 5 := Nat.pow_le_pow_right hV (by norm_num)
  have p56 : V ^ 5 ≤ V ^ 6 := Nat.pow_le_pow_right hV (by norm_num)
  have p37 : V ^ 3 ≤ V ^ 7 := Nat.pow_le_pow_right hV (by norm_num)
  have p12 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) V
  have p02 : 1 ≤ V ^ 2 := Nat.one_le_pow _ _ hV
  have hN : Fintype.card (sys R FL Pl).N ≤ 17 * V ^ 6 := by
    have h3 := card_N_le (R := R) (FL := FL) (Pl := Pl) hD
    have h4 : J * (h * (h * r * Fintype.card (T.X 0) * Fintype.card FL.Di)) ≤ V * (V * (V * V * V * V)) := by gcongr
    have h5 : V * (V * (V * V * V * V)) = V ^ 6 := by ring
    omega
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_⟩
  · have h3 := card_Z_le (R := R) (FL := FL) (Pl := Pl) hD hb hS
    have h4 := Nat.mul_le_mul_right V h2
    have h5 : V ^ 4 * V = V ^ 5 := by ring
    omega
  · have h3 := card_R_le (R := R) (FL := FL) (Pl := Pl) hD hb
    have h4 : lmN h J (Fintype.card (T.X 0)) (Fintype.card FL.Di) * b ≤ V ^ 4 * V := Nat.mul_le_mul h2 hbV
    have h5 : V ^ 4 * V = V ^ 5 := by ring
    omega
  · rw [card_Un]
    have h4 : AA * AA * U0 ≤ V * V * V := by gcongr
    have h5 : Fintype.card (sys R FL Pl).N * U1 ≤ 17 * V ^ 6 * V := Nat.mul_le_mul hN hU1
    have h6 : V * V * V = V ^ 3 := by ring
    have h7 : 17 * V ^ 6 * V = 17 * V ^ 7 := by ring
    omega
  · have h3 := card_Mv_le (R := R) (ch := ch) (FL := FL) hD hb
    omega
  · have h3 := card_Nd_le (T := T) hD
    have h4 : (J + 1) * Fintype.card (T.X 0) ≤ (V + 1) * V := by gcongr
    have h5 : (V + 1) * V = V ^ 2 + V := by ring
    omega

end Powers

end Nc.Tow
