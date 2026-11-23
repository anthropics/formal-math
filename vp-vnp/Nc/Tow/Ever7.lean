/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Ever6

/-!
# The copies at a node
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}
  {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}

/-- Roles by their moves. -/
noncomputable def eR (R : Routes T m Uu) {ch : Fin AA ↪ T.X 0} (FL : FlagLaws F T) (Pl : Place T ch A') :
    (sys R FL Pl).R ≃ Σ mv : Mv T R ch FL, (kindM R ch FL mv).Ro :=
  Equiv.sigmaCongrLeft (β := fun mv => (kindM R ch FL mv).Ro) (eE R FL)

variable (R ch FL Pl lhat n o) in
/-- Units of zeros and counts of a role. -/
noncomputable def padR (r' : (sys R FL Pl).R) : ℕ :=
  (1 + Fintype.card (((sys R FL Pl).kind r'.1).SlAt r'.2)) * num R ch FL lhat (nn n) (oo R FL Pl o) (eE R FL r'.1)

open Classical in
/-- **The units of zeros at a node.** -/
theorem pads_node {Sm : ℕ} (hSm : ∀ d, Fintype.card (FL.L d).Sl ≤ Sm) (P : Nd T) :
    (∑ r' : (sys R FL Pl).R, if (sys R FL Pl).rp r' = Pl.pt P then padR R ch FL Pl lhat n o r' else 0) ≤
      2 * NR R ch FL lhat (nn n) (oo R FL Pl o) P + (1 + Sm) * NL R ch FL lhat (nn n) (oo R FL Pl o) P := by
  have h1 : (∑ r' : (sys R FL Pl).R, if (sys R FL Pl).rp r' = Pl.pt P then padR R ch FL Pl lhat n o r' else 0) =
      ∑ y : (Σ mv : Mv T R ch FL, (kindM R ch FL mv).Ro), if partM R ch FL y.1 y.2 = P then
        (1 + Fintype.card ((kindM R ch FL y.1).SlAt y.2)) * num R ch FL lhat (nn n) (oo R FL Pl o) y.1 else 0 := by
    rw [← Equiv.sum_comp (eR R FL Pl)]
    refine Finset.sum_congr rfl fun r' _ => if_congr ?_ rfl rfl
    exact Pl.pt.injective.eq_iff
  rw [h1, Fintype.sum_sigma, Fintype.sum_sum_type]
  refine add_le_add ?_ ?_
  · have h7 : (∑ x : {x : RM T m AA // okR T R ch x}, 2 * ∑ q : Fin 3, if tri T R ch x.1 q = P then
        nR R ch FL lhat (nn n) (oo R FL Pl o) x.1 else 0) ≤ 2 * NR R ch FL lhat (nn n) (oo R FL Pl o) P := by
      rw [← Finset.mul_sum]
      refine Nat.mul_le_mul_left _ ?_
      exact sum_sub_le (fun x => okR T R ch x) fun x => ∑ q : Fin 3, if tri T R ch x q = P then
        nR R ch FL lhat (nn n) (oo R FL Pl o) x else 0
    refine le_trans (Finset.sum_le_sum fun x _ => ?_) h7
    rw [Finset.mul_sum]
    have h6 : nR R ch FL lhat (nn n) (oo R FL Pl o) x.1 = num R ch FL lhat (nn n) (oo R FL Pl o) (.inl x) := by
      unfold nR
      rw [dif_pos x.2]
    have h2 : ∀ (q : (relay F).Ro) (inst : Fintype ((relay F).SlAt q)), @Fintype.card _ inst ≤ 1 := fun q inst => by
      refine (Fintype.card_le_of_injective (Subtype.val : (relay F).SlAt q → Unit) Subtype.val_injective).trans ?_
      exact le_of_eq Fintype.card_unit
    rw [h6]
    refine Finset.sum_le_sum (ι := (relay F).Ro) fun q _ => ?_
    by_cases hq : partM R ch FL (.inl x) q = P
    · rw [if_pos hq, if_pos (show tri T R ch x.1 q = P from hq)]
      refine Nat.mul_le_mul_right _ ?_
      exact Nat.add_le_add_left (h2 q _) 1
    · rw [if_neg hq]
      exact Nat.zero_le _
  · unfold NL
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [Finset.mul_sum, ← Equiv.sum_comp (FL.ro l.2.2.2)]
    refine Finset.sum_le_sum (ι := (FL.L l.2.2.2).Ro) fun p _ => ?_
    change (if nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 p)) = P then _ else 0) ≤ _
    have h2 : ∀ (inst : Fintype ((FL.L l.2.2.2).SlAt p)), @Fintype.card _ inst ≤ Sm := fun inst =>
      (Fintype.card_le_of_injective (Subtype.val : (FL.L l.2.2.2).SlAt p → (FL.L l.2.2.2).Sl)
        Subtype.val_injective).trans (hSm _)
    split_ifs
    · exact Nat.mul_le_mul_right _ (Nat.add_le_add_left (h2 _) 1)
    · exact le_rfl

open Classical in
/-- **The copies at a node**, units of zeros and counts included: the start at a base party, one end for every channel,
and a constant times the loads at the chamber and below its children. -/
theorem held_node_le (hh : 0 < h) (hr : 0 < r) (hb : 0 < b)
    (hgR : ∀ (x : {x : RM T m AA // okR T R ch x}) (ν : Bool),
      oo R FL Pl o ⟨.inl x, ν⟩ = num R ch FL lhat (nn n) (oo R FL Pl o) (.inl x))
    (hgL : ∀ l : LMv T FL, GoodL R ch FL (oo R FL Pl o) l (num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l)) ∧
      ∀ ν, num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) ≤ oo R FL Pl o ⟨.inr l, ν⟩)
    (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f) {Sm : ℕ} (hSm : ∀ d, Fintype.card (FL.L d).Sl ≤ Sm) {ℓf : ℕ}
    (P : Nd T) (hini : ∀ a, P = nd T 0 (Nat.zero_le _) (ch a) → ∑ c, ((n a c).1 + (n c a).1) ≤ ℓf) :
    heldN R FL Pl n o (Pl.pt P) +
      (∑ r' : (sys R FL Pl).R, if (sys R FL Pl).rp r' = Pl.pt P then padR R ch FL Pl lhat n o r' else 0) ≤
      isB ch P * (ℓf + 8 * m * lhat) + chanN R FL Pl (Pl.pt P) +
        (4 + (2 * Fintype.card T.Nr * FL.G₁ + 1 + Sm) * Fintype.card FL.Di) *
          onN (fun j x => 8 * fb (LfO R ch FL Pl lhat n o) j x + 3 * chF hh (LfO R ch FL Pl lhat n o) j x)
            (∑ e : T.Ed J, LfO R ch FL Pl lhat n o J e) P := by
  set Lf := LfO R ch FL Pl lhat n o with hLf
  set f : ∀ j, T.X j → ℕ := fun j x => 8 * fb Lf j x + 3 * chF hh Lf j x with hf
  set f0 := ∑ e : T.Ed J, Lf J e with hf0
  set c1 := 2 * Fintype.card T.Nr * FL.G₁ with hc1
  have a1 : heldN R FL Pl n o (Pl.pt P) ≤ initN (A' := A') n (Pl.pt P) + chanN R FL Pl (Pl.pt P) +
      2 * NR R ch FL lhat (nn n) (oo R FL Pl o) P + c1 * NL R ch FL lhat (nn n) (oo R FL Pl o) P :=
    held_le hr hb hgR hgL P
  have a2 := pads_node (R := R) (Pl := Pl) (lhat := lhat) (n := n) (o := o) hSm P
  have a3 : NR R ch FL lhat (nn n) (oo R FL Pl o) P ≤ isB ch P * (2 * m * lhat) + onN f f0 P :=
    NR_onN hh hr hb hgR P
  have a4 : NL R ch FL lhat (nn n) (oo R FL Pl o) P ≤ Fintype.card FL.Di * onN f f0 P :=
    NL_onN hh hr hb hgL hnr P
  have a5 := initN_le (Pl := Pl) (n := n) (ℓf := ℓf) P hini
  generalize NR R ch FL lhat (nn n) (oo R FL Pl o) P = NRv at a1 a2 a3
  generalize NL R ch FL lhat (nn n) (oo R FL Pl o) P = NLv at a1 a2 a4
  have a6 : c1 * NLv ≤ c1 * (Fintype.card FL.Di * onN f f0 P) := Nat.mul_le_mul_left _ a4
  have a7 : (1 + Sm) * NLv ≤ (1 + Sm) * (Fintype.card FL.Di * onN f f0 P) := Nat.mul_le_mul_left _ a4
  have e1 : (4 + (c1 + 1 + Sm) * Fintype.card FL.Di) * onN f f0 P = 4 * onN f f0 P +
      c1 * (Fintype.card FL.Di * onN f f0 P) + (1 + Sm) * (Fintype.card FL.Di * onN f f0 P) := by ring
  have e2 : isB ch P * (ℓf + 8 * m * lhat) = isB ch P * ℓf + 4 * (isB ch P * (2 * m * lhat)) := by ring
  rw [e1, e2]
  generalize (∑ r' : (sys R FL Pl).R, if (sys R FL Pl).rp r' = Pl.pt P then padR R ch FL Pl lhat n o r' else 0) = pv
    at a2 ⊢
  generalize heldN R FL Pl n o (Pl.pt P) = hv at a1 ⊢
  generalize initN (A' := A') n (Pl.pt P) = iv at a1 a5
  generalize chanN R FL Pl (Pl.pt P) = cv at a1 ⊢
  generalize onN f f0 P = ov at a3 a6 a7 ⊢
  generalize c1 * (Fintype.card FL.Di * ov) = x1 at a6 ⊢
  generalize (1 + Sm) * (Fintype.card FL.Di * ov) = x2 at a7 ⊢
  generalize c1 * NLv = x3 at a1 a6
  generalize (1 + Sm) * NLv = x4 at a2 a7
  generalize isB ch P * ℓf = x5 at a5 ⊢
  generalize isB ch P * (2 * m * lhat) = x6 at a3 ⊢
  omega

end Nc.Tow
