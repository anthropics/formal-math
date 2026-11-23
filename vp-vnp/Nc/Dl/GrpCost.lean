/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Num0
import Nc.Dl.Inst
import Nc.Grp.GrpTime
import Nc.Grp.GroupThm

/-!
# The time of the evaluator; bits and numbers of names
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

/-- The time of GROUP. -/
def GrpTimeOK (A : Type) [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
    [DecidableEq Q] {c : ℕ} (cb : Option Γ → Fin c → Bool) (qn : Q → ℕ) : Prop :=
  ∀ {K A' E U0 U1 cap mm : ℕ} {M : Sys A (K + K + A') E} (P : G.Plan M U0 U1) (_ : P.Ok cap) (q : Fin (K + 1) → Q)
    (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
    (grp : Fin (K + K + A') → Fin mm) (g : Fin mm) (key : Grp.Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.R → ℕ) (bT bub : List Bool)
    (b : G.Uid (K + K) U0 M.N U1 → UW (Grp.bval bub)) {Lc X ιb lh ev : ℕ},
    (∀ κ, (x κ).length ≤ Grp.bval bT) → (∀ a, (key a).length ≤ Lc) → (∀ a, (dkey a).length ≤ Lc) → bT.length ≤ Lc →
    bub.length ≤ Lc → Fintype.card (Option S) ≤ X → K + K + 1 ≤ X → Fintype.card M.R ≤ X →
    Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X → (∀ y, Fintype.card (M.kind y).Sl ≤ X) →
    (∀ y, Fintype.card (M.kind y).Cn ≤ X) →
    (univ.filter fun p : Fin (K + K) => grp (Fin.castAdd A' p) = g).card ≤ ιb → ιb ≤ X →
    (∀ p : Fin (K + K), grp (Fin.castAdd A' p) = g → ∑ b, ((n p b).val + (n b p).val) ≤ lh) →
    evG (fun _ _ => grp) n o g + pdG P (fun _ _ => grp) n o g ≤ ev →
    grpT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b) ≤
      2 * (Lc + 1) * (Grp.bval bT + Grp.bval bub + 2) + ιb * Grp.bval bT +
      1000 * (ev + ιb * lh) * (Grp.bval bub + Lc + 1) + X ^ 4 * 1000 * (Lc + 1)


section Bits

theorem bval_append (l : List Bool) (b : Bool) : Grp.bval (l ++ [b]) = 2 * Grp.bval l + b.toNat := by
  simp [Grp.bval]

theorem bval_reverse (w : List Bool) : Grp.bval w.reverse = KT.val w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [List.reverse_cons, bval_append, ih, KT.val]
    cases b <;> simp <;> omega

theorem exists_bits (n : ℕ) {L : ℕ} (h : n < 2 ^ L) : (bitsN L n).length = L ∧ KT.val (bitsN L n) = n ∧
    (bitsN L n).reverse.length = L ∧ Grp.bval (bitsN L n).reverse = n :=
  ⟨length_bitsN L n, val_bitsN L n h, by rw [List.length_reverse, length_bitsN], by rw [bval_reverse, val_bitsN L n h]⟩

end Bits

section Cards

theorem card_uid_le {A0 U0 U1 : ℕ} {N : Type} [Fintype N] [DecidableEq N] :
    Fintype.card (G.Uid A0 U0 N U1) ≤ A0 * A0 * U0 + Fintype.card N * U1 := by
  let f : G.Uid A0 U0 N U1 → (Fin A0 × Fin A0 × Fin U0) ⊕ (N × Fin U1) := fun id => match id with
    | .init a b k => .inl (a, b, k)
    | .new ν k => .inr (ν, k)
  have hf : Function.Injective f := by
    intro x y h
    cases x <;> cases y <;> simp only [f, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq] at h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
    · obtain ⟨rfl, rfl⟩ := h
      rfl
  have h := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h
  calc _ ≤ _ := h
    _ = _ := by ring

theorem card_row (A0 : ℕ) : Fintype.card (RowData A0) = 2 * (A0 * A0) := by
  simp [RowData, Fintype.card_prod]

set_option maxHeartbeats 4000000 in
theorem card_nm {K E pS : ℕ} {S N Id : Type} [Fintype S] [Fintype N] [Fintype Id] {X : ℕ} (h1 : K + K + 1 ≤ X)
    (h2 : Fintype.card (Option S) ≤ X) (h3 : Fintype.card N ≤ X) (h4 : pS ≤ X) (h5 : E + 1 ≤ X) (h6 : Fintype.card Id ≤ X) :
    Fintype.card (Nm K E pS S N Id) ≤ 30 * (X * X) := by
  have hX : 1 ≤ X := by omega
  have e := Fintype.card_congr (nmEquiv (K := K) (E := E) (pS := pS) (S := S) (N := N) (Id := Id))
  rw [← e]
  have a1 : Fintype.card (Option S) * (K + K) ≤ X * X := Nat.mul_le_mul h2 (by omega)
  have a2 : (K + K) * (K + K) ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  have a3 : X ≤ X * X := Nat.le_mul_of_pos_left _ hX
  have a4 : Fintype.card (Option (Fin E)) = E + 1 := by rw [Fintype.card_option, Fintype.card_fin]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit, Fintype.card_bool, a4]
  omega

end Cards

section Time

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {c : ℕ}

/-- The time of GROUP. -/
theorem grpTimeOK (cb : Option Γ → Fin c → Bool) (qn : Q → ℕ) : GrpTimeOK (S := S) A cb qn := by
  classical
  intro K A' E U0 U1 cap mm M P hP q x ρ n o grp g key dkey tg bT bub b Lc X ιb lh ev hx hk hd hbT hbub hS hK hR hId hSl hCn hι
    hιX hlh hev
  have e1 : Grp.evG n o grp g = evG (fun _ _ => grp) n o g := by
    unfold Grp.evG evG
    refine Finset.sum_congr ?_ fun p _ => ?_
    · ext p; simp
    · first | rfl | congr 1
  have e2 : Grp.pdG P n o grp g = pdG P (fun _ _ => grp) n o g := by
    unfold Grp.pdG pdG
    refine Finset.sum_congr ?_ fun p _ => rfl
    ext p; simp
  have hbase : (Grp.baseList (A' := A') grp g).length ≤ ιb := by
    refine le_trans (le_of_eq ?_) hι
    unfold Grp.baseList
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
    congr 1
    ext p
    simp
  have h := Grp.script_time_le (qn := qn) (cb := cb) (q := q) (x := x) (ρ := ρ) (n := n) (o := o) (grp := grp) (g := g)
    (key := key) (dkey := dkey) (tg := tg) (Lc := Lc) (X := X) (ιb := ιb) (lh := lh) (ev := evG (fun _ _ => grp) n o g)
    (pd := pdG P (fun _ _ => grp) n o g) (bT := bT) (bub := bub) rfl rfl hbT hbub hP hx hk hd hS (by omega) hR
    (fun r => (Fintype.card_subtype_le _).trans (hSl _)) (fun r => (Fintype.card_subtype_le _).trans (hCn _)) hbase hιX hlh
    e1.le e2.le b
  have hX1 : 1 ≤ X := by omega
  have h3 : X ^ 3 ≤ X ^ 4 := Nat.pow_le_pow_right hX1 (by norm_num)
  have h4 : (evG (fun _ _ => grp) n o g + pdG P (fun _ _ => grp) n o g + ιb * lh) * (1000 * (Grp.bval bub + Lc + 1)) ≤
      1000 * (ev + ιb * lh) * (Grp.bval bub + Lc + 1) := by
    calc _ ≤ (ev + ιb * lh) * (1000 * (Grp.bval bub + Lc + 1)) := Nat.mul_le_mul_right _ (Nat.add_le_add_right hev _)
      _ = _ := by ring
  have h5 : 1000 * X ^ 3 ≤ X ^ 4 * 1000 * (Lc + 1) := by
    calc 1000 * X ^ 3 ≤ 1000 * X ^ 4 := Nat.mul_le_mul_left _ h3
      _ = X ^ 4 * 1000 * 1 := by ring
      _ ≤ X ^ 4 * 1000 * (Lc + 1) := Nat.mul_le_mul_left _ (by omega)
  unfold grpT
  omega

end Time

end Nc.Dl
