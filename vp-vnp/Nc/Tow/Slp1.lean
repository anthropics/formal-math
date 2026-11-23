/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Slp0
import Nc.Tow.Plan
import Nc.Tow.Load3

/-!
# The program of the tower plan: bounds, loads from numbers of units
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r}

/-- Targets as a sum. -/
def tgEquiv (T : Tower h b D J r) (m AA : ℕ) : Tg T m AA ≃ Unit ⊕ ((Σ j : Fin (J + 1), T.Ed j) ⊕
    (RM T m AA ⊕ (Σ j : Fin J, Σ i : Fin h, T.V (j + 1) i × Sym2 T.Fl))) where
  toFun
    | .done => .inl ()
    | .edge j e => .inr (.inl ⟨j, e⟩)
    | .nxt x => .inr (.inr (.inl x))
    | .seg j i ω q => .inr (.inr (.inr ⟨j, i, ω, q⟩))
  invFun
    | .inl _ => .done
    | .inr (.inl x) => .edge x.1 x.2
    | .inr (.inr (.inl x)) => .nxt x
    | .inr (.inr (.inr x)) => .seg x.1 x.2.1 x.2.2.1 x.2.2.2
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | _ | _ <;> rfl

instance (T : Tower h b D J r) (m AA : ℕ) : Fintype (Tg T m AA) := Fintype.ofEquiv _ (tgEquiv T m AA).symm

variable (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T)

/-- A bound for all loads. -/
noncomputable def Wb (U0 U1 : ℕ) : ℕ := AA * AA * U0 + Fintype.card (NM R FL (ch := ch)) * U1

/-- Bounds for the program. -/
structure Bnd (U0 U1 Y : ℕ) : Prop where
  aa : AA * AA ≤ Y
  w : Wb R ch FL U0 U1 ≤ Y
  nm : Fintype.card (NM R FL (ch := ch)) ≤ Y
  mv : Fintype.card (Mv T R ch FL) ≤ Y
  tg : Fintype.card (Tg T m AA) ≤ Y
  nd : Fintype.card (Nd T) ≤ Y
  fl : Fintype.card (Sym2 T.Fl) ≤ Y
  di : Fintype.card FL.Di ≤ Y
  h : h ≤ Y
  j : J + 1 ≤ Y
  t : tend J m ≤ Y
  tt : b * Fintype.card (Sym2 T.Fl) * Wb R ch FL U0 U1 + 2 ≤ Y

variable {R ch FL}

namespace Bnd

variable {Y : ℕ} (hB : Bnd R ch FL U0 U1 Y)
include hB

theorem u0 (a : Fin AA) : U0 ≤ Y := by
  have h1 := hB.w
  unfold Wb at h1
  have h2 : 0 < AA * AA := Nat.mul_pos (Fin.pos a) (Fin.pos a)
  have h3 : U0 ≤ AA * AA * U0 := Nat.le_mul_of_pos_left _ h2
  omega

theorem u1 (ν : NM R FL (ch := ch)) : U1 ≤ Y := by
  have h1 := hB.w
  unfold Wb at h1
  have h2 : 0 < Fintype.card (NM R FL (ch := ch)) := Fintype.card_pos_iff.2 ⟨ν⟩
  have h3 : U1 ≤ Fintype.card (NM R FL (ch := ch)) * U1 := Nat.le_mul_of_pos_left _ h2
  omega

theorem aa1 : AA ≤ Y := by
  have h1 := hB.aa
  rcases Nat.eq_zero_or_pos AA with h0 | h0
  · omega
  · exact (Nat.le_mul_of_pos_left _ h0).trans h1

theorem ed (j : Fin (J + 1)) : Fintype.card (T.Ed j) ≤ Y := by
  refine (Fintype.card_le_of_injective (fun e : T.Ed j => (Tg.edge j e : Tg T m AA)) ?_).trans hB.tg
  intro e e' he
  injection he

end Bnd

section Bounds

variable {lhat : ℕ} {n : Fin AA → Fin AA → ℕ} {o : NM R FL (ch := ch) → ℕ}

theorem bt_le (hn : ∀ a c, n a c ≤ U0) (τ : Tg T m AA) : bt R ch lhat n τ ≤ AA * AA * U0 := by
  unfold bt
  split_ifs
  · calc _ ≤ ∑ _a : Fin AA, ∑ _c : Fin AA, U0 := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => ?_
          refine (card_filter_le _ _).trans ?_
          rw [card_range]
          exact hn a c
      _ = AA * AA * U0 := by simp; ring
  · exact Nat.zero_le _

theorem ld_le (hn : ∀ a c, n a c ≤ U0) (ho : ∀ ν, o ν ≤ U1) (N : Mv T R ch FL → ℕ) (τ : Tg T m AA) :
    ld R ch FL lhat n o N τ ≤ Wb R ch FL U0 U1 := by
  unfold ld Wb
  refine add_le_add (bt_le hn τ) ?_
  refine (Finset.sum_le_card_nsmul _ _ U1 fun ν _ => ?_).trans (by simp)
  split_ifs
  · exact (alvN_le _ _).trans (ho ν)
  · exact Nat.zero_le _

theorem fits_mono {L : Tg T m AA → ℕ} {l : LMv T FL} {s t : ℕ} (hst : s ≤ t) (hs : Fits FL L l s) :
    Fits FL L l t := fun q hq => (hs q hq).trans (Nat.mul_le_mul_left _ hst)

/-- The number of units at a vertex is not large. -/
theorem tmin_lt (hb : 0 < b) {L : Tg T m AA → ℕ} (hL : ∀ τ, L τ ≤ Wb R ch FL U0 U1) (l : LMv T FL) :
    tmin FL L l < b * Fintype.card (Sym2 T.Fl) * Wb R ch FL U0 U1 + 2 := by
  set w := Wb R ch FL U0 U1 with hw
  set s := Fintype.card (Sym2 T.Fl) with hs
  have h1 := tmin_le hb L l (n' := fun _ => w) fun q => hL _
  have hN : T.NN2 (fun _ => w) ≤ ((b * s * w : ℕ) : ℝ) ^ 2 := by
    unfold Tower.NN2
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have e1 : (∑ q : Sym2 T.Fl, if q.IsDiag then (0 : ℝ) else ((w : ℕ) : ℝ) ^ 2) ≤ s * (w : ℝ) ^ 2 := by
      refine (Finset.sum_le_card_nsmul _ _ ((w : ℝ) ^ 2) fun q _ => ?_).trans (by simp [hs])
      split_ifs
      · positivity
      · exact le_rfl
    have e2 : ((b : ℝ) * (b - 1) / 2) ≤ (b : ℝ) ^ 2 := by nlinarith
    have e3 : (0 : ℝ) ≤ (b : ℝ) * (b - 1) / 2 := by
      have : (0 : ℝ) ≤ b - 1 := by linarith
      positivity
    have e4 : (s : ℝ) ≤ (s : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · rw [h0]; simp
      · have : (1 : ℝ) ≤ s := by exact_mod_cast h0
        nlinarith
    calc _ ≤ ((b : ℝ) * (b - 1) / 2) * (s * (w : ℝ) ^ 2) := mul_le_mul_of_nonneg_left e1 e3
      _ ≤ (b : ℝ) ^ 2 * ((s : ℝ) ^ 2 * (w : ℝ) ^ 2) := by
          refine mul_le_mul e2 (mul_le_mul_of_nonneg_right e4 (by positivity)) (by positivity) (by positivity)
      _ = _ := by push_cast; ring
  have h2 : √(T.NN2 fun _ => w) ≤ ((b * s * w : ℕ) : ℝ) := by
    rw [show ((b * s * w : ℕ) : ℝ) = √(((b * s * w : ℕ) : ℝ) ^ 2) from (Real.sqrt_sq (Nat.cast_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hN
  have ha : (1 : ℝ) ≤ FL.a₁ := by exact_mod_cast FL.a₁_pos
  have h3 : (tmin FL L l : ℝ) ≤ (b * s * w : ℕ) + 1 := by
    by_contra hcon
    push Not at hcon
    have h4 : (FL.a₁ : ℝ) * ((b * s * w : ℕ) + 1) < FL.a₁ * tmin FL L l :=
      mul_lt_mul_of_pos_left hcon (by linarith)
    have h5 : ((b * s * w : ℕ) : ℝ) ≤ FL.a₁ * (b * s * w : ℕ) :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) ha
    nlinarith
  have h4 : tmin FL L l ≤ b * s * w + 1 := by exact_mod_cast h3
  omega

/-- The number of units at a vertex, as a sum. -/
theorem tmin_sum {L : Tg T m AA → ℕ} {l : LMv T FL} {B : ℕ} (hlt : tmin FL L l < B) :
    tmin FL L l = ∑ s ∈ range B, ind (fun _ : Unit => ¬ ∃ d, Fits FL L (withD FL l d) s) () := by
  classical
  have h1 : ∀ s, (ind (fun _ : Unit => ¬ ∃ d, Fits FL L (withD FL l d) s) ()) = if s < tmin FL L l then 1 else 0 := by
    intro s
    by_cases hs : s < tmin FL L l
    · rw [if_pos hs, ind_true]
      intro hd
      have h3 : tmin FL L l ≤ s := Nat.sInf_le hd
      omega
    · rw [if_neg hs, ind_false]
      intro hn
      obtain ⟨d, hd⟩ := tmin_spec L l
      exact hn ⟨d, fits_mono (not_lt.1 hs) hd⟩
  rw [Finset.sum_congr rfl fun s _ => h1 s, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have h2 : (range B).filter (fun s => s < tmin FL L l) = range (tmin FL L l) := by
    ext s
    simp only [mem_filter, mem_range]
    omega
  rw [h2, card_range]

end Bounds

end Nc.Tow
