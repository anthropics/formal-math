/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tower.Grp

/-!
# The layers 1 + s^{n+1} A
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Matrix Finset

variable {h n : ℕ} [NeZero h]

/-- Reduction of the groups. -/
noncomputable def redG : G h (n + 1) →* G h n := Matrix.SpecialLinearGroup.map (red (n + 1))

theorem redG_apply (g : G h (n + 1)) (a b : Fin h) : (redG g).1 a b = red (n + 1) (g.1 a b) := rfl

theorem s_sq (n : ℕ) : (s (n + 2) ^ (n + 1)) ^ 2 = 0 := by
  rw [← pow_mul]
  exact s_pow_ge (by omega)

/-- The matrix 1 + s^{n+1} A. -/
noncomputable def layMat (n : ℕ) (A : Matrix (Fin h) (Fin h) (ZMod 2)) : Matrix (Fin h) (Fin h) (R (n + 2)) :=
  1 + s (n + 2) ^ (n + 1) • A.map (cst (n + 2))

theorem det_layMat (A : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (layMat n A).det = 1 + cst (n + 2) A.trace * s (n + 2) ^ (n + 1) := by
  rw [layMat, Matrix.det_one_add_smul, s_sq, mul_zero, add_zero]
  congr 2
  simp [Matrix.trace, map_sum]

theorem layMat_mul (A B : Matrix (Fin h) (Fin h) (ZMod 2)) : layMat n A * layMat n B = layMat n (A + B) := by
  have h1 : s (n + 2) ^ (n + 1) * s (n + 2) ^ (n + 1) = 0 := by rw [← sq, s_sq]
  rw [layMat, layMat, layMat, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, h1,
    zero_smul, add_zero, Matrix.map_add _ (map_add _), smul_add]
  abel

/-- The element 1 + s^{n+1} A. -/
noncomputable def lay (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) : G h (n + 1) :=
  ⟨layMat n A, by rw [det_layMat, hA, map_zero, zero_mul, add_zero]⟩

theorem lay_val (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) : (lay (n := n) A hA).1 = layMat n A := rfl

theorem lay_mul (A B : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) (hB : B.trace = 0) :
    lay (n := n) A hA * lay B hB = lay (A + B) (by rw [trace_add, hA, hB, add_zero]) :=
  Subtype.ext (layMat_mul A B)

theorem layMat_injective : Function.Injective (layMat (h := h) n) := by
  intro A B e
  ext a b
  have h1 := congrFun (congrFun e a) b
  simp only [layMat, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h1
  have h2 := add_left_cancel h1
  have key : ∀ x : ZMod 2, s (n + 2) ^ (n + 1) * cst (n + 2) x = 0 → x = 0 := by
    intro x hx
    fin_cases x
    · rfl
    · exfalso
      have : cst (n + 2) 1 = 1 := map_one _
      change s (n + 2) ^ (n + 1) * cst (n + 2) 1 = 0 at hx
      rw [this, mul_one] at hx
      exact s_pow_ne (by omega) hx
  have h3 := key (A a b - B a b) (by rw [map_sub, mul_sub, h2, sub_self])
  exact sub_eq_zero.1 h3

theorem red_s_pow (n : ℕ) : red (n + 1) (s (n + 2) ^ (n + 1)) = 0 := by
  rw [map_pow, red_s]
  exact s_pow_self _

theorem redG_lay (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) : redG (lay (n := n) A hA) = 1 := by
  refine Subtype.ext ?_
  ext a b
  rw [redG_apply, lay_val, layMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, red_s_pow,
    zero_mul, add_zero]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.one_apply_ne hab, map_zero]
    exact (Matrix.one_apply_ne hab).symm

/-- The kernel of the reduction is the layer. -/
theorem exists_lay {g : G h (n + 1)} (hg : redG g = 1) : ∃ A hA, g = lay A hA := by
  have h1 : ∀ a b, ∃ c : ZMod 2, g.1 a b = (1 : Matrix (Fin h) (Fin h) (R (n + 2))) a b +
      s (n + 2) ^ (n + 1) * cst (n + 2) c := by
    intro a b
    have h2 : red (n + 1) (g.1 a b - (1 : Matrix (Fin h) (Fin h) (R (n + 2))) a b) = 0 := by
      rw [map_sub, ← redG_apply, hg]
      by_cases hab : a = b
      · subst hab
        simp
      · rw [Matrix.one_apply_ne hab, map_zero, sub_zero]
        exact Matrix.one_apply_ne hab
    obtain ⟨c, hc⟩ := exists_of_red_eq_zero h2
    refine ⟨c, ?_⟩
    rw [mul_comm, ← hc]
    abel
  choose A hA using h1
  have e : g.1 = layMat n (Matrix.of A) := by
    ext a b
    rw [hA, layMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  have htr : (Matrix.of A).trace = 0 := by
    have h2 := g.2
    rw [e, det_layMat] at h2
    have h3 : cst (n + 2) (Matrix.of A).trace * s (n + 2) ^ (n + 1) = 0 := by
      have := congrArg (fun x => x - 1) h2
      simpa using this
    by_contra hne
    have h4 : (Matrix.of A).trace = 1 := by
      generalize (Matrix.of A).trace = x at hne
      fin_cases x
      · exact absurd rfl hne
      · rfl
    rw [h4, map_one, one_mul] at h3
    exact s_pow_ne (by omega) h3
  exact ⟨Matrix.of A, htr, Subtype.ext e⟩

/-- The reduction is onto. -/
theorem redG_surjective : Function.Surjective (redG : G h (n + 1) →* G h n) := by
  intro g
  choose f hf using red_surjective (n + 1)
  let A : Matrix (Fin h) (Fin h) (R (n + 2)) := g.1.map f
  have hA : A.map (red (n + 1)) = g.1 := by
    ext a b
    simp [A, hf]
  have hd : red (n + 1) A.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, g.2]
  have hdd : A.det * A.det = 1 := by
    obtain ⟨c, hc⟩ := exists_of_red_eq_zero (m := n + 1) (x := A.det - 1) (by rw [map_sub, hd, map_one, sub_self])
    have h1 : A.det = 1 + cst (n + 2) c * s (n + 2) ^ (n + 1) := by rw [← hc]; ring
    have h2 := s_sq n
    have h3 := two_eq_zero (n + 2)
    rw [h1]
    linear_combination (cst (n + 2) c) ^ 2 * h2 +
      (cst (n + 2) c * s (n + 2) ^ (n + 1)) * h3
  let i0 : Fin h := 0
  let B : Matrix (Fin h) (Fin h) (R (n + 2)) := A.updateRow i0 (A.det • A i0)
  have hB : B.det = 1 := by
    rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, hdd]
  refine ⟨(⟨B, hB⟩ : G h (n + 1)), Subtype.ext ?_⟩
  ext a b
  refine (redG_apply (⟨B, hB⟩ : G h (n + 1)) a b).trans ?_
  have h4 : red (n + 1) (A a b) = g.1 a b := congrFun (congrFun hA a) b
  by_cases ha : a = i0
  · subst ha
    simp only [B, Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul, map_mul, hd, one_mul, h4]
  · simp only [B, Matrix.updateRow_ne ha, h4]

/-- The trace-zero matrices. -/
def tr0 (h : ℕ) : AddSubgroup (Matrix (Fin h) (Fin h) (ZMod 2)) := (Matrix.traceAddMonoidHom (Fin h) (ZMod 2)).ker

theorem card_tr0 : Nat.card (tr0 h) = 2 ^ (h ^ 2 - 1) := by
  have h1 := AddSubgroup.card_mul_index (tr0 h)
  have h2 : (tr0 h).index = 2 := by
    rw [tr0, AddSubgroup.index_ker]
    have : (Matrix.traceAddMonoidHom (Fin h) (ZMod 2)).range = ⊤ := by
      rw [AddMonoidHom.range_eq_top]
      intro c
      refine ⟨Matrix.single 0 0 c, ?_⟩
      simp
    rw [this, AddSubgroup.card_top, Nat.card_zmod]
  have h3 : Nat.card (Matrix (Fin h) (Fin h) (ZMod 2)) = 2 ^ (h ^ 2) := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Fin h → Fin h → ZMod 2) = _
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    rw [← pow_mul, sq]
  rw [h2, h3] at h1
  have hpos : 1 ≤ h ^ 2 := Nat.one_le_pow _ _ (NeZero.pos h)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hpos
  rw [hk, pow_add, pow_one] at h1
  rw [hk, Nat.add_sub_cancel_left]
  omega

theorem card_ker_redG : Nat.card (redG : G h (n + 1) →* G h n).ker = 2 ^ (h ^ 2 - 1) := by
  rw [← card_tr0]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun A : tr0 h => ⟨lay A.1 A.2, redG_lay A.1 A.2⟩) ⟨?_, ?_⟩)
  · intro A B e
    have := congrArg (fun g : (redG : G h (n + 1) →* G h n).ker => g.1.1) e
    exact Subtype.ext (layMat_injective this)
  · rintro ⟨g, hg⟩
    obtain ⟨A, hA, rfl⟩ := exists_lay hg
    exact ⟨⟨A, hA⟩, rfl⟩

theorem card_G_succ : Nat.card (G h (n + 1)) = Nat.card (G h n) * 2 ^ (h ^ 2 - 1) := by
  have h1 := Subgroup.card_mul_index (redG : G h (n + 1) →* G h n).ker
  rw [card_ker_redG, Subgroup.index_ker, MonoidHom.range_eq_top.2 redG_surjective, Subgroup.card_top] at h1
  rw [← h1, mul_comm]

theorem evG_bijective_zero : Function.Bijective (evG : G h 0 →* SL2 h) := by
  constructor
  · intro g g' e
    refine Subtype.ext ?_
    ext a b
    rw [eq_cst_ev (g.1 a b), eq_cst_ev (g'.1 a b)]
    congr 1
    exact congrFun (congrFun (congrArg Subtype.val e) a) b
  · intro A
    refine ⟨th0 0 A, Subtype.ext ?_⟩
    ext a b
    rw [evG_th0, sub_zero, sub_zero]

theorem evG_surjective : Function.Surjective (evG : G h n →* SL2 h) := by
  intro A
  refine ⟨th0 0 A, Subtype.ext ?_⟩
  ext a b
  rw [evG_th0, sub_zero, sub_zero]

/-- The order of the group. -/
theorem card_G (h n : ℕ) [NeZero h] : Nat.card (G h n) = Nat.card (SL2 h) * 2 ^ ((h ^ 2 - 1) * n) := by
  induction n with
  | zero =>
    rw [mul_zero, pow_zero, mul_one]
    exact Nat.card_congr (Equiv.ofBijective _ evG_bijective_zero)
  | succ n ih => rw [card_G_succ, ih, mul_assoc, ← pow_add, mul_add, mul_one]

/-- The kernel of the value at s = 0 is a 2-group. -/
theorem card_ker_evG : Nat.card (evG : G h n →* SL2 h).ker = 2 ^ ((h ^ 2 - 1) * n) := by
  have h1 := Subgroup.card_mul_index (evG : G h n →* SL2 h).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 evG_surjective, Subgroup.card_top, card_G, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

end Nc.Tower
