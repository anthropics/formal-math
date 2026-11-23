/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Toolkit
import Nc.Flag.Len

/-!
# Finite groups of isometries of complete CAT(0) spaces: projections to fixed points
-/

open Finset

namespace Nc.Flag

open Cat

/-- An action by isometries. -/
structure IsoAct (G Z : Type*) [Group G] [MetricSpace Z] where
  /-- the action -/
  act : G → Z → Z
  one' : ∀ z, act 1 z = z
  mul' : ∀ g h z, act (g * h) z = act g (act h z)
  iso' : ∀ g z z', dist (act g z) (act g z') = dist z z'

namespace IsoAct
variable {G H Z : Type*} [Group G] [Group H] [MetricSpace Z] (A : IsoAct G Z)

/-- Pull-back along a homomorphism. -/
def comap (φ : H →* G) : IsoAct H Z where
  act g := A.act (φ g)
  one' z := by rw [map_one, A.one']
  mul' g h z := by rw [map_mul, A.mul']
  iso' g := A.iso' _

theorem isometry (g : G) : Isometry (A.act g) := Isometry.of_dist_eq (A.iso' g)

theorem surj (g : G) : Function.Surjective (A.act g) := fun z =>
  ⟨A.act g⁻¹ z, by rw [← A.mul', mul_inv_cancel, A.one']⟩

/-- The displacement of a point. -/
def len (z : Z) : Len G where
  val g := dist z (A.act g z)
  one' := by rw [A.one', dist_self]
  inv' g := by
    rw [← A.iso' g, ← A.mul', mul_inv_cancel, A.one', dist_comm]
  mul' g h := by
    rw [A.mul']
    refine (dist_triangle z (A.act g z) _).trans ?_
    rw [A.iso']

theorem len_val (z : Z) (g : G) : (A.len z).val g = dist z (A.act g z) := rfl

/-- Fixed points. -/
def Fix (z : Z) : Prop := ∀ g, A.act g z = z

section proj
variable [CN Z] [Fintype G]

theorem exists_proj (z : Z) : ∃ b, IsBary (fun _ : G => (1 : ℝ)) (fun g => A.act g z) b := by
  have : Nonempty Z := ⟨z⟩
  exact Paper.lem_toolkit_c_exists _ (fun _ => zero_le_one) _

/-- The projection to the fixed points: the barycentre of the orbit. -/
noncomputable def P (z : Z) : Z := Classical.choose (A.exists_proj z)

theorem P_spec (z : Z) : IsBary (fun _ : G => (1 : ℝ)) (fun g => A.act g z) (A.P z) :=
  Classical.choose_spec (A.exists_proj z)

theorem card_pos' : (0 : ℝ) < ∑ _g : G, (1 : ℝ) := by
  rw [sum_const, card_univ, nsmul_eq_mul, mul_one]
  exact_mod_cast Fintype.card_pos

/-- An isometry that commutes with the action commutes with the projection. -/
theorem P_comm (f : Z → Z) (hf : Isometry f) (hs : Function.Surjective f)
    (hc : ∀ g z, f (A.act g z) = A.act g (f z)) (z : Z) : f (A.P z) = A.P (f z) := by
  have h1 := (A.P_spec z).map hf hs
  simp only [hc] at h1
  exact h1.unique card_pos' (A.P_spec (f z))

theorem P_fix (z : Z) : A.Fix (A.P z) := by
  intro g
  have h1 := (A.P_spec z).map (A.isometry g) (A.surj g)
  have h2 := (A.P_spec z).comp_equiv (Equiv.mulLeft g)
  refine h1.unique card_pos' ?_
  have e : (fun i => A.act g (A.act i z)) = (fun g => A.act g z) ∘ Equiv.mulLeft g :=
    funext fun k => (A.mul' g k z).symm
  rw [e]
  exact h2

end proj
end IsoAct

/-- The arithmetic at the end of the proof of Lemma lem:angle (a quadrangle with two right angles). -/
theorem angle_num {r r' α β Q A c : ℝ} (hr : 0 < r) (hr' : 0 < r') (hα : 0 < α) (hβ : 0 < β)
    (hA1 : r ^ 2 + α ^ 2 ≤ A) (hA2 : r' ^ 2 + β ^ 2 ≤ A)
    (hQ : α ^ 2 + β ^ 2 - 2 * c * (α * β) ≤ Q)
    (hbox : ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      t * (1 - t) * A + s * (1 - s) * Q ≤ (1 - t) * (1 - s) * r ^ 2 + (1 - t) * s * r' ^ 2 +
        t * (1 - s) * α ^ 2 + t * s * β ^ 2) :
    Q ≤ r ^ 2 + r' ^ 2 + 2 * c * (r * r') := by
  set T := r * α + r' * β with hT
  set S := r * β + r' * α with hS
  set N := r * r' + α * β with hN
  have hT0 : 0 < T := by positivity
  have hN0 : 0 < N := by positivity
  set s := r * α / T with hs
  set t := r * r' / N with ht
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hT0, hT]
    have : 0 ≤ r' * β := by positivity
    linarith
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hN0, hN]
    have : 0 ≤ α * β := by positivity
    linarith
  have hb := hbox s t hs0 hs1 ht0 ht1
  have hA : (1 - s) * (r ^ 2 + α ^ 2) + s * (r' ^ 2 + β ^ 2) ≤ A := by
    have h1 := mul_le_mul_of_nonneg_left hA1 (show 0 ≤ 1 - s by linarith)
    have h2 := mul_le_mul_of_nonneg_left hA2 hs0
    linarith
  have hA' := mul_le_mul_of_nonneg_left hA (show 0 ≤ t * (1 - t) from
    mul_nonneg ht0 (by linarith))
  have h1 : s * (1 - s) * Q ≤ (1 - t) ^ 2 * ((1 - s) * r ^ 2 + s * r' ^ 2) +
      t ^ 2 * ((1 - s) * α ^ 2 + s * β ^ 2) := by nlinarith
  have e1 : 1 - s = r' * β / T := by rw [hs, hT]; field_simp; ring
  have e2 : 1 - t = α * β / N := by rw [ht, hN]; field_simp; ring
  have e3 : (1 - s) * r ^ 2 + s * r' ^ 2 = r * r' * S / T := by
    rw [e1, hs, hS]; field_simp
  have e4 : (1 - s) * α ^ 2 + s * β ^ 2 = α * β * S / T := by
    rw [e1, hs, hS]; field_simp; ring
  have e5 : (1 - t) ^ 2 * (r * r' * S / T) + t ^ 2 * (α * β * S / T) =
      (r * r' * (α * β)) * (S / (T * N)) := by
    rw [e2, ht]
    field_simp
    rw [hN]; ring
  have e6 : s * (1 - s) = (r * r' * (α * β)) * (1 / T ^ 2) := by
    rw [e1, hs]; field_simp
  rw [e3, e4, e5, e6, mul_assoc] at h1
  have h2 := le_of_mul_le_mul_left h1 (by positivity)
  have h3 : Q * N ≤ T * S := by
    have h4 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ T ^ 2 * N by positivity)
    have e7 : T ^ 2 * N * (1 / T ^ 2 * Q) = Q * N := by field_simp
    have e8 : T ^ 2 * N * (S / (T * N)) = T * S := by field_simp
    rw [e7, e8] at h4
    exact h4
  have e9 : T * S = α * β * (r ^ 2 + r' ^ 2) + r * r' * (α ^ 2 + β ^ 2) := by
    rw [hT, hS]; ring
  have h4 : r * r' * (α ^ 2 + β ^ 2) ≤ r * r' * (Q + 2 * c * (α * β)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [e9, hN] at h3
  have h5 : (α * β) * Q ≤ (α * β) * (r ^ 2 + r' ^ 2 + 2 * c * (r * r')) := by nlinarith
  exact le_of_mul_le_mul_left h5 (by positivity)

end Nc.Flag
