/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Prices

/-!
# Lemmas for the crossing inequality

For Paper.prop_crossing (Paper/Crossing.lean): tensors with four legs, the two wires among them, and the compact set of the
pairs (r, l).
-/

namespace Nc.Price

open Ov Ov.Ten Finset

/-- `f` is a sum of `r` products of a function of the first two indices and one of the last two. -/
def SplitAB {K : Type} [Field K] {α β : Type} (f : α → β → α → β → K) (r : ℕ) : Prop :=
  ∃ g h : Fin r → α × β → K, ∀ a b c d, f a b c d = ∑ k, g k (a, b) * h k (c, d)

/-- `f` is a sum of `r` products of a function of the first and the last index and one of the two in the middle. -/
def SplitAD {K : Type} [Field K] {α β : Type} (f : α → β → α → β → K) (r : ℕ) : Prop :=
  ∃ (g : Fin r → α × β → K) (h : Fin r → β × α → K), ∀ a b c d, f a b c d = ∑ k, g k (a, d) * h k (b, c)

section Four

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]
variable {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β]
  [Nonempty β]

/-- A tensor with four legs, of sizes |α|, |β|, |α|, |β|. -/
def four (f : α → β → α → β → K) : Ten K (Fin 4) where
  ι q := match q with
    | 0 => α
    | 1 => β
    | 2 => α
    | 3 => β
  fin q := match q with
    | 0 => inferInstanceAs (Fintype α)
    | 1 => inferInstanceAs (Fintype β)
    | 2 => inferInstanceAs (Fintype α)
    | 3 => inferInstanceAs (Fintype β)
  dec q := match q with
    | 0 => inferInstanceAs (DecidableEq α)
    | 1 => inferInstanceAs (DecidableEq β)
    | 2 => inferInstanceAs (DecidableEq α)
    | 3 => inferInstanceAs (DecidableEq β)
  val x := f (x 0) (x 1) (x 2) (x 3)

variable (F : Spec K I)

/-- The two wires between x and v and between y and u. -/
theorem le_F_cross (x y v u : I) :
    (Fintype.card α : ℝ) ^ F.e x v * (Fintype.card β : ℝ) ^ F.e y u ≤
      F.F (Ten.push ![x, y, v, u]
        (four fun (a : α) (b : β) c d => if a = c ∧ b = d then (1 : K) else 0)) := by
  classical
  set D := Fintype.card α with hD
  set D' := Fintype.card β with hD'
  rw [← F.wire_eq x v (n := D) Fintype.card_pos, ← F.wire_eq y u (n := D') Fintype.card_pos,
    ← F.mul]
  refine F.mono ?_
  let e : Fin D ≃ α := (Fintype.equivFin α).symm
  let e' : Fin D' ≃ β := (Fintype.equivFin β).symm
  let σ : Fin 2 ⊕ Fin 2 → Fin 4 := Sum.elim ![0, 2] ![1, 3]
  let t : Ten K (Fin 2 ⊕ Fin 2) := outer₂ (unit K (Fin 2) D) (unit K (Fin 2) D')
  have h1 : (Sum.elim ![x, v] ![y, u] : Fin 2 ⊕ Fin 2 → I) = ![x, y, v, u] ∘ σ := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  have h2 := (Equi.push_outer₂ (Sum.elim ![x, v] ![y, u]) (unit K (Fin 2) D) (unit K (Fin 2) D')).2
  refine Restr.trans h2 ?_
  rw [h1]
  refine (Equi.push_push ![x, y, v, u] σ t).2.trans (Restr.push _ ?_)
  refine Restr.of_map' (fun q => match q with
    | 0 => fun a => e (a ⟨Sum.inl 0, rfl⟩)
    | 1 => fun a => e' (a ⟨Sum.inr 0, rfl⟩)
    | 2 => fun a => e (a ⟨Sum.inl 1, rfl⟩)
    | 3 => fun a => e' (a ⟨Sum.inr 1, rfl⟩)) fun z => ?_
  have gen : ∀ (a0 a2 : Fin D) (a1 a3 : Fin D'),
      (if a0 = a2 then (1 : K) else 0) * (if a1 = a3 then 1 else 0) =
        if e a0 = e a2 ∧ e' a1 = e' a3 then 1 else 0 := by
    intro a0 a2 a1 a3
    simp only [e.injective.eq_iff, e'.injective.eq_iff]
    rw [ite_and, ite_mul, one_mul, zero_mul]
  exact (congr_arg₂ (· * ·) (unit_two_val fun l => z (σ (Sum.inl l)) ⟨Sum.inl l, rfl⟩)
    (unit_two_val fun l => z (σ (Sum.inr l)) ⟨Sum.inr l, rfl⟩)).trans (gen _ _ _ _)

end Four

theorem rpow_le_exp (r : ℕ) (z : ℝ) : (r : ℝ) ^ z ≤ Real.exp (Real.log r * z) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [Nat.cast_zero, Real.log_zero, zero_mul, Real.exp_zero]
    exact Real.zero_rpow_le_one z
  · rw [Real.rpow_def_of_pos (by exact_mod_cast hr)]

/-- The quarter disc of radius √ρ. -/
def quarter (ρ : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ ρ}

theorem isCompact_quarter (ρ : ℝ) : IsCompact (quarter ρ) := by
  have h1 : IsCompact (Set.Icc (0 : ℝ) (ρ + 1) ×ˢ Set.Icc (0 : ℝ) (ρ + 1)) :=
    isCompact_Icc.prod isCompact_Icc
  refine h1.of_isClosed_subset ?_ ?_
  · have h2 : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} := isClosed_le continuous_const continuous_fst
    have h3 : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := isClosed_le continuous_const continuous_snd
    have h4 : IsClosed {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ ρ} :=
      isClosed_le (by fun_prop) continuous_const
    exact h2.inter (h3.inter h4)
  · rintro ⟨r, l⟩ ⟨hr, hl, h⟩
    simp only at hr hl h
    refine ⟨⟨hr, ?_⟩, ⟨hl, ?_⟩⟩ <;> nlinarith [sq_nonneg (r - 1), sq_nonneg (l - 1)]

/-- If X ≤ min(A + r·s, B + l·t) + δ for all δ > 0 with some (r, l) in the quarter disc, then also for
δ = 0. -/
theorem exists_quarter {ρ X A B s t : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ δ : ℝ, 0 < δ → ∃ p ∈ quarter ρ, X ≤ min (A + p.1 * s) (B + p.2 * t) + δ) :
    ∃ p ∈ quarter ρ, X ≤ min (A + p.1 * s) (B + p.2 * t) := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_quarter ρ).exists_isMaxOn
    (f := fun p : ℝ × ℝ => min (A + p.1 * s) (B + p.2 * t))
    ⟨(0, 0), le_rfl, le_rfl, by simpa using hρ⟩ (by fun_prop)
  refine ⟨p, hp, le_of_forall_pos_le_add fun δ hδ => ?_⟩
  obtain ⟨p', hp', h'⟩ := h δ hδ
  have hm : min (A + p'.1 * s) (B + p'.2 * t) ≤ min (A + p.1 * s) (B + p.2 * t) := hmax hp'
  linarith

end Nc.Price
