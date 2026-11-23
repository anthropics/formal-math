/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.Defs
import Nc.Tow.Load

/-!
# Relays, the laws of a tower, monotone enumerations
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

section Relay

variable (F : Type) [CommRing F]

/-- The table of a role of a relay. -/
def relTab (p : Fin 3) (X : {e : Unit // (0 : Fin 3) = p ∨ (2 : Fin 3) = p} → Bool)
    (g : ∀ ν : {ν : Bool // (if ν then (1 : Fin 3) else 0) = p ∨ (if ν then (2 : Fin 3) else 1) = p},
      Fin 1 → Bool) : F :=
  if h0 : p = 0 then if X ⟨(), Or.inl h0.symm⟩ = g ⟨false, by simp [h0]⟩ 0 then 1 else 0
  else if h1 : p = 1 then if g ⟨false, by simp [h1]⟩ 0 = g ⟨true, by simp [h1]⟩ 0 then 1 else 0
  else if h2 : p = 2 then if g ⟨true, by simp [h2]⟩ 0 = X ⟨(), Or.inr h2.symm⟩ then 1 else 0
  else 1

/-- The relay: a bit shared by the roles 0 and 2 is led through the role 1. -/
def relay : Law F where
  Ro := Fin 3
  Sl := Unit
  Cn := Bool
  I := Unit
  a _ := 0
  b _ := 2
  ab _ := by decide
  c ν := if ν then 1 else 0
  d ν := if ν then 2 else 1
  cd ν := by cases ν <;> decide
  lam := 0
  lab _ i := i.elim0
  lab_inj _ _ _ := rfl
  len _ _ := 1
  tab p _ X g := relTab F p X g
  law X := by
    classical
    rw [Fintype.sum_unique]
    have e : (fun g : ∀ _ : Bool, Fin 1 → Bool => ∏ p : Fin 3, relTab F p (fun e => X p e) fun ν => g ν) =
        fun g => if g false 0 = X 0 () ∧ g true 0 = X 0 () ∧ X 0 () = X 2 () then 1 else 0 := by
      funext g
      rw [Fin.prod_univ_three]
      simp only [relTab, Fin.isValue, dite_true, if_true, one_ne_zero, dite_false, reduceDIte]
      have h20 : ¬ (2 : Fin 3) = 0 := by decide
      have h21 : ¬ (2 : Fin 3) = 1 := by decide
      simp only [h20, h21, dite_false]
      have key : ∀ x y u v : Bool, ((if x = u then (1 : F) else 0) * (if u = v then 1 else 0) *
          if v = y then 1 else 0) = if u = x ∧ v = x ∧ x = y then 1 else 0 := by
        intro x y u v
        cases x <;> cases y <;> cases u <;> cases v <;> simp
      exact key _ _ _ _
    rw [show (∑ g : ∀ _ : Bool, Fin 1 → Bool, ∏ p : Fin 3, relTab F p (fun e => X p e) fun ν => g ν) =
      ∑ g : ∀ _ : Bool, Fin 1 → Bool, if g false 0 = X 0 () ∧ g true 0 = X 0 () ∧ X 0 () = X 2 () then (1 : F) else 0 from
        congrArg (fun f => ∑ g, f g) e]
    by_cases h : X 0 () = X 2 ()
    · rw [if_pos fun _ => h, Finset.sum_eq_single fun _ _ => X 0 ()]
      · simp [h]
      · intro g _ hg
        rw [if_neg]
        rintro ⟨h1, h2, -⟩
        apply hg
        funext ν k
        have hk : k = 0 := Subsingleton.elim _ _
        subst hk
        cases ν
        · exact h1
        · exact h2
      · intro hn; exact absurd (mem_univ _) hn
    · rw [if_neg fun hh => h (hh ()), Finset.sum_eq_zero]
      intro g _
      rw [if_neg fun hh => h hh.2.2]
  conn _ _ _ _ := rfl

end Relay

/-- The laws at the vertices of a tower. -/
structure FlagLaws (F : Type) [CommRing F] {h b D J r : ℕ} (T : Tower h b D J r) where
  /-- kinds of laws -/
  Di : Type
  [fD : Fintype Di]
  [dD : DecidableEq Di]
  /-- the laws -/
  L : Di → Law F
  /-- roles are the chambers at a vertex -/
  ro : ∀ d, (L d).Ro ≃ T.Fl
  /-- channels are the near pairs -/
  cn : ∀ d, (L d).Cn ≃ T.Nr
  ends : ∀ d ν, s(ro d ((L d).c ν), ro d ((L d).d ν)) = s(T.cN (cn d ν), T.dN (cn d ν))
  lam_pos : ∀ d, 1 ≤ (L d).lam
  nonempty : ∀ d, Nonempty (L d).I
  /-- the scale -/
  a₁ : ℕ
  a₁_pos : 0 < a₁
  /-- the constant of the contraction -/
  C₁ : ℝ
  C₁_nonneg : 0 ≤ C₁
  /-- its integer form -/
  G₁ : ℕ
  G₁_le : (G₁ : ℝ) ≤ 2 * C₁ * (a₁ : ℝ) ^ 2
  /-- every load is below one of finitely many -/
  L1 : ∀ (n : Sym2 T.Fl → ℕ) (t : ℕ), √(T.NN2 n) ≤ (a₁ : ℝ) * t → ∃ d, ∀ q : Sym2 T.Fl, ¬ q.IsDiag →
    n q ≤ (univ.filter fun e : (L d).Sl => s(ro d ((L d).a e), ro d ((L d).b e)) = q).card * t
  /-- the strings are short -/
  L2 : ∀ d i, r * b * ∑ ν, ((L d).lam + (L d).len i ν) ^ 2 ≤ G₁

attribute [instance] FlagLaws.fD FlagLaws.dD

/-- A monotone enumeration of a finite set. -/
theorem exists_mono_equiv {κ : Type} [Fintype κ] (time : κ → ℕ) :
    ∃ e : Fin (Fintype.card κ) ≃ κ, ∀ x y, time x < time y → e.symm x < e.symm y := by
  classical
  let e0 := (Fintype.equivFin κ).symm
  let σ := Tuple.sort (time ∘ e0)
  refine ⟨σ.trans e0, fun x y hxy => ?_⟩
  have hm : Monotone ((time ∘ e0) ∘ σ) := Tuple.monotone_sort _
  by_contra hn
  have h1 := hm (not_lt.1 hn)
  simp only [Function.comp_apply] at h1
  have h2 : ∀ z, e0 (σ ((σ.trans e0).symm z)) = z := fun z => (σ.trans e0).apply_symm_apply z
  rw [h2, h2] at h1
  omega

end Nc.Tow
