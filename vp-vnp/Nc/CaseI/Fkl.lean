/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.CaseI.Multi
import Nc.Final.CClasses

/-!
# The polynomials of complete networks

f_{k,ℓ} = Σ_σ ∏_a x_{a, σ|a}, the sum over all σ that give a string of ℓ bits to every pair of [k]. A table a
has variables x_{a,t}, t : [k] → strings (with t a = 0 for the variables that occur).
-/

namespace Nc.CaseI

open Finset MvPolynomial

/-- The pairs. -/
abbrev Pr (k : ℕ) := {e : Fin k × Fin k // e.1 < e.2}

/-- The strings at a table. -/
abbrev Ix (k ℓ : ℕ) := Fin k → Fin ℓ → Bool

variable {k ℓ : ℕ}

/-- Every end of a pair has a string; the strings at the tables. -/
def asm (x : Pr k → Fin 2 → Fin ℓ → Bool) (a : Fin k) : Ix k ℓ := fun b =>
  if h : a < b then x ⟨(a, b), h⟩ 0 else if h : b < a then x ⟨(b, a), h⟩ 1 else fun _ => false

theorem asm_lt (x : Pr k → Fin 2 → Fin ℓ → Bool) (e : Pr k) : asm x e.1.1 e.1.2 = x e 0 := by
  rw [asm, dif_pos e.2]

theorem asm_gt (x : Pr k → Fin 2 → Fin ℓ → Bool) (e : Pr k) : asm x e.1.2 e.1.1 = x e 1 := by
  rw [asm, dif_neg (not_lt.2 e.2.le), dif_pos e.2]

theorem asm_inj : Function.Injective (asm : (Pr k → Fin 2 → Fin ℓ → Bool) → Fin k → Ix k ℓ) := by
  intro x y h
  funext e i
  fin_cases i
  · have := congrFun (congrFun h e.1.1) e.1.2
    rwa [asm_lt, asm_lt] at this
  · have := congrFun (congrFun h e.1.2) e.1.1
    rwa [asm_gt, asm_gt] at this

/-- The strings at a table depend on the ends at this table only. -/
theorem asm_congr {x y : Pr k → Fin 2 → Fin ℓ → Bool} {a : Fin k}
    (h : ∀ e : Pr k, ∀ i : Fin 2, (if i = 0 then e.1.1 else e.1.2) = a → x e i = y e i) :
    asm x a = asm y a := by
  funext b
  simp only [asm]
  split_ifs with h1 h2
  · rw [h ⟨(a, b), h1⟩ 0 rfl]
  · rw [h ⟨(b, a), h2⟩ 1 rfl]
  · rfl

section Poly

variable (F : Type*) [CommSemiring F] (k ℓ : ℕ)

/-- **The polynomial of the complete network** of k tables with strings of ℓ bits. -/
noncomputable def fkl : MvPolynomial (Fin k × Ix k ℓ) F :=
  ∑ σ : Pr k → Fin ℓ → Bool, ∏ a, X (a, asm (fun e _ => σ e) a)

variable {F k ℓ}

theorem prod_X (y : Fin k → Ix k ℓ) :
    ∏ a, (X (a, y a) : MvPolynomial (Fin k × Ix k ℓ) F) = monomial (mono univ y) 1 := by
  rw [mono, monomial_sum_one]
  rfl

theorem mono_univ_inj {y z : Fin k → Ix k ℓ} (h : mono univ y = mono univ z) : y = z := by
  funext a
  have h1 := DFunLike.congr_fun h (a, y a)
  rw [mono_apply, mono_apply, if_pos ⟨Finset.mem_univ _, rfl⟩] at h1
  by_contra hne
  rw [if_neg fun h2 => hne h2.2.symm] at h1
  exact one_ne_zero h1

/-- The coefficients. -/
theorem cf_fkl (x : Pr k → Fin 2 → Fin ℓ → Bool) :
    cf univ (fkl F k ℓ) (asm x) = if ∀ e, x e 0 = x e 1 then 1 else 0 := by
  classical
  rw [cf, fkl, coeff_sum]
  simp only [prod_X, coeff_monomial]
  by_cases h : ∀ e, x e 0 = x e 1
  · rw [if_pos h, Finset.sum_eq_single fun e => x e 0]
    · rw [if_pos]
      congr 2
      funext e i
      fin_cases i
      · rfl
      · exact h e
    · intro σ _ hσ
      rw [if_neg]
      intro h1
      have h2 := asm_inj (mono_univ_inj h1)
      apply hσ
      funext e
      exact congrFun (congrFun h2 e) 0
    · exact fun hn => absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [if_neg]
    intro h1
    have h2 := asm_inj (mono_univ_inj h1)
    apply h
    intro e
    rw [← h2]

end Poly

end Nc.CaseI
