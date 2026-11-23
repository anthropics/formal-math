/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.Defs

/-!
# Tables with code words, and the strings on the sides

The string on a side determines the indices and the strings of all blocks.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

section Codes

variable {F : Type*} [CommRing F] {I : Type*} [Fintype I] {A B : I → Type*}
  [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] {Zg Zh : Type*} [Fintype Zg] [DecidableEq Zg] [Fintype Zh]
  [DecidableEq Zh] (ca : (i : I) → A i → Zg) (cb : (i : I) → B i → Zh)

variable {ca cb} (hca : Function.Injective fun p : Σ i, A i => ca p.1 p.2)
  (hcb : Function.Injective fun p : Σ i, B i => cb p.1 p.2)

include hca hcb

end Codes

section Strings

variable {I : Type} {lam : ℕ} (lab : I → Fin lam → Bool)

theorem sideString_succ {B : ℕ} (len : I → ℕ) (i : Fin (B + 1) → I) (g : ∀ k, Fin (len (i k)) → Bool) :
    sideString lab len i g = List.ofFn (lab (i 0)) ++ (List.ofFn (g 0) ++
      sideString lab len (fun k => i k.succ) fun k => g k.succ) := by
  simp [sideString, List.ofFn_succ]

theorem length_sideString {B : ℕ} (len : I → ℕ) (i : Fin B → I) (g : ∀ k, Fin (len (i k)) → Bool) :
    (sideString lab len i g).length = ∑ k, (lam + len (i k)) := by
  induction B with
  | zero => simp [sideString]
  | succ B ih =>
    rw [sideString_succ, List.length_append, List.length_append, ih, Fin.sum_univ_succ]
    simp [add_assoc]

variable {lab}

theorem sideString_inj (hlab : Function.Injective lab) {B : ℕ} (len : I → ℕ) {i i' : Fin B → I}
    {g : ∀ k, Fin (len (i k)) → Bool} {g' : ∀ k, Fin (len (i' k)) → Bool}
    (h : sideString lab len i g = sideString lab len i' g') : ∀ k, i k = i' k ∧ HEq (g k) (g' k) := by
  induction B with
  | zero => exact fun k => k.elim0
  | succ B ih =>
    rw [sideString_succ, sideString_succ] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    have e0 : i 0 = i' 0 := hlab (List.ofFn_injective h1)
    obtain ⟨h3, h4⟩ := List.append_inj h2 (by simp [e0])
    have key : ∀ (a a' : I) (_ : a = a') (f : Fin (len a) → Bool) (f' : Fin (len a') → Bool),
        List.ofFn f = List.ofFn f' → HEq f f' := by
      rintro a _ rfl f f' hf
      exact heq_of_eq (List.ofFn_injective hf)
    intro k
    refine Fin.cases ⟨e0, key _ _ e0 _ _ h3⟩ (fun k => ih h4 k) k

theorem sideString_injective (hlab : Function.Injective lab) {B : ℕ} (len : I → ℕ) :
    Function.Injective fun p : Σ i : Fin B → I, ∀ k, Fin (len (i k)) → Bool =>
      sideString lab len p.1 p.2 := by
  rintro ⟨i, g⟩ ⟨i', g'⟩ h
  have h := sideString_inj hlab len h
  have e : i = i' := funext fun k => (h k).1
  subst e
  have : g = g' := funext fun k => eq_of_heq (h k).2
  rw [this]

theorem ucount_sideString_le {m B U ub : ℕ} {len : I → ℕ} (hlen : ∀ i, len i ≤ m) (hB : B * (m + lam) / ub + 1 ≤ U)
    (i : Fin B → I) (g : ∀ k, Fin (len (i k)) → Bool) : ucount ub (sideString lab len i g) ≤ U := by
  refine le_trans ?_ hB
  rw [ucount, length_sideString]
  refine Nat.add_le_add_right (Nat.div_le_div_right ?_) _
  calc ∑ k, (lam + len (i k)) ≤ ∑ _k : Fin B, (m + lam) :=
        Finset.sum_le_sum fun k _ => by have := hlen (i k); omega
    _ = B * (m + lam) := by simp

/-- The code word of a string: its first `U` units. -/
def codeWord (lab : I → Fin lam → Bool) (len : I → ℕ) (ub U : ℕ) {B : ℕ} (i : Fin B → I)
    (g : ∀ k, Fin (len (i k)) → Bool) : Fin U → UW ub := fun k => unitsOf ub (sideString lab len i g) k

theorem codeWord_injective (hlab : Function.Injective lab) {m B U ub : ℕ} (hub : 0 < ub) {len : I → ℕ}
    (hlen : ∀ i, len i ≤ m) (hB : B * (m + lam) / ub + 1 ≤ U) :
    Function.Injective fun p : Σ i : Fin B → I, ∀ k, Fin (len (i k)) → Bool =>
      codeWord lab len ub U p.1 p.2 := by
  intro p p' h
  apply sideString_injective hlab len
  apply unitsOf_inj hub
  intro k
  by_cases hk : k < U
  · exact congrFun h ⟨k, hk⟩
  · rw [unitsOf_eq_none.2, unitsOf_eq_none.2]
    · exact (ucount_sideString_le hlen hB _ _).trans (not_lt.1 hk)
    · exact (ucount_sideString_le hlen hB _ _).trans (not_lt.1 hk)

end Strings

end Nc.Cut
