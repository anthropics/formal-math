/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.SlpCalc

/-!
# Straight-line programs: costs as powers of one number

`CY D H Y a f`: the function `f` is computed in at most `Y ^ a` steps from functions of `H`; `PY` the same for
properties.
-/

namespace Nc.Tow

open Finset Unc

variable {Inp ι : Type} {D Y : ℕ} {H H' : Set (Inp → ℕ)}

/-- Computed in at most `Y ^ a` steps. -/
def CY (D : ℕ) (H : Set (Inp → ℕ)) (Y a : ℕ) (f : Inp → ℕ) : Prop := Cost D H (Y ^ a) f

/-- Decided in at most `Y ^ a` steps. -/
def PY (D : ℕ) (H : Set (Inp → ℕ)) (Y a : ℕ) (P : Inp → Prop) : Prop := CostP D H (Y ^ a) P

/-- The bounds for the alphabet. -/
structure Alph (D Y : ℕ) : Prop where
  three : 3 ≤ Y
  pow : Y ^ 4 ≤ D

namespace Alph

variable (h : Alph D Y)
include h

theorem pos : 0 < Y := by have := h.three; omega

theorem lt_of_le {n : ℕ} (hn : n ≤ Y) : n < D := by
  have h3 := h.three
  have h4 : Y < Y ^ 4 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ < Y ^ 4 := Nat.pow_lt_pow_right (by omega) (by omega)
  have := h.pow
  omega

theorem lt_of_le3 {n : ℕ} (hn : n ≤ 2 * Y ^ 3) : n < D := by
  have h3 := h.three
  have h4 : 2 * Y ^ 3 < Y ^ 4 := by
    have e : Y ^ 4 = Y * Y ^ 3 := by ring
    have hp : 0 < Y ^ 3 := Nat.pow_pos (by omega)
    rw [e]
    nlinarith
  have := h.pow
  omega

theorem one_lt : 1 < D := h.lt_of_le (by have := h.three; omega)

theorem zero_lt : 0 < D := by have := h.one_lt; omega

theorem pow_pos (a : ℕ) : 1 ≤ Y ^ a := Nat.one_le_pow _ _ h.pos

theorem step (a : ℕ) : 3 * Y ^ a ≤ Y ^ (a + 1) := by
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left _ h.three

theorem step2 (a : ℕ) : 9 * Y ^ a ≤ Y ^ (a + 2) := by
  have h1 := h.step a
  have h2 : 3 * Y ^ (a + 1) ≤ Y ^ (a + 2) := h.step (a + 1)
  omega

theorem sum_step {s a : ℕ} (hs : s ≤ Y) : s * (Y ^ a + 1) + 1 ≤ Y ^ (a + 2) := by
  have h1 := h.pow_pos a
  have h2 : 3 * Y ^ (a + 1) ≤ Y ^ (a + 2) := h.step (a + 1)
  have h3 : Y * Y ^ a = Y ^ (a + 1) := by ring
  have h4 : Y ≤ Y ^ (a + 1) := by
    rw [← h3]
    exact Nat.le_mul_of_pos_right Y (by omega)
  have h5 := h.pos
  have h6 : s * (Y ^ a + 1) ≤ Y * (Y ^ a + 1) := Nat.mul_le_mul_right _ hs
  have e1 : Y * (Y ^ a + 1) = Y ^ (a + 1) + Y := by ring
  rw [e1] at h6
  omega

end Alph

namespace CY

theorem base {f : Inp → ℕ} (hf : f ∈ H) (_hY : 0 < Y) : CY D H Y 0 f :=
  Cost.mono (Cost.base hf) (Nat.zero_le _)

theorem const (c : ℕ) (hc : c < D) : CY D H Y 0 fun _ => c := by
  unfold CY
  rw [pow_zero]
  exact Cost.const c hc

theorem mono {a b : ℕ} {f : Inp → ℕ} (hY : 0 < Y) (hf : CY D H Y a f) (hab : a ≤ b) : CY D H Y b f :=
  Cost.mono hf (Nat.pow_le_pow_right hY hab)

theorem congr {a : ℕ} {f g : Inp → ℕ} (hf : CY D H Y a f) (e : ∀ x, f x = g x) : CY D H Y a g := Cost.congr hf e

theorem weaken {a : ℕ} {f : Inp → ℕ} (hf : CY D H Y a f) (hH : H ⊆ H') : CY D H' Y a f := Cost.weaken hH hf

variable (hA : Alph D Y)
include hA

theorem op {a : ℕ} {f g : Inp → ℕ} (φ : ℕ → ℕ → ℕ) (hf : CY D H Y a f) (hg : CY D H Y a g)
    (hb : ∀ x, φ (f x) (g x) < D) : CY D H Y (a + 1) fun x => φ (f x) (g x) :=
  Cost.mono (Cost.op φ hf hg hb) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem op1 {a : ℕ} {f : Inp → ℕ} (φ : ℕ → ℕ) (hf : CY D H Y a f) (hb : ∀ x, φ (f x) < D) :
    CY D H Y (a + 1) fun x => φ (f x) :=
  Cost.mono (Cost.op1 hA.zero_lt φ hf hb) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem sum {κ : Type*} (s : Finset κ) {a : ℕ} {f : κ → Inp → ℕ} (hs : s.card ≤ Y)
    (hf : ∀ i ∈ s, CY D H Y a (f i)) (hb : ∀ x, ∑ i ∈ s, f i x < D) :
    CY D H Y (a + 2) fun x => ∑ i ∈ s, f i x :=
  Cost.mono (Cost.sum hA.zero_lt s hf hb) (hA.sum_step hs)

theorem ite {a : ℕ} {P : Inp → Prop} [DecidablePred P] {f g : Inp → ℕ} (hP : PY D H Y a P)
    (hf : CY D H Y a f) (hg : CY D H Y a g) (b1 : ∀ x, f x < D) (b2 : ∀ x, g x < D) :
    CY D H Y (a + 2) fun x => if P x then f x else g x :=
  Cost.mono (Cost.ite hP hf hg b1 b2) (by
    have := hA.step2 a
    have := hA.pow_pos a
    omega)

end CY

namespace PY

theorem base {P : Inp → Prop} (hP : ind P ∈ H) (hY : 0 < Y) : PY D H Y 0 P := CY.base hP hY

theorem mono {a b : ℕ} {P : Inp → Prop} (hY : 0 < Y) (hP : PY D H Y a P) (hab : a ≤ b) : PY D H Y b P :=
  CY.mono hY hP hab

theorem congr {a : ℕ} {P Q : Inp → Prop} (hP : PY D H Y a P) (e : ∀ x, P x ↔ Q x) : PY D H Y a Q :=
  CostP.congr hP e

variable (hA : Alph D Y)
include hA

theorem const (P : Prop) : PY D H Y 0 fun _ => P := by
  unfold PY
  rw [pow_zero]
  exact CostP.const hA.one_lt P

theorem rel {a : ℕ} {f g : Inp → ℕ} (r : ℕ → ℕ → Prop) (hf : CY D H Y a f) (hg : CY D H Y a g) :
    PY D H Y (a + 1) fun x => r (f x) (g x) :=
  CostP.mono (CostP.rel hA.one_lt r hf hg) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem rel1 {a : ℕ} {f : Inp → ℕ} (r : ℕ → Prop) (hf : CY D H Y a f) : PY D H Y (a + 1) fun x => r (f x) :=
  CostP.mono (CostP.rel1 hA.one_lt r hf) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem and {a : ℕ} {P Q : Inp → Prop} (hP : PY D H Y a P) (hQ : PY D H Y a Q) :
    PY D H Y (a + 1) fun x => P x ∧ Q x :=
  CostP.mono (CostP.and hA.one_lt hP hQ) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem or {a : ℕ} {P Q : Inp → Prop} (hP : PY D H Y a P) (hQ : PY D H Y a Q) :
    PY D H Y (a + 1) fun x => P x ∨ Q x :=
  CostP.mono (CostP.or hA.one_lt hP hQ) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem not {a : ℕ} {P : Inp → Prop} (hP : PY D H Y a P) : PY D H Y (a + 1) fun x => ¬ P x :=
  CostP.mono (CostP.not hA.one_lt hP) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem exists_mem {κ : Type*} (s : Finset κ) {a : ℕ} {P : κ → Inp → Prop} (hs : s.card ≤ Y)
    (hP : ∀ i ∈ s, PY D H Y a (P i)) : PY D H Y (a + 2) fun x => ∃ i ∈ s, P i x :=
  CostP.mono (CostP.exists_mem hA.one_lt s hP) (hA.sum_step hs)

theorem forall_mem {κ : Type*} (s : Finset κ) {a : ℕ} {P : κ → Inp → Prop} (hs : s.card ≤ Y)
    (hP : ∀ i ∈ s, PY D H Y a (P i)) : PY D H Y (a + 2) fun x => ∀ i ∈ s, P i x :=
  CostP.mono (CostP.forall_mem hA.one_lt s hP) (hA.sum_step hs)

theorem forall_univ {κ : Type*} [Fintype κ] {a : ℕ} {P : κ → Inp → Prop} (hs : Fintype.card κ ≤ Y)
    (hP : ∀ i, PY D H Y a (P i)) : PY D H Y (a + 2) fun x => ∀ i, P i x :=
  (forall_mem hA univ hs fun i _ => hP i).congr fun x => by simp

theorem exists_univ {κ : Type*} [Fintype κ] {a : ℕ} {P : κ → Inp → Prop} (hs : Fintype.card κ ≤ Y)
    (hP : ∀ i, PY D H Y a (P i)) : PY D H Y (a + 2) fun x => ∃ i, P i x :=
  (exists_mem hA univ hs fun i _ => hP i).congr fun x => by simp

omit hA in
/-- The indicator as a number. -/
theorem toCY {a : ℕ} {P : Inp → Prop} (hP : PY D H Y a P) : CY D H Y a (ind P) := hP

end PY

variable {inp : ι → Inp → Fin D}

/-- The set of functions is computed in `p + c * Y ^ 12` steps. -/
def SY (inp : ι → Inp → Fin D) (Y p c : ℕ) (H : Set (Inp → ℕ)) : Prop := SlpN inp (p + c * Y ^ 12) H

/-- A family of functions is added. -/
theorem SY.add (hA : Alph D Y) {p c : ℕ} (h : SY inp Y p c H) {κ : Type*} [Fintype κ] (f : κ → Inp → ℕ) {a e : ℕ}
    (hκ : Fintype.card κ ≤ Y ^ e) (hf : ∀ i, CY D H Y a (f i)) (hae : a + e ≤ 12) :
    ∃ H', SY inp Y p (c + 1) H' ∧ H ⊆ H' ∧ ∀ i, f i ∈ H' := by
  refine ⟨H ∪ Set.range f, (SlpN.stage hA.zero_lt h f (Y ^ a) hf).le hA.zero_lt ?_, Set.subset_union_left,
    fun i => Or.inr ⟨i, rfl⟩⟩
  have h1 : Fintype.card κ * Y ^ a ≤ Y ^ 12 := by
    calc Fintype.card κ * Y ^ a ≤ Y ^ e * Y ^ a := Nat.mul_le_mul_right _ hκ
      _ = Y ^ (a + e) := by rw [← pow_add, add_comm]
      _ ≤ Y ^ 12 := Nat.pow_le_pow_right hA.pos hae
  have e2 : (c + 1) * Y ^ 12 = c * Y ^ 12 + Y ^ 12 := by ring
  rw [e2]
  omega

theorem SY.le (hA : Alph D Y) {p c c' : ℕ} (h : SY inp Y p c H) (hc : c ≤ c') : SY inp Y p c' H :=
  SlpN.le hA.zero_lt (Nat.add_le_add_left (Nat.mul_le_mul_right _ hc) _) h

end Nc.Tow
