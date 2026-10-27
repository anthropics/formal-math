/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBoundInfinitelyOftenStatement
public import CircuitLowerBound.Closed
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7) at infinitely many lengths

`ENP.allDecided`: every set of words of length n is decided by some circuit. The proof extends a
given circuit: a function of the input is AVAILABLE in a circuit if some wire carries it; every
circuit can be extended so that a given function
becomes available (`Ext`), first for the input bits and the constants, then for any function of two
functions that have this property, then, by induction on k, for every function that depends on the
first k input bits only.
`ENP.infinitely_often`: if for some c all lengths n ≥ N had circuits with at most c·(n+1) gates, the
finitely many lengths below N could be paid for by a larger c; so a language without circuits of
linear size fails at infinitely many lengths, for every c. -/

public section

namespace CircuitLowerBound.Inf

open ENP

theorem wires_append (x : List Bool) (C D : Circuit) : wires x (C ++ D) = wires (wires x C) D := List.foldl_append

theorem wires_concat (x : List Bool) (C : Circuit) (G : Gate) :
    wires x (C ++ [G]) = wires x C ++ [G.op ((wires x C).getD G.in₁ false) ((wires x C).getD G.in₂ false)] := by
  simp [wires]

theorem length_wires (x : List Bool) (C : Circuit) : (wires x C).length = x.length + C.length := by
  induction C using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton C G ih => rw [wires_concat, List.length_append, ih, List.length_append]; simp; omega

theorem prefix_wires (x : List Bool) (C : Circuit) : x <+: wires x C := by
  induction C using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton C G ih => rw [wires_concat]; exact ih.trans (List.prefix_append _ _)

theorem getD_of_prefix {l₁ l₂ : List Bool} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) : l₂.getD i false = l₁.getD i false := by
  obtain ⟨r, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

/-- Some wire of the circuit carries g x on every input x of n bits. -/
def Avail (n : ℕ) (C : Circuit) (g : List Bool → Bool) : Prop := ∃ w, w < n + C.length ∧ ∀ x : List Bool, x.length = n → (wires x C).getD w false = g x

theorem Avail.mono {n : ℕ} {C : Circuit} {g : List Bool → Bool} (h : Avail n C g) (D : Circuit) : Avail n (C ++ D) g := by
  obtain ⟨w, hw, h⟩ := h
  refine ⟨w, by rw [List.length_append]; omega, fun x hx => ?_⟩
  rw [wires_append, getD_of_prefix (prefix_wires _ D) (by rw [length_wires, hx]; exact hw), h x hx]

/-- One more gate. -/
theorem Avail.gate {n : ℕ} {C : Circuit} {g₁ g₂ : List Bool → Bool} (h₁ : Avail n C g₁) (h₂ : Avail n C g₂) (op : Bool → Bool → Bool) :
    ∃ G : Gate, Avail n (C ++ [G]) fun x => op (g₁ x) (g₂ x) := by
  obtain ⟨w₁, -, h₁⟩ := h₁
  obtain ⟨w₂, -, h₂⟩ := h₂
  refine ⟨⟨op, w₁, w₂⟩, n + C.length, by simp, fun x hx => ?_⟩
  rw [wires_concat, List.getD_append_right _ _ _ _ (by rw [length_wires, hx]), length_wires, hx, h₁ x hx, h₂ x hx]
  simp

/-- Every circuit can be extended so that g becomes available. -/
def Ext (n : ℕ) (g : List Bool → Bool) : Prop := ∀ C₀ : Circuit, ∃ D : Circuit, Avail n (C₀ ++ D) g

theorem Ext.congr {n : ℕ} {g g' : List Bool → Bool} (h : Ext n g) (e : ∀ x : List Bool, x.length = n → g x = g' x) : Ext n g' := fun C₀ => by
  obtain ⟨D, w, hw, hD⟩ := h C₀
  exact ⟨D, w, hw, fun x hx => (hD x hx).trans (e x hx)⟩

theorem Ext.op {n : ℕ} {g₁ g₂ : List Bool → Bool} (h₁ : Ext n g₁) (h₂ : Ext n g₂) (op : Bool → Bool → Bool) : Ext n fun x => op (g₁ x) (g₂ x) := fun C₀ => by
  obtain ⟨D₁, a₁⟩ := h₁ C₀
  obtain ⟨D₂, a₂⟩ := h₂ (C₀ ++ D₁)
  obtain ⟨G, a⟩ := (a₁.mono D₂).gate a₂ op
  exact ⟨D₁ ++ D₂ ++ [G], by simpa only [List.append_assoc] using a⟩

theorem ext_proj {n i : ℕ} (hi : i < n) : Ext n fun x => x.getD i false := fun C₀ =>
  ⟨[], i, by omega, fun x hx => by rw [List.append_nil]; exact getD_of_prefix (prefix_wires x C₀) (by omega)⟩

theorem ext_const (n : ℕ) (b : Bool) : Ext n fun _ => b := fun C₀ =>
  ⟨[⟨fun _ _ => b, 0, 0⟩], n + C₀.length, by simp, fun x hx => by
    rw [wires_concat, List.getD_append_right _ _ _ _ (by rw [length_wires, hx]), length_wires, hx]
    simp⟩

/-- Every function that depends on the first k input bits only can be made available. -/
theorem ext_of_dep {n : ℕ} : ∀ k, k ≤ n → ∀ g : List Bool → Bool,
    (∀ x y : List Bool, x.length = n → y.length = n → x.take k = y.take k → g x = g y) → Ext n g := by
  intro k
  induction k with
  | zero =>
    intro _ g hg
    exact (ext_const n (g (List.replicate n false))).congr fun x hx => hg _ _ (by simp) hx (by simp)
  | succ k ih =>
    intro hk g hg
    have hdep : ∀ b : Bool, Ext n fun x => g (x.set k b) := fun b =>
      ih (by omega) _ fun x y hx hy hxy => hg _ _ (by simpa using hx) (by simpa using hy) (by
        apply List.ext_getElem?
        intro i
        by_cases hi : i < k + 1
        · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi, List.getElem?_set, List.getElem?_set]
          by_cases hik : k = i
          · simp [hik, hx, hy]
          · have h1 : (x.take k)[i]? = (y.take k)[i]? := by rw [hxy]
            rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at h1
            simp [hik, h1]
        · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)])
    have h1 := ((ext_proj (n := n) (i := k) (by omega)).op (hdep true) fun p q => p && q).op
      ((ext_proj (n := n) (i := k) (by omega)).op (hdep false) fun p q => !p && q) fun p q => p || q
    refine h1.congr fun x hx => ?_
    have hset : x.set k (x.getD k false) = x := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.set_getElem_self _
    cases hb : x.getD k false <;> rw [hb] at hset <;> simp [hset]

end CircuitLowerBound.Inf

open CircuitLowerBound.Inf in
/-- Every set of words of length n is decided by some circuit. -/
theorem ENP.allDecided : ENP.AllDecided := by
  classical
  intro L n
  obtain ⟨D, w, -, hD⟩ := ext_of_dep n le_rfl (fun x => decide (L x)) (fun x y hx hy h => by
    rw [List.take_of_length_le hx.le, List.take_of_length_le hy.le] at h; rw [h]) []
  refine ⟨_, [] ++ D ++ [⟨fun p _ => p, w, w⟩], le_rfl, fun x hx => ?_⟩
  rw [ENP.eval, wires_concat, List.getLastD_concat, hD x hx]
  simp

/-- A language that is not decided by circuits of linear size fails at infinitely many lengths, for
every c. -/
theorem ENP.infinitely_often {L : ENP.Lang} (h : ¬ENP.HasLinearCircuits L) (c N : ℕ) : ∃ n, N ≤ n ∧ ¬ENP.DecidedAt L (c * (n + 1)) n := by
  by_contra hc
  have hc : ∀ n, N ≤ n → ENP.DecidedAt L (c * (n + 1)) n := by
    intro n hn
    by_contra h'
    exact hc ⟨n, hn, h'⟩
  choose s hs using ENP.allDecided L
  refine h ⟨c + ∑ n ∈ Finset.range N, s n, fun n => ?_⟩
  by_cases hn : N ≤ n
  · obtain ⟨C, hC, hd⟩ := hc n hn
    exact ⟨C, hC.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)), hd⟩
  · obtain ⟨C, hC, hd⟩ := hs n
    refine ⟨C, hC.trans ?_, hd⟩
    have h1 : s n ≤ ∑ n ∈ Finset.range N, s n := Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    calc s n ≤ (c + ∑ n ∈ Finset.range N, s n) * 1 := by omega
      _ ≤ (c + ∑ n ∈ Finset.range N, s n) * (n + 1) := Nat.mul_le_mul_left _ (by omega)
