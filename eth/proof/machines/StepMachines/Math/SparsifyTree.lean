/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Logic.Function.Iterate

/-! Binary branching given by a step function: its leaves, a depth-first walk with an explicit
stack, and the count
of leaves when a path has at most D steps and at most T/q heavy steps. It is used for the branching
tree of the
sparsification lemma (Lemma 4). -/

namespace Groundwork.Sparsify

open Finset

variable {σ : Type*} (step : σ → Option (σ × σ))

/-- The leaves below s, left (light) to right (heavy), cut at depth k. -/
@[expose] public def leaves : ℕ → σ → List σ
  | 0, s => [s]
  | k + 1, s =>
    match step s with
    | none => [s]
    | some (l, h) => leaves k l ++ leaves k h

/-- One round of the depth-first walk on (stack, leaves found so far). -/
@[expose] public def round : List σ × List σ → List σ × List σ
  | ([], out) => ([], out)
  | (s :: r, out) =>
    match step s with
    | none => (r, s :: out)
    | some (l, h) => (l :: h :: r, out)

public theorem leaves_length_pos (k : ℕ) (s : σ) : 0 < (leaves step k s).length := by
  induction k generalizing s with
  | zero => simp [leaves]
  | succ k ih =>
    rw [leaves]
    split
    · simp
    · rename_i l h _
      have := ih l
      simp only [List.length_append]
      omega

theorem round_nil_iterate (m : ℕ) (out : List σ) : (round step)^[m] ([], out) = ([], out) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih

/-- The walk needs 2·(number of leaves) − 1 rounds for the tree below the top of the stack. -/
public theorem round_iterate (k : ℕ) (s : σ) (hk : ∀ x ∈ leaves step k s, step x = none) (r out : List σ) :
    (round step)^[2 * (leaves step k s).length - 1] (s :: r, out) = (r, (leaves step k s).reverse ++ out) := by
  induction k generalizing s r out with
  | zero =>
    have h0 : step s = none := hk s (by simp [leaves])
    simp [leaves, round, h0]
  | succ k ih =>
    cases h0 : step s with
    | none => simp [leaves, round, h0]
    | some lh =>
      obtain ⟨l, h⟩ := lh
      have e0 : leaves step (k + 1) s = leaves step k l ++ leaves step k h := by simp [leaves, h0]
      rw [e0] at hk ⊢
      have hl := leaves_length_pos step k l
      have hh := leaves_length_pos step k h
      have e : 2 * (leaves step k l ++ leaves step k h).length - 1 =
          (2 * (leaves step k h).length - 1) + ((2 * (leaves step k l).length - 1) + 1) := by
        simp only [List.length_append]; omega
      rw [e, Function.iterate_add_apply, Function.iterate_succ_apply]
      have e1 : round step (s :: r, out) = (l :: h :: r, out) := by simp [round, h0]
      rw [e1, ih l (fun x hx => hk x (List.mem_append_left _ hx)),
        ih h (fun x hx => hk x (List.mem_append_right _ hx))]
      simp

/-- After at least 2·(number of leaves) − 1 rounds from [s] the stack is empty and all leaves are
listed. -/
public theorem round_iterate_of_le (k : ℕ) (s : σ) (hk : ∀ x ∈ leaves step k s, step x = none) (R : ℕ)
    (hR : 2 * (leaves step k s).length - 1 ≤ R) :
    (round step)^[R] ([s], []) = ([], (leaves step k s).reverse) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hR
  rw [Function.iterate_add_apply, round_iterate step k s hk, round_nil_iterate]
  simp

/-- One round of the walk that keeps only «some leaf so far passed the test». -/
@[expose] public def roundB (test : σ → Bool) : List σ × Bool → List σ × Bool
  | ([], b) => ([], b)
  | (s :: r, b) =>
    match step s with
    | none => (r, test s || b)
    | some (l, h) => (l :: h :: r, b)

public theorem roundB_iterate (test : σ → Bool) (i : ℕ) (st out : List σ) :
    (roundB step test)^[i] (st, out.any test) =
      (((round step)^[i] (st, out)).1, ((round step)^[i] (st, out)).2.any test) := by
  induction i generalizing st out with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    obtain _ | ⟨s, r⟩ := st
    · exact ih [] out
    · cases h0 : step s with
      | none =>
        have e1 : roundB step test (s :: r, out.any test) = (r, (s :: out).any test) := by
          simp [roundB, h0]
        have e2 : round step (s :: r, out) = (r, s :: out) := by simp [round, h0]
        rw [e1, e2]; exact ih r (s :: out)
      | some lh =>
        have e1 : roundB step test (s :: r, out.any test) = (lh.1 :: lh.2 :: r, out.any test) := by
          simp [roundB, h0]
        have e2 : round step (s :: r, out) = (lh.1 :: lh.2 :: r, out) := by simp [round, h0]
        rw [e1, e2]; exact ih _ out

/-- After at least 2·(number of leaves) − 1 rounds the flag says whether some leaf passes the test. -/
public theorem roundB_iterate_of_le (test : σ → Bool) (k : ℕ) (s : σ)
    (hk : ∀ x ∈ leaves step k s, step x = none) (R : ℕ) (hR : 2 * (leaves step k s).length - 1 ≤ R) :
    (roundB step test)^[R] ([s], false) = ([], (leaves step k s).any test) := by
  have := roundB_iterate step test R [s] []
  rw [round_iterate_of_le step k s hk R hR] at this
  simpa using this

section Budget

/-! G s p t: the node s has used at least p of D units of depth and t of T units, of which a heavy
step uses q. -/

variable {step} {G : σ → ℕ → ℕ → Prop} {D T q : ℕ}

theorem sum_choose_succ (d h : ℕ) :
    ∑ j ∈ range (h + 1 + 1), (d + 1).choose j =
      ∑ j ∈ range (h + 1 + 1), d.choose j + ∑ j ∈ range (h + 1), d.choose j := by
  rw [sum_range_succ' _ (h + 1), sum_range_succ' _ (h + 1)]
  simp only [Nat.choose_succ_succ, sum_add_distrib, Nat.choose_zero_right, Nat.succ_eq_add_one]
  omega

theorem one_le_sum_choose (d h : ℕ) : 1 ≤ ∑ j ∈ range (h + 1), d.choose j := by
  rw [sum_range_succ']
  simp

/-- The number of leaves is at most Σ_{j ≤ h} C(d, j): d steps and h heavy steps are left. -/
public theorem length_leaves_le (hb : ∀ s p t, G s p t → p ≤ D ∧ t ≤ T)
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (k d h : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) (hd : D ≤ p + d) (hh : T < t + (h + 1) * q) :
    (leaves step k s).length ≤ ∑ j ∈ range (h + 1), d.choose j := by
  induction k generalizing d h s p t with
  | zero => simpa [leaves] using one_le_sum_choose d h
  | succ k ih =>
    rw [leaves]
    split
    · simpa using one_le_sum_choose d h
    · rename_i l r h0
      obtain ⟨hl, hr⟩ := hs s p t l r hG h0
      have hbl := hb _ _ _ hl
      have hbr := hb _ _ _ hr
      obtain _ | d := d
      · omega
      obtain _ | h := h
      · omega
      have h1 := ih d (h + 1) l (p + 1) t hl (by omega) hh
      have h2 := ih d h r (p + 1) (t + q) hr (by omega) (by rw [Nat.add_mul (h + 1) 1 q] at hh; omega)
      rw [List.length_append, sum_choose_succ]
      omega

/-- If k ≥ D − p the cut at depth k removes nothing: the list holds true leaves only. -/
public theorem step_eq_none_of_mem_leaves (hb : ∀ s p t, G s p t → p ≤ D ∧ t ≤ T)
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (k : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) (hk : D ≤ p + k) : ∀ x ∈ leaves step k s, step x = none := by
  induction k generalizing s p t with
  | zero =>
    intro x hx
    obtain rfl : x = s := by simpa [leaves] using hx
    cases h0 : step x with
    | none => rfl
    | some lh =>
      have := (hb _ _ _ (hs x p t lh.1 lh.2 hG h0).1).1
      omega
  | succ k ih =>
    intro x hx
    rw [leaves] at hx
    split at hx
    · rename_i h0
      obtain rfl : x = s := by simpa using hx
      exact h0
    · rename_i l r h0
      obtain ⟨hl, hr⟩ := hs s p t l r hG h0
      rcases List.mem_append.1 hx with hx | hx
      · exact ih l (p + 1) t hl (by omega) x hx
      · exact ih r (p + 1) (t + q) hr (by omega) x hx

/-- Every listed node satisfies the invariant. -/
public theorem exists_of_mem_leaves
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (k : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) : ∀ x ∈ leaves step k s, ∃ p' t', G x p' t' := by
  induction k generalizing s p t with
  | zero =>
    intro x hx
    obtain rfl : x = s := by simpa [leaves] using hx
    exact ⟨p, t, hG⟩
  | succ k ih =>
    intro x hx
    rw [leaves] at hx
    split at hx
    · obtain rfl : x = s := by simpa using hx
      exact ⟨p, t, hG⟩
    · rename_i l r h0
      obtain ⟨hl, hr⟩ := hs s p t l r hG h0
      rcases List.mem_append.1 hx with hx | hx
      · exact ih l (p + 1) t hl x hx
      · exact ih r (p + 1) (t + q) hr x hx

/-- If a property holds at a node exactly when it holds at one of the node's two children, then it
holds at s exactly when it holds at one of the leaves below s. -/
public theorem iff_exists_mem_leaves
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (S : σ → Prop) (hS : ∀ s p t l h, G s p t → step s = some (l, h) → (S s ↔ S l ∨ S h))
    (k : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) : S s ↔ ∃ x ∈ leaves step k s, S x := by
  induction k generalizing s p t with
  | zero => simp [leaves]
  | succ k ih =>
    rw [leaves]
    split
    · simp
    · rename_i l r h0
      obtain ⟨hl, hr⟩ := hs s p t l r hG h0
      rw [hS s p t l r hG h0, ih l (p + 1) t hl, ih r (p + 1) (t + q) hr]
      simp only [List.mem_append, or_and_right, exists_or]

/-- The stack's invariant: the node at height j from the bottom has used at least j units of depth. -/
def StackOK (G : σ → ℕ → ℕ → Prop) : List σ → Prop
  | [] => True
  | s :: r => (∃ p t, G s p t ∧ r.length ≤ p) ∧ StackOK G r

theorem StackOK.round
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (st : List σ × List σ) (h : StackOK G st.1) : StackOK G (round step st).1 := by
  obtain ⟨_ | ⟨s, r⟩, out⟩ := st
  · exact h
  · obtain ⟨⟨p, t, hG, hp⟩, hr⟩ := h
    rw [Sparsify.round]
    split
    · exact hr
    · rename_i l h' h0
      obtain ⟨hl, hh⟩ := hs s p t l h' hG h0
      exact ⟨⟨p + 1, t, hl, by simpa using hp⟩, ⟨p + 1, t + q, hh, by omega⟩, hr⟩

theorem StackOK.mem {st : List σ} (h : StackOK G st) : ∀ x ∈ st, ∃ p t, G x p t := by
  induction st with
  | nil => simp
  | cons s r ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨⟨p, t, hG, -⟩, -⟩ := h
      exact ⟨p, t, hG⟩
    · exact ih h.2 x hx

/-- At all times the stack holds at most D + 1 nodes, and each satisfies the invariant. -/
public theorem stack_bound (hb : ∀ s p t, G s p t → p ≤ D ∧ t ≤ T)
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (s : σ) (p t : ℕ) (hG : G s p t) (i : ℕ) :
    ((round step)^[i] ([s], [])).1.length ≤ D + 1 ∧ ∀ x ∈ ((round step)^[i] ([s], [])).1, ∃ p' t', G x p' t' := by
  have hok : StackOK G ((round step)^[i] ([s], [])).1 := by
    induction i with
    | zero => exact ⟨⟨p, t, hG, Nat.zero_le _⟩, trivial⟩
    | succ i ih => rw [Function.iterate_succ_apply']; exact ih.round hs
  refine ⟨?_, hok.mem⟩
  generalize ((round step)^[i] ([s], [])).1 = st at hok
  obtain _ | ⟨x, r⟩ := st
  · simp
  · obtain ⟨⟨p', t', hG', hp'⟩, -⟩ := hok
    have := (hb _ _ _ hG').1
    simp only [List.length_cons]
    omega

end Budget

end Groundwork.Sparsify
