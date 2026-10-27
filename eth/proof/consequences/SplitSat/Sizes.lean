/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitSat.Defs
import SplitSat.Leaf
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 5: the tree with n carried along, and sizes

No sentence of the paper stands behind this file. A node of the tree of `SplitSat.reduceCore` is a
formula with n in unary beside it (`stepN step`).
* `leaves_stepN`, `stack_stepN`: the leaves and the stacks of the walk are those of `step`, with n
  beside every formula.
* `length_le_of_nodup`: a formula on n variables with at most k literals per clause and no clause
  written twice has at most 2^k·(n+2)^k clauses.
* `size_node_le`, `size_stack_le`, `final_bound`: the sizes that occur in the run of the reduction
  are at most c'·(n+2)^c'.
The first four lemmas on sizes repeat lemmas of proof/machines/StepMachines/Prog/Sat.lean and
proof/consequences/WidthK/Top/Sat.lean that are not visible from outside those files. -/

public section

namespace SplitSat

open Groundwork Groundwork.Prog Groundwork.Sparsify

/-! ### The tree with n carried along -/

/-- The leaves of the tree with n carried along are the leaves of the tree, with n beside each. -/
theorem leaves_stepN (step : Fml → Option (Fml × Fml)) (u : List Unit) : ∀ (d : ℕ) (x : Fml),
    leaves (stepN step) d (u, x) = (leaves step d x).map fun y => ((u, y) : NFml)
  | 0, _ => rfl
  | d + 1, x => by
    cases h : step x with
    | none => simp [leaves, stepN, h]
    | some lh =>
      obtain ⟨l, r⟩ := lh
      simp [leaves, stepN, h, leaves_stepN step u d]

/-- One round of the walk commutes with putting n beside every formula. -/
theorem round_stepN (step : Fml → Option (Fml × Fml)) (u : List Unit) (p : List Fml × List Fml) :
    Sparsify.round (stepN step) (p.1.map fun y => ((u, y) : NFml), p.2.map fun y => ((u, y) : NFml)) =
      ((Sparsify.round step p).1.map fun y => ((u, y) : NFml), (Sparsify.round step p).2.map fun y => ((u, y) : NFml)) := by
  obtain ⟨st, out⟩ := p
  obtain _ | ⟨s, r⟩ := st
  · rfl
  · cases h : step s with
    | none => simp [Sparsify.round, stepN, h]
    | some lh =>
      obtain ⟨l, r'⟩ := lh
      simp [Sparsify.round, stepN, h]

/-- The same for any number of rounds. -/
theorem round_stepN_iterate (step : Fml → Option (Fml × Fml)) (u : List Unit) (i : ℕ) (p : List Fml × List Fml) :
    (Sparsify.round (stepN step))^[i] (p.1.map fun y => ((u, y) : NFml), p.2.map fun y => ((u, y) : NFml)) =
      (((Sparsify.round step)^[i] p).1.map fun y => ((u, y) : NFml), ((Sparsify.round step)^[i] p).2.map fun y => ((u, y) : NFml)) := by
  induction i generalizing p with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, round_stepN, ih]

/-- The stack of the walk with n carried along, after i rounds, is the stack of the walk, with n
beside every formula. -/
theorem stack_stepN (step : Fml → Option (Fml × Fml)) (u : List Unit) (i : ℕ) (x : Fml) :
    ((Sparsify.round (stepN step))^[i] ([((u, x) : NFml)], [])).1 = ((Sparsify.round step)^[i] ([x], [])).1.map fun y => ((u, y) : NFml) :=
  congrArg Prod.fst (round_stepN_iterate step u i ([x], []))

/-! ### The number of clauses -/

/-- A formula with variables below n, at most k literals per clause and no clause written twice has
at most 2^k·(n+2)^k clauses. -/
theorem length_le_of_nodup {k n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (hnd : ψ.Nodup) :
    ψ.length ≤ 2 ^ k * (n + 2) ^ k := by
  obtain ⟨φ, h3, rfl⟩ := exists_instance hψ hnd
  rw [Decode.length_toN]
  calc φ.length ≤ (2 * n + 1) ^ k := DecodeK.IsKCNF.length_le h3
    _ ≤ (2 * (n + 2)) ^ k := Nat.pow_le_pow_left (by omega) k
    _ = 2 ^ k * (n + 2) ^ k := mul_pow _ _ _

/-! ### Sizes -/

/-- The sum of (size + 1) over a list whose members have size at most s is at most (length)·(s+1). -/
theorem sum_size_le {α : Type} [HasSize α] {s : ℕ} (l : List α) (hs : ∀ x ∈ l, size x ≤ s) :
    (l.map fun x => size x + 1).sum ≤ l.length * (s + 1) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have h1 := hs x (by simp)
    have h2 := ih fun y hy => hs y (by simp [hy])
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- A list of at most k members of size at most s has size at most k·(s+1) + 1. -/
theorem size_list_le {α : Type} [HasSize α] {l : List α} {k s : ℕ} (hl : l.length ≤ k) (hs : ∀ x ∈ l, size x ≤ s) :
    size l ≤ k * (s + 1) + 1 := by
  rw [size_list]
  exact Nat.succ_le_succ ((sum_size_le l hs).trans (Nat.mul_le_mul_right _ hl))

/-- A literal on a variable below n has size at most n + 2. -/
theorem size_lit_le {l : ℕ × Bool} {n : ℕ} (h : l.1 < n) : size l ≤ n + 2 := by
  have : l.1.size ≤ n := Nat.size_le.2 (h.trans Nat.lt_two_pow_self)
  simp only [size_prod, size_nat, size_bool]
  omega

/-- A bound on the size of a formula of at most m clauses of at most k literals with variables below
n. -/
theorem size_fml_le {k : ℕ} {x : Fml} {m n : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    size x ≤ m * (k * (n + 2 + 1) + 1 + 1) + 1 :=
  size_list_le hm fun C hC => size_list_le (hx C hC).1 fun l hl => size_lit_le ((hx C hC).2 l hl)

/-- n in unary has size at most 2n + 1. -/
theorem size_unary_le (n : ℕ) : size (List.replicate n ()) ≤ 2 * n + 1 := by
  have := size_list_le (l := List.replicate n ()) (k := n) (s := 1) (by simp) fun x _ => le_rfl
  omega

/-- A node (n in unary, x), where x has at most a·(n+2)^k clauses of at most k literals with
variables below n, has size at most (a·(2k+1) + 3)·(n+2)^(k+1). -/
theorem size_node_le {k n a : ℕ} {x : Fml} (hm : x.length ≤ a * (n + 2) ^ k) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    size ((List.replicate n (), x) : NFml) ≤ (a * (2 * k + 1) + 3) * (n + 2) ^ (k + 1) := by
  have h1 := size_fml_le hm hx
  have h2 := size_unary_le n
  have hq : k * (n + 2 + 1) + 1 + 1 ≤ (2 * k + 1) * (n + 2) := by
    have a1 : k * (n + 2 + 1) ≤ k * (2 * (n + 2)) := Nat.mul_le_mul_left _ (by omega)
    have a2 : (2 * k + 1) * (n + 2) = k * (2 * (n + 2)) + (n + 2) := by ring
    omega
  have h3 : a * (n + 2) ^ k * (k * (n + 2 + 1) + 1 + 1) ≤ a * (2 * k + 1) * (n + 2) ^ (k + 1) := by
    calc a * (n + 2) ^ k * (k * (n + 2 + 1) + 1 + 1) ≤ a * (n + 2) ^ k * ((2 * k + 1) * (n + 2)) := Nat.mul_le_mul_left _ hq
      _ = a * (2 * k + 1) * (n + 2) ^ (k + 1) := by ring
  have h4 : n + 2 ≤ (n + 2) ^ (k + 1) := Nat.le_self_pow (by omega) _
  have h5 : (a * (2 * k + 1) + 3) * (n + 2) ^ (k + 1) = a * (2 * k + 1) * (n + 2) ^ (k + 1) + 3 * (n + 2) ^ (k + 1) := by ring
  rw [size_prod, h5]
  dsimp only
  omega

/-- A stack of at most Dd·n + 1 such nodes has size at most ((Dd+1)·(a·(2k+1) + 4) + 1)·(n+2)^(k+2). -/
theorem size_stack_le {k n a Dd : ℕ} {st : List Fml} (hl : st.length ≤ Dd * n + 1)
    (hst : ∀ x ∈ st, x.length ≤ a * (n + 2) ^ k ∧ ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    size (st.map fun y => ((List.replicate n (), y) : NFml)) ≤ ((Dd + 1) * (a * (2 * k + 1) + 4) + 1) * (n + 2) ^ (k + 2) := by
  have h1 := size_list_le (l := st.map fun y => ((List.replicate n (), y) : NFml)) (k := Dd * n + 1)
    (s := (a * (2 * k + 1) + 3) * (n + 2) ^ (k + 1)) (by simpa using hl) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact size_node_le (hst x hx).1 (hst x hx).2)
  refine h1.trans ?_
  have e1 : 1 ≤ (n + 2) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have e2 : 1 ≤ (n + 2) ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
  have hp : Dd * n + 1 ≤ (Dd + 1) * (n + 2) := by
    have a1 : Dd * n ≤ Dd * (n + 2) := Nat.mul_le_mul_left _ (by omega)
    have a3 : (Dd + 1) * (n + 2) = Dd * (n + 2) + (n + 2) := by ring
    omega
  have hp2 : (a * (2 * k + 1) + 3) * (n + 2) ^ (k + 1) + 1 ≤ (a * (2 * k + 1) + 4) * (n + 2) ^ (k + 1) := by
    have a3 : (a * (2 * k + 1) + 4) * (n + 2) ^ (k + 1) = (a * (2 * k + 1) + 3) * (n + 2) ^ (k + 1) + (n + 2) ^ (k + 1) := by ring
    omega
  calc (Dd * n + 1) * ((a * (2 * k + 1) + 3) * (n + 2) ^ (k + 1) + 1) + 1
      ≤ (Dd + 1) * (n + 2) * ((a * (2 * k + 1) + 4) * (n + 2) ^ (k + 1)) + 1 := Nat.succ_le_succ (Nat.mul_le_mul hp hp2)
    _ = (Dd + 1) * (a * (2 * k + 1) + 4) * (n + 2) ^ (k + 2) + 1 := by ring
    _ ≤ (Dd + 1) * (a * (2 * k + 1) + 4) * (n + 2) ^ (k + 2) + (n + 2) ^ (k + 2) := Nat.add_le_add_left e2 _
    _ = ((Dd + 1) * (a * (2 * k + 1) + 4) + 1) * (n + 2) ^ (k + 2) := by ring

/-- The constant c' of `reduceCore_decides`, from the constants of the size bounds in its proof. -/
@[expose] def cOf (P₂ P₀ R c e : ℕ) : ℕ := P₂ + P₀ + c * R ^ c + c + e + 20

/-- The sizes that occur in the proof of `reduceCore_decides` are at most c'·W^c', where W = n + 2. -/
theorem final_bound (P₂ P₀ R c e W : ℕ) (h1 : 1 ≤ W) :
    P₂ * W ^ e + c * (R * W) ^ c + 4 ≤ cOf P₂ P₀ R c e * W ^ cOf P₂ P₀ R c e ∧ P₀ * W ^ e + 3 ≤ cOf P₂ P₀ R c e * W ^ cOf P₂ P₀ R c e := by
  have ee : W ^ e ≤ W ^ cOf P₂ P₀ R c e := Nat.pow_le_pow_right h1 (by unfold cOf; omega)
  have ec : W ^ c ≤ W ^ cOf P₂ P₀ R c e := Nat.pow_le_pow_right h1 (by unfold cOf; omega)
  have e0 : 1 ≤ W ^ cOf P₂ P₀ R c e := Nat.one_le_pow _ _ h1
  generalize W ^ cOf P₂ P₀ R c e = P at ee ec e0
  have hc : cOf P₂ P₀ R c e * P = P₂ * P + P₀ * P + c * R ^ c * P + c * P + e * P + 20 * P := by
    unfold cOf; ring
  have h3 : P₂ * W ^ e ≤ P₂ * P := Nat.mul_le_mul_left _ ee
  have h2 : P₀ * W ^ e ≤ P₀ * P := Nat.mul_le_mul_left _ ee
  have hA : c * (R * W) ^ c ≤ c * R ^ c * P := by
    rw [mul_pow, ← mul_assoc]
    exact Nat.mul_le_mul_left _ ec
  rw [hc]
  constructor <;> omega

end SplitSat
