/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Suffices.Defs
public import Exits.Tested
import all StepMachines.Prog.Sat
import Mathlib.Tactic.Ring

/-! # Sizes

What lines 1 to 4 of Algorithm 1 keep in memory has size polynomial in N, the length of the input
plus 1: a formula with at most m clauses of at most 3 literals, a node (ψ, 𝒩) of the recursion tree
of the sparsification algorithm in the proof sketch of Theorem C (Appendix C), the stack of the
walk.
The counts follow the size part of `Groundwork.Prog.SatTopK.sat_correct`, here for nodes with a side
list. Also here: `tested` under a map (line 2 of Algorithm 1): the formulas tested are the outputs
of the leaves tested. -/

public section

namespace Suffices

open Groundwork Groundwork.Prog CountKSat Exits

/-- The entries of a mapped list that are tested are the images of the entries tested by the
composed test. -/
theorem tested_map {μ ν : Type} (f : μ → ν) (u : ν → Bool) (l : List μ) : tested u (l.map f) = (tested (fun x => u (f x)) l).map f := by
  induction l with
  | nil => rw [List.map_nil, tested_nil, tested_nil, List.map_nil]
  | cons x l ih =>
    cases hx : u (f x) with
    | true => rw [List.map_cons, tested_cons_of_pass hx, tested_cons_of_pass (v := fun x => u (f x)) (x := x) hx]; rfl
    | false => rw [List.map_cons, tested_cons_of_fail hx, tested_cons_of_fail (v := fun x => u (f x)) (x := x) hx, List.map_cons, ih]

/-- No more entries are tested than there are. -/
theorem length_tested_le {ν : Type} (u : ν → Bool) (l : List ν) : (tested u l).length ≤ l.length := (List.take_sublist _ _).length_le

/-- A formula of at most m clauses of at most 3 literals on variables below n ≤ N has size at most
14·m·N + 1. -/
theorem size_clauses_le {x : Fml} {m k n N : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (hk : k ≤ 3) (hn : n ≤ N) (hN : 1 ≤ N) : size x ≤ m * (14 * N) + 1 := by
  have s : size x ≤ m * (k * (n + 2 + 1) + 1 + 1) + 1 := size_list_le hm fun C hC => size_list_le (hx C hC).1 fun l hl => size_lit_le ((hx C hC).2 l hl)
  have a : k * (n + 2 + 1) ≤ 3 * (n + 2 + 1) := Nat.mul_le_mul_right _ hk
  have b : m * (k * (n + 2 + 1) + 1 + 1) ≤ m * (14 * N) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- A node (ψ, 𝒩) within the bounds of `Enumerate.Enumerates.stack` has size at most 142·N². -/
theorem size_node_le {x : CNode} {m n N : ℕ} (h1 : x.1.length ≤ m * 2 ^ 3) (h2 : x.2.length ≤ 2 * n) (h3 : ∀ C ∈ x.1, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n)
    (h4 : ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) (hm : m ≤ N) (hn : n ≤ N) (hN : 1 ≤ N) : size x ≤ 142 * N ^ 2 := by
  have s1 := size_clauses_le h1 h3 le_rfl hn hN
  have s2 := size_clauses_le h2 h4 (by omega) hn hN
  have a1 : m * 2 ^ 3 * (14 * N) ≤ 8 * N * (14 * N) := Nat.mul_le_mul_right _ (by omega)
  have a2 : 2 * n * (14 * N) ≤ 2 * N * (14 * N) := Nat.mul_le_mul_right _ (by omega)
  have e : 8 * N * (14 * N) + 2 * N * (14 * N) = 140 * N ^ 2 := by ring
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN
  rw [size_prod]
  omega

/-- A stack of at most D·n + 1 such nodes has size at most (143·(D + 1) + 1)·N³. -/
theorem size_stack_le {st : List CNode} {D n N : ℕ} (hl : st.length ≤ D * n + 1) (hx : ∀ x ∈ st, size x ≤ 142 * N ^ 2) (hn : n ≤ N) (hN : 1 ≤ N) : size st ≤ (143 * (D + 1) + 1) * N ^ 3 := by
  have s := size_list_le hl hx
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN
  have hN3 : 1 ≤ N ^ 3 := Nat.one_le_pow _ _ hN
  have p1 : D * n + 1 ≤ (D + 1) * N := by
    have a1 : D * n ≤ D * N := Nat.mul_le_mul_left _ hn
    have a3 : (D + 1) * N = D * N + N := by ring
    omega
  have a : (D * n + 1) * (142 * N ^ 2 + 1) ≤ (D + 1) * N * (143 * N ^ 2) := Nat.mul_le_mul p1 (by omega)
  have e : (D + 1) * N * (143 * N ^ 2) + N ^ 3 = (143 * (D + 1) + 1) * N ^ 3 := by ring
  omega

/-- The bound on the stack, plus 4, is at most c·N^c for c = 143·(D + 1) + 5. -/
theorem loop_bound (D N : ℕ) (hN : 1 ≤ N) : (143 * (D + 1) + 1) * N ^ 3 + 4 ≤ (143 * (D + 1) + 5) * N ^ (143 * (D + 1) + 5) := by
  have e3 : N ^ 3 ≤ N ^ (143 * (D + 1) + 5) := Nat.pow_le_pow_right hN (by omega)
  have hN3 : 1 ≤ N ^ 3 := Nat.one_le_pow _ _ hN
  have a : (143 * (D + 1) + 5) * N ^ 3 ≤ (143 * (D + 1) + 5) * N ^ (143 * (D + 1) + 5) := Nat.mul_le_mul_left _ e3
  have e : (143 * (D + 1) + 5) * N ^ 3 = (143 * (D + 1) + 1) * N ^ 3 + 4 * N ^ 3 := by ring
  omega

/-- The input as it is held after decoding, (1ⁿ, ψ) with at most N clauses, has size at most 18·N². -/
theorem size_input_le {ψ : Fml} {n N : ℕ} (hm : ψ.length ≤ N) (hx : ∀ C ∈ ψ, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n) (hn : n ≤ N) (hN : 1 ≤ N) : size (List.replicate n (), ψ) ≤ 18 * N ^ 2 := by
  have s1 := size_clauses_le hm hx le_rfl hn hN
  have s2 : size (List.replicate n ()) ≤ n * (1 + 1) + 1 := size_list_le (by simp) fun _ _ => le_rfl
  have e : N * (14 * N) = 14 * N ^ 2 := by ring
  have hNN : N ≤ N ^ 2 := by nlinarith
  rw [size_prod]
  change size (List.replicate n ()) + size ψ ≤ _
  omega

/-- A formula of at most M·n clauses, together with n, has size at most (14·M + 2)·N². -/
theorem size_sparse_le {Φ : Fml} {M n N : ℕ} (hm : Φ.length ≤ M * n) (hx : ∀ C ∈ Φ, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n) (hn : n ≤ N) (hN : 1 ≤ N) : size Φ + n ≤ (14 * M + 2) * N ^ 2 := by
  have s1 := size_clauses_le hm hx le_rfl hn hN
  have a : M * n * (14 * N) ≤ M * N * (14 * N) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn)
  have e : M * N * (14 * N) + 2 * N ^ 2 = (14 * M + 2) * N ^ 2 := by ring
  have hNN : N ≤ N ^ 2 := by nlinarith
  omega

/-- For c = c₁ + A·(14M + 2)^A + 2A + c₂ + 22: the bound on the states of the loop plus that on the
states of the machine for sparse formulas, and 20·N², are each at most c·N^c (used in
`stSufficesOf`). -/
theorem main_bound {c c₁ c₂ A M N : ℕ} (hc : c = c₁ + A * (14 * M + 2) ^ A + 2 * A + c₂ + 22) (hN : 1 ≤ N) :
    c₁ * N ^ c₁ + A * ((14 * M + 2) * N ^ 2) ^ A ≤ c * N ^ c ∧ 20 * N ^ 2 ≤ c * N ^ c := by
  have e1 : N ^ c₁ ≤ N ^ c := Nat.pow_le_pow_right hN (by omega)
  have e2 : N ^ 2 ≤ N ^ c := Nat.pow_le_pow_right hN (by omega)
  have eA : N ^ (2 * A) ≤ N ^ c := Nat.pow_le_pow_right hN (by omega)
  generalize N ^ c = P at e1 e2 eA ⊢
  have hcP : c * P = c₁ * P + A * (14 * M + 2) ^ A * P + 2 * A * P + c₂ * P + 22 * P := by rw [hc]; ring
  have k1 : c₁ * N ^ c₁ ≤ c₁ * P := Nat.mul_le_mul_left _ e1
  have kA : A * ((14 * M + 2) * N ^ 2) ^ A ≤ A * (14 * M + 2) ^ A * P := by
    rw [mul_pow, ← pow_mul, ← mul_assoc]
    exact Nat.mul_le_mul_left _ eA
  rw [hcP]
  constructor <;> omega

end Suffices
