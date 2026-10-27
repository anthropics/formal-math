/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.CountNet
import StepMachines.Math.SatArith

/-! The network of a k-CNF as a program: the clauses are cut into g groups (the nodes), and the
weights and
the interactions are given by procedures; `presents` shows that these procedures compute
`wordNet g k φ` within the size `S₀`. -/

namespace Groundwork.Prog

open Finset Groundwork.Prog.Count

/-- Some assignment makes a literal of every clause true. -/
@[expose] public def Fml.Sat (φ : Fml) : Prop := ∃ a : ℕ → Bool, ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2

/-- The network of φ, given by procedures: g groups of clauses (the nodes), one state bit for each
of the
k literal slots of a clause. The procedures take φ itself as their context. -/
@[expose] public def satP (g k : ℕ) : PNet Fml where
  n φ _ := mu g φ * k
  cap φ a b := capF g k φ a b
  W := Stepped.ofFun (wF g k)
  f := Stepped.ofFun (fF g k)

theorem size_word (z : List Bool) : size z = 2 * z.length + 1 := by
  induction z with
  | nil => rfl
  | cons b z ih =>
    simp only [size_list, List.map_cons, List.sum_cons, size_bool, List.length_cons] at ih ⊢
    omega

theorem size_fin {g : ℕ} (a : Fin g) : size a.val ≤ g + 1 := by
  simp only [size_nat]
  exact Nat.add_le_add_right (Nat.size_le.2 (a.2.trans Nat.lt_two_pow_self)) 1

theorem size_boole (p : Prop) [Decidable p] : size (if p then (1 : ℤ) else 0) ≤ 2 := by
  simp only [size_int]
  refine Nat.add_le_add_right (Nat.size_le.2 ?_) 1
  split_ifs <;> simp

theorem length_lt_size (φ : Fml) : φ.length < size φ := by
  have : ∀ l : List (List (ℕ × Bool)), l.length ≤ (l.map fun x => size x + 1).sum := by
    intro l
    induction l with
    | nil => simp
    | cons C l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  simp only [size_list]
  exact Nat.lt_succ_of_le (this φ)

/-- The size within which the procedures of satP answer. -/
def S₀ (g k : ℕ) (φ : Fml) : ℕ := size φ + 2 * g + 6 * (mu g φ * k) + 8

theorem capF_le {g k : ℕ} (hg : 0 < g) (φ : Fml) {a b : Fin g} (hab : a ≠ b) :
    capF g k φ a.val b.val ≤ 2 * (mu g φ * k) := by
  have h := (sized_wordNet (k := k) (φ := φ) hg 0).sum_c a
  have h1 : (wordNet g k φ).c a b ≤ ∑ b ∈ univ.erase a, (wordNet g k φ).c a b :=
    Finset.single_le_sum (f := fun b => (wordNet g k φ).c a b) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.2 ⟨hab.symm, mem_univ b⟩)
  have h2 : 2 * k * mu g φ = 2 * (mu g φ * k) := by ring
  have h3 : (wordNet g k φ).c a b = capF g k φ a.val b.val := rfl
  omega

/-- The procedures of `satP` compute the network `wordNet g k φ`, each in one step and within size
`S₀`. -/
theorem presents {g k : ℕ} (hg : 0 < g) (φ : Fml) : (satP g k).Presents φ (wordNet g k φ) 1 (S₀ g k φ) where
  S_eq _ := rfl
  c_eq _ _ _ := rfl
  lab_eq a b _ := lab_wordNet a b
  W_runs a z hz := by
    refine (Stepped.ofFun_runs (wF g k) (φ, (a.val, z))).mono le_rfl ?_
    have h1 := size_fin a
    have h2 : size (wF g k (φ, (a.val, z))) ≤ 2 := size_boole _
    have h3 : z.length = mu g φ * k := hz
    simp only [size_prod, size_word, S₀, h3] at *
    omega
  f_runs a b z θ hab hz hθ := by
    refine (Stepped.ofFun_runs (fF g k) (φ, ((a.val, b.val), (z, θ)))).mono le_rfl ?_
    have h1 := size_fin a
    have h1' := size_fin b
    have h2 : size (fF g k (φ, ((a.val, b.val), (z, θ)))) ≤ 2 := by
      unfold fF
      split_ifs <;> simp
    have h3 : z.length = mu g φ * k := hz
    have h4 : θ.length = capF g k φ a.val b.val := hθ
    have h5 := capF_le (k := k) hg φ hab
    simp only [size_prod, size_word, S₀, h3, h4] at *
    omega

theorem sized_mono {J σ τ : Type} [Fintype J] [LinearOrder J] {N : Network J σ τ} {P P' B : ℕ} (h : N.Sized P B)
    (hP : P ≤ P') : N.Sized P' B :=
  { h with
    card_S := fun a => (h.card_S a).trans (Nat.pow_le_pow_right (by norm_num) hP)
    sum_c := fun a => (h.sum_c a).trans hP }

end Groundwork.Prog
