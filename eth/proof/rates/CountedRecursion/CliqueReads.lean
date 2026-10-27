/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.SquareGrid
import ClauseBound.Alg.Level
import Mathlib.Tactic

/-! # What the value of a clique reads, and the value of a callee

* `clique_value_congr`: the value of the (K, λ)-clique reads its tables only on settings (strings of
  (K − 1)λ bits). `clique_readTables`: so tables that were made an oracle (`answersOf`) and read
  back (`readTables`) give the same value.
* `parentAt_readyOf`: the parent that the solver hands to a callee, written with the numbers of the
  level.
* `child_value`: the value that the specification gives to a callee is the value of the clique of
  the groups (`Value.groupClique`) of the network of its pattern, at the callee's label length.
* `Net.abs_value_le`: |Z| ≤ 2^{gP + g²B} for a network on [g] with parameters P, B. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- The value of a clique reads its tables only on settings. -/
theorem clique_value_congr {K lam : ℕ} {W W' : Fin K → List Bool → ℤ} (h : ∀ w, ∀ z ∈ words ((K - 1) * lam), W w z = W' w z) : (clique K lam W).value = (clique K lam W').value := by
  unfold Net.value
  refine Finset.sum_congr rfl fun z hz => ?_
  congr 1
  exact Finset.prod_congr rfl fun a _ => h a _ (Fintype.mem_piFinset.1 hz a)

/-- Tables made an oracle and read back are the tables, on settings. -/
theorem readTables_setting {K lam : ℕ} (W : ℕ → List Bool → ℤ) {w : ℕ} {z : List Bool} (hw : w < K) (hz : z.length = (K - 1) * lam) : readTables (answersOf K lam W) w z = W w z := by
  simp [readTables, answersOf, tables, hw, hz, asInt]

/-- So they give the same value. -/
theorem clique_readTables (K lam : ℕ) (W : ℕ → List Bool → ℤ) : (clique K lam fun w => readTables (answersOf K lam W) w.val).value = (clique K lam fun w => W w.val).value :=
  clique_value_congr fun w _ hz => readTables_setting W w.2 (mem_words.1 hz)

/-- A string of units is its length in unary. -/
theorem unary_length_eq (u : List Unit) : unary u.length = u := by
  induction u with
  | nil => rfl
  | cons a u ih => exact congrArg (List.cons ()) ih

/-- The length of a number in unary. -/
theorem length_unary (n : ℕ) : (unary n).length = n := List.length_replicate

/-- The parent that the solver hands to a callee at the level ℓ + 1: K = K_ℓ, g = g_ℓ, the solver's
λ and B, the lists of the pieces for λ, the direction, y and x. -/
theorem parentAt_readyOf (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ} (hl : hLev h = l + 1) (y x : ℕ) :
    parentAt (readyOf D x₀ h, y) x = mkParent D (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (hLam h) (hB h) (direction (readyOf D x₀ h, y)) y x := by
  have e : rG (readyOf D x₀ h) = Levels.Gen.g x₀ l := by
    simp only [rG, readyOf, hl, Nat.add_sub_cancel, length_unary, Levels.Gen.g]
  have e2 : (rHead (readyOf D x₀ h)).2 = (unary (hLam h), unary (hB h)) := by
    simp only [rHead, readyOf, hLam, hB, unary_length_eq]
  simp only [parentAt, mkParent, e, e2]
  simp only [readyOf, hl, Nat.add_sub_cancel, rLists]

/-- The tables W̃, made an oracle and read back, give the value of the clique of the groups. -/
theorem groupTables_value (D : PiecesCounted.Data) (c : ℕ) (p : Parent) (L : ℕ) (W : ℕ → List Bool → ℤ) : ∀ hK0 : 0 < pK p,
    (clique (pK p) L fun w => readTables (answersOf (pK p) L (groupTables D c p L W)) w.val).value =
      (Value.groupClique asked.under (netInput (patternNet D c (pG p) (pTr p) (pLam p) (pY p) W) (netP p) (netB c p)) (patternNet D c (pG p) (pTr p) (pLam p) (pY p) W) hK0 (pX p) L).value := by
  intro hK0
  rw [clique_readTables]
  refine clique_value_congr fun w z _ => ?_
  simp only [groupTables, w.2, dite_true]
  rfl

/-- **The value of a callee** with the parent (K, g, λ, B, the lists, tr, y, x) and the label length
L: the value of the (K, L)-clique of the groups of the grouping x of the network of the pattern y. -/
theorem child_value (D : PiecesCounted.Data) (c x₀ : ℕ) (Bound : Ctx → Prop) (a' : Ctx) (f : TableQuery → Option Ans) {K g lam B L y x : ℕ} {tr : Bool} (hK : Levels.Gen.K x₀ (cLev a') = K)
    (hp : parentOf a' = mkParent D K g lam B tr y x) (hL : cLam a' = L) (hK0 : 0 < K) :
    (spec D c x₀ Bound).val a' ((spec D c x₀ Bound).tab a' f) =
      .inl (Value.groupClique asked.under (netInput (patternNet D c g tr lam y (readTables f)) (g ^ 3 * lam) (bitsOne c g lam B)) (patternNet D c g tr lam y (readTables f)) hK0 x L).value := by
  have h := groupTables_value D c (mkParent D K g lam B tr y x) L (readTables f)
  unfold netP netB at h
  rw [show pK (mkParent D K g lam B tr y x) = K from length_unary K, show pG (mkParent D K g lam B tr y x) = g from length_unary g, show pLam (mkParent D K g lam B tr y x) = lam from length_unary lam,
    show pB (mkParent D K g lam B tr y x) = B from length_unary B, show pTr (mkParent D K g lam B tr y x) = tr from rfl, show pY (mkParent D K g lam B tr y x) = y from rfl,
    show pX (mkParent D K g lam B tr y x) = x from rfl] at h
  rw [← h hK0]
  show Sum.inl (clique (Levels.Gen.K x₀ (cLev a')) (cLam a') fun w => readTables (answersOf (pK (parentOf a')) (cLam a') (groupTables D c (parentOf a') (cLam a') (readTables f))) w.val).value = _
  rw [hp, hL, hK, show pK (mkParent D K g lam B tr y x) = K from length_unary K]

/-- A network on [g] with parameters P, B has |Z| ≤ 2^{gP + g²B}. -/
theorem Net.abs_value_le {g : ℕ} (N : Net g) {P B : ℕ} (h : N.Is P B) : |N.value| ≤ 2 ^ (g * P + g * g * B) := by
  unfold Net.value
  have hW : ∀ z ∈ Fintype.piFinset N.S, |∏ a, N.W a (z a)| ≤ (2 ^ B) ^ g := by
    intro z hz
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _a : Fin g, (2 : ℤ) ^ B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun a _ => (h.ii_W a _ (Fintype.mem_piFinset.1 hz a)).le
      _ = _ := by rw [Finset.prod_const, card_univ, Fintype.card_fin]
  have hΨ : ∀ z ∈ Fintype.piFinset N.S, |∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)| ≤ (2 ^ B) ^ #(pairs (Fin g)) := by
    intro z hz
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _p ∈ pairs (Fin g), (2 : ℤ) ^ B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun p hp =>
          (h.ii_Ψ _ _ (ne_of_lt (by simpa [pairs] using hp)) _ (Fintype.mem_piFinset.1 hz _) _ (Fintype.mem_piFinset.1 hz _)).le
      _ = ((2 : ℤ) ^ B) ^ #(pairs (Fin g)) := by rw [Finset.prod_const]
  have hS : (#(Fintype.piFinset N.S) : ℤ) ≤ (2 ^ P) ^ g := by
    rw [Fintype.card_piFinset]
    have h1 : ∀ a, #(N.S a) ≤ 2 ^ P := fun a => by
      have h2 : N.S a ⊆ words (N.len a) := fun z hz => mem_words.2 (h.len_S a z hz)
      calc #(N.S a) ≤ #(words (N.len a)) := Finset.card_le_card h2
        _ = 2 ^ N.len a := card_words _
        _ ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) (h.len_le a)
    have : ∏ a, #(N.S a) ≤ ∏ _a : Fin g, 2 ^ P := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun a _ => h1 a
    rw [Finset.prod_const, card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have hc := ClauseBound.Alg.Level.card_add_card_pairs_le (Fin g)
  rw [Fintype.card_fin] at hc
  calc _ ≤ ∑ z ∈ Fintype.piFinset N.S, |(∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ Fintype.piFinset N.S, ((2 : ℤ) ^ B) ^ g * ((2 : ℤ) ^ B) ^ #(pairs (Fin g)) := by
        refine Finset.sum_le_sum fun z hz => ?_
        rw [abs_mul]
        exact mul_le_mul (hW z hz) (hΨ z hz) (abs_nonneg _) (by positivity)
    _ = (#(Fintype.piFinset N.S) : ℤ) * (((2 : ℤ) ^ B) ^ g * ((2 : ℤ) ^ B) ^ #(pairs (Fin g))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ P) ^ g * (((2 : ℤ) ^ B) ^ g * ((2 : ℤ) ^ B) ^ #(pairs (Fin g))) := mul_le_mul_of_nonneg_right hS (by positivity)
    _ = 2 ^ (g * P + (g + #(pairs (Fin g))) * B) := by
        rw [← pow_add, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring
    _ ≤ 2 ^ (g * P + g * g * B) := pow_le_pow_right₀ (by norm_num) (by gcongr)

end ExplicitCost
