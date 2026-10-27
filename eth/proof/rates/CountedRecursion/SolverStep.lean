/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.SolverRoom
public import CountedRecursion.GridLemmas
import Mathlib.Tactic

/-! # The solver at a level ℓ + 1

Proof of Theorem A (b): the set 𝓘 and the numbers d, c^row_i, c^col_i are computed once, and each of
the following takes at most Ξ^{C₃} operations: finding the numbers c_{a,a'} and the totals of both
networks for one ι; adding one Z_ι; computing d^{|ℛ|} and dividing by it.
* `pieces_ask`: what the oracle of the pieces answers to a question about strings of λ bits, 1 ≤ λ ≤
  Λ.
* `division_exact`: «d^{|ℛ|}Z = Σ_ι Z_ι», so the division at the end returns Z.
* `solverStepOf`: the statement `SolverStep` from the numbers of the level, the expansion, the
  number |𝓘|^{|ℛ|} of functions ι : ℛ → 𝓘 (called patterns here), Lemma 8 up to the call with its L
  and «whose value is that of the network», the two networks, case (ii), the crude bounds and the
  rule of substitution. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- The oracle of the pieces, asked about strings of λ bits, 1 ≤ λ ≤ Λ. -/
theorem pieces_ask (D : PiecesCounted.Data) {Lam : ℕ} {u : List Unit} (h1 : 1 ≤ u.length) (h2 : u.length ≤ Lam) (q : PiecesCounted.Question) : piecesUpTo D Lam (u, q) = D.answer u.length q := by
  simp [piecesUpTo, PiecesCounted.Data.oracle, h1, h2]

/-- The question for c^row_i or c^col_i, i the element number j of 𝓘. -/
theorem pieces_cap (D : PiecesCounted.Data) (lam : ℕ) (tr : Bool) {j : ℕ} (hj : j < ((D.fam lam).I.sort).length) :
    D.answer lam (.inr (.inr (.inl (tr, ((D.fam lam).I.sort).getD j 0)))) = some (.inl (((((D.fam lam).I.sort).map fun i => D.cap lam tr i).getD j 0 : ℕ) : ℤ)) := by
  have h1 : ((D.fam lam).I.sort).getD j 0 ∈ (D.fam lam).I := indexAt_mem D lam (by rwa [length_sortI] at hj)
  rw [getD_map_of_lt (fun i => D.cap lam tr i) _ hj 0 0]
  exact if_pos h1

variable {ρ : ℝ} {c x₀ l : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}

/-- «Thus d^{|ℛ|}Z = Σ_ι Z_ι»: the sum of the Z_ι, divided by d^{|ℛ|}, is the value of the instance. -/
theorem division_exact (hExp : Expansion) (hS : Setting ρ c x₀ D) (Bound : Ctx → Prop) (hF : Fits x₀ a f) (hl : cLev a = l + 1) :
    (spec D c x₀ Bound).val a f = Sum.inl ((∑ y ∈ range (nPatterns (readyOf D x₀ a.1)), (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value) / (((rD (readyOf D x₀ a.1)).toNat ^ rRect (readyOf D x₀ a.1) : ℕ) : ℤ)) := by
  have hK2 := two_le_K (by have := hS.x₀_ge; omega : 1 ≤ x₀) l
  have hKg := K_le_g x₀ l
  have hE := hExp ρ c x₀ D hS (Levels.Gen.g x₀ l) (cLam a) (readTables f) (fun y => direction (readyOf D x₀ a.1, y)) (by omega) hF.1
  have hnP : nPatterns (readyOf D x₀ a.1) = #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := nPatterns_ready D x₀ a.1 hl
  have hdpos := hS.is.d_pos _ hF.1
  have hd : (((rD (readyOf D x₀ a.1)).toNat ^ rRect (readyOf D x₀ a.1) : ℕ) : ℤ) = (D.fam (cLam a)).d ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := by
    have h1 : rD (readyOf D x₀ a.1) = (D.fam (cLam a)).d := rfl
    have h2 : rRect (readyOf D x₀ a.1) = nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := by
      unfold rRect
      rw [rG_ready D x₀ a.1 hl]
    rw [h1, h2]
    push_cast
    rw [Int.toNat_of_nonneg (by omega)]
  rw [hnP, ← hE, hd, Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by omega))]
  show Sum.inl (clique (Levels.Gen.K x₀ (cLev a)) (cLam a) fun w => readTables f w.val).value = _
  rw [hl, K_succ_mul]

/-- **The solver at a level ℓ + 1.** -/
theorem solverStepOf : NumbersRun → Expansion → PatternsFew → GroupingWithCall → LabelLengthIsL → ValueIsKept → BothNetworks → CaseTwoApplies → CrudeBounds → QueryMachines.StSubstWithin → SolverStep := by
  intro hNum hExp hFew hGW hLL hV hBN hC2 hCr hSub c
  obtain ⟨Cn, hCn⟩ := hNum
  obtain ⟨Cg, hCg⟩ := pattern_run hGW hLL hV hBN hC2 hSub c
  obtain ⟨C, hC⟩ := solver_room hFew hCr c Cn Cg
  refine ⟨C, fun ρ x₀ D hS Bound a f l hF hl => ?_⟩
  obtain ⟨hroom, hc1, hc2⟩ := hC ρ x₀ D hS a l hF.1 hF.2.1 hl
  refine ⟨fun a' hCh => (child_size hLL hBN hS Bound hF hl a' hCh).trans (le_trans (by omega) hroom), fun tc tq Lam hLam => ?_⟩
  have hpat := hCg ρ x₀ D hS Bound a f l hF hl
  have h6 := sumAndDivide_within (c := c) (O := ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f)) (w := solPrices c tc tq) (r := readyOf D x₀ a.1) (Cg * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + (tc + 2)) ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg + (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + 2 * (2 * size (readyOf D x₀ a.1) + 2 * size (nPatterns (readyOf D x₀ a.1)) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + 2 * Levels.Gen.g x₀ l + 6 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) + 2 * bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 12)) (2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))))
    (fun y => (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value) (fun y hy => (hpat y hy).2 tc tq Lam) (fun y hy => (hpat y hy).1)
  have s5 : hLev a.1 - 1 = l := by
    have : hLev a.1 = l + 1 := hl
    omega
  have ht : a.1.1.tail = unary l := by
    rw [← unary_length_eq a.1.1.tail, List.length_tail]
    show unary (hLev a.1 - 1) = _
    rw [s5]
  have hN : (numbersM x₀).Runs a.1.1.tail (2 * l) (Cn * Levels.Gen.g x₀ l) (unary (2 ^ (3 * (hLev a.1 - 1) + x₀)), unary (Levels.Gen.K x₀ (hLev a.1 - 1))) := by
    rw [ht, s5]
    exact hCn x₀ l
  have hu1 : 1 ≤ a.1.2.1.length := hF.1
  have hu2 : a.1.2.1.length ≤ Lam := hLam
  have hlev : (levelSolver c x₀).Within ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (solPrices c tc tq) a.1 (2 * l + 5 + 2 * #(D.fam (cLam a)).I + (2 * #(D.fam (cLam a)).I + 2) * askCost c (cLam a) + (nPatterns (readyOf D x₀ a.1) * (Cg * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + (tc + 2) + 1) + 2)) (Cn * Levels.Gen.g x₀ l + 8 * size (readyOf D x₀ a.1) + (2 * size (readyOf D x₀ a.1) + size (nPatterns (readyOf D x₀ a.1)) + size (nPatterns (readyOf D x₀ a.1) * 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) + ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg + (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + 2 * (2 * size (readyOf D x₀ a.1) + 2 * size (nPatterns (readyOf D x₀ a.1)) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + 2 * Levels.Gen.g x₀ l + 6 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) + 2 * bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 12)) + 3) + 10) ((∑ y ∈ range (nPatterns (readyOf D x₀ a.1)), (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value) / (((rD (readyOf D x₀ a.1)).toNat ^ rRect (readyOf D x₀ a.1) : ℕ) : ℤ)) := by
    have hor : ∀ q, ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (Sum.inr (Sum.inr (a.1.2.1, q))) = D.answer (cLam a) q := fun q => pieces_ask D hu1 hu2 q
    have hI : ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (Sum.inr (Sum.inr (a.1.2.1, .inr (.inl ())))) = some (.inr (listsOf D (cLam a)).1) := hor _
    have hd : ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (Sum.inr (Sum.inr (a.1.2.1, .inl ()))) = some (.inl (D.fam (cLam a)).d) := hor _
    have h₀ : ∀ j < (listsOf D (cLam a)).1.length, ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (Sum.inr (Sum.inr (a.1.2.1, .inr (.inr (.inl (false, (listsOf D (cLam a)).1.getD j 0)))))) = some (.inl (((listsOf D (cLam a)).2.1.getD j 0 : ℕ) : ℤ)) :=
      fun j hj => (hor _).trans (pieces_cap D (cLam a) false hj)
    have h₁ : ∀ j < (listsOf D (cLam a)).1.length, ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (Sum.inr (Sum.inr (a.1.2.1, .inr (.inr (.inl (true, (listsOf D (cLam a)).1.getD j 0)))))) = some (.inl (((listsOf D (cLam a)).2.2.getD j 0 : ℕ) : ℤ)) :=
      fun j hj => (hor _).trans (pieces_cap D (cLam a) true hj)
    have hl₀ : (listsOf D (cLam a)).2.1.length = (listsOf D (cLam a)).1.length := List.length_map _
    have hl₁ : (listsOf D (cLam a)).2.2.length = (listsOf D (cLam a)).1.length := List.length_map _
    have hlen : (listsOf D (cLam a)).1.length = #(D.fam (cLam a)).I := Finset.length_sort _
    have h := levelSolver_within (c := c) (O := ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f)) (w := solPrices c tc tq) hN (listsOf D (cLam a)).1 (D.fam (cLam a)).d (listsOf D (cLam a)).2.1 (listsOf D (cLam a)).2.2 (askCost c (cLam a)) hI hd hl₀ hl₁ h₀ h₁ (fun _ => rfl) h6
    rw [hlen] at h
    exact h
  have hemp : a.1.1.isEmpty = false := by
    rcases h : a.1.1 with _ | ⟨u, t⟩
    · have h2 : a.1.1.length = l + 1 := hl
      rw [h] at h2
      exact absurd h2 (by simp)
    · rfl
  have hsol := mapOut_within (g := (Sum.inl : ℤ → Ans)) (mapIn_within (g := (Prod.fst : Ctx → Head)) (a := a) (ite_within_false (p := fun a : Head => a.1.isEmpty) (M := baseSolver x₀) hemp hlev))
  rw [division_exact hExp hS Bound hF hl]
  refine QueryMachine.Within.mono hsol ?_ ?_
  · have hnP : nPatterns (readyOf D x₀ a.1) = #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := nPatterns_ready D x₀ a.1 hl
    rw [hnP]
    have k1 : 1 ≤ Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l := Nat.one_le_pow _ _ (K_pos x₀ l)
    have k2 : (Cg + 3) * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l := Nat.mul_le_mul_right _ hc1
    have k3 : (Cg + 3) * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l = Cg * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + 3 * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l := by ring
    have k4 : #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) * (Cg * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + (tc + 2) + 1) ≤ #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) * (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + tc) := Nat.mul_le_mul_left _ (by omega)
    omega
  · exact le_trans (by omega) hroom

/-- `solverStepOf`, in the form of the statement `SolverStepFrom`. -/
theorem solverStepFrom : SolverStepFrom := solverStepOf

end ExplicitCost
