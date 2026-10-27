/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.SolverPattern
import Mathlib.Tactic

/-! # The solver and the procedure meet the specification

`Tower.Spec.Meets` indexes the costs by the depth alone, while the label length of a callee depends
on the pattern. So the statements on one instance (`SolverBase`, `SolverStep`, `ProcedureCost`,
`ChildIsGood`) are taken at the bounds Λ_j, 𝔅_j that λ and B obey along the recursion from one
outermost instance (`boundsDown`): every bound grows with λ and B.
* `lamAt_step`, `bitsAt_step`: the bounds of the depth j from those of the depth j + 1.
* `bitsOne_mono`, `bitsOut_mono`, `askCost_mono`, `Xi_mono`: monotonicity.
* `room_term_le`: (K_i(λ' + B'))^{C'} is within `roomAll`, for an instance of the depth i within the
  bounds.
* `child_inBounds`: a callee is within the bounds.
* `recursionMeetsFrom`. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

variable {ρ : ℝ} {c x₀ l lam B j : ℕ}

/-- Λ_j from Λ_{j+1}. -/
theorem lamAt_step (ρ : ℝ) (c x₀ lam B : ℕ) (h : j < l) : lamAt ρ c x₀ l lam B j =
    ⌊((ρ + 3 * Levels.Gen.zeta j) * ((Levels.Gen.g x₀ j : ℝ) ^ 4 * lamAt ρ c x₀ l lam B (j + 1)) + (c : ℝ) / 4 * (Levels.Gen.g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) + (Levels.Gen.K x₀ j : ℝ) ^ 2) / (Levels.Gen.K x₀ j : ℝ) ^ 2⌋₊ := by
  have e : l - j = (l - (j + 1)) + 1 := by omega
  have e2 : l - (l - (j + 1) + 1) = j := by omega
  unfold lamAt
  rw [e]
  simp only [boundsDown, e2]

/-- 𝔅_j from Λ_{j+1} and 𝔅_{j+1}. -/
theorem bitsAt_step (ρ : ℝ) (c x₀ lam B : ℕ) (h : j < l) : bitsAt ρ c x₀ l lam B j = bitsOut (Levels.Gen.K x₀ j) (Levels.Gen.g x₀ j) (Levels.Gen.g x₀ j ^ 3 * lamAt ρ c x₀ l lam B (j + 1)) (bitsOne c (Levels.Gen.g x₀ j) (lamAt ρ c x₀ l lam B (j + 1)) (bitsAt ρ c x₀ l lam B (j + 1))) := by
  have e : l - j = (l - (j + 1)) + 1 := by omega
  have e2 : l - (l - (j + 1) + 1) = j := by omega
  unfold bitsAt lamAt
  rw [e]
  simp only [boundsDown, e2]

/-- B₁ grows with λ and B. -/
theorem bitsOne_mono (c g : ℕ) {u u' v v' : ℕ} (h1 : u ≤ u') (h2 : v ≤ v') : bitsOne c g u v ≤ bitsOne c g u' v' :=
  Nat.add_le_add (Nat.mul_le_mul_left _ h2) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ h1) _))

/-- B' grows with P and B₁. -/
theorem bitsOut_mono (K g : ℕ) {u u' v v' : ℕ} (h1 : u ≤ u') (h2 : v ≤ v') : bitsOut K g u v ≤ bitsOut K g u' v' :=
  Nat.add_le_add (Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)) _)) (Nat.mul_le_mul_left _ h2)

/-- The price of a query to the pieces grows with λ. -/
theorem askCost_mono (c : ℕ) {u u' : ℕ} (h : u ≤ u') : askCost c u ≤ askCost c u' :=
  Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h)) _

/-- Ξ grows with λ and B. -/
theorem Xi_mono (g : ℕ) {u u' v v' : ℕ} (h1 : u ≤ u') (h2 : v ≤ v') : Xi g u v ≤ Xi g u' v' := Nat.mul_le_mul_left _ (Nat.add_le_add h1 h2)

/-- Ξ = K_{j+1}(λ + B). -/
theorem Xi_eq (x₀ j u v : ℕ) : Xi (Levels.Gen.g x₀ j) u v = Levels.Gen.K x₀ (j + 1) * (u + v) := by rw [K_succ_mul, Xi, sq]

/-- A power of K_i(λ' + B'), for λ' and B' within the bounds of the depth i ≤ ℓ, is within the room
for all depths. -/
theorem room_term_le (ρ : ℝ) (c x₀ lam B : ℕ) {C C' i u v : ℕ} (hC : C' ≤ C) (hi : i ≤ l) (h1 : 1 ≤ u) (hu : u ≤ lamAt ρ c x₀ l lam B i) (hv : v ≤ bitsAt ρ c x₀ l lam B i) : (Levels.Gen.K x₀ i * (u + v)) ^ C' ≤ roomAll C ρ c x₀ l lam B := by
  have hK := K_pos x₀ i
  have hb : 1 ≤ Levels.Gen.K x₀ i * (lamAt ρ c x₀ l lam B i + bitsAt ρ c x₀ l lam B i) := Nat.mul_pos hK (by omega)
  calc (Levels.Gen.K x₀ i * (u + v)) ^ C' ≤ (Levels.Gen.K x₀ i * (lamAt ρ c x₀ l lam B i + bitsAt ρ c x₀ l lam B i)) ^ C' := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.add_le_add hu hv)) _
    _ ≤ (Levels.Gen.K x₀ i * (lamAt ρ c x₀ l lam B i + bitsAt ρ c x₀ l lam B i)) ^ C := Nat.pow_le_pow_right hb hC
    _ ≤ roomAll C ρ c x₀ l lam B := Finset.single_le_sum (f := fun j => (Levels.Gen.K x₀ j * (lamAt ρ c x₀ l lam B j + bitsAt ρ c x₀ l lam B j)) ^ C) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))

/-- Λ_i is at most the largest label length. -/
theorem lamAt_le_max (ρ : ℝ) (c x₀ lam B : ℕ) {i : ℕ} (hi : i ≤ l) : lamAt ρ c x₀ l lam B i ≤ lamMax ρ c x₀ l lam B :=
  Finset.le_sup (f := fun j => lamAt ρ c x₀ l lam B j) (Finset.mem_range.2 (by omega))

/-- A callee of an instance within the bounds is within the bounds. -/
theorem child_inBounds {a a' : Ctx} (hρ : 1 / 2 ≤ ρ) (hIn : InBounds ρ c x₀ l lam B a) (h1 : 1 ≤ cLam a) (hj : cLev a = j + 1) (hj' : cLev a' = j)
    (hL : (Levels.Gen.K x₀ j : ℝ) ^ 2 * cLam a' ≤ (ρ + 3 * Levels.Gen.zeta j) * ((Levels.Gen.g x₀ j : ℝ) ^ 4 * cLam a) + (c : ℝ) / 4 * (Levels.Gen.g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * cLam a) + (Levels.Gen.K x₀ j : ℝ) ^ 2)
    (hB : cB a' = bitsOut (Levels.Gen.K x₀ j) (Levels.Gen.g x₀ j) (Levels.Gen.g x₀ j ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ j) (cLam a) (cB a))) : InBounds ρ c x₀ l lam B a' := by
  obtain ⟨i1, i2, i3⟩ := hIn
  rw [hj] at i1 i2 i3
  have hjl : j < l := by omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [hj', lamAt_step ρ c x₀ lam B hjl]
    have hK : (0 : ℝ) < (Levels.Gen.K x₀ j : ℝ) ^ 2 := by
      have := K_pos x₀ j
      positivity
    refine Nat.le_floor ((le_div_iff₀ hK).2 ?_)
    have hz : (0 : ℝ) ≤ Levels.Gen.zeta j := by unfold Levels.Gen.zeta; positivity
    have c1 : (cLam a : ℝ) ≤ lamAt ρ c x₀ l lam B (j + 1) := by exact_mod_cast i2
    have c0 : (1 : ℝ) ≤ cLam a := by exact_mod_cast h1
    have hlog : Real.logb 2 (2 * cLam a) ≤ Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) := Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
    have m1 : (ρ + 3 * Levels.Gen.zeta j) * ((Levels.Gen.g x₀ j : ℝ) ^ 4 * cLam a) ≤ (ρ + 3 * Levels.Gen.zeta j) * ((Levels.Gen.g x₀ j : ℝ) ^ 4 * lamAt ρ c x₀ l lam B (j + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c1 (by positivity)) (by linarith)
    have m2 : (c : ℝ) / 4 * (Levels.Gen.g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * cLam a) ≤ (c : ℝ) / 4 * (Levels.Gen.g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) := mul_le_mul_of_nonneg_left hlog (by positivity)
    linarith
  · rw [hj', hB, bitsAt_step ρ c x₀ lam B hjl]
    exact bitsOut_mono _ _ (Nat.mul_le_mul_left _ i2) (bitsOne_mono _ _ i2 i3)

/-- **The solver and the procedure meet the specification.** From the statements on one instance
(`SolverBase`, `SolverStep`, `ProcedureCost`, `ChildIsGood`), taken at the bounds Λ_j, 𝔅_j, the
solver and the procedure meet `Tower.Spec.Meets`, with costs that depend on the depth alone. -/
theorem recursionMeetsFrom : RecursionMeetsFrom := by
  intro hBase hStep hProc hChild c
  obtain ⟨C₅, h5⟩ := hBase
  obtain ⟨C₃, h3⟩ := hStep c
  obtain ⟨Cp, hp⟩ := hProc c
  refine ⟨C₅ + C₃ + Cp, fun ρ x₀ D hS l lam B _ _ => ?_⟩
  have lev : ∀ (a : Ctx) (f : TableQuery → Option Ans) (a' : Ctx), (spec D c x₀ (InBounds ρ c x₀ l lam B)).Child a f a' → ∃ j, cLev a = j + 1 := fun a _ _ h => ⟨cLev a - 1, by have := h.1; omega⟩
  refine ⟨fun a f a' hG hC => ?_, fun a f a' hG hC => ?_, fun a f a' hG hC => ?_, fun a f hG tc tq => ?_, fun a f a' hG hC q v hq tq => ?_⟩
  · obtain ⟨j, hj⟩ := lev _ _ _ hC
    have h := (hChild ρ c x₀ D hS _ a a' f j hG.2 hj hC).1
    show cLev a' + 1 = cLev a
    omega
  · obtain ⟨j, hj⟩ := lev _ _ _ hC
    obtain ⟨g1, g2, -, -, g5, g6⟩ := hChild ρ c x₀ D hS _ a a' f j hG.2 hj hC
    exact ⟨child_inBounds hS.is.rho_ge hG.1 hG.2.1 hj g1 g5 g6, g2⟩
  · obtain ⟨j, hj⟩ := lev _ _ _ hC
    obtain ⟨i1, i2, i3⟩ := hG.1
    rw [hj] at i1 i2 i3
    refine ((h3 ρ x₀ D hS _ a f j hG.2 hj).1 a' hC).trans ?_
    rw [Xi_eq]
    exact room_term_le ρ c x₀ lam B (by omega) i1 hG.2.1 i2 i3
  · obtain ⟨i1, i2, i3⟩ := hG.1
    show (solver c x₀).Within _ (solPrices c tc tq) a (solverCost (C₅ + C₃ + Cp) ρ c x₀ l lam B (cLev a) tc tq) _ _
    rcases hj : cLev a with _ | j
    · rw [hj] at i1 i2 i3
      refine (h5 D c x₀ _ _ a f hG.2 hj tc tq).mono ?_ (room_term_le (i := 0) ρ c x₀ lam B (by omega) i1 hG.2.1 i2 i3)
      have hE : 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * cLam a) ≤ 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ i2)
      calc 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * cLam a) * (2 ^ x₀ * (tq + 1) + 1) ≤ 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) * (2 ^ x₀ * (tq + 1) + 1) := Nat.mul_le_mul_right _ hE
        _ = solverCost (C₅ + C₃ + Cp) ρ c x₀ l lam B 0 tc tq := by
          simp only [solverCost, Tower.shapeS, solverOwn, solverCalls, solverAsks]
          ring
    · rw [hj] at i1 i2 i3
      have hX : Xi (Levels.Gen.g x₀ j) (cLam a) (cB a) ^ C₃ ≤ xiAt ρ c x₀ l lam B j ^ (C₅ + C₃ + Cp) := by
        have hb : 1 ≤ xiAt ρ c x₀ l lam B j := by
          have h1 := K_pos x₀ (j + 1)
          have h2 := hG.2.1
          unfold xiAt
          rw [Xi_eq]
          exact Nat.mul_pos h1 (by omega)
        exact (Nat.pow_le_pow_left (Xi_mono _ i2 i3) _).trans (Nat.pow_le_pow_right hb (by omega))
      refine ((h3 ρ x₀ D hS _ a f j hG.2 hj).2 tc tq _ (i2.trans (lamAt_le_max ρ c x₀ lam B i1))).mono ?_ ?_
      · have hI : #(D.fam (cLam a)).I ≤ (2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c := (hS.is.card _ hG.2.1).trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ i2) _)
        have hP : #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ j) (Levels.Gen.g x₀ j) ≤ patternsAt ρ c x₀ l lam B j := Nat.pow_le_pow_left hI _
        have hA := askCost_mono c i2
        calc #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ j) (Levels.Gen.g x₀ j) * (Xi (Levels.Gen.g x₀ j) (cLam a) (cB a) ^ C₃ * Levels.Gen.K x₀ j ^ Levels.Gen.g x₀ j + tc) + (2 * #(D.fam (cLam a)).I + 2) * askCost c (cLam a) + Xi (Levels.Gen.g x₀ j) (cLam a) (cB a) ^ C₃
            ≤ patternsAt ρ c x₀ l lam B j * (xiAt ρ c x₀ l lam B j ^ (C₅ + C₃ + Cp) * Levels.Gen.K x₀ j ^ Levels.Gen.g x₀ j + tc) + (2 * (2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c + 2) * askCost c (lamAt ρ c x₀ l lam B (j + 1)) + xiAt ρ c x₀ l lam B j ^ (C₅ + C₃ + Cp) :=
              Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hP (Nat.add_le_add_right (Nat.mul_le_mul_right _ hX) _)) (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left _ hI) _) hA)) hX
          _ = solverCost (C₅ + C₃ + Cp) ρ c x₀ l lam B (j + 1) tc tq := by
            simp only [solverCost, Tower.shapeS, solverOwn, solverCalls, solverAsks]
            ring
      · rw [Xi_eq]
        exact room_term_le ρ c x₀ lam B (by omega) i1 hG.2.1 i2 i3
  · obtain ⟨j, hj⟩ := lev _ _ _ hC
    obtain ⟨i1, i2, i3⟩ := hG.1
    rw [hj] at i1 i2 i3
    have hj' : cLev a' = j := (hChild ρ c x₀ D hS _ a a' f j hG.2 hj hC).1
    show (procedure c).Within _ (upPrices c tq) (a', q) (entryCost (C₅ + C₃ + Cp) ρ c x₀ l lam B (cLev a') tq) _ _
    rw [hj']
    have hX : Xi (Levels.Gen.g x₀ j) (cLam a) (cB a) ^ Cp ≤ xiAt ρ c x₀ l lam B j ^ (C₅ + C₃ + Cp) := by
      have hb : 1 ≤ xiAt ρ c x₀ l lam B j := by
        have h1 := K_pos x₀ (j + 1)
        have h2 := hG.2.1
        unfold xiAt
        rw [Xi_eq]
        exact Nat.mul_pos h1 (by omega)
      exact (Nat.pow_le_pow_left (Xi_mono _ i2 i3) _).trans (Nat.pow_le_pow_right hb (by omega))
    refine (hp ρ x₀ D hS _ a a' f j hG.2 hj hC q v hq tq _ (i2.trans (lamAt_le_max ρ c x₀ lam B i1))).mono ?_ ?_
    · have hA := askCost_mono c i2
      have hE : 2 ^ (Levels.Gen.g x₀ j ^ 3 * cLam a * (2 * Levels.Gen.g x₀ j / Levels.Gen.K x₀ j)) ≤ 2 ^ (Levels.Gen.g x₀ j ^ 3 * lamAt ρ c x₀ l lam B (j + 1) * (2 * Levels.Gen.g x₀ j / Levels.Gen.K x₀ j)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ i2))
      calc 2 ^ (Levels.Gen.g x₀ j ^ 3 * cLam a * (2 * Levels.Gen.g x₀ j / Levels.Gen.K x₀ j)) * ((askCost c (cLam a) + tq) * Xi (Levels.Gen.g x₀ j) (cLam a) (cB a) ^ Cp)
          ≤ 2 ^ (Levels.Gen.g x₀ j ^ 3 * lamAt ρ c x₀ l lam B (j + 1) * (2 * Levels.Gen.g x₀ j / Levels.Gen.K x₀ j)) * ((askCost c (lamAt ρ c x₀ l lam B (j + 1)) + tq) * xiAt ρ c x₀ l lam B j ^ (C₅ + C₃ + Cp)) :=
            Nat.mul_le_mul hE (Nat.mul_le_mul (Nat.add_le_add_right hA _) hX)
        _ = entryCost (C₅ + C₃ + Cp) ρ c x₀ l lam B j tq := by
          simp only [entryCost, Tower.shapeI, entryOwn, entryAsks]
          ring
    · rw [Xi_eq]
      exact room_term_le ρ c x₀ lam B (by omega) i1 hG.2.1 i2 i3

end ExplicitCost
