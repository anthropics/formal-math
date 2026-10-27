/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Rec.Rate
public import ClauseBound.Gen.Seq
public import ClauseBound.Gen.Pick
public import ClauseBound.Alg.Need
import all ClauseBound.Gen.Pick

/-! # Parts (a) and (b) of the theorem on the general recursion as a clique solver with a sequence of indices, for every x₀ ≥ 18 with 2^x₀ ≥ c + 5

The index of level ℓ is the schedule of the steps from K_ℓ nodes down to K₀ nodes. Part (a) (K_ℓ <
K_{ℓ+1} ≤ K_ℓ^10, the bounds on e_ℓ) is `PartA.thmRunningTime_a`, used through `Num/PartAUse.lean`.
Part (b) has two halves: the
answer is right, by the statement on all levels under the hypotheses of case (ii) of the lemma on
groupings with explicit cost, because every step of the schedule is in order and a pad of
length 2^needG meets all budgets; and the exponent needG obeys the bound of part (b). As in Theorem
A of the paper, any such x₀ is allowed. -/

public section

namespace GeneralPieces

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen

/-- What the program `ClauseBound.Gen.Pick.pick` does: from a bound in unary, in polynomial time,
the largest ℓ with K_ℓ ≤ bound (ℓ = 0 if the bound is below K₀) and the schedule of display (40) for
that ℓ. This is `ClauseBound.Gen.Pick.stPick` with the program named. -/
theorem pick_spec (P : PiecesF) (x₀ : ℕ) : PolyT (Pick.pick P x₀) ∧ (∀ b, (Pick.pick P x₀ b).2 = idx P x₀ (Pick.pick P x₀ b).1.length) ∧
    (∀ b, K x₀ 0 ≤ b.length → K x₀ (Pick.pick P x₀ b).1.length ≤ b.length) ∧ ∀ b, b.length < K x₀ ((Pick.pick P x₀ b).1.length + 1) := by
  refine ⟨Pick.pick_polyT P x₀, fun b => ?_, fun b h0 => ?_, fun b => ?_⟩ <;>
    obtain ⟨l, h1, h2, h3, h4⟩ := Pick.rounds P x₀ b b.length le_rfl <;>
    have hl : Pick.loop P x₀ b = Pick.state P x₀ l := h1 <;>
    simp only [Pick.pick, hl, Pick.state, rep, List.length_replicate]
  · rfl
  · rcases h3 with rfl | h3
    · exact h0
    · exact h3
  · rcases h4 with h4 | h4
    · exact h4.trans_lt (Pick.lt_K_succ x₀ l)
    · exact h4

/-- The theorem on the general recursion, parts (a) and (b), in the form that the top levels use,
with a given program that picks the level. The constant is C₀ + 10 for the C₀ of part (b): the
fields `K_le` (K_{ℓ+1} ≤ K_ℓ^10) and `e_ge` want
it to be at least 10 and at least 1. -/
theorem seq_of_pick (hCh : StChain2) (hR : StRate2) (hSolve : ∀ P, StSolveG2 P) (hNeed : ∀ P, StNeedG P) (P : PiecesF) (ρ : ℝ) (c x₀ : ℕ)
    (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (hx2 : c + 5 ≤ 2 ^ x₀) (pick : U → U × (List Step × U)) (hp1 : PolyT pick)
    (hp2 : ∀ b, (pick b).2 = idx P x₀ (pick b).1.length) (hp3 : ∀ b, K x₀ 0 ≤ b.length → K x₀ (pick b).1.length ≤ b.length)
    (hp4 : ∀ b, b.length < K x₀ ((pick b).1.length + 1)) :
    ∃ C₀ : ℕ, ∃ Q : (solverOf P).Seq (e ρ x₀) C₀, (∀ l, Q.idx l = idx P x₀ l) ∧ Q.pick = pick := by
  obtain ⟨C, hC'⟩ := hR c
  have hC := hC' P ρ x₀ hρ hρ1 hP hm hx hx2
  have hK : ∀ l, (solverOf P).K (idx P x₀ l) = K x₀ l := topK_idx P x₀
  have hA := PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  refine ⟨C + 10, ⟨{
    idx := idx P x₀
    K_two := fun l => by rw [hK]; exact two_le_K x₀ l hx
    K_lt := fun l => by rw [hK, hK]; exact (hA.K_lt_le l).1
    K_le := fun l => by
      rw [hK, hK]
      exact (hA.K_lt_le l).2.trans (Nat.pow_le_pow_right (by have := two_le_K x₀ l hx; omega) (by omega))
    e_le := fun l => PartAUse.e_le_one hA (by linarith) hρ1.le l
    e_ge := fun l => by rw [hK]; exact PartAUse.inv_logK_pow_le_e hA hρ (by omega) l (C + 10) (by omega)
    correct := ?_
    rate := ?_
    pick := pick
    pick_poly := hp1
    pick_idx := hp2
    pick_le := fun b hb => by
      rw [hK] at hb
      rw [hp2, hK]
      exact hp3 b hb
    pick_max := fun b => by rw [hK]; exact hp4 b }, fun _ => rfl, rfl⟩⟩
  · rintro pad i lam B I ⟨l, rfl⟩ hlam hI hpad
    rw [hK] at hI ⊢
    have h1 : 2 ^ needG P (K x₀ l) lam B 1 1 (sched P x₀ l) ≤ pad.length := by
      rw [← topK_idx P x₀ l]
      simpa [solverOf, idx] using hpad
    have h2 := hSolve P pad (K x₀ 0) (sched P x₀ l) (K x₀ l) lam B I (hCh P ρ c x₀ hP hm hx hx2 l lam hlam)
      (hNeed P pad.length (K x₀ l) lam B 1 1 (sched P x₀ l) h1) hI
    simpa [solverOf, idx, rep] using h2
  · intro l lam B hlam hB
    rw [hK]
    have h1 : (solverOf P).need (idx P x₀ l, List.replicate lam (), List.replicate B ()) = needG P (K x₀ l) lam B 1 1 (sched P x₀ l) := by
      rw [← topK_idx P x₀ l]
      simp [solverOf, idx]
    rw [h1]
    refine (hC l lam B hlam hB).trans ?_
    have h2 : (1 : ℝ) ≤ (K x₀ l : ℝ) * ((lam : ℝ) + B) := by
      have a : (1 : ℝ) ≤ (K x₀ l : ℝ) := by have := two_le_K x₀ l hx; exact_mod_cast (by omega : 1 ≤ K x₀ l)
      have b : (1 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hlam
      have d : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h3 : 0 ≤ Real.logb 2 ((K x₀ l : ℝ) * ((lam : ℝ) + B)) := Real.logb_nonneg (by norm_num) h2
    have h4 : (C : ℝ) * (K x₀ l : ℝ) ^ 2 * Real.logb 2 ((K x₀ l : ℝ) * ((lam : ℝ) + B)) ≤
        ((C + 10 : ℕ) : ℝ) * (K x₀ l : ℝ) ^ 2 * Real.logb 2 ((K x₀ l : ℝ) * ((lam : ℝ) + B)) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) h3
      push_cast; linarith
    linarith

/-- The same from the five interface statements. -/
theorem stSeq2_of (hCh : StChain2) (hR : StRate2) (hPk : StPick) (hSolve : ∀ P, StSolveG2 P) (hNeed : ∀ P, StNeedG P) : StSeq2 := by
  intro P ρ c x₀ hρ hρ1 hP hm hx hx2
  obtain ⟨pick, hp1, hp2, hp3, hp4⟩ := hPk P x₀
  obtain ⟨C₀, Q, hQ, -⟩ := seq_of_pick hCh hR hSolve hNeed P ρ c x₀ hρ hρ1 hP hm hx hx2 pick hp1 hp2 hp3 hp4
  exact ⟨C₀, Q, hQ⟩

/-- The same from the two statements that are proved elsewhere: every step of the schedule is in
order, and all levels together give the value of the clique. -/
theorem stSeq2 (hChain : StChain2) (hSolve : ∀ P, StSolveG2 P) : StSeq2 :=
  stSeq2_of hChain stRate2 Pick.stPick hSolve Need.stNeedG

end GeneralPieces
