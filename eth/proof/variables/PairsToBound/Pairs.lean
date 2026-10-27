/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PairsToBound.Defs
public import GeneralPieces.Rec.Seq
import GeneralPieces.ThmRunningTime
import GeneralPieces.Rec.Chain
import GeneralPieces.Rec.Rate
import GeneralPieces.Rec.PartB
import GeneralPieces.Num.PartA
import GeneralPieces.Num.PartAUse
import GeneralPieces.Num.Asymptotic
import ClauseBound.Alg.Need

/-! # Theorem D (b) from Theorem D (a): the pairs of Appendix A

Sentences (1) to (4) of Step 6 of Appendix D, in the numbering of
proof/variables/PairsToBound/Defs.lean.

* `seq_of_rate`: the sequence of levels of the recursion of Appendix A, built as in
  `GeneralPieces.seq_of_pick`, but with the constant chosen first. There the constant C₀ is said to
  exist after the pieces; its proof takes the constant C of part (b) of Theorem A, which depends on
  c alone (`GeneralPieces.StRate2`), and puts C₀ = C + 10. Here that
  order is in the statement: for every c there is a C₀ that serves all programs with parameters (ρ,
  c) and P.m = 1, all ρ with 1/2 ≤ ρ < 1 and all x₀ ≥ 18 with 2^x₀ ≥ c + 5.
* `theRecursionHasLevels`: the same for pieces as Appendix A defines them
  (`AppRunningTime.IsPieces`), with the solver polynomial-time, K at the ℓ-th index equal to K_ℓ,
  and the level picked by the program of `pick_spec`.
* `thePairsSatisfyTheHypothesis`: the case ρ = 1/√2, x₀ = `GeneralPieces.x₀Of c`, with the fraction
  between e_ℓ and 2e_ℓ (`GeneralPieces.Between.between_half`, `GeneralPieces.Asymptotic.between`)
  and the precision ℓ + 1.
* `thetaOfThePairs`: the four inequalities are part (a) of Theorem A and two steps of its proof;
  with (1/√2)^ℓ = 1/√(2^ℓ) they give the two-sided bound. -/

public section

namespace PairsToBound

open Turing Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen GeneralPieces MainTheoremForms

/-! ### The sequence of levels, with a constant that depends on c alone -/

/-- Parts (a) and (b) of Theorem A as a sequence of levels, with the constant before the pieces,
from the statements `StChain2`, `StRate2`, `StSolveG2` and `StNeedG` taken as hypotheses. For every
c there is a C₀ such that for all programs P with parameters (ρ, c) and P.m = 1, 1/2 ≤ ρ < 1, every
x₀ ≥ 18 with 2^x₀ ≥ c + 5 and every program `pick` that finds the level, the solver made of P has a
sequence of levels for the numbers e_ℓ of display (40) with the
constant C₀, whose ℓ-th index is the schedule of display (40) and whose level is picked by `pick`.
The proof is that of `GeneralPieces.seq_of_pick`; C₀ = C + 10 for the C of part (b). -/
theorem seq_of_rate (hCh : StChain2) (hR : StRate2) (hSolve : ∀ P, StSolveG2 P) (hNeed : ∀ P, StNeedG P) (c : ℕ) :
    ∃ C₀ : ℕ, ∀ (P : PiecesF) (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
      ∀ pick : U → U × (List Step × U), PolyT pick → (∀ b, (pick b).2 = idx P x₀ (pick b).1.length) → (∀ b, K x₀ 0 ≤ b.length → K x₀ (pick b).1.length ≤ b.length) →
        (∀ b, b.length < K x₀ ((pick b).1.length + 1)) →
        ∃ Q : (solverOf P).Seq (e ρ x₀) C₀, (∀ l, Q.idx l = idx P x₀ l) ∧ Q.pick = pick := by
  obtain ⟨C, hC'⟩ := hR c
  refine ⟨C + 10, fun P ρ x₀ hρ hρ1 hP hm hx hx2 pick hp1 hp2 hp3 hp4 => ?_⟩
  have hC := hC' P ρ x₀ hρ hρ1 hP hm hx hx2
  have hK : ∀ l, (solverOf P).K (idx P x₀ l) = K x₀ l := topK_idx P x₀
  have hA := PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  refine ⟨{
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
    pick_max := fun b => by rw [hK]; exact hp4 b }, fun _ => rfl, rfl⟩
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

/-- «That its pairs satisfy the hypothesis of Theorem D (a) is checked in the proof of Theorem A
(c)» (Step 6 of Appendix D), for every ρ and x₀ of Theorem A, with a constant that depends on c
alone. -/
theorem theRecursionHasLevels : TheRecursionHasLevels := by
  intro c
  obtain ⟨C₀, hC⟩ := seq_of_rate Chain.stChain2 stRate2 solveG2 Need.stNeedG c
  refine ⟨C₀, fun ρ x₀ P A val h hx hx2 => ?_⟩
  obtain ⟨hP, hKeeps, hm⟩ := par_of_isPieces h
  obtain ⟨hp1, hp2, hp3, hp4⟩ := pick_spec (Tied.recOf P val c) x₀
  obtain ⟨Q, hQ, hpick⟩ := hC (Tied.recOf P val c) ρ x₀ h.rho_ge h.rho_lt hP hm hx hx2 _ hp1 hp2 hp3 hp4
  exact ⟨Q, solver_poly _ hKeeps, fun l => by rw [hQ, K_idx], hpick⟩

/-! ### ρ = 1/√2 -/

/-- 1/2 ≤ 1/√2 < 1. -/
theorem half_le_inv_sqrt_two : (1 : ℝ) / 2 ≤ 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 < 1 := by
  have h0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨one_div_le_one_div_of_le h0 (by nlinarith), ?_⟩
  rw [div_lt_one h0]
  nlinarith

/-- For 1/2 ≤ ρ < 1 and x₀ ≥ 18, ℓ ↦ ℓ + 1 is a precision for the numbers e_ℓ of display (40), by
part (a) of Theorem A. -/
theorem precision_succ {ρ : ℝ} {x₀ : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) : ∃ C : ℕ, Precision (e ρ x₀) RecursionWithPieces.prec C := by
  have hA := PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  obtain ⟨C, hC⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hρ1
  exact ⟨C + 1, by unfold RecursionWithPieces.prec; fun_prop, fun l => by simpa [RecursionWithPieces.prec] using PartAUse.inv_two_pow_le_e hA hρ l,
    fun l => by simpa [RecursionWithPieces.prec] using PartAUse.two_pow_le_div hA hρ hρ1 hC.le l⟩

/-- «The pairs (K_ℓ, e_ℓ) of (40), for the pieces of Appendix B, satisfy this hypothesis» (Theorem D
(b)), with constants that depend on c alone. -/
theorem thePairsSatisfyTheHypothesis : ThePairsSatisfyTheHypothesis := by
  intro c
  obtain ⟨C₀, hC⟩ := theRecursionHasLevels c
  obtain ⟨Cp, hCp⟩ := precision_succ half_le_inv_sqrt_two.1 half_le_inv_sqrt_two.2 (x₀Of_ge c)
  refine ⟨C₀, Cp, fun P₀ A val h => ?_⟩
  obtain ⟨Q, h1, h2, h3⟩ := hC _ _ P₀ A val h (x₀Of_ge c) (x₀Of_pow c)
  refine ⟨Q, h1, h2, h3, ⟨?_, fun l => ?_⟩, hCp⟩
  · exact Between.num_den_polyT.comp (PolyT.fst PolyT.id')
  · have hb := Between.between_half l
    simpa [fractionHalf] using Asymptotic.between (1 / Real.sqrt 2) (x₀Of c) l _ half_le_inv_sqrt_two.1 (x₀Of_ge c) hb.1 hb.2

/-! ### e_ℓ = Θ((log K_ℓ)^(−1/2)) -/

/-- For a > 0 and t > 0 with t² = p: if a·p ≤ L ≤ b·p, then √a/√L ≤ 1/t ≤ √b/√L. -/
theorem inv_between_sqrt {a b L t p : ℝ} (ha : 0 < a) (ht : 0 < t) (htp : t ^ 2 = p) (h1 : a * p ≤ L) (h2 : L ≤ b * p) :
    Real.sqrt a / Real.sqrt L ≤ 1 / t ∧ 1 / t ≤ Real.sqrt b / Real.sqrt L := by
  have hp : 0 < p := htp ▸ pow_pos ht 2
  have hL : 0 < L := lt_of_lt_of_le (mul_pos ha hp) h1
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hb : 0 ≤ b := by
    by_contra h
    have : b * p < 0 := mul_neg_of_neg_of_pos (not_le.1 h) hp
    linarith
  constructor
  · rw [div_le_div_iff₀ hsL ht, one_mul]
    refine Real.le_sqrt_of_sq_le ?_
    rw [mul_pow, Real.sq_sqrt ha.le, htp]
    exact h1
  · rw [div_le_div_iff₀ ht hsL, one_mul]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hb, htp]
    exact h2

/-- «By Theorem A (a) and its proof, ½ρ^ℓ ≤ e_ℓ ≤ 0.85ρ^ℓ and x₀2^ℓ ≤ log K_ℓ ≤ (3x₀+6)2^ℓ, so e_ℓ =
Θ((log K_ℓ)^(−1/2))» (Step 6 of Appendix D). -/
theorem thetaOfThePairs : ThetaOfThePairs := by
  intro x₀ l hx
  have hA := PartA.thmRunningTime_a (1 / Real.sqrt 2) x₀ half_le_inv_sqrt_two.1 half_le_inv_sqrt_two.2 hx
  have hlo : (x₀ : ℝ) * 2 ^ l ≤ lg (K x₀ l) := by
    unfold lg
    rw [PartA.logK_eq_x]
    have h' : ((2 ^ l * x₀ : ℕ) : ℝ) ≤ (x x₀ l : ℝ) := by exact_mod_cast PartA.x_ge_pow x₀ l
    push_cast at h'
    linarith
  have hhi : lg (K x₀ l) ≤ (3 * x₀ + 6) * 2 ^ l := by
    unfold lg
    rw [hA.logK]
    have h1 : (0 : ℝ) ≤ l := by positivity
    have h2 : (0 : ℝ) ≤ x₀ := by positivity
    linarith
  obtain ⟨he1, he2⟩ := hA.e_bounds l
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have htp : (Real.sqrt 2 ^ l) ^ 2 = 2 ^ l := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  have hx0 : (0 : ℝ) < x₀ := by exact_mod_cast (by omega : 0 < x₀)
  obtain ⟨g1, g2⟩ := inv_between_sqrt hx0 (pow_pos hs l) htp hlo hhi
  have hpow : (1 / Real.sqrt 2) ^ l = 1 / Real.sqrt 2 ^ l := by rw [div_pow, one_pow]
  refine ⟨he1, he2, hlo, hhi, ?_, ?_⟩
  · rw [hpow] at he1
    rw [mul_div_assoc]
    linarith
  · rw [hpow] at he2
    rw [mul_div_assoc]
    linarith

end PairsToBound
