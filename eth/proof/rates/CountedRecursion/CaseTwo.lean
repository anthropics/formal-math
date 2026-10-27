/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.PatternPsi
import GeneralPieces.Rec.Chain
import Mathlib.Tactic

/-! # Case (ii) of Lemma 8 applies, and the lemma's L

Proof of Theorem A (b), the step from ℓ to ℓ + 1: so P = g³λ, gP = N, and moreover c_{a,a'} ≤ g²λ =
P/g. Case (ii) of Lemma 8 applies to the network with the smaller total (with B₁ in the role of B):
K divides g and 2ζ²g = 2^{ℓ+x₀−9}K, while 2gK ≤ g² = K_{ℓ+1} gives ln(2gK) ≤ 0.7·log K_{ℓ+1} ≤ 1.4(3x₀+6)2^ℓ,
and 1.4(3x₀+6) ≤ 2^{x₀−9} for x₀ ≥ 18. Also 1/g ≤ ζ, since ζg = 2^{2ℓ+x₀−5}K. So the lemma's L
satisfies K²L ≤ U + 2ζN + K² ≤ (ρ + 3ζ)N + (c/4)g⁴log(2λ) + K².
* `shared_le`: c_{a,a'} ≤ g²λ, for every g (`ClauseBound.Alg.GridNet.gridN_c_le`).
* `caseTwoApplies : CaseTwoApplies`: with `GeneralPieces.Chain.K_dvd_g` and
  `GeneralPieces.Chain.hoeffding_cond`, which is proved there from the sentences of the proof on
  2ζ²g and ln(2gK), one theorem for each.
* `label_first`: K²L ≤ U + 2ζN + K², for L = ⌈(U + 2ζgP)/K²⌉; `labelBound : LabelBound`: the whole
  display, with `GeneralPieces.Chain.inv_g_le_zeta`. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- ζ_ℓ as the machines have it, 1/2^{ℓ+5} with the power a natural number. -/
theorem zeta_cast (l : ℕ) : (1 : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ) = Levels.Gen.zeta l := by
  unfold Levels.Gen.zeta
  push_cast
  rfl

/-- «and moreover c_{a,a'} ≤ g²λ». -/
theorem shared_le {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) (g : ℕ) {lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ) (a b : Fin (nParts g g tr)) :
    (patternNet D c g tr lam y W).c a b ≤ g ^ 2 * lam := by
  have h := gridN_c_le (cutsOK_piecesOf hS hlam [()]) g g tr y (fun w θ => W w.val (List.ofFn θ).flatten) a b
  rw [nMemb_self] at h
  exact h.trans (le_of_eq (congrArg _ (Nat.one_mul lam)))

/-- **«Case (ii) of Lemma 8 applies to the network with the smaller total»**: to either network. -/
theorem caseTwoApplies : CaseTwoApplies := by
  intro ρ c x₀ D hS l lam y tr W hlam _
  have e : ((nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) tr : ℕ) : ℝ) = (Levels.Gen.g x₀ l : ℝ) := by rw [nParts_self]
  have hg0 : (0 : ℝ) < Levels.Gen.g x₀ l := by
    have h1 := ClauseBound.Gen.Rate.big_le_K hS.x₀_ge l
    have h2 := ClauseBound.Gen.Rate.K_le_g x₀ l
    exact_mod_cast (by omega : 0 < Levels.Gen.g x₀ l)
  refine Or.inr ⟨?_, fun a b _ => ?_, ?_⟩
  · -- «K divides g»
    rw [nParts_self]
    exact GeneralPieces.Chain.K_dvd_g x₀ l
  · -- «c_{a,a'} ≤ g²λ = P/g»
    rw [e, le_div_iff₀ hg0]
    have h : (patternNet D c (Levels.Gen.g x₀ l) tr lam y W).c a b * Levels.Gen.g x₀ l ≤ Levels.Gen.g x₀ l ^ 3 * lam := by
      calc _ ≤ Levels.Gen.g x₀ l ^ 2 * lam * Levels.Gen.g x₀ l := Nat.mul_le_mul_right _ (shared_le hS _ hlam y tr W a b)
        _ = Levels.Gen.g x₀ l ^ 3 * lam := by ring
    exact_mod_cast h
  · -- 2ζ²g ≥ K·ln(2gK)
    rw [e, zeta_cast]
    exact GeneralPieces.Chain.hoeffding_cond x₀ l hS.x₀_ge

/-- «K²L ≤ U + 2ζN + K²», for the lemma's L = ⌈(U + 2ζgP)/K²⌉, P = g³λ. -/
theorem label_first (x₀ l lam U : ℕ) :
    (Levels.Gen.K x₀ l : ℝ) ^ 2 * AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) U ≤
      U + 2 * Levels.Gen.zeta l * ((Levels.Gen.g x₀ l : ℝ) ^ 4 * lam) + (Levels.Gen.K x₀ l : ℝ) ^ 2 := by
  have hK : (0 : ℝ) < Levels.Gen.K x₀ l := by rw [ClauseBound.Gen.K_cast]; positivity
  have hz := ClauseBound.Gen.zeta_pos l
  unfold AppRunningTime.Lof
  rw [zeta_cast]
  have ht : 0 ≤ ((U : ℝ) + 2 * Levels.Gen.zeta l * Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * lam : ℕ) : ℝ)) / (Levels.Gen.K x₀ l : ℝ) ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one ht).le (by positivity : 0 ≤ (Levels.Gen.K x₀ l : ℝ) ^ 2)
  refine h1.trans (le_of_eq ?_)
  push_cast
  field_simp

/-- **«So the lemma's L satisfies K²L ≤ U + 2ζN + K² ≤ (ρ + 3ζ)N + (c/4)g⁴log(2λ) + K².»** -/
theorem labelBound : LabelBound := by
  intro ρ c x₀ l lam U _ hx _ hU
  have h1 := label_first x₀ l lam U
  have h3 : (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam * (1 / Levels.Gen.g x₀ l) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam * Levels.Gen.zeta l :=
    mul_le_mul_of_nonneg_left (GeneralPieces.Chain.inv_g_le_zeta x₀ l hx) (by positivity)
  linarith

end ExplicitCost
