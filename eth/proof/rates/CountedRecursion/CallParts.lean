/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.CliqueReads
import ClauseBound.Gen.Seq
import ClauseBound.Gen.Pick
import Mathlib.Tactic

/-! # The parts of the context of a call

Plain facts about the data that the solver hands to a callee, with no machine and no mathematics of
the networks:
* the row network and the column network of the g × g grid have g nodes (`nParts_self`, in
  proof/rates/CountedRecursion/SquareGrid.lean);
* `rK_readyOf`, `rG_readyOf`, `nPatterns_readyOf`: what the solver holds at the level ℓ + 1 when the
  loop over the patterns begins: K_ℓ, g_ℓ and the number |𝓘|^{|ℛ|} of patterns; `total_direction`:
  the network that it takes has the smaller total;
* `answersOf_readTables`, `answersOf_some`, `fits_succ`: the tables read back from the oracle of a
  well-formed instance are its tables, on settings;
* `groupTables_mkParent`: the tables W̃ of the callee, written with the numbers of the parent. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- K_ℓ ≥ 2, K_ℓ ≤ g_ℓ, g_ℓ ≥ 2. -/
theorem level_numbers {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) : 2 ≤ Levels.Gen.K x₀ l ∧ Levels.Gen.K x₀ l ≤ Levels.Gen.g x₀ l ∧ 2 ≤ Levels.Gen.g x₀ l :=
  ⟨ClauseBound.Gen.Seq.two_le_K x₀ l hx, ClauseBound.Gen.Pick.K_le_g x₀ l, (ClauseBound.Gen.Seq.two_le_K x₀ l hx).trans (ClauseBound.Gen.Pick.K_le_g x₀ l)⟩

/-! ### What the solver holds -/

section Ready

variable (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ}

/-- The K that the solver holds at the level ℓ + 1 is K_ℓ. -/
theorem rK_readyOf (hl : hLev h = l + 1) : rK (readyOf D x₀ h) = Levels.Gen.K x₀ l := by
  have e : hLev h - 1 = l := by omega
  change (unary (Levels.Gen.K x₀ (hLev h - 1))).length = _
  rw [e, length_unary]

/-- The g that the solver holds at the level ℓ + 1 is g_ℓ. -/
theorem rG_readyOf (hl : hLev h = l + 1) : rG (readyOf D x₀ h) = Levels.Gen.g x₀ l := by
  have e : hLev h - 1 = l := by omega
  change (unary (2 ^ (3 * (hLev h - 1) + x₀))).length * (unary (Levels.Gen.K x₀ (hLev h - 1))).length = _
  rw [e, length_unary, length_unary]
  rfl

/-- The number of patterns is |𝓘|^{|ℛ|}. -/
theorem nPatterns_readyOf (hl : hLev h = l + 1) : nPatterns (readyOf D x₀ h) = #(D.fam (hLam h)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := by
  unfold nPatterns rRect
  rw [rG_readyOf D x₀ h hl]
  change ((D.fam (hLam h)).I.sort).length ^ _ = _
  rw [Finset.length_sort]

/-- «the network with the smaller total»: its total is the smaller of the two. -/
theorem total_direction (hl : hLev h = l + 1) (y : ℕ) :
    totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ h, y)) 0 (hLam h) y =
      min (totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) false 0 (hLam h) y) (totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) true 0 (hLam h) y) := by
  have e : direction (readyOf D x₀ h, y) = decide (totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) true 0 (hLam h) y <
      totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) false 0 (hLam h) y) := by
    unfold direction
    rw [rG_readyOf D x₀ h hl]
    rfl
  rw [e]
  by_cases hlt : totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) true 0 (hLam h) y < totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) false 0 (hLam h) y
  · rw [decide_eq_true hlt, min_eq_right hlt.le]
  · rw [decide_eq_false hlt, min_eq_left (not_lt.1 hlt)]

end Ready

/-! ### Tables and oracles -/

/-- The oracle reads the tables only on settings. -/
theorem answersOf_congr {K lam : ℕ} {W W' : ℕ → List Bool → ℤ} (h : ∀ w < K, ∀ z ∈ words ((K - 1) * lam), W w z = W' w z) : answersOf K lam W = answersOf K lam W' := by
  funext q
  unfold answersOf tables
  by_cases hq : q.1 < K ∧ q.2.length = (K - 1) * lam
  · rw [if_pos hq, if_pos hq, h q.1 hq.1 q.2 (mem_words.2 hq.2)]
  · rw [if_neg hq, if_neg hq]

/-- The oracle of the tables read back from an oracle of tables is that oracle. -/
theorem answersOf_readTables (K lam : ℕ) (W : ℕ → List Bool → ℤ) : answersOf K lam (readTables (answersOf K lam W)) = answersOf K lam W :=
  answersOf_congr fun _ hw _ hz => readTables_setting W hw (mem_words.1 hz)

/-- An answer of the oracle: the query names a node and a setting, and the answer is the entry. -/
theorem answersOf_some {K lam : ℕ} {W : ℕ → List Bool → ℤ} {q : TableQuery} {v : Ans} (h : answersOf K lam W q = some v) : q.1 < K ∧ q.2 ∈ words ((K - 1) * lam) ∧ v = .inl (W q.1 q.2) := by
  unfold answersOf tables at h
  by_cases hq : q.1 < K ∧ q.2.length = (K - 1) * lam
  · rw [if_pos hq] at h
    exact ⟨hq.1, mem_words.2 hq.2, (Option.some.inj h).symm⟩
  · rw [if_neg hq] at h
    exact absurd h (by simp)

/-- A well-formed instance of the level ℓ + 1: λ, B ≥ 1, the tables read from its oracle are below
2^B on the settings of the clique on g_ℓ·g_ℓ nodes, and the oracle is the oracle of these tables. -/
theorem fits_succ {x₀ l : ℕ} {a : Ctx} {f : TableQuery → Option Ans} (hF : Fits x₀ a f) (hl : cLev a = l + 1) :
    1 ≤ cLam a ∧ 1 ≤ cB a ∧ (∀ w < Levels.Gen.g x₀ l * Levels.Gen.g x₀ l, ∀ z ∈ words ((Levels.Gen.g x₀ l * Levels.Gen.g x₀ l - 1) * cLam a), |readTables f w z| < 2 ^ cB a) ∧
      f = answersOf (Levels.Gen.g x₀ l * Levels.Gen.g x₀ l) (cLam a) (readTables f) := by
  obtain ⟨h1, h2, W, hW, rfl⟩ := hF
  have e : Levels.Gen.K x₀ (cLev a) = Levels.Gen.g x₀ l * Levels.Gen.g x₀ l := by
    rw [hl]
    exact sq (Levels.Gen.g x₀ l)
  rw [e] at hW ⊢
  refine ⟨h1, h2, fun w hw z hz => ?_, (answersOf_readTables _ _ _).symm⟩
  rw [readTables_setting _ hw (mem_words.1 hz)]
  exact hW w hw z hz

/-- The tables W̃ of the callee, written with the numbers of the parent. -/
theorem groupTables_mkParent (D : PiecesCounted.Data) (c K g lam B : ℕ) (tr : Bool) (y x L : ℕ) (W : ℕ → List Bool → ℤ) :
    groupTables D c (mkParent D K g lam B tr y x) L W = fun γ Θ => if h : γ < K then
      (Value.groupClique asked.under (netInput (patternNet D c g tr lam y W) (g ^ 3 * lam) (bitsOne c g lam B)) (patternNet D c g tr lam y W) (Nat.zero_lt_of_lt h) x L).W ⟨γ, h⟩ Θ else 0 := by
  have key : ∀ K' g' lam' B' : ℕ, K' = K → g' = g → lam' = lam → B' = B →
      (fun (γ : ℕ) (Θ : List Bool) => if h : γ < K' then
        (Value.groupClique asked.under (netInput (patternNet D c g' tr lam' y W) (g' ^ 3 * lam') (bitsOne c g' lam' B')) (patternNet D c g' tr lam' y W) (Nat.zero_lt_of_lt h) x L).W ⟨γ, h⟩ Θ else 0) =
      fun γ Θ => if h : γ < K then
        (Value.groupClique asked.under (netInput (patternNet D c g tr lam y W) (g ^ 3 * lam) (bitsOne c g lam B)) (patternNet D c g tr lam y W) (Nat.zero_lt_of_lt h) x L).W ⟨γ, h⟩ Θ else 0 := by
    rintro _ _ _ _ rfl rfl rfl rfl
    rfl
  exact key _ _ _ _ (length_unary K) (length_unary g) (length_unary lam) (length_unary B)

end ExplicitCost
