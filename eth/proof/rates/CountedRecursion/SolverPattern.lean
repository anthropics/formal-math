/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.CliqueReads
public import CountedRecursion.SolverStages
public import CountedRecursion.LevelNumbers
public import Printed.GroupingEntry
import Mathlib.Tactic

/-! # One pattern (a pattern is one function ι : ℛ → 𝓘 of the proof of Theorem A(b), numbered by y < |𝓘|^{|ℛ|})

«Case (ii) of Lemma 8 applies to the network with the smaller total»: `patternValue c` is the
procedure of that lemma up to the call (`groupingCall`), and its call is passed on as a call of the
solver.
* `patternValue_within`: the rule of substitution (`QueryMachines.StSubstWithin`) for this machine:
  the call costs two operations more.
* `K_succ_mul`, `two_le_K`, `rK_ready`, `rG_ready`, `nPatterns_ready`, `tables_lt`: the numbers of a
  level, and what the solver holds when the loop begins.
* `pattern_input`: what the solver hands to the procedure is the input that belongs to ζ = 2^{−ℓ−5},
  K_ℓ and the network of the pattern; the label length that the procedure computes is the L of the
  lemma, and L ≤ 3gP.
The context of the call written out (`child_eq`) and the run for one pattern (`pattern_run`) are in
SolverCall.lean. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- The call of the procedure of the lemma is passed on as a call of the solver, at two operations
more. -/
theorem patternValue_within (hSub : QueryMachines.StSubstWithin) {c : ℕ} {O : SolQuery → Option Ans} {w : SolQuery → ℕ} {v : Ready × ℕ} {x tc T Sg : ℕ} {Z Zc : ℤ}
    (hG : ∀ O' : CliqueCall → Option ℤ, O' (callOf (searchInput c v, x)) = some Zc → groupingCall.Within O' (fun _ => tc + 2) (searchInput c v) T Sg Z)
    (hO : O (Sum.inl (child (v, callOf (searchInput c v, x)))) = some (.inl Zc)) (hw : w (Sum.inl (child (v, callOf (searchInput c v, x)))) = tc) :
    (patternValue c).Within O w v T (size v + Sg + (max (size (v, callOf (searchInput c v, x))) (size (Sum.inl Zc : Ans)) + 1) + 1) Z := by
  classical
  refine mapIn_within (g := fun v : Ready × ℕ => (v, searchInput c v)) ?_
  refine hSub CliqueCall ℤ SolQuery Ans (Ready × ℕ) GroupingInput ℤ groupingCall (askInt fun z : (Ready × ℕ) × CliqueCall => (Sum.inl (child z) : SolQuery))
    (fun z => if z = callOf (searchInput c v, x) then some Zc else none) O (fun _ => tc + 2) w v (searchInput c v) T Sg _ Z (fun _ => tc) (hG _ (if_pos rfl)) ?_ fun _ => le_rfl
  intro z u hz
  split_ifs at hz with hz'
  obtain rfl := Option.some.inj hz
  subst hz'
  exact (askInt_within (h := fun z : (Ready × ℕ) × CliqueCall => (Sum.inl (child z) : SolQuery)) (w := w) (a := (v, callOf (searchInput c v, x))) hO).mono hw.le le_rfl

/-! ### The numbers of a level -/

/-- K_{ℓ+1} = g_ℓ². -/
theorem K_succ_mul (x₀ l : ℕ) : Levels.Gen.K x₀ (l + 1) = Levels.Gen.g x₀ l * Levels.Gen.g x₀ l := by
  show (2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l) ^ 2 = _
  rw [sq]
  rfl

/-- K_ℓ ≥ 2. -/
theorem two_le_K {x₀ : ℕ} (hx : 1 ≤ x₀) (l : ℕ) : 2 ≤ Levels.Gen.K x₀ l :=
  le_trans (by calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) hx) (two_pow_le_K x₀ l)

/-- The K that the solver holds. -/
theorem rK_ready (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ} (hl : hLev h = l + 1) : rK (readyOf D x₀ h) = Levels.Gen.K x₀ l := by
  simp only [rK, readyOf, hl, Nat.add_sub_cancel, length_unary]

/-- The g that the solver holds. -/
theorem rG_ready (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ} (hl : hLev h = l + 1) : rG (readyOf D x₀ h) = Levels.Gen.g x₀ l := by
  simp only [rG, readyOf, hl, Nat.add_sub_cancel, length_unary, Levels.Gen.g]

/-- The number of patterns: |𝓘|^{|ℛ|}. -/
theorem nPatterns_ready (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ} (hl : hLev h = l + 1) :
    nPatterns (readyOf D x₀ h) = #(D.fam (hLam h)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := by
  simp only [nPatterns, rRect, rG_ready D x₀ h hl]
  simp only [rLists, readyOf, listsOf, Finset.length_sort]

/-- The tables of a well-formed instance of the level ℓ + 1, read back from the oracle: |W_w| < 2^B
on the g² nodes. -/
theorem tables_lt {x₀ l : ℕ} {a : Ctx} {f : TableQuery → Option Ans} (hF : Fits x₀ a f) (hl : cLev a = l + 1) :
    ∀ w < Levels.Gen.g x₀ l * Levels.Gen.g x₀ l, ∀ z ∈ words ((Levels.Gen.g x₀ l * Levels.Gen.g x₀ l - 1) * cLam a), |readTables f w z| < 2 ^ cB a := by
  obtain ⟨_, _, W, hW, rfl⟩ := hF
  rw [hl, K_succ_mul] at hW ⊢
  intro w hw z hz
  rw [readTables_setting W hw (mem_words.1 hz)]
  exact hW w hw z hz

/-- L ≤ 3gP, crudely. -/
theorem lof_le {K g P U : ℕ} {ζ : ℝ} (hK : 1 ≤ K) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (hU : U ≤ g * P) : AppRunningTime.Lof K g ζ P U ≤ 3 * (g * P) := by
  unfold AppRunningTime.Lof
  refine Nat.ceil_le.2 ?_
  have hK' : (1 : ℝ) ≤ (K : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hK)
  have hU' : (U : ℝ) ≤ (g : ℝ) * P := by exact_mod_cast hU
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg _
  have hgP : (0 : ℝ) ≤ (g : ℝ) * P := by positivity
  have h2 : 2 * ζ * g * P = 2 * (ζ * ((g : ℝ) * P)) := by ring
  have h3 : ζ * ((g : ℝ) * P) ≤ 1 * ((g : ℝ) * P) := mul_le_mul_of_nonneg_right h1 hgP
  have h4 : 0 ≤ ζ * ((g : ℝ) * P) := mul_nonneg h0 hgP
  rw [h2]
  calc ((U : ℝ) + 2 * (ζ * ((g : ℝ) * P))) / (K : ℝ) ^ 2 ≤ (U : ℝ) + 2 * (ζ * ((g : ℝ) * P)) := div_le_self (by linarith) hK'
    _ ≤ 3 * ((g : ℝ) * P) := by linarith
    _ = ((3 * (g * P) : ℕ) : ℝ) := by push_cast; ring

/-- U ≤ gP, by (i) of Definition 2. -/
theorem total_le_gP {g : ℕ} {N : Net g} {P B : ℕ} (hN : N.Is P B) : N.U ≤ g * P := by
  unfold Net.U
  calc ∑ a, ∑ b ∈ univ.erase a, N.c a b ≤ ∑ _a : Fin g, P := Finset.sum_le_sum fun a _ => hN.i a
    _ = g * P := by simp

/-! ### What is handed to the procedure of the lemma -/

variable {ρ : ℝ} {c x₀ l y : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}

/-- The network of the pattern y is a network with P = g³λ and B₁; the solver hands over the input
that belongs to it, with ζ = 1/2^{ℓ+5} and K_ℓ; the label length computed from it is the L of the
lemma; and L ≤ 3gP. -/
theorem pattern_input (hLL : LabelLengthIsL) (hBN : BothNetworks) (hS : Setting ρ c x₀ D) (hF : Fits x₀ a f) (hl : cLev a = l + 1) (hy : y < nPatterns (readyOf D x₀ a.1)) :
    (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).Is (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) ∧
    searchInput c (readyOf D x₀ a.1, y) = groupingInput 1 (2 ^ (l + 5)) (Levels.Gen.K x₀ l) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) ∧
    labelLength (searchInput c (readyOf D x₀ a.1, y)) = AppRunningTime.Lof (Levels.Gen.K x₀ l) (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) (((1 : ℕ) : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).U ∧
    labelLength (searchInput c (readyOf D x₀ a.1, y)) ≤ 3 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) := by
  obtain ⟨C₂, hC₂⟩ := hBN c
  have hK2 := two_le_K (by have := hS.x₀_ge; omega : 1 ≤ x₀) l
  have hKg := K_le_g x₀ l
  rw [nPatterns_ready D x₀ a.1 hl] at hy
  obtain ⟨hIs, -, hin, -⟩ := hC₂ ρ x₀ D hS (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) y 0 0 (cLam a) (direction (readyOf D x₀ a.1, y)) (readTables f) (by omega) hKg hF.1 le_rfl hF.2.1 (tables_lt hF hl) hy (by positivity)
  have e : unary (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) = unary (Levels.Gen.g x₀ l) := by rw [nParts_self]
  have hsi : searchInput c (readyOf D x₀ a.1, y) = groupingInput 1 (2 ^ (l + 5)) (Levels.Gen.K x₀ l) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) := by
    simp only [searchInput, groupingInput, dataInput, e]
    rw [parentAt_readyOf D x₀ a.1 hl y 0]
    refine Prod.ext (Prod.ext rfl ?_) hin
    show 2 ^ (cLev a + 4) = 2 ^ (l + 5)
    rw [hl]
  have hL := (hLL 1 (2 ^ (l + 5)) (Levels.Gen.K x₀ l) _ (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) (by positivity) (Nat.one_le_two_pow) (by omega) hIs).1
  refine ⟨hIs, hsi, by rw [hsi]; exact hL, ?_⟩
  rw [hsi, hL]
  have h := lof_le (K := Levels.Gen.K x₀ l) (g := nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) (P := (Levels.Gen.g x₀ l ^ 3 * cLam a)) (U := (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).U) (ζ := ((1 : ℕ) : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ)) (by omega) (by positivity)
    ((div_le_one (by positivity)).2 (by exact_mod_cast Nat.one_le_two_pow)) (total_le_gP hIs)
  exact h.trans (le_of_eq (by rw [nParts_self]))

end ExplicitCost
