/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.RowFactorRun
public import CountedRecursion.ParentSize
import Mathlib.Tactic

/-! # «Definition 2 holds with B₁ = gB + g²(2λ)^c in the role of B and with τ = 2^{cλ}Ξ^{C₂}»

`bothNetworksFrom : BothNetworksFrom` and `bothNetworks : BothNetworks`, with C₂ = 2c + 6 (proof of
Theorem A (b)). The parts:
* the network is a network with the parameters g³λ and B₁, c_{a,a'} ≤ g²λ, and the input that the
  procedure writes is its input: PatternIs.lean, ParentNumbers.lean;
* every query of Definition 2(iii) that the network answers is answered by the four procedures as
  one machine (`Printed.ProcsQ.answer`): the runs of RowWeightRun.lean, RowPairRun.lean,
  RowFactorRun.lean, whose costs and sizes are explicit;
* `cost_le`, `room_le`: these are at most (2^{cλ} + 2 + tq)·Ξ^{C₂} and Ξ^{C₂}; the size of the
  parent is `size_mkParent_le` (ParentSize.lean). -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-! ## The arithmetic -/

/-- What is used of g, λ, B: with Ξ = g²(λ + B). -/
theorem xi_facts {g lam B : ℕ} (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) :
    8 ≤ Xi g lam B ∧ g ≤ Xi g lam B ∧ 2 * (g * g) ≤ Xi g lam B ∧ 2 * lam ≤ Xi g lam B ∧ B ≤ Xi g lam B ∧ g * (g * g) * lam ≤ Xi g lam B * Xi g lam B ∧ B * g ≤ Xi g lam B * Xi g lam B := by
  have h4 : 4 ≤ g * g := Nat.mul_le_mul hg hg
  have e : Xi g lam B = g * g * (lam + B) := by unfold Xi; ring
  have h1 : g * g * 2 ≤ g * g * (lam + B) := Nat.mul_le_mul_left _ (by omega)
  have h2 : 4 * (lam + B) ≤ g * g * (lam + B) := Nat.mul_le_mul_right _ h4
  have h3 : g ≤ g * g := Nat.le_mul_of_pos_left _ (by omega)
  rw [e]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩
  · calc g * (g * g) * lam ≤ (g * g) * (g * g) * ((lam + B) * (lam + B)) := by
          refine Nat.mul_le_mul (Nat.mul_le_mul_right _ h3) ?_
          exact (Nat.le_add_right lam B).trans (Nat.le_mul_of_pos_left _ (by omega))
      _ = g * g * (lam + B) * (g * g * (lam + B)) := by ring
  · calc B * g ≤ (g * g * (lam + B)) * (g * g * (lam + B)) := Nat.mul_le_mul (by omega) (by omega)

/-- The costs of the four procedures are at most (2^{cλ} + 2 + tq)·Ξ^{C₂}. -/
theorem cost_le {c g lam B tq T : ℕ} (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) (hT : T ≤ g * g * (askCost c lam + 1) ∨ T ≤ g * (tq + 1) ∨ T ≤ 1) : T ≤ (askCost c lam + tq) * Xi g lam B ^ (2 * c + 6) := by
  obtain ⟨h8, h1, h2, -, -, -, -⟩ := xi_facts hg hlam hB
  have ha : 2 ≤ askCost c lam := by unfold askCost; omega
  have hX : Xi g lam B ≤ Xi g lam B ^ (2 * c + 6) := Nat.le_self_pow (by omega) _
  refine le_trans ?_ (Nat.mul_le_mul_left _ hX)
  rcases hT with h | h | h
  · refine h.trans ?_
    calc g * g * (askCost c lam + 1) ≤ g * g * (2 * (askCost c lam + tq)) := Nat.mul_le_mul_left _ (by omega)
      _ = (askCost c lam + tq) * (2 * (g * g)) := by ring
      _ ≤ (askCost c lam + tq) * Xi g lam B := Nat.mul_le_mul_left _ h2
  · refine h.trans ?_
    calc g * (tq + 1) ≤ Xi g lam B * (askCost c lam + tq) := Nat.mul_le_mul h1 (by omega)
      _ = (askCost c lam + tq) * Xi g lam B := Nat.mul_comm _ _
  · exact h.trans (Nat.mul_pos (by omega) (by omega))

/-- The sizes of the states of the four procedures are at most Ξ^{C₂}. Here sp is the size of the
parent, sQ that of the query. -/
theorem room_le {c g lam B sp sQ S : ℕ} (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) (hsp : sp ≤ Xi g lam B ^ (2 * c + 4)) (hsq : sQ ≤ 2 * (g + 2) + 2 * (2 * (g * (g * g) * lam) + 1))
    (hS : S ≤ 2 * (sp + sQ) + 2 * (g * g + 2) + (2 * lam) ^ c * (g * g) + (2 * lam) ^ c + B * g + B + 12) : S ≤ Xi g lam B ^ (2 * c + 6) := by
  obtain ⟨h8, h1, h2, h3, h4, h5, h6⟩ := xi_facts hg hlam hB
  generalize Xi g lam B = X at *
  obtain ⟨M, hM⟩ : ∃ M, M = X ^ (2 * c + 4) := ⟨_, rfl⟩
  have hX0 : 0 < X := by omega
  have le : ∀ a, a ≤ 2 * c + 4 → X ^ a ≤ M := fun a ha => hM ▸ Nat.pow_le_pow_right hX0 ha
  have m1 : X ≤ M := by simpa using le 1 (by omega)
  have m2 : X * X ≤ M := by
    have := le 2 (by omega)
    rwa [pow_two] at this
  have hb : (2 * lam) ^ c ≤ X ^ c := Nat.pow_le_pow_left h3 c
  have m3 : (2 * lam) ^ c ≤ M := hb.trans (le c (by omega))
  have m4 : (2 * lam) ^ c * (g * g) ≤ M := by
    calc (2 * lam) ^ c * (g * g) ≤ X ^ c * X := Nat.mul_le_mul hb (by omega)
      _ = X ^ (c + 1) := (pow_succ X c).symm
      _ ≤ M := le _ (by omega)
  have m5 : 64 * M ≤ X ^ (2 * c + 6) := by
    calc 64 * M = 8 * 8 * M := rfl
      _ ≤ X * X * M := Nat.mul_le_mul_right _ (Nat.mul_le_mul h8 h8)
      _ = X ^ (2 * c + 6) := by rw [hM]; ring
  rw [← hM] at hsp
  omega

/-! ## The four procedures as one machine -/

variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

/-- The size of the number of a row is at most g + 1. -/
theorem size_row_le (a : Fin (nParts g g tr)) : size a.val ≤ g + 1 := by
  have h : a.val < g := lt_of_lt_of_eq a.2 (nParts_self g tr)
  have := size_nat_of_lt (h.trans Nat.lt_two_pow_self)
  omega

/-- The size of the number g². -/
theorem size_sq_le (g : ℕ) : size (g * g) ≤ g * g + 2 := by
  have := size_nat_of_lt (Nat.lt_two_pow_self (n := g * g))
  omega

/-- **Every query of Definition 2(iii) is answered by the procedures.** -/
theorem answer_within (hPP : PairIsProduct) (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hg : 2 ≤ g) (hK : K ≤ g) (hlam : 1 ≤ lam) (hLam : lam ≤ Lam) (hB : 1 ≤ B) (hW : ∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B)
    (hy : y < #(D.fam lam).I ^ nRectG g g) (hx : x < K ^ g) {q : NetQuery} {v : ℤ} (hq : netOracle (patternNet D c g tr lam y W) q = some v) :
    (gridProcsData c).answer.Within (upOracle D g lam Lam W) (upPrices c tq) (mkParent D K g lam B tr y x, q) ((askCost c lam + tq) * Xi g lam B ^ (2 * c + 6)) (Xi g lam B ^ (2 * c + 6)) v := by
  have hsp := size_mkParent_le hS tr hK hg hlam hB hy hx
  have hm := nMemb_self g tr
  have hgg := size_sq_le g
  have hsg : size g ≤ g + 1 := size_nat_of_lt Nat.lt_two_pow_self
  have hgle : g ≤ g * g := Nat.le_mul_of_pos_left _ (by omega)
  rcases q with q | q | q | q
  · -- is z ∈ S_a?
    simp only [netOracle] at hq
    split_ifs at hq with h1 h2 h3
    swap
    · refine absurd ((mem_S_iff _ _).2 ?_) h3
      rw [h2, hm]
      change g ^ 3 * lam = _
      ring
    rw [← Option.some.inj hq]
    have r0 : (Stepped.mapIn (fun _ : Parent × WQ => ()) (Stepped.const true)).Runs (mkParent D K g lam B tr y x, q) 1 (max (size ()) (size true) + 1) true :=
      Stepped.mapIn_runs (f := fun _ : Parent × WQ => ()) (Stepped.const_runs true ())
    have r : (QueryMachine.mapOut (gridProcsData c).mem fun b => if b = true then (1 : ℤ) else 0).Within (upOracle D g lam Lam W) (upPrices c tq) (mkParent D K g lam B tr y x, q) 1 (max (size ()) (size true) + 1) 1 :=
      mapOut_within (g := fun b : Bool => if b = true then (1 : ℤ) else 0) (lift_within r0)
    refine (branch_within_inl (sel := dist) rfl r).mono (cost_le hg hlam hB (Or.inr (Or.inr le_rfl))) (room_le (sp := 0) (sQ := 0) hg hlam hB (Nat.zero_le _) (Nat.zero_le _) ?_)
    simp only [size_unit, size_bool]
    omega
  · -- W_a(z)
    simp only [netOracle] at hq
    split_ifs at hq with h1 h2
    rw [← Option.some.inj hq]
    have hz := (mem_S_iff _ _).1 h2
    have r := rowWeight_within (D := D) (c := c) (y := y) (tq := tq) (Lam := Lam) (p := mkParent D K g lam B tr y x) pG_mk pLam_mk pTr_mk (by omega) hW ⟨q.1, h1⟩ hz
    refine (branch_within_inr (sel := dist) rfl (branch_within_inl (sel := dist) rfl r)).mono (cost_le hg hlam hB (Or.inr (Or.inl le_rfl)))
      (room_le (sp := size (mkParent D K g lam B tr y x)) (sQ := size q) hg hlam hB hsp ?_ ?_)
    · have s1 : size q.1 ≤ g + 1 := size_row_le (⟨q.1, h1⟩ : Fin (nParts g g tr))
      have s2 := size_word q.2
      rw [hz, hm] at s2
      have e : size q = size q.1 + size q.2 := rfl
      omega
    · have e : size (mkParent D K g lam B tr y x, ((⟨q.1, h1⟩ : Fin (nParts g g tr)).val, q.2)) = size (mkParent D K g lam B tr y x) + size q := rfl
      omega
  · -- Ψ_{a,b}(z, z')
    simp only [netOracle] at hq
    split_ifs at hq with h1 h2
    rw [← Option.some.inj hq]
    have hab : (⟨q.1.1, h1.1⟩ : Fin (nParts g g tr)) ≠ ⟨q.1.2, h1.2⟩ := fun e => h2.1 (congrArg Fin.val e)
    have r := rowPair_within hPP hLA (W := W) (tq := tq) (p := mkParent D K g lam B tr y x) pG_mk pLam_mk pTr_mk pY_mk pLists_mk hS hg hlam hLam hy hab h2.2.1 h2.2.2
    refine (branch_within_inr (sel := dist) rfl (branch_within_inr (sel := dist) rfl (branch_within_inl (sel := dist) rfl r))).mono (cost_le hg hlam hB (Or.inl le_rfl))
      (room_le (sp := size (mkParent D K g lam B tr y x)) (sQ := size q) hg hlam hB hsp ?_ ?_)
    · have s1 : size q.1.1 ≤ g + 1 := size_row_le (⟨q.1.1, h1.1⟩ : Fin (nParts g g tr))
      have s1' : size q.1.2 ≤ g + 1 := size_row_le (⟨q.1.2, h1.2⟩ : Fin (nParts g g tr))
      have s2 := size_word q.2.1
      have s2' := size_word q.2.2
      rw [(mem_S_iff _ _).1 h2.2.1, hm] at s2
      rw [(mem_S_iff _ _).1 h2.2.2, hm] at s2'
      have e : size q = (size q.1.1 + size q.1.2) + (size q.2.1 + size q.2.2) := rfl
      omega
    · have e : size (mkParent D K g lam B tr y x, (((⟨q.1.1, h1.1⟩ : Fin (nParts g g tr)).val, (⟨q.1.2, h1.2⟩ : Fin (nParts g g tr)).val), (q.2.1, q.2.2))) = size (mkParent D K g lam B tr y x) + size q := rfl
      omega
  · -- f_{a,b}(z, θ)
    simp only [netOracle] at hq
    split_ifs at hq with h1 h2
    rw [← Option.some.inj hq]
    have hab : (⟨q.1.1, h1.1⟩ : Fin (nParts g g tr)) ≠ ⟨q.1.2, h1.2⟩ := fun e => h2.1 (congrArg Fin.val e)
    have hz := (mem_S_iff _ _).1 h2.2.1
    have hθ : q.2.2.length = capG (piecesOf D c) g g tr 0 lam y q.1.1 q.1.2 := (mem_words.1 h2.2.2).trans (c_eq hab)
    have r := rowFactor_within hLA (W := W) (tq := tq) (p := mkParent D K g lam B tr y x) pG_mk pLam_mk pTr_mk pY_mk pLists_mk hS (by omega) hlam hLam hab hz hθ
    refine (branch_within_inr (sel := dist) rfl (branch_within_inr (sel := dist) rfl (branch_within_inr (sel := dist) rfl r))).mono (cost_le hg hlam hB (Or.inl le_rfl))
      (room_le (sp := size (mkParent D K g lam B tr y x)) (sQ := size q) hg hlam hB hsp ?_ ?_)
    · have s1 : size q.1.1 ≤ g + 1 := size_row_le (⟨q.1.1, h1.1⟩ : Fin (nParts g g tr))
      have s1' : size q.1.2 ≤ g + 1 := size_row_le (⟨q.1.2, h1.2⟩ : Fin (nParts g g tr))
      have s2 := size_word q.2.1
      have s2' := size_word q.2.2
      have hc := pattern_c_le (y := y) (W := W) hS hlam (⟨q.1.1, h1.1⟩ : Fin (nParts g g tr)) ⟨q.1.2, h1.2⟩
      rw [hz, hm] at s2
      rw [mem_words.1 h2.2.2] at s2'
      have h3 : g ^ 2 * lam ≤ g * (g * g) * lam := by
        calc g ^ 2 * lam = 1 * (g * g) * lam := by ring
          _ ≤ g * (g * g) * lam := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      have e : size q = (size q.1.1 + size q.1.2) + (size q.2.1 + size q.2.2) := rfl
      omega
    · have e : size (mkParent D K g lam B tr y x, (((⟨q.1.1, h1.1⟩ : Fin (nParts g g tr)).val, (⟨q.1.2, h1.2⟩ : Fin (nParts g g tr)).val), (q.2.1, q.2.2))) = size (mkParent D K g lam B tr y x) + size q := rfl
      omega

/-- The two networks, assuming that Ψ is the product that `rowPair` computes (used for the run of
`rowPair`) and that the numbers read from the lists are those of the pieces (used for the input that
the procedure writes and for the runs of `rowPair` and `rowFactor`). What the grid needs of the
pieces is taken from `cutsOK_piecesOf`. C₂ = 2c + 6. -/
theorem bothNetworksFrom : BothNetworksFrom := fun hPP hLA c => ⟨2 * c + 6, fun _ _ _ hS _ _ _ _ _ _ _ _ _ _ hg hK hlam hLam hB hW hy hx =>
  ⟨pattern_is hS (by omega) hlam hB hW, fun a b _ => pattern_c_le hS hlam a b, netData_eq hLA hS hlam, fun _ _ hq => answer_within hPP hLA hS hg hK hlam hLam hB hW hy hx hq⟩⟩

/-- **«Definition 2 holds with B₁ = gB + g²(2λ)^c in the role of B and with τ = 2^{cλ}Ξ^{C₂}.»** -/
theorem bothNetworks : BothNetworks := bothNetworksFrom pairIsProduct listsAgree

end ExplicitCost
