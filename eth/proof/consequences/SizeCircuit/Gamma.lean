/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SizeCircuit.Defs
public import CircuitLowerBound.Circ.Blocks
import SizeCircuit.General
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 7: the 3-CNF Γ

Proofs of `StGamma` and `StGammaCount` of proof/consequences/SizeCircuit/Defs.lean. The paper: «a
new variable for each gate, clauses of at most 3 literals that force it to equal the value of the
gate, and a clause that makes the output true give a 3-CNF Γ with O(n) variables and O(n) clauses.
Each S of size s extends to exactly one satisfying assignment of Γ, and no other S to any.»

Both follow from `stUniqueExtension` (General.lean): the clauses of the gates have exactly one
extension of every S, and in it the variable of the output has the value of the circuit, which is 1
exactly if |S| = s. The count: an assignment that satisfies ψ ∧ Γ is sent to its part on x₀ … xₙ₋₁;
this is one to one and onto the assignments that satisfy ψ and make exactly s variables true. -/

public section

namespace SizeCircuit

open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP

/-! ### The shape of the formula -/

/-- The variables of the four clauses of a gate are the two wires that it reads and its own wire. -/
theorem var_gateClauses {i : ℕ} {g : GateD} {C : List (ℕ × Bool)} (hC : C ∈ gateClauses i g) {l : ℕ × Bool} (hl : l ∈ C) :
    l.1 = g.2.1 ∨ l.1 = g.2.2 ∨ l.1 = i := by
  simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;>
    (simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
     rcases hl with rfl | rfl | rfl <;> simp)

/-- The clauses of the gates of K, numbered from j on, have at most 3 literals and variables below n +
j + (number of gates), if the gates read earlier wires only. -/
private theorem shaped_zipIdx (n : ℕ) : ∀ (K : List GateD) (j : ℕ), WFa (n + j) K →
    ∀ C ∈ (K.zipIdx j).flatMap fun gt => gateClauses (n + gt.2) gt.1, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n + j + K.length
  | [], j, _, C, hC => by
    rw [List.zipIdx_nil, List.flatMap_nil] at hC
    exact absurd hC List.not_mem_nil
  | g :: K, j, h, C, hC => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.mem_append] at hC
    rw [List.length_cons]
    rcases hC with hC | hC
    · refine ⟨(stForces (fun _ => false) _ g).2 C hC, fun l hl => ?_⟩
      have h1 := h.1
      have h2 : l.1 = g.2.1 ∨ l.1 = g.2.2 ∨ l.1 = n + j := var_gateClauses hC hl
      omega
    · obtain ⟨h1, h2⟩ := shaped_zipIdx n K (j + 1) h.2 C hC
      refine ⟨h1, fun l hl => ?_⟩
      have := h2 l hl
      omega

/-- Four clauses for every gate. -/
private theorem length_zipIdx (n : ℕ) : ∀ (K : List GateD) (j : ℕ), ((K.zipIdx j).flatMap fun gt => gateClauses (n + gt.2) gt.1).length = 4 * K.length
  | [], j => rfl
  | g :: K, j => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, length_zipIdx n K (j + 1), List.length_cons]
    have h : (gateClauses (n + (g, j).2) (g, j).1).length = 4 := rfl
    rw [h]
    omega

/-- Four clauses for every gate and one for the output. -/
theorem length_formulaOf (n : ℕ) (K : List GateD) : (formulaOf n K).length = 4 * K.length + 1 := by
  rw [formulaOf, List.length_append, wiresFormula, length_zipIdx]
  rfl

/-- The formula of a non-empty circuit whose gates read earlier wires only is a 3-CNF on the
variables of the wires. -/
theorem shaped_formulaOf {n : ℕ} {K : List GateD} (hK : WFa n K) (hne : K ≠ []) : Shaped 3 (n + K.length) (formulaOf n K) := by
  intro C hC
  rcases List.mem_append.1 hC with hC | hC
  · exact shaped_zipIdx n K 0 hK C hC
  · rw [List.mem_singleton.1 hC]
    have hp : 0 < K.length := List.length_pos_iff.2 hne
    refine ⟨by simp, fun l hl => ?_⟩
    rw [List.mem_singleton.1 hl]
    show n + K.length - 1 < n + K.length
    omega

/-- The formula holds exactly if the clauses of the gates hold and the variable of the output is 1. -/
theorem holds_formulaOf (a : ℕ → Bool) (n : ℕ) (K : List GateD) : Holds a (formulaOf n K) ↔ Holds a (wiresFormula n K) ∧ a (n + K.length - 1) = true := by
  rw [formulaOf, holds_append, holds_cons]
  constructor
  · rintro ⟨h1, ⟨l, hl, h2⟩, -⟩
    rw [List.mem_singleton.1 hl] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, ⟨_, List.mem_singleton.2 rfl, h2⟩, holds_nil a⟩

/-! ### Words and sets -/

/-- The number of ones of the word of x is the number of places where x is 1. -/
theorem count_ofFn : ∀ {n : ℕ} (x : Fin n → Bool), (List.ofFn x).count true = (Finset.univ.filter fun i => x i = true).card
  | 0, x => by simp
  | n + 1, x => by
    have ih := count_ofFn fun i => x i.succ
    rw [List.ofFn_succ, List.count_cons, ih, Fin.card_filter_univ_succ']
    cases x 0 <;> simp [add_comm]

/-! ### Γ -/

/-- **`StGamma`.** «give a 3-CNF Γ with O(n) variables and O(n) clauses. Each S of size s extends to
exactly one satisfying assignment of Γ, and no other S to any.» For every family of circuits that
tests the size with at most a·(n+1) gates, and n ≥ 1: Γ is a 3-CNF on n + (number of gates) ≤
(a+1)·(n+1) variables with at most 4a·(n+1) + 1 clauses; an assignment x of x₀ … xₙ₋₁ with exactly s
ones has exactly one extension that satisfies Γ, and every other x has none. -/
theorem stGamma : StGamma := by
  intro gates a hT n s hn
  obtain ⟨hne, hlen, hWF, hev⟩ := hT n s hn
  refine ⟨shaped_formulaOf (wfa_of_wf hWF) hne, ?_, ?_, fun x => ?_⟩
  · rw [Nat.succ_mul]
    omega
  · rw [length_formulaOf, Nat.mul_assoc]
    omega
  · obtain ⟨⟨b0, ⟨hb0, hH0⟩, hu⟩, hout⟩ := stUniqueExtension n (gates n s) hWF hne x
    have hc : ENP.eval (toC (gates n s)) (List.ofFn x) = true ↔ (Finset.univ.filter fun i => x i = true).card = s := by
      rw [hev (List.ofFn x) List.length_ofFn, count_ofFn]
    refine ⟨fun hs => ⟨b0, ⟨hb0, (holds_formulaOf _ _ _).2 ⟨hH0, ?_⟩⟩, ?_⟩, ?_⟩
    · rw [hout b0 hb0 hH0]
      exact hc.2 hs
    · rintro b ⟨hb, hH⟩
      exact hu b ⟨hb, ((holds_formulaOf _ _ _).1 hH).1⟩
    · rintro hs ⟨b, hb, hH⟩
      obtain ⟨h1, h2⟩ := (holds_formulaOf _ _ _).1 hH
      rw [hout b hb h1] at h2
      exact hs (hc.1 h2)

/-- A formula on x₀ … xₙ₋₁ holds under an assignment on more variables exactly if it holds under its
part on x₀ … xₙ₋₁. -/
theorem holds_restrict {n m : ℕ} (b : Fin (n + m) → Bool) (x : Fin n → Bool) (hbx : ∀ i, b (Fin.castAdd m i) = x i) {ψ : Fml}
    (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) : Holds (ext b) ψ ↔ Holds (ext x) ψ :=
  holds_congr fun C hC l hl => by
    have h := hψ C hC l hl
    rw [ext_of_lt b (by omega : l.1 < n + m), ext_of_lt x h]
    exact hbx ⟨l.1, h⟩

/-- **`StGammaCount`.** A formula ψ on x₀ … xₙ₋₁ together with Γ has as many satisfying assignments
as ψ has satisfying assignments with exactly s true variables. For every n, also n = 0. -/
theorem stGammaCount : StGammaCount := by
  intro gates a hT n s ψ hψ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e1 : numVars gates 0 s = 0 := if_pos rfl
    have e2 : gamma gates 0 s = if s = 0 then [] else [[]] := if_pos rfl
    have hcard : ∀ x : Fin 0 → Bool, (Finset.univ.filter fun i => x i = true).card = 0 := fun x => by simp
    rw [e1, e2]
    unfold cntN cntS
    refine congrArg Finset.card (Finset.filter_congr fun x _ => ?_)
    rw [hcard x]
    by_cases hs : s = 0
    · rw [if_pos hs, List.append_nil]
      exact ⟨fun h => ⟨h, hs.symm⟩, fun h => h.1⟩
    · rw [if_neg hs]
      constructor
      · intro h
        obtain ⟨l, hl, -⟩ := h [] (by simp)
        exact absurd hl List.not_mem_nil
      · rintro ⟨-, h⟩
        exact absurd h.symm hs
  · have e1 : numVars gates n s = n + (gates n s).length := if_neg (by omega)
    have e2 : gamma gates n s = formulaOf n (gates n s) := if_neg (by omega)
    obtain ⟨-, -, -, hx⟩ := stGamma gates a hT n s hn
    rw [e1, e2]
    unfold cntN cntS
    have hsize : ∀ b : Fin (n + (gates n s).length) → Bool, Holds (ext b) (formulaOf n (gates n s)) →
        (Finset.univ.filter fun i => b (Fin.castAdd (gates n s).length i) = true).card = s := by
      intro b hb
      by_contra hne
      exact (hx fun i => b (Fin.castAdd (gates n s).length i)).2 hne ⟨b, fun _ => rfl, hb⟩
    refine Finset.card_bij (fun b _ => fun i => b (Fin.castAdd (gates n s).length i)) ?_ ?_ ?_
    · intro b hb
      obtain ⟨h1, h2⟩ := (holds_append _ _ _).1 (Finset.mem_filter.1 hb).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (holds_restrict b _ (fun _ => rfl) hψ).1 h1, hsize b h2⟩
    · intro b hb b' hb' e
      have h2 := ((holds_append _ _ _).1 (Finset.mem_filter.1 hb).2).2
      have h2' := ((holds_append _ _ _).1 (Finset.mem_filter.1 hb').2).2
      obtain ⟨b0, -, hu⟩ := (hx fun i => b (Fin.castAdd (gates n s).length i)).1 (hsize b h2)
      exact (hu b ⟨fun _ => rfl, h2⟩).trans (hu b' ⟨fun i => (congrFun e i).symm, h2'⟩).symm
    · intro x hxm
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hxm
      obtain ⟨b, ⟨hb, hH⟩, -⟩ := (hx x).1 h2
      exact ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, (holds_append _ _ _).2 ⟨(holds_restrict b x hb hψ).2 h1, hH⟩⟩, funext hb⟩

end SizeCircuit
