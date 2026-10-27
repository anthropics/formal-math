/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.Answers
public import QueryMachines.CombRuns
import Mathlib.Tactic

/-! # The cost of a machine from the costs of its parts

The run statements of the machines with query access
(proof/machines/QueryMachines/CombRunsStatement.lean) give, for each way to build such a machine,
the own steps and the LIST of the queries of the whole from those of the parts. Here the same in
costs (`QueryMachine.Within`: own steps plus the prices of the queries asked), for any prices w: one
lemma for each construction.
Counting one operation for each query would not give a bound for every price of a query (for example
the price 0). So these lemmas count own steps and the prices of the queries separately, and the
lists are never named. -/

public section

namespace ExplicitCost

open Groundwork QueryMachines Finset

variable {Q Q' A A' α α₁ α₂ β γ : Type}

/-- A step machine asks nothing. -/
theorem lift_within {R : Stepped α β} {O : Q → Option A} {w : Q → ℕ} {a : α} {t S : ℕ} {b : β} (h : R.Runs a t S b) : (QueryMachine.lift R : QueryMachine Q A α β).Within O w a t S b :=
  ⟨t, [], stLiftRuns _ _ _ _ R O a t S b h, by simp⟩

/-- One query: its price. -/
theorem query_within [HasSize α] [HasSize A] {h : α → Q} {O : Q → Option A} {w : Q → ℕ} {a : α} {v : A} (hv : O (h a) = some v) :
    (QueryMachine.query h : QueryMachine Q A α A).Within O w a (w (h a)) (max (size a) (size v) + 1) v :=
  ⟨0, [h a], stQueryRuns _ _ _ h O a v hv, by simp⟩

/-- A function applied to the input. -/
theorem mapIn_within {g : α → β} {M : QueryMachine Q A β γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {c : γ} (h : M.Within O w (g a) T S c) : (QueryMachine.mapIn g M).Within O w a T S c :=
  let ⟨own, L, hr, hle⟩ := h
  ⟨own, L, stMapInRuns _ _ _ _ _ g M O a own S L c hr, hle⟩

/-- A function applied to the result. -/
theorem mapOut_within {M : QueryMachine Q A α β} {g : β → γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {b : β} (h : M.Within O w a T S b) : (QueryMachine.mapOut M g).Within O w a T S (g b) :=
  let ⟨own, L, hr, hle⟩ := h
  ⟨own, L, stMapOutRuns _ _ _ _ _ M g O a own S L b hr, hle⟩

/-- Queries rewritten by h: oracle and prices are read through h. -/
theorem mapAsk_within {h : Q → Q'} {M : QueryMachine Q A α β} {O : Q' → Option A} {w : Q' → ℕ} {a : α} {T S : ℕ} {b : β} (hr : M.Within (fun x => O (h x)) (fun x => w (h x)) a T S b) :
    (QueryMachine.mapAsk h M).Within O w a T S b :=
  let ⟨own, L, hr, hle⟩ := hr
  ⟨own, L.map h, stMapAskRuns _ _ _ _ _ h M O a own S L b hr, by rw [List.map_map]; exact hle⟩

/-- Answers read by r. -/
theorem readAs_within {r : A' → A} {M : QueryMachine Q A α β} {O : Q → Option A} {O' : Q → Option A'} (h : ∀ x, (O' x).map r = O x) {w : Q → ℕ} {a : α} {T S : ℕ} {b : β}
    (hr : M.Within O w a T S b) : (readAs r M).Within O' w a T S b :=
  let ⟨own, L, hr, hle⟩ := hr
  ⟨own, L, readAs_reaches h hr, hle⟩

/-- A choice, first machine. -/
theorem branch_within_inl {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} {O : Q → Option A} {w : Q → ℕ} {a : α} {x : α₁} {T S : ℕ} {b : β} (hs : sel a = .inl x)
    (h : M₁.Within O w x T S b) : (QueryMachine.branch sel M₁ M₂).Within O w a T (S + 1) b :=
  let ⟨own, L, hr, hle⟩ := h
  ⟨own, L, (stBranchRuns _ _ _ _ _ _ sel M₁ M₂ O a own S L b).1 x hs hr, hle⟩

/-- A choice, second machine. -/
theorem branch_within_inr {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} {O : Q → Option A} {w : Q → ℕ} {a : α} {y : α₂} {T S : ℕ} {b : β} (hs : sel a = .inr y)
    (h : M₂.Within O w y T S b) : (QueryMachine.branch sel M₁ M₂).Within O w a T (S + 1) b :=
  let ⟨own, L, hr, hle⟩ := h
  ⟨own, L, (stBranchRuns _ _ _ _ _ _ sel M₁ M₂ O a own S L b).2 y hs hr, hle⟩

/-- M if p a. -/
theorem ite_within_true {p : α → Bool} {M N : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {b : β} (hp : p a = true) (h : M.Within O w a T S b) :
    (QueryMachine.ite p M N).Within O w a T (S + 1) b := branch_within_inl (by simp [Stepped.iteSel, hp]) h

/-- N if not p a. -/
theorem ite_within_false {p : α → Bool} {M N : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {b : β} (hp : p a = false) (h : N.Within O w a T S b) :
    (QueryMachine.ite p M N).Within O w a T (S + 1) b := branch_within_inr (by simp [Stepped.iteSel, hp]) h

/-- M, then N: the costs add up, with one more step for the hand-over. -/
theorem bind_within [HasSize α] {M : QueryMachine Q A α β} {N : QueryMachine Q A (α × β) γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T T' S S' : ℕ} {b : β} {c : γ} (h : M.Within O w a T S b)
    (h' : N.Within O w (a, b) T' S' c) : (QueryMachine.bind M N).Within O w a (T + 1 + T') (max (size a + S) S' + 1) c :=
  let ⟨own, L, hr, hle⟩ := h
  let ⟨own', L', hr', hle'⟩ := h'
  ⟨own + 1 + own', L ++ L', stBindRuns _ _ _ _ _ M N O a own own' S S' L L' b c hr hr', by rw [List.map_append, List.sum_append]; omega⟩

/-- The prices of the queries of all rounds. -/
theorem sum_map_flatMap_range (w : Q → ℕ) (Lq : ℕ → List Q) (n : ℕ) : (((List.range n).flatMap Lq).map w).sum = ∑ y ∈ range n, ((Lq y).map w).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The loop over y < N a: the costs of the rounds add up, with one more step for each round. -/
theorem foldRange_within [HasSize α] [HasSize γ] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) β} {g : γ → ℕ → β → γ} {c₀ : α → γ} {O : Q → Option A} {w : Q → ℕ} {a : α} (T : ℕ → ℕ) (v : ℕ → β) (Sc Sm : ℕ)
    (hM : ∀ y < N a, M.Within O w (a, y) (T y) Sm (v y)) (hc : ∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) :
    (QueryMachine.foldRange N M g c₀).Within O w a (∑ y ∈ range (N a), (T y + 1)) (size a + size (N a) + (Sc + Sm) + 1) ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a)) := by
  have h : ∀ y, ∃ (own : ℕ) (L : List Q), y < N a → M.Runs O (a, y) own L Sm (v y) ∧ own + (L.map w).sum ≤ T y := fun y => by
    by_cases hy : y < N a
    · obtain ⟨own, L, h1, h2⟩ := hM y hy
      exact ⟨own, L, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, [], fun h => absurd h hy⟩
  choose t Lq hq using h
  refine ⟨_, _, stFoldRangeRuns _ _ _ _ _ N M g c₀ O a t Lq v Sc Sm (fun y hy => (hq y hy).1) hc, ?_⟩
  rw [sum_map_flatMap_range, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y hy => ?_
  have := (hq y (Finset.mem_range.1 hy)).2
  omega

/-- Σ_{y < N a} M(a, y); V bounds every |v y|. -/
theorem sumRange_within [HasSize α] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) ℤ} {O : Q → Option A} {w : Q → ℕ} {a : α} (T : ℕ → ℕ) (v : ℕ → ℤ) (V Sm : ℕ)
    (hM : ∀ y < N a, M.Within O w (a, y) (T y) Sm (v y)) (hV : ∀ y < N a, (v y).natAbs ≤ V) :
    (QueryMachine.sumRange N M).Within O w a (∑ y ∈ range (N a), (T y + 1)) (size a + size (N a) + (size (N a * V) + Sm) + 1) (∑ y ∈ range (N a), v y) := by
  have e : ∀ k, (List.range k).foldl (fun c y => Stepped.addG c y (v y)) (Stepped.zeroC a) = ∑ y ∈ range k, v y := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [Stepped.foldl_range_succ, ih, sum_range_succ]; rfl
  have r := foldRange_within (g := Stepped.addG) (c₀ := Stepped.zeroC) T v (size (N a * V)) Sm hM fun k hk => by
    rw [e]
    have h1 := Stepped.natAbs_sum_le v V k fun y hy => hV y (by omega)
    have h2 := Nat.size_le_size (h1.trans (Nat.mul_le_mul_right V hk))
    simp only [size_int, size_nat]
    omega
  rw [e] at r
  exact r

/-- ∏_{y < N a} M(a, y); V ≥ 1 bounds every |v y|. -/
theorem prodRange_within [HasSize α] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) ℤ} {O : Q → Option A} {w : Q → ℕ} {a : α} (T : ℕ → ℕ) (v : ℕ → ℤ) (V Sm : ℕ) (hV1 : 1 ≤ V)
    (hM : ∀ y < N a, M.Within O w (a, y) (T y) Sm (v y)) (hV : ∀ y < N a, (v y).natAbs ≤ V) :
    (QueryMachine.prodRange N M).Within O w a (∑ y ∈ range (N a), (T y + 1)) (size a + size (N a) + (size (V ^ N a) + Sm) + 1) (∏ y ∈ range (N a), v y) := by
  have e : ∀ k, (List.range k).foldl (fun c y => Stepped.mulG c y (v y)) (Stepped.oneC a) = ∏ y ∈ range k, v y := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [Stepped.foldl_range_succ, ih, prod_range_succ]; rfl
  have r := foldRange_within (g := Stepped.mulG) (c₀ := Stepped.oneC) T v (size (V ^ N a)) Sm hM fun k hk => by
    rw [e]
    have h1 := Stepped.natAbs_prod_le v V k fun y hy => hV y (by omega)
    have h2 := Nat.size_le_size (h1.trans (Nat.pow_le_pow_right hV1 hk))
    simp only [size_int, size_nat]
    omega
  rw [e] at r
  exact r

end ExplicitCost
