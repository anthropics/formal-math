/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.AnswersDefs
public import QueryMachines.Runs
public import QueryMachines.Poly
import Mathlib.Tactic

/-! # Answers read by a function; prices raised

Facts on machines with query access; runs and costs are followed by induction over a run or over the
list of its queries:
* `readAsRuns`, `readAsPoly`: `readAs r M` runs as M does, if the new oracle, read by r, is the old
  one; and it has polynomial-time steps if M has and r is polynomial-time.
* `pricesScale`: if every price is raised at most k times, so is the cost. -/

public section

namespace ExplicitCost

open Groundwork QueryMachines Printed

variable {Q A A' α β : Type}

/-- `readAs r M` runs as M does (from a state). -/
theorem readAs_reaches {r : A' → A} {M : QueryMachine Q A α β} {O : Q → Option A} {O' : Q → Option A'} (h : ∀ x, (O' x).map r = O x) {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (hr : M.Reaches O S b s own L) : (readAs r M).Reaches O' S b s own L := by
  induction hr with
  | halt ho hs => exact .halt ho hs
  | step ho ha hs _ ih => exact .step ho ha hs ih
  | @query s own L x v ho ha hv hs _ ih =>
    obtain ⟨v', hv', rfl⟩ : ∃ v', O' x = some v' ∧ r v' = v := by
      have e := h x
      rw [hv] at e
      exact Option.map_eq_some_iff.1 e
    exact .query ho ha hv' hs ih

/-- `ReadAsRuns`. -/
theorem readAsRuns : ReadAsRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hr => readAs_reaches h hr

/-- The certificate of `readAs r M`. -/
@[instance_reducible] def readAsIsPolyQ [Enc Q] [Enc A] [Enc A'] [Enc α] [Enc β] {r : A' → A} (hr : PolyT r) (M : QueryMachine Q A α β) [i : QueryMachine.IsPolyQ M] : QueryMachine.IsPolyQ (readAs r M) where
  enc := i.enc
  carried := i.carried
  init := i.init
  step := i.step
  out := i.out
  ask := i.ask
  resume := by
    have := i.resume
    exact (by fun_prop : PolyT fun p : M.σ × A' => M.resume p.1 (r p.2))

/-- `ReadAsPoly`. -/
theorem readAsPoly : ReadAsPoly := fun _ _ _ _ _ _ _ _ _ _ _ M hr ⟨_⟩ => ⟨readAsIsPolyQ hr M⟩

/-- The sum of the prices of a list of queries, if every price is raised at most k times. -/
theorem sum_map_le_mul {w w' : Q → ℕ} {k : ℕ} (h : ∀ x, w' x ≤ k * w x) (L : List Q) : (L.map w').sum ≤ k * (L.map w).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have := h x
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

/-- `PricesScale`. -/
theorem pricesScale : PricesScale := fun _ _ _ _ _ _ w w' _ T _ k _ hk h ⟨own, L, hr, hle⟩ => ⟨own, L, hr, by
  have h1 := sum_map_le_mul h L
  have h2 := Nat.mul_le_mul_left k hle
  have h3 : own ≤ k * own := Nat.le_mul_of_pos_left _ hk
  rw [Nat.mul_add] at h2
  omega⟩

end ExplicitCost
