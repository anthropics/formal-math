/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Exits.Tested
import all StepMachines.Prog.Range
import all StepMachines.Prog.Walk

/-! # A loop that can be left early: steps, sizes, result

Proofs of the statements of proof/threesat/Exits/Defs.lean about steps, sizes and results of the
machines `foldUntil`, `firstUntil` and `walkUntil` (all but `StFoldUntilPoly`, which is proved in
Poly.lean).
* `stFoldUntil`: the loop. The proof is that of `Groundwork.Stepped.foldWhile_runs`
  (proof/machines/StepMachines/Prog/Stepped.lean), an induction along the orbit, with one more case:
  after a round whose accumulator passes `stop` the machine is in a halting state.
* `stFirstUntilOf`, `stFirstUntil`: line 10 of Algorithm 1, «try all groupings into K_ℓ groups until
  one is good».
* `stWalkUntilOf`, `stWalkUntil`: line 2 of Algorithm 1, «for each … do», run so that it stops at
  the first Φ with Count(Φ) > 0 (the deciding form; the printed algorithm sums the counts). The
  further ingredient here is the count of the stacks that are met, `length_tested_visits`.
Neither use goes through `firstRange` or `walk`.
The imports `import all StepMachines.Prog.Range` and `import all StepMachines.Prog.Walk` give access
to lemmas of those files that are not public: `orbit_range`, `sum_map_range` and `foldl_first`
(Range.lean) and `sum_sel` (Walk.lean). -/

public section

namespace Exits

open Finset Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)

variable {α β γ τ ν : Type}

/-! ### The loop -/

section foldUntil

variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β} {g : γ → τ → β → γ} {stop : γ → Bool} {c₀ : α → γ}

/-- The body, run inside the loop; when it has halted, the loop goes to the next point, or halts if
the new accumulator passes `stop`. -/
theorem foldUntil_body {x : τ} {c r : γ} {b : β} {s : M.σ} {t T Sm S : ℕ} (h : M.Reaches Sm b s t) (hS : size x + (size c + Sm) + 1 ≤ S)
    (hr : (foldUntil start nxt M g stop c₀).Reaches S r (foldGo M (g c x b) (if stop (g c x b) then none else nxt x)) T) :
    (foldUntil start nxt M g stop c₀).Reaches S r (.inl (x, c, s)) (t + 1 + T) := by
  induction h with
  | @halt s t ho hs =>
    have e : (foldUntil start nxt M g stop c₀).step (.inl (x, c, s)) = foldGo M (g c x b) (if stop (g c x b) then none else nxt x) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (foldUntil start nxt M g stop c₀).Reaches S r (.inl (x, c, s)) (T + 1) :=
      .step rfl (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ hr)
    exact this.mono (by omega) le_rfl
  | @step s t ho hs _ ih =>
    have e : (foldUntil start nxt M g stop c₀).step (.inl (x, c, s)) = .inl (x, c, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (foldUntil start nxt M g stop c₀).Reaches S r (.inl (x, c, s)) (t + 1 + T + 1) :=
      .step rfl (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl

/-- The loop from any point of the orbit and any accumulator. -/
theorem foldUntil_reaches {xs : List τ} {o : Option τ} (ho : Orbit nxt o xs) (t : τ → ℕ) (v : τ → β) (Sx Sc Sm : ℕ) (c : γ)
    (hM : ∀ x ∈ met (fun c x => g c x (v x)) stop c xs, M.Runs x (t x) Sm (v x)) (hx : ∀ x ∈ met (fun c x => g c x (v x)) stop c xs, size x ≤ Sx)
    (hc : ∀ l, l <+: met (fun c x => g c x (v x)) stop c xs → size (l.foldl (fun c x => g c x (v x)) c) ≤ Sc) :
    (foldUntil start nxt M g stop c₀).Reaches (Sx + (Sc + Sm) + 1) ((met (fun c x => g c x (v x)) stop c xs).foldl (fun c x => g c x (v x)) c)
      (foldGo M c o) ((met (fun c x => g c x (v x)) stop c xs).map fun x => t x + 1).sum := by
  induction ho generalizing c with
  | nil =>
    have := hc [] List.nil_prefix
    rw [met_nil]
    exact .halt rfl (by change size c + 1 ≤ _; simp only [List.foldl_nil] at this; omega)
  | @cons x xs _ ih =>
    have h2 := hc [] List.nil_prefix
    simp only [List.foldl_nil] at h2
    cases hs : stop (g c x (v x)) with
    | true =>
      have e : met (fun c x => g c x (v x)) stop c (x :: xs) = [x] := met_cons_of_stop hs xs
      rw [e] at hM hx hc ⊢
      have h1 := hx x List.mem_cons_self
      have h3 := hc [x] List.prefix_rfl
      simp only [List.foldl_cons, List.foldl_nil] at h3
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.foldl_cons, List.foldl_nil]
      refine foldUntil_body (hM x List.mem_cons_self) (by omega) ?_
      rw [hs, if_pos rfl]
      exact .halt rfl (by change size (g c x (v x)) + 1 ≤ _; omega)
    | false =>
      have e : met (fun c x => g c x (v x)) stop c (x :: xs) = x :: met (fun c x => g c x (v x)) stop (g c x (v x)) xs := met_cons_of_go hs xs
      rw [e] at hM hx hc ⊢
      have h1 := hx x List.mem_cons_self
      simp only [List.map_cons, List.sum_cons, List.foldl_cons]
      refine foldUntil_body (hM x List.mem_cons_self) (by omega) ?_
      rw [hs, if_neg Bool.false_ne_true]
      exact ih (g c x (v x)) (fun y hy => hM y (List.mem_cons_of_mem _ hy)) (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        fun l hl => by simpa using hc (x :: l) ((List.prefix_cons_inj x).2 hl)

end foldUntil

/-- **The loop that can be left.** Steps: Σ (steps of the body + 1) over the points that are met;
result: the fold over them. Behind «until one is good» (line 10 of Algorithm 1) and the stop at the
first Φ with Count(Φ) > 0 in the deciding form of lines 2 and 3. -/
theorem stFoldUntil : StFoldUntil := by
  intro α β γ τ _ _ start nxt M g stop c₀ a xs ho t v Sx Sc Sm hM hx hc
  exact foldUntil_reaches ho t v Sx Sc Sm (c₀ a) hM hx hc

/-! ### «try all … until one is good» -/

/-- «try all groupings into K_ℓ groups until one is good» (line 10 of Algorithm 1), from the loop:
the points met are (a, y) for y below `reach`. -/
theorem stFirstUntilOf : StFirstUntilOf := by
  intro H α β _ N M p a t v Sm hM
  have ho := orbit_range N a (N a) 0 (by omega)
  rw [← List.range_eq_range'] at ho
  have hmet : met (fun c (x : α × ℕ) => rangeG (firstG p) c x (v x.2)) Option.isSome none ((List.range (N a)).map fun y => (a, y))
      = (List.range (reach (fun y => p (v y)) (N a))).map fun y => (a, y) := by rw [← tested_range]; exact met_first p v a _
  have hr := reach_le (fun y => p (v y)) (N a)
  have key := H α β (Option ℕ) (α × ℕ) (rangeStart N) (rangeNext N) M (rangeG (firstG p)) Option.isSome noneC a _ ho (fun x => t x.2) (fun x => v x.2) (size a + size (N a)) (size (N a) + 1) Sm
  rw [show noneC a = none from rfl, hmet] at key
  have key2 := key
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hM y (List.mem_range.1 hy))
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := Nat.size_le_size ((List.mem_range.1 hy).le.trans hr)
      simp only [size_prod, size_nat]; omega)
    (by
      intro l hl
      rw [List.prefix_iff_eq_take] at hl
      rw [hl, ← List.map_take, List.take_range, List.foldl_map]
      rw [show List.foldl (fun c y => rangeG (firstG p) c (a, y) (v y)) none (List.range (min l.length (reach (fun y => p (v y)) (N a))))
        = (List.range (min l.length (reach (fun y => p (v y)) (N a)))).find? fun y => p (v y) from foldl_first (fun y => p (v y)) _]
      cases h : (List.range (min l.length (reach (fun y => p (v y)) (N a)))).find? fun y => p (v y) with
      | none => simp only [size_none]; omega
      | some i =>
        have hi := List.mem_range.1 (List.mem_of_find?_eq_some h)
        have := Nat.size_le_size (hi.le.trans ((min_le_right _ _).trans hr))
        simp only [size_some, size_nat]; omega)
  rw [List.map_map, List.foldl_map] at key2
  rw [← sum_map_range, ← foldl_first_tested p v, tested_range]
  exact key2

/-- «try all groupings into K_ℓ groups until one is good» (line 10 of Algorithm 1): the search halts
at the first good number, within the steps of the numbers up to it. -/
theorem stFirstUntil : StFirstUntil := stFirstUntilOf stFoldUntil

/-! ### «for each … do», stopped at the first leaf that passes -/

/-- **How many stacks are met.** While the tree below s, of depth at most k, is walked up to the
first leaf that passes, at most 2·(number of leaves tested) + k − 1 stacks are met: an inner node
that is met either has all the leaves of its left half tested, or lies on the path to the last leaf
tested. -/
theorem length_tested_visits (step : ν → Option (ν × ν)) (v : ν → Bool) (w : List ν → Bool) (hw : ∀ st, w st = ((walkSel step st).map v).getD false) (k : ℕ) (s : ν) (r : List ν)
    (hk : ∀ x ∈ leaves step k s, step x = none) : (tested w (visits step k s r)).length + 1 ≤ 2 * (tested v (leaves step k s)).length + k := by
  induction k generalizing s r with
  | zero =>
    rw [show visits step 0 s r = [s :: r] from rfl, show leaves step 0 s = [s] from rfl, tested_singleton, tested_singleton]
    exact le_rfl
  | succ k ih =>
    cases h0 : step s with
    | none =>
      rw [show visits step (k + 1) s r = [s :: r] by simp [visits, h0], show leaves step (k + 1) s = [s] by simp [leaves, h0], tested_singleton, tested_singleton]
      simp only [List.length_singleton]; omega
    | some lh =>
      obtain ⟨l, h'⟩ := lh
      have ev : visits step (k + 1) s r = (s :: r) :: (visits step k l (h' :: r) ++ visits step k h' r) := by simp [visits, h0]
      have el : leaves step (k + 1) s = leaves step k l ++ leaves step k h' := by simp [leaves, h0]
      rw [el] at hk
      have hl : ∀ x ∈ leaves step k l, step x = none := fun x hx => hk x (List.mem_append_left _ hx)
      have hs : w (s :: r) = false := by rw [hw]; simp [walkSel, h0]
      have ha : (visits step k l (h' :: r)).any w = (leaves step k l).any v := by rw [← any_filterMap_sel (walkSel step) v w hw, filterMap_visits step k l (h' :: r) hl]
      have i1 := ih l (h' :: r) hl
      have i2 := ih h' r fun x hx => hk x (List.mem_append_right _ hx)
      have n1 := length_visits step k l (h' :: r)
      rw [ev, el, tested_cons_of_fail hs, List.length_cons]
      cases hp : (leaves step k l).any v with
      | true => rw [tested_append_of_pass (ha.trans hp), tested_append_of_pass hp]; omega
      | false => rw [tested_append_of_fail (ha.trans hp), tested_append_of_fail hp, List.length_append, List.length_append]; omega

/-- «for each … do» (line 2 of Algorithm 1), run so that it stops at the first Φ with Count(Φ) > 0
(the deciding form), from the loop: the stacks met are those up to the first whose top is a leaf
that passes. -/
theorem stWalkUntilOf : StWalkUntilOf := by
  intro H α ν _ step root T k a hk v t Sm Sx hT hS
  obtain ⟨w, hw⟩ : ∃ w : List ν → Bool, ∀ st, w st = ((walkSel step st).map v).getD false := ⟨_, fun _ => rfl⟩
  have ho : Orbit (walkNext step) (some [root a]) (visits step k (root a) [] ++ [[]]) := orbit_visits step k (root a) [] [[]] hk (.cons .nil)
  have hf : (visits step k (root a) [] ++ [[]]).filterMap (walkSel step) = leaves step k (root a) := by
    rw [List.filterMap_append, filterMap_visits step k (root a) [] hk]
    simp [walkSel]
  have hfm : (tested w (visits step k (root a) [] ++ [[]])).filterMap (walkSel step) = tested v (leaves step k (root a)) := by rw [filterMap_tested (walkSel step) v w hw, hf]
  have hlen : (tested w (visits step k (root a) [] ++ [[]])).length ≤ 2 * (tested v (leaves step k (root a))).length + k := by
    have ha : (visits step k (root a) []).any w = (leaves step k (root a)).any v := by rw [← any_filterMap_sel (walkSel step) v w hw, filterMap_visits step k (root a) [] hk]
    cases hp : (leaves step k (root a)).any v with
    | true =>
      have := length_tested_visits step v w hw k (root a) [] hk
      rw [tested_append_of_pass (ha.trans hp)]; omega
    | false =>
      have := length_visits step k (root a) []
      rw [tested_append_of_fail (ha.trans hp), tested_of_fail hp, tested_singleton, List.length_append, List.length_singleton]; omega
  have key := H α Bool Bool (List ν) (fun a : α => some [root a]) (walkNext step) (guard (walkSel step) T false) (fun c _ b => c || b) id (fun _ => false) a _ ho
    (fun st => ((walkSel step st).map fun _ => t).getD 0) w Sx 1 (Sm + 1)
  rw [met_or w] at key
  have key2 := key
    (by
      intro st hst
      rw [hw st]
      cases h : walkSel step st with
      | none => exact (guard_runs_none h).mono le_rfl (by omega)
      | some x => exact guard_runs_some h (hT x (hfm ▸ List.mem_filterMap.2 ⟨st, hst, h⟩)))
    (by
      intro st hst
      obtain ⟨i, rfl⟩ := exists_round_of_orbit step ho st (mem_of_mem_tested hst)
      exact hS i)
    (fun _ _ => le_rfl)
  rw [sum_sel, foldl_or, hfm, Bool.false_or, any_tested, ← any_filterMap_sel (walkSel step) v w hw, hf] at key2
  exact key2.mono (by rw [Nat.mul_add]; omega) le_rfl

/-- «for each … do» (line 2 of Algorithm 1), run so that it stops at the first Φ with Count(Φ) > 0
(the deciding form): the walk halts at the first leaf that passes, within t + 2 steps for each leaf
tested and k more. -/
theorem stWalkUntil : StWalkUntil := stWalkUntilOf stFoldUntil

end Exits
