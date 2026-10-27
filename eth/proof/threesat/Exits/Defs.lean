/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Range
public import StepMachines.Prog.Walk
public import ToTuring.PolyT

/-! # A loop that can be left early (definitions and statements only)

The machines of this development leave a loop early in two places: lines 1 to 4 in their deciding
form (Suffices/Defs.lean), which return at the first formula Φ of Lemma 4 with Count(Φ) > 0, and
line 10, «try all groupings into K_ℓ groups until one is good».
The loop of the step machines of this development, `Groundwork.Stepped.foldWhile`
(proof/machines/StepMachines/Prog/Stepped.lean), cannot do this: its next point is a function of the
present point alone. So `firstRange` (Range.lean) runs through the whole range and keeps the first
hit, and `walk` (Walk.lean) tests every leaf.
`foldUntil` is `foldWhile` with one more argument, a test `stop` on the accumulator: after each
round the loop halts if the new accumulator passes the test. Its states are those of `foldWhile`.
The two uses:
* `firstUntil N M p`: the least y < N a such that p holds of M(a, y); the loop halts there;
* `walkUntil step root T`: does some leaf below root a pass the test T? The walk halts at the first
  leaf that passes.
What the statements say beyond those of `firstRange_runs` and `walk_runs`: the body need only halt
on the points up to the first hit (nothing is asked of it on later points), and the number of steps
is bounded by a sum over these points alone. This is how «the loop is left» shows in a statement.
This file has no proofs. -/

@[expose] public section

namespace Exits

open Finset Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)

section Loops

variable {α β γ τ ν : Type}

/-- The loop: run M at x = start a, fold its result into the accumulator by g; halt if the new
accumulator passes `stop`; else go on to nxt x; halt at none. -/
def foldUntil [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ) (M : Stepped τ β) (g : γ → τ → β → γ) (stop : γ → Bool) (c₀ : α → γ) : Stepped α γ where
  σ := (τ × γ × M.σ) ⊕ γ
  init a := foldGo M (c₀ a) (start a)
  step s := match s with
    | .inl p => match M.out p.2.2 with
      | some b => foldGo M (g p.2.1 p.1 b) (if stop (g p.2.1 p.1 b) then none else nxt p.1)
      | none => .inl (p.1, p.2.1, M.step p.2.2)
    | .inr c => .inr c
  out s := match s with | .inl _ => none | .inr c => some c

/-- The least y < N a such that p holds of M(a, y), if there is one; the loop halts at it. -/
def firstUntil [HasSize α] (N : α → ℕ) (M : Stepped (α × ℕ) β) (p : β → Bool) : Stepped α (Option ℕ) :=
  foldUntil (rangeStart N) (rangeNext N) M (rangeG (firstG p)) Option.isSome noneC

/-- Does some leaf below root a pass the test T? The walk halts at the first leaf that passes. -/
def walkUntil [HasSize ν] (step : ν → Option (ν × ν)) (root : α → ν) (T : Stepped ν Bool) : Stepped α Bool :=
  foldUntil (fun a => some [root a]) (walkNext step) (Stepped.guard (walkSel step) T false) (fun c _ b => c || b) id fun _ => false

end Loops

/-- The points of the loop that are met: those of xs up to and including the first after which the
accumulator passes `stop`; all of xs if there is none. `f` is one round on the accumulator. -/
def met {τ γ : Type} (f : γ → τ → γ) (stop : γ → Bool) : γ → List τ → List τ
  | _, [] => []
  | c, x :: xs => if stop (f c x) then [x] else x :: met f stop (f c x) xs

/-- **The loop.** Let xs be the orbit of nxt from start a, and let the body take t x steps on x and
return v x, FOR THE POINTS THAT ARE MET. Then the loop halts within Σ (t x + 1) steps, summed over
the points that are met, and returns the fold over them. (xs is a finite list; a loop whose orbit is
infinite and which ends only because of «stop» is not covered.) Sx, Sc, Sm bound the sizes of the
points, of the accumulator and inside the body. -/
def StFoldUntil : Prop := ∀ (α β γ τ : Type) [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ) (M : Stepped τ β) (g : γ → τ → β → γ) (stop : γ → Bool) (c₀ : α → γ)
  (a : α) (xs : List τ), Orbit nxt (start a) xs → ∀ (t : τ → ℕ) (v : τ → β) (Sx Sc Sm : ℕ),
  (∀ x ∈ met (fun c x => g c x (v x)) stop (c₀ a) xs, M.Runs x (t x) Sm (v x)) → (∀ x ∈ met (fun c x => g c x (v x)) stop (c₀ a) xs, size x ≤ Sx) →
  (∀ l, l <+: met (fun c x => g c x (v x)) stop (c₀ a) xs → size (l.foldl (fun c x => g c x (v x)) (c₀ a)) ≤ Sc) →
  (foldUntil start nxt M g stop c₀).Runs a ((met (fun c x => g c x (v x)) stop (c₀ a) xs).map fun x => t x + 1).sum (Sx + (Sc + Sm) + 1)
    ((met (fun c x => g c x (v x)) stop (c₀ a) xs).foldl (fun c x => g c x (v x)) (c₀ a))

/-- How far the search goes: one past the first hit, or to the end of the range. -/
def reach (q : ℕ → Bool) (n : ℕ) : ℕ := match (List.range n).find? q with | some i => i + 1 | none => n

/-- **«try all … until one is good».** The body need only halt on y < reach, that is, up to the
first y with p (v y). Steps: at most Σ_{y < reach} (t y + 1). Result: the least y < N a such that p
holds of v y, as for `firstRange`. -/
def StFirstUntil : Prop := ∀ (α β : Type) [HasSize α] (N : α → ℕ) (M : Stepped (α × ℕ) β) (p : β → Bool) (a : α) (t : ℕ → ℕ) (v : ℕ → β) (Sm : ℕ),
  (∀ y < reach (fun y => p (v y)) (N a), M.Runs (a, y) (t y) Sm (v y)) →
  (firstUntil N M p).Runs a (∑ y ∈ range (reach (fun y => p (v y)) (N a)), (t y + 1)) (size a + size (N a) + (size (N a) + 1 + Sm) + 1) ((List.range (N a)).find? fun y => p (v y))

/-- The leaves that are tested: those up to and including the first that passes. -/
def tested {ν : Type} (v : ν → Bool) (ls : List ν) : List ν := ls.take (ls.findIdx v + 1)

/-- **«for each … do if … then return».** The tree below root a has depth at most k. The test need
only halt on the leaves that are tested, that is, up to the first that passes. Steps: at most t + 2
for each leaf that is tested, and k more (for the nodes on the path to the last of them). Result:
whether some leaf passes, as for `walk`. -/
def StWalkUntil : Prop := ∀ (α ν : Type) [HasSize ν] (step : ν → Option (ν × ν)) (root : α → ν) (T : Stepped ν Bool) (k : ℕ) (a : α),
  (∀ x ∈ leaves step k (root a), step x = none) → ∀ (v : ν → Bool) (t Sm Sx : ℕ),
  (∀ x ∈ tested v (leaves step k (root a)), T.Runs x t Sm (v x)) → (∀ i, size ((Sparsify.round step)^[i] ([root a], [])).1 ≤ Sx) →
  (walkUntil step root T).Runs a ((tested v (leaves step k (root a))).length * (t + 2) + k) (Sx + (1 + (Sm + 1)) + 1) ((leaves step k (root a)).any v)

/-- The loop has polynomial-time steps if its body has and `start`, `nxt`, `g`, `stop`, `c₀` are
polynomial-time. -/
def StFoldUntilPoly : Prop := ∀ (α β γ τ : Type) [HasSize τ] [HasSize γ] [Enc α] [Enc β] [Enc γ] [Enc τ] [Carried γ] [Carried τ]
  (start : α → Option τ) (nxt : τ → Option τ) (M : Stepped τ β) [IsPolyT M] (g : γ → τ → β → γ) (stop : γ → Bool) (c₀ : α → γ),
  PolyT start → PolyT nxt → (PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2) → PolyT stop → PolyT c₀ → Nonempty (IsPolyT (foldUntil start nxt M g stop c₀))

/-- The two uses from the loop. -/
def StFirstUntilOf : Prop := StFoldUntil → StFirstUntil

/-- See `StFirstUntilOf`. -/
def StWalkUntilOf : Prop := StFoldUntil → StWalkUntil

end Exits
