/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Exits.Defs
public import ToTuring.Poly.Range
public import ToTuring.Poly.Walk

/-! # A loop that can be left early: polynomial-time steps

`IsPolyT` (every part of a stepped computation is polynomial-time) for the machine `foldUntil` of
proof/threesat/Exits/Defs.lean, the loop that can be left early, which stands for line 10 of
Algorithm 1, «try all groupings into K_ℓ groups until one is good», and for lines 2 and 3 read for
deciding (stop at the first Φ with Count(Φ) > 0).
The proof is that of `Groundwork.IsPolyT.foldWhile` (proof/machines/ToTuring/Poly/IsPoly.lean). The
one difference: after a round the next point is «none if the new accumulator passes `stop`, else nxt
x», which is polynomial-time because `stop` is.
The chain Lemma 1 → Proposition 3 → Theorem 2 of this folder needs only `stFoldUntilPoly` from this
file: the two uses of the loop (`search_isPolyT` in proof/threesat/Exits/Grouping.lean,
`Suffices.satLoop_polyTimeSteps_of` in proof/threesat/Suffices/Loop.lean) take the statement
`StFoldUntilPoly` as a hypothesis, and `stFoldUntilPoly` proves it. -/

@[expose] public section

namespace Exits

open Groundwork Groundwork.Stepped

variable {α β γ τ ν : Type}

section foldUntil

variable [Enc τ] [Enc γ] [Enc α] [Enc β] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β} [IsPolyT M] {g : γ → τ → β → γ} {stop : γ → Bool} {c₀ : α → γ}

/-- One step of the loop that can be left is polynomial-time. -/
theorem IsPolyT.foldUntil_step (hn : PolyT nxt) (hg : PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2) (hst : PolyT stop) :
    PolyT (fun s : (τ × γ × M.σ) ⊕ γ => match s with
      | .inl p => match M.out p.2.2 with
        | some b => foldGo M (g p.2.1 p.1 b) (if stop (g p.2.1 p.1 b) then none else nxt p.1)
        | none => .inl (p.1, p.2.1, M.step p.2.2)
      | .inr c => .inr c) := by
  have h1 := IsPolyT.step (M := M)
  have h2 := IsPolyT.out (M := M)
  have hg' : PolyT fun q : (τ × γ × M.σ) × β => g q.1.2.1 q.1.1 q.2 := PolyT.comp (g := fun q : (τ × γ × M.σ) × β => (q.1.2.1, q.1.1, q.2)) hg (by fun_prop)
  have hsg : PolyT fun q : (τ × γ × M.σ) × β => stop (g q.1.2.1 q.1.1 q.2) := PolyT.comp hst hg'
  have hnx : PolyT fun q : (τ × γ × M.σ) × β => if stop (g q.1.2.1 q.1.1 q.2) then none else nxt q.1.1 := PolyT.ite' (PolyT.decide_eq_true hsg) (by fun_prop) (by fun_prop)
  have h3 : PolyT fun q : (τ × γ × M.σ) × β => foldGo M (g q.1.2.1 q.1.1 q.2) (if stop (g q.1.2.1 q.1.1 q.2) then none else nxt q.1.1) :=
    PolyT.comp (g := fun q : (τ × γ × M.σ) × β => (g q.1.2.1 q.1.1 q.2, if stop (g q.1.2.1 q.1.1 q.2) then none else nxt q.1.1)) (IsPolyT.foldGo_poly (M := M) (γ := γ)) (PolyT.prodMk hg' hnx)
  have h4 : PolyT fun p : τ × γ × M.σ => (M.out p.2.2).elim (.inl (p.1, p.2.1, M.step p.2.2) : (τ × γ × M.σ) ⊕ γ)
      fun b => foldGo M (g p.2.1 p.1 b) (if stop (g p.2.1 p.1 b) then none else nxt p.1) :=
    PolyT.optionElim (by fun_prop) (by fun_prop) h3
  have h5 : PolyT fun s : (τ × γ × M.σ) ⊕ γ => s.elim
      (fun p => (M.out p.2.2).elim (.inl (p.1, p.2.1, M.step p.2.2) : (τ × γ × M.σ) ⊕ γ)
        fun b => foldGo M (g p.2.1 p.1 b) (if stop (g p.2.1 p.1 b) then none else nxt p.1)) fun c => .inr c :=
    PolyT.sumElim (by fun_prop) (PolyT.comp (g := fun q : ((τ × γ × M.σ) ⊕ γ) × (τ × γ × M.σ) => q.2) h4 (by fun_prop)) (by fun_prop)
  refine h5.congr fun s => ?_
  rcases s with p | c
  · simp only [Sum.elim_inl]
    cases M.out p.2.2 <;> rfl
  · rfl

variable [HasSize τ] [HasSize γ] [Carried τ] [Carried γ]

/-- The loop `foldUntil` is `IsPolyT` if its body `M` is and `start`, `nxt`, `g`, `stop`, `c₀` are
polynomial-time. -/
@[instance_reducible] def IsPolyT.foldUntil (hs : PolyT start) (hn : PolyT nxt) (hg : PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2) (hst : PolyT stop) (hc : PolyT c₀) :
    IsPolyT (foldUntil start nxt M g stop c₀) where
  enc := (inferInstance : Enc ((τ × γ × M.σ) ⊕ γ))
  carried := (inferInstance : Carried ((τ × γ × M.σ) ⊕ γ))
  init := IsPolyT.foldWhile_init hs hc
  step := IsPolyT.foldUntil_step hn hg hst
  out := IsPolyT.foldWhile_out

end foldUntil

/-- **The loop that can be left has polynomial-time steps.** Behind «until one is good» (line 10 of
Algorithm 1) and the exit at the first Φ with Count(Φ) > 0 (lines 2 and 3 read for deciding). -/
theorem stFoldUntilPoly : StFoldUntilPoly := by
  intro α β γ τ _ _ _ _ _ _ _ _ start nxt M _ g stop c₀ hs hn hg hst hc
  exact ⟨IsPolyT.foldUntil hs hn hg hst hc⟩

/-- «try all groupings into K_ℓ groups until one is good» (line 10 of Algorithm 1): the search that
halts at the first good number has polynomial-time steps if its body has and the bound `N` and the
test `p` are polynomial-time. -/
@[instance_reducible] def IsPolyT.firstUntil [Enc α] [HasSize α] [Carried α] [Enc β] {N : α → ℕ} {M : Stepped (α × ℕ) β} [IsPolyT M] {p : β → Bool} (hN : PolyT N) (hp : PolyT p) :
    IsPolyT (firstUntil N M p) :=
  IsPolyT.foldUntil (IsPolyT.rangeStart_poly hN) (IsPolyT.rangeNext_poly hN)
    ((by fun_prop : PolyT fun q : Option ℕ × (α × ℕ) × β => q.1.elim (if p q.2.2 = true then some q.2.1.2 else none) fun i => some i).congr
      fun q => by rcases q with ⟨_ | i, y, b⟩ <;> rfl)
    (PolyT.optionIsSome PolyT.id') (by unfold noneC; fun_prop)

/-- «for each … do» (line 2 of Algorithm 1), read for deciding: stop at the first Φ with Count(Φ) >
0: the walk that halts at the first leaf that passes has polynomial-time steps if `step`, `root` and
the steps of the test `T` are polynomial-time. -/
@[instance_reducible] def IsPolyT.walkUntil [Enc ν] [HasSize ν] [Carried ν] [Enc α] {step : ν → Option (ν × ν)} {root : α → ν} {T : Stepped ν Bool} [IsPolyT T] (hs : PolyT step) (hr : PolyT root) :
    IsPolyT (walkUntil step root T) :=
  haveI := IsPolyT.guard (T := T) (d := false) (IsPolyT.walkSel_polyT hs)
  IsPolyT.foldUntil (by fun_prop) (IsPolyT.walkNext_polyT hs) (by fun_prop) PolyT.id' (by fun_prop)

end Exits
