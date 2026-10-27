/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedToPadded.Defs
import CountedToPadded.Compare
import ToTuring.Closure.Fold
import ToTuring.Lib.List1b

/-! # A step machine run on a padding string

Proofs of `EveryWordIsCompared`, `RunForIsRight`, `RunForPolyFrom` and `RunForPoly` (Defs.lean). -/

public section

namespace QueryMachines.Bridge.Proof

open Groundwork Groundwork.PolyT PaddedDescent.F

section right

variable {α β : Type} {N : Stepped α β} [Enc N.σ] [Carried N.σ] {S room : ℕ} {b : β}

omit [Enc N.σ] [Carried N.σ] in
/-- The first state of a run is within the bound on the sizes. -/
theorem reaches_size {s : N.σ} {t : ℕ} (h : N.Reaches S b s t) : size s ≤ S := by
  cases h with
  | halt _ h => exact h
  | step _ h _ => exact h

/-- A state of size at most S is not cut. -/
theorem cutAt_some (hS : 7 * S + 2 ≤ room) {s : N.σ} (h : size s ≤ S) : cutAt room (some s) = some s := by
  have := Carried.le s
  exact if_pos (by rw [len_some]; omega)

/-- A halted state stays to the end. -/
theorem fold_halted (hS : 7 * S + 2 ≤ room) {s : N.σ} (h1 : N.out s = some b) (h2 : size s ≤ S) (fuel : U) :
    fuel.foldl (fun (s : Option N.σ) _ => cutAt room (s.map (stay N))) (some s) = some s := by
  induction fuel with
  | nil => rfl
  | cons u l ih =>
    have e : stay N s = s := if_pos (by rw [h1]; rfl)
    rw [List.foldl_cons, Option.map_some, e, cutAt_some hS h2, ih]

/-- From a state from which N halts with b within T steps, the fold ends in a state with the result
b once the fuel has at least T units. -/
theorem fold_reaches (hS : 7 * S + 2 ≤ room) {s : N.σ} {T : ℕ} (h : N.Reaches S b s T) : ∀ fuel : U, T ≤ fuel.length →
    (fuel.foldl (fun (s : Option N.σ) _ => cutAt room (s.map (stay N))) (some s)).bind N.out = some b := by
  induction h with
  | halt h1 h2 => intro fuel _; rw [fold_halted hS h1 h2]; exact h1
  | @step s t h1 h2 h3 ih =>
    intro fuel hf
    rcases fuel with _ | ⟨u, l⟩
    · simp at hf
    · have e : stay N s = N.step s := if_neg (by rw [h1]; simp)
      rw [List.foldl_cons, Option.map_some, e, cutAt_some hS (reaches_size h3)]
      exact ih l (by rw [List.length_cons] at hf; omega)

end right

/-- The output of the cut has length at most `room + 2`: a value that is kept has length at most
`room`, and `none` has length at most 2. -/
theorem len_cutAt_le {γ : Type} [Enc γ] (room : ℕ) (x : Option γ) : len (cutAt room x) ≤ room + 2 := by
  unfold cutAt
  split
  · omega
  · rw [len_none]; omega

end QueryMachines.Bridge.Proof

namespace QueryMachines.Bridge

open Groundwork Groundwork.PolyT PaddedDescent.F Proof

/-- Whether the word of a value is at most as long as a padding string is decided in polynomial
time, for every coding. -/
theorem everyWordIsCompared : EveryWordIsCompared := fun α _ => wordCompared α

/-- `runFor` returns the result of the machine once fuel and room suffice. -/
theorem runForIsRight : RunForIsRight := by
  intro α β N _ _ a T S b fuel room h hT hS
  unfold runFor
  rw [cutAt_some hS (reaches_size h)]
  exact fold_reaches hS h fuel hT

/-- `RunForPoly` follows from `EveryWordIsCompared`. -/
theorem runForPolyFrom : RunForPolyFrom := by
  intro hC α β _ _ N _
  have hcut : PolyT fun q : U × Option N.σ => cutAt q.1.length q.2 := PolyT.ite' (hC (Option N.σ)) (by fun_prop) (by fun_prop)
  have hstay : PolyT (stay N) := by
    have := IsPolyT.out (M := N); have := IsPolyT.step (M := N)
    unfold stay; fun_prop
  have hinit := IsPolyT.init (M := N)
  have hout := IsPolyT.out (M := N)
  have hfold : PolyT fun p : (U × U) × α => p.1.1.foldl (fun (s : Option N.σ) _ => cutAt p.1.2.length (s.map (stay N))) (cutAt p.1.2.length (some (N.init p.2))) := by
    refine PolyT.foldl (l := fun p : (U × U) × α => p.1.1) (a := fun p => cutAt p.1.2.length (some (N.init p.2))) (g := fun p (s : Option N.σ) _ => cutAt p.1.2.length (s.map (stay N))) (by fun_prop)
      (comp hcut (by fun_prop : PolyT fun p : (U × U) × α => (p.1.2, some (N.init p.2))))
      (comp hcut (prodMk (by fun_prop) (PolyT.optionMap (f := fun _ s => stay N s) (comp hstay (by fun_prop)) (by fun_prop))))
      ⟨fun n => n + 2, PB.id'.add (PB.const 2), fun p k => ?_⟩
    have hr : p.1.2.length ≤ len p := by
      have h1 := length_le_len p.1.2
      have h2 : len p = len p.1 + len p.2 + 2 := len_pair p.1 p.2
      have h3 : len p.1 = len p.1.1 + len p.1.2 + 2 := len_pair p.1.1 p.1.2
      omega
    have key : ∀ (l : List Unit) (c : Option N.σ), len c ≤ p.1.2.length + 2 → len (l.foldl (fun (s : Option N.σ) _ => cutAt p.1.2.length (s.map (stay N))) c) ≤ p.1.2.length + 2 := by
      intro l
      induction l with
      | nil => intro c h; exact h
      | cons u l ih => intro c _; exact ih _ (len_cutAt_le _ _)
    have := key (p.1.1.take k) _ (len_cutAt_le p.1.2.length (some (N.init p.2)))
    show _ ≤ len p + 2
    omega
  exact PolyT.optionBind (f := fun _ s => N.out s) (comp hout (by fun_prop)) hfold

/-- `runFor N` is polynomial-time for every step machine N with polynomial-time steps. -/
theorem runForPoly : RunForPoly := runForPolyFrom everyWordIsCompared

end QueryMachines.Bridge
