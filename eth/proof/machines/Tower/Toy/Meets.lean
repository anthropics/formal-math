/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Tower.Toy.Defs
import Tower.Toy.Spec
import Tower.Kernel
import Tower.TowerRuns
import StepMachines.Prog.SideBasics
import Mathlib.Tactic.Ring

/-! # A toy recursion: the hypotheses of `TowerRuns` hold, and its conclusion

`toyMeets`: the two explicit machines meet the specification, so the hypotheses of `TowerRuns` are
not empty. `toyRuns`: ONE machine, on the input (ℓ, b), with query access to a table f at t
operations per query, returns the sum of f over all
bit strings of length ℓ within 2^ℓ·(t + 2ℓ + 5) operations; `toyPoly` (Toy/Machines.lean): that
machine has polynomial-time steps. -/

public section

namespace QueryMachines.Tower.Toy

open Groundwork Groundwork.Prog

/-- The size of the solver's state at the start. -/
theorem size_start (l : ℕ) : size ((l, Sum.inl ()) : ℕ × Ph) = l.size + 3 := by simp only [size_prod, size_inl, size_nat, size_unit]
/-- With the first result. -/
theorem size_one (l u : ℕ) : size ((l, Sum.inr (Sum.inl u)) : ℕ × Ph) = l.size + u.size + 4 := by simp only [size_prod, size_inl, size_inr, size_nat]; omega
/-- With both results. -/
theorem size_two (l u v : ℕ) : size ((l, Sum.inr (Sum.inr (Sum.inl (u, v)))) : ℕ × Ph) = l.size + u.size + v.size + 6 := by simp only [size_prod, size_inl, size_inr, size_nat]; omega
/-- When it is done. -/
theorem size_done (l v : ℕ) : size ((l, Sum.inr (Sum.inr (Sum.inr v))) : ℕ × Ph) = l.size + v.size + 5 := by simp only [size_prod, size_inr, size_nat]; omega

/-- A call one level down is answered by the sum over the strings that begin with the callee's bit. -/
theorem oracle_call (ℓ0 M0 l : ℕ) (b b' : Bool) (f : List Bool → Option ℕ) : (spec ℓ0 M0).oracle noG (l + 1, b) f (Sum.inl (l, b')) = some (sumF l fun q => f (b' :: q)) := by
  rw [← val_child ℓ0 M0]; exact if_pos rfl

/-- The solver, with its calls and queries answered as specified, returns the value. -/
theorem sol_within (ℓ0 M0 : ℕ) (c : ℕ × Bool) (f : List Bool → Option ℕ) (hG : (spec ℓ0 M0).Good c f) (tc tq : ℕ) :
    Sol.Within ((spec ℓ0 M0).oracle noG c f) (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW)) c (TS c.1 tc tq) (SS ℓ0 M0) (sumF c.1 f) := by
  obtain ⟨l, b⟩ := c
  obtain ⟨hl, hf⟩ := hG
  replace hl : l ≤ ℓ0 := hl
  replace hf : ∀ q : List Bool, q.length = l → ∃ a, a ≤ M0 ∧ f q = some a := hf
  have hls := Nat.size_le_size hl
  have hV : sumF l f ≤ 2 ^ ℓ0 * M0 := (sumF_le M0 l f hf).trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hl))
  have hVs := Nat.size_le_size hV
  show Sol.WithinFrom _ _ ((l, Sum.inl ()) : ℕ × Ph) (TS l tc tq) (SS ℓ0 M0) (sumF l f)
  cases l with
  | zero =>
    obtain ⟨a, ha, e⟩ := hf [] rfl
    have hval : sumF 0 f = a := by simp [sumF, e]
    rw [hval] at hVs ⊢
    have h2 : Sol.WithinFrom ((spec ℓ0 M0).oracle noG (0, b) f) (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW)) ((0, Sum.inr (Sum.inr (Sum.inr a))) : ℕ × Ph) 0 (SS ℓ0 M0) a :=
      wfHalt rfl (by show size ((0, Sum.inr (Sum.inr (Sum.inr a))) : ℕ × Ph) ≤ _; rw [size_done, SS]; omega)
    have h1 := wfQuery (M := Sol) (s := ((0, Sum.inl ()) : ℕ × Ph)) (x := Sum.inr (Sum.inl [])) (v := a) rfl rfl e
      (by show size ((0, Sum.inl ()) : ℕ × Ph) ≤ _; rw [size_start, SS]; omega) h2
    exact wfMono h1 (by show 0 + tq ≤ tq; omega) le_rfl
  | succ l =>
    have hu : sumF l (fun q => f (false :: q)) ≤ sumF (l + 1) f := Nat.le_add_right _ _
    have hv : sumF l (fun q => f (true :: q)) ≤ sumF (l + 1) f := Nat.le_add_left _ _
    have hus := Nat.size_le_size hu
    have hvs := Nat.size_le_size hv
    generalize hU : sumF l (fun q => f (false :: q)) = u at *
    generalize hW : sumF l (fun q => f (true :: q)) = v at *
    have hsum : sumF (l + 1) f = u + v := by simp only [sumF, hU, hW]
    rw [hsum] at hVs hus hvs ⊢
    have h5 : Sol.WithinFrom ((spec ℓ0 M0).oracle noG (l + 1, b) f) (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW)) ((l + 1, Sum.inr (Sum.inr (Sum.inr (u + v)))) : ℕ × Ph) 0 (SS ℓ0 M0) (u + v) :=
      wfHalt rfl (by show size ((l + 1, Sum.inr (Sum.inr (Sum.inr (u + v)))) : ℕ × Ph) ≤ _; rw [size_done, SS]; omega)
    have h4 := wfStep (M := Sol) (s := ((l + 1, Sum.inr (Sum.inr (Sum.inl (u, v)))) : ℕ × Ph)) rfl rfl
      (by show size ((l + 1, Sum.inr (Sum.inr (Sum.inl (u, v)))) : ℕ × Ph) ≤ _; rw [size_two, SS]; omega) h5
    have h3 := wfQuery (M := Sol) (s := ((l + 1, Sum.inr (Sum.inl u)) : ℕ × Ph)) (x := Sum.inl (l, true)) (v := v) rfl rfl (by rw [oracle_call, hW])
      (by show size ((l + 1, Sum.inr (Sum.inl u)) : ℕ × Ph) ≤ _; rw [size_one, SS]; omega) h4
    have h2 := wfQuery (M := Sol) (O := (spec ℓ0 M0).oracle noG (l + 1, b) f) (w := Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW)) (S := SS ℓ0 M0) (s := ((l + 1, Sum.inl ()) : ℕ × Ph))
      (x := Sum.inl (l, false)) (v := u) rfl (by simp [Sol, solAsk]) (by rw [oracle_call, hU])
      (by show size ((l + 1, Sum.inl ()) : ℕ × Ph) ≤ _; rw [size_start, SS]; omega)
      (by rw [show Sol.resume ((l + 1, Sum.inl ()) : ℕ × Ph) u = ((l + 1, Sum.inr (Sum.inl u)) : ℕ × Ph) by simp [Sol, solResume]]; exact h3)
    exact wfMono h2 (by show 0 + 1 + tc + tc ≤ 2 * tc + 1; omega) le_rfl

/-- The procedure, with the caller's tables, returns the entries of the callee's tables. -/
theorem inn_within (ℓ0 M0 : ℕ) (c : ℕ × Bool) (f : List Bool → Option ℕ) (c' : ℕ × Bool) (hG : (spec ℓ0 M0).Good c f) (hch : (spec ℓ0 M0).Child c f c') (q : List Bool) (a : ℕ)
    (ht : (spec ℓ0 M0).tab c' f q = some a) (tq : ℕ) : Inn.Within (Sum.elim f noG) (Sum.elim (fun _ => tq) noW) (c', q) (TI c'.1 tq) (SI ℓ0 M0) a := by
  replace hch : c'.1 + 1 = c.1 := hch
  replace ht : (if q.length = c'.1 then f (c'.2 :: q) else none) = some a := ht
  have hl : c.1 ≤ ℓ0 := hG.1
  by_cases hq : q.length = c'.1
  · rw [if_pos hq] at ht
    obtain ⟨a', ha', e⟩ := hG.2 (c'.2 :: q) (by rw [List.length_cons, hq]; exact hch)
    obtain rfl : a' = a := Option.some.inj (e.symm.trans ht)
    have has := Nat.size_le_size ha'
    have h2 : Inn.WithinFrom (Sum.elim f noG) (Sum.elim (fun _ => tq) noW) (Sum.inr a' : (Bool × List Bool) ⊕ ℕ) 0 (SI ℓ0 M0) a' :=
      wfHalt rfl (by show size (Sum.inr a' : (Bool × List Bool) ⊕ ℕ) ≤ _; rw [size_inr, size_nat, SI]; omega)
    have h1 := wfQuery (M := Inn) (s := (Sum.inl (c'.2, q) : (Bool × List Bool) ⊕ ℕ)) (x := Sum.inl (c'.2 :: q)) (v := a') rfl rfl ht
      (by show size (Sum.inl (c'.2, q) : (Bool × List Bool) ⊕ ℕ) ≤ _; rw [size_inl, size_prod, size_bool, size_bools, SI]; dsimp only; omega) h2
    exact wfMono h1 (by show 0 + tq ≤ tq; omega) le_rfl
  · rw [if_neg hq] at ht; cases ht

/-- The two machines meet the specification. -/
theorem toyMeets : ToyMeets := fun ℓ0 M0 => {
  child_lev := fun _ _ _ _ h => h
  child_good := fun c f c' hG h => by
    replace h : c'.1 + 1 = c.1 := h
    have hl : c.1 ≤ ℓ0 := hG.1
    refine ⟨(by omega : c'.1 ≤ ℓ0), fun q hq => ?_⟩
    replace hq : q.length = c'.1 := hq
    obtain ⟨a, ha, e⟩ := hG.2 (c'.2 :: q) (by rw [List.length_cons, hq]; exact h)
    exact ⟨a, ha, (if_pos hq).trans e⟩
  child_size := fun c f c' hG h => by
    replace h : c'.1 + 1 = c.1 := h
    have hl : c.1 ≤ ℓ0 := hG.1
    have := Nat.size_le_size (by omega : c'.1 ≤ ℓ0)
    rw [size_prod, size_nat, size_bool, SC]; omega
  sol := fun c f hG tc tq => sol_within ℓ0 M0 c f hG tc tq
  inn := fun c f c' hG hch q a ht tq => inn_within ℓ0 M0 c f c' hG hch q a ht tq }

/-- The recursion of the costs, solved. -/
theorem cost_toy : ∀ l t : ℕ, cost TS TI l t + 5 = 2 ^ l * (t + 2 * l + 5)
  | 0, t => by show t + 5 = _; ring
  | l + 1, t => by
    have ih := cost_toy l (t + 2)
    have e : 2 ^ (l + 1) * (t + 2 * (l + 1) + 5) = 2 * (2 ^ l * (t + 2 + 2 * l + 5)) := by ring
    rw [e, ← ih]
    show 2 * (cost TS TI l (t + 2) + 2) + 1 + 5 = _
    omega

/-- ONE machine, on the input (ℓ, b), with query access to a table f whose entries for the bit
strings of length ℓ are at most M0, at t operations per query: it returns the sum of f over all bit
strings of length ℓ within 2^ℓ·(t + 2ℓ + 5) operations. -/
theorem toyRuns : ToyRuns := by
  intro ℓ M0 t b f hf
  obtain ⟨own, L, hr, hc⟩ := towerRuns _ _ _ _ (spec ℓ M0) noG noW Sol Inn TS TI _ _ _ (toyMeets ℓ M0) (ℓ, b) f ⟨le_rfl, hf⟩ t
  rw [← sumF_eq]
  have := cost_toy ℓ t
  exact ⟨own, L, hr, hc.trans (by show cost TS TI ℓ t ≤ _; omega)⟩

end QueryMachines.Tower.Toy
