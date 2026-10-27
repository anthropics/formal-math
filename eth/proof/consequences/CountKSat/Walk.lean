/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSat.Interfaces
public import ToTuring.Poly.Walk
import all StepMachines.Prog.Walk
import Mathlib.Tactic.Ring

/-! # The walk that sums over the leaves

`proof/machines/StepMachines/Prog/Walk.lean` walks the tree of a step function depth first and says
whether some leaf passes a test. `walkSum` is the same loop with a number
in place of the truth value: it adds up the numbers that a computation T returns on the leaves. This
file has the lemma on trees (a quantity that splits at every
node is the sum over the leaves), the steps, the space and the result of `walkSum`, and its
polynomial-time certificate. The orbit of the loop, its length and its
leaves are taken from that file unchanged. -/

namespace CountKSat

open Groundwork Groundwork.Stepped Groundwork.Sparsify

variable {α ν : Type}

namespace Walk

variable {τ : Type}

/-- The loop's fold adds v over the points that sel picks. -/
theorem foldl_add_sel (sel : τ → Option ν) (v : ν → ℕ) (xs : List τ) (c : ℕ) :
    xs.foldl (fun c x => c + ((sel x).map v).getD 0) c = c + ((xs.filterMap sel).map v).sum := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    cases h : sel x <;> simp [h, Nat.add_assoc]

/-- The sum over a prefix of a list of numbers is at most the sum over the whole list. -/
theorem sum_prefix_le (sel : τ → Option ν) (v : ν → ℕ) {l xs : List τ} (h : l <+: xs) :
    ((l.filterMap sel).map v).sum ≤ ((xs.filterMap sel).map v).sum := by
  obtain ⟨r, rfl⟩ := h
  rw [List.filterMap_append, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

end Walk

open Walk

/-- A quantity that is the sum of its values at the two children, at every node with the invariant
G, is the sum of its values at the leaves. -/
public theorem sum_leaves {σ : Type*} {step : σ → Option (σ × σ)} {G : σ → ℕ → ℕ → Prop} {q : ℕ}
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q)) (f : σ → ℕ)
    (hf : ∀ s p t l h, G s p t → step s = some (l, h) → f s = f l + f h)
    (d : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) : f s = ((leaves step d s).map f).sum := by
  induction d generalizing s p t with
  | zero => simp [leaves]
  | succ d ih =>
    cases h0 : step s with
    | none => simp [leaves, h0]
    | some lh =>
      obtain ⟨l, h⟩ := lh
      obtain ⟨h1, h2⟩ := hs s p t l h hG h0
      simp only [leaves, h0, List.map_append, List.sum_append]
      rw [← ih l _ _ h1, ← ih h _ _ h2]
      exact hf s p t l h hG h0

/-- If T takes t steps on each leaf and the sum over the leaves is below 2^B, the summing walk takes
t + 2 steps per leaf and returns that sum. -/
public theorem walkSum_runs [HasSize ν] (step : ν → Option (ν × ν)) {root : α → ν} {T : Stepped ν ℕ} (d : ℕ) (a : α)
    (hd : ∀ x ∈ leaves step d (root a), step x = none) (v : ν → ℕ) (t Sm Sx B : ℕ)
    (hT : ∀ x ∈ leaves step d (root a), T.Runs x t Sm (v x))
    (hS : ∀ i, size ((Sparsify.round step)^[i] ([root a], [])).1 ≤ Sx)
    (hB : ((leaves step d (root a)).map v).sum < 2 ^ B) :
    (walkSum step root T).Runs a ((leaves step d (root a)).length * (t + 2)) (Sx + (B + 1 + (Sm + 1)) + 1)
      ((leaves step d (root a)).map v).sum := by
  have ho : Orbit (walkNext step) (some [root a]) (visits step d (root a) [] ++ [[]]) :=
    orbit_visits step d (root a) [] [[]] hd (.cons .nil)
  have hf : (visits step d (root a) [] ++ [[]]).filterMap (walkSel step) = leaves step d (root a) := by
    rw [List.filterMap_append, filterMap_visits step d (root a) [] hd]
    simp [walkSel]
  have hlen : (visits step d (root a) [] ++ [[]]).length = 2 * (leaves step d (root a)).length := by
    rw [List.length_append, ← length_visits step d (root a) []]
    rfl
  have key := foldWhile_runs (start := fun a : α => some [root a]) (M := guard (walkSel step) T 0)
    (g := fun c _ b => c + b) (c₀ := fun _ => 0) (a := a) ho
    (fun st => ((walkSel step st).map fun _ => t).getD 0) (fun st => ((walkSel step st).map v).getD 0)
    Sx (B + 1) (Sm + 1)
    (by
      intro st hst
      cases h : walkSel step st with
      | none => exact (guard_runs_none h).mono le_rfl (by omega)
      | some x => exact guard_runs_some h (hT x (hf ▸ List.mem_filterMap.2 ⟨st, hst, h⟩)))
    (by
      intro st hst
      obtain ⟨i, rfl⟩ := exists_round_of_orbit step ho st hst
      exact hS i)
    (by
      intro l hl
      rw [foldl_add_sel, Nat.zero_add]
      have h1 := sum_prefix_le (walkSel step) v hl
      rw [hf] at h1
      exact Nat.succ_le_succ (Nat.size_le.2 (lt_of_le_of_lt h1 hB)))
  rw [sum_sel, foldl_add_sel, hf, hlen, Nat.zero_add] at key
  exact key.mono (le_of_eq (by ring)) le_rfl

/-- Init, step and out of the summing walk are polynomial-time if `step`, `root` and the parts of T
are. -/
@[instance_reducible] public def isPolyT_walkSum [Enc ν] [HasSize ν] [Carried ν] [Enc α] {step : ν → Option (ν × ν)}
    {root : α → ν} {T : Stepped ν ℕ} [IsPolyT T] (hs : PolyT step) (hr : PolyT root) : IsPolyT (walkSum step root T) :=
  haveI := IsPolyT.guard (T := T) (d := 0) (IsPolyT.walkSel_polyT hs)
  IsPolyT.foldWhile (by fun_prop) (IsPolyT.walkNext_polyT hs) (by fun_prop) (by fun_prop)

/-! ### The interface statements of `proof/consequences/CountKSat/Interfaces.lean` that this file proves -/

/-- The lemma on trees, as the interface states it. -/
public theorem stSumLeaves : StSumLeaves := fun _ _ _ _ hs f hf d s p t hG => sum_leaves hs f hf d s p t hG

/-- The steps, the space and the result of the summing walk, as the interface states them. -/
public theorem stWalkSum : StWalkSum := fun _ _ _ step _ _ d a hd v t Sm Sx B hT hS hB =>
  walkSum_runs step d a hd v t Sm Sx B hT hS hB

end CountKSat
