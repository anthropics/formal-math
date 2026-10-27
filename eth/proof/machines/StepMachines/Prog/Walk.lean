/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Stepped
public import StepMachines.Math.SparsifyTree

/-! The depth-first walk of a binary tree given by a step function, as a computation cut into steps;
an expensive
test T is run on the leaves only, and the result says whether some leaf passes it. -/

namespace Groundwork.Stepped

open Groundwork.Sparsify (leaves)

variable {α β τ ν : Type}

/-! ### Run T only where sel picks an input for it -/

/-- T on sel x if that is some input; the result d at once if it is none. -/
@[expose] public def guard (sel : τ → Option ν) (T : Stepped ν β) (d : β) : Stepped τ β where
  σ := Option T.σ
  init x := (sel x).map T.init
  step := Option.map T.step
  out s := match s with | none => some d | some s => T.out s

public theorem guard_runs_none {sel : τ → Option ν} {T : Stepped ν β} {d : β} {x : τ} (h : sel x = none) :
    (guard sel T d).Runs x 0 1 d := by
  change (guard sel T d).Reaches 1 d ((sel x).map T.init) 0
  rw [h]
  exact .halt rfl le_rfl

theorem guard_reaches {sel : τ → Option ν} {T : Stepped ν β} {d b : β} {s : T.σ} {t S : ℕ}
    (h : T.Reaches S b s t) : (guard sel T d).Reaches (S + 1) b (some s) t := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho hs _ ih => exact .step ho (Nat.succ_le_succ hs) ih

public theorem guard_runs_some {sel : τ → Option ν} {T : Stepped ν β} {d b : β} {x : τ} {a : ν} {t S : ℕ}
    (h : sel x = some a) (hT : T.Runs a t S b) : (guard sel T d).Runs x t (S + 1) b := by
  change (guard sel T d).Reaches (S + 1) b ((sel x).map T.init) t
  rw [h]
  exact guard_reaches hT

/-! ### Facts on orbits and folds, for any loop -/

/-- A property of the first point that each move keeps holds on the whole orbit. -/
public theorem Orbit.forall {nxt : τ → Option τ} {o : Option τ} {xs : List τ} (h : Orbit nxt o xs) (P : τ → Prop)
    (h0 : ∀ x, o = some x → P x) (hs : ∀ y z, P y → nxt y = some z → P z) : ∀ y ∈ xs, P y := by
  induction h with
  | nil => simp
  | @cons x xs _ ih =>
    have hx := h0 x rfl
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact ih (fun z hz => hs x z hx hz) y hy

theorem foldl_or_sel (sel : τ → Option ν) (v : ν → Bool) (xs : List τ) (c : Bool) :
    xs.foldl (fun c x => c || ((sel x).map v).getD false) c = (c || (xs.filterMap sel).any v) := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    cases h : sel x <;> simp [h, Bool.or_assoc]

theorem sum_sel (sel : τ → Option ν) (t : ℕ) (xs : List τ) :
    (xs.map fun x => ((sel x).map fun _ => t).getD 0 + 1).sum = xs.length + (xs.filterMap sel).length * t := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, ih]
    cases h : sel x
    · simp only [List.filterMap_cons, h, Option.map_none, Option.getD_none, List.length_cons]; omega
    · simp only [List.filterMap_cons, h, Option.map_some, Option.getD_some, List.length_cons, Nat.succ_mul]; omega

/-! ### The walk -/

variable (step : ν → Option (ν × ν))

/-- The next stack: the top is dropped if it is a leaf, else replaced by its two children. -/
@[expose] public def walkNext : List ν → Option (List ν)
  | [] => none
  | s :: r => some (match step s with | none => r | some (l, h) => l :: h :: r)

/-- The top of the stack if it is a leaf. -/
@[expose] public def walkSel : List ν → Option ν
  | [] => none
  | s :: _ => match step s with | none => some s | some _ => none

/-- Does some leaf below root a pass the test T? -/
@[expose] public def walk [HasSize ν] (root : α → ν) (T : Stepped ν Bool) : Stepped α Bool :=
  foldWhile (fun a => some [root a]) (walkNext step) (guard (walkSel step) T false) (fun c _ b => c || b)
    fun _ => false

/-- The stacks met while the tree below s, cut at depth k, is walked above the rest r. -/
@[expose] public def visits : ℕ → ν → List ν → List (List ν)
  | 0, s, r => [s :: r]
  | k + 1, s, r =>
    match step s with
    | none => [s :: r]
    | some (l, h) => (s :: r) :: (visits k l (h :: r) ++ visits k h r)

public theorem orbit_visits (k : ℕ) (s : ν) (r : List ν) (ys : List (List ν))
    (hk : ∀ x ∈ leaves step k s, step x = none) (h : Orbit (walkNext step) (some r) ys) :
    Orbit (walkNext step) (some (s :: r)) (visits step k s r ++ ys) := by
  induction k generalizing s r ys with
  | zero =>
    have h0 : step s = none := hk s (by simp [leaves])
    have e : walkNext step (s :: r) = some r := by simp [walkNext, h0]
    exact .cons (by rw [e]; exact h)
  | succ k ih =>
    cases h0 : step s with
    | none =>
      have e : walkNext step (s :: r) = some r := by simp [walkNext, h0]
      have ev : visits step (k + 1) s r = [s :: r] := by simp [visits, h0]
      rw [ev]
      exact .cons (by rw [e]; exact h)
    | some lh =>
      obtain ⟨l, h'⟩ := lh
      have e : walkNext step (s :: r) = some (l :: h' :: r) := by simp [walkNext, h0]
      have ev : visits step (k + 1) s r = (s :: r) :: (visits step k l (h' :: r) ++ visits step k h' r) := by
        simp [visits, h0]
      have el : leaves step (k + 1) s = leaves step k l ++ leaves step k h' := by simp [leaves, h0]
      rw [el] at hk
      rw [ev, List.cons_append, List.append_assoc]
      refine .cons ?_
      rw [e]
      exact ih l (h' :: r) _ (fun x hx => hk x (List.mem_append_left _ hx))
        (ih h' r ys (fun x hx => hk x (List.mem_append_right _ hx)) h)

/-- 2·(number of leaves) − 1 stacks are met. -/
public theorem length_visits (k : ℕ) (s : ν) (r : List ν) :
    (visits step k s r).length + 1 = 2 * (leaves step k s).length := by
  induction k generalizing s r with
  | zero => simp [visits, leaves]
  | succ k ih =>
    cases h0 : step s with
    | none => simp [visits, leaves, h0]
    | some lh =>
      have h1 := ih lh.1 (lh.2 :: r)
      have h2 := ih lh.2 r
      simp only [visits, leaves, h0, List.length_cons, List.length_append]
      omega

/-- The tops that are leaves are the leaves, in order. -/
public theorem filterMap_visits (k : ℕ) (s : ν) (r : List ν) (hk : ∀ x ∈ leaves step k s, step x = none) :
    (visits step k s r).filterMap (walkSel step) = leaves step k s := by
  induction k generalizing s r with
  | zero =>
    have h0 : step s = none := hk s (by simp [leaves])
    simp [visits, leaves, walkSel, h0]
  | succ k ih =>
    cases h0 : step s with
    | none => simp [visits, leaves, walkSel, h0]
    | some lh =>
      have el : leaves step (k + 1) s = leaves step k lh.1 ++ leaves step k lh.2 := by simp [leaves, h0]
      rw [el] at hk ⊢
      have h1 := ih lh.1 (lh.2 :: r) fun x hx => hk x (List.mem_append_left _ hx)
      have h2 := ih lh.2 r fun x hx => hk x (List.mem_append_right _ hx)
      simp [visits, walkSel, h0, h1, h2]

theorem round_fst {y z : List ν} (h : walkNext step y = some z) (out : List ν) :
    (Sparsify.round step (y, out)).1 = z := by
  obtain _ | ⟨s, r⟩ := y
  · simp [walkNext] at h
  · simp only [walkNext, Option.some.injEq] at h
    subst h
    cases h0 : step s <;> simp [Sparsify.round, h0]

/-- Every stack on the orbit of [s] is the stack of the walk of SparsifyTree after some number of
rounds. -/
public theorem exists_round_of_orbit {s : ν} {xs : List (List ν)} (h : Orbit (walkNext step) (some [s]) xs) :
    ∀ y ∈ xs, ∃ i, ((Sparsify.round step)^[i] ([s], [])).1 = y := by
  refine h.forall _ (fun x hx => ⟨0, Option.some.inj hx⟩) ?_
  rintro y z ⟨i, hi⟩ hz
  refine ⟨i + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  generalize (Sparsify.round step)^[i] ([s], []) = p at hi
  obtain ⟨st, out⟩ := p
  subst hi
  exact round_fst step hz out

/-- The walk: (t + 2) steps a leaf, where the test takes t steps on each leaf. -/
public theorem walk_runs [HasSize ν] {root : α → ν} {T : Stepped ν Bool} (k : ℕ) (a : α)
    (hk : ∀ x ∈ leaves step k (root a), step x = none) (v : ν → Bool) (t Sm Sx : ℕ)
    (hT : ∀ x ∈ leaves step k (root a), T.Runs x t Sm (v x))
    (hS : ∀ i, size ((Sparsify.round step)^[i] ([root a], [])).1 ≤ Sx) :
    (walk step root T).Runs a ((leaves step k (root a)).length * (t + 2)) (Sx + (1 + (Sm + 1)) + 1)
      ((leaves step k (root a)).any v) := by
  have ho : Orbit (walkNext step) (some [root a]) (visits step k (root a) [] ++ [[]]) :=
    orbit_visits step k (root a) [] [[]] hk (.cons .nil)
  have hf : (visits step k (root a) [] ++ [[]]).filterMap (walkSel step) = leaves step k (root a) := by
    rw [List.filterMap_append, filterMap_visits step k (root a) [] hk]
    simp [walkSel]
  have hlen : (visits step k (root a) [] ++ [[]]).length = 2 * (leaves step k (root a)).length := by
    rw [List.length_append, ← length_visits step k (root a) []]
    rfl
  have key := foldWhile_runs (start := fun a : α => some [root a]) (M := guard (walkSel step) T false)
    (g := fun c _ b => c || b) (c₀ := fun _ => false) (a := a) ho
    (fun st => ((walkSel step st).map fun _ => t).getD 0) (fun st => ((walkSel step st).map v).getD false)
    Sx 1 (Sm + 1)
    (by
      intro st hst
      cases h : walkSel step st with
      | none => exact (guard_runs_none h).mono le_rfl (by omega)
      | some x => exact guard_runs_some h (hT x (hf ▸ List.mem_filterMap.2 ⟨st, hst, h⟩)))
    (by
      intro st hst
      obtain ⟨i, rfl⟩ := exists_round_of_orbit step ho st hst
      exact hS i)
    (fun _ _ => le_rfl)
  rw [sum_sel, foldl_or_sel, hf, hlen, Bool.false_or] at key
  exact key.mono (le_of_eq (by ring)) le_rfl

end Groundwork.Stepped
