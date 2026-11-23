/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.Groups

/-!
# Sums over contents, one step after the other

A step writes the cells of a set `wr`: it chooses `ω`, with a weight, and the contents of the cells, both as functions
of the cells written before. The sum, over all contents of the cells, of the product of the factors of the steps is
the sum over all executions.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset

variable {F : Type*} [CommRing F] {Ce W : Type*} [Fintype Ce] [DecidableEq Ce] [Fintype W] [DecidableEq W]

/-- Write the cells of `wr`. -/
def ovr (wr : Finset Ce) (v σ : Ce → W) : Ce → W := fun c => if c ∈ wr then v c else σ c

/-- A step: a sum over choices of a weight and contents of the cells of `wr`. The sum is given by its values
`sum σ f` at functions `f` of the new contents. -/
structure WStep (F Ce W : Type*) where
  /-- choices -/
  ι : Type
  /-- finitely many choices -/
  Om : Finset ι
  /-- cells that are written -/
  wr : Finset Ce
  /-- weight -/
  w : ι → (Ce → W) → F
  /-- contents -/
  v : ι → (Ce → W) → Ce → W
  /-- cells that are read -/
  rd : Finset Ce

namespace WStep

/-- The factor of a step. -/
def phi (s : WStep F Ce W) (y : Ce → W) : F :=
  ∑ ω ∈ s.Om, if ∀ c ∈ s.wr, y c = s.v ω y c then s.w ω y else 0

/-- The cells written by a list of steps. -/
def wrs : List (WStep F Ce W) → Finset Ce
  | [] => ∅
  | s :: l => s.wr ∪ wrs l

/-- The sum over all executions. -/
def exec : List (WStep F Ce W) → ((Ce → W) → F) → (Ce → W) → F
  | [], G, σ => G σ
  | s :: l, G, σ => ∑ ω ∈ s.Om, s.w ω σ * exec l G (ovr s.wr (s.v ω σ) σ)

/-- Steps read only what has been written before, and write every cell once. -/
def Seq : List (WStep F Ce W) → Prop
  | [] => True
  | s :: l => Disjoint s.wr (wrs l) ∧ (∀ ω ∈ s.Om, ∀ y y' : Ce → W, (∀ c, c ∉ s.wr ∪ wrs l → y c = y' c) →
      s.w ω y = s.w ω y' ∧ ∀ c ∈ s.wr, s.v ω y c = s.v ω y' c) ∧ Seq l

/-- **Sums over contents are sums over executions.** -/
theorem sum_eq_exec (l : List (WStep F Ce W)) (hl : Seq l) (G : (Ce → W) → F) (σ : Ce → W) :
    (∑ y ∈ univ.filter (fun y : Ce → W => ∀ c, c ∉ wrs l → y c = σ c), (l.map fun s => s.phi y).prod * G y) =
      exec l G σ := by
  induction l generalizing σ with
  | nil =>
    have : univ.filter (fun y : Ce → W => ∀ c, c ∉ wrs ([] : List (WStep F Ce W)) → y c = σ c) = {σ} := by
      ext y
      simp only [wrs, Finset.notMem_empty, not_false_eq_true, true_imp_iff, mem_filter, mem_univ, true_and,
        mem_singleton]
      exact funext_iff.symm
    rw [this, sum_singleton]
    simp [exec]
  | cons s l ih =>
    obtain ⟨hd, hr, hl⟩ := hl
    have h1 : ∀ y ∈ univ.filter (fun y : Ce → W => ∀ c, c ∉ wrs (s :: l) → y c = σ c),
        ((s :: l).map fun s => s.phi y).prod * G y = ∑ ω ∈ s.Om,
          if ∀ c ∈ s.wr, y c = s.v ω σ c then s.w ω σ * ((l.map fun s => s.phi y).prod * G y) else 0 := by
      intro y hy
      have hy' := (mem_filter.1 hy).2
      rw [List.map_cons, List.prod_cons, phi, mul_assoc, sum_mul]
      refine sum_congr rfl fun ω hω => ?_
      obtain ⟨e1, e2⟩ := hr ω hω y σ hy'
      have e3 : (∀ c ∈ s.wr, y c = s.v ω y c) ↔ ∀ c ∈ s.wr, y c = s.v ω σ c := by
        constructor
        · intro h c hc
          rw [← e2 c hc, h c hc]
        · intro h c hc
          rw [e2 c hc, h c hc]
      simp only [e3, e1, ite_mul, zero_mul]
    rw [sum_congr rfl h1, sum_comm, exec]
    refine sum_congr rfl fun ω _ => ?_
    rw [← ih hl, mul_sum, ← sum_filter, filter_filter]
    refine sum_congr ?_ fun y _ => rfl
    ext y
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩ c hc
      by_cases hcs : c ∈ s.wr
      · rw [ovr, if_pos hcs, h2 c hcs]
      · rw [ovr, if_neg hcs]
        exact h1 c fun h => (mem_union.1 h).elim hcs hc
    · intro h
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · rw [wrs, mem_union, not_or] at hc
        rw [h c hc.2, ovr, if_neg hc.1]
      · rw [h c fun h' => (disjoint_left.1 hd hc h'), ovr, if_pos hc]

theorem mem_wrs {l : List (WStep F Ce W)} {c : Ce} : c ∈ wrs l ↔ ∃ s ∈ l, c ∈ s.wr := by
  induction l with
  | nil => simp [wrs]
  | cons s l ih => simp [wrs, ih]

/-- A criterion for `Seq`. -/
theorem seq_of {l : List (WStep F Ce W)}
    (h1 : l.Pairwise fun s s' => Disjoint s.wr s'.wr ∧ Disjoint s.rd s'.wr)
    (h2 : ∀ s ∈ l, Disjoint s.rd s.wr ∧ ∀ ω ∈ s.Om, ∀ y y' : Ce → W, (∀ c ∈ s.rd, y c = y' c) →
      s.w ω y = s.w ω y' ∧ ∀ c ∈ s.wr, s.v ω y c = s.v ω y' c) : Seq l := by
  induction l with
  | nil => trivial
  | cons s l ih =>
    rw [List.pairwise_cons] at h1
    obtain ⟨h3, h4⟩ := h2 s List.mem_cons_self
    refine ⟨?_, fun ω hω y y' hy => h4 ω hω y y' fun c hc => hy c ?_, ih h1.2 fun s' hs' =>
      h2 s' (List.mem_cons_of_mem _ hs')⟩
    · rw [disjoint_left]
      intro c hc hc'
      obtain ⟨s', hs', hc''⟩ := mem_wrs.1 hc'
      exact disjoint_left.1 (h1.1 s' hs').1 hc hc''
    · rw [mem_union, not_or]
      refine ⟨disjoint_left.1 h3 hc, fun hc' => ?_⟩
      obtain ⟨s', hs', hc''⟩ := mem_wrs.1 hc'
      exact disjoint_left.1 (h1.1 s' hs').2 hc hc''

end WStep

end Nc.Grp
