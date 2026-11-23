/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Pointer machines

Every step loads one record and allocates one record, at the next address.
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset

/-- A pointer machine with modes M, kinds of records K, weights in A. The variables of a step are: the 5 registers,
the 3 fields of the record that is loaded, the new address. -/
structure Mach (A M K : Type*) where
  /-- rules -/
  Rl : Type
  [fR : Fintype Rl]
  [dR : DecidableEq Rl]
  /-- mode before -/
  src : Rl → M
  /-- mode after -/
  dst : Rl → M
  /-- the bit that is read from the input -/
  rd : Rl → Option Bool
  /-- kind of the record that is loaded -/
  lk : Rl → K
  /-- the register with its address -/
  la : Rl → Fin 5
  /-- kind of the record that is allocated -/
  ak : Rl → K
  /-- its fields -/
  af : Rl → Fin 3 → Fin 9
  /-- the registers after the step -/
  dr : Rl → Fin 5 → Fin 9
  /-- weight -/
  wt : Rl → A
  /-- first mode -/
  m0 : M
  /-- last mode -/
  mh : M
  /-- kind of the record with address 0 -/
  kN : K

attribute [instance] Mach.fR Mach.dR

variable {A M K : Type*} (P : Mach A M K)

/-- A register as a variable. -/
def rv (i : Fin 5) : Fin 9 := ⟨i.1, by omega⟩

/-- Records: kind, address, fields. -/
abbrev Rec (K : Type*) := K × (Fin 4 → ℕ)

namespace Mach

/-- A step: a rule and the values of the variables. -/
abbrev Step := P.Rl × (Fin 9 → ℕ)

variable {P}

/-- The record that is loaded. -/
def ld (st : P.Step) : Rec K := (P.lk st.1, ![st.2 (rv (P.la st.1)), st.2 5, st.2 6, st.2 7])

/-- The record that is allocated. -/
def al (st : P.Step) : Rec K :=
  (P.ak st.1, ![st.2 8, st.2 (P.af st.1 0), st.2 (P.af st.1 1), st.2 (P.af st.1 2)])

/-- The weight of a list of steps. -/
def wts [CommMonoid A] (tr : List P.Step) : A := (tr.map fun st => P.wt st.1).prod

variable (P)

/-- States. -/
structure State where
  /-- mode -/
  mode : M
  /-- registers -/
  regs : Fin 5 → ℕ
  /-- records -/
  heap : List (Rec K)
  /-- last address -/
  n : ℕ
  /-- the rest of the input -/
  inp : List Bool

variable {P}

/-- A step is possible. -/
structure Fire (σ : State (M := M) (K := K)) (st : P.Step) : Prop where
  src : P.src st.1 = σ.mode
  regs : ∀ i, st.2 (rv i) = σ.regs i
  fresh : st.2 8 = σ.n + 1
  load : ld st ∈ σ.heap
  read : (P.rd st.1).toList <+: σ.inp

/-- The state after a step. -/
def nxt (σ : State (M := M) (K := K)) (st : P.Step) : State (M := M) (K := K) where
  mode := P.dst st.1
  regs i := st.2 (P.dr st.1 i)
  heap := σ.heap ++ [al st]
  n := σ.n + 1
  inp := σ.inp.drop (P.rd st.1).toList.length

variable (P) in
/-- Accepting runs. -/
def Seq : State (M := M) (K := K) → List P.Step → Prop
  | σ, [] => σ.mode = P.mh ∧ σ.inp = []
  | σ, st :: tr => Fire σ st ∧ Seq (nxt σ st) tr

/-- Runs that are checked globally: loads may refer to any record. -/
structure GV (σ : State (M := M) (K := K)) (tr : List P.Step) : Prop where
  modes : σ.mode :: tr.map (fun st => P.dst st.1) = tr.map (fun st => P.src st.1) ++ [P.mh]
  regs : ∀ i, ∃ fin, σ.regs i :: tr.map (fun st => st.2 (P.dr st.1 i)) = tr.map (fun st => st.2 (rv i)) ++ [fin]
  fresh : tr.map (fun st => st.2 8) = (List.range tr.length).map fun j => σ.n + 1 + j
  read : (tr.flatMap fun st => (P.rd st.1).toList) = σ.inp
  load : ∀ st ∈ tr, ld st ∈ σ.heap ++ tr.map al

/-- The heap is closed. -/
structure Closed (σ : State (M := M) (K := K)) : Prop where
  le : ∀ c ∈ σ.heap, ∀ i, c.2 i ≤ σ.n
  ex : ∀ j ≤ σ.n, ∃ c ∈ σ.heap, c.2 0 = j
  reg : ∀ i, σ.regs i ≤ σ.n

theorem env_cases (p : Fin 9 → Prop) (h : ∀ i : Fin 5, p (rv i)) (h5 : p 5) (h6 : p 6) (h7 : p 7) (h8 : p 8) :
    ∀ i, p i := by
  intro i
  fin_cases i
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h5
  · exact h6
  · exact h7
  · exact h8

theorem Closed.env {σ : State (M := M) (K := K)} (hσ : Closed σ) {st : P.Step} (hf : Fire σ st) :
    ∀ i, st.2 i ≤ σ.n + 1 := by
  have hl := hσ.le _ hf.load
  refine env_cases _ (fun i => ?_) ?_ ?_ ?_ ?_
  · rw [hf.regs]
    exact (hσ.reg i).trans (Nat.le_succ _)
  · exact (hl 1).trans (Nat.le_succ _)
  · exact (hl 2).trans (Nat.le_succ _)
  · exact (hl 3).trans (Nat.le_succ _)
  · exact hf.fresh.le

theorem Closed.nxt {σ : State (M := M) (K := K)} (hσ : Closed σ) {st : P.Step} (hf : Fire σ st) :
    Closed (Mach.nxt σ st) := by
  have he := hσ.env hf
  constructor
  · intro c hc i
    simp only [Mach.nxt, List.mem_append, List.mem_singleton] at hc ⊢
    rcases hc with hc | rfl
    · exact (hσ.le c hc i).trans (Nat.le_succ _)
    · have h4 : ∀ i : Fin 4, (al st).2 i ≤ σ.n + 1 := by
        intro i
        fin_cases i
        · exact he _
        · exact he _
        · exact he _
        · exact he _
      exact h4 i
  · intro j hj
    simp only [Mach.nxt] at hj ⊢
    rcases Nat.lt_or_ge σ.n j with h | h
    · refine ⟨al st, by simp, ?_⟩
      have : (al st).2 0 = st.2 8 := rfl
      rw [this, hf.fresh]
      omega
    · obtain ⟨c, hc, h0⟩ := hσ.ex j h
      exact ⟨c, by simp [hc], h0⟩
  · intro i
    exact he _

/-- The global check is the same as the check step by step, if the heap is closed. -/
theorem gv_iff {σ : State (M := M) (K := K)} (hσ : Closed σ) (tr : List P.Step) : GV σ tr ↔ Seq P σ tr := by
  induction tr generalizing σ with
  | nil =>
    constructor
    · rintro ⟨h1, -, -, h4, -⟩
      exact ⟨by simpa using h1, by simpa using h4.symm⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by simp [h1], fun i => ⟨σ.regs i, rfl⟩, rfl, by simp [h2], by simp⟩
  | cons st tr ih =>
    constructor
    · intro h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h1
      have hr : ∀ i, σ.regs i = st.2 (rv i) ∧ ∃ fin, st.2 (P.dr st.1 i) :: tr.map (fun st => st.2 (P.dr st.1 i)) =
          tr.map (fun st => st.2 (rv i)) ++ [fin] := by
        intro i
        obtain ⟨fin, hfin⟩ := h2 i
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at hfin
        exact ⟨hfin.1, fin, hfin.2⟩
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_cons, List.cons.injEq, List.map_map] at h3
      have hfr : ∀ st' ∈ tr, σ.n + 1 < st'.2 8 := by
        intro st' hst
        have hm : st'.2 8 ∈ tr.map fun st => st.2 8 := List.mem_map.2 ⟨st', hst, rfl⟩
        rw [h3.2, List.mem_map] at hm
        obtain ⟨j, -, hj⟩ := hm
        simp only [Function.comp] at hj
        omega
      have hload : ld st ∈ σ.heap := by
        have hm := h5 st (by simp)
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · exact hm
        · exfalso
          have ha : (ld st).2 0 ≤ σ.n := by
            have : (ld st).2 0 = st.2 (rv (P.la st.1)) := rfl
            rw [this, ← (hr _).1]
            exact hσ.reg _
          rw [List.map_cons, List.mem_cons, List.mem_map] at hm
          rcases hm with e | ⟨st', hst, e⟩
          · have h0 : (ld st).2 0 = (al st).2 0 := by rw [e]
            have h8 : (al st).2 0 = st.2 8 := rfl
            have := h3.1
            omega
          · have h0 : (ld st).2 0 = (al st').2 0 := by rw [e]
            have h8 : (al st').2 0 = st'.2 8 := rfl
            have := hfr st' hst
            omega
      have hf : Fire σ st := by
        refine ⟨h1.1.symm, fun i => (hr i).1.symm, by simpa using h3.1, hload, ?_⟩
        rw [← h4, List.flatMap_cons]
        exact List.prefix_append _ _
      refine ⟨hf, (ih (hσ.nxt hf)).1 ⟨h1.2, fun i => (hr i).2, ?_, ?_, ?_⟩⟩
      · rw [h3.2]
        refine List.map_congr_left fun j _ => ?_
        simp only [Function.comp, Mach.nxt]
        omega
      · simp only [Mach.nxt]
        rw [← h4, List.flatMap_cons, List.drop_left]
      · intro st' hst
        have hm := h5 st' (by simp [hst])
        simp only [Mach.nxt]
        rw [List.map_cons] at hm
        simpa using hm
    · rintro ⟨hf, h⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := (ih (hσ.nxt hf)).2 h
      refine ⟨?_, fun i => ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.cons_append, List.cons.injEq]
        exact ⟨hf.src.symm, h1⟩
      · obtain ⟨fin, hfin⟩ := h2 i
        refine ⟨fin, ?_⟩
        simp only [List.map_cons, List.cons_append, List.cons.injEq]
        exact ⟨(hf.regs i).symm, hfin⟩
      · rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_cons, List.cons.injEq, List.map_map]
        refine ⟨hf.fresh, ?_⟩
        rw [h3]
        refine List.map_congr_left fun j _ => ?_
        simp only [Function.comp, Mach.nxt]
        omega
      · rw [List.flatMap_cons, h4]
        simp only [Mach.nxt]
        obtain ⟨rest, hrest⟩ := hf.read
        rw [← hrest, List.drop_left]
      · intro st' hst
        rw [List.mem_cons] at hst
        rw [List.map_cons]
        rcases hst with rfl | hst
        · exact List.mem_append_left _ hf.load
        · have := h5 st' hst
          simp only [Mach.nxt] at this
          simpa using this

/-- All values of the variables are at most the number of steps. -/
theorem Seq.le {σ : State (M := M) (K := K)} (hσ : Closed σ) {tr : List P.Step} (h : Seq P σ tr) :
    ∀ st ∈ tr, ∀ i, st.2 i ≤ σ.n + tr.length := by
  induction tr generalizing σ with
  | nil => simp
  | cons st tr ih =>
    obtain ⟨hf, h⟩ := h
    intro st' hst i
    rw [List.mem_cons] at hst
    rw [List.length_cons]
    rcases hst with rfl | hst
    · have := hσ.env hf i
      omega
    · have := ih (hσ.nxt hf) h st' hst i
      simp only [Mach.nxt] at this
      omega

variable [CommRing A]

variable (P) in
/-- The accepting runs from a state are finitely many; their weights have the sum S, their lengths are at most B. -/
def SumTo {A M K : Type*} [CommRing A] (P : Mach A M K) (σ : State (M := M) (K := K)) (S : A) (B : ℤ) : Prop :=
  ∃ R : Finset (List P.Step), (∀ tr, tr ∈ R ↔ Seq P σ tr) ∧ ∑ tr ∈ R, wts tr = S ∧ ∀ tr ∈ R, (tr.length : ℤ) ≤ B

theorem SumTo.mono {σ : State (M := M) (K := K)} {S : A} {B B' : ℤ} (h : SumTo P σ S B) (hB : B ≤ B') : SumTo P σ S B' := by
  obtain ⟨R, h1, h2, h3⟩ := h
  exact ⟨R, h1, h2, fun tr htr => (h3 tr htr).trans hB⟩

/-- The end. -/
theorem SumTo.halt {σ : State (M := M) (K := K)} (hm : σ.mode = P.mh) (hi : σ.inp = []) (hP : ∀ r, P.src r ≠ P.mh) :
    SumTo P σ 1 0 := by
  classical
  refine ⟨{[]}, fun tr => ?_, by simp [wts], by simp⟩
  rw [Finset.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨hm, hi⟩
  · intro h
    rcases tr with _ | ⟨st, tr⟩
    · rfl
    · exact absurd (h.1.src.trans hm) (hP _)

/-- One step: finitely many possibilities. -/
theorem SumTo.fin {σ : State (M := M) (K := K)} (hm : σ.mode ≠ P.mh) (F : Finset P.Step) (hF : ∀ st, st ∈ F ↔ Fire σ st)
    (S : P.Step → A) (B : ℤ) (h : ∀ st ∈ F, SumTo P (nxt σ st) (S st) B) :
    SumTo P σ (∑ st ∈ F, P.wt st.1 * S st) (B + 1) := by
  classical
  have h' : ∀ st, ∃ R : Finset (List P.Step), st ∈ F → (∀ tr, tr ∈ R ↔ Seq P (nxt σ st) tr) ∧
      ∑ tr ∈ R, wts tr = S st ∧ ∀ tr ∈ R, (tr.length : ℤ) ≤ B := by
    intro st
    by_cases hst : st ∈ F
    · obtain ⟨R, hR⟩ := h st hst
      exact ⟨R, fun _ => hR⟩
    · exact ⟨∅, fun h => absurd h hst⟩
  choose R hR using h'
  refine ⟨F.biUnion fun st => (R st).image fun tr => st :: tr, fun tr => ?_, ?_, ?_⟩
  · simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨st, hst, tr, htr, rfl⟩
      exact ⟨(hF st).1 hst, ((hR st hst).1 tr).1 htr⟩
    · intro htr
      rcases tr with _ | ⟨st, tr⟩
      · exact absurd htr.1 hm
      · have hst := (hF st).2 htr.1
        exact ⟨st, hst, tr, ((hR st hst).1 tr).2 htr.2, rfl⟩
  · rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun st hst => ?_
      rw [Finset.sum_image (by intro x _ y _ e; simpa using e), ← (hR st hst).2.1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun tr _ => by simp [wts]
    · intro st _ st' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro tr h1 h2
      rw [Finset.mem_image] at h1 h2
      obtain ⟨t1, -, rfl⟩ := h1
      obtain ⟨t2, -, e⟩ := h2
      exact hne (List.cons.inj e).1.symm
  · intro tr htr
    simp only [Finset.mem_biUnion, Finset.mem_image] at htr
    obtain ⟨st, hst, tr, htr, rfl⟩ := htr
    have := (hR st hst).2.2 tr htr
    rw [List.length_cons]
    push_cast
    omega

/-- No step. -/
theorem SumTo.none {σ : State (M := M) (K := K)} (hm : σ.mode ≠ P.mh) (h : ∀ st : P.Step, ¬ Fire σ st) (B : ℤ) :
    SumTo P σ 0 B := by
  have h1 := SumTo.fin hm (∅ : Finset P.Step) (by simpa using h) (fun _ => 0) 0 (by simp)
  refine ⟨∅, ?_, by simp, by simp⟩
  obtain ⟨R, hR, -, -⟩ := h1
  intro tr
  simp only [Finset.notMem_empty, false_iff]
  intro htr
  rcases tr with _ | ⟨st, tr⟩
  · exact hm htr.1
  · exact h st htr.1

/-- Exactly one step. -/
theorem SumTo.one {σ : State (M := M) (K := K)} (hm : σ.mode ≠ P.mh) (st : P.Step) (hst : ∀ st', Fire σ st' ↔ st' = st)
    {S : A} {B : ℤ} (h : SumTo P (nxt σ st) S B) : SumTo P σ (P.wt st.1 * S) (B + 1) := by
  have h1 := SumTo.fin hm {st} (fun st' => by rw [Finset.mem_singleton, hst]) (fun _ => S) B (by
    intro st' hst'
    rw [Finset.mem_singleton] at hst'
    subst hst'
    exact h)
  simpa using h1

/-- Exactly two steps. -/
theorem SumTo.two {σ : State (M := M) (K := K)} (hm : σ.mode ≠ P.mh) (st st₁ : P.Step) (hne : st ≠ st₁)
    (hst : ∀ st', Fire σ st' ↔ st' = st ∨ st' = st₁) {S S₁ : A} {B : ℤ} (h : SumTo P (nxt σ st) S B)
    (h₁ : SumTo P (nxt σ st₁) S₁ B) : SumTo P σ (P.wt st.1 * S + P.wt st₁.1 * S₁) (B + 1) := by
  classical
  have h1 := SumTo.fin hm {st, st₁} (fun st' => by rw [Finset.mem_insert, Finset.mem_singleton, hst])
    (fun st' => if st' = st then S else S₁) B (by
    intro st' hst'
    rw [Finset.mem_insert, Finset.mem_singleton] at hst'
    rcases hst' with rfl | rfl
    · rw [if_pos rfl]; exact h
    · rw [if_neg hne.symm]; exact h₁)
  rw [Finset.sum_pair hne, if_pos rfl, if_neg hne.symm] at h1
  exact h1

end Mach

end Nc.Uni
