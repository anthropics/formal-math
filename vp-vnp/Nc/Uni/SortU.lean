/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.Alpha

/-!
# The sorting loop
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

variable {A : Type*} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K]

/-- The list tape, read. -/
abbrev lsT : Zc K := .tp .ls true
/-- The list tape, written. -/
abbrev lsF : Zc K := .tp .ls false

/-- A record on the list: flag, letters and mark, end. -/
def rw' (f : Bool) (w : List (Option (Bl K))) : List (Sy M K) := .flag f :: (w.map ol ++ [.dot])

/-- Letters other than the end of a block. -/
abbrev NB (M K : Type) := {γ : Sy M K // γ ≠ .bar}

/-- Rounds of the distribution: flag, first letter, the others. -/
abbrev Dr (K : Type) := Bool × Bl K × List (Option (Bl K))

/-- Emissions of a round of the distribution. -/
def emDr (d : Dr K) : Zc K → List (Sy M K) := fun z =>
  on {lsT} (rw' d.1 (some d.2.1 :: d.2.2)) z ++ on {.tp (.bk d.2.1) false} (rw' d.1 (d.2.2 ++ [some d.2.1])) z

theorem runs_dr : Runs (Fintype.card (Bl K) * (10 + 3 + (Fintype.card (Option (Bl K)) * 5 + 1) + 7))
    (emDr : Dr K → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h := Runs.sum (F := A) fun b : Bl K =>
    (((Runs.letter (F := A) (Z := Zc K) {lsT, .tp (.bk b) false} (fun f : Bool => (Sy.flag f : Sy M K)) (fun _ => 1)).mul
    (Runs.word (F := A) {lsT} [(be b : Sy M K)])).mul
    (Runs.wordstar (F := A) {lsT, .tp (.bk b) false} ⟨lsT, by simp⟩ (ol : Option (Bl K) → Sy M K))).mul
    (Runs.const (F := A) fun z : Zc K => on {lsT} [(Sy.dot : Sy M K)] z ++ on {.tp (.bk b) false} [be b, Sy.dot] z)
  refine (h.congr ⟨fun d => ⟨d.2.1, (((d.1, ()), d.2.2), ())⟩, fun y => (y.2.1.1.1, y.1, y.2.1.2), fun d => rfl,
    fun y => rfl⟩ (fun d z => ?_) fun d => by simp).mono ?_
  · obtain ⟨f, b, w⟩ := d
    simp only [Equiv.coe_fn_mk, emDr, rw']
    by_cases h1 : z = lsT
    · subst h1
      simp [on, ol]
    · by_cases h2 : z = .tp (.bk b) false
      · subst h2
        simp [on, ol]
      · simp [on, h1, h2]
  · have hc : ∀ b : Bl K, ({lsT, .tp (.bk b) false} : Finset (Zc K)).card = 2 := fun b => Finset.card_pair (by simp)
    simp only [hc, List.length_append, Finset.sum_add_distrib, sum_on]
    simp
    ring_nf
    omega

/-- The channels where a pass of the distribution ends a block. -/
def barSet : Finset (Zc K) := insert lsT (univ.image fun b : Bl K => (.tp (.bk b) false : Zc K))

/-- Runs of a pass. -/
abbrev Ps (M K : Type) := List (Dr K) × (Bl K → List (NB M K))

/-- The letters of records, in some order. -/
noncomputable def bsl (K : Type) [Fintype K] [DecidableEq K] : List (Bl K) := List.ofFn (Fintype.equivFin (Bl K)).symm

theorem mem_bsl (b : Bl K) : b ∈ bsl K := by
  rw [bsl, List.mem_ofFn]
  exact ⟨Fintype.equivFin (Bl K) b, by simp⟩

theorem bsl_nodup : (bsl K).Nodup := by
  rw [bsl, List.nodup_ofFn]
  exact Equiv.injective _

/-- Emissions of the collection. -/
noncomputable def emCo (m : Bl K → List (NB M K)) : Zc K → List (Sy M K) := fun z =>
  (List.ofFn fun i => on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
      ((m ((Fintype.equivFin (Bl K)).symm i)).map Subtype.val) z ++
    on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [Sy.bar] z).flatten ++ on {lsF} [Sy.bar] z

theorem runs_co : Runs (Fintype.card (Bl K) * (Fintype.card (Sy M K) * 5 + 1 + 3) + 1 + 3)
    (emCo : (Bl K → List (NB M K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h0 : ∀ i : Fin (Fintype.card (Bl K)), Runs (Fintype.card (Sy M K) * 5 + 1 + 3)
      (fun (w : List (NB M K)) (z : Zc K) => on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
        (w.map Subtype.val) z ++ on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [Sy.bar] z)
      (fun _ => (1 : A)) := by
    intro i
    have h1 := (Runs.wordstar (F := A) (Z := Zc K) {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
      ⟨lsF, by simp⟩ (Subtype.val : NB M K → Sy M K)).mul
      (Runs.word (F := A) (Z := Zc K) {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [(Sy.bar : Sy M K)])
    refine (h1.congr ⟨fun w => (w, ()), Prod.fst, fun w => rfl, fun y => rfl⟩ (fun w z => rfl) fun w => by simp).mono ?_
    have hc : ({.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF} : Finset (Zc K)).card = 2 :=
      Finset.card_pair (by simp)
    have hs : Fintype.card (NB M K) ≤ Fintype.card (Sy M K) := Fintype.card_subtype_le _
    rw [hc, Finset.card_singleton, List.length_singleton]
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_right 5 hs) 1) (by norm_num)
  have h := (Runs.pi h0).mul (Runs.word (F := A) (Z := Zc K) {lsF} [(Sy.bar : Sy M K)])
  refine (h.congr ⟨fun m => ((fun i => m ((Fintype.equivFin (Bl K)).symm i)), ()),
    fun y b => y.1 (Fintype.equivFin (Bl K) b), fun m => by simp, fun y => by simp⟩ (fun m z => rfl) fun m => ?_).mono ?_
  · simp
  · simp

/-- Emissions of a pass. -/
noncomputable def emPs (p : Ps M K) : Zc K → List (Sy M K) := fun z =>
  (p.1.flatMap fun d => emDr d z) ++ (on barSet [Sy.bar] z ++ emCo p.2 z)

/-- Dimension of a pass. -/
def dimPs (m k : ℕ) : ℕ := (k * (10 + 3 + ((k + 1) * 5 + 1) + 7) + 1) + ((2 * (k + 1) + 1) + (k * (m * 5 + 1 + 3) + 1 + 3))

theorem emDr_ne (d : Dr K) : ∃ z, (emDr d : Zc K → List (Sy M K)) z ≠ [] := ⟨lsT, by simp [emDr, on, rw']⟩

theorem card_barSet : (barSet : Finset (Zc K)).card ≤ Fintype.card (Bl K) + 1 := by
  unfold barSet
  refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
  exact Finset.card_image_le

theorem runs_ps : Runs (dimPs (Fintype.card (Sy M K)) (Fintype.card (Bl K)))
    (emPs : Ps M K → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h := ((runs_dr (A := A) (M := M) (K := K)).kstar fun d => emDr_ne d).mul
    ((Runs.word (F := A) (Z := Zc K) barSet [(Sy.bar : Sy M K)]).mul (runs_co (A := A) (M := M) (K := K)))
  refine (h.congr ⟨fun p => (p.1, (), p.2), fun y => (y.1, y.2.2), fun p => rfl, fun y => rfl⟩ (fun p z => rfl)
    fun p => ?_).mono ?_
  · simp
  · have := card_barSet (K := K)
    unfold dimPs
    rw [Fintype.card_option]
    simp only [List.length_singleton, mul_one]
    omega

/-- Emissions of the last reading: the marks are in front and are dropped. -/
def emFi (l : List (Bool × List (Bl K))) : Zc K → List (Sy M K) := fun z =>
  (l.flatMap fun d => on {lsT} (rw' d.1 (none :: d.2.map some)) z ++
    on {.tp (.cm false) false, .tp (.cm true) false} (rw' d.1 (d.2.map some)) z) ++ on {lsT} [Sy.bar] z

theorem runs_fi : Runs (14 + 3 + (Fintype.card (Bl K) * 7 + 1) + 7 + 1 + 3)
    (emFi : List (Bool × List (Bl K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have hc : ({lsT, .tp (.cm false) false, .tp (.cm true) false} : Finset (Zc K)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by simp)]
  have h1 := (((Runs.letter (F := A) (Z := Zc K) {lsT, .tp (.cm false) false, .tp (.cm true) false}
      (fun f : Bool => (Sy.flag f : Sy M K)) (fun _ => 1)).mul
    (Runs.word (F := A) {lsT} [(Sy.mark : Sy M K)])).mul
    (Runs.wordstar (F := A) {lsT, .tp (.cm false) false, .tp (.cm true) false} ⟨lsT, by simp⟩ (be : Bl K → Sy M K))).mul
    (Runs.word (F := A) {lsT, .tp (.cm false) false, .tp (.cm true) false} [(Sy.dot : Sy M K)])
  have h2 := h1.congr (em' := fun (d : Bool × List (Bl K)) z => on {lsT} (rw' d.1 (none :: d.2.map some)) z ++
    on {.tp (.cm false) false, .tp (.cm true) false} (rw' d.1 (d.2.map some)) z) (wt' := fun _ => 1)
    ⟨fun d => (((d.1, ()), d.2), ()), fun y => (y.1.1.1, y.1.2), fun d => rfl, fun y => rfl⟩ (fun d z => by
      obtain ⟨f, w⟩ := d
      have hw : (w.map some).map (ol : Option (Bl K) → Sy M K) = w.map be := by
        rw [List.map_map]; rfl
      simp only [Equiv.coe_fn_mk, rw', List.map_cons, hw]
      by_cases h1 : z = lsT
      · subst h1
        simp [on, ol]
      · by_cases h2 : z = .tp (.cm false) false
        · subst h2
          simp [on]
        · by_cases h3 : z = .tp (.cm true) false
          · subst h3
            simp [on]
          · simp [on, h1, h2, h3]) (fun d => by simp)
  have h3 := (h2.kstar fun d => ⟨lsT, by simp [on, rw']⟩).mul (Runs.word (F := A) (Z := Zc K) {lsT} [(Sy.bar : Sy M K)])
  refine (h3.congr ⟨fun l => (l, ()), Prod.fst, fun l => rfl, fun y => rfl⟩ (fun l z => rfl) fun l => by simp).mono ?_
  rw [hc]
  simp

end Nc.Uni
