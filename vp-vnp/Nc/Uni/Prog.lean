/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.SpecU2
import Nc.Uni.PM

/-!
# A tape program that simulates a pointer machine
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K]

/-- A word of bits, ended. -/
def bw (w : List Bool) : List (Sy M K) := w.map .bit ++ [.semi]

/-- The content of a record: kind and columns. -/
def cont (κ : K) (cs : List (Fin 4 → Bool)) : List (Bl K) := .inl κ :: cs.map .inr

/-- A record, as it is written. -/
def rec' (f : Bool) (κ : K) (cs : List (Fin 4 → Bool)) : List (Sy M K) := rw' f ((cont κ cs).map some ++ [none])

theorem rec'_eq (f : Bool) (κ : K) (cs : List (Fin 4 → Bool)) :
    (rec' f κ cs : List (Sy M K)) = .flag f :: .kd κ :: (cs.map .col ++ [.mark, .dot]) := by
  simp [rec', rw', cont, ol, be, List.map_map, Function.comp_def]

/-- A side of a tape. -/
abbrev tp (s : Tp K) (b : Bool) : Zc K := .tp s b

/-- The sides of all register tapes. -/
def rgs (b : Bool) : Finset (Zc K) := univ.image fun i => tp (.rg i) b

theorem mem_rgs (b : Bool) (z : Zc K) : z ∈ rgs b ↔ ∃ i, z = tp (.rg i) b := by
  simp [rgs, eq_comm]

theorem card_rgs (b : Bool) : (rgs b : Finset (Zc K)).card = 5 := by
  rw [rgs, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i j h
  simpa using h

/-- Loops with a fixed body. -/
theorem runs_rep (w : Zc K → List (Sy M K)) (hw : ∃ z, w z ≠ []) :
    Runs (2 * ∑ z, (w z).length + 1 + 1) (fun (l : List Unit) z => l.flatMap fun _ => w z) (fun _ => (1 : A)) := by
  have h := (Runs.const (F := A) w).kstar fun _ => hw
  exact h.congr (Equiv.refl _) (fun l z => rfl) fun l => by simp

/-- The three words of a round of the counter. -/
def cn (r : List Bool × List Unit) : List Bool := r.1 ++ false :: List.replicate r.2.length true

/-- The next number. -/
def cn1 (r : List Bool × List Unit) : List Bool := r.1 ++ true :: List.replicate r.2.length false

/-- Emissions of a round of the counter. -/
def emCt (r : List Bool × List Unit) : Zc K → List (Sy M K) := fun z =>
  on {tp .cp true, tp .fr false} (bw (cn r)) z ++ on {tp .cp false} (bw (cn1 r)) z

theorem flatMap_unit {γ : Type*} (l : List Unit) (a : γ) : (l.flatMap fun _ => [a]) = List.replicate l.length a := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, ih]; rfl

theorem runs_ct : Runs 60 (emCt : List Bool × List Unit → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have hc : ({tp .cp true, tp .fr false, tp .cp false} : Finset (Zc K)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by simp)]
  have hc2 : ({tp .cp true, tp .fr false} : Finset (Zc K)).card = 2 := Finset.card_pair (by simp)
  have h1 := Runs.wordstar (F := A) (Z := Zc K) {tp .cp true, tp .fr false, tp .cp false} ⟨tp .cp true, by simp⟩
    (fun b : Bool => (Sy.bit b : Sy M K))
  have h2 := Runs.const (F := A) fun z : Zc K => on {tp .cp true, tp .fr false} [(Sy.bit false : Sy M K)] z ++
    on {tp .cp false} [Sy.bit true] z
  have h3 := runs_rep (A := A) (fun z : Zc K => on {tp .cp true, tp .fr false} [(Sy.bit true : Sy M K)] z ++
    on {tp .cp false} [Sy.bit false] z) ⟨tp .cp false, by simp [on]⟩
  have h4 := Runs.word (F := A) (Z := Zc K) {tp .cp true, tp .fr false, tp .cp false} [(Sy.semi : Sy M K)]
  refine ((((h1.mul h2).mul h3).mul h4).congr ⟨fun r => (((r.1, ()), r.2), ()), fun y => (y.1.1.1, y.1.2), fun r => rfl,
    fun y => rfl⟩ (fun r z => ?_) fun r => ?_).mono ?_
  · obtain ⟨w, l⟩ := r
    simp only [Equiv.coe_fn_mk, emCt, cn, cn1, bw]
    by_cases hz1 : z = tp .cp true
    · subst hz1
      simp [on, flatMap_unit]
    · by_cases hz2 : z = tp .fr false
      · subst hz2
        simp [on, flatMap_unit]
      · by_cases hz3 : z = tp .cp false
        · subst hz3
          simp [on, flatMap_unit]
        · simp [on, hz1, hz2, hz3]
  · simp
  · simp only [List.length_append, Finset.sum_add_distrib, sum_on, hc, hc2]
    simp

/-- The first words: registers 0, counter 1. -/
def i0 (l : List Unit) : List Bool := List.replicate (l.length + 1) false

/-- The first address. -/
def i1 (l : List Unit) : List Bool := List.replicate l.length false ++ [true]

/-- Emissions at the start. -/
def emIn (m0 : M) (kN : K) (l : List Unit) : Zc K → List (Sy M K) := fun z =>
  on (rgs false) (bw (i0 l)) z ++ on {tp .cp false} (bw (i1 l)) z ++
    on {lsF} (rec' false kN (List.replicate (l.length + 1) fun _ => false)) z ++ on {tp .md false} [.md m0] z

theorem runs_in (m0 : M) (kN : K) : Runs 80 (emIn m0 kN : List Unit → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h1 := Runs.const (F := A) fun z : Zc K => on {lsF} [(Sy.flag false : Sy M K), .kd kN] z ++ on {tp .md false} [.md m0] z
  have h2 := runs_rep (A := A) (fun z : Zc K => on (insert (tp .cp false) (rgs false)) [(Sy.bit false : Sy M K)] z ++
    on {lsF} [.col fun _ => false] z) ⟨lsF, by simp [on, mem_rgs]⟩
  have h3 := Runs.const (F := A) fun z : Zc K => on (rgs false) [(Sy.bit false : Sy M K), .semi] z ++
    on {tp .cp false} [.bit true, .semi] z ++ on {lsF} [.col fun _ => false, .mark, .dot] z
  refine (((h1.mul h2).mul h3).congr ⟨fun l => (((), l), ()), fun y => y.1.2, fun l => rfl, fun y => rfl⟩
    (fun l z => ?_) fun l => ?_).mono ?_
  · simp only [Equiv.coe_fn_mk, emIn, i0, i1, bw, rec'_eq]
    by_cases hz1 : z ∈ rgs false
    · obtain ⟨i, rfl⟩ := (mem_rgs _ _).1 hz1
      simp [on, mem_rgs, flatMap_unit, List.replicate_succ']
    · by_cases hz2 : z = tp .cp false
      · subst hz2
        simp [on, mem_rgs, flatMap_unit]
      · by_cases hz3 : z = lsF
        · subst hz3
          simp [on, mem_rgs, flatMap_unit, List.replicate_succ']
        · simp [on, hz1, hz2, hz3]
  · simp
  · have hc : (insert (tp .cp false) (rgs false) : Finset (Zc K)).card = 6 := by
      rw [Finset.card_insert_of_notMem (by simp [mem_rgs]), card_rgs]
    simp only [List.length_append, Finset.sum_add_distrib, sum_on, hc, card_rgs]
    simp

section Steps

variable (P : Mach A M K)

/-- A column of the variables of all bits. -/
def cw (w : List (Fin 9 → Bool)) (i : Fin 9) : List Bool := w.map fun v => v i

/-- The columns of the record that is loaded. -/
def ldc (r : P.Rl) (w : List (Fin 9 → Bool)) : List (Fin 4 → Bool) := w.map fun v => ![v (rv (P.la r)), v 5, v 6, v 7]

/-- The columns of the record that is allocated. -/
def alc (r : P.Rl) (w : List (Fin 9 → Bool)) : List (Fin 4 → Bool) :=
  w.map fun v => ![v 8, v (P.af r 0), v (P.af r 1), v (P.af r 2)]

/-- What a step writes on a register tape. -/
def rgw (s : Bool) (r : P.Rl) (w : List (Fin 9 → Bool)) (i : Fin 5) : List Bool :=
  if s then cw w (rv i) else cw w (P.dr r i)

/-- Emissions of a step. -/
def emSt (x : P.Rl × List (Fin 9 → Bool)) : Zc K → List (Sy M K)
  | .tp (.rg i) s => bw (rgw P s x.1 x.2 i)
  | .tp .md s => [.md (if s then P.src x.1 else P.dst x.1)]
  | .tp .cp _ => []
  | .tp .fr s => if s then bw (cw x.2 8) else []
  | .tp .lk s => if s then [] else rec' true (P.lk x.1) (ldc P x.1 x.2)
  | .tp .ls s => if s then [] else rec' false (P.ak x.1) (alc P x.1 x.2)
  | .tp (.bk _) _ => []
  | .tp (.cm _) _ => []
  | .inp _ => (P.rd x.1).toList.map .bit

/-- Before the columns. -/
def st0 (r : P.Rl) : Zc K → List (Sy M K)
  | .tp .md s => [.md (if s then P.src r else P.dst r)]
  | .tp .lk s => if s then [] else [.flag true, .kd (P.lk r)]
  | .tp .ls s => if s then [] else [.flag false, .kd (P.ak r)]
  | .inp _ => (P.rd r).toList.map .bit
  | _ => []

/-- A column. -/
def st1 (r : P.Rl) (v : Fin 9 → Bool) : Zc K → List (Sy M K)
  | .tp (.rg i) s => [.bit (if s then v (rv i) else v (P.dr r i))]
  | .tp .fr s => if s then [.bit (v 8)] else []
  | .tp .lk s => if s then [] else [.col ![v (rv (P.la r)), v 5, v 6, v 7]]
  | .tp .ls s => if s then [] else [.col ![v 8, v (P.af r 0), v (P.af r 1), v (P.af r 2)]]
  | _ => []

/-- After the columns. -/
def st2 : Zc K → List (Sy M K)
  | .tp (.rg _) _ => [.semi]
  | .tp .fr s => if s then [.semi] else []
  | .tp .lk s => if s then [] else [.mark, .dot]
  | .tp .ls s => if s then [] else [.mark, .dot]
  | _ => []

theorem flatMap_single' {α β : Type*} (l : List α) (f : α → β) : (l.flatMap fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih]; rfl

theorem flatMap_nil' {α β : Type*} (l : List α) : (l.flatMap fun _ => ([] : List β)) = [] := by simp

theorem emSt_eq (x : P.Rl × List (Fin 9 → Bool)) (z : Zc K) :
    st0 P x.1 z ++ (x.2.flatMap (fun v => st1 P x.1 v z) ++ st2 z) = emSt P x z := by
  obtain ⟨r, w⟩ := x
  match z with
  | .tp (.rg i) s =>
    simp only [st0, st1, st2, emSt, flatMap_single', rgw, bw, List.nil_append, cw]
    cases s <;> simp [List.map_map, Function.comp_def]
  | .tp .md s => simp [st0, st1, st2, emSt]
  | .tp .cp s => simp [st0, st1, st2, emSt]
  | .tp .fr s =>
    cases s
    · simp [st0, st1, st2, emSt]
    · simp [st0, st1, st2, emSt, flatMap_single', bw, cw, List.map_map, Function.comp_def]
  | .tp .lk s =>
    cases s
    · simp [st0, st1, st2, emSt, flatMap_single', rec'_eq, ldc, List.map_map, Function.comp_def]
    · simp [st0, st1, st2, emSt]
  | .tp .ls s =>
    cases s
    · simp [st0, st1, st2, emSt, flatMap_single', rec'_eq, alc, List.map_map, Function.comp_def]
    · simp [st0, st1, st2, emSt]
  | .tp (.bk b) s => simp [st0, st1, st2, emSt]
  | .tp (.cm k) s => simp [st0, st1, st2, emSt]
  | .inp j => simp [st0, st1, st2, emSt]

theorem st1_ne (r : P.Rl) (v : Fin 9 → Bool) : ∃ z, st1 P r v z ≠ [] := ⟨tp .fr true, by simp [st1]⟩

/-- Dimension of a step. -/
def dimSt : ℕ := ∑ r : P.Rl, (2 * ∑ z, (st0 P r z).length + 1 +
  ((∑ v : Fin 9 → Bool, (2 * ∑ z, (st1 P r v z).length + 1)) + 1 + (2 * ∑ z, ((st2 z : List (Sy M K))).length + 1)))

theorem runs_st : Runs (dimSt P) (emSt P : P.Rl × List (Fin 9 → Bool) → Zc K → List (Sy M K)) (fun x => P.wt x.1) := by
  have h := Runs.sum (F := A) fun r : P.Rl =>
    (Runs.pick (F := A) (fun _ : Unit => st0 P r) fun _ => P.wt r).mul
    (((Runs.pick (F := A) (fun v : Fin 9 → Bool => st1 P r v) fun _ => 1).kstar fun v => st1_ne P r v).mul
    (Runs.const (F := A) (st2 : Zc K → List (Sy M K))))
  refine (h.congr ⟨fun x => ⟨x.1, ((), x.2, ())⟩, fun y => (y.1, y.2.2.1), fun x => rfl, fun y => rfl⟩ (fun x z => ?_)
    fun x => ?_).mono ?_
  · simp only [Equiv.coe_fn_mk]
    exact emSt_eq P x z
  · simp
  · unfold dimSt
    refine Finset.sum_le_sum fun r _ => ?_
    simp

end Steps

/-- Emissions at the end. -/
def emEd (mh : M) (x : List (Fin 5 → Bool) × List Bool) : Zc K → List (Sy M K)
  | .tp (.rg i) s => if s then bw (x.1.map fun v => v i) else []
  | .tp .md s => if s then [.md mh] else []
  | .tp .cp s => if s then bw (true :: x.2) else []
  | _ => []

/-- Emissions at the end, the registers. -/
def ed1 (v : Fin 5 → Bool) : Zc K → List (Sy M K)
  | .tp (.rg i) s => if s then [.bit (v i)] else []
  | _ => []

theorem runs_ed (mh : M) : Runs ((∑ v : Fin 5 → Bool, (2 * ∑ z, (ed1 v z : List (Sy M K)).length + 1)) + 1 + 30)
    (emEd mh : List (Fin 5 → Bool) × List Bool → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h1 := (Runs.pick (F := A) (fun v : Fin 5 → Bool => (ed1 v : Zc K → List (Sy M K))) fun _ => 1).kstar
    fun v => ⟨tp (.rg 0) true, by simp [ed1]⟩
  have h2 := Runs.const (F := A) fun z : Zc K => on (rgs true) [(Sy.semi : Sy M K)] z ++
    on {tp .md true} [.md mh] z ++ on {tp .cp true} [.bit true] z
  have h3 := Runs.wordstar (F := A) (Z := Zc K) {tp .cp true} ⟨tp .cp true, by simp⟩ (fun b : Bool => (Sy.bit b : Sy M K))
  have h4 := Runs.word (F := A) (Z := Zc K) {tp .cp true} [(Sy.semi : Sy M K)]
  refine ((((h1.mul h2).mul h3).mul h4).congr ⟨fun x => (((x.1, ()), x.2), ()), fun y => (y.1.1.1, y.1.2), fun r => rfl,
    fun y => rfl⟩ (fun x z => ?_) fun x => ?_).mono ?_
  · obtain ⟨w, u⟩ := x
    simp only [Equiv.coe_fn_mk]
    match z with
    | .tp (.rg i) s =>
      cases s
      · simp [ed1, emEd, on, mem_rgs]
      · simp [ed1, emEd, on, mem_rgs, flatMap_single', bw, List.map_map, Function.comp_def]
    | .tp .md s => cases s <;> simp [ed1, emEd, on, mem_rgs]
    | .tp .cp s => cases s <;> simp [ed1, emEd, on, mem_rgs, bw]
    | .tp .fr s => simp [ed1, emEd, on, mem_rgs]
    | .tp .lk s => simp [ed1, emEd, on, mem_rgs]
    | .tp .ls s => simp [ed1, emEd, on, mem_rgs]
    | .tp (.bk b) s => simp [ed1, emEd, on, mem_rgs]
    | .tp (.cm k) s => simp [ed1, emEd, on, mem_rgs]
    | .inp j => simp [ed1, emEd, on, mem_rgs]
  · simp
  · simp only [List.length_append, Finset.sum_add_distrib, sum_on, card_rgs]
    simp

/-- Emissions of the phase that appends the lookups to the list. -/
def emAp (w : List (Sy M K)) : Zc K → List (Sy M K) := fun z => on {tp .lk true, lsF} w z ++ on {lsF} [.bar] z

theorem runs_ap : Runs (Fintype.card (Sy M K) * 5 + 1 + 3)
    (emAp : List (Sy M K) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have hc : ({tp .lk true, lsF} : Finset (Zc K)).card = 2 := Finset.card_pair (by simp)
  have h := (Runs.wordstar (F := A) (Z := Zc K) {tp .lk true, lsF} ⟨lsF, by simp⟩ (fun γ : Sy M K => γ)).mul
    (Runs.word (F := A) (Z := Zc K) {lsF} [(Sy.bar : Sy M K)])
  refine (h.congr ⟨fun w => (w, ()), Prod.fst, fun w => rfl, fun y => rfl⟩ (fun w z => ?_) fun w => ?_).mono ?_
  · simp [emAp]
  · simp
  · rw [hc]
    simp

/-- Runs of the program. -/
abbrev XP (P : Mach A M K) := List Unit × List (List Bool × List Unit) × List (P.Rl × List (Fin 9 → Bool)) ×
  (List (Fin 5 → Bool) × List Bool) × List (Sy M K) × XU M K

variable (P : Mach A M K)

/-- Emissions of the program. -/
noncomputable def emX (x : XP P) : Zc K → List (Sy M K) := fun z =>
  emIn P.m0 P.kN x.1 z ++ ((x.2.1.flatMap fun r => emCt r z) ++ ((x.2.2.1.flatMap fun s => emSt P s z) ++
    (emEd P.mh x.2.2.2.1 z ++ (emAp x.2.2.2.2.1 z ++ emU x.2.2.2.2.2 z))))

/-- Dimension of the program. -/
noncomputable def dimX : ℕ := 80 + ((60 + 1) + ((dimSt P + 1) +
  (((∑ v : Fin 5 → Bool, (2 * ∑ z, (ed1 v z : List (Sy M K)).length + 1)) + 1 + 30) +
    ((Fintype.card (Sy M K) * 5 + 1 + 3) + dimU (Fintype.card (Sy M K)) (Fintype.card (Bl K))))))

theorem emSt_ne (x : P.Rl × List (Fin 9 → Bool)) : ∃ z, emSt P x z ≠ [] := ⟨tp .md true, by simp [emSt]⟩

theorem runs_X : Runs (dimX P) (emX P : XP P → Zc K → List (Sy M K)) (fun x => (x.2.2.1.map fun s => P.wt s.1).prod) := by
  have h := (runs_in (A := A) (M := M) (K := K) P.m0 P.kN).mul
    (((runs_ct (A := A) (M := M) (K := K)).kstar fun r => ⟨tp .cp true, by simp [emCt, on, bw]⟩).mul
    (((runs_st P).kstar fun s => emSt_ne P s).mul ((runs_ed (A := A) (M := M) (K := K) P.mh).mul
    ((runs_ap (A := A) (M := M) (K := K)).mul (runs_U (A := A) (M := M) (K := K))))))
  refine h.congr (Equiv.refl _) (fun x z => rfl) fun x => ?_
  simp

end Nc.Uni
