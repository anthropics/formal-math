/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.Prog
import Nc.Uni.Bin

/-!
# What the program writes on the tapes; matched runs
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] (P : Mach A M K)

/-- Words of bits, one after the other. -/
def bws (ws : List (List Bool)) : List (Sy M K) := ws.flatMap bw

theorem bws_cons (w : List Bool) (ws : List (List Bool)) : (bws (w :: ws) : List (Sy M K)) = bw w ++ bws ws := rfl

theorem bw_inj {w w' : List Bool} {u v : List (Sy M K)} (h : bw w ++ u = bw w' ++ v) : w = w' ∧ u = v := by
  simp only [bw, List.append_assoc, List.singleton_append] at h
  have hs : ∀ w : List Bool, (Sy.semi : Sy M K) ∉ w.map .bit := by
    intro w hw
    rw [List.mem_map] at hw
    obtain ⟨b, -, hb⟩ := hw
    exact absurd hb (by simp)
  obtain ⟨h1, h2⟩ := cut_inj (hs w) (hs w') h
  exact ⟨List.map_injective_iff.2 (fun a b e => by simpa using e) h1, h2⟩

theorem bws_inj : Function.Injective (bws : List (List Bool) → List (Sy M K)) := by
  refine flatMap_inj (fun w => by simp [bw]) ?_
  intro w w' u v h
  exact (bw_inj h).1

/-- The contents of the records, with the mark. -/
def oc (c : List (Bl K)) : List (Option (Bl K)) := c.map some ++ [none]

theorem encW_append (l l' : List (Bool × List (Option (Bl K)))) : (encW (l ++ l') : List (Sy M K)) = encW l ++ encW l' := by
  simp [encW]

theorem encW_cons (r : Bool × List (Option (Bl K))) (l : List (Bool × List (Option (Bl K)))) :
    (encW (r :: l) : List (Sy M K)) = rw' r.1 r.2 ++ encW l := rfl

variable {P}

/-- The records that are defined. -/
def dfs (x : XP P) : List (List (Bl K)) :=
  cont P.kN (List.replicate (x.1.length + 1) fun _ => false) :: x.2.2.1.map fun s => cont (P.ak s.1) (alc P s.1 s.2)

/-- The records that are looked up. -/
def lks (x : XP P) : List (List (Bl K)) := x.2.2.1.map fun s => cont (P.lk s.1) (ldc P s.1 s.2)

theorem emX_rg_true (x : XP P) (i : Fin 5) :
    emX P x (tp (.rg i) true) = bws (x.2.2.1.map (fun s => cw s.2 (rv i)) ++ [x.2.2.2.1.1.map fun v => v i]) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp (.rg i) true) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp (.rg i) true) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp (.rg i) true) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, rgw, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_rg_false (x : XP P) (i : Fin 5) :
    emX P x (tp (.rg i) false) = bws (i0 x.1 :: x.2.2.1.map fun s => cw s.2 (P.dr s.1 i)) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp (.rg i) false) : List (Sy M K)) = bw (i0 l) := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp (.rg i) false) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp (.rg i) false) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, rgw, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_md_true (x : XP P) : emX P x (tp .md true) = (x.2.2.1.map (fun s => P.src s.1) ++ [P.mh]).map .md := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .md true) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .md true) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .md true) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, flatMap_single', List.map_map, Function.comp_def]

theorem emX_md_false (x : XP P) : emX P x (tp .md false) = (P.m0 :: x.2.2.1.map fun s => P.dst s.1).map .md := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .md false) : List (Sy M K)) = [.md P.m0] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .md false) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .md false) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, flatMap_single', List.map_map, Function.comp_def]

theorem emX_cp_true (x : XP P) : emX P x (tp .cp true) = bws (x.2.1.map cn ++ [true :: x.2.2.2.1.2]) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .cp true) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .cp true) : List (Sy M K)) = bw (cn r) := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .cp true) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_cp_false (x : XP P) : emX P x (tp .cp false) = bws (i1 x.1 :: x.2.1.map cn1) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .cp false) : List (Sy M K)) = bw (i1 l) := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .cp false) : List (Sy M K)) = bw (cn1 r) := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .cp false) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_fr_true (x : XP P) : emX P x (tp .fr true) = bws (x.2.2.1.map fun s => cw s.2 8) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .fr true) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .fr true) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .fr true) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_fr_false (x : XP P) : emX P x (tp .fr false) = bws (x.2.1.map cn) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .fr false) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .fr false) : List (Sy M K)) = bw (cn r) := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .fr false) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_lk_true (x : XP P) : emX P x (tp .lk true) = x.2.2.2.2.1 := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .lk true) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .lk true) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .lk true) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, flatMap_nil']

theorem emX_lk_false (x : XP P) : emX P x (tp .lk false) = encW ((lks x).map fun c => (true, oc c)) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .lk false) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .lk false) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .lk false) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, encW, lks, List.flatMap_map, oc, rec']

theorem emX_ls_true (x : XP P) : emX P x lsT = emU x.2.2.2.2.2 lsT := by
  have h1 : ∀ l, (emIn P.m0 P.kN l lsT : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r lsT : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  unfold emX
  rw [h1]
  simp [h2, emSt, emEd, emAp, on, flatMap_nil']

theorem emX_ls_false (x : XP P) :
    emX P x lsF = encW ((dfs x).map fun c => (false, oc c)) ++ (x.2.2.2.2.1 ++ .bar :: emU x.2.2.2.2.2 lsF) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l lsF : List (Sy M K)) =
      rec' false P.kN (List.replicate (l.length + 1) fun _ => false) := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r lsF : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  unfold emX
  rw [h1]
  simp [h2, emSt, emEd, emAp, on, encW, dfs, List.flatMap_map, oc, rec']

theorem emX_bk (x : XP P) (b : Bl K) (s : Bool) : emX P x (tp (.bk b) s) = emU x.2.2.2.2.2 (tp (.bk b) s) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp (.bk b) s) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp (.bk b) s) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  unfold emX
  rw [h1]
  simp [h2, emSt, emEd, emAp, on, flatMap_nil']

theorem emX_cm (x : XP P) (k s : Bool) : emX P x (tp (.cm k) s) = emU x.2.2.2.2.2 (tp (.cm k) s) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp (.cm k) s) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp (.cm k) s) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  unfold emX
  rw [h1]
  simp [h2, emSt, emEd, emAp, on, flatMap_nil']

theorem emX_inp (x : XP P) : emX P x (.inp ()) = (x.2.2.1.flatMap fun s => (P.rd s.1).toList).map .bit := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (.inp ()) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (.inp ()) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (.inp ()) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, List.map_flatMap]

/-- The conditions for a matched run. -/
structure MX (x : XP P) (bits : List Bool) : Prop where
  rg : ∀ i, i0 x.1 :: x.2.2.1.map (fun s => cw s.2 (P.dr s.1 i)) =
    x.2.2.1.map (fun s => cw s.2 (rv i)) ++ [x.2.2.2.1.1.map fun v => v i]
  md : P.m0 :: x.2.2.1.map (fun s => P.dst s.1) = x.2.2.1.map (fun s => P.src s.1) ++ [P.mh]
  cp : i1 x.1 :: x.2.1.map cn1 = x.2.1.map cn ++ [true :: x.2.2.2.1.2]
  fr : x.2.1.map cn = x.2.2.1.map fun s => cw s.2 8
  lk : x.2.2.2.2.1 = encW ((lks x).map fun c => (true, oc c))
  ls : IMU x.2.2.2.2.2 (encW ((dfs x).map (fun c => (false, oc c)) ++ (lks x).map fun c => (true, oc c)))
  inp : (x.2.2.1.flatMap fun s => (P.rd s.1).toList) = bits

theorem mt_X (x : XP P) (bits : List Bool) :
    Mt (emX P) (fun _ => bits.map .bit) x ↔ MX x bits := by
  have hmd : Function.Injective (Sy.md : M → Sy M K) := fun a b e => by simpa using e
  have hbit : Function.Injective (Sy.bit : Bool → Sy M K) := fun a b e => by simpa using e
  constructor
  · rintro ⟨h1, h2⟩
    have hlk : x.2.2.2.2.1 = encW ((lks x).map fun c => (true, oc c)) := by
      have := h1 .lk
      rw [emX_lk_false, emX_lk_true] at this
      exact this.symm
    refine ⟨fun i => ?_, ?_, ?_, ?_, hlk, ⟨?_, fun b => ?_, fun k => ?_⟩, ?_⟩
    · have := h1 (.rg i)
      rw [emX_rg_false, emX_rg_true] at this
      exact bws_inj this
    · have := h1 .md
      rw [emX_md_false, emX_md_true] at this
      exact List.map_injective_iff.2 hmd this
    · have := h1 .cp
      rw [emX_cp_false, emX_cp_true] at this
      exact bws_inj this
    · have := h1 .fr
      rw [emX_fr_false, emX_fr_true] at this
      exact bws_inj this
    · have := h1 .ls
      rw [emX_ls_false, emX_ls_true, hlk, ← List.append_assoc, ← encW_append] at this
      exact this
    · have := h1 (.bk b)
      rw [emX_bk, emX_bk] at this
      exact this
    · have := h1 (.cm k)
      rw [emX_cm, emX_cm] at this
      exact this
    · have := h2 ()
      rw [emX_inp] at this
      exact List.map_injective_iff.2 hbit this
  · rintro ⟨h1, h2, h3, h4, h5, ⟨h6, h7, h8⟩, h9⟩
    refine ⟨?_, ?_⟩
    · intro s
      cases s with
      | rg i => rw [emX_rg_false, emX_rg_true, h1]
      | md => rw [emX_md_false, emX_md_true, h2]
      | cp => rw [emX_cp_false, emX_cp_true, h3]
      | fr => rw [emX_fr_false, emX_fr_true, h4]
      | lk => rw [emX_lk_false, emX_lk_true, h5]
      | ls => rw [emX_ls_false, emX_ls_true, h5, ← List.append_assoc, ← encW_append, h6]
      | bk b => rw [emX_bk, emX_bk, h7]
      | cm k => rw [emX_cm, emX_cm, h8]
    · rintro ⟨⟩
      rw [emX_inp, h9]

end Nc.Uni
