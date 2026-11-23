/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Base

/-!
# The program of a base party: simulation and writing
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

section sim

variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool)

/-- The tapes, and the input. -/
noncomputable def tapes (S : Type) [Fintype S] [DecidableEq S] : List (Option S) := (univ : Finset (Option S)).toList

/-- The number of tapes. -/
noncomputable abbrev nT (S : Type) [Fintype S] [DecidableEq S] : ℕ := (tapes S).length

/-- The tape and the side of a channel. -/
def chOf : Ch S Unit → Option S × Bool
  | .tp s b => (some s, b)
  | .inp _ => (none, true)

/-- The tape and the side of an output list. -/
noncomputable def outOf (j : Fin (nT S + nT S)) : Option S × Bool :=
  Fin.addCases (motive := fun _ => Option S × Bool) (fun i => ((tapes S).get i, false)) (fun i => ((tapes S).get i, true)) j

/-- The code of a letter. -/
def code (a : Γ) : List Bool := List.ofFn (cb (some a))

/-- What a letter of a run pushes. -/
noncomputable def pushOf (z : Letter S Unit Γ) (j : Fin (nT S + nT S)) : List (List Bool) :=
  match z with
  | none => []
  | some (ch, a) => if chOf ch = outOf j then [code cb a] else []

/-- Numbers of states. -/
noncomputable def qn (Q : Type) [Fintype Q] : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q

variable (θ) in
/-- The automaton as a transducer. -/
noncomputable def simTab (q : Fin (Fintype.card Q)) (_ : Fin 0 → Bool) :
    List (Opt (Fintype.card Q) (nT S + nT S) (List Bool)) :=
  (univ : Finset (Letter S Unit Γ × Q)).toList.map fun z => ⟨we θ (mu z.1 ((qn Q).symm q) z.2), qn Q z.2, pushOf cb z.1⟩

/-- Output lists. -/
abbrev Outs (S : Type) [Fintype S] [DecidableEq S] := Fin (nT S + nT S) → List (List Bool)

/-- As a tree. -/
noncomputable def encO (o : Outs S) : Tree := listT (List.ofFn fun j => listT ((o j).map ofBits))

variable (θ) in
/-- The simulation of `T` steps. -/
noncomputable def simSem (T : ℕ) (q q' : Fin (Fintype.card Q)) : List (A × Outs S) :=
  bindL (runL θ (simTab θ mu cb) T (q, Fin.elim0, fun _ => [])) fun s => if s.1 = q' then [((1 : A), s.2.2)] else []

theorem num_injective : Function.Injective num := by
  intro a b h
  rw [← len_num a, h, len_num]

theorem size_num (k : ℕ) : (num k).size = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [num, size, ih]
    omega

/-- **Simulation.** -/
theorem ex_sim : ∃ F κ, ∀ (T : ℕ) (q q' : Fin (Fintype.card Q)),
    Does θ F (.cons (num T) (.cons (num q) (num q'))) ((simSem θ mu cb T q q').map (Prod.map id encO)) (κ * (T + 1)) := by
  obtain ⟨F, κ, hF⟩ := ex_run (θ := θ) ofBits (simTab θ mu cb)
  refine ⟨lett (.cons .id (lett (.cons (.hd .id) (.cons (.hd (.tl .id)) (.cons (.quote .nil)
    (.quote (listT (List.replicate (nT S + nT S) .nil)))))) F))
    (.ite (eqF (.hd (.tl .id)) (.tl (.tl (.hd .id)))) (.tl (.tl (.tl .id))) .fail),
    κ + 120 * Fintype.card Q + 300, fun T q q' => ?_⟩
  set x : Tree := .cons (num T) (.cons (num q) (num q')) with hx
  let s₀ : TSt (Fintype.card Q) 0 (nT S + nT S) (List Bool) := (q, Fin.elim0, fun _ => [])
  have hs₀ : encS ofBits s₀ = .cons (num q) (.cons .nil (listT (List.replicate (nT S + nT S) .nil))) := by
    have e2 : (List.ofFn fun _ : Fin (nT S + nT S) => listT (([] : List (List Bool)).map ofBits)) =
        List.replicate (nT S + nT S) .nil := by
      rw [List.ofFn_const]
      rfl
    simp only [encS, s₀, e2]
    rfl
  have h1 : Gives θ (.cons (.hd .id) (.cons (.hd (.tl .id)) (.cons (.quote .nil)
      (.quote (listT (List.replicate (nT S + nT S) .nil)))))) x (.cons (num T) (encS ofBits s₀)) 20 := by
    rw [hs₀]
    exact (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd (Gives.cons (Gives.quote _ _)
      (Gives.quote _ _)))).mono (by omega)
  have h2 := Does.of_gives h1 (hF T s₀)
  have h3 := Does.letkT (G := .ite (eqF (.hd (.tl .id)) (.tl (.tl (.hd .id)))) (.tl (.tl (.tl .id))) .fail)
    (f := fun s => (if s.1 = q' then [((1 : A), s.2.2)] else []).map (Prod.map id encO))
    (d := 120 * Fintype.card Q + 200) h2 (by
      rintro ⟨a, s⟩ -
      simp only
      have e1 := eqF_gives (θ := θ) (x := .cons x (encS ofBits s)) (a := .hd (.tl .id)) (b := .tl (.tl (.hd .id)))
        (u := num s.1) (v := num q') (Gives.id _).tl.hd (Gives.id _).hd.tl.tl
      have hs := s.1.2
      rw [size_num] at e1
      by_cases h : s.1 = q'
      · have e2 : bit (decide (num s.1 = num q')) ≠ .nil := by simp [h, bit, one]
        refine ((Does.ite_true (H := .fail) e1 e2 (Gives.id _).tl.tl.tl).replace ?_).mono (by omega)
        rw [if_pos h]
        rfl
      · have e2 : bit (decide (num s.1 = num q')) = .nil := by
          have : num s.1 ≠ num q' := fun h' => h (Fin.ext (num_injective h'))
          simp [this, bit]
        rw [e2] at e1
        refine ((Does.ite_false e1 (Does.fail _)).replace ?_).mono (by omega)
        rw [if_neg h]
        rfl)
  rw [bindL_map] at h3
  refine h3.mono ?_
  nlinarith

theorem length_of_mem_pushOf {z : Letter S Unit Γ} {j : Fin (nT S + nT S)} {a : List Bool} (ha : a ∈ pushOf cb z j) :
    a.length ≤ c := by
  cases z with
  | none => simp [pushOf] at ha
  | some z =>
    obtain ⟨ch, x⟩ := z
    simp only [pushOf] at ha
    split_ifs at ha
    · rw [List.mem_singleton] at ha
      subst ha
      simp [code]
    · simp at ha

/-- The lengths of what is simulated, and its letters. -/
theorem exists_simSem_length : ∃ κ, ∀ (T : ℕ) (q q' : Fin (Fintype.card Q)), ∀ r ∈ simSem θ mu cb T q q',
    (∀ j, (r.2 j).length ≤ κ * T) ∧ ∀ j, ∀ a ∈ r.2 j, a.length ≤ c := by
  obtain ⟨κ, hκ⟩ := exists_runL_length (θ := θ) (simTab θ mu cb)
  refine ⟨κ, fun T q q' r hr => ?_⟩
  obtain ⟨s, hs, z, hz, hrz⟩ := mem_bindL hr
  have h1 := hκ T (q, Fin.elim0, fun _ => []) (fun _ => rfl) s hs
  have h2 := mem_foldL_induct (f := fun (_ : Unit) s => stepL θ (simTab θ mu cb) s) (xs := List.replicate T ())
    (Inv := fun _ s => ∀ j, ∀ a ∈ s.2.2 j, a.length ≤ c) (m := 0) (s := (q, Fin.elim0, fun _ => []))
    (fun x _ s m hm q hq j a ha => by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hq
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 ho
      rcases List.mem_append.1 ha with ha | ha
      · exact length_of_mem_pushOf cb ha
      · exact hm j a ha) (fun j a ha => by simp at ha) s hs
  split_ifs at hz
  · rw [List.mem_singleton] at hz
    subst hz
    rw [hrz]
    exact ⟨h1, h2⟩
  · simp at hz

/-- The output lists of an input party. -/
noncomputable def inOuts (part : List (List Bool)) : Outs S := fun j => if outOf j = (none, false) then part else []

/-- The output lists of an input party, as a formula. -/
theorem ex_inOuts : ∃ F : Fm → Fm, ∃ κ, ∀ (p : Fm) (x : Tree) (part : List (List Bool)) (cp : ℕ),
    Gives θ p x (listT (part.map ofBits)) cp → Gives θ (F p) x (encO (inOuts (S := S) part)) (κ * (cp + 1)) := by
  refine ⟨fun p => mkList (List.ofFn fun j : Fin (nT S + nT S) => if outOf j = (none, false) then p else .quote .nil),
    2 * (nT S + nT S) + 2, fun p x part cp hp => ?_⟩
  have h1 := mkList_gives (θ := θ) (x := x) (m := nT S + nT S) (c := cp + 1)
    (f := fun j => if outOf j = (none, false) then p else .quote .nil)
    (o := fun j => listT ((inOuts (S := S) part j).map ofBits)) (fun j => by
      by_cases h : outOf j = ((none : Option S), false)
      · simp only [inOuts, h, if_true]
        exact hp.mono (by omega)
      · simp only [inOuts, h, if_false]
        exact (Gives.quote _ _).mono (by omega))
  refine h1.mono ?_
  nlinarith

section pack

/-- Items for what is written. -/
noncomputable def itemsR (flags : List (List ℕ)) (o : Outs S) : List Item :=
  List.ofFn fun i : Fin (nT S) => (flags.getD i.rev [], o (Fin.castAdd (nT S) i.rev))

/-- Items for what is read. -/
noncomputable def itemsC (m : ℕ) (o : Outs S) : List Item :=
  List.ofFn fun i : Fin (nT S) => (List.replicate m 2, o (Fin.natAdd (nT S) i.rev))

theorem itemsR_gives : ∃ G : Fm → Fm → Fm, ∃ κ, ∀ (a b : Fm) (x : Tree) (flags : List (List ℕ)) (o : Outs S) (ca cb : ℕ),
    Gives θ a x (listT (flags.map fun l => listT (l.map num))) ca → Gives θ b x (encO o) cb →
    Gives θ (G a b) x (listT ((itemsR flags o).map encI)) (κ * (ca + cb + 1)) := by
  refine ⟨fun a b => mkList (List.ofFn fun i : Fin (nT S) => .cons (nthF i.rev a) (nthF i.rev b)),
    nT S * (2 * nT S + 10) + 1, fun a b x flags o ca cb ha hb => ?_⟩
  have h1 := mkList_gives (θ := θ) (x := x) (m := nT S) (c := ca + cb + 2 * nT S + 5)
    (f := fun i : Fin (nT S) => .cons (nthF i.rev a) (nthF i.rev b))
    (o := fun i => encI (flags.getD i.rev [], o (Fin.castAdd (nT S) i.rev))) (fun i => by
      have h2 := nthF_gives (i.rev : ℕ) ha
      have e2 : (flags.map fun l => listT (l.map num)).getD (i.rev : ℕ) .nil = listT ((flags.getD i.rev []).map num) := by
        rw [show (.nil : Tree) = (fun l : List ℕ => listT (l.map num)) [] from rfl, List.getD_map]
      rw [e2] at h2
      have h3 := nthF_gives (i.rev : ℕ) hb
      have e3 : (List.ofFn fun j => listT ((o j).map ofBits)).getD (i.rev : ℕ) .nil =
          listT ((o (Fin.castAdd (nT S) i.rev)).map ofBits) := by
        have hlt : (i.rev : ℕ) < (List.ofFn fun j => listT ((o j).map ofBits)).length := by
          rw [List.length_ofFn]
          have := i.rev.2
          omega
        rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        rfl
      rw [e3] at h3
      have := i.rev.2
      exact (Gives.cons h2 h3).mono (by omega))
  rw [itemsR, List.map_ofFn]
  refine h1.mono ?_
  nlinarith [Nat.zero_le (nT S * nT S * (ca + cb)), Nat.zero_le (nT S * (ca + cb))]

theorem itemsC_gives : ∃ G : Fm → Fm → Fm, ∃ κ, ∀ (a b : Fm) (x : Tree) (m : ℕ) (o : Outs S) (ca cb : ℕ),
    Gives θ a x (listT ((List.replicate m 2).map num)) ca → Gives θ b x (encO o) cb →
    Gives θ (G a b) x (listT ((itemsC m o).map encI)) (κ * (ca + cb + 1)) := by
  refine ⟨fun a b => mkList (List.ofFn fun i : Fin (nT S) => .cons a (nthF (nT S + i.rev) b)),
    nT S * (2 * nT S + 10) + 1, fun a b x m o ca cb ha hb => ?_⟩
  have h1 := mkList_gives (θ := θ) (x := x) (m := nT S) (c := ca + cb + 2 * nT S + 5)
    (f := fun i : Fin (nT S) => .cons a (nthF (nT S + i.rev) b))
    (o := fun i => encI (List.replicate m 2, o (Fin.natAdd (nT S) i.rev))) (fun i => by
      have h3 := nthF_gives (nT S + i.rev : ℕ) hb
      have e3 : (List.ofFn fun j => listT ((o j).map ofBits)).getD (nT S + i.rev : ℕ) .nil =
          listT ((o (Fin.natAdd (nT S) i.rev)).map ofBits) := by
        have hlt : (nT S + i.rev : ℕ) < (List.ofFn fun j => listT ((o j).map ofBits)).length := by
          rw [List.length_ofFn]
          have := i.rev.2
          omega
        rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        rfl
      rw [e3] at h3
      have := i.rev.2
      exact (Gives.cons ha h3).mono (by omega))
  rw [itemsC, List.map_ofFn]
  refine h1.mono ?_
  nlinarith [Nat.zero_le (nT S * nT S * (ca + cb)), Nat.zero_le (nT S * (ca + cb))]

end pack

end sim

end Nc.Grp
