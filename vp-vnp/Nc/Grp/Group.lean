/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.StepRole
import Nc.Grp.GrpVal

/-!
# GROUP computes the value of a group
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T cap : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {dkey : Fin (K + K) × Fin U0 → List Bool} {tg : M.R → ℕ}

/-- A list of steps. -/
theorem sumL_steps {ι : Type} (l : List ι) (I : ι → List Ins) (s : ι → WStep A (Cell M U0 U1) (UW ub))
    (h : ∀ i ∈ l, StepOK (S := S) θ T mu cb kinds key (I i) (s i)) (J : List Ins) (G : (Cell M U0 U1 → UW ub) → A)
    (hJ : ∀ t σ, Rep ub key t σ → sumL (scriptSem (S := S) θ mu cb kinds T ub J t) (fun _ => 1) = G σ) (t : Tree)
    (σ : Cell M U0 U1 → UW ub) (hr : Rep ub key t σ) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub (l.flatMap I ++ J) t) (fun _ => 1) = WStep.exec (l.map s) G σ := by
  induction l generalizing t σ with
  | nil => exact hJ t σ hr
  | cons i l ih =>
    rw [List.flatMap_cons, List.append_assoc, sumL_script_append, List.map_cons, WStep.exec]
    exact h i List.mem_cons_self t σ _ _ hr fun t' σ' hr' => ih (fun i hi => h i (List.mem_cons_of_mem _ hi)) t' σ' hr'

/-- What is compared at a unit. -/
def EndOk (grp : Fin (K + K + A') → Gr) (g : Gr) (σ : Cell M U0 U1 → UW ub) (b : G.Uid (K + K) U0 M.N U1 → UW ub)
    (id : G.Uid (K + K) U0 M.N U1) : Prop :=
  (grp (G.hold0 M.np id) = g → grp (G.hold1 M.np id) = g →
      uwBits (σ (G.hold0 M.np id, id)) = uwBits (σ (G.hold1 M.np id, id))) ∧
    (grp (G.hold0 M.np id) = g → grp (G.hold1 M.np id) ≠ g → uwBits (σ (G.hold0 M.np id, id)) = uwBits (b id)) ∧
    (grp (G.hold0 M.np id) ≠ g → grp (G.hold1 M.np id) = g → uwBits (σ (G.hold1 M.np id, id)) = uwBits (b id))

open Classical in
/-- The last instructions compare. -/
theorem sumL_end (b : G.Uid (K + K) U0 M.N U1 → UW ub) (l : List (G.Uid (K + K) U0 M.N U1)) (t : Tree)
    (σ : Cell M U0 U1 → UW ub) (hr : Rep ub key t σ) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub (l.filterMap fun id =>
      if grp (G.hold0 M.np id) = g then
        if grp (G.hold1 M.np id) = g then some (.both (key (G.hold0 M.np id, id)) (key (G.hold1 M.np id, id)))
        else some (.one (key (G.hold0 M.np id, id)) (uwBits (b id)))
      else if grp (G.hold1 M.np id) = g then some (.one (key (G.hold1 M.np id, id)) (uwBits (b id)))
      else none) t) (fun _ => 1) =
    if ∀ id ∈ l, EndOk grp g σ b id then 1 else 0 := by
  have hof : ∀ v w : List Bool, ofBits v = ofBits w ↔ v = w := fun v w => ofBits_injective.eq_iff
  induction l with
  | nil => simp [sumL_script_nil]
  | cons id l ih =>
    have hcons : (∀ i ∈ id :: l, EndOk grp g σ b i) ↔ EndOk grp g σ b id ∧ ∀ i ∈ l, EndOk grp g σ b i :=
      List.forall_mem_cons
    by_cases h0 : grp (G.hold0 M.np id) = g
    · by_cases h1 : grp (G.hold1 M.np id) = g
      · rw [List.filterMap_cons_some (by rw [if_pos h0, if_pos h1]), sumL_script_cons, insSem]
        simp only [hr.2, hof]
        by_cases he : uwBits (σ (G.hold0 M.np id, id)) = uwBits (σ (G.hold1 M.np id, id))
        · rw [if_pos he, sumL_single, ih]
          refine if_congr ?_ rfl rfl
          rw [hcons]
          simp [EndOk, h0, h1, he]
        · rw [if_neg he, sumL_nil, if_neg fun h => he ((hcons.1 h).1.1 h0 h1)]
      · rw [List.filterMap_cons_some (by rw [if_pos h0, if_neg h1]), sumL_script_cons, insSem]
        simp only [hr.2, hof]
        by_cases he : uwBits (σ (G.hold0 M.np id, id)) = uwBits (b id)
        · rw [if_pos he, sumL_single, ih]
          refine if_congr ?_ rfl rfl
          rw [hcons]
          simp [EndOk, h0, h1, he]
        · rw [if_neg he, sumL_nil, if_neg fun h => he ((hcons.1 h).1.2.1 h0 h1)]
    · by_cases h1 : grp (G.hold1 M.np id) = g
      · rw [List.filterMap_cons_some (by rw [if_neg h0, if_pos h1]), sumL_script_cons, insSem]
        simp only [hr.2, hof]
        by_cases he : uwBits (σ (G.hold1 M.np id, id)) = uwBits (b id)
        · rw [if_pos he, sumL_single, ih]
          refine if_congr ?_ rfl rfl
          rw [hcons]
          simp [EndOk, h0, h1, he]
        · rw [if_neg he, sumL_nil, if_neg fun h => he ((hcons.1 h).1.2.2 h0 h1)]
      · rw [List.filterMap_cons_none (by rw [if_neg h0, if_neg h1]), ih]
        refine if_congr ?_ rfl rfl
        rw [hcons]
        simp [EndOk, h0, h1]

theorem uwBits_injective (hub : 0 < ub) : Function.Injective (uwBits (ub := ub)) := by
  intro v w h
  by_cases hv : v = none
  · by_cases hw : w = none
    · rw [hv, hw]
    · have := (uwBits_ne_nil hub w).2 hw
      rw [← h, hv] at this
      exact absurd rfl this
  · by_cases hw : w = none
    · have := (uwBits_ne_nil hub v).2 hv
      rw [h, hw] at this
      exact absurd rfl this
    · exact G.uwBits_inj hv hw h

theorem rep_nil : Rep ub key .nil (fun _ : Cell M U0 U1 => none) :=
  ⟨tOk_nil ub, fun c => by rw [tget_nil]; rfl⟩

/-- **GROUP computes the value of a group.** -/
theorem sumL_script [Fintype Gr] (hkey : Function.Injective (Sum.elim key dkey)) (hub : 0 < ub) (hP : P.Ok cap)
    (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (hx : ∀ κ, (x κ).length ≤ T)
    (hρ : ∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2)
    (hkind : ∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩)
    (htab : ∀ (r : M.R) i y h, ∃ e : WE, e.val θ = (M.kind r.1).tab r.2 i y h)
    (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub
      (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b) .nil) (fun _ => 1) =
      G.grpVal mu T cb P q x ρ n o grp g b := by
  classical
  rw [grpVal_eq_exec hP]
  have hk : Function.Injective key := key_injective hkey
  -- one list of steps
  let I : Fin (K + K) ⊕ M.R → List Ins := Sum.elim (baseIns (fun z => (qn Q z : ℕ)) cb q x ρ n key dkey)
    fun r => [roleIns P n o key tg r]
  let s : Fin (K + K) ⊕ M.R → WStep A (Cell M U0 U1) (UW ub) := Sum.elim (baseStep mu T cb q x ρ n o grp g ub)
    (roleStep P n o grp g ub)
  let l : List (Fin (K + K) ⊕ M.R) := (baseList (A' := A') grp g).map Sum.inl ++ (roleList grp g M).map Sum.inr
  have hl : l.map s = steps mu T cb P q x ρ n o grp g ub := by
    simp only [l, s, List.map_append, List.map_map, steps]
    rfl
  have hI : script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b = l.flatMap I ++ endIns P n o grp g key b := by
    simp only [l, I, List.flatMap_append, List.flatMap_map, script, Sum.elim_inl, Sum.elim_inr]
    rw [flatMap_single]
  rw [hI, ← hl]
  refine sumL_steps (key := key) l I s ?_ _ _ ?_ _ _ rep_nil
  · intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
      exact stepOK_base hkey hub hmu hx (mem_baseList.1 hp) fun s => hρ s p
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hi
      exact stepOK_role hk hub (mem_roleList.1 hr) (hkind r) (htab r)
  · intro t σ hr
    rw [endIns, sumL_end b _ t σ hr]
    refine if_congr ?_ rfl rfl
    have huw : ∀ v w : UW ub, uwBits v = uwBits w ↔ v = w := fun v w => (uwBits_injective hub).eq_iff
    simp only [List.mem_filter, G.allIds, Finset.mem_toList, mem_univ, true_and, decide_eq_true_eq, EndOk, huw]
    constructor
    · intro h
      exact ⟨fun id hid => (h id hid).1, fun id hid => (h id hid).2.1, fun id hid => (h id hid).2.2⟩
    · intro h id hid
      exact ⟨h.both id hid, h.fst id hid, h.snd id hid⟩

/-- The conditions on the instructions hold. -/
theorem insOk_script (hkind : ∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩) (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    ∀ i ∈ script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b, InsOk S Q c kinds i := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_append.1 hi with hi | hi
    · obtain ⟨p, -, hi⟩ := List.mem_flatMap.1 hi
      rcases List.mem_cons.1 hi with rfl | hi
      · refine Fin.addCases (motive := fun p => InsOk S Q c kinds (Fin.addCases (motive := fun _ => Ins)
          (fun κ => .block (qn Q (q κ.castSucc)) (qn Q (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
          (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p))
          ?_ ?_ p
        · intro κ
          rw [Fin.addCases_left]
          exact ⟨(qn Q _).2, (qn Q _).2⟩
        · intro κ
          rw [Fin.addCases_right]
          intro a ha
          rw [List.mem_reverse] at ha
          obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
          simp
      · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hi
        trivial
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hi
      exact ⟨_, hkind r, by simp [slList]⟩
  · obtain ⟨id, -, h⟩ := List.mem_filterMap.1 hi
    split_ifs at h
    · simp only [Option.some.injEq] at h
      subst h
      trivial
    · simp only [Option.some.injEq] at h
      subst h
      trivial
    · simp only [Option.some.injEq] at h
      subst h
      trivial

end Nc.Grp
