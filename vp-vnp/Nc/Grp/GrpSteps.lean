/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Steps
import Nc.G.Exact

/-!
# The value of a group as a sum over executions

Steps: the base parties of the group (blocks and input parties) write their initial units, then the roles, in the
order of the moves, write the new units.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset Nc.G Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c cap : ℕ} {Gr : Type} [DecidableEq Gr]

/-- Is it an initial unit? -/
def isInit {A U0 : ℕ} {N : Type} {U1 : ℕ} : G.Uid A U0 N U1 → Bool
  | .init _ _ _ => true
  | .new _ _ => false

/-- Is it a unit made by the move `x`? -/
def isNewOf {M : Sys F (K + K + A') E} (x : Fin E) : G.Uid (K + K) U0 M.N U1 → Bool
  | .init _ _ _ => false
  | .new ν _ => decide (ν.1 = x)

section

variable (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → Fin c → Bool)
  {M : Sys F (K + K + A') E} (P : G.Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
  (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
  (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr)

/-- Cells. -/
abbrev Cell (M : Sys F (K + K + A') E) (U0 U1 : ℕ) := Fin (K + K + A') × G.Uid (K + K) U0 M.N U1

/-- The cells of the group. -/
def dom : Finset (Cell M U0 U1) := univ.filter fun c =>
  grp c.1 = g ∧ c.2 ∈ G.Plan.seenAt n o E ∧ Holds (G.hold0 M.np) (G.hold1 M.np) c.1 c.2

/-- Contents of initial units. -/
noncomputable def initV (ub : ℕ) (N : Type) (U0 U1 : ℕ) (R C : Option S → Fin (K + K) → List Γ) (p : Fin (K + K)) :
    G.Uid (K + K) U0 N U1 → UW ub
  | .init a b k => if a = p then unitsOf ub (strOf cb fun s => R s b) k else unitsOf ub (strOf cb fun s => C s a) k
  | .new _ _ => none

/-- The conditions on what a base party writes and reads. -/
def InitC (ub U0 : ℕ) (n : Fin (K + K) → Fin (K + K) → ℕ) (ρ : Option S → RowData (K + K)) (p : Fin (K + K))
    (R C : Option S → Fin (K + K) → List Γ) : Prop :=
  (∀ s, RowOk (ρ s) (R s)) ∧ (∀ b, ucount ub (strOf cb fun s => R s b) = n p b) ∧
    (∀ b, ucount ub (strOf cb fun s => C s b) = n b p) ∧
    ∀ k : Fin U0, unitsOf ub (strOf cb fun s => R s p) k = unitsOf ub (strOf cb fun s => C s p) k

open Classical in
/-- The step of a base party. -/
noncomputable def baseStep (ub : ℕ) (p : Fin (K + K)) : WStep F (Cell M U0 U1) (UW ub) where
  ι := (Option S → Fin (K + K) → List Γ) × (Option S → Fin (K + K) → List Γ)
  Om := (Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T) ×ˢ
    (Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T)
  wr := (dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true
  w RC _ := if InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p RC.1 RC.2 then
    partyW mu T q x p RC.1 RC.2 else 0
  v RC _ c := initV cb ub M.N U0 U1 RC.1 RC.2 p c.2
  rd := ∅

/-- What a role chooses in a block. -/
abbrev Bk (L : Law F) (p : L.Ro) := Σ i : L.I, ∀ ν : L.CnAt p, Fin (L.len i ν) → Bool

/-- The string of a channel. -/
def chS (L : Law F) (p : L.Ro) {B : ℕ} (f : Fin B → Bk L p) (ν : L.CnAt p) : List Bool :=
  chString L.lab (fun j => L.len j ν) (fun k => (f k).1) (fun k => (f k).2 ν)

open Classical in
/-- The contents that a role writes. -/
noncomputable def roleV (ub : ℕ) {M : Sys F (K + K + A') E} (r : M.R) {B : ℕ} (f : Fin B → Bk (M.kind r.1) r.2) :
    G.Uid (K + K) U0 M.N U1 → UW ub
  | .init _ _ _ => none
  | .new ν k => if h : ∃ c : (M.kind r.1).CnAt r.2, (⟨r.1, c.1⟩ : M.N) = ν then
      unitsOf ub (chS (M.kind r.1) r.2 f h.choose) k else none

open Classical in
/-- The step of a role. -/
noncomputable def roleStep (ub : ℕ) (r : M.R) : WStep F (Cell M U0 U1) (UW ub) where
  ι := Fin (P.num n o r.1 * ub) → Bk (M.kind r.1) r.2
  Om := univ
  wr := (dom n o grp g).filter fun c => c.1 = M.rp r ∧ isNewOf r.1 c.2 = true
  w f σ := if (∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, σ (M.rp r, id) ≠ none) ∧
      ∀ ν : (M.kind r.1).CnAt r.2, ucount ub (chS (M.kind r.1) r.2 f ν) = (o ⟨r.1, ν.1⟩).1 + 1 then
    ∏ k, (M.kind r.1).tab r.2 (f k).1 (fun e => (slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩)
      fun id => σ (M.rp r, id)).getD k false) (f k).2 else 0
  v f _ c := roleV ub r f c.2
  rd := univ.filter fun c => c.1 = M.rp r ∧ ∃ e : (M.kind r.1).SlAt r.2, c.2 ∈ P.ids n o ⟨r.1, e.1⟩

/-- The base parties of the group. -/
def baseList : List (Fin (K + K)) := (List.finRange (K + K)).filter fun p => grp (Fin.castAdd A' p) = g

/-- All roles, in the order of the moves. -/
noncomputable def allRoles (M : Sys F (K + K + A') E) : List M.R := (List.finRange E).flatMap fun x =>
  (univ : Finset (M.kind x).Ro).toList.map (Sigma.mk x)

/-- The roles of the group. -/
noncomputable def roleList (M : Sys F (K + K + A') E) : List M.R := (allRoles M).filter fun r => grp (M.rp r) = g

/-- The steps of a group. -/
noncomputable def steps (ub : ℕ) : List (WStep F (Cell M U0 U1) (UW ub)) :=
  (baseList grp g).map (baseStep mu T cb q x ρ n o grp g ub) ++ (roleList grp g M).map (roleStep P n o grp g ub)

end

section facts

variable {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {cb : Option Γ → Fin c → Bool}
  {M : Sys F (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}

theorem mem_dom {c : Cell M U0 U1} : c ∈ dom n o grp g ↔
    grp c.1 = g ∧ c.2 ∈ G.Plan.seenAt n o E ∧ Holds (G.hold0 M.np) (G.hold1 M.np) c.1 c.2 := by
  simp [dom]

theorem mem_baseList {p : Fin (K + K)} : p ∈ baseList (A' := A') grp g ↔ grp (Fin.castAdd A' p) = g := by
  simp [baseList]

theorem mem_allRoles (r : M.R) : r ∈ allRoles M := by
  obtain ⟨x, p⟩ := r
  exact List.mem_flatMap.2 ⟨x, List.mem_finRange x, List.mem_map.2 ⟨p, Finset.mem_toList.2 (mem_univ p), rfl⟩⟩

theorem mem_roleList {r : M.R} : r ∈ roleList grp g M ↔ grp (M.rp r) = g := by
  simp [roleList, mem_allRoles]

theorem nodup_baseList : (baseList (A' := A') (K := K) grp g).Nodup := (List.nodup_finRange _).filter _

theorem pairwise_allRoles : (allRoles M).Pairwise fun r r' => r ≠ r' ∧ r.1 ≤ r'.1 := by
  unfold allRoles
  rw [List.pairwise_flatMap]
  refine ⟨fun x _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (Finset.nodup_toList _).imp fun {p p'} h => ⟨fun h' => h ?_, le_rfl⟩
    exact eq_of_heq (Sigma.mk.inj h').2
  · refine (List.pairwise_lt_finRange E).imp fun {x x'} hx r hr r' hr' => ?_
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hr
    obtain ⟨p', -, rfl⟩ := List.mem_map.1 hr'
    exact ⟨fun h => hx.ne (Sigma.mk.inj h).1, hx.le⟩

theorem pairwise_roleList : (roleList grp g M).Pairwise fun r r' => r ≠ r' ∧ r.1 ≤ r'.1 :=
  pairwise_allRoles.filter _

/-- A cell of a new unit is written by a role. -/
theorem exists_role {a : Fin (K + K + A')} {ν : M.N} {k : Fin U1}
    (h : Holds (G.hold0 M.np) (G.hold1 M.np) a (G.Uid.new ν k : G.Uid (K + K) U0 M.N U1)) :
    ∃ d, a = M.rp (M.nr ν d) := by
  rcases h with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

theorem role_eq_of_rp {x : Fin E} {p p' : (M.kind x).Ro} (h : M.rp ⟨x, p⟩ = M.rp ⟨x, p'⟩) : p = p' :=
  M.inj x h

/-- The channels of a role. -/
theorem exists_cnAt {r : M.R} {ν : M.N} {k : Fin U1} (hx : ν.1 = r.1)
    (h : Holds (G.hold0 M.np) (G.hold1 M.np) (M.rp r) (G.Uid.new ν k : G.Uid (K + K) U0 M.N U1)) :
    ∃ c : (M.kind r.1).CnAt r.2, (⟨r.1, c.1⟩ : M.N) = ν := by
  obtain ⟨x, p⟩ := r
  obtain ⟨x', ν⟩ := ν
  simp only at hx
  subst hx
  rcases h with h | h
  · have : p = (M.kind x').c ν := role_eq_of_rp h
    exact ⟨⟨ν, Or.inl this.symm⟩, rfl⟩
  · have : p = (M.kind x').d ν := role_eq_of_rp h
    exact ⟨⟨ν, Or.inr this.symm⟩, rfl⟩

theorem holds_cnAt {r : M.R} (ν : (M.kind r.1).CnAt r.2) (k : Fin U1) :
    Holds (G.hold0 M.np) (G.hold1 M.np) (M.rp r) (G.Uid.new ⟨r.1, ν.1⟩ k : G.Uid (K + K) U0 M.N U1) := by
  obtain ⟨x, p⟩ := r
  obtain ⟨ν, h | h⟩ := ν
  · exact Or.inl (congrArg (M.part x) h.symm)
  · exact Or.inr (congrArg (M.part x) h.symm)

theorem roleV_new (r : M.R) {B : ℕ} (f : Fin B → Bk (M.kind r.1) r.2) (ν : (M.kind r.1).CnAt r.2) (k : Fin U1) :
    roleV ub r f (G.Uid.new ⟨r.1, ν.1⟩ k : G.Uid (K + K) U0 M.N U1) = unitsOf ub (chS (M.kind r.1) r.2 f ν) k := by
  have h : ∃ c : (M.kind r.1).CnAt r.2, (⟨r.1, c.1⟩ : M.N) = ⟨r.1, ν.1⟩ := ⟨ν, rfl⟩
  rw [roleV, dif_pos h]
  have : h.choose = ν := Subtype.ext (eq_of_heq (Sigma.mk.inj h.choose_spec).2)
  rw [this]

/-- **All cells of the group are written.** -/
theorem wrs_steps : WStep.wrs (steps mu T cb P q x ρ n o grp g ub) = dom n o grp g := by
  ext ⟨a, id⟩
  rw [WStep.mem_wrs]
  constructor
  · rintro ⟨s, hs, hc⟩
    rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs
      exact (mem_filter.1 hc).1
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs
      exact (mem_filter.1 hc).1
  · intro hc
    obtain ⟨h1, h2, h3⟩ := mem_dom.1 hc
    cases id with
    | init a' b' k =>
      obtain ⟨p, rfl⟩ : ∃ p : Fin (K + K), a = Fin.castAdd A' p := by
        rcases h3 with h3 | h3
        · exact ⟨a', h3⟩
        · exact ⟨b', h3⟩
      exact ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨p, mem_baseList.2 h1, rfl⟩),
        mem_filter.2 ⟨hc, rfl, rfl⟩⟩
    | new ν k =>
      obtain ⟨d, rfl⟩ := exists_role h3
      refine ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨M.nr ν d, mem_roleList.2 h1, rfl⟩), ?_⟩
      exact mem_filter.2 ⟨hc, rfl, by simp [isNewOf, Sys.nr]⟩

/-- **The steps of a group are a sequence.** -/
theorem seq_steps (hP : P.Ok cap) : WStep.Seq (steps mu T cb P q x ρ n o grp g ub) := by
  have hnew : ∀ (r : M.R) (e : (M.kind r.1).SlAt r.2) (id) , id ∈ P.ids n o ⟨r.1, e.1⟩ →
      ∀ x', r.1 ≤ x' → isNewOf x' id = false := by
    intro r e id hid x' hx'
    have h1 := hP.sub n o _ (G.Plan.mem_ids.1 hid)
    have h2 := (G.Plan.mem_cur.1 h1).1
    cases id with
    | init _ _ _ => rfl
    | new ν k =>
      have h3 := (G.Plan.new_mem_seenAt.1 h2).1
      simp only [isNewOf, decide_eq_false_iff_not]
      rintro rfl
      exact absurd h3 (not_lt.2 hx')
  refine WStep.seq_of ?_ ?_
  · unfold steps
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      refine nodup_baseList.imp fun {p p'} hpp' => ⟨?_, disjoint_empty_left _⟩
      rw [disjoint_left]
      intro c hc hc'
      have h1 := (mem_filter.1 hc).2.1
      have h2 := (mem_filter.1 hc').2.1
      exact hpp' (Fin.castAdd_injective _ _ (h1.symm.trans h2))
    · rw [List.pairwise_map]
      refine pairwise_roleList.imp fun {r r'} hrr' => ⟨?_, ?_⟩
      · rw [disjoint_left]
        rintro ⟨a, id⟩ hc hc'
        obtain ⟨h1, h2, h3⟩ := mem_filter.1 hc
        obtain ⟨-, h4, h5⟩ := mem_filter.1 hc'
        cases id with
        | init _ _ _ => simp [isNewOf] at h3
        | new ν k =>
          simp only [isNewOf, decide_eq_true_eq] at h3 h5
          obtain ⟨x, p⟩ := r
          obtain ⟨x', p'⟩ := r'
          simp only at h2 h3 h4 h5
          obtain rfl := h3.symm.trans h5
          exact hrr'.1 (by rw [role_eq_of_rp (h2.symm.trans h4)])
      · rw [disjoint_left]
        rintro ⟨a, id⟩ hc hc'
        obtain ⟨-, -, e, he⟩ := mem_filter.1 hc
        have h5 := (mem_filter.1 hc').2.2
        rw [hnew r e id he _ hrr'.2] at h5
        exact absurd h5 (by simp)
    · intro s hs s' hs'
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs'
      refine ⟨?_, disjoint_empty_left _⟩
      rw [disjoint_left]
      rintro ⟨a, id⟩ hc hc'
      have h1 := (mem_filter.1 hc).2.2
      have h2 := (mem_filter.1 hc').2.2
      cases id with
      | init _ _ _ => simp [isNewOf] at h2
      | new _ _ => simp [isInit] at h1
  · intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs
      exact ⟨disjoint_empty_left _, fun ω _ y y' _ => ⟨rfl, fun c _ => rfl⟩⟩
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs
      refine ⟨?_, fun f _ y y' hy => ⟨?_, fun c _ => rfl⟩⟩
      · rw [disjoint_left]
        rintro ⟨a, id⟩ hc hc'
        obtain ⟨-, -, e, he⟩ := mem_filter.1 hc
        have h5 := (mem_filter.1 hc').2.2
        rw [hnew r e id he _ le_rfl] at h5
        exact absurd h5 (by simp)
      · have hy' : ∀ (e : (M.kind r.1).SlAt r.2), ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, y (M.rp r, id) = y' (M.rp r, id) :=
          fun e id hid => hy _ (mem_filter.2 ⟨mem_univ _, rfl, e, hid⟩)
        have e1 : (∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, y (M.rp r, id) ≠ none) ↔
            ∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, y' (M.rp r, id) ≠ none := by
          refine forall_congr' fun e => forall₂_congr fun id hid => ?_
          rw [hy' e id hid]
        have e2 : ∀ e : (M.kind r.1).SlAt r.2, slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩)
            (fun id => y (M.rp r, id)) = slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩)
            (fun id => y' (M.rp r, id)) := by
          intro e
          unfold slotBits
          congr 1
          refine List.flatMap_congr fun id hid => ?_
          simp only [hy' e id hid]
        simp only [roleStep, e1, e2]

end facts

end Nc.Grp
