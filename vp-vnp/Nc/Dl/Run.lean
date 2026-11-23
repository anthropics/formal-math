/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Phases
import Nc.Cut.Rows

/-!
# The runs of the dealing program
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

variable {B : Type} [CommRing B] {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m : ℕ}

section Values

variable (qn : Q → ℕ) (hU0 : U0 < D) (hU1 : U1 ≤ D)

/-- A number of units as a digit. -/
def digN (n : Fin (U0 + 1)) : Fin D := ⟨n, lt_of_le_of_lt (Nat.le_of_lt_succ n.2) hU0⟩

/-- An outcome as a digit. -/
def digO (j : Fin U1) : Fin D := ⟨j, lt_of_lt_of_le j.2 hU1⟩

/-- The flags of a row. -/
def flagT (d : RowData (K + K)) : Tree := listT ((List.ofFn fun b => Grp.rowFlag d b).reverse.map num)

/-- Keys of units written. -/
def kRT (a b : Fin (K + K)) (n : Fin (U0 + 1)) : Tree :=
  listT (((List.finRange U0).filter fun k => k.1 < n.1).map fun k => ofBits (C.key (Fin.castAdd A' a, .init a b k)))

/-- Keys of units read. -/
def kCT (a b : Fin (K + K)) (n : Fin (U0 + 1)) : Tree :=
  listT (((List.finRange U0).filter fun k => k.1 < n.1).map fun k =>
    ofBits (if a = b then C.dkey (b, k) else C.key (Fin.castAdd A' b, .init a b k)))

/-- Instructions for the diagonal. -/
def dgT (a : Fin (K + K)) (n : Fin (U0 + 1)) : Tree :=
  listT (((List.finRange U0).filter fun k => k.1 < n.1).map fun k =>
    (Grp.Ins.both (C.key (Fin.castAdd A' a, .init a a k)) (C.dkey (a, k))).tree)

/-- Keys of new units. -/
def chT (ν : M.N) (d : Bool) (j : Fin U1) : Tree :=
  listT (((List.finRange U1).filter fun k => k ≤ j).map fun k => ofBits (C.key (M.np ν d, .new ν k)))

end Values

section Picks

variable (pt : Fin K → Tree) (qn : Q → ℕ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)

/-- The state at the beginning. -/
def S0 : NmT S M U0 U1 pS → Tree
  | .part κ => pt κ
  | _ => .nil

/-- Names of phase 1. -/
def own1 : NmT S M U0 U1 pS → Option (Fin (K + 1))
  | .q a => some a
  | _ => none

/-- Values of phase 1. -/
def v1 (q : Fin (K + 1) → Q) : NmT S M U0 U1 pS → Tree
  | .q a => num (qn (q a))
  | _ => .nil

/-- Options of phase 1. -/
noncomputable def opts1 (a : Fin (K + 1)) : List Q :=
  if a = 0 then [i] else if a = Fin.last K then [e] else (univ : Finset Q).toList

/-- Phase 1: the states between the blocks. -/
noncomputable def steps1 : List DStep := (univ : Finset (Fin (K + 1))).toList.map fun a =>
  pickS C (opts1 i e a) fun q => [(.q a, num (qn q))]

/-- The state after phase 1. -/
def S1 (q : Fin (K + 1) → Q) : NmT S M U0 U1 pS → Tree := fun x =>
  if (own1 x).isSome then v1 qn q x else S0 pt x

theorem phase1 (hK : 0 < K) [Nonempty Q] (Φ : (List Bool → Tree) → B) :
    ((execAll m (steps1 C qn i e) (byPath C.nm (S0 pt))).map Φ).sum =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then Φ (byPath C.nm (S1 pt qn q)) else 0 := by
  classical
  rw [steps1, phase_picks C rfl (opts1 i e) (fun a => ?_) (fun a q => [(.q a, num (qn q))]) own1 (v1 qn)
    (fun f a b hb => ?_) (fun f a x hx => ?_) rfl (fun _ => Classical.arbitrary Q)]
  · refine Finset.sum_congr rfl fun q _ => ?_
    have h0 : (0 : Fin (K + 1)) ≠ Fin.last K := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have key : (∀ a, q a ∈ opts1 i e a) ↔ q 0 = i ∧ q (Fin.last K) = e := by
      constructor
      · intro h
        have h1 := h 0
        have h2 := h (Fin.last K)
        rw [opts1, if_pos rfl, List.mem_singleton] at h1
        rw [opts1, if_neg (Ne.symm h0), if_pos rfl, List.mem_singleton] at h2
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩ a
        unfold opts1
        split_ifs with ha ha'
        · rw [ha, h1]; exact List.mem_singleton_self _
        · rw [ha', h2]; exact List.mem_singleton_self _
        · simp
    by_cases hq : q 0 = i ∧ q (Fin.last K) = e
    · rw [if_pos hq, if_pos (key.2 hq)]
      rfl
    · rw [if_neg hq, if_neg fun h => hq (key.1 h)]
  · unfold opts1
    split_ifs
    · simp
    · simp
    · exact Finset.nodup_toList _
  · rw [List.mem_singleton] at hb
    subst hb
    exact ⟨rfl, rfl⟩
  · cases x <;> simp only [own1, reduceCtorEq, Option.some.injEq] at hx
    subst hx
    exact ⟨_, List.mem_singleton_self _, rfl⟩

/-- Names of phase 2. -/
def own2 : NmT S M U0 U1 pS → Option (Option S × Fin (K + K))
  | .flag s p => some (s, p)
  | .rd s p => some (s, p)
  | _ => none

/-- Values of phase 2. -/
def v2 (ρ : Option S × Fin (K + K) → RowData (K + K)) : NmT S M U0 U1 pS → Tree
  | .flag s p => flagT (ρ (s, p))
  | .rd s p => ofBits (C.rc (ρ (s, p)))
  | _ => .nil

/-- Phase 2: row data. -/
noncomputable def steps2 : List DStep := (univ : Finset (Option S × Fin (K + K))).toList.map fun a =>
  pickS C (univ : Finset (RowData (K + K))).toList fun d => [(.flag a.1 a.2, flagT d), (.rd a.1 a.2, ofBits (C.rc d))]

theorem phase2 [Nonempty (RowData (K + K))] {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil)
    (Φ : (List Bool → Tree) → B) :
    ((execAll m (steps2 C) (byPath C.nm st)).map Φ).sum = ∑ ρ : Option S → Fin (K + K) → RowData (K + K),
      Φ (byPath C.nm fun x => if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else st x) := by
  classical
  rw [steps2, phase_picks C hz (fun _ => (univ : Finset (RowData (K + K))).toList) (fun _ => Finset.nodup_toList _)
    (fun a d => [(.flag a.1 a.2, flagT d), (.rd a.1 a.2, ofBits (C.rc d))]) own2 (v2 C)
    (fun f a b hb => ?_) (fun f a x hx => ?_) rfl (fun _ => Classical.arbitrary _)]
  · rw [← (Equiv.curry (Option S) (Fin (K + K)) (RowData (K + K))).sum_comp]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [if_pos]
    · rfl
    · intro a
      simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · cases x <;> simp only [own2, reduceCtorEq, Option.some.injEq] at hx
    · subst hx
      exact ⟨_, List.mem_cons_self, rfl⟩
    · subst hx
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩

/-- Names of phase 3. -/
def own3 : NmT S M U0 U1 pS → Option (Fin (K + K) × Fin (K + K))
  | .kR a b => some (a, b)
  | .kC a b => some (a, b)
  | .dn a b => some (a, b)
  | .dg a => some (a, a)
  | _ => none

/-- Values of phase 3. -/
def v3 (n : Fin (K + K) × Fin (K + K) → Fin (U0 + 1)) : NmT S M U0 U1 pS → Tree
  | .kR a b => kRT C a b (n (a, b))
  | .kC a b => kCT C a b (n (a, b))
  | .dn a b => C.dt (digN hU0 (n (a, b)))
  | .dg a => dgT C a (n (a, a))
  | _ => .nil

/-- Options of phase 3. -/
def o3 (a : Fin (K + K) × Fin (K + K)) (n : Fin (U0 + 1)) : List (NmT S M U0 U1 pS × Tree) :=
  (.kR a.1 a.2, kRT C a.1 a.2 n) :: (.kC a.1 a.2, kCT C a.1 a.2 n) :: (.dn a.1 a.2, C.dt (digN hU0 n)) ::
    if a.1 = a.2 then [(.dg a.1, dgT C a.1 n)] else []

/-- Phase 3: numbers of units. -/
noncomputable def steps3 : List DStep := (univ : Finset (Fin (K + K) × Fin (K + K))).toList.map fun a =>
  pickS C (univ : Finset (Fin (U0 + 1))).toList (o3 C hU0 a)

theorem phase3 {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil) (Φ : (List Bool → Tree) → B) :
    ((execAll m (steps3 C hU0) (byPath C.nm st)).map Φ).sum = ∑ n : NN K U0,
      Φ (byPath C.nm fun x => if (own3 x).isSome then v3 C hU0 (fun a => n a.1 a.2) x else st x) := by
  classical
  rw [steps3, phase_picks C hz (fun _ => (univ : Finset (Fin (U0 + 1))).toList) (fun _ => Finset.nodup_toList _)
    (o3 C hU0) own3 (v3 C hU0) (fun f a b hb => ?_) (fun f a x hx => ?_) rfl (fun _ => 0)]
  · rw [← (Equiv.curry (Fin (K + K)) (Fin (K + K)) (Fin (U0 + 1))).sum_comp]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [if_pos]
    · rfl
    · intro a
      simp
  · obtain ⟨a1, a2⟩ := a
    simp only [o3, List.mem_cons] at hb
    rcases hb with rfl | rfl | rfl | hb
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · split_ifs at hb with h
      · rw [List.mem_singleton] at hb
        subst hb
        have h : a1 = a2 := h
        subst h
        exact ⟨rfl, rfl⟩
      · simp at hb
  · cases x <;> simp only [own3, reduceCtorEq, Option.some.injEq] at hx
    · subst hx
      exact ⟨_, List.mem_cons_self, rfl⟩
    · subst hx
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
    · rename_i a0
      subst hx
      refine ⟨(.dg a0, dgT C a0 (f (a0, a0))), ?_, rfl⟩
      simp only [o3, if_true]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · subst hx
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩

/-- Names of phase 4. -/
def own4 : NmT S M U0 U1 pS → Option M.N
  | .dO ν => some ν
  | .ch ν _ => some ν
  | _ => none

/-- Values of phase 4. -/
def v4 (o : M.N → Fin U1) : NmT S M U0 U1 pS → Tree
  | .dO ν => C.dt (digO hU1 (o ν))
  | .ch ν d => chT C ν d (o ν)
  | _ => .nil

/-- Phase 4: outcomes. -/
noncomputable def steps4 : List DStep := (univ : Finset M.N).toList.map fun ν =>
  pickS C (univ : Finset (Fin U1)).toList fun j =>
    [(.dO ν, C.dt (digO hU1 j)), (.ch ν false, chT C ν false j), (.ch ν true, chT C ν true j)]

theorem phase4 [Nonempty (Fin U1)] {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil) (Φ : (List Bool → Tree) → B) :
    ((execAll m (steps4 C hU1) (byPath C.nm st)).map Φ).sum = ∑ o : M.N → Fin U1,
      Φ (byPath C.nm fun x => if (own4 x).isSome then v4 C hU1 o x else st x) := by
  classical
  rw [steps4, phase_picks C hz (fun _ => (univ : Finset (Fin U1)).toList) (fun _ => Finset.nodup_toList _)
    (fun ν j => [(.dO ν, C.dt (digO hU1 j)), (.ch ν false, chT C ν false j), (.ch ν true, chT C ν true j)]) own4
    (v4 C hU1) (fun f a b hb => ?_) (fun f a x hx => ?_) rfl (fun _ => Classical.arbitrary _)]
  · refine Finset.sum_congr rfl fun f _ => ?_
    rw [if_pos]
    intro a
    simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  · cases x with
    | dO ν =>
      simp only [own4, Option.some.injEq] at hx
      subst hx
      exact ⟨_, List.mem_cons_self, rfl⟩
    | ch ν d =>
      simp only [own4, Option.some.injEq] at hx
      subst hx
      cases d
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), rfl⟩
    | _ => simp [own4] at hx

end Picks

section Rows

/-- The row data are valid after the given last party. -/
def vr (h : ℕ) (d : RowData (K + K)) : Prop :=
  if d.1 then d.2.1.1 = h ∧ d.2.2.1 = h else h ≤ d.2.1.1 ∧ d.2.1 ≤ d.2.2

theorem validRow_iff (ρ : Fin (K + K) → RowData (K + K)) (p : Fin (K + K)) : ValidRow ρ p ↔ vr (prevHi ρ p) (ρ p) :=
  Iff.rfl

open Classical in
/-- Check of a row. -/
noncomputable def rowStep (a : Option S × Fin (K + K)) : DStep :=
  if h : a.2.1 = 0 then .op (C.nm .zero) (C.nm (.rd a.1 a.2)) (C.nm (.row a.1 a.2))
    (.cons (trieOf C.rc fun d => bit (decide (vr 0 d))) .nil)
  else .op (C.nm (.rd a.1 ⟨a.2.1 - 1, by omega⟩)) (C.nm (.rd a.1 a.2)) (C.nm (.row a.1 a.2))
    (trieOf C.rc fun d' => trieOf C.rc fun d => bit (decide (vr d'.2.2.1 d)))

/-- Phase 5: checks of the rows. -/
noncomputable def steps5 : List DStep := (univ : Finset (Option S × Fin (K + K))).toList.map (rowStep C)

open Classical in
theorem phase5 {st : NmT S M U0 U1 pS → Tree} {ρ : Option S → Fin (K + K) → RowData (K + K)} (hz : st .zero = .nil)
    (hρ : ∀ s p, st (.rd s p) = ofBits (C.rc (ρ s p))) :
    execAll m (steps5 C) (byPath C.nm st) = [byPath C.nm fun x =>
      if h : ∃ a : Option S × Fin (K + K), Nm.row a.1 a.2 = x then bit (decide (ValidRow (ρ h.choose.1) h.choose.2))
      else st x] := by
  refine phase_det C (fun a : Option S × Fin (K + K) => Nm.row a.1 a.2) (fun a b h => ?_)
    (fun a => bit (decide (ValidRow (ρ a.1) a.2)))
    (fun st => st .zero = .nil ∧ ∀ s p, st (.rd s p) = ofBits (C.rc (ρ s p))) ⟨hz, hρ⟩ (fun a st hst => ?_)
    (fun a st hst => ⟨?_, fun s p => ?_⟩) _ (fun a => Finset.mem_toList.2 (Finset.mem_univ a))
  · simp only [Nm.row.injEq] at h
    exact Prod.ext h.1 h.2
  · obtain ⟨hz, hr⟩ := hst
    unfold rowStep
    split_ifs with h
    · rw [exec_op C.nm_inj, hz, hr, path_ofBits]
      simp only [path, tget, hd_cons]
      rw [tget_trieOf C.rc_inj]
      have : prevHi (ρ a.1) a.2 = 0 := by rw [prevHi, dif_pos h]
      rw [validRow_iff, this]
    · rw [exec_op C.nm_inj, hr, hr, path_ofBits, path_ofBits, tget_trieOf C.rc_inj, tget_trieOf C.rc_inj]
      have : prevHi (ρ a.1) a.2 = (ρ a.1 ⟨a.2.1 - 1, by omega⟩).2.2.1 := by rw [prevHi, dif_neg h]
      rw [validRow_iff, this]
  · rw [Function.update_of_ne (by simp)]
    exact hst.1
  · rw [Function.update_of_ne (by simp)]
    exact hst.2 s p

end Rows

section Slp

variable (tab : SlpTab P grp D pS)

/-- The name of an input of the straight-line program. -/
def coord : (Fin (K + K) × Fin (K + K)) ⊕ M.N → NmT S M U0 U1 pS
  | .inl a => .dn a.1 a.2
  | .inr ν => .dO ν

open Classical in
/-- A step of the straight-line program. -/
noncomputable def slpStep (k : Fin pS) : DStep :=
  if h : ∃ i, tab.fn k = tab.inp i then C.un (coord h.choose) (.slp k) C.dt
  else if h : ∃ c, tab.fn k = fun _ => c then C.con (.slp k) (C.dt h.choose)
  else if h : ∃ i j : Fin pS, i < k ∧ j < k ∧ ∃ φ : Fin D → Fin D → Fin D, ∀ x, tab.fn k x = φ (tab.fn i x) (tab.fn j x)
    then C.bin (.slp h.choose) (.slp h.choose_spec.choose) (.slp k) h.choose_spec.choose_spec.2.2.choose
  else C.con (.slp k) .nil

/-- Phase 6: the straight-line program. -/
noncomputable def steps6 : List DStep := (List.finRange pS).map (slpStep C tab)

theorem exec_slpStep (x : NN K U0 × (M.N → Fin U1)) (k : Fin pS) {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil)
    (hc : ∀ i, st (coord i) = C.dt (tab.inp i x)) (hprev : ∀ j < k, st (.slp j) = C.dt (tab.fn j x)) :
    (slpStep C tab k).exec m (byPath C.nm st) = [byPath C.nm (Function.update st (.slp k) (C.dt (tab.fn k x)))] := by
  classical
  unfold slpStep
  split_ifs with h1 h2 h3
  · rw [exec_un hz (hc _)]
    have e := congrFun h1.choose_spec x
    exact congrArg (fun t => [byPath C.nm (Function.update st (Nm.slp k) (C.dt t))]) e.symm
  · rw [exec_con hz]
    have e := congrFun h2.choose_spec x
    exact congrArg (fun t => [byPath C.nm (Function.update st (Nm.slp k) (C.dt t))]) e.symm
  · obtain ⟨a1, a2, a3⟩ := h3.choose_spec.choose_spec
    rw [exec_bin (hprev _ a1) (hprev _ a2), ← a3.choose_spec x]
  · exfalso
    rcases tab.step k k.2 with h | h | ⟨i, hi, j, hj, φ, hφ⟩
    · exact h1 h
    · exact h2 h
    · exact h3 ⟨⟨i, hi.trans k.2⟩, ⟨j, hj.trans k.2⟩, hi, hj, φ, hφ⟩

theorem phase6 (x : NN K U0 × (M.N → Fin U1)) {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil)
    (hc : ∀ i, st (coord i) = C.dt (tab.inp i x)) :
    ∃ st' : NmT S M U0 U1 pS → Tree, execAll m (steps6 C tab) (byPath C.nm st) = [byPath C.nm st'] ∧
      (∀ k, st' (.slp k) = C.dt (tab.fn k x)) ∧ ∀ y, (∀ k, y ≠ .slp k) → st' y = st y := by
  -- the first k steps
  have key : ∀ k, k ≤ pS → ∃ st' : NmT S M U0 U1 pS → Tree,
      execAll m (((List.finRange pS).take k).map (slpStep C tab)) (byPath C.nm st) = [byPath C.nm st'] ∧
      (∀ j : Fin pS, j.1 < k → st' (.slp j) = C.dt (tab.fn j x)) ∧ ∀ y, (∀ k, y ≠ .slp k) → st' y = st y := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨st, rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨st', e1, e2, e3⟩ := ih (Nat.le_of_succ_le hk)
      have hlen : k < (List.finRange pS).length := by rw [List.length_finRange]; exact hk
      have e4 : (List.finRange pS).take (k + 1) = (List.finRange pS).take k ++ [⟨k, hk⟩] := by
        rw [List.take_succ_eq_append_getElem hlen, List.getElem_finRange]
        rfl
      refine ⟨Function.update st' (.slp ⟨k, hk⟩) (C.dt (tab.fn k x)), ?_, fun j hj => ?_, fun y hy => ?_⟩
      · rw [e4, List.map_append, execAll_append, e1, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons,
          List.map_nil, execAll, exec_slpStep C tab x ⟨k, hk⟩ (by rw [e3 _ (fun _ => by simp)]; exact hz)
          (fun i => by rw [e3 _ (fun _ => by cases i <;> simp [coord])]; exact hc i) (fun j hj => e2 j hj)]
        rfl
      · by_cases hjk : j.1 = k
        · have : j = ⟨k, hk⟩ := Fin.ext hjk
          subst this
          rw [Function.update_self]
        · rw [Function.update_of_ne (fun h => hjk (by simpa using congrArg (fun z => match z with | Nm.slp j => j.1 | _ => 0) h))]
          exact e2 j (by omega)
      · rw [Function.update_of_ne (hy _)]
        exact e3 y hy
  obtain ⟨st', e1, e2, e3⟩ := key pS le_rfl
  rw [List.take_of_length_le (by rw [List.length_finRange])] at e1
  exact ⟨st', e1, fun k => e2 k k.2, e3⟩

end Slp

end Nc.Dl
