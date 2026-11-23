/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Scr

/-!
# The sum over all runs of the dealing program
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

variable {B : Type} [CommRing B] {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m : ℕ}
  (tab : SlpTab P grp D pS) (pt : Fin K → Tree) (qn : Q → ℕ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)

/-- The state after the choices. -/
def S4 (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1) :
    NmT S M U0 U1 pS → Tree := fun x =>
  if (own4 x).isSome then v4 C hU1 o x else if (own3 x).isSome then v3 C hU0 (fun a => n a.1 a.2) x else
    if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else S1 pt qn q x

/-- The values after the deterministic phases. -/
structure Mid (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
    (st : NmT S M U0 U1 pS → Tree) : Prop where
  part : ∀ κ, st (.part κ) = pt κ
  q : ∀ a, st (.q a) = num (qn (q a))
  flag : ∀ s p, st (.flag s p) = flagT (ρ s p)
  kR : ∀ a b, st (.kR a b) = kRT C a b (n a b)
  kC : ∀ a b, st (.kC a b) = kCT C a b (n a b)
  dg : ∀ a, st (.dg a) = dgT C a (n a a)
  ch : ∀ ν d, st (.ch ν d) = chT C ν d (o ν)
  slp : ∀ k, st (.slp k) = C.dt (tab.fn k (n, o))
  num : ∀ x, st (.num x) = NS1.Tree.num (P.num n o x)
  row : ∀ s p, st (.row s p) ≠ .nil ↔ ValidRow (ρ s) p
  good : ∀ x, st (.cond (some x)) ≠ .nil ↔ P.good n o x
  valid : st (.cond none) ≠ .nil ↔ tab.valid n
  cut : ∀ id, ∃ c : Bool, st (.cut id) = bit c ∧
    (c = true ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E))

theorem exists_mid (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0)
    (o : M.N → Fin U1) : ∃ st : NmT S M U0 U1 pS → Tree,
    execAll m (steps5 C ++ (steps6 C tab ++ steps7 C tab)) (byPath C.nm (S4 C pt qn hU0 hU1 q ρ n o)) =
      [byPath C.nm st] ∧ Mid C tab pt qn q ρ n o st := by
  classical
  obtain ⟨s4, hs4⟩ : ∃ s, s = S4 C pt qn hU0 hU1 q ρ n o := ⟨_, rfl⟩
  have z4 : s4 .zero = .nil := by rw [hs4]; rfl
  have r4 : ∀ s p, s4 (.rd s p) = ofBits (C.rc (ρ s p)) := fun s p => by rw [hs4]; rfl
  have h5 := phase5 C (m := m) z4 r4
  obtain ⟨s5, hs5⟩ : ∃ s : NmT S M U0 U1 pS → Tree, s = fun x =>
      if h : ∃ a : Option S × Fin (K + K), Nm.row a.1 a.2 = x then bit (decide (ValidRow (ρ h.choose.1) h.choose.2))
      else s4 x := ⟨_, rfl⟩
  rw [← hs5] at h5
  have k5 : ∀ y, (∀ s p, y ≠ .row s p) → s5 y = s4 y := by
    intro y hy
    rw [hs5]
    exact dif_neg fun ⟨a, ha⟩ => hy a.1 a.2 ha.symm
  have w5 : ∀ s p, s5 (.row s p) = bit (decide (ValidRow (ρ s) p)) := by
    intro s p
    have h : ∃ a : Option S × Fin (K + K), (Nm.row a.1 a.2 : NmT S M U0 U1 pS) = .row s p := ⟨(s, p), rfl⟩
    rw [hs5]
    simp only [dif_pos h]
    have hinj : ∀ (s s' : Option S) (p p' : Fin (K + K)), (Nm.row s p : NmT S M U0 U1 pS) = .row s' p' → s = s' ∧ p = p' :=
      fun s s' p p' h => by simpa using h
    obtain ⟨h1, h2⟩ := hinj _ _ _ _ h.choose_spec
    rw [h1, h2]
  have hc : ∀ c, s5 (coord c) = C.dt (tab.inp c (n, o)) := by
    intro c
    rw [k5 _ fun s p => by cases c <;> simp [coord]]
    rcases c with ⟨a, b⟩ | ν
    · rw [hs4]
      show C.dt (digN hU0 (n a b)) = _
      congr 1
      apply Fin.ext
      rw [tab.inpN]
      rfl
    · rw [hs4]
      show C.dt (digO hU1 (o ν)) = _
      congr 1
      apply Fin.ext
      rw [tab.inpO]
      rfl
  obtain ⟨s6, h6, w6, k6⟩ := phase6 C tab (m := m) (n, o) (by rw [k5 _ fun s p => by simp]; exact z4) hc
  have z6 : s6 .zero = .nil := by rw [k6 _ fun k => by simp, k5 _ fun s p => by simp]; exact z4
  have h7 := phase7 C tab (m := m) (n, o) z6 w6
  obtain ⟨s7, hs7⟩ : ∃ s : NmT S M U0 U1 pS → Tree, s = fun y =>
      if h : ∃ a : Ix7 M U0 U1, nm7 a = y then v7 tab (n, o) h.choose else s6 y := ⟨_, rfl⟩
  rw [← hs7] at h7
  have k7 : ∀ y, (∀ a, y ≠ nm7 a) → s7 y = s6 y := by
    intro y hy
    rw [hs7]
    exact dif_neg fun ⟨a, ha⟩ => hy a ha.symm
  have w7 : ∀ a, s7 (nm7 a) = v7 tab (n, o) a := by
    intro a
    have h : ∃ a' : Ix7 M U0 U1, (nm7 a' : NmT S M U0 U1 pS) = nm7 a := ⟨a, rfl⟩
    rw [hs7]
    simp only [dif_pos h]
    rw [nm7_inj h.choose_spec]
  have old : ∀ y, (∀ s p, y ≠ .row s p) → (∀ k, y ≠ .slp k) → (∀ a, y ≠ nm7 a) → s7 y = s4 y := fun y h1 h2 h3 => by
    rw [k7 y h3, k6 y h2, k5 y h1]
  refine ⟨s7, ?_, ?_⟩
  · rw [← hs4, execAll_append, h5, List.flatMap_cons, List.flatMap_nil, List.append_nil, execAll_append, h6,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, h7]
  · have n7 : ∀ y : NmT S M U0 U1 pS, (∀ x, y ≠ .num x) → (∀ x, y ≠ .cond x) → (∀ x, y ≠ .cut x) → ∀ a, y ≠ nm7 a := by
      rintro y h1 h2 h3 (x | c | id)
      · exact h1 x
      · exact h2 c
      · exact h3 id
    refine ⟨fun κ => ?_, fun a => ?_, fun s p => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun ν d => ?_, fun k => ?_,
      fun x => ?_, fun s p => ?_, fun x => ?_, ?_, fun id => ?_⟩
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [k7 _ (n7 _ (by simp) (by simp) (by simp)), w6]
    · have := w7 (.inl x)
      simp only [nm7, v7] at this
      rw [this, tab.hnum]
    · rw [k7 _ (n7 _ (by simp) (by simp) (by simp)), k6 _ (by simp), w5, bit_ne_nil, decide_eq_true_eq]
    · have := w7 (.inr (.inl (some x)))
      simp only [nm7, v7] at this
      rw [this, bit_ne_nil, decide_eq_true_eq, tab.hgood]
    · have := w7 (.inr (.inl none))
      simp only [nm7, v7] at this
      rw [this, bit_ne_nil, decide_eq_true_eq, tab.hvalid]
    · have := w7 (.inr (.inr id))
      simp only [nm7, v7] at this
      refine ⟨_, this, ?_⟩
      rw [decide_eq_true_eq, tab.hcut, cutUnits, Finset.mem_filter]
      split_ifs with h <;> simp [h]

/-- All steps. -/
noncomputable def allSteps (i e : Q) : List DStep :=
  steps1 C qn i e ++ (steps2 C ++ (steps3 C hU0 ++ (steps4 C hU1 ++ ((steps5 C ++ (steps6 C tab ++ steps7 C tab)) ++
    (steps8 C ++ steps9 C)))))

open Classical in
/-- **All runs.** -/
theorem sum_allSteps (hK : 0 < K) [Nonempty Q] [Nonempty (Fin U1)] : ∃ st : (Fin (K + 1) → Q) →
    (Option S → Fin (K + K) → RowData (K + K)) → NN K U0 → (M.N → Fin U1) →
    (G.Uid (K + K) U0 M.N U1 → UW ub) → NmT S M U0 U1 pS → Tree,
    (∀ q ρ n o b, Final C tab qn pt q ρ n o b (st q ρ n o b)) ∧ ∀ (B : Type) [CommRing B] (Φ : (List Bool → Tree) → B),
    ((execAll ub (allSteps C tab qn hU0 hU1 i e) (byPath C.nm (S0 pt))).map Φ).sum =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : NN K U0, if tab.valid n then ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
            ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
              if ∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E) then
                Φ (byPath C.nm (st q ρ n o b)) else 0
            else 0 else 0 else 0 else 0 := by
  have hmid := fun q ρ n o => exists_mid (m := ub) C tab pt qn hU0 hU1 q ρ n o
  choose s7 hs7 hm7 using hmid
  refine ⟨fun q ρ n o b => (univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.foldl (fun st id => ov9 id (b id) st)
    (s7 q ρ n o), fun q ρ n o b => ?_, fun B _ Φ => ?_⟩
  · obtain ⟨f1, f2⟩ := foldl_ov9 b (univ : Finset (G.Uid (K + K) U0 M.N U1)).toList (s7 q ρ n o)
    have h := hm7 q ρ n o
    refine ⟨fun κ => ?_, fun a => ?_, fun s p => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun ν d => ?_, fun k => ?_,
      fun x => ?_, fun id v hv => f1 id (Finset.mem_toList.2 (Finset.mem_univ _)) v hv⟩
    · exact (f2 _ fun _ => by simp).trans (h.part κ)
    · exact (f2 _ fun _ => by simp).trans (h.q a)
    · exact (f2 _ fun _ => by simp).trans (h.flag s p)
    · exact (f2 _ fun _ => by simp).trans (h.kR a b)
    · exact (f2 _ fun _ => by simp).trans (h.kC a b)
    · exact (f2 _ fun _ => by simp).trans (h.dg a)
    · exact (f2 _ fun _ => by simp).trans (h.ch ν d)
    · exact (f2 _ fun _ => by simp).trans (h.slp k)
    · exact (f2 _ fun _ => by simp).trans (h.num x)
  · have hne : Nonempty (RowData (K + K)) := ⟨(false, ⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    rw [allSteps, sum_execAll_append, phase1 C pt qn i e hK fun σ' => _]
    refine Finset.sum_congr rfl fun q _ => if_congr Iff.rfl ?_ rfl
    rw [sum_execAll_append, phase2 C (by rfl) fun σ' => _]
    -- row data, numbers, outcomes
    have h4 : ∀ ρ, ((execAll ub (steps3 C hU0 ++ (steps4 C hU1 ++ ((steps5 C ++ (steps6 C tab ++ steps7 C tab)) ++
        (steps8 C ++ steps9 C)))) (byPath C.nm fun x => if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else
          S1 pt qn q x)).map Φ).sum = if ValidRows ρ then
          ∑ n : NN K U0, if tab.valid n then ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
            ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
              if ∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E) then
                Φ (byPath C.nm ((univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.foldl (fun st id => ov9 id (b id) st)
                  (s7 q ρ n o))) else 0
            else 0 else 0 else 0 := by
      intro ρ
      rw [sum_execAll_append, phase3 C hU0 (by rfl) fun σ' => _]
      have h5 : ∀ n : NN K U0, ((execAll ub (steps4 C hU1 ++ ((steps5 C ++ (steps6 C tab ++ steps7 C tab)) ++
          (steps8 C ++ steps9 C))) (byPath C.nm fun x => if (own3 x).isSome then v3 C hU0 (fun a => n a.1 a.2) x else
            if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else S1 pt qn q x)).map Φ).sum =
          ∑ o : M.N → Fin U1, if ValidRows ρ ∧ tab.valid n ∧ ∀ x, P.good n o x then
            ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
              if ∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E) then
                Φ (byPath C.nm ((univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.foldl (fun st id => ov9 id (b id) st)
                  (s7 q ρ n o))) else 0
            else 0 := by
        intro n
        rw [sum_execAll_append, phase4 C hU1 (by rfl) fun σ' => _]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [sum_execAll_append]
        have e4 : (fun x : NmT S M U0 U1 pS => if (own4 x).isSome then v4 C hU1 o x else
            if (own3 x).isSome then v3 C hU0 (fun a => n a.1 a.2) x else
            if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else S1 pt qn q x) = S4 C pt qn hU0 hU1 q ρ n o := rfl
        rw [e4, hs7 q ρ n o, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sum_execAll_append]
        have hm := hm7 q ρ n o
        by_cases hcond : ValidRows ρ ∧ tab.valid n ∧ ∀ x, P.good n o x
        · rw [if_pos hcond, phase8_pos C (fun s p => (hm.row s p).2 (hcond.1 s p)) (fun c => by
            cases c with
            | none => exact hm.valid.2 hcond.2.1
            | some x => exact (hm.good x).2 (hcond.2.2 x)), List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          choose cutb hcut1 hcut2 using hm.cut
          rw [phase9 C hcut1 Φ]
          refine Finset.sum_congr rfl fun b _ => if_congr (forall_congr' fun id => ?_) rfl rfl
          rw [hcut2]
        · rw [if_neg hcond, phase8_neg]
          · simp
          · by_contra hc
            push Not at hc
            refine hcond ⟨fun s p => (hm.row s p).1 (hc.1 s p), hm.valid.1 (hc.2 none), fun x => (hm.good x).1 (hc.2 (some x))⟩
      simp only [h5]
      by_cases hv : ValidRows ρ
      · rw [if_pos hv]
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases hvn : tab.valid n
        · rw [if_pos hvn]
          refine Finset.sum_congr rfl fun o _ => if_congr ?_ rfl rfl
          simp [hv, hvn]
        · rw [if_neg hvn]
          refine Finset.sum_eq_zero fun o _ => if_neg ?_
          rintro ⟨-, h, -⟩
          exact hvn h
      · rw [if_neg hv]
        refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun o _ => if_neg ?_
        rintro ⟨h, -⟩
        exact hv h
    exact Finset.sum_congr rfl fun ρ _ => h4 ρ

end Nc.Dl
