/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.PlayThm

/-!
# Start: units (general laws)

The sum over the segments with staircase support is the sum, over the row data and the numbers of units, of the
values of the starting positions.
-/

set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K U0 U1 : ℕ} {N : Type} [Fintype N] [DecidableEq N] {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
  {cb : Option Γ → Fin c → Bool}

/-- The condition in the table of a party at the beginning. -/
def InitOk (ub : ℕ) {c : ℕ} (cb : Option Γ → Fin c → Bool) {A : ℕ} (ρ : Option S → RowData A)
    (n : Fin A → Fin A → ℕ) (p : Fin A) (y : Uid A U0 N U1 → UW ub) (R C : Option S → Fin A → List Γ) : Prop :=
  (∀ s, RowOk (ρ s) (R s)) ∧ (∀ b, ucount ub (strOf cb fun s => R s b) = n p b ∧
      ∀ k : Fin U0, y (.init p b k) = unitsOf ub (strOf cb fun s => R s b) k) ∧
    (∀ b, ucount ub (strOf cb fun s => C s b) = n b p ∧
      ∀ k : Fin U0, y (.init b p k) = unitsOf ub (strOf cb fun s => C s b) k)

open Classical in
theorem tabInit_eq (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → ℕ) (p : Fin (K + K)) (y : Uid (K + K) U0 N U1 → UW ub) :
    tabInit mu T cb q x ρ n p y =
      ∑ R ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T,
      ∑ C ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T,
        if InitOk ub cb ρ n p y R C then partyW mu T q x p R C else 0 := by
  unfold tabInit
  exact Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => if_congr Iff.rfl rfl rfl

/-- All initial units held by a party are present if its table is not zero. -/
theorem tabInit_ne_none {np : N → Bool → Fin (K + K + A')} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    {ρ : Option S → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {p : Fin (K + K)}
    {y : Uid (K + K) U0 N U1 → UW ub} (h : tabInit mu T cb q x ρ (fun a b => (n a b).1) p y ≠ 0) :
    ∀ id ∈ seen0 (N := N) (U1 := U1) n, Holds (hold0 np) (hold1 np) (Fin.castAdd A' p) id → y id ≠ none := by
  classical
  rw [tabInit_eq] at h
  obtain ⟨R, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨C, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at h with hc
  swap
  · exact absurd rfl h
  obtain ⟨-, h1, h2⟩ := hc
  intro id hid hh
  cases id with
  | new ν k => exact absurd hid new_not_mem_seen0
  | init a b k =>
    rw [init_mem_seen0] at hid
    rcases hh with hh | hh
    · have hh : p = a := Fin.castAdd_injective _ _ hh
      subst hh
      rw [(h1 b).2, Ne, unitsOf_eq_none, (h1 b).1]
      exact not_le.2 hid
    · have hh : p = b := Fin.castAdd_injective _ _ hh
      subst hh
      rw [(h2 a).2, Ne, unitsOf_eq_none, (h2 a).1]
      exact not_le.2 hid

/-- The table of a party at the beginning depends on its copies of initial units only. -/
theorem tabInit_congr {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {ρ : Option S → RowData (K + K)}
    {n : Fin (K + K) → Fin (K + K) → ℕ} {p : Fin (K + K)} {y y' : Uid (K + K) U0 N U1 → UW ub}
    (h : ∀ a b k, y (.init a b k) = y' (.init a b k)) :
    tabInit mu T cb q x ρ n p y = tabInit mu T cb q x ρ n p y' := by
  classical
  rw [tabInit_eq, tabInit_eq]
  refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => if_congr ?_ rfl rfl
  simp only [InitOk, h]

/-- What the parties write or read. -/
noncomputable def sides (Γ S : Type) [Fintype Γ] [Fintype S] [DecidableEq S] (K T : ℕ) :
    Finset (Fin (K + K) → Option S → Fin (K + K) → List Γ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Fintype.piFinset fun _ => wordsLe Γ T

theorem mem_sides {K T : ℕ} {R : Fin (K + K) → Option S → Fin (K + K) → List Γ} :
    R ∈ sides Γ S K T ↔ ∀ p s b, (R p s b).length ≤ T := by
  simp [sides, mem_wordsLe]

open Classical in
theorem prod_tabInit (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → ℕ) (y : Fin (K + K) → Uid (K + K) U0 N U1 → UW ub) :
    (∏ p, tabInit mu T cb q x (fun s => ρ s p) n p (y p)) =
      ∑ R ∈ sides Γ S K T, ∑ C ∈ sides Γ S K T, if ∀ p, InitOk ub cb (fun s => ρ s p) n p (y p) (R p) (C p) then
        ∏ p, partyW mu T q x p (R p) (C p) else 0 := by
  simp only [tabInit_eq]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, true_imp_iff]

open Classical in
/-- **Units.** -/
theorem sum_pos (hcb : Function.Injective cb) (hc : 0 < c) (hub : 0 < ub)
    (hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ U0) (np : N → Bool → Fin (K + K + A'))
    (q : Fin (K + 1) → Q) {x : Fin K → List Γ} (hx : ∀ κ, (x κ).length ≤ T) :
    (∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
      ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1),
        posVal (hold0 np) (hold1 np) (none : UW ub) (seen0 (N := N) (U1 := U1) n) (seen0 n) fun y =>
          ∏ p : Fin (K + K), tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p (y (Fin.castAdd A' p))
      else 0) =
    ∑ X ∈ segs Γ S K T, if ∀ s, Stair (X s) then segW mu T q x X else 0 := by
  have hpos : ∀ (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (f : (Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub) → F),
      posVal (hold0 np) (hold1 np) (none : UW ub) (seen0 n) (seen0 n) f = ∑ y, if
        y ∈ Contents (hold0 np) (hold1 np) none (seen0 n) ∧ Agree (hold0 np) (hold1 np) (seen0 n) y then
          f y else 0 := by
    intro n f
    rw [posVal, ← Finset.univ_inter (Contents (hold0 np) (hold1 np) none (seen0 n)), ← Finset.sum_ite_mem]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h1 : y ∈ Contents (hold0 np) (hold1 np) none (seen0 n) <;>
      by_cases h2 : Agree (hold0 np) (hold1 np) (seen0 n) y <;> simp [h1, h2]
  have hprod : ∀ (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → ℕ)
      (y : Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub),
      (∏ p : Fin (K + K), tabInit mu T cb q x (fun s => ρ s p) n p (y (Fin.castAdd A' p))) =
      ∑ R ∈ sides Γ S K T, ∑ C ∈ sides Γ S K T,
        if ∀ p, InitOk ub cb (fun s => ρ s p) n p (y (Fin.castAdd A' p)) (R p) (C p) then
          ∏ p, partyW mu T q x p (R p) (C p) else 0 := fun ρ n y =>
    prod_tabInit q x ρ n fun p => y (Fin.castAdd A' p)
  simp only [hpos, hprod, ite_sum, ite_ite_zero]
  -- one sum over all data
  let Cnd : (Option S → Fin (K + K) → RowData (K + K)) × (Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) ×
      (Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub) × (Fin (K + K) → Option S → Fin (K + K) → List Γ) ×
      (Fin (K + K) → Option S → Fin (K + K) → List Γ) → Prop := fun ω =>
    ValidRows ω.1 ∧ (ω.2.2.1 ∈ Contents (hold0 np) (hold1 np) none (seen0 ω.2.1) ∧
      Agree (hold0 np) (hold1 np) (seen0 ω.2.1) ω.2.2.1) ∧
      ∀ p, InitOk ub cb (fun s => ω.1 s p) (fun a b => (ω.2.1 a b).1) p (ω.2.2.1 (Fin.castAdd A' p)) (ω.2.2.2.1 p) (ω.2.2.2.2 p)
  have big : (∑ ω ∈ (univ ×ˢ (univ ×ˢ (univ ×ˢ (sides Γ S K T ×ˢ sides Γ S K T))) :
      Finset ((Option S → Fin (K + K) → RowData (K + K)) × (Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) ×
      (Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub) × (Fin (K + K) → Option S → Fin (K + K) → List Γ) ×
      (Fin (K + K) → Option S → Fin (K + K) → List Γ))),
      if Cnd ω then ∏ p, partyW mu T q x p (ω.2.2.2.1 p) (ω.2.2.2.2 p) else 0) =
      ∑ ρ : Option S → Fin (K + K) → RowData (K + K), ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1),
        ∑ y : Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub, ∑ R ∈ sides Γ S K T, ∑ C ∈ sides Γ S K T,
        if ValidRows ρ ∧ (y ∈ Contents (hold0 np) (hold1 np) none (seen0 n) ∧
          Agree (hold0 np) (hold1 np) (seen0 n) y) ∧ ∀ p, InitOk ub cb (fun s => ρ s p)
          (fun a b => (n a b).1) p (y (Fin.castAdd A' p)) (R p) (C p) then ∏ p, partyW mu T q x p (R p) (C p) else 0 := by
    simp only [Finset.sum_product, Cnd]
  refine big.symm.trans ?_
  symm
  -- the data of given segments
  let nX : (Option S → Fin (K + K) → Fin (K + K) → List Γ) → Fin (K + K) → Fin (K + K) → Fin (U0 + 1) :=
    fun X a b => ⟨min (ucount ub (strOf cb fun s => X s a b)) U0, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  let yX : (Option S → Fin (K + K) → Fin (K + K) → List Γ) → Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub :=
    fun X p id => match id with
      | .init a b k => if p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b then unitsOf ub (strOf cb fun s => X s a b) k
          else none
      | .new _ _ => none
  have hst : ∀ X, (if ∀ s, Stair (X s) then segW mu T q x X else 0) ≠ 0 →
      (∀ s, Stair (X s)) ∧ segW mu T q x X ≠ 0 := by
    intro X h
    by_cases hs : ∀ s, Stair (X s)
    · rw [if_pos hs] at h
      exact ⟨hs, h⟩
    · rw [if_neg hs] at h
      exact absurd rfl h
  have hrows : ∀ X : Option S → Fin (K + K) → Fin (K + K) → List Γ, (∀ s, Stair (X s)) →
      ∃ ρ : Option S → Fin (K + K) → RowData (K + K), ValidRows ρ ∧ ∀ s p, RowOk (ρ s p) (X s p) := by
    intro X h
    choose ρ h1 h2 using fun s => exists_rows (h s)
    exact ⟨ρ, h1, h2⟩
  choose ρX hρ1 hρ2 using hrows
  have hcount : ∀ X, segW mu T q x X ≠ 0 → ∀ a b, ucount ub (strOf cb fun s => X s a b) ≤ U0 := by
    intro X h a b
    refine le_trans ?_ hU
    rw [ucount, length_strOf]
    refine Nat.add_le_add_right (Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.add_le_add_right ?_ _))) _
    have ha : partyW mu T q x a (fun s b => X s a b) (fun s b => X s b a) ≠ 0 := fun h0 =>
      h (Finset.prod_eq_zero (Finset.mem_univ a) h0)
    exact (Finset.sum_le_sum fun s _ => length_le_cat (X s a) b).trans (partyW_sum_le hx ha)
  refine Finset.sum_bij_ne_zero (fun X _ h => (ρX X (hst X h).1, nX X, yX X, fun p s b => X s p b,
    fun p s b => X s b p)) ?_ ?_ ?_ ?_
  · intro X hX h
    rw [mem_segs] at hX
    simp only [Finset.mem_product, Finset.mem_univ, true_and, mem_sides]
    exact ⟨fun p s b => hX s p b, fun p s b => hX s b p⟩
  · intro X _ h X' _ h' heq
    have := congrArg (fun ω => ω.2.2.2.1) heq
    funext s a b
    exact congrFun (congrFun (congrFun this a) s) b
  · rintro ⟨ρ, n, y, R, C⟩ hω h
    have hC : Cnd (ρ, n, y, R, C) := by
      by_contra hc
      rw [if_neg hc] at h
      exact h rfl
    rw [if_pos hC] at h
    obtain ⟨v, ⟨hy, hag⟩, hI⟩ := hC
    simp only at v hy hag hI h
    rw [mem_contents_iff] at hy
    simp only [Finset.mem_product, Finset.mem_univ, true_and, mem_sides] at hω
    -- rows and columns agree
    have hRC : ∀ a b, (fun s => R a s b) = fun s => C b s a := by
      intro a b
      apply strOf_inj hcb hc
      apply unitsOf_inj hub
      intro k
      have r := (hI a).2.1 b
      have r' := (hI b).2.2 a
      by_cases hk : k < (n a b).1
      · have hkU : k < U0 := lt_of_lt_of_le hk (Nat.le_of_lt_succ (n a b).2)
        rw [← r.2 ⟨k, hkU⟩, ← r'.2 ⟨k, hkU⟩]
        exact hag (.init a b ⟨k, hkU⟩) (init_mem_seen0.2 hk)
      · rw [unitsOf_eq_none.2 (r.1.trans_le (not_lt.1 hk)), unitsOf_eq_none.2 (r'.1.trans_le (not_lt.1 hk))]
    let X : Option S → Fin (K + K) → Fin (K + K) → List Γ := fun s a b => R a s b
    have hCX : ∀ p s b, C p s b = X s b p := fun p s b => (congrFun (hRC b p) s).symm
    have hC' : C = fun p s b => X s b p := by
      funext p s b
      exact hCX p s b
    have hrow : ∀ s p, RowOk (ρ s p) (X s p) := fun s p => (hI p).1 s
    have hstX : ∀ s, Stair (X s) := fun s => stair_of_rows (v s) (hrow s)
    have hW : segW mu T q x X = ∏ p, partyW mu T q x p (R p) (C p) := by
      rw [hC']
      rfl
    have hne : (if ∀ s, Stair (X s) then segW mu T q x X else 0) ≠ 0 := by
      rw [if_pos hstX, hW]
      exact h
    refine ⟨X, mem_segs.2 fun s a b => hω.1 a s b, hne, ?_⟩
    have e1 : ρX X (hst X hne).1 = ρ := by
      funext s
      exact rows_unique (hρ1 X _ s) (v s) (hρ2 X _ s) (hrow s)
    have e2 : nX X = n := by
      funext a b
      apply Fin.ext
      have := ((hI a).2.1 b).1
      show min (ucount ub (strOf cb fun s => R a s b)) U0 = (n a b).1
      rw [this]
      exact Nat.min_eq_left (Nat.le_of_lt_succ (n a b).2)
    have e3 : yX X = y := by
      funext p id
      cases id with
      | new ν k =>
        symm
        exact hy _ _ fun hh => new_not_mem_seen0 hh.1
      | init a b k =>
        show (if p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b then unitsOf ub (strOf cb fun s => R a s b) k else none) =
          y p (.init a b k)
        by_cases hp : p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b
        · rw [if_pos hp]
          rcases hp with rfl | rfl
          · exact (((hI a).2.1 b).2 k).symm
          · rw [((hI b).2.2 a).2 k, hRC]
        · rw [if_neg hp]
          symm
          exact hy _ _ fun hh => hp hh.2
    rw [e1, e2, e3, hC']
  · intro X _ h
    obtain ⟨hs, hne⟩ := hst X h
    have hcnt := hcount X hne
    have hn : ∀ a b, (nX X a b).1 = ucount ub (strOf cb fun s => X s a b) := fun a b =>
      Nat.min_eq_left (hcnt a b)
    have hy : ∀ p a b k, p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b → yX X p (.init a b k) = unitsOf ub (strOf cb fun s => X s a b) k := by
      intro p a b k hp
      exact if_pos hp
    rw [if_pos hs, if_pos]
    · rfl
    refine ⟨hρ1 X hs, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_contents_iff]
      intro p id hn'
      cases id with
      | new ν k => rfl
      | init a b k =>
        by_cases hp : p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b
        · have h1 : yX X p (.init a b k) = unitsOf ub (strOf cb fun s => X s a b) k := hy p a b k hp
          refine h1.trans (unitsOf_eq_none.2 ?_)
          rw [← hn]
          exact not_lt.1 fun hk => hn' ⟨init_mem_seen0.2 hk, hp⟩
        · exact if_neg hp
    · intro id hid
      cases id with
      | new ν k => exact absurd hid new_not_mem_seen0
      | init a b k => exact (hy _ a b k (Or.inl rfl)).trans (hy _ a b k (Or.inr rfl)).symm
    · intro p
      refine ⟨fun s => hρ2 X hs s p, fun b => ⟨(hn p b).symm, fun k => hy _ p b k (Or.inl rfl)⟩,
        fun b => ⟨(hn b p).symm, fun k => hy _ b p k (Or.inr rfl)⟩⟩

open Classical in
/-- **Start.** The value of an automaton in `K * T` steps is the sum, over the states between the blocks, the row data
and the numbers of units, of the values of the starting positions. -/
theorem start (hcb : Function.Injective cb) (hc : 0 < c) (hub : 0 < ub)
    (hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ U0) (np : N → Bool → Fin (K + K + A')) (i e : Q)
    (u : Unit → List Γ) {ℓ : ℕ} (hℓ : ℓ ≤ T) (hu : (u ()).length ≤ K * ℓ) :
    runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
        ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1),
          posVal (hold0 np) (hold1 np) (none : UW ub) (seen0 (N := N) (U1 := U1) n) (seen0 n) fun y =>
            ∏ p : Fin (K + K), tabInit mu T cb q (parts ℓ (u ())) (fun s => ρ s p) (fun a b => (n a b).1) p
              (y (Fin.castAdd A' p))
      else 0
    else 0 := by
  rw [runVal_blocks]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hx : ∀ κ : Fin K, (parts ℓ (u ()) κ).length ≤ T := fun κ => (length_parts_le _ _ _).trans hℓ
  have hcat : cat (parts ℓ (u ()) : Fin K → List Γ) = u () := by
    rw [cat_parts, List.take_of_length_le hu]
  rw [sum_pos hcb hc hub hU np q hx, ← sum_segs q hx u hcat]

end Nc.G
