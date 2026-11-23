/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Cut

/-!
# Bounds for the steps of the dealing program
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

section Reach

variable {m mb : ℕ}

end Reach

variable {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m mb : ℕ}

section Tries

theorem tget_mkTrie_mem (l : List (List Bool × Tree)) (p : List Bool) :
    tget p (mkTrie l) = .nil ∨ ∃ a ∈ l, a.1 = p ∧ tget p (mkTrie l) = a.2 := by
  induction l with
  | nil => left; exact tget_nil p
  | cons a l ih =>
    rw [mkTrie, List.foldr_cons, tget_tset]
    by_cases h : p = a.1
    · right
      exact ⟨a, List.mem_cons_self, h.symm, if_pos h⟩
    · rw [if_neg h]
      rw [mkTrie] at ih
      rcases ih with ih | ⟨b, hb, h1, h2⟩
      · exact Or.inl ih
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩

theorem tget_trieOf_cases {α : Type} [Fintype α] (code : α → List Bool) (f : α → Tree) (p : List Bool) :
    tget p (trieOf code f) = .nil ∨ ∃ a, tget p (trieOf code f) = f a := by
  rcases tget_mkTrie_mem ((Finset.univ : Finset α).toList.map fun a => (code a, f a)) p with h | ⟨a, ha, -, h⟩
  · exact Or.inl h
  · rw [List.mem_map] at ha
    obtain ⟨b, -, rfl⟩ := ha
    exact Or.inr ⟨b, h⟩

theorem tget_single (t : Tree) (p : List Bool) : tget p (.cons t .nil) = .nil ∨ tget p (.cons t .nil) = t := by
  cases p with
  | nil => exact Or.inr rfl
  | cons b p =>
    left
    cases b <;> exact tget_nil p

end Tries

section Readable

/-- The names that are read by steps. -/
def Rdb : NmT S M U0 U1 pS → Prop
  | .zero => True
  | .rd _ _ => True
  | .dn _ _ => True
  | .dO _ => True
  | .slp _ => True
  | _ => False

/-- Values at readable names are short. -/
def Short (Lc : ℕ) (σ : List Bool → Tree) : Prop := ∀ y : NmT S M U0 U1 pS, Rdb y → (σ (C.nm y)).len ≤ Lc

/-- Steps that keep values short and have bounded cost. -/
structure OkStep (Lc X : ℕ) (st : DStep) : Prop where
  keep : ∀ σ, Short C Lc σ → ∀ σ' ∈ st.exec m σ, Short C Lc σ'
  cost : ∀ σ, Short C Lc σ → st.cost m mb σ ≤ X

variable {C}

theorem Short.update {Lc : ℕ} {σ : List Bool → Tree} (h : Short C Lc σ) (y : NmT S M U0 U1 pS) {v : Tree}
    (hv : Rdb y → v.len ≤ Lc) : Short C Lc (Function.update σ (C.nm y) v) := by
  intro z hz
  by_cases hzy : z = y
  · subst hzy
    rw [Function.update_self]
    exact hv hz
  · rw [Function.update_of_ne fun h => hzy (C.nm_inj h)]
    exact h z hz

theorem Short.assign {Lc : ℕ} {σ : List Bool → Tree} (h : Short C Lc σ) {o : List (NmT S M U0 U1 pS × Tree)}
    (ho : ∀ a ∈ o, Rdb a.1 → a.2.len ≤ Lc) : Short C Lc (assignS σ (optT C.nm o)) := by
  unfold assignS optT
  rw [toList_listT]
  induction o generalizing σ with
  | nil => exact h
  | cons a o ih =>
    rw [List.map_cons, List.foldl_cons, hd_cons, tl_cons, path_ofBits]
    exact ih (h.update a.1 (ho a List.mem_cons_self)) fun b hb => ho b (List.mem_cons_of_mem _ hb)

variable {Lc : ℕ} (hnm : ∀ y, (C.nm y).length ≤ Lc)

include hnm

/-- Choices. -/
theorem okStep_pick {α : Type} (opts : List α) (o : α → List (NmT S M U0 U1 pS × Tree)) {X w : ℕ}
    (ho : ∀ a ∈ opts, ∀ b ∈ o a, Rdb b.1 → b.2.len ≤ Lc) (hX : opts.length ≤ X) (hw : ∀ a ∈ opts, (o a).length ≤ w) :
    OkStep (m := m) (mb := mb) C Lc (60 * Lc + 20 * X + X * (w * (60 * Lc + 80)) + 200) (pickS C opts o) := by
  have hlist : ∀ p : List Bool, (tget p (.cons (listT (opts.map fun a => optT C.nm (o a))) .nil)).toList = [] ∨
      (tget p (.cons (listT (opts.map fun a => optT C.nm (o a))) .nil)).toList = opts.map fun a => optT C.nm (o a) := by
    intro p
    rcases tget_single (listT (opts.map fun a => optT C.nm (o a))) p with h | h
    · left; rw [h]; rfl
    · right; rw [h, toList_listT]
  constructor
  · intro σ hσ σ' hσ'
    rw [pickS, DStep.exec, List.mem_map] at hσ'
    obtain ⟨t, ht, rfl⟩ := hσ'
    rcases hlist (σ (C.nm .zero)).path with h | h
    · rw [h] at ht
      simp at ht
    · rw [h, List.mem_map] at ht
      obtain ⟨a, ha, rfl⟩ := ht
      exact hσ.assign (ho a ha)
  · intro σ hσ
    have h1 := hnm .zero
    have h2 := hσ .zero trivial
    rw [pickS, DStep.cost]
    have hsum : ((opts.map fun a => optT C.nm (o a)).map fun t => (t.toList.map fun y => 60 * y.hd.len + 80).sum).sum ≤
        X * (w * (60 * Lc + 80)) := by
      rw [List.map_map]
      refine (List.sum_le_card_nsmul _ (w * (60 * Lc + 80)) ?_).trans ?_
      · intro n hn
        rw [List.mem_map] at hn
        obtain ⟨a, ha, rfl⟩ := hn
        simp only [Function.comp_apply, optT, toList_listT, List.map_map]
        refine (List.sum_le_card_nsmul _ (60 * Lc + 80) ?_).trans ?_
        · intro n hn
          rw [List.mem_map] at hn
          obtain ⟨b, hb, rfl⟩ := hn
          simp only [Function.comp_apply, hd_cons, len_ofBits]
          have := hnm b.1
          omega
        · rw [List.length_map, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (hw a ha)
      · rw [List.length_map, smul_eq_mul]
        exact Nat.mul_le_mul_right _ hX
    rcases hlist (σ (C.nm .zero)).path with h | h
    · rw [h]
      simp only [List.length_nil, List.map_nil, List.sum_nil]
      omega
    · rw [h]
      rw [List.length_map]
      have : 20 * opts.length ≤ 20 * X := Nat.mul_le_mul_left _ hX
      omega

/-- Operations. -/
theorem okStep_op {x y z : NmT S M U0 U1 pS} {φ : Tree} (hx : Rdb x) (hy : Rdb y)
    (hz : Rdb z → ∀ p q : List Bool, (tget q (tget p φ)).len ≤ Lc) :
    OkStep (m := m) (mb := mb) C Lc (180 * Lc + 200) (.op (C.nm x) (C.nm y) (C.nm z) φ) := by
  constructor
  · intro σ hσ σ' hσ'
    rw [DStep.exec, List.mem_singleton] at hσ'
    subst hσ'
    exact hσ.update z fun h => hz h _ _
  · intro σ hσ
    have h1 := hnm x
    have h2 := hnm y
    have h3 := hnm z
    have h4 := hσ x hx
    have h5 := hσ y hy
    rw [DStep.cost]
    omega

/-- Checks. -/
theorem okStep_check (x : NmT S M U0 U1 pS) :
    OkStep (m := m) (mb := mb) C Lc (30 * Lc + 100) (.check (C.nm x)) := by
  constructor
  · intro σ hσ σ' hσ'
    rw [DStep.exec] at hσ'
    split_ifs at hσ'
    · simp at hσ'
    · rw [List.mem_singleton] at hσ'
      subst hσ'
      exact hσ
  · intro σ _
    have := hnm x
    rw [DStep.cost]
    omega

end Readable

theorem OkStep.mono {C : Codes S M U0 U1 D pS} {Lc X X' : ℕ} {st : DStep} (h : OkStep (m := m) (mb := mb) C Lc X st)
    (hX : X ≤ X') : OkStep (m := m) (mb := mb) C Lc X' st := ⟨h.keep, fun σ hσ => (h.cost σ hσ).trans hX⟩

/-- The invariant for a list of such steps. -/
theorem okSteps_inv {C : Codes S M U0 U1 D pS} {Lc X : ℕ} {sts : List DStep}
    (h : ∀ st ∈ sts, OkStep (m := m) (mb := mb) C Lc X st) {σ0 : List Bool → Tree} (h0 : Short C Lc σ0) :
    ∃ I : List DStep → (List Bool → Tree) → Prop, (∀ st sts' σ, I (st :: sts') σ → st.cost m mb σ ≤ X ∧
      ∀ σ' ∈ st.exec m σ, I sts' σ') ∧ I sts σ0 := by
  refine ⟨fun rest σ => (∀ st ∈ rest, OkStep (m := m) (mb := mb) C Lc X st) ∧ Short C Lc σ, ?_, h, h0⟩
  rintro st sts' σ ⟨h1, h2⟩
  have hst := h1 st List.mem_cons_self
  exact ⟨hst.cost σ h2, fun σ' hσ' => ⟨fun s hs => h1 s (List.mem_cons_of_mem _ hs), hst.keep σ h2 σ' hσ'⟩⟩

section All

variable {C} (tab : SlpTab P grp D pS) (qn : Q → ℕ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)

/-- The bound for the cost of a step. -/
def stepB (Lc X : ℕ) : ℕ := 60 * Lc + 20 * X + X * (4 * (60 * Lc + 80)) + 180 * Lc + 200

theorem okSteps18 {Lc X : ℕ} (hnm : ∀ y, (C.nm y).length ≤ Lc) (hdc : ∀ d, (C.dc d).length ≤ Lc)
    (hrc : ∀ d, (C.rc d).length ≤ Lc) (hLc : 1 ≤ Lc) (hXQ : Fintype.card Q + 1 ≤ X)
    (hXr : Fintype.card (RowData (K + K)) ≤ X) (hXU : U0 + 1 ≤ X) (hXU1 : U1 ≤ X) :
    ∀ st ∈ steps18 C tab qn i e hU0 hU1, OkStep (m := m) (mb := mb) C Lc (stepB Lc X) st := by
  have hdt : ∀ d, (C.dt d).len ≤ Lc := fun d => by rw [dt, len_ofBits]; exact hdc d
  have hbit : ∀ b : Bool, (bit b).len ≤ Lc := fun b => by
    cases b
    · simp [bit, len]
    · simpa [bit, one, len] using hLc
  have hop : 180 * Lc + 200 ≤ stepB Lc X := by unfold stepB; omega
  have hck : 30 * Lc + 100 ≤ stepB Lc X := by unfold stepB; omega
  have hpk : ∀ w, w ≤ 4 → 60 * Lc + 20 * X + X * (w * (60 * Lc + 80)) + 200 ≤ stepB Lc X := by
    intro w hw
    have := Nat.mul_le_mul_left X (Nat.mul_le_mul_right (60 * Lc + 80) hw)
    unfold stepB
    omega
  have hun : ∀ (x dst : NmT S M U0 U1 pS) (f : Fin D → Tree), Rdb x → (Rdb dst → ∀ d, (f d).len ≤ Lc) →
      OkStep (m := m) (mb := mb) C Lc (stepB Lc X) (C.un x dst f) := by
    intro x dst f hx hf
    refine (okStep_op hnm (x := x) (y := .zero) (z := dst) hx trivial fun hd p q => ?_).mono hop
    rcases tget_trieOf_cases C.dc (fun d => Tree.cons (f d) .nil) p with h | ⟨d, h⟩
    · rw [h, tget_nil]; exact Nat.zero_le _
    · rw [h]
      rcases tget_single (f d) q with h' | h'
      · rw [h']; exact Nat.zero_le _
      · rw [h']; exact hf hd d
  have hcon : ∀ (dst : NmT S M U0 U1 pS) (t : Tree), (Rdb dst → t.len ≤ Lc) →
      OkStep (m := m) (mb := mb) C Lc (stepB Lc X) (C.con dst t) := by
    intro dst t ht
    refine (okStep_op hnm (x := .zero) (y := .zero) (z := dst) trivial trivial fun hd p q => ?_).mono hop
    rcases tget_single (.cons t .nil) p with h | h
    · rw [h, tget_nil]; exact Nat.zero_le _
    · rw [h]
      rcases tget_single t q with h' | h'
      · rw [h']; exact Nat.zero_le _
      · rw [h']; exact ht hd
  intro st hst
  simp only [steps18, List.mem_append] at hst
  rcases hst with h | h | h | h | (h | h | h) | h
  · -- states
    rw [steps1, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine (okStep_pick hnm _ _ (X := X) (w := 1) (fun q _ b hb hr => ?_) ?_ fun q _ => by simp).mono (hpk 1 (by norm_num))
    · rw [List.mem_singleton] at hb
      subst hb
      exact absurd hr (by simp [Rdb])
    · unfold opts1
      split_ifs
      · simp only [List.length_singleton]; omega
      · simp only [List.length_singleton]; omega
      · rw [Finset.length_toList, Finset.card_univ]; omega
  · rw [steps2, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine (okStep_pick hnm _ _ (X := X) (w := 2) (fun d _ b hb hr => ?_) ?_ fun d _ => by simp).mono (hpk 2 (by norm_num))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact absurd hr (by simp [Rdb])
      · simp only [len_ofBits]; exact hrc d
    · rw [Finset.length_toList, Finset.card_univ]; exact hXr
  · rw [steps3, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine (okStep_pick hnm _ _ (X := X) (w := 4) (fun d _ b hb hr => ?_) ?_ fun d _ => ?_).mono (hpk 4 le_rfl)
    · simp only [o3, List.mem_cons] at hb
      rcases hb with rfl | rfl | rfl | hb
      · exact absurd hr (by simp [Rdb])
      · exact absurd hr (by simp [Rdb])
      · exact hdt _
      · split_ifs at hb
        · rw [List.mem_singleton] at hb
          subst hb
          exact absurd hr (by simp [Rdb])
        · simp at hb
    · rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]; exact hXU
    · simp only [o3, List.length_cons]
      split_ifs <;> simp
  · rw [steps4, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine (okStep_pick hnm _ _ (X := X) (w := 3) (fun d _ b hb hr => ?_) ?_ fun d _ => by simp).mono (hpk 3 (by norm_num))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact hdt _
      · exact absurd hr (by simp [Rdb])
      · exact absurd hr (by simp [Rdb])
    · rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]; exact hXU1
  · rw [steps5, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    unfold rowStep
    split_ifs
    · exact (okStep_op hnm (x := .zero) (y := .rd _ _) trivial trivial fun hd => absurd hd (by simp [Rdb])).mono hop
    · exact (okStep_op hnm (x := .rd _ _) (y := .rd _ _) trivial trivial fun hd => absurd hd (by simp [Rdb])).mono hop
  · rw [steps6, List.mem_map] at h
    obtain ⟨k, -, rfl⟩ := h
    unfold slpStep
    split_ifs with h1 h2 h3
    · refine hun _ _ _ ?_ fun _ => hdt
      cases h1.choose <;> exact trivial
    · exact hcon _ _ fun _ => hdt _
    · refine (okStep_op hnm (x := .slp _) (y := .slp _) (z := .slp _) trivial trivial fun _ p q => ?_).mono hop
      rcases tget_trieOf_cases C.dc (fun d => trieOf C.dc fun d' => C.dt (h3.choose_spec.choose_spec.2.2.choose d d')) p with
        h | ⟨d, h⟩
      · rw [h, tget_nil]; exact Nat.zero_le _
      · rw [h]
        rcases tget_trieOf_cases C.dc (fun d' => C.dt (h3.choose_spec.choose_spec.2.2.choose d d')) q with h' | ⟨d', h'⟩
        · rw [h']; exact Nat.zero_le _
        · rw [h']; exact hdt _
    · exact hcon _ _ fun _ => Nat.zero_le _
  · rw [steps7, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    rcases a with y | c | id
    · exact hun _ _ _ trivial fun hd => absurd hd (by simp [Rdb])
    · exact hun _ _ _ trivial fun hd => absurd hd (by simp [Rdb])
    · exact hun _ _ _ trivial fun hd => absurd hd (by simp [Rdb])
  · rw [steps8, List.map_append, List.mem_append, List.map_map, List.map_map, List.mem_map, List.mem_map] at h
    rcases h with ⟨a, -, rfl⟩ | ⟨c, -, rfl⟩
    · exact (okStep_check hnm _).mono hck
    · exact (okStep_check hnm _).mono hck

end All

end Nc.Dl
