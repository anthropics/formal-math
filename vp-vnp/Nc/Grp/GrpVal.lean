/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.GrpSteps

/-!
# The value of a group as a sum over executions: the theorem
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset Nc.G Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c cap : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {cb : Option Γ → Fin c → Bool}
  {M : Sys F (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}

/-- The factor of a base party. -/
theorem phi_baseStep {p : Fin (K + K)} (hp : grp (Fin.castAdd A' p) = g) {y : Cell M U0 U1 → UW ub}
    (hy : ∀ c, c ∉ dom n o grp g → y c = none) :
    (baseStep mu T cb q x ρ n o grp g ub p).phi y =
      G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p fun id => y (Fin.castAdd A' p, id) := by
  classical
  rw [G.tabInit, ← Finset.sum_product']
  refine Finset.sum_congr rfl ?_
  rintro ⟨R, C⟩ -
  have key : ((∀ s, RowOk (ρ s p) (R s)) ∧
        (∀ b, ucount ub (strOf cb fun s => R s b) = n p b ∧
          ∀ k : Fin U0, y (Fin.castAdd A' p, .init p b k) = unitsOf ub (strOf cb fun s => R s b) k) ∧
        (∀ b, ucount ub (strOf cb fun s => C s b) = n b p ∧
          ∀ k : Fin U0, y (Fin.castAdd A' p, .init b p k) = unitsOf ub (strOf cb fun s => C s b) k)) ↔
      (∀ c ∈ (baseStep mu T cb q x ρ n o grp g ub p).wr, y c = initV cb ub M.N U0 U1 R C p c.2) ∧
        InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p R C := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h1, fun b => (h2 b).1, fun b => (h3 b).1, fun k => ?_⟩
      · rintro ⟨a, id⟩ hc
        obtain ⟨h4, h5, h6⟩ := mem_filter.1 hc
        simp only at h5
        subst h5
        cases id with
        | new _ _ => simp [isInit] at h6
        | init a b k =>
          simp only [initV]
          by_cases hap : a = p
          · subst hap
            rw [if_pos rfl]
            exact (h2 b).2 k
          · rw [if_neg hap]
            have hbp : b = p := by
              rcases (mem_dom.1 h4).2.2 with h | h
              · exact absurd (Fin.castAdd_injective _ _ h).symm hap
              · exact (Fin.castAdd_injective _ _ h).symm
            subst hbp
            exact (h3 a).2 k
      · rw [← (h2 p).2 k, ← (h3 p).2 k]
    · rintro ⟨h1, h2, h3, h4, h5⟩
      have hin : ∀ a b (k : Fin U0), (a = p ∨ b = p) → k.1 < (n a b).1 →
          y (Fin.castAdd A' p, .init a b k) = initV cb ub M.N U0 U1 R C p (.init a b k) := by
        intro a b k hab hk
        refine h1 (Fin.castAdd A' p, .init a b k) (mem_filter.2 ⟨mem_dom.2 ⟨hp, G.Plan.init_mem_seenAt.2 hk, ?_⟩, rfl, rfl⟩)
        rcases hab with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hout : ∀ a b (k : Fin U0), ¬ k.1 < (n a b).1 → y (Fin.castAdd A' p, .init a b k) = none := by
        intro a b k hk
        exact hy _ fun h => hk (G.Plan.init_mem_seenAt.1 (mem_dom.1 h).2.1)
      refine ⟨h2, fun b => ⟨h3 b, fun k => ?_⟩, fun b => ⟨h4 b, fun k => ?_⟩⟩
      · by_cases hk : k.1 < (n p b).1
        · rw [hin p b k (Or.inl rfl) hk, initV, if_pos rfl]
        · rw [hout p b k hk]
          exact (unitsOf_eq_none.2 (by rw [h3 b]; exact not_lt.1 hk)).symm
      · by_cases hk : k.1 < (n b p).1
        · rw [hin b p k (Or.inr rfl) hk, initV]
          by_cases hbp : b = p
          · subst hbp
            rw [if_pos rfl]
            exact h5 k
          · rw [if_neg hbp]
        · rw [hout b p k hk]
          exact (unitsOf_eq_none.2 (by rw [h4 b]; exact not_lt.1 hk)).symm
  by_cases hA : ∀ c ∈ (baseStep mu T cb q x ρ n o grp g ub p).wr, y c = initV cb ub M.N U0 U1 R C p c.2
  · by_cases h2 : InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p R C
    · exact (if_pos hA).trans ((if_pos h2).trans (if_pos (key.2 ⟨hA, h2⟩)).symm)
    · exact (if_pos hA).trans ((if_neg h2).trans (if_neg fun h => h2 (key.1 h).2).symm)
  · exact (if_neg hA).trans (if_neg fun h => hA (key.1 h).1).symm

/-- Choices in all blocks. -/
def bkEquiv (L : Law F) (p : L.Ro) (B : ℕ) : (Fin B → Bk L p) ≃
    Σ i : Fin B → L.I, ∀ k, ∀ ν : L.CnAt p, Fin (L.len (i k) ν) → Bool where
  toFun f := ⟨fun k => (f k).1, fun k => (f k).2⟩
  invFun z k := ⟨z.1 k, z.2 k⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The factor of a role. -/
theorem phi_roleStep {r : M.R} (hr : grp (M.rp r) = g) {y : Cell M U0 U1 → UW ub}
    (hy : ∀ c, c ∉ dom n o grp g → y c = none) :
    (roleStep P n o grp g ub r).phi y = G.roleAt P n o r fun id => y (M.rp r, id) := by
  classical
  rw [G.roleAt, G.role]
  by_cases hne : ∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, y (M.rp r, id) ≠ none
  swap
  · rw [if_neg hne, WStep.phi]
    refine Finset.sum_eq_zero fun f _ => ?_
    have : (roleStep P n o grp g ub r).w f y = 0 := if_neg fun h => hne h.1
    rw [this, ite_self]
  rw [if_pos hne, WStep.phi]
  have hsig := Finset.sum_sigma' (univ : Finset (Fin (P.num n o r.1 * ub) → (M.kind r.1).I)) (fun _ => univ)
    (fun i (g : ∀ k, ∀ ν : (M.kind r.1).CnAt r.2, Fin ((M.kind r.1).len (i k) ν) → Bool) =>
      if ∀ ν : (M.kind r.1).CnAt r.2, ChOk ⟨r.1, ν.1⟩ (o ⟨r.1, ν.1⟩).1
          (chString (M.kind r.1).lab (fun j => (M.kind r.1).len j ν) i fun k => g k ν) (fun id => y (M.rp r, id))
        then ∏ k : Fin (P.num n o r.1 * ub), (M.kind r.1).tab r.2 (i k) (fun e =>
          (slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩) fun id => y (M.rp r, id)).getD k false) (g k) else 0)
  rw [hsig, Finset.univ_sigma_univ]
  refine Fintype.sum_equiv (bkEquiv (M.kind r.1) r.2 (P.num n o r.1 * ub)) _ _ fun f => ?_
  have key : (∀ ν : (M.kind r.1).CnAt r.2, ChOk ⟨r.1, ν.1⟩ (o ⟨r.1, ν.1⟩).1
        (chS (M.kind r.1) r.2 f ν) (fun id => y (M.rp r, id))) ↔
      (∀ c ∈ (roleStep P n o grp g ub r).wr, y c = roleV ub r f c.2) ∧
        ∀ ν : (M.kind r.1).CnAt r.2, ucount ub (chS (M.kind r.1) r.2 f ν) = (o ⟨r.1, ν.1⟩).1 + 1 := by
    constructor
    · intro h
      refine ⟨?_, fun ν => (h ν).1⟩
      rintro ⟨a, id⟩ hc
      obtain ⟨h4, h5, h6⟩ := mem_filter.1 hc
      simp only at h5
      subst h5
      cases id with
      | init _ _ _ => simp [isNewOf] at h6
      | new ν k =>
        simp only [isNewOf, decide_eq_true_eq] at h6
        obtain ⟨ν, rfl⟩ := exists_cnAt h6 (mem_dom.1 h4).2.2
        simp only
        rw [roleV_new]
        exact (h ν).2 k
    · rintro ⟨h1, h2⟩ ν
      refine ⟨h2 ν, fun k => ?_⟩
      by_cases hk : k ≤ o ⟨r.1, ν.1⟩
      · have hc : (M.rp r, G.Uid.new ⟨r.1, ν.1⟩ k) ∈ (roleStep P n o grp g ub r).wr := by
          refine mem_filter.2 ⟨mem_dom.2 ⟨hr, G.Plan.new_mem_seenAt.2 ⟨r.1.2, hk⟩, holds_cnAt ν k⟩, rfl, ?_⟩
          simp [isNewOf]
        have := h1 _ hc
        rw [roleV_new] at this
        exact this
      · have : y (M.rp r, G.Uid.new ⟨r.1, ν.1⟩ k) = none :=
          hy _ fun h => hk (G.Plan.new_mem_seenAt.1 (mem_dom.1 h).2.1).2
        show y (M.rp r, G.Uid.new ⟨r.1, ν.1⟩ k) = _
        rw [this]
        refine (unitsOf_eq_none.2 ?_).symm
        have h3 : (o ⟨r.1, ν.1⟩).1 < k.1 := not_le.1 hk
        show ucount ub (chS (M.kind r.1) r.2 f ν) ≤ k.1
        rw [h2 ν]
        exact h3
  by_cases h1 : ∀ c ∈ (roleStep P n o grp g ub r).wr, y c = roleV ub r f c.2
  · by_cases h2 : ∀ ν : (M.kind r.1).CnAt r.2, ucount ub (chS (M.kind r.1) r.2 f ν) = (o ⟨r.1, ν.1⟩).1 + 1
    · exact (if_pos h1).trans ((if_pos ⟨hne, h2⟩).trans (if_pos (key.2 ⟨h1, h2⟩)).symm)
    · exact (if_pos h1).trans ((if_neg fun h => h2 h.2).trans (if_neg fun h => h2 (key.1 h).2).symm)
  · exact (if_neg h1).trans (if_neg fun h => h1 (key.1 h).1).symm

/-- The product over the steps. -/
theorem prod_phi {y : Cell M U0 U1 → UW ub} (hy : ∀ c, c ∉ dom n o grp g → y c = none) :
    ((steps mu T cb P q x ρ n o grp g ub).map fun s => s.phi y).prod =
      ∏ a ∈ univ.filter (fun a => grp a = g), G.tabFinal mu T cb P q x ρ n o a fun id => y (a, id) := by
  classical
  rw [steps, List.map_append, List.prod_append, List.map_map, List.map_map]
  have e1 : ((baseList grp g).map ((fun s => s.phi y) ∘ baseStep mu T cb q x ρ n o grp g ub)).prod =
      ∏ p ∈ univ.filter (fun p => grp (Fin.castAdd A' p) = g),
        G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p fun id => y (Fin.castAdd A' p, id) := by
    rw [← List.prod_toFinset _ nodup_baseList]
    refine Finset.prod_congr ?_ fun p hp => phi_baseStep (mem_filter.1 hp).2 hy
    ext p
    simp [mem_baseList]
  have hnd : (roleList grp g M).Nodup := pairwise_roleList.imp fun h => h.1
  have e2 : ((roleList grp g M).map ((fun s => s.phi y) ∘ roleStep P n o grp g ub)).prod =
      ∏ r ∈ univ.filter (fun r => grp (M.rp r) = g), G.roleAt P n o r fun id => y (M.rp r, id) := by
    rw [← List.prod_toFinset _ hnd]
    refine Finset.prod_congr ?_ fun r hr => phi_roleStep (mem_filter.1 hr).2 hy
    ext r
    simp [mem_roleList]
  rw [e1, e2]
  have e3 : ∀ a, (G.tabFinal mu T cb P q x ρ n o a fun id => y (a, id)) =
      G.initAll mu T cb A' q x ρ n a (fun id => y (a, id)) *
        ∏ r : M.R, if M.rp r = a then G.roleAt P n o r (fun id => y (a, id)) else 1 := by
    intro a
    rw [G.tabFinal_eq, G.partyTab]
  rw [Finset.prod_congr rfl fun a _ => e3 a, Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_filter, Finset.prod_filter]
    have h := Fin.prod_univ_add (fun a : Fin (K + K + A') => if grp a = g then
      G.initAll mu T cb A' q x ρ n a (fun id => y (a, id)) else 1)
    refine Eq.trans ?_ h.symm
    have h1 : (∏ p : Fin A', if grp (Fin.natAdd (K + K) p) = g then
        G.initAll mu T cb A' q x ρ n (Fin.natAdd (K + K) p) (fun id => y (Fin.natAdd (K + K) p, id)) else 1) = 1 := by
      refine Finset.prod_eq_one fun p _ => ?_
      rw [G.initAll, Fin.addCases_right, ite_self]
    rw [h1, mul_one]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [G.initAll, Fin.addCases_left]
  · rw [Finset.prod_comm, Finset.prod_filter]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Finset.prod_ite_eq]
    simp only [mem_filter, mem_univ, true_and]

open Classical in
/-- **The value of a group is the sum over all executions of its steps.** -/
theorem grpVal_eq_exec [Fintype Gr] (hP : P.Ok cap) (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    G.grpVal mu T cb P q x ρ n o grp g b = WStep.exec (steps mu T cb P q x ρ n o grp g ub)
      (fun y => if GAgree (G.hold0 M.np) (G.hold1 M.np) grp g (P.cur n o E) b (fun a id => y (a, id)) then 1 else 0)
      (fun _ => none) := by
  rw [← WStep.sum_eq_exec _ (seq_steps hP), G.grpVal, groupVal]
  refine Finset.sum_equiv (Equiv.curry (Fin (K + K + A')) (G.Uid (K + K) U0 M.N U1) (UW ub)).symm ?_ ?_
  · intro y
    rw [mem_gcontents_iff, mem_filter]
    simp only [mem_univ, true_and, wrs_steps]
    constructor
    · rintro h ⟨a, id⟩ hc
      exact h a id fun h' => hc (mem_dom.2 h')
    · intro h a id hc
      exact h (a, id) fun h' => hc (mem_dom.1 h')
  · intro y hy
    rw [mem_gcontents_iff] at hy
    have hy' : ∀ c, c ∉ dom n o grp g → (Equiv.curry (Fin (K + K + A')) (G.Uid (K + K) U0 M.N U1) (UW ub)).symm y c = none := by
      rintro ⟨a, id⟩ hc
      exact hy a id fun h' => hc (mem_dom.2 h')
    rw [prod_phi hy', mul_ite, mul_one, mul_zero]
    rfl

end Nc.Grp
