/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Bd3
import Nc.Dl.Code

/-!
# The cost of the dealing program
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {θ : List Bool → A} {K A' E U0 U1 ub mm D pS c T ℓ : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} {C : Codes S M U0 U1 D pS} {tab : SlpTab P grp D pS}
  {qn : Q → ℕ} {tg : M.R → ℕ} {bT bub nl nub : List Bool} {gt : Fin mm → Tree} {d1 gp : Tree} {cb : Option Γ → Fin c → Bool}
  {b0 b1 : Γ} {i e : Q} {hU0 : U0 < D} {hU1 : U1 ≤ D} {Lc X : ℕ}

/-- The bound for the cost of a template. -/
def tmB' (Lc X : ℕ) : ℕ := X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000) +
  X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500) + X * (2000 * Lc + 5000) + 1000

/-- The bound for the cost of the dealing program: `s` is the size of the argument, `bd` bounds the number of cut
units. -/
def dealB (Lc X K mm ub bd nS s : ℕ) : ℕ := 60 * s + (s + K) * (60 * Lc + 100) + K * (60 * Lc + 130) +
  nS * (stepB Lc X + 30) + (X * (90 * Lc + 230) + bd * ((ub + 1) * (60 * Lc + 100))) + mm * (tmB' Lc X + 60) + 300

theorem deal_does (hK : 0 < K) [Nonempty Q] [Nonempty (Fin U1)] (hnl : KT.val nl = ℓ) (hnub : KT.val nub = ub)
    (hnll : nl.length ≤ Lc) (hnubl : nub.length ≤ Lc)
    (hnm : ∀ y, (C.nm y).length ≤ Lc) (hdc : ∀ d, (C.dc d).length ≤ Lc)
    (hrc : ∀ d, (C.rc d).length ≤ Lc) (hLc : 1 ≤ Lc) (hXQ : Fintype.card Q + 1 ≤ X)
    (hXr : Fintype.card (RowData (K + K)) ≤ X) (hU0X : U0 + 1 ≤ X) (hXU1 : U1 ≤ X)
    (hS : Fintype.card (Option S) ≤ X) (hK2 : K + K ≤ X) (hId : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X)
    (hSl : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X)
    (hCn : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X) (hR : Fintype.card M.R ≤ X)
    {bd nS : ℕ} (hnS : (steps18 C tab qn i e hU0 hU1).length ≤ nS)
    (hbd : ∀ n o, tab.valid n → (∀ x, P.good n o x) →
      (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)).card ≤ bd) {s : ℕ} (z : Tree) (hz : z.size ≤ s) :
    ∃ Qs : List (A × Tree),
      Does θ (dealProg C tab qn tg bT bub nl nub gt d1 gp cb b0 b1 i e hU0 hU1) z Qs (dealB Lc X K mm ub bd nS s) ∧
      (∀ q ∈ Qs, ∃ σ ∈ execAll ub (allSteps C tab qn hU0 hU1 i e)
        (byPath C.nm (S0 (ptT cb (parts ℓ (wordG b0 b1 z))))),
        q.2 = listT (((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)).map fun t => t.expand σ)) ∧
      wsum Qs (pvs θ) = ((execAll ub (allSteps C tab qn hU0 hU1 i e)
        (byPath C.nm (S0 (ptT cb (parts ℓ (wordG b0 b1 z)))))).map
        fun σ => (((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)).map fun t => pv θ (t.expand σ)).prod).sum := by
  classical
  have hparts := gets_parts C nl cb b0 b1 hnl z
  obtain ⟨pt, hpt⟩ : ∃ pt, pt = ptT cb (parts (K := K) ℓ (wordG b0 b1 z)) := ⟨_, rfl⟩
  rw [← hpt] at hparts
  have hshort : Short C Lc (byPath C.nm (S0 pt)) := by
    intro y hy
    rw [byPath_nm C.nm_inj]
    cases y <;> simp_all [S0, Rdb, len]
  obtain ⟨I, hI, hI0⟩ := okSteps_inv (m := KT.val nub) (mb := nub.length)
    (okSteps18 tab qn i e hU0 hU1 hnm hdc hrc hLc hXQ hXr hU0X hXU1) hshort
  have h9 : ∀ σ ∈ execAll (KT.val nub) (steps18 C tab qn i e hU0 hU1) (byPath C.nm (S0 pt)),
      (∃ I' : List DStep → (List Bool → Tree) → Prop, ∃ c' : DStep → ℕ,
        (∀ st sts'' σ, I' (st :: sts'') σ → st.cost (KT.val nub) nub.length σ ≤ c' st ∧
          ∀ σ' ∈ st.exec (KT.val nub) σ, I' sts'' σ') ∧ I' (steps9 C) σ ∧
          ((steps9 C).map fun st => c' st + 30).sum ≤ X * (90 * Lc + 230) + bd * ((ub + 1) * (60 * Lc + 100))) ∧
      ∀ σ' ∈ execAll (KT.val nub) (steps9 C) σ, ∀ t ∈ (List.finRange mm).map (instTm C tab tg bT bub gt d1 gp),
        t.cost σ' ≤ tmB' Lc X := by
    intro σ hσ
    constructor
    · obtain ⟨q, ρ, n, o, st, hn, ho, hmid, rfl⟩ := mem_steps18 C tab pt qn i e hU0 hU1 hK hσ
      obtain ⟨I', c', h1, h2, h3⟩ := cost9 tab pt qn hnm (m := KT.val nub) (mb := nub.length) hmid
      refine ⟨I', c', h1, h2, h3.trans ?_⟩
      rw [hnub]
      have a1 := Nat.mul_le_mul_right (90 * Lc + 230) hId
      have a2 : (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)).card * ((ub + 1) * (60 * nub.length + 100)) ≤
          bd * ((ub + 1) * (60 * Lc + 100)) := Nat.mul_le_mul (hbd n o hn ho) (Nat.mul_le_mul_left _ (by omega))
      omega
    · intro σ' hσ' t ht
      rw [List.mem_map] at ht
      obtain ⟨g, -, rfl⟩ := ht
      have hmem : σ' ∈ execAll ub (allSteps C tab qn hU0 hU1 i e) (byPath C.nm (S0 pt)) := by
        rw [allSteps_eq, execAll_append, List.mem_flatMap]
        rw [hnub] at hσ hσ'
        exact ⟨σ, hσ, hσ'⟩
      obtain ⟨q, ρ, n, o, b, st, h1, h2, h3, h4, h5, hfin, rfl⟩ := mem_execAll C tab qn i e hU0 hU1 hK hmem
      exact cost_instTm hfin hnm hdc hS hK2 hId hU0X hSl hCn hR g
  have := dealF_does (θ := θ) (lT cb b0) (lT cb b1) ((List.finRange K).map fun κ => C.nm (.part κ)) nl nub
    (steps18 C tab qn i e hU0 hU1) (steps9 C) ((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)) z (Ln := Lc)
    (fun p hp => by
      rw [List.mem_map] at hp
      obtain ⟨κ, -, rfl⟩ := hp
      exact hnm _) (c := fun _ => stepB Lc X) (ct := tmB' Lc X) (c9 := X * (90 * Lc + 230) + bd * ((ub + 1) * (60 * Lc + 100)))
    hI (by rw [hparts]; exact hI0) (by rw [hparts]; exact h9)
  obtain ⟨Qs, d1', m1, s1⟩ := this
  rw [hparts, hnub, ← allSteps_eq] at m1 s1
  rw [← hpt]
  refine ⟨Qs, d1'.mono ?_, m1, s1⟩
  rw [List.length_map, List.length_finRange, List.length_map, List.length_finRange, List.map_const', List.sum_replicate,
    smul_eq_mul]
  have a1 : (steps18 C tab qn i e hU0 hU1).length * (stepB Lc X + 30) ≤ nS * (stepB Lc X + 30) := Nat.mul_le_mul_right _ hnS
  have a2 : (z.size + K) * (60 * nl.length + 100) ≤ (s + K) * (60 * Lc + 100) := Nat.mul_le_mul (by omega) (by omega)
  unfold dealB
  omega

/-- The number of the steps 1 to 8. -/
theorem length_steps18_le (hXQ : Fintype.card Q + 1 ≤ X) (hS : Fintype.card (Option S) ≤ X) (hK2 : K + K + 1 ≤ X)
    (hN : Fintype.card M.N ≤ X) (hpS : pS ≤ X) (hE : E + 1 ≤ X) (hId : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X) :
    (steps18 C tab qn i e hU0 hU1).length ≤ 4 * (X * X) + 10 * X := by
  have hm : Fintype.card (Option S) * (K + K) ≤ X * X := Nat.mul_le_mul hS (by omega)
  have hkk : (K + K) * (K + K) ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  simp only [steps18, steps1, steps2, steps3, steps4, steps5, steps6, steps7, steps8, List.length_append, List.length_map,
    Finset.length_toList, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_sum, List.length_finRange]
  rw [Fintype.card_option (α := Fin E), Fintype.card_fin]
  omega

end Nc.Dl
