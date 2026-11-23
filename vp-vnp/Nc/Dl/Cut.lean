/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.DealThm
import Nc.Dl.Facts

/-!
# One cut
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

/-- The brackets of a tree, as letters. -/
def wordG {Γ : Type} (b0 b1 : Γ) : Tree → List Γ
  | .nil => [b0]
  | .cons a b => b1 :: (wordG b0 b1 a ++ wordG b0 b1 b)

theorem length_wordG {Γ : Type} (b0 b1 : Γ) (z : Tree) : (wordG b0 b1 z).length = z.size := by
  induction z with
  | nil => rfl
  | cons a b iha ihb => simp only [wordG, List.length_cons, List.length_append, iha, ihb, Tree.size]

theorem wordT_eq {Γ : Type} (b0 b1 : Γ) (f : Γ → Tree) (z : Tree) : wordT (f b0) (f b1) z = (wordG b0 b1 z).map f := by
  induction z with
  | nil => rfl
  | cons a b iha ihb => simp only [wordT, wordG, iha, ihb, List.map_cons, List.map_append]

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {θ : List Bool → A} {K A' E U0 U1 ub mm D pS c T ℓ : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) (tab : SlpTab P grp D pS)
  (qn : Q → ℕ) (tg : M.R → ℕ) (bT bub nl nub : List Bool) (gt : Fin mm → Tree) (d1 gp : Tree) (cb : Option Γ → Fin c → Bool)
  (b0 b1 : Γ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)

/-- The code of a letter. -/
def lT (cb : Option Γ → Fin c → Bool) (a : Γ) : Tree := ofBits (List.ofFn (cb (some a)))

/-- The instances. -/
noncomputable def instTm (g : Fin mm) : Tm := .cons (.c gp) (scriptTm C tab tg bT bub gt d1 g)

/-- Steps 1 to 8. -/
noncomputable def steps18 : List DStep :=
  steps1 C qn i e ++ (steps2 C ++ (steps3 C hU0 ++ (steps4 C hU1 ++ ((steps5 C ++ (steps6 C tab ++ steps7 C tab)) ++
    steps8 C))))

theorem allSteps_eq : allSteps C tab qn hU0 hU1 i e = steps18 C tab qn i e hU0 hU1 ++ steps9 C := by
  simp only [allSteps, steps18, List.append_assoc]

/-- The dealing program. -/
noncomputable def dealProg : Fm :=
  dealF (lT cb b0) (lT cb b1) ((List.finRange K).map fun κ => C.nm (.part κ)) nl nub (steps18 C tab qn i e hU0 hU1)
    (steps9 C) ((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp))

/-- The parts as trees. -/
def ptT (cb : Option Γ → Fin c → Bool) (x : Fin K → List Γ) (κ : Fin K) : Tree :=
  listT (((x κ).map fun a => ofBits (List.ofFn (cb (some a)))).reverse)

theorem gets_parts (hnl : KT.val nl = ℓ) (z : Tree) :
    gets (partsT (KT.val nl) ((List.finRange K).map fun κ => C.nm (.part κ)) .nil (wordT (lT cb b0) (lT cb b1) z)) =
      byPath C.nm (S0 (ptT cb (parts ℓ (wordG b0 b1 z)))) := by
  have h0 : gets .nil = byPath C.nm fun _ => .nil := by
    rw [gets_nil]
    funext p
    unfold byPath
    split_ifs <;> rfl
  obtain ⟨st', h1, h2, h3⟩ := gets_partsT C.nm_inj (KT.val nl) ((List.finRange K).map Nm.part)
    ((List.nodup_finRange K).map fun a b h => by simpa using h) .nil (wordT (lT cb b0) (lT cb b1) z) _ h0
  rw [List.map_map] at h1
  have e1 : (C.nm ∘ Nm.part) = fun κ : Fin K => C.nm (.part κ) := rfl
  rw [e1] at h1
  rw [h1]
  congr 1
  funext y
  by_cases hy : y ∈ (List.finRange K).map (Nm.part : Fin K → NmT S M U0 U1 pS)
  · rw [List.mem_map] at hy
    obtain ⟨κ, -, rfl⟩ := hy
    have hk : κ.1 < ((List.finRange K).map (Nm.part : Fin K → NmT S M U0 U1 pS)).length := by simp
    have := h2 κ.1 hk
    rw [List.getElem_map, List.getElem_finRange] at this
    have h4 : st' (.part κ) = listT ((((wordT (lT cb b0) (lT cb b1) z)).drop (κ.1 * KT.val nl)).take (KT.val nl)).reverse :=
      this
    rw [h4, wordT_eq b0 b1 (lT cb), hnl, ← List.map_drop, ← List.map_take]
    rfl
  · rw [h3 y hy]
    cases y with
    | part κ => exact absurd (List.mem_map.2 ⟨κ, List.mem_finRange κ, rfl⟩) hy
    | _ => rfl

/-- **All states are good.** -/
theorem mem_execAll (hK : 0 < K) [Nonempty Q] [Nonempty (Fin U1)] {pt : Fin K → Tree} {σ : List Bool → Tree}
    (hσ : σ ∈ execAll ub (allSteps C tab qn hU0 hU1 i e) (byPath C.nm (S0 pt))) :
    ∃ (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
      (b : G.Uid (K + K) U0 M.N U1 → UW ub) (st : NmT S M U0 U1 pS → Tree), (q 0 = i ∧ q (Fin.last K) = e) ∧ ValidRows ρ ∧
      tab.valid n ∧ (∀ x, P.good n o x) ∧
      (∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)) ∧
      Final C tab qn pt q ρ n o b st ∧ σ = byPath C.nm st := by
  classical
  obtain ⟨st, hf, hs⟩ := sum_allSteps (ub := ub) C tab pt qn i e hU0 hU1 hK
  by_contra hno
  have h := hs ℤ fun σ' => if σ' = σ then 1 else 0
  have hz : ∀ (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
      (b : G.Uid (K + K) U0 M.N U1 → UW ub), (q 0 = i ∧ q (Fin.last K) = e) → ValidRows ρ → tab.valid n →
      (∀ x, P.good n o x) → (∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)) →
      byPath C.nm (st q ρ n o b) ≠ σ := fun q ρ n o b h1 h2 h3 h4 h5 h6 =>
    hno ⟨q, ρ, n, o, b, st q ρ n o b, h1, h2, h3, h4, h5, hf q ρ n o b, h6.symm⟩
  have hR : (∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : NN K U0, if tab.valid n then ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
            ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
              if ∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E) then
                (if byPath C.nm (st q ρ n o b) = σ then (1 : ℤ) else 0) else 0
            else 0 else 0 else 0 else 0) = 0 := by
    refine Finset.sum_eq_zero fun q _ => ?_
    split_ifs with h1
    swap
    · rfl
    refine Finset.sum_eq_zero fun ρ _ => ?_
    split_ifs with h2
    swap
    · rfl
    refine Finset.sum_eq_zero fun n _ => ?_
    split_ifs with h3
    swap
    · rfl
    refine Finset.sum_eq_zero fun o _ => ?_
    split_ifs with h4
    swap
    · rfl
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with h5 h6
    · exact absurd h6 (hz q ρ n o b h1 h2 h3 h4 h5)
    · rfl
    · rfl
  rw [hR] at h
  have hpos : (0 : ℤ) < ((execAll ub (allSteps C tab qn hU0 hU1 i e) (byPath C.nm (S0 pt))).map
      fun σ' => if σ' = σ then (1 : ℤ) else 0).sum := by
    refine lt_of_lt_of_le (b := (if σ = σ then (1 : ℤ) else 0)) (by simp) ?_
    refine List.single_le_sum (fun x hx => ?_) _ (List.mem_map.2 ⟨σ, hσ, rfl⟩)
    rw [List.mem_map] at hx
    obtain ⟨σ', -, rfl⟩ := hx
    split_ifs <;> norm_num
  omega

variable {mu : Letter S Unit Γ → Matrix Q Q A} {τ s τ' s' t : ℕ}

open Classical in
/-- **One cut.** -/
theorem deal_cut (hK : 0 < K) [Nonempty Q] [Nonempty (Fin U1)] (hnl : KT.val nl = ℓ) (hnub : KT.val nub = ub)
    (hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1) (hgt : ∀ (d : Fin D) (g : Fin mm), C.dt d = gt g ↔ d.1 = g.1)
    -- the automaton
    (hU : ∀ z, z.size ≤ s → Plain θ τ z → runVal mu i e (K * T) (fun _ => wordG b0 b1 z) = pv θ z)
    -- the formula of the pieces
    (hval : ∀ z, z.size ≤ s → runVal mu i e (K * T) (fun _ => wordG b0 b1 z) =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : NN K U0, if tab.valid n then
            ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
              ∑ b ∈ Common (none : UW ub) (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)),
                ∏ g, G.grpVal mu T cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g b
            else 0
          else 0
        else 0
      else 0)
    -- the program
    (hdoes : ∀ z, z.size ≤ s → ∃ Qs : List (A × Tree),
      Does θ (dealProg C tab qn tg bT bub nl nub gt d1 gp cb b0 b1 i e hU0 hU1) z Qs t ∧
      (∀ q ∈ Qs, ∃ σ ∈ execAll ub (allSteps C tab qn hU0 hU1 i e)
        (byPath C.nm (S0 (ptT cb (parts ℓ (wordG b0 b1 z))))),
        q.2 = listT (((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)).map fun t => t.expand σ)) ∧
      wsum Qs (pvs θ) = ((execAll ub (allSteps C tab qn hU0 hU1 i e)
        (byPath C.nm (S0 (ptT cb (parts ℓ (wordG b0 b1 z)))))).map
        fun σ => (((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)).map fun t => pv θ (t.expand σ)).prod).sum)
    -- the pieces
    (hpc : ∀ z, z.size ≤ s → ∀ (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0)
      (o : M.N → Fin U1) (b : G.Uid (K + K) U0 M.N U1 → UW ub) (g : Fin mm), ValidRows ρ → tab.valid n →
      (∀ x, P.good n o x) →
      (∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)) →
      (Tree.cons gp (Grp.scriptT bT bub (Grp.script qn cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g C.key C.dkey
        tg b))).size ≤ s' ∧
      Plain θ τ' (.cons gp (Grp.scriptT bT bub (Grp.script qn cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g C.key
        C.dkey tg b))) ∧
      pv θ (.cons gp (Grp.scriptT bT bub (Grp.script qn cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g C.key
        C.dkey tg b))) = G.grpVal mu T cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g b) :
    CutD θ τ s τ' s' mm t (dealProg C tab qn tg bT bub nl nub gt d1 gp cb b0 b1 i e hU0 hU1).code := by
  classical
  intro z hz
  obtain ⟨Qs, hD, hmem, hsum⟩ := hdoes z hz
  have hpt : ∀ κ : Fin K, ptT cb (parts ℓ (wordG b0 b1 z)) κ =
      listT (((parts ℓ (wordG b0 b1 z) κ).map fun a => ofBits (List.ofFn (cb (some a)))).reverse) := fun κ => rfl
  -- the instances at a final state
  have hinst : ∀ (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
      (b : G.Uid (K + K) U0 M.N U1 → UW ub) (st : NmT S M U0 U1 pS → Tree),
      (∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)) →
      Final C tab qn (ptT cb (parts ℓ (wordG b0 b1 z))) q ρ n o b st → ∀ g,
      (instTm C tab tg bT bub gt d1 gp g).expand (byPath C.nm st) = .cons gp (Grp.scriptT bT bub (Grp.script qn cb P q
        (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g C.key C.dkey tg b)) := by
    intro q ρ n o b st hb hst g
    rw [instTm, Tm.expand, Tm.expand, expand_scriptTm hst hd1 hgt hpt fun id hid hne =>
      (hb id).2 (Finset.mem_filter.2 ⟨hid, hne⟩)]
  have hpieces : ∀ q ∈ Qs, ∀ y ∈ q.2.toList, y.size ≤ s' ∧ Plain θ τ' y := by
    intro q hq y hy
    obtain ⟨σ, hσ, hq2⟩ := hmem q hq
    obtain ⟨q', ρ, n, o, b, st, h1, h2, h3, h4, h5, h6, rfl⟩ := mem_execAll C tab qn i e hU0 hU1 hK hσ
    rw [hq2, toList_listT, List.map_map, List.mem_map] at hy
    obtain ⟨g, -, rfl⟩ := hy
    simp only [Function.comp_apply]
    rw [hinst q' ρ n o b st h5 h6 g]
    have := hpc z hz q' ρ n o b g h2 h3 h4 h5
    exact ⟨this.1, this.2.1⟩
  refine ⟨Qs, by rw [Fm.ofTree_code]; exact hD, fun q hq => ⟨?_, fun y hy => (hpieces q hq y hy).1⟩, fun hpl =>
    ⟨fun q hq y hy => (hpieces q hq y hy).2, ?_⟩⟩
  · obtain ⟨σ, hσ, hq2⟩ := hmem q hq
    rw [hq2, toList_listT, List.length_map, List.length_map, List.length_finRange]
  · rw [hsum, ← hU z hz hpl, hval z hz]
    obtain ⟨st, hf, hs'⟩ := sum_allSteps (ub := ub) C tab (ptT cb (parts ℓ (wordG b0 b1 z))) qn i e hU0 hU1 hK
    rw [hs' A fun σ => _]
    refine Finset.sum_congr rfl fun q _ => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun ρ _ => ?_
    by_cases hρ : ValidRows ρ
    swap
    · rw [if_neg hρ, if_neg hρ]
    rw [if_pos hρ, if_pos hρ]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : tab.valid n
    swap
    · rw [if_neg hn, if_neg hn]
    rw [if_pos hn]
    rw [if_pos hn]
    refine Finset.sum_congr rfl fun o _ => ?_
    by_cases ho : ∀ x, P.good n o x
    swap
    · rw [if_neg ho, if_neg ho]
    rw [if_pos ho, if_pos ho]
    have hb : (∑ b ∈ Common (none : UW ub) (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)),
        ∏ g, G.grpVal mu T cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g b) =
        ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
          if b ∈ Common (none : UW ub) (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)) then
          ∏ g, G.grpVal mu T cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g b else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hb]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hbc : ∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)
    · rw [if_pos hbc, if_pos]
      · rw [List.map_map, Fin.prod_univ_def]
        congr 1
        refine List.map_congr_left fun g _ => ?_
        simp only [Function.comp_apply]
        rw [hinst q ρ n o b _ hbc (hf q ρ n o b) g]
        exact (hpc z hz q ρ n o b g hρ hn ho hbc).2.2.symm
      · rw [mem_common_iff]
        intro id hid
        by_contra hne
        exact hid ((hbc id).1 hne)
    · rw [if_neg hbc]
      split_ifs with hcm
      swap
      · rfl
      rw [mem_common_iff] at hcm
      push Not at hbc
      obtain ⟨id, hid⟩ := hbc
      rcases hid with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (hcm id h2) h1
      · obtain ⟨hcur, hne⟩ := Finset.mem_filter.1 h2
        refine Finset.prod_eq_zero (Finset.mem_univ (grp n o (G.hold0 M.np id))) ?_
        by_contra hg
        exact grpVal_ne_none hg hcur (Or.inl ⟨rfl, Ne.symm hne⟩) h1

end Nc.Dl
