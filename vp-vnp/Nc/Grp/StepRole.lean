/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.StepBase
import Nc.Grp.SumRole

/-!
# The step of a role
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {tg : M.R → ℕ}

/-- The keys of the new units of a channel. -/
noncomputable def kNew (o : M.N → Fin U1) (key : Cell M U0 U1 → List Bool) (r : M.R) (ν : (M.kind r.1).CnAt r.2) :
    List (List Bool) := ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k)

theorem kNew_eq (r : M.R) (ν : (M.kind r.1).CnAt r.2) : kNew o key r ν =
    ((List.finRange U1).filter fun k => k.1 < (o ⟨r.1, ν.1⟩).1 + 1).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k) := by
  unfold kNew
  congr 1
  refine List.filter_congr fun k _ => ?_
  rw [decide_eq_decide, Nat.lt_succ_iff]
  rfl

theorem length_kNew (r : M.R) (ν : (M.kind r.1).CnAt r.2) : (kNew o key r ν).length = (o ⟨r.1, ν.1⟩).1 + 1 := by
  rw [kNew_eq, List.length_map, filter_finRange (by have := (o ⟨r.1, ν.1⟩).2; omega), List.length_ofFn]

theorem mem_kNew {r : M.R} {ν : (M.kind r.1).CnAt r.2} {k : List Bool} :
    k ∈ kNew o key r ν ↔ ∃ i : Fin U1, i ≤ o ⟨r.1, ν.1⟩ ∧ k = key (M.rp r, .new ⟨r.1, ν.1⟩ i) := by
  simp only [kNew, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

/-- What a role writes. -/
noncomputable def PN (o : M.N → Fin U1) (key : Cell M U0 U1 → List Bool) (r : M.R) {B : ℕ}
    (f : Fin B → Bk (M.kind r.1) r.2) : List (List (List Bool) × List Bool) :=
  (cnList (M.kind r.1) r.2).map fun ν => (kNew o key r ν, chS (M.kind r.1) r.2 f ν)

theorem mem_cnList {L : G.Law A} {p : L.Ro} (ν : L.CnAt p) : ν ∈ cnList L p := Finset.mem_toList.2 (mem_univ ν)

theorem mem_PN {r : M.R} {B : ℕ} {f : Fin B → Bk (M.kind r.1) r.2} {k : List Bool} :
    k ∈ (PN o key r f).flatMap Prod.fst ↔ ∃ ν : (M.kind r.1).CnAt r.2, ∃ i : Fin U1, i ≤ o ⟨r.1, ν.1⟩ ∧
      k = key (M.rp r, .new ⟨r.1, ν.1⟩ i) := by
  rw [PN, List.flatMap_map, List.mem_flatMap]
  constructor
  · rintro ⟨ν, -, h⟩
    exact ⟨ν, mem_kNew.1 h⟩
  · rintro ⟨ν, h⟩
    exact ⟨ν, mem_cnList ν, mem_kNew.2 h⟩

theorem nodup_PN (hkey : Function.Injective key) (r : M.R) {B : ℕ} (f : Fin B → Bk (M.kind r.1) r.2) :
    ((PN o key r f).flatMap Prod.fst).Nodup := by
  rw [PN, List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun ν _ => ?_, (Finset.nodup_toList _).imp fun {ν ν'} hν => ?_⟩
  · refine ((List.nodup_finRange _).filter _).map fun i j h => ?_
    have := hkey h
    simpa using this
  · rw [Function.onFun, List.disjoint_left]
    intro k hk1 hk2
    obtain ⟨i, -, rfl⟩ := mem_kNew.1 hk1
    obtain ⟨j, -, h⟩ := mem_kNew.1 hk2
    have := hkey h
    simp only [Prod.mk.injEq, true_and, G.Uid.new.injEq, Sigma.mk.injEq, heq_eq_eq] at this
    exact hν (Subtype.ext this.1)

/-- The contents after a role. -/
theorem rep_role (hkey : Function.Injective key) {r : M.R} (hr : grp (M.rp r) = g) {B : ℕ}
    (f : Fin B → Bk (M.kind r.1) r.2) {t : Tree} {σ : Cell M U0 U1 → UW ub} (h : Rep ub key t σ) :
    Rep ub key (putsAll ub (PN o key r f) t)
      (ovr ((dom n o grp g).filter fun c => c.1 = M.rp r ∧ isNewOf r.1 c.2 = true) (fun c => roleV ub r f c.2) σ) := by
  refine ⟨h.1.putsAll, fun c' => ?_⟩
  obtain ⟨a, id⟩ := c'
  by_cases hc : (a, id) ∈ (dom n o grp g).filter fun c => c.1 = M.rp r ∧ isNewOf r.1 c.2 = true
  · rw [ovr, if_pos hc]
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 hc
    simp only at h2
    subst h2
    cases id with
    | init _ _ _ => simp [isNewOf] at h3
    | new ν k =>
      simp only [isNewOf, decide_eq_true_eq] at h3
      have hk := (G.Plan.new_mem_seenAt.1 (mem_dom.1 h1).2.1).2
      obtain ⟨ν, rfl⟩ := exists_cnAt h3 (mem_dom.1 h1).2.2
      simp only
      rw [roleV_new]
      have hmem : (kNew o key r ν, chS (M.kind r.1) r.2 f ν) ∈ PN o key r f :=
        List.mem_map.2 ⟨ν, mem_cnList ν, rfl⟩
      refine tget_putsAll (nodup_PN hkey r f) hmem ?_ t
      simp only
      rw [kNew_eq]
      exact getElem_map_filter (by have := (o ⟨r.1, ν.1⟩).2; omega) _ k (Nat.lt_succ_of_le hk)
  · rw [ovr, if_neg hc, ← h.2, tget_putsAll_not (nodup_PN hkey r f)]
    rw [mem_PN]
    rintro ⟨ν, i, hi, he⟩
    have := hkey he
    rw [this] at hc
    exact hc (mem_filter.2 ⟨mem_dom.2 ⟨hr, G.Plan.new_mem_seenAt.2 ⟨r.1.2, hi⟩, holds_cnAt ν i⟩, rfl, by simp [isNewOf]⟩)

theorem uwBits_ne_nil (hub : 0 < ub) (w : UW ub) : uwBits w ≠ [] ↔ w ≠ none := by
  cases w with
  | none => simp [uwBits]
  | some w =>
    have : (List.ofFn w).length ≠ 0 := by
      rw [List.length_ofFn]
      omega
    simp only [uwBits, ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
    intro h
    rw [h] at this
    simp at this

theorem getD_append_replicate (l : List Bool) (m k : ℕ) : (l ++ List.replicate m false).getD k false = l.getD k false := by
  rcases lt_or_ge k l.length with h | h
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ h, List.getD_eq_default l _ h]
    rcases lt_or_ge (k - l.length) m with h' | h'
    · rw [List.getD_eq_getElem _ _ (by simpa using h'), List.getElem_replicate]
    · rw [List.getD_eq_default _ _ (by simpa using h')]

open Classical in
/-- **The step of a role.** -/
theorem stepOK_role (hkey : Function.Injective key) (hub : 0 < ub) {r : M.R} (hr : grp (M.rp r) = g)
    (hkind : kinds[tg r]? = some ⟨M.kind r.1, r.2⟩)
    (htab : ∀ i y h, ∃ e : WE, e.val θ = (M.kind r.1).tab r.2 i y h) :
    StepOK (S := S) θ T mu cb kinds key [roleIns P n o key tg r] (roleStep P n o grp g ub r) := by
  intro t σ Ψ Ψ' hrep hΨ
  rw [sumL_script_cons]
  simp only [sumL_script_nil]
  rw [roleIns, insSem, hkind]
  simp only
  have hct : ∀ id, (tget (key (M.rp r, id)) t).path = uwBits (σ (M.rp r, id)) := by
    intro id
    rw [hrep.2, path_ofBits]
  have hpres : (∀ es ∈ (univ : Finset ((M.kind r.1).SlAt r.2)).toList.map (fun e =>
      ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse), ∀ k ∈ es, (tget k t).path ≠ []) ↔
      ∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, σ (M.rp r, id) ≠ none := by
    simp only [List.forall_mem_map, Finset.mem_toList, mem_univ, true_imp_iff, List.mem_reverse]
    refine forall_congr' fun e => forall₂_congr fun id _ => ?_
    rw [hct, uwBits_ne_nil hub]
  by_cases hp : ∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, σ (M.rp r, id) ≠ none
  swap
  · rw [roleSem, if_neg fun h => hp (hpres.1 h), sumL_nil]
    symm
    refine Finset.sum_eq_zero fun f _ => ?_
    have : (roleStep P n o grp g ub r).w f σ = 0 := if_neg fun h => hp h.1
    rw [this, zero_mul]
  rw [roleSem, if_pos (hpres.2 hp), sumL_bindL, sumL_role _ _ htab]
  show _ = ∑ f : Fin (P.num n o r.1 * ub) → Bk (M.kind r.1) r.2, _
  refine Finset.sum_congr rfl fun f _ => ?_
  -- the streams
  have hins : ∀ e : (M.kind r.1).SlAt r.2, ∀ k : ℕ,
      ((((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map (fun e =>
        ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse)).map fun es =>
          es.reverse.flatMap fun k => (tget k t).path).getD (slIdx (M.kind r.1) r.2 e) []).getD k false =
      (slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩) fun id => σ (M.rp r, id)).getD k false := by
    intro e k
    have hlt : (slIdx (M.kind r.1) r.2 e : ℕ) < ((univ : Finset ((M.kind r.1).SlAt r.2)).toList).length :=
      (slIdx (M.kind r.1) r.2 e).2
    have hget : ((univ : Finset ((M.kind r.1).SlAt r.2)).toList)[(slIdx (M.kind r.1) r.2 e : ℕ)]'hlt = e :=
      List.getElem_idxOf hlt
    have hlist : (((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map (fun e =>
        ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse)).map fun es =>
          es.reverse.flatMap fun k => (tget k t).path).getD (slIdx (M.kind r.1) r.2 e) [] =
        (P.ids n o ⟨r.1, e.1⟩).flatMap fun id => uwBits (σ (M.rp r, id)) := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_map]; exact hlt), List.getElem_map,
        List.getElem_map, hget, List.reverse_reverse, List.flatMap_map]
      exact List.flatMap_congr fun id _ => hct id
    rw [hlist, slotBits, getD_append_replicate]
  -- the strings
  have hkeys : ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k)) =
      (PN o key r f).map Prod.fst := by
    rw [PN, List.map_map]
    rfl
  have hstr : (List.ofFn fun j => ((chS (M.kind r.1) r.2 f ((cnList (M.kind r.1) r.2).get j)).reverse).reverse ++ [true]) =
      (PN o key r f).map fun z => z.2 ++ [true] := by
    rw [PN, List.map_map]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp
  simp only [hins]
  rw [hkeys, hstr, putsL_eq hub]
  have hcnt : (∀ z ∈ PN o key r f, ucount ub z.2 = z.1.length) ↔
      ∀ ν : (M.kind r.1).CnAt r.2, ucount ub (chS (M.kind r.1) r.2 f ν) = (o ⟨r.1, ν.1⟩).1 + 1 := by
    rw [PN, List.forall_mem_map]
    constructor
    · intro h ν
      rw [h ν (mem_cnList ν), length_kNew]
    · intro h ν _
      rw [h ν, length_kNew]
  by_cases hc : ∀ ν : (M.kind r.1).CnAt r.2, ucount ub (chS (M.kind r.1) r.2 f ν) = (o ⟨r.1, ν.1⟩).1 + 1
  · rw [if_pos (hcnt.2 hc)]
    have hw : (roleStep P n o grp g ub r).w f σ = ∏ k, (M.kind r.1).tab r.2 (f k).1 (fun e =>
        (slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩) fun id => σ (M.rp r, id)).getD k false) (f k).2 := if_pos ⟨hp, hc⟩
    rw [hw]
    simp only [encT, List.map_cons, List.map_nil, sumL_single]
    congr 1
    exact hΨ _ _ (rep_role hkey hr f hrep)
  · rw [if_neg fun h => hc (hcnt.1 h)]
    have hw : (roleStep P n o grp g ub r).w f σ = 0 := if_neg fun h => hc h.2
    rw [hw, zero_mul]
    simp

end Nc.Grp
