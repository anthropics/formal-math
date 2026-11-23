/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Bd2

/-!
# Bounds for the templates
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

theorem cost_listTm (σ : List Bool → Tree) (ts : List Tm) :
    (listTm ts).cost σ = (ts.map fun t => t.cost σ + 100).sum + 20 := by
  induction ts with
  | nil => simp [listTm, Tm.cost]
  | cons t ts ih =>
    simp only [listTm, Tm.cost, ih, List.map_cons, List.sum_cons]
    omega

theorem cost_catTm (σ : List Bool → Tree) (ts : List Tm) :
    (catTm ts).cost σ = (ts.map fun t => t.cost σ + 62 * (t.expand σ).toList.length + 250).sum + 20 := by
  induction ts with
  | nil => simp [catTm, Tm.cost]
  | cons t ts ih =>
    simp only [catTm, Tm.cost, ih, List.map_cons, List.sum_cons]
    omega

theorem sum_map_le {α : Type*} (l : List α) (f : α → ℕ) {n b : ℕ} (h : ∀ a ∈ l, f a ≤ b) (hn : l.length ≤ n) :
    (l.map f).sum ≤ n * b := by
  refine (List.sum_le_card_nsmul _ b ?_).trans ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact h a ha
  · rw [List.length_map, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hn

variable {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} {C : Codes S M U0 U1 D pS}
  {tab : SlpTab P grp D pS} {qn : Q → ℕ} {pt : Fin K → Tree} {q : Fin (K + 1) → Q}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : NN K U0} {o : M.N → Fin U1}
  {b : G.Uid (K + K) U0 M.N U1 → UW ub} {st : NmT S M U0 U1 pS → Tree} {tg : M.R → ℕ} {bT bub : List Bool}
  {gt : Fin mm → Tree} {d1 gp : Tree} {Lc X : ℕ}

section

variable (hst : Final C tab qn pt q ρ n o b st) (hnm : ∀ y, (C.nm y).length ≤ Lc) (hdc : ∀ d, (C.dc d).length ≤ Lc)

include hst hnm hdc

theorem cost_gN (y : NmT S M U0 U1 pS) (σ : List Bool → Tree) : (gN C y).cost σ ≤ 30 * Lc + 50 := by
  have := hnm y
  simp only [gN, Tm.cost]
  omega

theorem size_slp (k : Fin pS) : (byPath C.nm st (C.nm (.slp k))).size ≤ 4 * Lc + 1 := by
  rw [byPath_nm C.nm_inj, hst.slp, dt]
  have h1 := size_ofBits (C.dc (tab.fn k (n, o)))
  have h2 := hdc (tab.fn k (n, o))
  omega

/-- Comparison of a digit. -/
theorem cost_ifeq (k : Fin pS) (t : Tree) (a c : Tm) : (Tm.ifeq (C.nm (.slp k)) t a c).cost (byPath C.nm st) ≤
    a.cost (byPath C.nm st) + c.cost (byPath C.nm st) + 270 * Lc + 260 := by
  have h1 := hnm (.slp k)
  have h2 := size_slp hst hnm hdc k
  simp only [Tm.cost]
  have h3 : (if byPath C.nm st (C.nm (.slp k)) = .nil then 0 else 0) = 0 := by split_ifs <;> rfl
  rw [h3]
  omega

theorem cost_ifTm (k : Fin pS) (t : Tree) (a : Tm) : (ifTm (C.nm (.slp k)) t a).cost (byPath C.nm st) ≤
    a.cost (byPath C.nm st) + 270 * Lc + 280 := by
  have := cost_ifeq hst hnm hdc k t a (.c .nil)
  have e : (Tm.c .nil).cost (byPath C.nm st) = 20 := rfl
  rw [ifTm]
  omega

variable (hS : Fintype.card (Option S) ≤ X) (hK2 : K + K ≤ X) (hId : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X)
  (hU0X : U0 + 1 ≤ X) (hSl : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X)
  (hCn : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X) (hR : Fintype.card M.R ≤ X)

include hS hK2

theorem cost_bodyTm (p : Fin (K + K)) :
    (bodyTm C p).cost (byPath C.nm st) ≤ 3 * (X * (30 * Lc + 150)) + 300 := by
  have h1 : ((listTm ((univ : Finset (Option S)).toList.map fun s => gN C (.flag s p)))).cost (byPath C.nm st) ≤
      X * (30 * Lc + 150) + 20 := by
    rw [cost_listTm, List.map_map]
    refine Nat.add_le_add_right (sum_map_le _ _ (fun s _ => ?_) ?_) _
    · have := cost_gN hst hnm hdc (.flag s p) (byPath C.nm st)
      simp only [Function.comp_apply]
      omega
    · rw [Finset.length_toList, Finset.card_univ]; exact hS
  have h2 : ∀ f : Fin (K + K) → NmT S M U0 U1 pS, (listTm (List.ofFn fun b => gN C (f b))).cost (byPath C.nm st) ≤
      X * (30 * Lc + 150) + 20 := by
    intro f
    rw [cost_listTm]
    refine Nat.add_le_add_right (sum_map_le _ _ (fun t ht => ?_) ?_) _
    · rw [List.mem_ofFn] at ht
      obtain ⟨b', rfl⟩ := ht
      have := cost_gN hst hnm hdc (f b') (byPath C.nm st)
      omega
    · rw [List.length_ofFn]; exact hK2
  have h3 := h2 fun b => .kR p b
  have h4 := h2 fun b => .kC b p
  simp only [bodyTm, Tm.cost]
  omega

theorem cost_basesTm (p : Fin (K + K)) :
    (basesTm C p).cost (byPath C.nm st) ≤ 3 * (X * (30 * Lc + 150)) + 90 * Lc + 1000 := by
  have h1 := cost_bodyTm hst hnm hdc hS hK2 p
  have h2 : (baseTm C p).cost (byPath C.nm st) ≤ 3 * (X * (30 * Lc + 150)) + 60 * Lc + 800 := by
    revert h1
    refine Fin.addCases (fun κ h1 => ?_) (fun κ h1 => ?_) p
    · rw [baseTm, Fin.addCases_left]
      have a1 := cost_gN hst hnm hdc (.q κ.castSucc) (byPath C.nm st)
      have a2 := cost_gN hst hnm hdc (.q κ.succ) (byPath C.nm st)
      simp only [Tm.cost]
      omega
    · rw [baseTm, Fin.addCases_right]
      have a1 := cost_gN hst hnm hdc (.part κ) (byPath C.nm st)
      simp only [Tm.cost]
      omega
  have h3 := cost_gN hst hnm hdc (.dg p) (byPath C.nm st)
  simp only [basesTm, Tm.cost]
  omega

include hId

theorem cost_slotTm (z : M.Z) (a : Fin (K + K + A')) :
    (slotTm C tab d1 z a).cost (byPath C.nm st) ≤ X * (270 * Lc + 700) + 20 := by
  rw [slotTm, cost_catTm, List.map_map]
  refine Nat.add_le_add_right (sum_map_le _ _ (fun id _ => ?_) ?_) _
  · have h1 := cost_ifTm hst hnm hdc (tab.kcons z id) d1 (.c (listT [ofBits (C.key (a, id))]))
    have e : (Tm.c (listT [ofBits (C.key (a, id))])).cost (byPath C.nm st) = 20 := rfl
    have h2 : ((ifTm (C.nm (.slp (tab.kcons z id))) d1 (.c (listT [ofBits (C.key (a, id))]))).expand
        (byPath C.nm st)).toList.length ≤ 1 := by
      rw [expand_ifTm]
      split_ifs
      · simp [Tm.expand]
      · simp
    simp only [Function.comp_apply]
    omega
  · rw [List.length_reverse, G.allIds, Finset.length_toList, Finset.card_univ]
    exact hId

include hSl hCn

theorem cost_roleTm (r : M.R) : (roleTm C tab tg d1 r).cost (byPath C.nm st) ≤
    X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 30 * Lc + 500 := by
  have h1 : (listTm ((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e => slotTm C tab d1 ⟨r.1, e.1⟩ (M.rp r))).cost
      (byPath C.nm st) ≤ X * (X * (270 * Lc + 700) + 120) + 20 := by
    rw [cost_listTm, List.map_map]
    refine Nat.add_le_add_right (sum_map_le _ _ (fun e _ => ?_) ?_) _
    · have := cost_slotTm (d1 := d1) hst hnm hdc hS hK2 hId ⟨r.1, e.1⟩ (M.rp r)
      simp only [Function.comp_apply]
      omega
    · rw [Finset.length_toList, Finset.card_univ]; exact hSl r
  have h2 : (listTm ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      gN C (.ch ⟨r.1, ν.1⟩ (decide ((M.kind r.1).c ν.1 ≠ r.2))))).cost (byPath C.nm st) ≤ X * (30 * Lc + 150) + 20 := by
    rw [cost_listTm, List.map_map]
    refine Nat.add_le_add_right (sum_map_le _ _ (fun ν _ => ?_) ?_) _
    · have := cost_gN hst hnm hdc (.ch ⟨r.1, ν.1⟩ (decide ((M.kind r.1).c ν.1 ≠ r.2))) (byPath C.nm st)
      simp only [Function.comp_apply]
      omega
    · rw [Finset.length_toList, Finset.card_univ]; exact hCn r
  have h3 := cost_gN hst hnm hdc (.num r.1) (byPath C.nm st)
  simp only [roleTm, Tm.cost]
  omega

omit hSl hCn in
theorem cost_endTm (g : Fin mm) (id : G.Uid (K + K) U0 M.N U1) :
    (endTm C tab gt d1 g id).cost (byPath C.nm st) ≤ 2000 * Lc + 4000 ∧
    ((endTm C tab gt d1 g id).expand (byPath C.nm st)).toList.length ≤ 1 := by
  have hone : ∀ k, (oneTm C k id).cost (byPath C.nm st) ≤ 30 * Lc + 500 := by
    intro k
    have := cost_gN hst hnm hdc (.cont id) (byPath C.nm st)
    rw [oneTm, cost_listTm]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Tm.cost]
    omega
  have lone : ∀ k, ((oneTm C k id).expand (byPath C.nm st)).toList.length = 1 := by
    intro k
    rw [oneTm, expand_listTm, toList_listT]
    rfl
  constructor
  · have e : ∀ t : Tree, (Tm.c t).cost (byPath C.nm st) = 20 := fun _ => rfl
    have h1 := hone (C.key (G.hold0 M.np id, id))
    have h2 := hone (C.key (G.hold1 M.np id, id))
    have h3 := cost_ifTm hst hnm hdc (tab.kgrp (G.hold1 M.np id)) (gt g) (oneTm C (C.key (G.hold1 M.np id, id)) id)
    have h4 := cost_ifeq hst hnm hdc (tab.kgrp (G.hold1 M.np id)) (gt g)
      (.c (listT [(Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id))).tree]))
      (oneTm C (C.key (G.hold0 M.np id, id)) id)
    have h5 := cost_ifeq hst hnm hdc (tab.kgrp (G.hold0 M.np id)) (gt g)
      (.ifeq (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g)
        (.c (listT [(Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id))).tree]))
        (oneTm C (C.key (G.hold0 M.np id, id)) id))
      (ifTm (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g) (oneTm C (C.key (G.hold1 M.np id, id)) id))
    have h6 := cost_ifTm hst hnm hdc (tab.kcur id) d1 (.ifeq (C.nm (.slp (tab.kgrp (G.hold0 M.np id)))) (gt g)
      (.ifeq (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g)
        (.c (listT [(Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id))).tree]))
        (oneTm C (C.key (G.hold0 M.np id, id)) id))
      (ifTm (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g) (oneTm C (C.key (G.hold1 M.np id, id)) id)))
    rw [e] at h4
    rw [endTm]
    omega
  · rw [endTm, expand_ifTm]
    split_ifs
    · simp only [Tm.expand]
      split_ifs
      · simp
      · exact (lone _).le
      · rw [expand_ifTm]
        split_ifs
        · exact (lone _).le
        · simp
    · simp

include hSl hCn hU0X hR

/-- **The cost of the templates.** -/
theorem cost_instTm (g : Fin mm) :
    (instTm C tab tg bT bub gt d1 gp g).cost (byPath C.nm st) ≤
      X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000) +
      X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500) +
      X * (2000 * Lc + 5000) + 1000 := by
  have hbase : ∀ p : Fin (K + K), (ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).cost
      (byPath C.nm st) + 62 * ((ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).expand
      (byPath C.nm st)).toList.length + 250 ≤ 3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000 := by
    intro p
    have h1 := cost_ifTm hst hnm hdc (tab.kgrp (Fin.castAdd A' p)) (gt g) (basesTm C p)
    have h2 := cost_basesTm hst hnm hdc hS hK2 p
    have h3 : ((ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).expand
        (byPath C.nm st)).toList.length ≤ X := by
      rw [expand_ifTm]
      split_ifs
      · simp only [basesTm, Tm.expand, expand_gN, hst.dg, dgT, NS1.Tree.toList, toList_listT, List.length_cons, List.length_map]
        have := List.length_filter_le (fun k : Fin U0 => decide (k.1 < (n p p).1)) (List.finRange U0)
        rw [List.length_finRange] at this
        omega
      · simp
    omega
  have hrole : ∀ r : M.R, (ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])).cost
      (byPath C.nm st) + 62 * ((ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])).expand
      (byPath C.nm st)).toList.length + 250 ≤
      X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500 := by
    intro r
    have h1 := cost_ifTm hst hnm hdc (tab.kgrp (M.rp r)) (gt g) (listTm [roleTm C tab tg d1 r])
    have h2 := cost_roleTm (tg := tg) (d1 := d1) hst hnm hdc hS hK2 hId hSl hCn r
    have h3 : (listTm [roleTm C tab tg d1 r]).cost (byPath C.nm st) = (roleTm C tab tg d1 r).cost (byPath C.nm st) + 120 := by
      rw [cost_listTm]
      simp
    have h4 : ((ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])).expand
        (byPath C.nm st)).toList.length ≤ 1 := by
      rw [expand_ifTm]
      split_ifs
      · rw [expand_listTm, toList_listT]
        simp
      · simp
    omega
  have hroles : (Grp.allRoles M).length ≤ X := by
    refine le_trans (le_of_eq ?_) hR
    rw [Grp.allRoles, List.length_flatMap]
    rw [Fintype.card_sigma]
    simp only [List.length_map, Finset.length_toList, Finset.card_univ]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  have h0 : ∀ l1 l2 l3 : List Tm, (catTm (l1 ++ l2 ++ l3)).cost (byPath C.nm st) =
      ((l1.map fun t => t.cost (byPath C.nm st) + 62 * (t.expand (byPath C.nm st)).toList.length + 250).sum +
      (l2.map fun t => t.cost (byPath C.nm st) + 62 * (t.expand (byPath C.nm st)).toList.length + 250).sum +
      (l3.map fun t => t.cost (byPath C.nm st) + 62 * (t.expand (byPath C.nm st)).toList.length + 250).sum) + 20 := by
    intro l1 l2 l3
    rw [cost_catTm, List.map_append, List.map_append, List.sum_append, List.sum_append]
  have h1 : (((List.finRange (K + K)).map fun p =>
      ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).map fun t => t.cost (byPath C.nm st) +
      62 * (t.expand (byPath C.nm st)).toList.length + 250).sum ≤
      X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000) := by
    rw [List.map_map]
    exact sum_map_le _ _ (fun p _ => hbase p) (by rw [List.length_finRange]; exact hK2)
  have h2 : (((Grp.allRoles M).map fun r => ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g)
      (listTm [roleTm C tab tg d1 r])).map fun t => t.cost (byPath C.nm st) +
      62 * (t.expand (byPath C.nm st)).toList.length + 250).sum ≤
      X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500) := by
    rw [List.map_map]
    exact sum_map_le _ _ (fun r _ => hrole r) hroles
  have h3 : (((G.allIds (K + K) U0 M.N U1).map (endTm C tab gt d1 g)).map fun t => t.cost (byPath C.nm st) +
      62 * (t.expand (byPath C.nm st)).toList.length + 250).sum ≤ X * (2000 * Lc + 5000) := by
    rw [List.map_map]
    refine sum_map_le _ _ (fun id _ => ?_) ?_
    · obtain ⟨a1, a2⟩ := cost_endTm (gt := gt) (d1 := d1) hst hnm hdc hS hK2 hId g id
      simp only [Function.comp_apply]
      omega
    · rw [G.allIds, Finset.length_toList, Finset.card_univ]; exact hId
  simp only [instTm, scriptTm, Tm.cost, h0]
  omega

end

end Nc.Dl
