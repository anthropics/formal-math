/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Script
import Nc.Dl.Names

/-!
# The size of a script
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Nc.Grp

theorem size_numT (k : ℕ) : (num k).size = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [num, Tree.size, ih]
    omega

theorem size_listT (l : List Tree) : (listT l).size = (l.map fun t => t.size + 1).sum + 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [listT, Tree.size, ih, List.map_cons, List.sum_cons]
    omega

theorem size_listT_le {l : List Tree} {s : ℕ} (h : ∀ t ∈ l, t.size ≤ s) :
    (listT l).size ≤ l.length * (s + 1) + 1 := by
  rw [size_listT]
  have := List.sum_le_card_nsmul (l.map fun t => t.size + 1) (s + 1) (by
    intro n hn
    rw [List.mem_map] at hn
    obtain ⟨t, ht, rfl⟩ := hn
    exact Nat.succ_le_succ (h t ht))
  rw [List.length_map, smul_eq_mul] at this
  omega

theorem size_listT_le' {l : List Tree} {s X : ℕ} (hl : l.length ≤ X) (h : ∀ t ∈ l, t.size ≤ s) :
    (listT l).size ≤ X * (s + 1) + 1 := by
  refine (size_listT_le h).trans ?_
  have := Nat.mul_le_mul_right (s + 1) hl
  omega

theorem size_keys {ks : List (List Bool)} {X Lc : ℕ} (hl : ks.length ≤ X) (h : ∀ k ∈ ks, k.length ≤ Lc) :
    (listT (ks.map ofBits)).size ≤ X * (4 * Lc + 2) + 1 := by
  refine size_listT_le' (s := 4 * Lc + 1) (by rw [List.length_map]; exact hl) ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  have h1 := size_ofBits k
  have h2 := h k hk
  omega

theorem size_keysT {l : List (List (List Bool))} {X Lc : ℕ} (hl : l.length ≤ X)
    (h : ∀ ks ∈ l, ks.length ≤ X ∧ ∀ k ∈ ks, k.length ≤ Lc) :
    (keysT l).size ≤ X * (X * (4 * Lc + 2) + 2) + 1 := by
  refine size_listT_le' (s := X * (4 * Lc + 2) + 1) (by rw [List.length_map]; exact hl) ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨ks, hks, rfl⟩ := ht
  exact size_keys (h ks hks).1 (h ks hks).2

/-- The size of a body. -/
theorem size_body {B : Body} {X Lc : ℕ} (h1 : B.flags.length ≤ X)
    (h2 : ∀ l ∈ B.flags, l.length ≤ X ∧ ∀ k ∈ l, k ≤ 2) (h3 : B.kR.length ≤ X)
    (h4 : ∀ ks ∈ B.kR, ks.length ≤ X ∧ ∀ k ∈ ks, k.length ≤ Lc) (h5 : B.kC.length ≤ X)
    (h6 : ∀ ks ∈ B.kC, ks.length ≤ X ∧ ∀ k ∈ ks, k.length ≤ Lc) :
    B.tree.size ≤ X * X * (8 * Lc + 10) + 6 * X + 5 := by
  have e1 : (listT (B.flags.map fun l => listT (l.map num))).size ≤ X * (X * 6 + 1 + 1) + 1 := by
    refine size_listT_le' (by rw [List.length_map]; exact h1) ?_
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨l, hl, rfl⟩ := ht
    refine size_listT_le' (s := 5) (by rw [List.length_map]; exact (h2 l hl).1) ?_
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    rw [size_numT]
    have := (h2 l hl).2 k hk
    omega
  have e2 := size_keysT h3 h4
  have e3 := size_keysT h5 h6
  simp only [Body.tree, Tree.size]
  have e4 : X * (X * (4 * Lc + 2) + 2) = X * X * (4 * Lc + 2) + 2 * X := by ring
  have e5 : X * (X * 6 + 1 + 1) = X * X * 6 + 2 * X := by ring
  have e6 : X * X * (8 * Lc + 10) = X * X * 6 + 2 * (X * X * (4 * Lc + 2)) := by ring
  omega

section script

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c : ℕ} {Gr : Type} [DecidableEq Gr]

variable {qn : Q → ℕ} {cb : Option Γ → Fin c → Bool} {M : Sys F (K + K + A') E} {P : G.Plan M U0 U1}
  {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
  {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {dkey : Fin (K + K) × Fin U0 → List Bool} {tg : M.R → ℕ} {X Lc : ℕ}

theorem rowFlag_le {A : ℕ} (d : RowData A) (b : Fin A) : rowFlag d b ≤ 2 := by
  unfold rowFlag
  split_ifs <;> omega

theorem size_bodyOf (hK : K + K ≤ X) (hU0 : U0 ≤ X) (hS : Fintype.card (Option S) ≤ X)
    (hkey : ∀ a, (key a).length ≤ Lc) (hdkey : ∀ a, (dkey a).length ≤ Lc) (p : Fin (K + K)) :
    (bodyOf ρ n key dkey p).tree.size ≤ X * X * (8 * Lc + 10) + 6 * X + 5 := by
  have hf : ∀ f : Fin U0 → Bool, ((List.finRange U0).filter f).length ≤ X := fun f => by
    refine (List.length_filter_le _ _).trans ?_
    rw [List.length_finRange]
    exact hU0
  refine size_body ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [bodyOf, List.length_map, Finset.length_toList, card_univ]
    exact hS
  · intro l hl
    simp only [bodyOf, List.mem_map] at hl
    obtain ⟨s, -, rfl⟩ := hl
    refine ⟨by simpa using hK, fun k hk => ?_⟩
    rw [List.mem_reverse, List.mem_ofFn] at hk
    obtain ⟨b, rfl⟩ := hk
    exact rowFlag_le _ _
  · simpa [bodyOf] using hK
  · intro ks hks
    simp only [bodyOf, List.mem_ofFn] at hks
    obtain ⟨b, rfl⟩ := hks
    refine ⟨by rw [List.length_map]; exact hf _, fun k hk => ?_⟩
    rw [List.mem_map] at hk
    obtain ⟨i, -, rfl⟩ := hk
    exact hkey _
  · simpa [bodyOf] using hK
  · intro ks hks
    simp only [bodyOf, List.mem_ofFn] at hks
    obtain ⟨b, rfl⟩ := hks
    refine ⟨by rw [List.length_map]; exact hf _, fun k hk => ?_⟩
    rw [List.mem_map] at hk
    obtain ⟨i, -, rfl⟩ := hk
    split_ifs
    · exact hdkey _
    · exact hkey _

/-- The number of letters of an input party. -/
def plen (x : Fin K → List Γ) (p : Fin (K + K)) : ℕ :=
  Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun κ => (x κ).length) p

theorem size_baseIns (hK : K + K ≤ X) (hU0 : U0 ≤ X) (hS : Fintype.card (Option S) ≤ X)
    (hkey : ∀ a, (key a).length ≤ Lc) (hdkey : ∀ a, (dkey a).length ≤ Lc) (hqn : ∀ a, qn a ≤ X)
    (p : Fin (K + K)) :
    (((baseIns qn cb q x ρ n key dkey p).map Ins.tree).map fun t => t.size + 1).sum ≤
      X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10) + plen x p * (4 * c + 2) := by
  have hboth : ((((List.finRange U0).filter fun k => k.1 < (n p p).1).map fun k =>
      (Ins.both (key (Fin.castAdd A' p, .init p p k)) (dkey (p, k))).tree.size + 1)).sum ≤ X * (8 * Lc + 10) := by
    refine (List.sum_le_card_nsmul _ (8 * Lc + 10) ?_).trans ?_
    · intro m hm
      rw [List.mem_map] at hm
      obtain ⟨k, -, rfl⟩ := hm
      have h1 := size_ofBits (key (Fin.castAdd A' p, .init p p k))
      have h2 := size_ofBits (dkey (p, k))
      have h3 := hkey (Fin.castAdd A' p, .init p p k)
      have h4 := hdkey (p, k)
      simp only [Ins.tree, Tree.size, size_numT]
      omega
    · rw [List.length_map, smul_eq_mul]
      refine Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans ?_)
      rw [List.length_finRange]
      exact hU0
  rw [baseIns, List.map_cons, List.map_cons, List.sum_cons, List.map_map, List.map_map]
  have hb := hboth
  have hsum : ((((List.finRange U0).filter fun k => k.1 < (n p p).1).map
      ((fun t : Tree => t.size + 1) ∘ Ins.tree ∘ fun k =>
        Ins.both (key (Fin.castAdd A' p, .init p p k)) (dkey (p, k))))).sum ≤ X * (8 * Lc + 10) := hb
  have hhead : (Fin.addCases (motive := fun _ => Ins)
      (fun κ => .block (qn (q κ.castSucc)) (qn (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
      (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ)))
        p).tree.size + 1 ≤ X * X * (8 * Lc + 10) + 10 * X + 12 + plen x p * (4 * c + 2) := by
    unfold plen
    refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
    · rw [Fin.addCases_left, Fin.addCases_left]
      have h1 := size_bodyOf (ρ := ρ) (n := n) hK hU0 hS hkey hdkey (Fin.castAdd K κ)
      have h2 := hqn (q κ.castSucc)
      have h3 := hqn (q κ.succ)
      simp only [Ins.tree, Tree.size, size_numT]
      omega
    · rw [Fin.addCases_right, Fin.addCases_right]
      have h1 := size_bodyOf (ρ := ρ) (n := n) hK hU0 hS hkey hdkey (Fin.natAdd K κ)
      have h2 : (listT ((((x κ).map fun a => List.ofFn (cb (some a))).reverse).map ofBits)).size ≤
          (x κ).length * (4 * c + 1 + 1) + 1 := by
        refine size_listT_le' (by simp) ?_
        intro t ht
        rw [List.mem_map] at ht
        obtain ⟨w, hw, rfl⟩ := ht
        rw [List.mem_reverse, List.mem_map] at hw
        obtain ⟨a, -, rfl⟩ := hw
        have := size_ofBits (List.ofFn (cb (some a)))
        rw [List.length_ofFn] at this
        exact this
      have e : (x κ).length * (4 * c + 1 + 1) = (x κ).length * (4 * c + 2) := by ring
      simp only [Ins.tree, Tree.size, size_numT]
      omega
  refine le_trans (Nat.add_le_add hhead hsum) ?_
  omega

theorem size_roleIns (hU : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X) (hU1 : U1 ≤ X)
    (hSl : ∀ y, Fintype.card (M.kind y).Sl ≤ X) (hCn : ∀ y, Fintype.card (M.kind y).Cn ≤ X)
    (hkey : ∀ a, (key a).length ≤ Lc) (htg : ∀ r, tg r ≤ X) (hnum : ∀ y, P.num n o y ≤ X) (r : M.R) :
    (roleIns P n o key tg r).tree.size ≤ X * X * (8 * Lc + 4) + 8 * X + 15 := by
  classical
  have h1 : (keysT ((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e =>
      ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse)).size ≤
      X * (X * (4 * Lc + 2) + 2) + 1 := by
    refine size_keysT ?_ ?_
    · rw [List.length_map, Finset.length_toList, card_univ]
      exact (Fintype.card_subtype_le _).trans (hSl _)
    · intro ks hks
      rw [List.mem_map] at hks
      obtain ⟨e, -, rfl⟩ := hks
      refine ⟨?_, fun k hk => ?_⟩
      · rw [List.length_reverse, List.length_map, G.Plan.ids]
        refine (List.length_filter_le _ _).trans ?_
        rw [G.allIds, Finset.length_toList, card_univ]
        exact hU
      · rw [List.mem_reverse, List.mem_map] at hk
        obtain ⟨id, -, rfl⟩ := hk
        exact hkey _
  have h2 : (keysT ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k =>
        key (M.rp r, .new ⟨r.1, ν.1⟩ k))).size ≤ X * (X * (4 * Lc + 2) + 2) + 1 := by
    refine size_keysT ?_ ?_
    · rw [List.length_map, Finset.length_toList, card_univ]
      exact (Fintype.card_subtype_le _).trans (hCn _)
    · intro ks hks
      rw [List.mem_map] at hks
      obtain ⟨ν, -, rfl⟩ := hks
      refine ⟨?_, fun k hk => ?_⟩
      · rw [List.length_map]
        refine (List.length_filter_le _ _).trans ?_
        rw [List.length_finRange]
        exact hU1
      · rw [List.mem_map] at hk
        obtain ⟨i, -, rfl⟩ := hk
        exact hkey _
  have h3 := htg r
  have h4 := hnum r.1
  have e : X * (X * (4 * Lc + 2) + 2) = X * X * (4 * Lc + 2) + 2 * X := by ring
  have e' : X * X * (8 * Lc + 4) = 2 * (X * X * (4 * Lc + 2)) := by ring
  simp only [roleIns, Ins.tree, Tree.size, size_numT]
  omega

/-- The units that are cut and have a holder in the group. -/
noncomputable def cutAt (P : G.Plan M U0 U1) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.N → Fin U1)
    (grp : Fin (K + K + A') → Gr) (g : Gr) : Finset (G.Uid (K + K) U0 M.N U1) :=
  open Classical in
  univ.filter fun id => id ∈ P.cur n o E ∧ grp (G.hold0 M.np id) ≠ grp (G.hold1 M.np id) ∧
    (grp (G.hold0 M.np id) = g ∨ grp (G.hold1 M.np id) = g)

theorem length_uwBits_le (w : UW ub) : (uwBits w).length ≤ ub := by
  cases w with
  | none => exact Nat.zero_le _
  | some v => simp [uwBits]

theorem size_endIns (hU : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X) (hkey : ∀ a, (key a).length ≤ Lc)
    (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    (((endIns P n o grp g key b).map Ins.tree).map fun t => t.size + 1).sum ≤
      X * (8 * Lc + 12) + (cutAt P n o grp g).card * (4 * ub) := by
  classical
  have key1 : ∀ l : List (G.Uid (K + K) U0 M.N U1),
      ((((l.filter fun id => id ∈ P.cur n o E).filterMap fun id =>
        if grp (G.hold0 M.np id) = g then
          if grp (G.hold1 M.np id) = g then some (Ins.both (key (G.hold0 M.np id, id)) (key (G.hold1 M.np id, id)))
          else some (.one (key (G.hold0 M.np id, id)) (uwBits (b id)))
        else if grp (G.hold1 M.np id) = g then some (.one (key (G.hold1 M.np id, id)) (uwBits (b id)))
        else none).map Ins.tree).map fun t => t.size + 1).sum ≤
      l.length * (8 * Lc + 12) + (l.map fun id => if id ∈ cutAt P n o grp g then 4 * ub else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons id l ih =>
      rw [List.length_cons, List.map_cons, List.sum_cons]
      have e0 : (l.length + 1) * (8 * Lc + 12) = l.length * (8 * Lc + 12) + (8 * Lc + 12) := by ring
      by_cases hc : id ∈ P.cur n o E
      · rw [List.filter_cons_of_pos (by simpa using hc), List.filterMap_cons]
        have k0 := hkey (G.hold0 M.np id, id)
        have k1 := hkey (G.hold1 M.np id, id)
        have s0 := size_ofBits (key (G.hold0 M.np id, id))
        have s1 := size_ofBits (key (G.hold1 M.np id, id))
        have sw := size_ofBits (uwBits (b id))
        have lw := length_uwBits_le (b id)
        by_cases h0 : grp (G.hold0 M.np id) = g
        · by_cases h1 : grp (G.hold1 M.np id) = g
          · simp only [h0, h1, if_true, List.map_cons, List.sum_cons, Ins.tree, Tree.size, size_numT]
            omega
          · have hcut : id ∈ cutAt P n o grp g := by
              refine mem_filter.2 ⟨mem_univ _, hc, ?_, Or.inl h0⟩
              rw [h0]
              exact fun h => h1 h.symm
            simp only [h0, h1, if_true, if_false, List.map_cons, List.sum_cons, Ins.tree, Tree.size, size_numT,
              if_pos hcut]
            omega
        · by_cases h1 : grp (G.hold1 M.np id) = g
          · have hcut : id ∈ cutAt P n o grp g := by
              refine mem_filter.2 ⟨mem_univ _, hc, ?_, Or.inr h1⟩
              rw [h1]
              exact h0
            simp only [h0, h1, if_true, if_false, List.map_cons, List.sum_cons, Ins.tree, Tree.size, size_numT,
              if_pos hcut]
            omega
          · simp only [h0, h1, if_false]
            omega
      · rw [List.filter_cons_of_neg (by simpa using hc)]
        omega
  have h1 := key1 (G.allIds (K + K) U0 M.N U1)
  have h2 : (G.allIds (K + K) U0 M.N U1).length ≤ X := by
    rw [G.allIds, Finset.length_toList, card_univ]
    exact hU
  have h3 : ((G.allIds (K + K) U0 M.N U1).map fun id => if id ∈ cutAt P n o grp g then 4 * ub else 0).sum =
      (cutAt P n o grp g).card * (4 * ub) := by
    rw [G.allIds, Finset.sum_map_toList, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
  have h4 := Nat.mul_le_mul_right (8 * Lc + 12) h2
  rw [endIns]
  omega

/-- **The size of a script.** -/
theorem size_scriptT (hX : 1 ≤ X) (hLc : 1 ≤ Lc) (hK : K + K ≤ X) (hU0 : U0 ≤ X) (hU1 : U1 ≤ X)
    (hS : Fintype.card (Option S) ≤ X) (hU : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X)
    (hR : Fintype.card M.R ≤ X) (hSl : ∀ y, Fintype.card (M.kind y).Sl ≤ X)
    (hCn : ∀ y, Fintype.card (M.kind y).Cn ≤ X) (hkey : ∀ a, (key a).length ≤ Lc)
    (hdkey : ∀ a, (dkey a).length ≤ Lc) (hqn : ∀ a, qn a ≤ X) (htg : ∀ r, tg r ≤ X)
    (hnum : ∀ y, P.num n o y ≤ X) {bT bub : List Bool} (hbT : bT.length ≤ Lc) (hbub : bub.length ≤ Lc)
    (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    (scriptT bT bub (script qn cb P q x ρ n o grp g key dkey tg b)).size ≤ 200 * X ^ 3 * Lc +
      (∑ κ ∈ univ.filter (fun κ : Fin K => grp (Fin.castAdd A' (Fin.natAdd K κ)) = g), (x κ).length) * (4 * c + 2) +
      (cutAt P n o grp g).card * (4 * ub) := by
  classical
  -- base parties
  have h1 : ((((baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey)).map Ins.tree).map
      fun t => t.size + 1).sum ≤ X * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
      (∑ κ ∈ univ.filter (fun κ : Fin K => grp (Fin.castAdd A' (Fin.natAdd K κ)) = g), (x κ).length) * (4 * c + 2) := by
    have e1 : ∀ l : List (Fin (K + K)), (((l.flatMap (baseIns qn cb q x ρ n key dkey)).map Ins.tree).map
        fun t => t.size + 1).sum ≤ l.length * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
        (l.map (plen x)).sum * (4 * c + 2) := by
      intro l
      induction l with
      | nil => simp
      | cons p l ih =>
        rw [List.flatMap_cons, List.map_append, List.map_append, List.sum_append, List.length_cons, List.map_cons,
          List.sum_cons]
        have h2 := size_baseIns (cb := cb) (q := q) (x := x) (ρ := ρ) (n := n) hK hU0 hS hkey hdkey hqn p
        have e2 : (l.length + 1) * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) =
          l.length * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
            (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) := by ring
        have e3 : (plen x p + (l.map (plen x)).sum) * (4 * c + 2) =
          plen x p * (4 * c + 2) + (l.map (plen x)).sum * (4 * c + 2) := by ring
        omega
    refine (e1 _).trans (Nat.add_le_add (Nat.mul_le_mul_right _ ?_) (Nat.mul_le_mul_right _ (le_of_eq ?_)))
    · rw [baseList]
      refine (List.length_filter_le _ _).trans ?_
      rw [List.length_finRange]
      exact hK
    · have e2 : ((baseList (A' := A') grp g).map (plen x)).sum =
          ∑ p ∈ univ.filter (fun p : Fin (K + K) => grp (Fin.castAdd A' p) = g), plen x p := by
        rw [← List.sum_toFinset _ nodup_baseList]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext p
        simp [mem_baseList]
      rw [e2, Finset.sum_filter, Fin.sum_univ_add, Finset.sum_filter]
      have e3 : ∀ κ : Fin K, plen x (Fin.castAdd K κ) = 0 := fun κ => Fin.addCases_left _
      have e4 : ∀ κ : Fin K, plen x (Fin.natAdd K κ) = (x κ).length := fun κ => Fin.addCases_right _
      simp only [e3, e4, ite_self, Finset.sum_const_zero, zero_add]
  -- roles
  have h2 : ((((roleList grp g M).map (roleIns P n o key tg)).map Ins.tree).map fun t => t.size + 1).sum ≤
      X * (X * X * (8 * Lc + 4) + 8 * X + 16) := by
    refine (List.sum_le_card_nsmul _ (X * X * (8 * Lc + 4) + 8 * X + 16) ?_).trans ?_
    · intro m hm
      rw [List.mem_map] at hm
      obtain ⟨t, ht, rfl⟩ := hm
      rw [List.mem_map] at ht
      obtain ⟨i, hi, rfl⟩ := ht
      rw [List.mem_map] at hi
      obtain ⟨r, -, rfl⟩ := hi
      have := size_roleIns (key := key) (tg := tg) (P := P) (n := n) (o := o) hU hU1 hSl hCn hkey htg hnum r
      omega
    · rw [List.length_map, List.length_map, List.length_map, smul_eq_mul]
      refine Nat.mul_le_mul_right _ ?_
      rw [roleList]
      refine (List.length_filter_le _ _).trans ?_
      have hnd : (allRoles M).Nodup := pairwise_allRoles.imp fun h => h.1
      rw [← List.toFinset_card_of_nodup hnd]
      exact (card_le_univ _).trans hR
  have h3 := size_endIns (P := P) (n := n) (o := o) (grp := grp) (g := g) (key := key) hU hkey b
  have hT := size_ofBits bT
  have hub := size_ofBits bub
  rw [scriptT, script]
  simp only [Tree.size]
  rw [size_listT, List.map_append, List.map_append, List.map_append, List.map_append, List.sum_append,
    List.sum_append]
  have f1 : X * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
      X * (X * X * (8 * Lc + 4) + 8 * X + 16) + X * (8 * Lc + 12) + 8 * Lc + 6 ≤ 200 * X ^ 3 * Lc := by
    have g1 : X ≤ X ^ 3 * Lc := by
      calc X = X ^ 1 * 1 := by ring
        _ ≤ X ^ 3 * Lc := Nat.mul_le_mul (Nat.pow_le_pow_right hX (by omega)) hLc
    have g2 : X ^ 2 ≤ X ^ 3 * Lc := by
      calc X ^ 2 = X ^ 2 * 1 := by ring
        _ ≤ X ^ 3 * Lc := Nat.mul_le_mul (Nat.pow_le_pow_right hX (by omega)) hLc
    have g3 : X ^ 3 ≤ X ^ 3 * Lc := Nat.le_mul_of_pos_right _ hLc
    have g4 : X ^ 2 * Lc ≤ X ^ 3 * Lc := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hX (by omega))
    have g5 : X * Lc ≤ X ^ 3 * Lc := by
      calc X * Lc = X ^ 1 * Lc := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hX (by omega))
    have g6 : Lc ≤ X ^ 3 * Lc := Nat.le_mul_of_pos_left _ (by positivity)
    have g7 : 1 ≤ X ^ 3 * Lc := Nat.one_le_iff_ne_zero.2 (by positivity)
    have e : X * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
      X * (X * X * (8 * Lc + 4) + 8 * X + 16) + X * (8 * Lc + 12) + 8 * Lc + 6 =
      16 * (X ^ 3 * Lc) + 14 * X ^ 3 + 28 * X ^ 2 + 8 * (X ^ 2 * Lc) + 40 * X + 8 * (X * Lc) + 8 * Lc + 6 := by ring
    rw [e, mul_assoc]
    omega
  omega

end script

end Nc.Dl
