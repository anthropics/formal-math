/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Slp0

/-!
# The paper, proof of Proposition prop:pieces: heavy nodes and pieces

A rooted tree by stages with two weights at every node: "Call a node of the tree heavy if it is the root or if
#(given nodes below)/(4M) + #(units below)/(2Ŷ) > 1/k ... A piece is a heavy node, or the subtree of a light node with
a heavy parent." A node is below itself, and the units below a node are counted at their lower ends.
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset

/-- A tree by stages on the nodes 0, ..., P − 1. -/
structure Staged (P : ℕ) where
  /-- the parent -/
  par : Fin P → Fin P
  /-- the stage -/
  stage : Fin P → ℕ
  /-- the stage of the root -/
  depth : ℕ
  /-- the root -/
  root : Fin P
  stage_le : ∀ p, stage p ≤ depth
  stage_root : ∀ p, stage p = depth ↔ p = root
  stage_par : ∀ p, p ≠ root → stage (par p) = stage p + 1

namespace Staged

variable {P : ℕ} (T : Staged P)

/-- One step up, resting at the root. -/
def nxt (p : Fin P) : Fin P := if p = T.root then p else T.par p

/-- The node q is below p. -/
def Below (q p : Fin P) : Prop := T.stage q ≤ T.stage p ∧ T.nxt^[T.stage p - T.stage q] q = p

open Classical in
/-- The sum over the nodes below. -/
noncomputable def below (f : Fin P → ℕ) (p : Fin P) : ℕ := ∑ q, if T.Below q p then f q else 0

/-- The sum over the children. -/
def kids (f : Fin P → ℕ) (p : Fin P) : ℕ := ∑ q ∈ univ.filter (fun q => q ≠ T.root ∧ T.par q = p), f q

variable (giv u : Fin P → ℕ) (M Y k : ℕ)

/-- Heavy nodes. -/
def Heavy (p : Fin P) : Prop :=
  p = T.root ∨ 8 * M * Y < k * (T.below giv p * (2 * Y) + T.below u p * (4 * M))

/-- Heads of pieces: heavy nodes, and light nodes with a heavy parent. -/
def Head (p : Fin P) : Prop := p = T.root ∨ T.Heavy giv u M Y k (T.par p)

open Classical in
/-- The head above a node, at most d steps up. -/
noncomputable def top : ℕ → Fin P → Fin P
  | 0, p => p
  | d + 1, p => if T.Head giv u M Y k p then p else top d (T.par p)

/-- The head of the piece of a node. -/
noncomputable def hd (p : Fin P) : Fin P := T.top giv u M Y k (T.depth - T.stage p) p

open Classical in
/-- The number of a head. -/
noncomputable def rank (p : Fin P) : ℕ := (univ.filter fun q => T.Head giv u M Y k q ∧ q < p).card

/-- The piece of a node. -/
noncomputable def piece (p : Fin P) : ℕ := T.rank giv u M Y k (T.hd giv u M Y k p)

variable {T giv u M Y k}

theorem below_refl (p : Fin P) : T.Below p p := ⟨le_rfl, by rw [Nat.sub_self]; rfl⟩

theorem stage_lt {p : Fin P} (hp : p ≠ T.root) : T.stage p < T.depth :=
  lt_of_le_of_ne (T.stage_le p) fun e => hp ((T.stage_root p).1 e)

theorem below_up {q p : Fin P} (h : T.Below q p) (hp : p ≠ T.root) : T.Below q (T.par p) := by
  refine ⟨by rw [T.stage_par p hp]; exact Nat.le_succ_of_le h.1, ?_⟩
  rw [T.stage_par p hp, Nat.succ_sub h.1, Function.iterate_succ_apply', h.2, nxt, if_neg hp]

theorem below_down {q p : Fin P} (hq : q ≠ T.root) (h : T.Below (T.par q) p) : T.Below q p := by
  have h1 := h.1
  have h2 := h.2
  rw [T.stage_par q hq] at h1 h2
  refine ⟨by omega, ?_⟩
  have e : T.stage p - T.stage q = T.stage p - (T.stage q + 1) + 1 := by omega
  rw [e, Function.iterate_succ_apply]
  rwa [show T.nxt q = T.par q from if_neg hq]

open Classical in
theorem below_mono (f : Fin P → ℕ) {p : Fin P} (hp : p ≠ T.root) : T.below f p ≤ T.below f (T.par p) :=
  Finset.sum_le_sum fun q _ => by
    by_cases h : T.Below q p
    · rw [if_pos h, if_pos (below_up h hp)]
    · rw [if_neg h]
      exact Nat.zero_le _

open Classical in
/-- "The sets below different nodes of one stage are disjoint." -/
theorem below_stage (f : Fin P → ℕ) (s : ℕ) :
    ∑ p ∈ univ.filter (fun p => T.stage p = s), T.below f p ≤ ∑ q, f q := by
  unfold below
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  refine le_trans (Nat.mul_le_mul_right _ (card_le_one.2 fun p hp p' hp' => ?_)) (le_of_eq (one_mul _))
  obtain ⟨h1, h2⟩ := mem_filter.1 hp
  obtain ⟨h1', h2'⟩ := mem_filter.1 hp'
  rw [← h2.2, ← h2'.2, (mem_filter.1 h1).2, (mem_filter.1 h1').2]

open Classical in
theorem below_kids (f : Fin P → ℕ) (p : Fin P) : T.below (T.kids f) p ≤ T.below f p := by
  have h1 : T.below (T.kids f) p = ∑ q ∈ univ.filter (fun q => q ≠ T.root), if T.Below (T.par q) p then f q else 0 := by
    have h2 : ∀ a, (if T.Below a p then T.kids f a else 0) =
        ∑ q ∈ univ.filter (fun q => q ≠ T.root), if T.par q = a then (if T.Below a p then f q else 0) else 0 := by
      intro a
      unfold kids
      rw [← Finset.sum_filter, Finset.filter_filter]
      split_ifs
      · rfl
      · simp
    unfold below
    rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_ite_eq, if_pos (mem_univ _)]
  rw [h1]
  refine (Finset.sum_le_sum fun q hq => ?_).trans (Finset.sum_le_sum_of_subset (subset_univ _))
  by_cases h : T.Below (T.par q) p
  · rw [if_pos h, if_pos (below_down (mem_filter.1 hq).2 h)]
  · rw [if_neg h]
    exact Nat.zero_le _

open Classical in
/-- "As the sets below different nodes of one stage are disjoint, each stage has fewer than k heavy nodes." -/
theorem _root_.Paper.prop_pieces_heavy_few (hk : 0 < k) (hM : 0 < M) (hY : 0 < Y) (hg : ∑ q, giv q ≤ M) (hu : ∑ q, u q ≤ Y)
    {s : ℕ} (hs : s < T.depth) :
    (univ.filter fun p => T.stage p = s ∧ T.Heavy giv u M Y k p).card < k := by
  by_contra hcon
  push Not at hcon
  set S := univ.filter fun p => T.stage p = s ∧ T.Heavy giv u M Y k p
  have hw : ∀ p ∈ S, 8 * M * Y + 1 ≤ k * (T.below giv p * (2 * Y) + T.below u p * (4 * M)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := (mem_filter.1 hp).2
    rcases h2 with h2 | h2
    · rw [(T.stage_root p).2 h2] at h1
      omega
    · exact h2
  have h3 : ∑ p ∈ S, (T.below giv p * (2 * Y) + T.below u p * (4 * M)) ≤ M * (2 * Y) + Y * (4 * M) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    have hsub : S ⊆ univ.filter fun p => T.stage p = s := fun p hp => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hp).2.1⟩
    exact Nat.add_le_add
      (Nat.mul_le_mul_right _ (((Finset.sum_le_sum_of_subset hsub).trans (below_stage _ s)).trans hg))
      (Nat.mul_le_mul_right _ (((Finset.sum_le_sum_of_subset hsub).trans (below_stage _ s)).trans hu))
  have h4 : k * (8 * M * Y + 1) ≤ k * (M * (2 * Y) + Y * (4 * M)) := by
    refine le_trans (Nat.mul_le_mul_right _ hcon) ?_
    calc S.card * (8 * M * Y + 1) = ∑ _p ∈ S, (8 * M * Y + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ p ∈ S, k * (T.below giv p * (2 * Y) + T.below u p * (4 * M)) := Finset.sum_le_sum hw
      _ ≤ _ := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ h3
  have h5 := Nat.le_of_mul_le_mul_left h4 hk
  nlinarith

/-- "Parents of heavy nodes are heavy." -/
theorem _root_.Paper.prop_pieces_heavy_up {p : Fin P} (hp : p ≠ T.root) (h : T.Heavy giv u M Y k p) :
    T.Heavy giv u M Y k (T.par p) := by
  refine Or.inr (lt_of_lt_of_le (h.resolve_left hp) (Nat.mul_le_mul_left _ ?_))
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (below_mono _ hp)) (Nat.mul_le_mul_right _ (below_mono _ hp))

theorem head_of_heavy {p : Fin P} (h : T.Heavy giv u M Y k p) : T.Head giv u M Y k p := by
  by_cases hp : p = T.root
  · exact Or.inl hp
  · exact Or.inr (prop_pieces_heavy_up hp h)

theorem top_spec : ∀ d p, T.stage p + d = T.depth → T.Head giv u M Y k (T.top giv u M Y k d p) ∧
    T.Below p (T.top giv u M Y k d p) ∧
    (T.top giv u M Y k d p = p ∨ ¬ T.Heavy giv u M Y k (T.top giv u M Y k d p)) := by
  intro d
  induction d with
  | zero => exact fun p hp => ⟨Or.inl ((T.stage_root p).1 hp), below_refl p, Or.inl rfl⟩
  | succ d ih =>
    intro p hp
    rw [top]
    by_cases h : T.Head giv u M Y k p
    · rw [if_pos h]
      exact ⟨h, below_refl p, Or.inl rfl⟩
    · rw [if_neg h]
      have hr : p ≠ T.root := fun e => h (Or.inl e)
      obtain ⟨a1, a2, a3⟩ := ih (T.par p) (by rw [T.stage_par p hr]; omega)
      refine ⟨a1, below_down hr a2, Or.inr ?_⟩
      rcases a3 with a3 | a3
      · rw [a3]
        exact fun e => h (Or.inr e)
      · exact a3

theorem hd_spec (p : Fin P) : T.Head giv u M Y k (T.hd giv u M Y k p) ∧ T.Below p (T.hd giv u M Y k p) ∧
    (T.hd giv u M Y k p = p ∨ ¬ T.Heavy giv u M Y k (T.hd giv u M Y k p)) :=
  top_spec _ p (by have := T.stage_le p; omega)

theorem hd_head {p : Fin P} (h : T.Head giv u M Y k p) : T.hd giv u M Y k p = p := by
  unfold hd
  generalize T.depth - T.stage p = d
  cases d with
  | zero => rfl
  | succ d => rw [top, if_pos h]

theorem hd_par {p : Fin P} (h : ¬ T.Head giv u M Y k p) : T.hd giv u M Y k p = T.hd giv u M Y k (T.par p) := by
  have hr : p ≠ T.root := fun e => h (Or.inl e)
  unfold hd
  have hlt := stage_lt hr
  rw [T.stage_par p hr, show T.depth - T.stage p = T.depth - (T.stage p + 1) + 1 by omega, top, if_neg h]

theorem rank_inj {p q : Fin P} (hp : T.Head giv u M Y k p) (hq : T.Head giv u M Y k q)
    (e : T.rank giv u M Y k p = T.rank giv u M Y k q) : p = q := by
  classical
  have key : ∀ {x y : Fin P}, T.Head giv u M Y k x → x < y → T.rank giv u M Y k x < T.rank giv u M Y k y := by
    intro x y hx hxy
    refine card_lt_card ((ssubset_iff_of_subset ?_).2
      ⟨x, mem_filter.2 ⟨mem_univ _, hx, hxy⟩, fun hc => lt_irrefl _ (mem_filter.1 hc).2.2⟩)
    intro z hz
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 hz
    exact mem_filter.2 ⟨h1, h2, h3.trans hxy⟩
  rcases lt_trichotomy p q with h | h | h
  · have := key hp h
    omega
  · exact h
  · have := key hq h
    omega

theorem piece_hd {p q : Fin P} (e : T.piece giv u M Y k p = T.piece giv u M Y k q) :
    T.hd giv u M Y k p = T.hd giv u M Y k q := rank_inj (hd_spec p).1 (hd_spec q).1 e

theorem piece_head {p : Fin P} (h : T.Head giv u M Y k p) : T.piece giv u M Y k p = T.rank giv u M Y k p := by
  rw [piece, hd_head h]

theorem below_subtree {x : Fin P} (hx : ¬ T.Heavy giv u M Y k x) :
    ∀ d p, T.Below p x → T.stage x = T.stage p + d → T.hd giv u M Y k p = T.hd giv u M Y k x := by
  intro d
  induction d with
  | zero =>
    intro p hp hd
    obtain ⟨-, h2⟩ := hp
    rw [Nat.add_zero] at hd
    rw [hd, Nat.sub_self] at h2
    rw [show p = x from h2]
  | succ d ih =>
    intro p hp hd
    have hr : p ≠ T.root := fun e => by
      have h1 := (T.stage_root p).2 e
      have h2 := T.stage_le x
      omega
    have hpar : T.Below (T.par p) x := by
      obtain ⟨-, h2⟩ := hp
      refine ⟨by rw [T.stage_par p hr]; omega, ?_⟩
      rw [show T.stage x - T.stage p = d + 1 by omega, Function.iterate_succ_apply,
        show T.nxt p = T.par p from if_neg hr] at h2
      rw [T.stage_par p hr, show T.stage x - (T.stage p + 1) = d by omega]
      exact h2
    have hnh : ∀ e q, T.Below q x → T.stage x = T.stage q + e → ¬ T.Heavy giv u M Y k q := by
      intro e
      induction e with
      | zero =>
        intro q hq he
        obtain ⟨-, h2⟩ := hq
        rw [Nat.add_zero] at he
        rw [he, Nat.sub_self] at h2
        rwa [show q = x from h2]
      | succ e ih' =>
        intro q hq he hh
        have hq' : q ≠ T.root := fun e' => by
          have h1 := (T.stage_root q).2 e'
          have h2 := T.stage_le x
          omega
        refine ih' (T.par q) ?_ (by rw [T.stage_par q hq']; omega) (prop_pieces_heavy_up hq' hh)
        obtain ⟨-, h2⟩ := hq
        refine ⟨by rw [T.stage_par q hq']; omega, ?_⟩
        rw [show T.stage x - T.stage q = e + 1 by omega, Function.iterate_succ_apply,
          show T.nxt q = T.par q from if_neg hq'] at h2
        rw [T.stage_par q hq', show T.stage x - (T.stage q + 1) = e by omega]
        exact h2
    have hp' : ¬ T.Head giv u M Y k p := fun e =>
      hnh d (T.par p) hpar (by rw [T.stage_par p hr]; omega) (e.resolve_left hr)
    rw [hd_par hp']
    exact ih (T.par p) hpar (by rw [T.stage_par p hr]; omega)

open Classical in
/-- "A piece is a heavy node, or the subtree of a light node with a heavy parent": the head x of the piece g is a heavy
node and is the whole piece, or it is light with a heavy parent and the piece is exactly the set below it. -/
theorem _root_.Paper.prop_pieces_shape (g : ℕ) (hne : ∃ p, T.piece giv u M Y k p = g) :
    ∃ x, (T.Heavy giv u M Y k x ∧ ∀ p, T.piece giv u M Y k p = g ↔ p = x) ∨
      (¬ T.Heavy giv u M Y k x ∧ T.Heavy giv u M Y k (T.par x) ∧ ∀ p, T.piece giv u M Y k p = g ↔ T.Below p x) := by
  obtain ⟨p0, hp0⟩ := hne
  have hs := hd_spec (T := T) (giv := giv) (u := u) (M := M) (Y := Y) (k := k) p0
  have hx : T.piece giv u M Y k (T.hd giv u M Y k p0) = g := by rw [piece_head hs.1]; exact hp0
  refine ⟨T.hd giv u M Y k p0, ?_⟩
  have he : ∀ p, T.piece giv u M Y k p = g → T.hd giv u M Y k p = T.hd giv u M Y k p0 :=
    fun p hp => piece_hd (hp.trans hp0.symm)
  by_cases hh : T.Heavy giv u M Y k (T.hd giv u M Y k p0)
  · refine Or.inl ⟨hh, fun p => ⟨fun hp => ?_, fun e => e ▸ hx⟩⟩
    rcases (hd_spec (T := T) (giv := giv) (u := u) (M := M) (Y := Y) (k := k) p).2.2 with h | h
    · exact h.symm.trans (he p hp)
    · exact absurd (he p hp ▸ hh) h
  · refine Or.inr ⟨hh, hs.1.resolve_left fun e => hh (Or.inl e), fun p => ⟨fun hp => he p hp ▸ (hd_spec p).2.1, fun hp => ?_⟩⟩
    rw [piece, below_subtree hh (T.stage (T.hd giv u M Y k p0) - T.stage p) p hp (by have := hp.1; omega)]
    exact hx

open Classical in
/-- A sum over a piece: one node, or the nodes below a light node. -/
theorem piece_sum_le (f : Fin P → ℕ) (B : ℕ) (hB : ∀ p, f p ≤ B)
    (hl : ∀ x, ¬ T.Heavy giv u M Y k x → T.below f x ≤ B) (g : ℕ) :
    ∑ p ∈ univ.filter (fun p => T.piece giv u M Y k p = g), f p ≤ B := by
  by_cases hne : ∃ p, T.piece giv u M Y k p = g
  · obtain ⟨x, ⟨-, h⟩ | ⟨hx, -, h⟩⟩ := prop_pieces_shape g hne
    · refine (Finset.sum_le_sum_of_subset (t := {x}) fun p hp => mem_singleton.2 ((h p).1 (mem_filter.1 hp).2)).trans ?_
      rw [Finset.sum_singleton]
      exact hB x
    · refine le_trans ?_ (hl x hx)
      unfold below
      rw [← Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset fun p hp => mem_filter.2 ⟨mem_univ _, (h p).1 (mem_filter.1 hp).2⟩
  · rw [Finset.filter_false_of_mem fun p _ hp => hne ⟨p, hp⟩, Finset.sum_empty]
    exact Nat.zero_le _

theorem light_le {x : Fin P} (hM : 0 < M) (hY : 0 < Y) (hx : ¬ T.Heavy giv u M Y k x) :
    k * T.below giv x ≤ 4 * M ∧ k * T.below u x ≤ 2 * Y := by
  have h : k * (T.below giv x * (2 * Y) + T.below u x * (4 * M)) ≤ 8 * M * Y := not_lt.1 fun h => hx (Or.inr h)
  have h1 : k * T.below giv x * (2 * Y) ≤ 4 * M * (2 * Y) := by linarith [Nat.zero_le (k * (T.below u x * (4 * M))), mul_add k (T.below giv x * (2 * Y)) (T.below u x * (4 * M)), mul_assoc k (T.below giv x) (2 * Y)]
  have h2 : k * T.below u x * (4 * M) ≤ 2 * Y * (4 * M) := by linarith [Nat.zero_le (k * (T.below giv x * (2 * Y))), mul_add k (T.below giv x * (2 * Y)) (T.below u x * (4 * M)), mul_assoc k (T.below u x) (4 * M)]
  exact ⟨Nat.le_of_mul_le_mul_right h1 (by omega), Nat.le_of_mul_le_mul_right h2 (by omega)⟩

/-- Between two pieces there are only units at the head of either: one node for every piece. -/
theorem piece_boundary (g : ℕ) : ∃ x, ∀ q, q ≠ T.root →
    ¬ (T.piece giv u M Y k q = g ↔ T.piece giv u M Y k (T.par q) = g) → q = x ∨ T.par q = x := by
  have hb : ∀ q, q ≠ T.root → ¬ (T.piece giv u M Y k q = g ↔ T.piece giv u M Y k (T.par q) = g) →
      ∃ y, T.Head giv u M Y k y ∧ T.rank giv u M Y k y = g ∧ (q = y ∨ T.par q = y) := by
    intro q hr hne
    have hh : T.Head giv u M Y k q := by
      by_contra h
      exact hne (by rw [piece, hd_par h]; rfl)
    have hp : T.Head giv u M Y k (T.par q) := head_of_heavy (hh.resolve_left hr)
    by_cases h1 : T.piece giv u M Y k q = g
    · exact ⟨q, hh, (piece_head hh).symm.trans h1, Or.inl rfl⟩
    · refine ⟨T.par q, hp, (piece_head hp).symm.trans ?_, Or.inr rfl⟩
      by_contra h2
      exact hne ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  by_cases hex : ∃ y, T.Head giv u M Y k y ∧ T.rank giv u M Y k y = g
  · obtain ⟨x, hx, hx2⟩ := hex
    refine ⟨x, fun q hr hne => ?_⟩
    obtain ⟨y, hy, hy2, hy3⟩ := hb q hr hne
    rwa [rank_inj hx hy (hx2.trans hy2.symm)]
  · refine ⟨T.root, fun q hr hne => ?_⟩
    obtain ⟨y, hy, hy2, -⟩ := hb q hr hne
    exact absurd ⟨y, hy, hy2⟩ hex

open Classical in
/-- "So there are at most kΛ pieces." -/
theorem _root_.Paper.prop_pieces_count {b C : ℕ} (hk : 0 < k) (hM : 0 < M) (hY : 0 < Y) (hg : ∑ q, giv q ≤ M)
    (hu : ∑ q, u q ≤ Y) (hb : ∀ p, p ≠ T.root → (univ.filter fun q => q ≠ T.root ∧ T.par q = p).card ≤ b)
    (hC : (univ.filter fun q => q ≠ T.root ∧ T.par q = T.root).card ≤ C) (p : Fin P) :
    T.piece giv u M Y k p < 1 + C + b * (T.depth * k) := by
  have hall : (univ.filter fun q => T.Head giv u M Y k q).card ≤ 1 + C + b * (T.depth * k) := by
    have hsub : (univ.filter fun q => T.Head giv u M Y k q) ⊆ ({T.root} ∪
        univ.filter fun q => q ≠ T.root ∧ T.par q = T.root) ∪
        ((range T.depth).biUnion fun s => univ.filter fun y => T.stage y = s ∧ T.Heavy giv u M Y k y).biUnion
          fun y => univ.filter fun q => q ≠ T.root ∧ T.par q = y := by
      intro q hq
      have hq := (mem_filter.1 hq).2
      by_cases h1 : q = T.root
      · exact mem_union_left _ (mem_union_left _ (mem_singleton.2 h1))
      by_cases h2 : T.par q = T.root
      · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨mem_univ _, h1, h2⟩))
      exact mem_union_right _ (mem_biUnion.2 ⟨T.par q, mem_biUnion.2 ⟨T.stage (T.par q),
        mem_range.2 (stage_lt h2), mem_filter.2 ⟨mem_univ _, rfl, hq.resolve_left h1⟩⟩,
        mem_filter.2 ⟨mem_univ _, h1, rfl⟩⟩)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add
      ((card_union_le _ _).trans (Nat.add_le_add (by rw [card_singleton]) hC)) ?_))
    refine card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum (g := fun _ => b) fun y hy => hb y fun e => ?_).trans ?_
    · obtain ⟨s, hs, hy⟩ := mem_biUnion.1 hy
      have := mem_range.1 hs
      have := (mem_filter.1 hy).2.1
      rw [(T.stage_root y).2 e] at this
      omega
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    refine Nat.mul_le_mul_left _ (card_biUnion_le.trans ?_)
    refine (Finset.sum_le_sum (g := fun _ => k) fun s hs =>
      (prop_pieces_heavy_few hk hM hY hg hu (mem_range.1 hs)).le).trans (le_of_eq ?_)
    simp
  refine lt_of_lt_of_le ?_ hall
  unfold piece rank
  exact card_lt_card ((ssubset_iff_of_subset fun q hq => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hq).2.1⟩).2
    ⟨T.hd giv u M Y k p, mem_filter.2 ⟨mem_univ _, (hd_spec p).1⟩, fun h => lt_irrefl _ (mem_filter.1 h).2.2⟩)

theorem piece_lt (p : Fin P) : T.piece giv u M Y k p < P := by
  classical
  have h := (hd_spec (T := T) (giv := giv) (u := u) (M := M) (Y := Y) (k := k) p).1
  unfold piece rank
  calc _ < (univ.filter fun q => T.Head giv u M Y k q).card :=
        card_lt_card ((ssubset_iff_of_subset fun q hq => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hq).2.1⟩).2
          ⟨_, mem_filter.2 ⟨mem_univ _, h⟩, fun h => lt_irrefl _ (mem_filter.1 h).2.2⟩)
    _ ≤ P := (card_le_univ _).trans (le_of_eq (Fintype.card_fin P))

end Staged

end Paper
