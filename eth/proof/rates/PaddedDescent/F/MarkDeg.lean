/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import SparsifyWidthK.ProgMain
import SparsifyWidthK.Step
import SparsifyWidthK.SetAlg
import SparsifyWidthK.Thresholds
import SparsifyWidthK.Refine

/-! # Marks and layers: how often a variable occurs at a leaf, and how many clauses touch a node

This file proves `StLeaf`, one of the interface lemmas of
proof/rates/PaddedDescent/F/Interfaces.lean: a leaf of the sparsification tree at width k has
nonempty clauses only, and
every variable occurs in at most leafC τ k of them. The reason is the definition of a leaf in
proof/sparsification/SparsifyWidthK/Defs.lean: no nonempty set of fewer than j literals lies in
θ (j − its size) or more clauses of size j, so a literal lies in fewer than θ (j − 1) clauses of
size j ≥ 2, and in at most one clause of size 1.
The invariant of the tree and the step from lists to finite sets are those of
proof/sparsification/SparsifyWidthK/ProgMain.lean and
proof/sparsification/SparsifyWidthK/Refine.lean.
It also proves `length_tch_le` and `length_tch_le_of_wfL`: if every variable occurs in at most Δ
clauses of the layers, at most qv g n · Δ clauses touch a node, because a node holds qv g n
variables. -/

namespace PaddedDescent.F.Mark.Deg

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)

/-! ### A leaf, as a finite set of finite sets -/

section fin
variable {α : Type*} [DecidableEq α] {θ : ℕ → ℕ} {k : ℕ} {F : Finset (Finset α)}

/-- A literal lies in at most one set of size 1. -/
theorem card_filter_mem_le_one {G : Finset (Finset α)} (hG : ∀ C ∈ G, C.card = 1) (y : α) : (G.filter fun C => y ∈ C).card ≤ 1 := by
  rw [card_le_one]
  intro C hC D hD
  obtain ⟨hC, hyC⟩ := mem_filter.1 hC
  obtain ⟨hD, hyD⟩ := mem_filter.1 hD
  obtain ⟨c, rfl⟩ := card_eq_one.1 (hG C hC)
  obtain ⟨e, rfl⟩ := card_eq_one.1 (hG D hD)
  rw [mem_singleton] at hyC hyD
  rw [← hyC, ← hyD]

/-- At a leaf whose clauses have 1 to k literals, a literal lies in at most θ 0 + … + θ (k − 1)
clauses. -/
theorem card_filter_mem_le (hθ : ∀ i, 0 < θ i) (h : WidthK.Leaf θ k F) (hF : ∀ C ∈ F, 1 ≤ C.card ∧ C.card ≤ k) (y : α) :
    (F.filter fun C => y ∈ C).card ≤ ∑ i ∈ range k, θ i := by
  have hd : ∀ i < k, ((lay F (i + 1)).filter fun C => y ∈ C).card ≤ θ i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact (card_filter_mem_le_one (fun C hC => (mem_filter.1 hC).2) y).trans (hθ 0)
    · by_contra hc
      refine h (i + 1) hi {y} ⟨singleton_nonempty y, by rw [card_singleton]; omega, ?_⟩
      rw [card_singleton, Nat.add_sub_cancel]
      simpa only [lay, Sparsify.over, filter_filter, singleton_subset_iff] using (not_le.1 hc).le
  have hsub : (F.filter fun C => y ∈ C) ⊆ (range k).biUnion fun i => (lay F (i + 1)).filter fun C => y ∈ C := by
    intro C hC
    obtain ⟨hCF, hy⟩ := mem_filter.1 hC
    obtain ⟨h1, h2⟩ := hF C hCF
    exact mem_biUnion.2 ⟨C.card - 1, mem_range.2 (by omega), mem_filter.2 ⟨mem_filter.2 ⟨hCF, by omega⟩, hy⟩⟩
  calc (F.filter fun C => y ∈ C).card ≤ ((range k).biUnion fun i => (lay F (i + 1)).filter fun C => y ∈ C).card := card_le_card hsub
    _ ≤ ∑ i ∈ range k, ((lay F (i + 1)).filter fun C => y ∈ C).card := card_biUnion_le
    _ ≤ ∑ i ∈ range k, θ i := sum_le_sum fun i hi => hd i (mem_range.1 hi)

end fin

/-! ### A leaf, as a list of lists -/

/-- In a list in normal form, the clauses with the variable v are at most those with the literal v
and those with the literal ¬v. -/
theorem length_occ_le {x : PFml} (hx : NF x) (v : ℕ) :
    (occ x v).length ≤ ((toFin x).filter fun C => (v, true) ∈ C).card + ((toFin x).filter fun C => (v, false) ∈ C).card := by
  have hnf : NF (occ x v) := ⟨fun C hC => hx.1 C (List.mem_filter.1 hC).1, hx.2.sublist (List.filter_sublist.map _)⟩
  rw [WidthK.ProgMain.nf_length_eq hnf]
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro X hX
  obtain ⟨C, hC, rfl⟩ := WidthK.ProgMain.mem_toFin.1 hX
  obtain ⟨hCx, hany⟩ := List.mem_filter.1 hC
  obtain ⟨l, hl, hv⟩ := List.any_eq_true.1 hany
  have hv' : l.1 = v := by simpa using hv
  have hm : C.toFinset ∈ toFin x := WidthK.ProgMain.mem_toFin.2 ⟨C, hCx, rfl⟩
  obtain ⟨a, b⟩ := l
  obtain rfl : a = v := hv'
  cases b
  · exact mem_union_right _ (mem_filter.2 ⟨hm, List.mem_toFinset.2 hl⟩)
  · exact mem_union_left _ (mem_filter.2 ⟨hm, List.mem_toFinset.2 hl⟩)

/-- Where `stepK` has no answer, every variable occurs in at most 2·(θ 0 + … + θ (k − 1)) clauses. -/
theorem length_occ_le_of_none {θ : ℕ → ℕ} {k : ℕ} (hθ : ∀ i, 1 ≤ θ i) {x : PFml} (hx : NF x)
    (hcl : ∀ C ∈ x, C ≠ [] ∧ C.length ≤ k) (hst : stepK θ k x = none) (v : ℕ) : (occ x v).length ≤ 2 * ∑ i ∈ range k, θ i := by
  have hleaf : WidthK.Leaf θ k (toFin x) := (WidthK.Refine.stRefines θ k hθ).none x hx (by simpa [stepK] using hst)
  have hF : ∀ C ∈ toFin x, 1 ≤ C.card ∧ C.card ≤ k := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := WidthK.ProgMain.mem_toFin.1 hX
    exact ⟨card_pos.2 ((List.toFinset_nonempty_iff C).2 (hcl C hC).1), (List.toFinset_card_le C).trans (hcl C hC).2⟩
  have h1 := card_filter_mem_le hθ hleaf hF (v, true)
  have h2 := card_filter_mem_le hθ hleaf hF (v, false)
  have h3 := length_occ_le hx v
  omega

/-- Every leaf of the tree of `stepK (theta τ) k` below `rootP ψ` is in normal form, has nonempty
clauses only, and every variable occurs in at most leafC τ k of
its clauses. ψ has variables below n and nonempty clauses of at most k literals. -/
theorem leaf_spec {τ : ℕ} (hτ : 1 ≤ τ) (k n : ℕ) (ψ : PFml) (hψ : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    ∀ x ∈ leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ), NF x ∧ (∀ C ∈ x, C ≠ []) ∧ ∀ v, (occ x v).length ≤ leafC τ k := by
  have hθ : ∀ i, 1 ≤ theta τ i := (WidthK.stThr τ hτ).pos
  have hI := WidthK.ProgMain.iface WidthK.stNodeRoot WidthK.stNodeStep WidthK.stNodeBound WidthK.stLeafCard WidthK.stLightEq
    WidthK.stHeavyEq WidthK.stSatIff WidthK.stThr WidthK.stBetaSum hτ k n
  have hR := WidthK.Refine.stRefines _ k hθ
  have hOk : WidthK.ProgMain.Ok k n (toFin ψ) := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := WidthK.ProgMain.mem_toFin.1 hX
    obtain ⟨a, b, c⟩ := hψ C hC
    refine ⟨fun l hl => ?_, (List.toFinset_nonempty_iff C).2 a, (List.toFinset_card_le C).trans b⟩
    rw [WidthK.ProgMain.litsBelow, Finset.mem_product, Finset.mem_range]
    exact ⟨c l (List.mem_toFinset.1 hl), Finset.mem_univ _⟩
  have hb : ∀ s p t, WidthK.ProgMain.G (fun F₀ F p t => WidthK.ProgMain.Ok k n F₀ ∧ WidthK.Node (theta τ) k τ F₀ F p t) ψ s p t →
      p ≤ bsum τ k * n ∧ t ≤ k * n := fun s p t h => hI.bound _ _ _ _ h.2
  have hs := WidthK.ProgMain.G_step hI hR ψ
  have hr : WidthK.ProgMain.G (fun F₀ F p t => WidthK.ProgMain.Ok k n F₀ ∧ WidthK.Node (theta τ) k τ F₀ F p t) ψ (rootP ψ) 0 0 :=
    ⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ hOk⟩
  have hnone := step_eq_none_of_mem_leaves hb hs (bsum τ k * n) (rootP ψ) 0 0 hr (by omega)
  intro x hx
  obtain ⟨p', t', hx'⟩ := exists_of_mem_leaves hs _ _ 0 0 hr x hx
  have hcl : ∀ C ∈ x, C ≠ [] ∧ C.length ≤ k := by
    intro C hC
    obtain ⟨C', hC', hsub, hne⟩ := hx'.2.2.1 _ (WidthK.ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
    obtain ⟨-, b, c⟩ := hx'.2.1 C' hC'
    refine ⟨(List.toFinset_nonempty_iff C).1 (hne b), ?_⟩
    rw [← List.toFinset_card_of_nodup (hx'.1.1 C hC)]
    exact (card_le_card hsub).trans c
  exact ⟨hx'.1, fun C hC => (hcl C hC).1, fun v => length_occ_le_of_none hθ hx'.1 hcl (hnone x hx) v⟩

/-! ### The clauses that touch a node -/

/-- Reading a list at the places 0, 1, … gives the list back. -/
theorem map_getD_range {α : Type*} (l : List α) (d : α) : (List.range l.length).map (fun e => l.getD e d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

/-- Counting the places of a list by a property of the entry is counting the entries. -/
public theorem length_filter_range {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    ((List.range l.length).filter fun e => p (l.getD e d)).length = l.countP p := by
  conv_rhs => rw [← map_getD_range l d, List.countP_map]
  rw [List.countP_eq_length_filter]
  rfl

/-- The clauses of `cls Ls`, without the numbers of their layers, are the layers one after the
other. -/
theorem map_snd_cls (Ls : List Fml) : (cls Ls).map Prod.snd = Ls.flatten := by
  conv_rhs => rw [← map_getD_range Ls [], ← List.flatMap_def]
  rw [cls, List.map_flatMap]
  congr 1
  funext i
  rw [List.map_map]
  exact List.map_id _

/-- `cls Ls` has as many entries as the layers have clauses. -/
theorem length_cls (Ls : List Fml) : (cls Ls).length = Ls.flatten.length := by
  rw [← map_snd_cls, List.length_map]

/-- A clause with a variable among a·q, …, a·q + q − 1 is counted at one of these variables. -/
theorem countP_block_le {q : ℕ} (hq : 0 < q) (a : ℕ) (L : Fml) :
    L.countP (fun C => C.any fun l => l.1 / q == a) ≤ ∑ r ∈ range q, L.countP fun C => C.any fun l => l.1 == a * q + r := by
  induction L with
  | nil => simp
  | cons C L ih =>
    simp only [List.countP_cons, sum_add_distrib]
    refine Nat.add_le_add ih ?_
    by_cases h : (C.any fun l => l.1 / q == a) = true
    · obtain ⟨l, hl, hla⟩ := List.any_eq_true.1 h
      have hla' : l.1 / q = a := by simpa using hla
      have hr : l.1 % q ∈ range q := mem_range.2 (Nat.mod_lt _ hq)
      have h1 : (C.any fun l' => l'.1 == a * q + l.1 % q) = true :=
        List.any_eq_true.2 ⟨l, hl, by rw [← hla', Nat.div_add_mod']; simp⟩
      rw [if_pos h]
      refine le_trans ?_ (single_le_sum (f := fun r => if (C.any fun l' => l'.1 == a * q + r) = true then 1 else 0)
        (fun _ _ => Nat.zero_le _) hr)
      simp only [h1, if_true, le_refl]
    · rw [if_neg h]; exact Nat.zero_le _

/-- If every variable occurs in at most Δ clauses of the layers, at most qv g n · Δ of these clauses
touch the node a. -/
public theorem length_tch_le {g n Δ : ℕ} {Ls : List Fml} (hq : 0 < qv g n) (hx : ∀ v, (occ Ls.flatten v).length ≤ Δ) (a : ℕ) :
    (tch g n Ls a).length ≤ qv g n * Δ := by
  have e1 : (tch g n Ls a).length = (cls Ls).countP fun p => p.2.any fun l => l.1 / qv g n == a :=
    length_filter_range (cls Ls) (0, []) fun p => p.2.any fun l => l.1 / qv g n == a
  have e2 : ((cls Ls).countP fun p => p.2.any fun l => l.1 / qv g n == a) =
      Ls.flatten.countP fun C => C.any fun l => l.1 / qv g n == a := by
    rw [← map_snd_cls, List.countP_map]; rfl
  rw [e1, e2]
  refine (countP_block_le hq a _).trans ?_
  refine (sum_le_card_nsmul _ _ Δ fun r _ => ?_).trans (by simp)
  refine le_trans ?_ (hx (a * qv g n + r))
  rw [occ, ← List.countP_eq_length_filter]

/-- A node holds at least one variable if there is a node and a variable. -/
theorem qv_pos {g n : ℕ} (hg : 0 < g) (hn : 0 < n) : 0 < qv g n := Nat.div_pos (by omega) hg

/-- At most qv g n · Δ clauses touch a node, for well-formed layers and at least one node, also if
there is no variable: then there is no clause. -/
public theorem length_tch_le_of_wfL {k g n Δ : ℕ} {Ls : List Fml} (hg : 0 < g) (hW : WfL k n Ls) (hx : ∀ v, (occ Ls.flatten v).length ≤ Δ) (a : ℕ) :
    (tch g n Ls a).length ≤ qv g n * Δ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : Ls.flatten = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro C hC
      obtain ⟨L, hL, hCL⟩ := List.mem_flatten.1 hC
      obtain ⟨hne, -, hlt⟩ := hW L hL C hCL
      obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil C hne
      exact absurd (hlt l hl) (Nat.not_lt_zero _)
    rw [tch, length_cls, h0]
    simp
  · exact length_tch_le (qv_pos hg hn) hx a

end PaddedDescent.F.Mark.Deg

namespace PaddedDescent.F

/-- A leaf of the tree at width k has nonempty clauses only, and every variable occurs in at most
leafC τ k of them: the interface lemma `StLeaf`. -/
public theorem stLeaf : StLeaf := fun k _ n ψ hτ hψ x hx =>
  ⟨(Mark.Deg.leaf_spec hτ k n ψ hψ x hx).2.1, (Mark.Deg.leaf_spec hτ k n ψ hψ x hx).2.2⟩

end PaddedDescent.F
