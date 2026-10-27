/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.StepSparsifyDefs
import SparsificationLemma.Iface
import SparsificationLemma.Shrink
import SparsificationLemma.Gen
import all PaddedDescent.F.MarkDeg
import all CountKSatRate.Leaf
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # The nodes of the tree of recursive calls

Lemmas for proof/sparsification/SparsificationLemma/StepSparsify.lean and
proof/sparsification/SparsificationLemma/Sketch.lean, which follow the sparsification of Lemma 4,
Appendix C and Step 5 of Appendix D sentence by sentence.
* For every step function: the leaves are among the nodes `nodesOf`
  (proof/sparsification/SparsificationLemma/StepSparsifyDefs.lean) of the tree
  (`mem_nodesOf_of_mem_leaves`), and what holds at the root and passes from a node to its two
  children holds at every node (`forall_nodesOf`).
* `node_facts`: at every node of the tree of a k-CNF ψ, for thresholds with `ThrC`, the formula is
  in normal form, none of its clauses contains another, it is a k-CNF on the variables below n, and
  it has at most as many clauses as ψ; every side clause has one literal, and the side list has at
  most k·(k−1)·n/τ clauses.
* `length_sideU_le`: the side list as it is written in the output has at most 2n clauses.
* `cntN_nil`: the formula without clauses has 2^n satisfying assignments. -/

@[expose] public section

namespace SparsificationLemma

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK

/-! ### All nodes of a tree, for every step function -/

section generic
variable {σ : Type} (step : σ → Option (σ × σ))

/-- The leaves are among the nodes. -/
theorem mem_nodesOf_of_mem_leaves (d : ℕ) (s : σ) : ∀ x ∈ leaves step d s, x ∈ nodesOf step d s := by
  induction d generalizing s with
  | zero => simp [nodesOf, leaves]
  | succ d ih =>
    cases h0 : step s with
    | none => simp [nodesOf, leaves, h0]
    | some lh =>
      simp only [nodesOf, leaves, h0, List.mem_append, List.mem_cons]
      rintro x (hx | hx)
      · exact Or.inr (Or.inl (ih _ x hx))
      · exact Or.inr (Or.inr (ih _ x hx))

/-- What holds at s and passes from a node to its two children holds at all nodes. -/
theorem forall_nodesOf {I : σ → Prop} (hI : ∀ s l h, I s → step s = some (l, h) → I l ∧ I h) (d : ℕ) (s : σ) (hs : I s) : ∀ x ∈ nodesOf step d s, I x := by
  induction d generalizing s with
  | zero => simpa [nodesOf] using hs
  | succ d ih =>
    cases h0 : step s with
    | none => simpa [nodesOf, h0] using hs
    | some lh =>
      obtain ⟨h1, h2⟩ := hI s lh.1 lh.2 hs h0
      simp only [nodesOf, h0, List.mem_append, List.mem_cons]
      rintro x (rfl | hx | hx)
      · exact hs
      · exact ih _ h1 x hx
      · exact ih _ h2 x hx

end generic

/-! ### What holds at every node -/

/-- At every node of the tree of a k-CNF ψ on n variables, for thresholds with `ThrC`: the formula
is in normal form, none of its clauses contains another, it is a k-CNF on n variables, and it has at
most as many clauses as ψ;
every side clause has one literal, on a variable below n; and the side list, as a list, has at most
k·(k−1)·n/τ clauses: only a step to a second child lengthens it, by at most k clauses, and a path
has at most (k−1)·n/τ such steps. -/
theorem node_facts {k τ n : ℕ} {θ β : ℕ → ℕ} {ψ : PFml} (hT : ThrC k τ θ β) (hψ : IsKCNF k n ψ) (D : ℕ) :
    ∀ x ∈ nodesOf (stepC θ k) D (root ψ), NF x.1 ∧ Reduced (toFin x.1) ∧ IsKCNF k n x.1 ∧ x.1.length ≤ ψ.length ∧ (∀ C ∈ x.2, ∃ l, C = [l] ∧ l.1 < n) ∧
      x.2.length * τ ≤ k * ((k - 1) * n) := by
  have hθ : ∀ i, 1 ≤ θ i := hT.pos
  have hI := stIfaceC k τ n _ θ β hT (le_refl _)
  have hR := Refine.stRefines θ k hθ
  have hOk := Gen.ok_of hψ
  have hψ' : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := fun C hC => (hψ C hC).2
  have key := forall_nodesOf (stepC θ k)
    (I := fun x => (∃ p t, ProgMain.G (fun F₀ F p t => ProgMain.Ok k n F₀ ∧ NodeU θ k τ F₀ F p t) ψ x.1 p t ∧ x.2.length * τ ≤ k * t) ∧ x.1.length ≤ ψ.length ∧
      ∀ C ∈ x.2, ∃ l, C = [l] ∧ l.1 < n) (by
      rintro s l h ⟨⟨p, t, hG, hlt⟩, hlen, hside⟩ hst
      obtain ⟨⟨H, P⟩, hp, he⟩ := Option.map_eq_some_iff.1 hst
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have hK : stepK θ k s.1 = some (addP [H] s.1, addP P s.1) := by simp [stepK, hp]
      obtain ⟨g1, g2⟩ := ProgMain.G_step hI hR ψ s.1 p t _ _ hG hK
      obtain ⟨-, N, a, hh, hInv, -⟩ := hG.2.2
      obtain ⟨l1, l2⟩ := Shrink.length_step_le hθ hG.1 hInv.red hst
      obtain ⟨hHk, hHn⟩ := ProgC.pick_spec hθ hI hR hψ' hG hp
      refine ⟨⟨⟨_, _, g1, hlt⟩, l1.trans hlen, hside⟩, ⟨⟨_, _, g2, ?_⟩, l2.trans hlen, fun C hC => ?_⟩⟩
      · show (negU H ++ s.2).length * τ ≤ k * (t + τ)
        rw [List.length_append, negU, List.length_map, Nat.add_mul, Nat.mul_add]
        have := Nat.mul_le_mul_right τ hHk
        omega
      · rcases List.mem_append.1 hC with hC | hC
        · obtain ⟨ω, hω, rfl⟩ := List.mem_map.1 hC
          exact ⟨_, rfl, hHn ω hω⟩
        · exact hside C hC) D (root ψ)
    ⟨⟨0, 0, ⟨hR.nf_root ψ, show ProgMain.Ok k n (toFin ψ) ∧ NodeU θ k τ (toFin ψ) (toFin (rootP ψ)) 0 0 by rw [hR.toFin_root]; exact hI.root _ hOk⟩, by simp [root]⟩,
      Gen.length_rootP_le ψ, by simp [root]⟩
  intro x hx
  obtain ⟨⟨p, t, hG, hlt⟩, hlen, hside⟩ := key x hx
  have hb := (hI.bound _ _ _ _ hG.2).2
  obtain ⟨hnf, hok, hsub, N, a, hh, hInv, -⟩ := hG
  refine ⟨hnf, hInv.red, fun C hC => ?_, hlen, hside, hlt.trans (Nat.mul_le_mul_left _ hb)⟩
  obtain ⟨C', hC', hs, hne⟩ := hsub _ (ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
  obtain ⟨b1, b2, b3⟩ := hok C' hC'
  refine ⟨(List.toFinset_nonempty_iff C).1 (hne b2), ?_, fun l hl => ?_⟩
  · rw [← List.toFinset_card_of_nodup (hnf.1 C hC)]
    exact (card_le_card hs).trans b3
  · have := b1 (hs (List.mem_toFinset.2 hl))
    rw [ProgMain.litsBelow, Finset.mem_product, Finset.mem_range] at this
    exact this.1

/-! ### The length of the side list -/

/-- There are only 2n clauses with one literal: the side list as it is written in the output has at
most 2n clauses, if its variables are below n. -/
theorem length_sideU_le {X : PFml} {n : ℕ} (h : ∀ C ∈ X, ∀ l ∈ C, l.1 < n) : (sideU X).length ≤ 2 * n := by
  have hnd : (sideU X).Nodup := List.nodup_dedup _
  rw [← List.toFinset_card_of_nodup hnd]
  refine (Finset.card_le_card (t := (ProgMain.litsBelow n).image fun l => [l]) ?_).trans (Finset.card_image_le.trans (ProgMain.card_litsBelow n))
  intro C hC
  rw [List.mem_toFinset, Leaf.mem_sideU] at hC
  obtain ⟨l, rfl⟩ := List.length_eq_one_iff.1 hC.2
  refine Finset.mem_image.2 ⟨l, ?_, rfl⟩
  rw [ProgMain.litsBelow, Finset.mem_product, Finset.mem_range]
  exact ⟨h _ hC.1 l (by simp), Finset.mem_univ _⟩

/-! ### The number of satisfying assignments of the formula without clauses -/

/-- The formula without clauses has 2^n satisfying assignments. -/
theorem cntN_nil (n : ℕ) : cntN n [] = 2 ^ n := by
  simp [cntN]

end SparsificationLemma
