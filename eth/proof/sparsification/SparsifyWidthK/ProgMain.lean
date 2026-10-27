/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyWidthK.Interfaces
import Mathlib.Tactic.Linarith

/-! # The sparsification lemma for width k, for the program on lists

This file proves `StProg`: the tree of the program `stepK` below `rootP ψ` has few leaves, every
leaf has few clauses, ψ is satisfied exactly if some leaf
is, and the stack of the depth-first walk stays small. `StProg` and the ten statements it is proved
from are interface statements of
SparsifyWidthK/Interfaces.lean: nine are about finite sets and thresholds, and `StRefines` says that
the program computes the rule on finite sets.
The lemmas on trees of StepMachines/Math/SparsifyTree.lean are applied to the program directly, with
the invariant «s is in normal form, and the set of
its clauses is a node of the tree of the rule». -/

@[expose] public section

namespace WidthK.ProgMain

open Finset Groundwork Groundwork.Sparsify WidthK.Prog

/-- The members of `toFin s` are the clauses of s, read as sets. -/
theorem mem_toFin {s : PFml} {X : Finset PLit} : X ∈ toFin s ↔ ∃ C ∈ s, C.toFinset = X := by
  simp [toFin]

/-- The test `subP D C` says that D, read as a set, is contained in C. -/
theorem subP_iff_subset (D C : PCl) : subP D C = true ↔ D.toFinset ⊆ C.toFinset := by
  simp [subP, Finset.subset_iff]

/-- As sets, `addP A s` consists of the clauses of A and the clauses of s that contain no clause of
A. -/
theorem toFin_addP (A s : PFml) :
    toFin (addP A s) = toFin A ∪ (toFin s).filter fun C => ∀ D ∈ toFin A, ¬ D ⊆ C := by
  ext X
  simp only [mem_union, mem_filter, mem_toFin, addP, List.mem_append, List.mem_filter, Bool.not_eq_true',
    List.any_eq_false, subP_iff_subset]
  constructor
  · rintro ⟨C, hC | ⟨hC, hno⟩, rfl⟩
    · exact Or.inl ⟨C, hC, rfl⟩
    · refine Or.inr ⟨⟨C, hC, rfl⟩, ?_⟩
      rintro D ⟨D₀, hD₀, rfl⟩
      exact hno D₀ hD₀
  · rintro (⟨C, hC, rfl⟩ | ⟨⟨C, hC, rfl⟩, hno⟩)
    · exact ⟨C, Or.inl hC, rfl⟩
    · exact ⟨C, Or.inr ⟨hC, fun D hD => hno _ ⟨D, hD, rfl⟩⟩, rfl⟩

/-- `addP` keeps the normal form. -/
theorem nf_addP {A s : PFml} (hA : NF A) (hs : NF s) : NF (addP A s) := by
  refine ⟨?_, ?_⟩
  · intro C hC
    rcases List.mem_append.1 hC with hC | hC
    · exact hA.1 C hC
    · exact hs.1 C (List.mem_filter.1 hC).1
  · rw [Groundwork.Sparsify.addP, List.map_append, List.nodup_append]
    refine ⟨hA.2, hs.2.sublist (List.filter_sublist.map _), ?_⟩
    intro X hX Y hY hXY
    obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hX
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hY
    have hno := (List.mem_filter.1 hC).2
    simp only [Bool.not_eq_true', List.any_eq_false, subP_iff_subset] at hno
    exact hno D hD (hXY ▸ Finset.Subset.refl _)

/-- A formula in normal form has as many clauses as its set of clauses has members. -/
theorem nf_length_eq {s : PFml} (hs : NF s) : s.length = (toFin s).card := by
  rw [toFin, List.toFinset_card_of_nodup hs.2, List.length_map]


section asm

variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

/-- The set of clauses of a formula with one clause. -/
theorem toFin_singleton (H : PCl) : toFin [H] = {H.toFinset} := by simp [toFin]

/-- A formula with one clause, in which no literal occurs twice, is in normal form. -/
theorem NF_singleton {H : PCl} (h : H.Nodup) : NF [H] := ⟨by simpa using h, by simp⟩

/-- Truth values satisfy the set of clauses of x exactly if every clause of the list x has a true
literal. -/
theorem sat_toFin (v : PLit → Prop) (x : PFml) : Sat v (toFin x) ↔ ∀ C ∈ x, ∃ a ∈ C, v a := by
  simp only [Sat, mem_toFin]
  constructor
  · intro h C hC
    obtain ⟨a, ha, hv⟩ := h _ ⟨C, hC, rfl⟩
    exact ⟨a, List.mem_toFinset.1 ha, hv⟩
  · rintro h X ⟨C, hC, rfl⟩
    obtain ⟨a, ha, hv⟩ := h C hC
    exact ⟨a, List.mem_toFinset.2 ha, hv⟩

/-- The invariant of the tree of ψ: s is in normal form, and its set of clauses is a node with the
counters p (steps) and t (units used by heavy steps). -/
def G (Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop) (ψ s : PFml) (p t : ℕ) : Prop :=
  NF s ∧ Node (toFin ψ) (toFin s) p t

/-- One step of the program is one step of the rule: the two lists it returns are in normal form,
and as sets they are the light and the heavy child. -/
theorem step_spec (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {ψ s l h : PFml} {p t : ℕ} (hG : G Node ψ s p t)
    (hst : stepK θ k s = some (l, h)) :
    ∃ j H, Rule θ k (toFin s) j H ∧ toFin l = light (toFin s) H ∧ toFin h = heavy (toFin s) j H ∧ NF l ∧ NF h := by
  obtain ⟨⟨H, P⟩, hp, he⟩ := Option.map_eq_some_iff.1 hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨j, hrule, hP, hnfP, hH⟩ := hR.some s H P hG.1 hp
  refine ⟨j, H.toFinset, hrule, ?_, ?_, nf_addP (NF_singleton hH) hG.1, nf_addP hnfP hG.1⟩
  · rw [toFin_addP, toFin_singleton, hI.light_eq _ _ _ _ _ _ hG.2 hrule]
    simp
  · rw [toFin_addP, hP, hI.heavy_eq _ _ _ _ _ _ hG.2 hrule]

/-- Both children of a step satisfy the invariant: one more step, and q more units at the heavy
child. -/
theorem G_step (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) (ψ : PFml) (s : PFml) (p t : ℕ) (l h : PFml)
    (hG : G Node ψ s p t) (hst : stepK θ k s = some (l, h)) : G Node ψ l (p + 1) t ∧ G Node ψ h (p + 1) (t + q) := by
  obtain ⟨j, H, hrule, hl, hh, hnl, hnh⟩ := step_spec hI hR hG hst
  obtain ⟨h1, h2⟩ := hI.step _ _ _ _ _ _ hG.2 hrule
  exact ⟨⟨hnl, hl ▸ h1⟩, ⟨hnh, hh ▸ h2⟩⟩

/-- If every clause of F lies inside a clause of F₀, and these have at most k literals, then F has
at most |F₀|·2^k clauses. -/
theorem card_le_of_clause {F₀ F : Finset (Finset PLit)} (hk : ∀ C ∈ F₀, C.card ≤ k) (h : ∀ C ∈ F, ∃ C₀ ∈ F₀, C ⊆ C₀) :
    F.card ≤ F₀.card * 2 ^ k := by
  have hsub : F ⊆ F₀.biUnion Finset.powerset := by
    intro C hC
    obtain ⟨C₀, hC₀, hs⟩ := h C hC
    exact mem_biUnion.2 ⟨C₀, hC₀, mem_powerset.2 hs⟩
  refine (card_le_card hsub).trans (card_biUnion_le_card_mul _ _ _ fun C hC => ?_)
  rw [card_powerset]
  exact Nat.pow_le_pow_right (by norm_num) (hk C hC)

/-- The sparsification lemma for the program `stepK`, for any thresholds θ and any bounds D, T, q,
leafB for which the facts on finite sets (`Iface`) and
the refinement (`Refines`) hold. hv bounds the number of heavy steps on a path. -/
theorem sparsify_prog_of (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n hv : ℕ} (hT : T < (hv + 1) * q) (ψ : PFml)
    (hOk : Ok (toFin ψ)) (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    let L := leaves (stepK θ k) D (rootP ψ)
    L.length ≤ ∑ j ∈ range (hv + 1), D.choose j ∧
    (∀ x ∈ L, stepK θ k x = none ∧ x.length ≤ leafB ∧ ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧
    (∀ v : PLit → Prop, (∀ C ∈ ψ, ∃ a ∈ C, v a) ↔ ∃ x ∈ L, ∀ C ∈ x, ∃ a ∈ C, v a) ∧
    ∀ i, ((round (stepK θ k))^[i] ([rootP ψ], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((round (stepK θ k))^[i] ([rootP ψ], [])).1, x.length ≤ ψ.length * 2 ^ k ∧
        ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
  intro L
  have hb : ∀ s p t, G Node ψ s p t → p ≤ D ∧ t ≤ T := fun s p t h => hI.bound _ _ _ _ h.2
  have hs := G_step hI hR ψ
  have hr : G Node ψ (rootP ψ) 0 0 := ⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ hOk⟩
  have hnone := step_eq_none_of_mem_leaves hb hs D (rootP ψ) 0 0 hr (by omega)
  have hk0 : ∀ C ∈ toFin ψ, C.card ≤ k := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := mem_toFin.1 hX
    exact (List.toFinset_card_le C).trans (hψ C hC).1
  have hcl : ∀ x p t, G Node ψ x p t → ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
    intro x p t hx C hC
    obtain ⟨X₀, hX₀, hsub⟩ := hI.clause _ _ _ _ hx.2 _ (mem_toFin.2 ⟨C, hC, rfl⟩)
    obtain ⟨C₀, hC₀, rfl⟩ := mem_toFin.1 hX₀
    refine ⟨?_, fun l hl => (hψ C₀ hC₀).2 l (List.mem_toFinset.1 (hsub (List.mem_toFinset.2 hl)))⟩
    rw [← List.toFinset_card_of_nodup (hx.1.1 C hC)]
    exact (card_le_card hsub).trans (hk0 _ hX₀)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact length_leaves_le hb hs _ _ _ _ 0 0 hr (by omega) (by omega)
  · intro x hx
    obtain ⟨p', t', hx'⟩ := exists_of_mem_leaves hs _ _ 0 0 hr x hx
    refine ⟨hnone x hx, ?_, hcl x p' t' hx'⟩
    rw [nf_length_eq hx'.1]
    refine hI.leaf _ _ _ _ hx'.2 (hR.none x hx'.1 ?_)
    have := hnone x hx
    simpa [stepK] using this
  · intro v
    have h0 : (∀ C ∈ ψ, ∃ a ∈ C, v a) ↔ ∀ C ∈ rootP ψ, ∃ a ∈ C, v a := by
      rw [← sat_toFin, ← sat_toFin, hR.toFin_root, sat_red]
    rw [h0]
    refine iff_exists_mem_leaves hs (fun s => ∀ C ∈ s, ∃ a ∈ C, v a) ?_ _ _ 0 0 hr
    intro s p t l h hn hst
    obtain ⟨j, H, hrule, hl, hh, -, -⟩ := step_spec hI hR hn hst
    have := hI.sat _ _ _ _ _ _ v hn.2 hrule
    rwa [← hl, ← hh, sat_toFin, sat_toFin, sat_toFin] at this
  · intro i
    obtain ⟨h1, h2⟩ := stack_bound hb hs (rootP ψ) 0 0 hr i
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨p', t', hx'⟩ := h2 x hx
    refine ⟨?_, hcl x p' t' hx'⟩
    rw [nf_length_eq hx'.1]
    refine (card_le_of_clause hk0 (hI.clause _ _ _ _ hx'.2)).trans (Nat.mul_le_mul_right _ ?_)
    rw [toFin]
    exact (List.toFinset_card_le _).trans (by simp)

end asm


/-- The literals on variables below n. -/
def litsBelow (n : ℕ) : Finset PLit := Finset.range n ×ˢ (Finset.univ : Finset Bool)

/-- The condition on the formula at the root: nonempty clauses of at most k literals on variables
below n. -/
def Ok (k n : ℕ) (F₀ : Finset (Finset PLit)) : Prop := ∀ C ∈ F₀, C ⊆ litsBelow n ∧ C.Nonempty ∧ C.card ≤ k

/-- There are at most 2n literals on variables below n. -/
theorem card_litsBelow (n : ℕ) : (litsBelow n).card ≤ 2 * n := by
  rw [litsBelow, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool, Nat.mul_comm]

/-- The facts on finite sets that `sparsify_prog_of` needs, for the thresholds `theta τ`, collected
from the interface statements. -/
theorem iface (h1 : StNodeRoot) (h2 : StNodeStep) (h3 : StNodeBound) (h4 : StLeafCard) (h5 : StLightEq) (h6 : StHeavyEq) (h7 : StSatIff)
    (h8 : StThr) (h9 : StBetaSum) {τ : ℕ} (hτ : 1 ≤ τ) (k n : ℕ) :
    Iface (theta τ) k (bsum τ k * n) (k * n) τ (leafC τ k * n) (Ok k n)
      (fun F₀ F p t => Ok k n F₀ ∧ Node (theta τ) k τ F₀ F p t) where
  root F₀ h := ⟨h, h1 _ _ _ _ _⟩
  step F₀ F p t j H hN hR := by
    obtain ⟨a, b⟩ := h2 _ _ _ _ _ _ _ _ _ _ (h8 τ hτ).pos hN.2 hR
    exact ⟨⟨hN.1, a⟩, ⟨hN.1, b⟩⟩
  bound F₀ F p t hN := by
    obtain ⟨a, b⟩ := h3 _ (theta τ) (beta τ) k τ n F₀ F (litsBelow n) p t (h8 τ hτ) (card_litsBelow n) (fun C hC => (hN.1 C hC).1) hN.2
    exact ⟨a.trans (Nat.mul_le_mul_right _ (h9 τ k)), b⟩
  clause F₀ F p t hN C hC := by
    obtain ⟨C', hC', hs, -⟩ := hN.2.1 C hC
    exact ⟨C', hC', hs⟩
  leaf F₀ F p t hN hL := by
    refine h4 _ (theta τ) k n F (litsBelow n) (h8 τ hτ).pos (card_litsBelow n) (fun C hC => ?_) hL
    obtain ⟨C', hC', hs, hne⟩ := hN.2.1 C hC
    obtain ⟨a, b, c⟩ := hN.1 C' hC'
    exact ⟨hs.trans a, hne b, (card_le_card hs).trans c⟩
  sat F₀ F p t j H v _ _ := h7 _ _ _ _ _
  light_eq F₀ F p t j H hN hR := by
    obtain ⟨-, N, a, h, hI, -⟩ := hN.2
    exact h5 _ _ _ _ _ (h8 τ hτ).pos hI.red hR.heart
  heavy_eq F₀ F p t j H hN hR := by
    obtain ⟨-, N, a, h, hI, -⟩ := hN.2
    exact h6 _ _ _ _ _ hI.red hR.heart

end WidthK.ProgMain

namespace WidthK

open Finset Groundwork Groundwork.Sparsify WidthK.Prog

/-- The sparsification lemma for width k for the program `stepK (theta τ) k`, from the other
interface statements. -/
theorem stProg (h1 : StNodeRoot) (h2 : StNodeStep) (h3 : StNodeBound) (h4 : StLeafCard) (h5 : StLightEq) (h6 : StHeavyEq) (h7 : StSatIff)
    (h8 : StThr) (h9 : StBetaSum) (h10 : StRefines) : StProg := by
  intro τ k n hτ ψ hψ
  refine ProgMain.sparsify_prog_of (ProgMain.iface h1 h2 h3 h4 h5 h6 h7 h8 h9 hτ k n) (h10 _ k (h8 τ hτ).pos) (n := n) (hv := k * n / τ)
    ?_ ψ ?_ fun C hC => (hψ C hC).2
  · calc k * n < τ * (k * n / τ + 1) := Nat.lt_mul_div_succ (k * n) (by omega : 0 < τ)
      _ = (k * n / τ + 1) * τ := Nat.mul_comm _ _
  · intro X hX
    obtain ⟨C, hC, rfl⟩ := ProgMain.mem_toFin.1 hX
    obtain ⟨a, b, c⟩ := hψ C hC
    refine ⟨fun l hl => ?_, (List.toFinset_nonempty_iff C).2 a, (List.toFinset_card_le C).trans b⟩
    rw [ProgMain.litsBelow, Finset.mem_product, Finset.mem_range]
    exact ⟨c l (List.mem_toFinset.1 hl), Finset.mem_univ _⟩

end WidthK
