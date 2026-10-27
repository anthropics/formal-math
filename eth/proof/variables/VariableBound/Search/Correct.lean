/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Search.Defs
public import VariableBound.StepChoice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Step 2 of Appendix D as a program: the search is right

Proves `VariableBound.StSearchD`.

* Lists of numbers against sets: load(E) is the number of lists that contain E (`load_chksD`), Σ_E
  2^load(E) is `loadSum` (`sum_load`), a list of distinct numbers below m has as many members as its
  set (`card_setD`).
* Υ(𝓛) is `upsNum` over a positive denominator that depends only on the number of checks (`ups_eq`),
  so the candidates of one round compare by `upsNum` as by Υ.
* `argminD` returns a member of the list with the smallest key (`argminD_spec`).
* Every list that the loop passes through consists of candidates and is reached in the sense of
  `AppVariables.Reached` (`Inv`); by the bounds of Step 2 on a list of checks
  (`VariableBound.stepChoice`) it, and it with one more candidate if X > 0, has `StructD`, so `evX`
  is only asked where it is right (`round_inv`), and the cut-off by the pad does nothing, because
  the word of such a list fits under it (`fold_inv`).
* After j rounds, X = 0 or the list has j checks (`fold_inv`); a reached list of r̄ checks has X = 0. -/

public section

namespace VariableBound.Search

open Groundwork PaddedDescent.F AppVariables Finset

/-! ### Lists of numbers and sets of clauses -/

/-- The list (𝓛, l) of lists of numbers is the list (𝓛, Γ) of sets. -/
theorem chksD_append (m : ℕ) (L : List (List ℕ)) (l : List ℕ) : chksD m (L ++ [l]) = chksD m L ++ [Fld.setD m l] := by
  simp [chksD]

/-- The two forms of a list of checks have the same length. -/
theorem length_chksD (m : ℕ) (L : List (List ℕ)) : (chksD m L).length = L.length := by
  simp [chksD]

/-- load(E) is the number of lists that contain the number of E. -/
theorem load_chksD (m : ℕ) (L : List (List ℕ)) (e : Fin m) : load (chksD m L) e = (L.filter fun l => l.contains e.val).length := by
  unfold load chksD
  rw [List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun l _ => ?_
  simp [Fld.setD]

/-- The sum of a list of values at 0, …, m − 1 is the sum over `Fin m`. -/
theorem sum_map_range (m : ℕ) (g : ℕ → ℕ) : ((List.range m).map g).sum = ∑ e : Fin m, g e.val := by
  rw [← Finset.sum_range]
  induction m with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

/-- Σ_E 2^load(E) is `loadSum`. -/
theorem sum_load (m : ℕ) (L : List (List ℕ)) : ∑ e : Fin m, (2 : ℚ) ^ load (chksD m L) e = (loadSum m L : ℚ) := by
  unfold loadSum
  rw [sum_map_range]
  push_cast
  exact sum_congr rfl fun e _ => by rw [load_chksD]

/-- A list of distinct numbers below m has as many members as its set of clauses. -/
theorem card_setD (m : ℕ) (l : List ℕ) (h1 : l.Nodup) (h2 : ∀ E ∈ l, E < m) : #(Fld.setD m l) = l.length := by
  have : (Fld.setD m l).map Fin.valEmbedding = l.toFinset := by
    ext E
    simp only [Fld.setD, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, List.mem_toFinset]
    constructor
    · rintro ⟨e, he, rfl⟩; exact he
    · intro hE; exact ⟨⟨E, h2 E hE⟩, hE, rfl⟩
  rw [← card_map Fin.valEmbedding, this, List.toFinset_card_of_nodup h1]

/-! ### Υ as a fraction -/

/-- The denominator of Υ for a list of r checks. -/
@[expose] def den (nb β rb tb r : ℕ) : ℚ := 3 ^ r * 2 ^ (β - 1) * 2 ^ tb * (15 * nb) ^ (rb - r)

/-- The denominator is positive, for n̄ ≥ 1. -/
theorem den_pos (nb β rb tb r : ℕ) (hnb : 1 ≤ nb) : 0 < den nb β rb tb r := by
  have : (0 : ℚ) < nb := by exact_mod_cast hnb
  unfold den; positivity

/-- Υ(𝓛) is `upsNum` over the denominator, for n̄ ≥ 1. -/
theorem ups_eq {X : Type} [Fintype X] (m : ℕ) (V : X → Finset (Fin m)) (nb β rb tb : ℕ) (L : List (List ℕ)) (hnb : 1 ≤ nb) :
    Ups V nb β rb tb (chksD m L) = (upsNum m nb β rb tb (Xsum V nb (chksD m L)) L : ℚ) / den nb β rb tb L.length := by
  have h0 : (0 : ℚ) < nb := by exact_mod_cast hnb
  unfold Ups upsNum den pp
  rw [sum_load, length_chksD]
  have h1 : (1 + 16 / (15 * (nb : ℚ))) = (15 * nb + 16) / (15 * nb) := by field_simp
  rw [h1, div_pow, div_pow]
  push_cast
  field_simp

/-! ### The first member with the smallest key -/

/-- One step of `argminD`, written with `Option.elim`. -/
@[expose] def stepD (key : List ℕ → ℤ) (best : Option (List ℕ × ℤ)) (l : List ℕ) : Option (List ℕ × ℤ) :=
  best.elim (some (l, key l)) fun b => if key l < b.2 then some (l, key l) else some b

/-- `argminD` is the fold of `stepD`. -/
theorem argminD_eq (key : List ℕ → ℤ) (fam : List (List ℕ)) : argminD key fam = (fam.foldl (stepD key) none).elim [] fun b => b.1 := by
  unfold argminD
  congr 2
  funext best l
  cases best <;> rfl

/-- The fold of `stepD` from a pair (l₀, key l₀) ends in a pair (l, key l), where l is l₀ or a
member of the list, and key l is at most key l₀ and at most the keys of all members. -/
theorem fold_stepD (key : List ℕ → ℤ) : ∀ (fam : List (List ℕ)) (b : List ℕ × ℤ), b.2 = key b.1 →
    ∃ c, fam.foldl (stepD key) (some b) = some c ∧ c.2 = key c.1 ∧ (c.1 = b.1 ∨ c.1 ∈ fam) ∧ c.2 ≤ b.2 ∧ ∀ l ∈ fam, c.2 ≤ key l := by
  intro fam
  induction fam with
  | nil => intro b hb; exact ⟨b, rfl, hb, Or.inl rfl, le_refl _, fun l h => by simp at h⟩
  | cons a t ih =>
    intro b hb
    rw [List.foldl_cons]
    by_cases h : key a < b.2
    · have e : stepD key (some b) a = some (a, key a) := by simp [stepD, h]
      obtain ⟨c, h1, h2, h3, h4, h5⟩ := ih (a, key a) rfl
      refine ⟨c, by rw [e, h1], h2, Or.inr ?_, by simp only at h4; omega, ?_⟩
      · rcases h3 with h3 | h3
        · rw [h3]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ h3
      · intro l hl
        rcases List.mem_cons.1 hl with rfl | hl
        · exact h4
        · exact h5 l hl
    · have e : stepD key (some b) a = some b := by simp [stepD, h]
      obtain ⟨c, h1, h2, h3, h4, h5⟩ := ih b hb
      refine ⟨c, by rw [e, h1], h2, h3.imp id (List.mem_cons_of_mem _), h4, ?_⟩
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · omega
      · exact h5 l hl

/-- On a list that is not empty, `argminD` returns a member with the smallest key. -/
theorem argminD_spec (key : List ℕ → ℤ) (fam : List (List ℕ)) (h : fam ≠ []) : argminD key fam ∈ fam ∧ ∀ l ∈ fam, key (argminD key fam) ≤ key l := by
  rw [argminD_eq]
  cases fam with
  | nil => exact absurd rfl h
  | cons a t =>
    rw [List.foldl_cons]
    have e : stepD key none a = some (a, key a) := rfl
    obtain ⟨c, h1, h2, h3, h4, h5⟩ := fold_stepD key t (a, key a) rfl
    rw [e, h1]
    simp only [Option.elim_some]
    refine ⟨?_, ?_⟩
    · rcases h3 with h3 | h3
      · rw [h3]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h3
    · intro l hl
      rw [← h2]
      rcases List.mem_cons.1 hl with rfl | hl
      · exact h4
      · exact h5 l hl

/-! ### The loop -/

section Loop

variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (n nb rb tb : ℕ) (fam : List (List ℕ))

/-- What holds of every list the loop passes through: its checks are candidates, and as a list of
sets it is reached by the algorithm of Step 2 of Appendix D (`Reached`). -/
@[expose] def Inv (L : List (List ℕ)) : Prop :=
  (∀ l ∈ L, l ∈ fam) ∧ Reached V nb (beta n m nb) rb tb (univ : Finset (Fin fam.length)) (fun i => Fld.setD m (fam.get i)) (chksD m L)

/-- The hypotheses of `StSearchD` on the parameters and on the candidates. -/
structure Hyp (X : Type) [Fintype X] (m n nb rb tb : ℕ) (fam : List (List ℕ)) : Prop where
  hX : Fintype.card X ≤ 2 ^ n
  hnb : 1 ≤ nb
  hrb : IsRb (beta n m nb) rb
  htb : IsTb m nb rb tb
  hne : fam ≠ []
  hinc : ∀ l ∈ fam, l.Pairwise (· < ·) ∧ ∀ E ∈ l, E < m
  hF : IsFamily nb (univ : Finset (Fin fam.length)) (fun i => Fld.setD m (fam.get i))

variable {V n nb rb tb fam}

/-- Under `Hyp`, the bounds of Step 2 on the number of checks, their sizes and the loads pass from
sets to lists of numbers, for a list of candidates. -/
theorem structD_of (H : Hyp X m n nb rb tb fam) (L : List (List ℕ)) (hm : ∀ l ∈ L, l ∈ fam)
    (h : (chksD m L).length ≤ rb ∧ (∀ Λ ∈ chksD m L, nb * #Λ ≤ 16 * Fintype.card (Fin m)) ∧ ∀ e : Fin m, load (chksD m L) e ≤ tb + 2) :
    StructD m nb rb tb L := by
  refine ⟨by simpa [length_chksD] using h.1, fun l hl => ?_, fun E hE => ?_⟩
  · obtain ⟨h1, h2⟩ := H.hinc l (hm l hl)
    refine ⟨h1, h2, ?_⟩
    have h3 := h.2.1 (Fld.setD m l) (List.mem_map_of_mem hl)
    rwa [card_setD m l (h1.imp fun h => Nat.ne_of_lt h) h2, Fintype.card_fin] at h3
  · have := h.2.2 ⟨E, hE⟩
    rwa [load_chksD] at this

/-- The bounds of Step 2 on a list of checks, first case, under `Hyp`: a list with `Inv`. -/
theorem structD_inv (H : Hyp X m n nb rb tb fam) (L : List (List ℕ)) (hL : Inv V n nb rb tb fam L) : StructD m nb rb tb L := by
  refine structD_of H L hL.1 ?_
  have := stepChoice.structure_ X (Fin m) (Fin fam.length) V n nb rb tb univ (fun i => Fld.setD m (fam.get i)) (chksD m L) (chksD m L) H.hX H.hnb
  rw [Fintype.card_fin] at this ⊢
  exact this H.hrb H.htb H.hF hL.2 (Or.inl rfl)

/-- The bounds of Step 2 on a list of checks, second case, under `Hyp`: a list with `Inv` and X > 0,
and one more candidate. -/
theorem structD_more (H : Hyp X m n nb rb tb fam) (L : List (List ℕ)) (hL : Inv V n nb rb tb fam L) (hpos : 0 < Xsum V nb (chksD m L)) (l : List ℕ) (hl : l ∈ fam) :
    StructD m nb rb tb (L ++ [l]) := by
  refine structD_of H (L ++ [l]) ?_ ?_
  · intro l' h'
    rcases List.mem_append.1 h' with h' | h'
    · exact hL.1 l' h'
    · rw [List.mem_singleton.1 h']; exact hl
  · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
    have := stepChoice.structure_ X (Fin m) (Fin fam.length) V n nb rb tb univ (fun i => Fld.setD m (fam.get i)) (chksD m L) (chksD m (L ++ [fam.get i])) H.hX H.hnb
    rw [Fintype.card_fin] at this ⊢
    exact this H.hrb H.htb H.hF hL.2 (Or.inr ⟨hpos, i, mem_univ i, chksD_append m L _⟩)

/-- Under `Hyp`, one round keeps `Inv`; it leaves a list with X = 0 as it is and makes a list with X >
0 longer by one check. Here `evX` returns X(𝓛) on every list with these bounds (`StructD`). -/
theorem round_inv (H : Hyp X m n nb rb tb fam) (evX : List (List ℕ) → ℤ) (hev : ∀ L, StructD m nb rb tb L → evX L = Xsum V nb (chksD m L))
    (L : List (List ℕ)) (hL : Inv V n nb rb tb fam L) :
    Inv V n nb rb tb fam (roundD evX fam m nb (beta n m nb) rb tb L) ∧
      (Xsum V nb (chksD m L) = 0 → roundD evX fam m nb (beta n m nb) rb tb L = L) ∧
      (Xsum V nb (chksD m L) ≠ 0 → (roundD evX fam m nb (beta n m nb) rb tb L).length = L.length + 1) := by
  unfold roundD
  rw [hev L (structD_inv H L hL)]
  by_cases h0 : Xsum V nb (chksD m L) = 0
  · rw [if_pos h0]; exact ⟨hL, fun _ => rfl, fun h => absurd h0 h⟩
  · rw [if_neg h0]
    have hpos : 0 < Xsum V nb (chksD m L) := lt_of_le_of_ne (StepChoice.Xsum_nonneg V nb _) (Ne.symm h0)
    obtain ⟨hmem, hmin⟩ := argminD_spec (fun l => upsNum m nb (beta n m nb) rb tb (evX (L ++ [l])) (L ++ [l])) fam H.hne
    generalize argminD (fun l => upsNum m nb (beta n m nb) rb tb (evX (L ++ [l])) (L ++ [l])) fam = a at hmem hmin
    have hups : ∀ l ∈ fam, Ups V nb (beta n m nb) rb tb (chksD m L ++ [Fld.setD m l]) =
        (upsNum m nb (beta n m nb) rb tb (evX (L ++ [l])) (L ++ [l]) : ℚ) / den nb (beta n m nb) rb tb (L.length + 1) := by
      intro l hl
      rw [hev _ (structD_more H L hL hpos l hl), ← chksD_append, ups_eq m V nb _ rb tb _ H.hnb, List.length_append, List.length_singleton]
    refine ⟨⟨?_, ?_⟩, fun h => absurd h h0, fun _ => by simp⟩
    · intro l' h'
      rcases List.mem_append.1 h' with h' | h'
      · exact hL.1 l' h'
      · rw [List.mem_singleton.1 h']; exact hmem
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hmem
      rw [chksD_append]
      refine Reached.step (Γ := fun i => Fld.setD m (fam.get i)) (chksD m L) i hL.2 hpos (mem_univ i) fun u' _ => ?_
      rw [hups _ hmem, hups _ (List.get_mem fam u')]
      refine div_le_div_of_nonneg_right ?_ (den_pos nb _ rb tb _ H.hnb).le
      exact_mod_cast hmin _ (List.get_mem fam u')

/-- Under `Hyp`, after j rounds the list has `Inv`, and X = 0 or it has j checks. Here `evX` returns
X(𝓛) on every list with these bounds (`StructD`), and the word of every such list fits under the
pad. -/
theorem fold_inv (H : Hyp X m n nb rb tb fam) (pad : U) (evX : List (List ℕ) → ℤ) (hev : ∀ L, StructD m nb rb tb L → evX L = Xsum V nb (chksD m L))
    (hpad : ∀ L, StructD m nb rb tb L → len L ≤ pad.length) (j : ℕ) :
    Inv V n nb rb tb fam ((List.range j).foldl (fun L _ => cap pad [] (roundD evX fam m nb (beta n m nb) rb tb L)) (cap pad [] [])) ∧
      (Xsum V nb (chksD m ((List.range j).foldl (fun L _ => cap pad [] (roundD evX fam m nb (beta n m nb) rb tb L)) (cap pad [] []))) = 0 ∨
        ((List.range j).foldl (fun L _ => cap pad [] (roundD evX fam m nb (beta n m nb) rb tb L)) (cap pad [] [])).length = j) := by
  induction j with
  | zero =>
    have e : cap pad ([] : List (List ℕ)) [] = [] := by unfold cap; split <;> rfl
    simp only [List.range_zero, List.foldl_nil, e]
    exact ⟨⟨fun l h => by simp at h, Reached.nil⟩, Or.inr rfl⟩
  | succ j ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize (List.range j).foldl (fun L _ => cap pad [] (roundD evX fam m nb (beta n m nb) rb tb L)) (cap pad [] []) = L at ih
    obtain ⟨h1, h2, h3⟩ := round_inv H evX hev L ih.1
    rw [cap_eq (hpad _ (structD_inv H _ h1))]
    refine ⟨h1, ?_⟩
    by_cases h0 : Xsum V nb (chksD m L) = 0
    · left; rw [h2 h0]; exact h0
    · right; rw [h3 h0]
      rcases ih.2 with h | h
      · exact absurd h h0
      · rw [h]

end Loop

end VariableBound.Search

namespace VariableBound

open Groundwork PaddedDescent.F AppVariables Finset

/-- Step 2, the algorithm as a program: under the hypotheses listed at `StSearchD`, the list that
`searchD` finds has the bounds of Step 2 (`StructD`) and X = 0. -/
theorem stSearchD : StSearchD := by
  intro X _ m V n nb rb tb pad evX fam hX hnb hrb htb hne hinc hF hev hpad
  have H : Search.Hyp X m n nb rb tb fam := ⟨hX, hnb, hrb, htb, hne, hinc, hF⟩
  obtain ⟨h1, h2⟩ := Search.fold_inv H pad evX hev hpad rb
  refine ⟨Search.structD_inv H _ h1, ?_⟩
  rcases h2 with h2 | h2
  · exact h2
  · have := stepChoice.ends X (Fin m) (Fin fam.length) V n nb rb tb univ (fun i => Fld.setD m (fam.get i)) (chksD m (searchD pad evX fam m nb (beta n m nb) rb tb)) hX hnb
    rw [Fintype.card_fin] at this
    exact this hrb htb hF h1.2 (by rw [Search.length_chksD]; exact h2)

end VariableBound
