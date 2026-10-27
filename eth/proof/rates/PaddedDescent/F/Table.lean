/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import ToTuring.EncLemmas
public import StepMachines.Prog.SideBasics
public import StepMachines.Prog.GridDefs

/-! # Explicit tables (StT1, StT2, StT3a, StT3b, StT3c)

Z reads an instance only at well-formed queries; a table made by `tabulate` answers every
well-formed query like the function it was made
from; it is well-formed (`WF`); the word of a well-formed instance is short; its entries are bounded
in the sense of `BoundedInst`. -/

public section

namespace PaddedDescent.F.Table

open Groundwork Groundwork.Prog Finset

/-- T1: Z reads an instance only at well-formed queries. -/
theorem stT1 : StT1 := by
  intro K ℓ R R' h
  unfold Inst.ZW
  refine Finset.sum_congr rfl fun Λ hΛ => Finset.prod_congr rfl fun v _ => h v _ ⟨fun u hu => ?_, ?_⟩
  · have h1 := ((mem_tuples _ _ _ _).1 hΛ (pr v u)).1 (min_lt_max.2 hu.symm)
    exact mem_words.1 h1
  · exact ((mem_tuples _ _ _ _).1 hΛ (pr v v)).2 (by simp [pr])

/-- The j-th block of a concatenation of words of length ℓ. -/
theorem block_flatten {ℓ : ℕ} : ∀ (L : List (List Bool)) (j : ℕ), (∀ w ∈ L, w.length = ℓ) → j < L.length →
    block ℓ j L.flatten = L.getD j []
  | [], j, _, hj => by simp at hj
  | a :: L, 0, h, _ => by
    have ha : a.length = ℓ := h a List.mem_cons_self
    simp [block, ha]
  | a :: L, j + 1, h, hj => by
    have ha : a.length = ℓ := h a List.mem_cons_self
    have ih := block_flatten L j (fun w hw => h w (List.mem_cons_of_mem _ hw)) (by simpa using hj)
    have e : (j + 1) * ℓ = a.length + j * ℓ := by rw [ha]; ring
    unfold block at ih ⊢
    rw [List.flatten_cons, e, ← List.drop_drop, List.drop_left, ih]
    simp

/-- The numbers 0, 1, … without v. -/
def skip (v j : ℕ) : ℕ := if j < v then j else j + 1

/-- An empty word may be left out of a concatenation. -/
theorem flatten_skip (t : ℕ → List Bool) : ∀ (K v : ℕ), v < K → t v = [] →
    ((List.range K).map t).flatten = ((List.range (K - 1)).map fun j => t (skip v j)).flatten
  | 0, v, h, _ => by omega
  | K + 1, v, h, hv => by
    rcases Nat.lt_or_ge v K with h1 | h1
    · have ih := flatten_skip t K v h1 hv
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at ih ⊢
      rw [List.range_succ, List.map_append, List.flatten_append, ih, List.range_succ (n := K'), List.map_append,
        List.flatten_append]
      have : skip v K' = K' + 1 := by unfold skip; rw [if_neg (by omega)]
      simp [this]
    · have e : v = K := by omega
      subst e
      rw [List.range_succ, List.map_append, List.flatten_append]
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hv, List.append_nil, Nat.add_sub_cancel]
      congr 1
      refine List.map_congr_left fun j hj => ?_
      unfold skip
      rw [if_pos (List.mem_range.1 hj)]

/-- T2: a table made by `tabulate` answers every well-formed query like F. -/
theorem stT2 : StT2 := by
  intro pad K ℓ F h v θ hq
  obtain ⟨hθ, hv⟩ := hq
  obtain ⟨t, ht⟩ : ∃ t : ℕ → List Bool, t = fun u => (List.ofFn θ).getD u [] := ⟨_, rfl⟩
  have htθ : ∀ u : Fin K, t u.1 = θ u := fun u => by rw [ht]; simp [u.2]
  have hof : List.ofFn θ = (List.range K).map t := by
    refine List.ext_getElem (by simp) fun u h1 h2 => ?_
    have hu : u < K := by simpa using h1
    simp [ht, hu]
  obtain ⟨L, hL⟩ : ∃ L, L = (List.range (K - 1)).map fun j => t (skip v.1 j) := ⟨_, rfl⟩
  have hskip : ∀ j, j < K - 1 → skip v.1 j < K ∧ skip v.1 j ≠ v.1 := by
    intro j hj; unfold skip; split_ifs <;> omega
  have hLlen : ∀ w ∈ L, w.length = ℓ := by
    intro w hw
    rw [hL] at hw
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
    obtain ⟨h1, h2⟩ := hskip j (List.mem_range.1 hj)
    rw [htθ ⟨_, h1⟩]
    exact hθ _ fun e => h2 (congrArg Fin.val e)
  have hfl : (List.ofFn θ).flatten = L.flatten := by
    rw [hof, hL]; exact flatten_skip t K v.1 v.2 (by rw [htθ v]; exact hv)
  have hLl : L.length = K - 1 := by rw [hL]; simp
  have hwl : L.flatten.length = (K - 1) * ℓ := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => ℓ) hLlen, List.map_const', List.sum_replicate, hLl,
      smul_eq_mul]
  have hlt : ofWord (List.ofFn θ).flatten < 2 ^ ((K - 1) * ℓ) := by rw [hfl, ← hwl]; exact ofWord_lt _
  have hun : unflat K ℓ v.1 (toWord ((K - 1) * ℓ) (ofWord (List.ofFn θ).flatten)) = List.ofFn θ := by
    rw [hfl, ← hwl, toWord_ofWord, hof]
    unfold unflat
    refine List.map_congr_left fun u hu => ?_
    have huK : u < K := List.mem_range.1 hu
    split_ifs with h1 h2
    · rw [h1, htθ v, hv]
    · rw [block_flatten L u hLlen (by omega), hL]
      have : u < K - 1 := by omega
      simp [List.getD_eq_getElem?_getD, this, skip, h2]
    · have h3 : u - 1 < K - 1 := by omega
      rw [block_flatten L (u - 1) hLlen (by omega), hL]
      have h4 : ¬ u - 1 < v.1 := by omega
      have h5 : u - 1 + 1 = u := by omega
      simp [List.getD_eq_getElem?_getD, h3, skip, h4, h5]
  unfold look tabulate
  have hrow : ((List.range K).map fun v' => (rng pad (2 ^ ((K - 1) * ℓ))).map fun i =>
      F (v', unflat K ℓ v' (toWord ((K - 1) * ℓ) i))).getD v.1 [] =
      (rng pad (2 ^ ((K - 1) * ℓ))).map fun i => F (v.1, unflat K ℓ v.1 (toWord ((K - 1) * ℓ) i)) := by
    simp [List.getD_eq_getElem?_getD, v.2]
  simp only [hrow]
  rw [rng_eq h]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.getD_some]
  rw [hun]

/-- `unflat` of a word of the right length is a well-formed query. -/
theorem unflat_wf {K ℓ : ℕ} (v : Fin K) {w : List Bool} (hw : w.length = (K - 1) * ℓ) :
    ∃ θ : Fin K → List Bool, unflat K ℓ v.1 w = List.ofFn θ ∧ WFQ ℓ v θ := by
  refine ⟨fun u => if u.1 = v.1 then [] else block ℓ (if u.1 < v.1 then u.1 else u.1 - 1) w, ?_, fun u hu => ?_, by simp⟩
  · unfold unflat
    rw [map_range_eq_ofFn]
  · have hne : u.1 ≠ v.1 := fun e => hu (Fin.ext e)
    simp only [hne, if_false]
    refine length_block ?_
    rw [hw]
    refine Nat.mul_le_mul_right _ ?_
    have := u.2
    have := v.2
    split_ifs <;> omega

/-- T3a: a tabulated instance is well-formed. -/
theorem stT3a : StT3a := by
  intro pad K ℓ Λ B F h h1 hΛ hF
  refine ⟨by simpa using h1, by simpa using hΛ, by simp [tabulate], fun r hr => ?_, fun r hr z hz => ?_⟩
  · simp only [tabulate, List.mem_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    simp [rng_eq h]
  · simp only [tabulate, List.mem_map, List.mem_range] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hz
    obtain ⟨θ, e, h2⟩ := unflat_wf (ℓ := ℓ) ⟨v, hv⟩ (length_toWord ((K - 1) * ℓ) i)
    have := hF ⟨v, hv⟩ θ h2
    simp only at e
    rw [e]
    exact this

theorem len_ints_le {B : ℕ} : ∀ (r : List ℤ), (∀ z ∈ r, z.natAbs ≤ 2 ^ B) → len r ≤ r.length * (3 * B + 10) + 2
  | [], _ => by simp [len_nil]
  | z :: r, h => by
    have ih := len_ints_le r fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hz : Nat.size z.natAbs ≤ B + 1 :=
      Nat.size_le.2 ((h z List.mem_cons_self).trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self B)))
    rw [len_cons, len_int, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem len_rows_le {X : ℕ} : ∀ (T : List (List ℤ)), (∀ r ∈ T, len r ≤ X + 2) → len T ≤ T.length * (X + 4) + 2
  | [], _ => by simp [len_nil]
  | r :: T, h => by
    have ih := len_rows_le T fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hr := h r List.mem_cons_self
    rw [len_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- T3b: the word of a well-formed instance is short. -/
theorem stT3b : StT3b := by
  intro K Λ B I h
  obtain ⟨lu, T⟩ := I
  have h1 : len T ≤ T.length * (2 ^ ((K - 1) * lu.length) * (3 * B + 10) + 4) + 2 :=
    len_rows_le T fun r hr => by
      have := len_ints_le r (h.abs_le r hr)
      rwa [h.row_len r hr] at this
  have h2 : T.length = K := h.rows
  have h3 : lu.length ≤ Λ := h.lam_le
  have h4 : 2 ^ ((K - 1) * lu.length) ≤ 2 ^ ((K - 1) * Λ) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h3)
  have h5 : K * (2 ^ ((K - 1) * lu.length) * (3 * B + 10) + 4) ≤ K * (2 ^ ((K - 1) * Λ) * (3 * B + 10) + 4) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ h4) _)
  rw [h2] at h1
  rw [len_pair, len_units]
  unfold instLen
  omega

/-- T3c: the entries of a well-formed instance are bounded, in the form that `sideN_sized` asks for. -/
theorem stT3c : StT3c := by
  intro K Λ B I h v θ _ _
  unfold instOf look
  rw [Int.abs_eq_natAbs]
  have key : ∀ (r : List ℤ) (i : ℕ), (∀ z ∈ r, z.natAbs ≤ 2 ^ B) → (r.getD i 0).natAbs ≤ 2 ^ B := by
    intro r i hr
    rcases Nat.lt_or_ge i r.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi]; exact hr _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ hi]; simp
  have hrow : ∀ z ∈ I.2.getD v.1 [], z.natAbs ≤ 2 ^ B := by
    have hv : v.1 < I.2.length := by rw [h.rows]; exact v.2
    rw [List.getD_eq_getElem _ _ hv]
    exact h.abs_le _ (List.getElem_mem hv)
  exact_mod_cast key _ _ hrow

end PaddedDescent.F.Table
