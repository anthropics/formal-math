/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.CodingDefs
public import QueryMachines.Comb
public import Eight.SecNetworks_Clique
public import Value.Clique
import Mathlib.Tactic

/-! # Between Definition 3's tables and the tables of this development: proofs

Definition 3: «A setting z_w is encoded by concatenating its K − 1 strings z_w(w')». This
development writes the same setting as the list of K strings with the empty string at w.
* `copyAt_flatten_ofFn`, `length_flatten_ofFn`: concatenating the K strings gives a string of (K − 1)λ
  bits whose copy at w' is the string number w';
* `flatten_copies`: cutting a string of (K − 1)λ bits into its copies and concatenating them gives
  the string back;
* `stAskServes`, `stCliqueValue`, `stToLists`: the three statements of CodingDefs.lean. -/

public section

namespace Printed

open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines

/-! ### Concatenating the K strings -/

/-- The first i of the K strings, of which the one at w is empty and the others have λ bits, have
i·λ bits together, or (i − 1)·λ if w is among them. -/
theorem sum_lengths (w lam i : ℕ) : ((List.range i).map fun u => if u = w then 0 else lam).sum = (if w < i then i - 1 else i) * lam := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rcases lt_trichotomy w i with h | h | h
    · have h1 : w < i + 1 := by omega
      have h2 : i ≠ w := by omega
      rw [if_pos h, if_pos h1, if_neg h2]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    · subst h
      simp
    · have h1 : ¬ w < i + 1 := by omega
      have h0 : ¬ w < i := by omega
      have h2 : i ≠ w := by omega
      rw [if_neg h0, if_neg h1, if_neg h2]
      ring

variable {K lam : ℕ}

/-- The lengths of the K strings. -/
theorem map_length_ofFn (w : Fin K) (θ : Fin K → List Bool) (h : ∀ u, u ≠ w → (θ u).length = lam) (hw : θ w = []) :
    (List.ofFn θ).map List.length = (List.range K).map fun u => if u = w.val then 0 else lam := by
  refine List.ext_getElem (by simp) fun u h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_ofFn, List.getElem_range]
  by_cases e : u = w.val
  · have e' : ∀ p, θ ⟨u, p⟩ = [] := fun p => by rw [show (⟨u, p⟩ : Fin K) = w from Fin.ext e]; exact hw
    rw [if_pos e, e']
    rfl
  · rw [if_neg e]
    exact h _ fun e' => e (congrArg Fin.val e')

/-- The number of bits of the first i strings. -/
theorem take_sum (w : Fin K) (θ : Fin K → List Bool) (h : ∀ u, u ≠ w → (θ u).length = lam) (hw : θ w = []) (i : ℕ) (hi : i ≤ K) :
    (((List.ofFn θ).map List.length).take i).sum = (if w.val < i then i - 1 else i) * lam := by
  rw [map_length_ofFn w θ h hw, ← List.map_take, List.take_range, min_eq_left hi, sum_lengths]

/-- The concatenation has (K − 1)λ bits. -/
theorem length_flatten_ofFn (w : Fin K) (θ : Fin K → List Bool) (h : ∀ u, u ≠ w → (θ u).length = lam) (hw : θ w = []) :
    (List.ofFn θ).flatten.length = (K - 1) * lam := by
  rw [List.length_flatten, map_length_ofFn w θ h hw, sum_lengths, if_pos w.2]

/-- The copy at u of the concatenation is the string number u. -/
theorem copyAt_flatten_ofFn (w : Fin K) (θ : Fin K → List Bool) (h : ∀ u, u ≠ w → (θ u).length = lam) (hw : θ w = []) (u : Fin K) (hu : u ≠ w) :
    copyAt lam w u (List.ofFn θ).flatten = θ u := by
  have hne : u.val ≠ w.val := Fin.val_ne_of_ne hu
  have e1 : (if w.val < u.val + 1 then u.val + 1 - 1 else u.val + 1) * lam = place w u * lam + lam := by
    have : (if w.val < u.val + 1 then u.val + 1 - 1 else u.val + 1) = place w u + 1 := by
      unfold place
      split_ifs <;> omega
    rw [this]
    ring
  have e2 : (if w.val < u.val then u.val - 1 else u.val) * lam = place w u * lam := by
    congr 1
    unfold place
    split_ifs <;> omega
  have h0 := List.drop_take_succ_flatten_eq_getElem (List.ofFn θ) u.val (by simp)
  rw [take_sum w θ h hw (u.val + 1) u.2, take_sum w θ h hw u.val u.2.le, e1, e2] at h0
  rw [copyAt, List.take_drop, h0]
  simp

/-! ### Cutting a string into its copies -/

/-- Two strings of r·λ bits with the same r blocks of λ bits are equal. -/
theorem eq_of_blocks (lam : ℕ) : ∀ (r : ℕ) (z z' : List Bool), z.length = r * lam → z'.length = r * lam → (∀ j < r, block lam j z = block lam j z') → z = z'
  | 0, z, z', h, h', _ => by
    have e : z = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    have e' : z' = [] := List.eq_nil_of_length_eq_zero (by simpa using h')
    rw [e, e']
  | r + 1, z, z', h, h', hb => by
    have e : (r + 1) * lam = r * lam + lam := by ring
    have h0 : z.take lam = z'.take lam := by simpa [block] using hb 0 (by omega)
    have h1 : z.drop lam = z'.drop lam := eq_of_blocks lam r _ _ (by rw [List.length_drop, h, e]; omega) (by rw [List.length_drop, h', e]; omega) fun j hj => by
      have := hb (j + 1) (by omega)
      simp only [block, List.drop_drop] at this ⊢
      rwa [show lam + j * lam = (j + 1) * lam by ring]
    calc z = z.take lam ++ z.drop lam := (List.take_append_drop lam z).symm
      _ = z'.take lam ++ z'.drop lam := by rw [h0, h1]
      _ = z' := List.take_append_drop lam z'

/-- Definition 3, «encoded by concatenating its K − 1 strings»: the copies of a string of (K − 1)λ
bits, concatenated, give the string back. -/
theorem flatten_copies (w : Fin K) {z : List Bool} (hz : z.length = (K - 1) * lam) :
    (List.ofFn fun u : Fin K => if u = w then [] else copyAt lam w u z).flatten = z := by
  have hl : ∀ u : Fin K, u ≠ w → ((fun u : Fin K => if u = w then [] else copyAt lam w u z) u).length = lam := fun u hu => by
    simp only [if_neg hu]
    exact length_copyAt w u hu hz
  have hw : (fun u : Fin K => if u = w then [] else copyAt lam w u z) w = [] := if_pos rfl
  refine eq_of_blocks lam (K - 1) _ _ (length_flatten_ofFn w _ hl hw) hz fun j hj => ?_
  obtain ⟨u, hu, rfl⟩ := place_surj w j hj
  rw [← copyAt_eq_block, ← copyAt_eq_block, copyAt_flatten_ofFn w _ hl hw u hu]
  exact if_neg hu

/-- The query made from (w, z) in this development: the list of the function w' ↦ z_w(w'). -/
theorem toLists_eq (lam : ℕ) (w : Fin K) (z : List Bool) :
    toLists K lam (w.val, z) = (w.val, List.ofFn fun u : Fin K => if u = w then [] else copyAt lam w u z) := by
  unfold toLists
  congr 1
  refine List.ext_getElem (by simp) fun u h1 h2 => ?_
  simp [Fin.ext_iff]

/-- Cutting a setting into its strings, and back. -/
theorem stToLists : StToLists := fun K lam w z hz =>
  ⟨toLists_eq lam w z, fun u hu => length_copyAt w u hu (mem_words.1 hz), by
    rw [toLists_eq]
    exact Prod.ext rfl (flatten_copies w (mem_words.1 hz))⟩

/-! ### The value -/

/-- The value of the network of Definition 3 reads the tables only at strings of (K − 1)λ bits;
there the two ways to write a setting name the same entry. Then the sentence after Definition 3,
«only the terms in which the two copies on every edge agree contribute, and the value is the sum,
over all choices of one string in {0,1}^λ per edge, of ∏_{w∈[K]} W_w evaluated at the strings on the
edges at w» (`Value.stCliqueValue`, proof/networks/Value/Clique.lean). -/
theorem stCliqueValue : StCliqueValue := fun K lam W _ _ => by
  refine (Eq.trans ?_ (Value.stCliqueValue K lam (listTables K W)) : _ = Paper.cliqueValue lam (listTables K W))
  unfold Net.value
  refine sum_congr rfl fun z hz => congrArg₂ (· * ·) (prod_congr rfl fun a _ => ?_) rfl
  have ha : (z a).length = (K - 1) * lam := mem_words.1 (Fintype.mem_piFinset.1 hz a)
  change W a.val (z a) = W a.val (List.ofFn fun u : Fin K => if u = a then [] else copyAt lam a u (z a)).flatten
  rw [flatten_copies a ha]

/-! ### One query, one step -/

/-- The size of a list of K strings of at most λ bits. -/
theorem size_ofFn_le (θ : Fin K → List Bool) (h : ∀ u, (θ u).length ≤ lam) : size (List.ofFn θ) ≤ K * (2 * lam + 2) + 1 := by
  have h1 := List.sum_le_card_nsmul ((List.ofFn θ).map fun x => size x + 1) (2 * lam + 2) (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨u, rfl⟩ : ∃ u, θ u = y := by simpa [List.mem_ofFn] using hy
    have := h u
    rw [size_word]
    omega)
  rw [size_list]
  simpa using h1

/-- An entry below 2^B has size at most B + 1. -/
theorem size_entry {v : ℤ} {B : ℕ} (h : |v| < 2 ^ B) : size v ≤ B + 1 := by
  rw [size_int]
  have h1 : v.natAbs < 2 ^ B := by
    have : ((v.natAbs : ℕ) : ℤ) < ((2 ^ B : ℕ) : ℤ) := by rw [Int.natCast_natAbs]; exact_mod_cast h
    exact_mod_cast this
  have := Nat.size_le.2 h1
  omega

/-- The procedure `askTable`, with the tables built in, answers every well-formed query of this
development in one step. -/
theorem stAskServes : StAskServes := fun C _ K lam B W c hW v θ hθ hv => by
  have hl := length_flatten_ofFn v θ hθ hv
  have hb : |listTables K W v θ| < 2 ^ B := hW v.val v.2 _ (mem_words.2 hl)
  refine ⟨?_, hb.le⟩
  have hO : (fun a : C × IQ => tables K lam W (toTable a.2)) (c, (v.val, List.ofFn θ)) = some (listTables K W v θ) := by
    change (if v.val < K ∧ (List.ofFn θ).flatten.length = (K - 1) * lam then some (W v.val (List.ofFn θ).flatten) else none) = _
    rw [if_pos ⟨v.2, hl⟩]
    rfl
  unfold askTable
  rw [QueryMachine.close_query]
  refine (Stepped.ofOption_runs (g := fun a : C × IQ => tables K lam W (toTable a.2)) (a := (c, (v.val, List.ofFn θ))) hO).mono le_rfl ?_
  have h1 := size_ofFn_le (lam := lam) θ fun u => by
    by_cases e : u = v
    · rw [e, hv]
      exact Nat.zero_le _
    · exact (hθ u e).le
  have h2 := size_fin v
  have h3 := size_entry hb
  simp only [size_prod]
  omega

end Printed
