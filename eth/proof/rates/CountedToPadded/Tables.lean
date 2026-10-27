/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedToPadded.Defs
public import ToTuring.Poly.IsPoly
import PaddedDescent.F.FuelCert
import PaddedDescent.F.CertNet
import ToTuring.Poly.NetFun

/-! # Tables that are written out

Proof of `BitsOfTablesFacts` (Defs.lean); the size of tables is at most the length of their word;
`entry` is polynomial-time; the number of bits of the entries and the length of the word of the
tables are computed in unary. -/

public section

namespace QueryMachines.Bridge.Proof

open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed

/-! ### The largest number of a list, at least 1 -/

/-- The largest number of a list, at least 1, is at least 1. -/
theorem one_le_foldr_max (l : List ℕ) : 1 ≤ l.foldr max 1 := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact ih.trans (le_max_right _ _)

/-- It is at least every number of the list. -/
theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 1 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- It is at most every c ≥ 1 that bounds the list. -/
theorem foldr_max_le {l : List ℕ} {c : ℕ} (hc : 1 ≤ c) (h : ∀ x ∈ l, x ≤ c) : l.foldr max 1 ≤ c := by
  induction l with
  | nil => exact hc
  | cons a l ih => exact max_le (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ### The entries -/

/-- An entry of a list with a value to fall back on is that value or stands in the list. -/
theorem getD_eq_or_mem {γ : Type} (l : List γ) (i : ℕ) (d : γ) : l.getD i d = d ∨ l.getD i d ∈ l := by
  by_cases h : i < l.length
  · right; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · left; exact List.getD_eq_default _ _ (not_lt.1 h)

/-- An entry is 0 or stands in the tables. -/
theorem entry_eq_or_mem (T : Tab) (x : TableQuery) : entry T x = 0 ∨ ∃ r ∈ T, entry T x ∈ r := by
  unfold entry
  rcases getD_eq_or_mem T x.1 [] with h | h
  · left; rw [h]; rfl
  · rcases getD_eq_or_mem (T.getD x.1 []) (ofWord x.2) 0 with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨_, h, h'⟩

/-! ### Size and word -/

/-- If every entry of a list has size at most the length of its word, so has the list. -/
theorem size_le_len_list {γ : Type} [Enc γ] [HasSize γ] (l : List γ) (h : ∀ a ∈ l, size a ≤ len a) : size l ≤ len l := by
  induction l with
  | nil => rw [len_nil]; simp [size_list]
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [size_list] at h2
    rw [len_cons, size_list, List.map_cons, List.sum_cons]
    omega

/-- The size of tables is at most the length of their word. (`Carried` is the inequality in the
other direction.) -/
theorem size_le_len_tab (T : Tab) : size T ≤ len T :=
  size_le_len_list T fun r _ => size_le_len_list r fun z _ => by rw [size_int, len_int]; omega

/-- An entry is no larger than the tables. -/
theorem size_entry_le (T : Tab) (x : TableQuery) : size (entry T x) ≤ size T := by
  have mem_le : ∀ {γ : Type} [HasSize γ] (l : List γ) (a : γ), a ∈ l → size a + 1 ≤ size l := by
    intro γ _ l a ha
    induction l with
    | nil => cases ha
    | cons b l ih =>
      rw [size_list, List.map_cons, List.sum_cons]
      rcases List.mem_cons.1 ha with rfl | ha
      · omega
      · have := ih ha; rw [size_list] at this; omega
  rcases entry_eq_or_mem T x with h | ⟨r, hr, h⟩
  · rw [h, size_list]; simp
  · have := mem_le r _ h; have := mem_le T r hr; omega

/-! ### Certificates -/

/-- `entry` is polynomial-time. -/
theorem entry_poly : PolyT fun p : Tab × TableQuery => entry p.1 p.2 := by unfold entry; fun_prop

/-- The certificate of `lookup`. -/
@[expose, instance_reducible] def lookupIsPoly : IsPolyT lookup := IsPolyT.ofFun entry_poly

/-- The largest number with the start value 1 is the largest number, with the start value 0, of the
list with 1 put behind it. -/
theorem bitsOfTables_eq (T : Tab) : bitsOfTables T = ((T.flatten.map fun z : ℤ => z.natAbs.size) ++ [1]).foldr max 0 := by simp [bitsOfTables]

/-- The number of bits of the entries is polynomial-time. -/
theorem bitsOfTables_poly : PolyT bitsOfTables :=
  (NetE.foldr_max_polyT (l := fun T : Tab => (T.flatten.map fun z : ℤ => z.natAbs.size) ++ [1]) (by fun_prop)).congr fun T => (bitsOfTables_eq T).symm

/-- The length of the word of the tables, written out. -/
theorem len_tab_eq (T : Tab) : len T = (T.map fun r : List ℤ => (r.map fun z : ℤ => 3 * (Nat.bits z.natAbs).length + 5 + 2).sum + 2 + 2).sum + 2 := by
  have hz : ∀ z : ℤ, len z + 2 = 3 * (Nat.bits z.natAbs).length + 5 + 2 := fun z => by rw [len_int, Nat.size_eq_bits_len]
  have hr : ∀ r : List ℤ, len r + 2 = (r.map fun z : ℤ => 3 * (Nat.bits z.natAbs).length + 5 + 2).sum + 2 + 2 := fun r => by rw [len_list]; simp only [hz]
  rw [len_list]; simp only [hr]

/-- The length of the word of the tables, in unary. -/
theorem len_tab_unary : Unary fun T : Tab => len T := by
  have h : Unary fun T : Tab => (T.map fun r : List ℤ => (r.map fun z : ℤ => 3 * (Nat.bits z.natAbs).length + 5 + 2).sum + 2 + 2).sum + 2 := by fun_prop
  exact PolyT.congr h fun T => congrArg (fun n => List.replicate n ()) (len_tab_eq T).symm

/-- The number of bits of the entries is at most the length of the word of the tables. -/
theorem bitsOfTables_le_len (T : Tab) : bitsOfTables T ≤ len T := by
  refine foldr_max_le ((by norm_num : 1 ≤ 2).trans (two_le_len_list T)) fun s hs => ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hs
  obtain ⟨r, hr, hzr⟩ := List.mem_flatten.1 hz
  have h1 := len_le_of_mem hzr
  have h2 := len_le_of_mem hr
  rw [len_int] at h1
  omega

/-- The number of bits of the entries, in unary. -/
theorem bitsOfTables_unary : Unary bitsOfTables := Unary.of_le len_tab_unary bitsOfTables_poly bitsOfTables_le_len

end QueryMachines.Bridge.Proof

namespace QueryMachines.Bridge

open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed Proof

/-- B′ is at least 1 and bounds every entry; under `WFe` it is at most B + 1. -/
theorem bitsOfTablesFacts : BitsOfTablesFacts := by
  intro T
  refine ⟨one_le_foldr_max _, fun x => ?_, fun K lam B lu h => ?_⟩
  · rcases entry_eq_or_mem T x with h | ⟨r, hr, h⟩
    · rw [h]; simp
    · have h1 : (entry T x).natAbs.size ≤ bitsOfTables T :=
        le_foldr_max (List.mem_map.2 ⟨_, List.mem_flatten.2 ⟨r, hr, h⟩, rfl⟩)
      have h2 : (entry T x).natAbs < 2 ^ bitsOfTables T := lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) h1)
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h2
  · refine foldr_max_le (Nat.succ_le_succ (Nat.zero_le _)) fun s hs => ?_
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hs
    obtain ⟨r, hr, hzr⟩ := List.mem_flatten.1 hz
    have := h.1.abs_le r hr z hzr
    exact Nat.size_le.2 (lt_of_le_of_lt this (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self B)))

end QueryMachines.Bridge
