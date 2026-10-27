/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Field.Ring
public import VariableBound.Field.Quot
public import VariableBound.Field.Transfer

/-! # «An irreducible polynomial of degree s is found by search» (proof of Lemma 13, Appendix D)

The programs of Defs.lean compute in the ring `FW g` of residues modulo X^s + g (`decW_xorW`,
`decW_mulW`, `decW_powW`). The test `irrW g`, «every word other than 0 has an inverse», holds
exactly if
X^s + g is irreducible (`irrW_iff`). `modW s` is found by a search with this test over the words of
s bits; as an irreducible polynomial of every degree s ≥ 1 exists, it has s bits and X^s + `modW s`
is irreducible (`modW_spec`). -/

public section

namespace VariableBound.Fld

open Polynomial

/-! ### The programs compute in the ring of residues -/

/-- `xorW` is the sum of residues, for words of the same length. -/
theorem decW_xorW (g : List Bool) {x y : List Bool} (h : x.length = y.length) : decW g (xorW x y) = decW g x + decW g y :=
  decR_xorW (two_eq_zero_FW g) _ x y h

/-- The word 0 stands for the residue 0. -/
theorem decW_zeroW (g : List Bool) : decW g (zeroW g) = 0 := decR_zeroW _ _

/-- The word 1 stands for the residue 1. -/
theorem decW_oneW (g : List Bool) : decW g (oneW g) = 1 := decR_oneW _ _

/-- `mulW g` is the product of residues, for a word x as long as g and any word y. -/
theorem decW_mulW (g : List Bool) {x : List Bool} (hx : x.length = g.length) (y : List Bool) : decW g (mulW g x y) = decW g x * decW g y :=
  decR_mulW (two_eq_zero_FW g) (root_pow g) hx y

/-- `powW g` is the power of residues, for g not empty and any word u. -/
theorem decW_powW {g : List Bool} (hg : 1 ≤ g.length) (u : List Bool) (e : ℕ) : decW g (powW g u e) = decW g u ^ e :=
  decR_powW (two_eq_zero_FW g) (root_pow g) hg u e

/-! ### The test -/

/-- What the test says: every word x as long as g is the word 0 or has a word y as long as g with
x·y = 1. -/
theorem irrW_eq_true {g : List Bool} : irrW g = true ↔
    ∀ x : List Bool, x.length = g.length → x = zeroW g ∨ ∃ y : List Bool, y.length = g.length ∧ mulW g x y = oneW g := by
  simp only [irrW, List.all_eq_true, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq, mem_wordsL]

/-- For a word g of s ≥ 1 bits, the test holds exactly if X^s + g is irreducible. -/
theorem irrW_iff {g : List Bool} (hg : 1 ≤ g.length) : irrW g = true ↔ Irreducible (modP g) := by
  rw [irrW_eq_true]
  constructor
  · intro h
    refine irreducible_of_inv g hg fun z hz => ?_
    obtain ⟨x, hx, rfl⟩ := decW_surj g z
    rcases h x hx with rfl | ⟨y, _, hy⟩
    · exact absurd (decW_zeroW g) hz
    · exact ⟨decW g y, by rw [← decW_mulW g hx, hy, decW_oneW]⟩
  · intro h x hx
    have : Fact (Irreducible (modP g)) := ⟨h⟩
    by_cases h0 : x = zeroW g
    · exact Or.inl h0
    · right
      have hne : decW g x ≠ 0 := fun e => h0 (decW_inj g hx (length_zeroW g) (by rw [e, decW_zeroW]))
      obtain ⟨y, hy, hyz⟩ := decW_surj g (decW g x)⁻¹
      refine ⟨y, hy, decW_inj g (length_mulW hx y) (length_oneW hg) ?_⟩
      rw [decW_mulW g hx, hyz, decW_oneW, mul_inv_cancel₀ hne]

/-! ### The search -/

/-- For s ≥ 1 the search succeeds: `modW s` is a word of s bits, and X^s + `modW s` is irreducible. -/
theorem modW_spec {s : ℕ} (hs : 1 ≤ s) : (modW s).length = s ∧ Irreducible (modP (modW s)) := by
  obtain ⟨g₀, hg₀, hirr⟩ := exists_irreducible_modP s hs
  have h₀ : irrW g₀ = true := (irrW_iff (by omega)).2 hirr
  cases hf : (wordsL s).find? irrW with
  | none => exact absurd h₀ (by simpa using List.find?_eq_none.1 hf g₀ (mem_wordsL.2 hg₀))
  | some g =>
    have h1 : g.length = s := mem_wordsL.1 (List.mem_of_find?_eq_some hf)
    have h2 : irrW g = true := List.find?_some hf
    have e : modW s = g := by rw [modW, hf]; rfl
    rw [e]
    exact ⟨h1, (irrW_iff (by omega)).1 h2⟩

end VariableBound.Fld
