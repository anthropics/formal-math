/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Field.Search
public import Mathlib.Data.ZMod.Basic

/-! # The list `famD m a` is the family of Lemma 13 (Family of checks)

The field is 𝔽 = `FW g`, the residues modulo X^s + g for the irreducible polynomial found by the
search; its elements are written as strings of s bits by `bitsW g`; ϑ_E is the residue that the word
of the number E stands for. `setD_gamW`: the list `gamW m a g u` lists the set Γ_u
(`AppVariables.Gam`) of the proof of Lemma 13. `stFamD`: from Lemma 13 over an arbitrary field with
2^s elements (`AppVariables.LemFamily`, a hypothesis
here, proved in proof/variables/VariableBound/Family) follows the statement `StFamD` on the list. -/

public section

namespace VariableBound.Fld

open Groundwork Finset Polynomial

/-! ### Two tests on words -/

/-- The first k bits of a word w of n bits are 0, as a test on the list and as a statement on the
places i < n. -/
theorem all_take_iff {n : ℕ} {w : List Bool} (hw : w.length = n) (k : ℕ) :
    ((w.take k).all fun b => !b) = true ↔ ∀ i : Fin n, i.val < k → w.getD i.val false = false := by
  subst hw
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    have h1 : w[i.val] ∈ w.take k := List.mem_take_iff_getElem.2 ⟨i.val, lt_min hi i.isLt, rfl⟩
    have h2 := h _ h1
    rw [List.getD_eq_getElem _ _ i.isLt]
    simpa using h2
  · intro h b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 hb
    have hj' := lt_min_iff.1 hj
    have h2 := h ⟨j, hj'.2⟩ hj'.1
    rw [List.getD_eq_getElem _ _ hj'.2] at h2
    simpa using h2

/-- The sum over the places of the products of the bits of two words of n bits is, modulo 2, the
number of places where both bits are set. -/
theorem sum_bitR_mul (n : ℕ) : ∀ x y : List Bool, x.length = n → y.length = n →
    ∑ i : Fin n, bitR (ZMod 2) (x.getD i.val false) * bitR (ZMod 2) (y.getD i.val false) = (((x.zip y).countP fun p => p.1 && p.2 : ℕ) : ZMod 2) := by
  induction n with
  | zero =>
    intro x y hx hy
    rw [List.length_eq_zero_iff.1 hx]
    simp
  | succ n ih =>
    intro x y hx hy
    obtain ⟨a, x, rfl⟩ := List.exists_cons_of_length_eq_add_one hx
    obtain ⟨b, y, rfl⟩ := List.exists_cons_of_length_eq_add_one hy
    have := ih x y (by simpa using hx) (by simpa using hy)
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ, this, List.zip_cons_cons, List.countP_cons]
    cases a <;> cases b <;> simp [bitR, add_comm]

/-- `ipW` is the inner product ⟨·,·⟩ modulo 2 of the proof of Lemma 13, for two words of n bits. -/
theorem ipW_iff {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    ipW x y = true ↔ AppVariables.ip (fun i : Fin n => bitR (ZMod 2) (x.getD i.val false)) (fun i : Fin n => bitR (ZMod 2) (y.getD i.val false)) = 1 := by
  rw [AppVariables.ip, sum_bitR_mul n x y hx hy, ipW, decide_eq_true_iff, ZMod.natCast_eq_one_iff_odd, Nat.odd_iff]

/-! ### The field, ϑ, and the quadruples -/

/-- The ring of residues is finite: its elements are written as strings of s bits. -/
@[instance_reducible] noncomputable def fintypeFW (g : List Bool) : Fintype (FW g) := Fintype.ofEquiv _ (bitsW g).symm.toEquiv

attribute [local instance] fintypeFW

/-- ϑ_E: the residue that the word of the number E stands for; distinct for distinct E < m ≤ 2^s. -/
noncomputable def thetaW (g : List Bool) (m : ℕ) (hm : m ≤ 2 ^ g.length) : Fin m ↪ FW g :=
  ⟨fun E => decW g (toWord g.length E.val), fun E E' h => by
    have h1 := decW_inj g (length_toWord _ _) (length_toWord _ _) h
    exact Fin.ext (toWord_injOn g.length (by simpa using E.isLt.trans_le hm) (by simpa using E'.isLt.trans_le hm) h1)⟩

/-- The quadruple of residues that a quadruple of words stands for. -/
noncomputable def decQ (g : List Bool) (u : List Bool × List Bool × List Bool × List Bool) : FW g × FW g × FW g × FW g :=
  (decW g u.1, decW g u.2.1, decW g u.2.2.1, decW g u.2.2.2)

/-- Distinct quadruples of words of s bits stand for distinct quadruples of residues. -/
theorem decQ_inj (g : List Bool) {u u' : List Bool × List Bool × List Bool × List Bool}
    (hu : u ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length)
    (hu' : u' ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length) (h : decQ g u = decQ g u') : u = u' := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_quad.1 hu
  obtain ⟨h1', h2', h3', h4'⟩ := mem_quad.1 hu'
  simp only [decQ, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4⟩ := h
  exact Prod.ext (decW_inj g h1 h1' e1) (Prod.ext (decW_inj g h2 h2' e2) (Prod.ext (decW_inj g h3 h3' e3) (decW_inj g h4 h4' e4)))

/-- Every quadruple of residues is written by a quadruple of words of s bits. -/
theorem decQ_surj (g : List Bool) (w : FW g × FW g × FW g × FW g) :
    ∃ u ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length, decQ g u = w := by
  obtain ⟨w1, w2, w3, w4⟩ := w
  obtain ⟨u1, h1, rfl⟩ := decW_surj g w1
  obtain ⟨u2, h2, rfl⟩ := decW_surj g w2
  obtain ⟨u3, h3, rfl⟩ := decW_surj g w3
  obtain ⟨u4, h4, rfl⟩ := decW_surj g w4
  exact ⟨(u1, u2, u3, u4), mem_quad.2 ⟨h1, h2, h3, h4⟩, rfl⟩

/-! ### The listed sets are the sets Γ_u -/

/-- Let X^s + g be irreducible, s ≥ 1 the length of g, and m ≤ 2^s. For a quadruple u of words of s
bits, the list `gamW m a g u` lists the set Γ_u of Lemma 13 (Family of checks), for v = 2^a. -/
theorem setD_gamW (g : List Bool) [Fact (Irreducible (modP g))] (hg : 1 ≤ g.length) (m a : ℕ) (hm : m ≤ 2 ^ g.length)
    {u : List Bool × List Bool × List Bool × List Bool} (hu : u ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length) :
    setD m (gamW m a g u) = AppVariables.Gam (bitsW g) (thetaW g m hm) a (decQ g u) := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_quad.1 hu
  ext E
  simp only [setD, gamW, AppVariables.Gam, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_filter, List.mem_range, E.isLt, Bool.and_eq_true]
  refine and_congr ?_ ?_
  · have hw : (xorW (mulW g u.1 (toWord g.length E.val)) u.2.1).length = g.length := by
      rw [length_xorW, length_mulW h1, h2, min_self]
    have hd : (decQ g u).1 * thetaW g m hm E + (decQ g u).2.1 = decW g (xorW (mulW g u.1 (toWord g.length E.val)) u.2.1) := by
      rw [decW_xorW g (by rw [length_mulW h1, h2]), decW_mulW g h1]; rfl
    rw [all_take_iff hw, hd]
    refine forall₂_congr fun i _ => ?_
    rw [bitsW_decW g _ hw]
    cases (xorW (mulW g u.1 (toWord g.length E.val)) u.2.1).getD i.val false <;> simp [bitR]
  · have hp : (decQ g u).2.2.1 ^ E.val = decW g (powW g u.2.2.1 E.val) := (decW_powW hg _ _).symm
    rw [ipW_iff (length_powW hg _ _) h4, hp]
    have e1 : (bitsW g (decW g (powW g u.2.2.1 E.val)) : Fin g.length → ZMod 2) = fun i => bitR (ZMod 2) ((powW g u.2.2.1 E.val).getD i.val false) :=
      funext fun i => bitsW_decW g _ (length_powW hg _ _) i
    have e2 : (bitsW g (decQ g u).2.2.2 : Fin g.length → ZMod 2) = fun i => bitR (ZMod 2) (u.2.2.2.getD i.val false) :=
      funext fun i => bitsW_decW g _ h4 i
    rw [e1, e2]

/-- Let X^s + g be irreducible, s ≥ 1 the length of g, and m ≤ 2^s. For a quadruple u of words of s
bits, the list `gamW m a g u` has |Γ_u| members. -/
theorem length_gamW (g : List Bool) [Fact (Irreducible (modP g))] (hg : 1 ≤ g.length) (m a : ℕ) (hm : m ≤ 2 ^ g.length)
    {u : List Bool × List Bool × List Bool × List Bool} (hu : u ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length) :
    (gamW m a g u).length = #(AppVariables.Gam (bitsW g) (thetaW g m hm) a (decQ g u)) := by
  rw [← setD_gamW g hg m a hm hu, card_setD (gamW_nodup m a g u) (gamW_lt m a g u)]

/-! ### The statement -/

/-- Lemma 13 (Family of checks) for the list made with any word g of s bits for which X^s + g is
irreducible: let 1 ≤ a, 2^a ≤ m and 16m ≤ 2^s < 32m, and let Lemma 13 hold over every field with 2^s
elements. Then the list is not empty, has fewer than (32m)⁴ members, every member is an increasing
list of numbers below m, and the members, indexed by their places, have (a), (b), (c) for v = 2^a. -/
theorem fam_of (h14 : AppVariables.LemFamily) (m a : ℕ) (g : List Bool) (ha : 1 ≤ a) (hm : 2 ^ a ≤ m) (hs1 : 16 * m ≤ 2 ^ g.length) (hs2 : 2 ^ g.length < 32 * m)
    (hirr : Irreducible (modP g)) (Lst : List (List ℕ))
    (hLst : Lst = ((wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length).filter fun u =>
      decide (2 ^ a * (gamW m a g u).length ≤ 16 * m)).map (gamW m a g)) :
    Lst ≠ [] ∧ Lst.length < (32 * m) ^ 4 ∧ (∀ l ∈ Lst, l.Pairwise (· < ·) ∧ l.Nodup ∧ ∀ E ∈ l, E < m) ∧
    AppVariables.IsFamily (2 ^ a) (Finset.univ : Finset (Fin Lst.length)) fun i => setD m (Lst.get i) := by
  subst hLst
  have : Fact (Irreducible (modP g)) := ⟨hirr⟩
  have hm1 : 1 ≤ m := Nat.one_le_two_pow.trans hm
  have hg : 1 ≤ g.length := by
    by_contra h
    have h0 : g.length = 0 := by omega
    rw [h0] at hs1
    omega
  have hm2 : m ≤ 2 ^ g.length := by omega
  obtain ⟨hpos, hcard, hfam⟩ := h14 (FW g) m g.length a (bitsW g) (thetaW g m hm2) ha hm hs1 hs2
  have key := isFamily_list (AppVariables.Om (bitsW g) (thetaW g m hm2) a) (AppVariables.Gam (bitsW g) (thetaW g m hm2) a)
    ((wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length).filter fun u => decide (2 ^ a * (gamW m a g u).length ≤ 16 * m))
    (decQ g) (gamW m a g) ((nodup_quad g.length).filter _)
    (fun u hu u' hu' h => decQ_inj g (List.mem_of_mem_filter hu) (List.mem_of_mem_filter hu') h)
    (fun w => by
      simp only [AppVariables.Om, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_filter, decide_eq_true_eq]
      constructor
      · intro hw
        obtain ⟨u, hu, rfl⟩ := decQ_surj g w
        exact ⟨u, ⟨hu, by rw [length_gamW g hg m a hm2 hu]; exact hw⟩, rfl⟩
      · rintro ⟨u, ⟨hu, hw⟩, rfl⟩
        rw [← length_gamW g hg m a hm2 hu]; exact hw)
    (fun u hu => setD_gamW g hg m a hm2 (List.mem_of_mem_filter hu)) hfam
  refine ⟨?_, by rw [← key.1]; exact hcard, fun l hl => ?_, key.2⟩
  · refine List.ne_nil_of_length_pos ?_
    rw [← key.1]
    exact hpos
  · obtain ⟨u, _, rfl⟩ := List.mem_map.1 hl
    exact ⟨gamW_sorted m a g u, gamW_nodup m a g u, gamW_lt m a g u⟩

/-- Lemma 13 (Family of checks) for the listed family `famD m a`, from Lemma 13 over an arbitrary
field with 2^s elements. -/
theorem stFamD (h14 : AppVariables.LemFamily) : StFamD := by
  intro m a ha hm
  have hm1 : 1 ≤ m := Nat.one_le_two_pow.trans hm
  obtain ⟨hlen, hirr⟩ := modW_spec (one_le_sD hm1)
  refine fam_of h14 m a (modW (sD m)) ha hm (by rw [hlen]; exact sD_le m) (by rw [hlen]; exact sD_lt hm1) hirr (famD m a) ?_
  rw [hlen]
  exact famD_eq m a

end VariableBound.Fld
