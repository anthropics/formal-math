/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements

/-!
# Theorem 21(b): repeated squaring computes the distances

For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix `⌈log₂ n⌉`
times in the (min,+)-product yields the distance matrix, and all finite entries that occur have
absolute value at most `nU`, where `U` bounds the edge weights (`theorem_21b_repeated_squaring`,
`theorem_21b_entries_bounded`).

Under this hypothesis, after `t` squarings the entry at `(i, j)` is the least weight of a walk from
`i` to `j` with at most `2^t` edges: it is the weight of such a walk (`exists_walk_of_entry`) and at
most the weight of every such walk (`entry_le_walkWeight`).  Cutting closed pieces out of a walk
shows that fewer than `n` edges are enough (`exists_short_walk`), and a walk of finite weight with
`k` edges has weight at most `kU` in absolute value (`abs_walkWeight_le`).
-/

public section

namespace ThreeSumApsp

namespace Theorem21

/-- The end of a walk that is followed by a second walk. -/
private theorem walkEnd_append {n : ℕ} (i : Fin n) (p q : List (Fin n)) :
    walkEnd i (p ++ q) = walkEnd (walkEnd i p) q := by
  induction p generalizing i with
  | nil => rfl
  | cons j p ih => exact ih j

/-- The weight of a walk that is followed by a second walk is the sum of the two weights. -/
private theorem walkWeight_append {R : Type} [AddCommGroup R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (i : Fin n) (p q : List (Fin n)) :
    walkWeight w i (p ++ q) = walkWeight w i p + walkWeight w (walkEnd i p) q := by
  induction p generalizing i with
  | nil => simp [walkWeight, walkEnd]
  | cons j p ih => simp [walkWeight, walkEnd, ih, add_assoc]

/-- Every entry of the matrix after `t` squarings is the weight of a walk with at most `2^t` edges.
-/
theorem exists_walk_of_entry {R : Type} [AddCommGroup R] [LinearOrder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (t : ℕ) (i j : Fin n) :
    ∃ rest : List (Fin n), walkEnd i rest = j ∧ rest.length ≤ 2 ^ t ∧
      walkWeight w i rest = minPlusSquares w t i j := by
  induction t generalizing i j with
  | zero =>
    by_cases hij : i = j
    · subst hij
      exact ⟨[], rfl, by simp, by simp [walkWeight, minPlusSquares, weightMatrix]⟩
    · exact ⟨[j], rfl, by simp, by simp [walkWeight, minPlusSquares, weightMatrix, hij]⟩
  | succ t ih =>
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf Finset.univ ⟨i, Finset.mem_univ i⟩
      fun k => minPlusSquares w t i k + minPlusSquares w t k j
    obtain ⟨p, hpend, hplen, hpweight⟩ := ih i k
    obtain ⟨q, hqend, hqlen, hqweight⟩ := ih k j
    refine ⟨p ++ q, ?_, ?_, ?_⟩
    · rw [walkEnd_append, hpend, hqend]
    · rw [List.length_append, pow_succ]
      omega
    · rw [walkWeight_append, hpend, hpweight, hqweight]
      exact hk.symm

/-- A walk with at least `n` edges visits some vertex twice: it consists of a walk `p`, a closed
walk `c` with at least one edge, and a walk `q`. -/
private theorem exists_closed_piece {n : ℕ} (i : Fin n) (rest : List (Fin n))
    (h : n ≤ rest.length) :
    ∃ p c q : List (Fin n),
      rest = p ++ c ++ q ∧ c ≠ [] ∧ walkEnd (walkEnd i p) c = walkEnd i p := by
  -- Among the `rest.length + 1` vertices that the walk visits, two are equal.
  obtain ⟨a, b, hab, hb, hrep⟩ : ∃ a b : ℕ, a < b ∧ b ≤ rest.length ∧
      walkEnd i (rest.take a) = walkEnd i (rest.take b) := by
    obtain ⟨a, b, hne, hrep⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (rest.length + 1) => walkEnd i (rest.take k)) (by simp; omega)
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact ⟨a, b, hlt, by omega, hrep⟩
    · exact ⟨b, a, hlt, by omega, hrep.symm⟩
  have htake : rest.take b = rest.take a ++ (rest.drop a).take (b - a) := by
    rw [← List.take_add, Nat.add_sub_cancel' hab.le]
  refine ⟨rest.take a, (rest.drop a).take (b - a), rest.drop b, ?_, ?_, ?_⟩
  · rw [← htake, List.take_append_drop]
  · refine List.ne_nil_of_length_pos ?_
    rw [List.length_take, List.length_drop]
    omega
  · rw [← walkEnd_append, ← htake, hrep]

/-- If no closed walk has negative weight, every walk can be replaced by a walk with the same ends,
fewer than `n` edges, no more edges than before, and no larger weight: cut out closed pieces. -/
theorem exists_short_walk {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) (i : Fin n) (rest : List (Fin n)) :
    ∃ rest' : List (Fin n), walkEnd i rest' = walkEnd i rest ∧ rest'.length < n ∧
      rest'.length ≤ rest.length ∧ walkWeight w i rest' ≤ walkWeight w i rest := by
  induction hlen : rest.length using Nat.strong_induction_on generalizing rest with
  | _ len ih =>
    rcases lt_or_ge rest.length n with hshort | hlong
    · exact ⟨rest, rfl, hshort, hlen.le, le_rfl⟩
    · -- The walk is `p`, then the closed walk `c`, then `q`; go on with `p`, then `q`.
      obtain ⟨p, c, q, rfl, hc, hclosed⟩ := exists_closed_piece i rest hlong
      have hend : walkEnd i (p ++ q) = walkEnd i (p ++ c ++ q) := by
        simp only [walkEnd_append, hclosed]
      have hweight : walkWeight w i (p ++ q) ≤ walkWeight w i (p ++ c ++ q) := by
        simp only [walkWeight_append, walkEnd_append, hclosed]
        gcongr
        exact le_add_of_nonneg_right (hw _ _ hclosed)
      have hless : (p ++ q).length < len := by
        have := List.length_pos_iff.mpr hc
        simp only [List.length_append] at hlen ⊢
        omega
      obtain ⟨rest', hend', hlt, hle, hweight'⟩ := ih _ hless (p ++ q) rfl
      exact ⟨rest', hend'.trans hend, hlt, by omega, hweight'.trans hweight⟩

/-- If no closed walk has negative weight, the entry after `t` squarings is at most the weight of
every walk with at most `2^t` edges. -/
theorem entry_le_walkWeight {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
    {n : ℕ} (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) (t : ℕ) (i : Fin n)
    (rest : List (Fin n)) (hlen : rest.length ≤ 2 ^ t) :
    minPlusSquares w t i (walkEnd i rest) ≤ walkWeight w i rest := by
  induction t generalizing i rest with
  | zero =>
    match rest, hlen with
    | [], _ => simp [walkWeight, walkEnd, minPlusSquares, weightMatrix]
    | [j], _ =>
      by_cases hij : i = j
      · -- The diagonal entry is 0, and a loop has weight at least 0.
        subst hij
        have h := hw i [i] rfl
        simpa [walkEnd, minPlusSquares, weightMatrix] using h
      · simp [walkWeight, walkEnd, minPlusSquares, weightMatrix, hij]
    | _ :: _ :: _, h => simp at h
  | succ t ih =>
    -- The walk is `p`, its first `2^t` edges, followed by `q`, the others.
    obtain ⟨p, q, rfl, hp, hq⟩ : ∃ p q, rest = p ++ q ∧ p.length ≤ 2 ^ t ∧ q.length ≤ 2 ^ t := by
      refine ⟨rest.take (2 ^ t), rest.drop (2 ^ t), (List.take_append_drop _ _).symm,
        List.length_take_le _ _, ?_⟩
      rw [List.length_drop]
      rw [pow_succ] at hlen
      omega
    rw [walkEnd_append, walkWeight_append]
    calc minPlusSquares w (t + 1) i (walkEnd (walkEnd i p) q)
        ≤ minPlusSquares w t i (walkEnd i p)
            + minPlusSquares w t (walkEnd i p) (walkEnd (walkEnd i p) q) :=
          Finset.inf_le (f := fun k =>
            minPlusSquares w t i k + minPlusSquares w t k (walkEnd (walkEnd i p) q))
            (Finset.mem_univ _)
      _ ≤ walkWeight w i p + walkWeight w (walkEnd i p) q := add_le_add (ih i p hp) (ih _ q hq)

/-- If the edge weights are at most `U` in absolute value, a walk of finite weight with `k` edges
has weight at most `kU` in absolute value. -/
theorem abs_walkWeight_le {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (U : R) (hwU : EdgeWeightsBoundedBy w U) (i : Fin n)
    (rest : List (Fin n)) (x : R) (hx : walkWeight w i rest = (x : WithTop R)) :
    |x| ≤ rest.length • U := by
  induction rest generalizing i x with
  | nil =>
    obtain rfl : x = 0 := (WithTop.coe_injective (hx : ((0 : R) : WithTop R) = x)).symm
    simp
  | cons j rest ih =>
    obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.mp hx
    rw [← hab, List.length_cons, succ_nsmul']
    exact (abs_add_le a b).trans (add_le_add (hwU i j a ha.symm) (ih j b hb.symm))

end Theorem21

/-- For **Theorem 21(b)**, repeated squaring: if no closed walk has negative weight, then squaring
the weight matrix `⌈log₂ n⌉` times in the (min,+)-product yields the distance matrix.
(`Nat.clog 2 n` is `⌈log₂ n⌉`.)  Stated for weights in any linearly ordered commutative group, so
that it covers integer and real weights. -/
theorem theorem_21b_repeated_squaring {R : Type} [AddCommGroup R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : ℕ} (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) :
    IsDistanceMatrix w (minPlusSquares w (Nat.clog 2 n)) := by
  intro i j
  constructor
  · obtain ⟨rest, hend, -, hweight⟩ := Theorem21.exists_walk_of_entry w (Nat.clog 2 n) i j
    exact ⟨rest, hend, hweight⟩
  · rintro x ⟨rest, rfl, rfl⟩
    -- A shortest walk needs fewer than `n ≤ 2^⌈log₂ n⌉` edges.
    obtain ⟨rest', hend, hlt, -, hle⟩ := Theorem21.exists_short_walk w hw i rest
    rw [← hend]
    exact (Theorem21.entry_le_walkWeight w hw _ i rest'
      (hlt.le.trans (Nat.le_pow_clog (by norm_num) n))).trans hle

/-- For **Theorem 21(b)**, repeated squaring: a bound on the entries.  If the edge weights have
absolute value at most `U`, every finite entry of every matrix of the repeated squaring has absolute
value at most `nU`; with `U = n^ν` this is `n^{ν+1}`.

NOTE.  A missing edge has the weight `⊤` here, while the (min,+)-product of Theorem 21(b) is on
integer matrices with entries of absolute value at most `U` (`IsMinPlusProduct`).  Nothing is stated
here about replacing `⊤` by a large number. -/
theorem theorem_21b_entries_bounded {R : Type} [AddCommGroup R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : ℕ} (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) (U : R)
    (hU : 0 ≤ U) (hwU : EdgeWeightsBoundedBy w U) (t : ℕ) (i j : Fin n) (x : R)
    (hx : minPlusSquares w t i j = (x : WithTop R)) : |x| ≤ n • U := by
  -- The entry is the weight of a walk with at most `2^t` edges.  Cutting it short gives a walk with
  -- fewer than `n` edges, whose weight is no larger, and no smaller because the entry is a minimum.
  obtain ⟨rest, hend, hlen, hweight⟩ := Theorem21.exists_walk_of_entry w t i j
  obtain ⟨rest', hend', hlt, hlen', hle⟩ := Theorem21.exists_short_walk w hw i rest
  have hge := Theorem21.entry_le_walkWeight w hw t i rest' (hlen'.trans hlen)
  rw [hend', hend, hx] at hge
  have hshort : walkWeight w i rest' = (x : WithTop R) :=
    le_antisymm (hle.trans (hweight.trans hx).le) hge
  exact (Theorem21.abs_walkWeight_le w U hwU i rest' x hshort).trans
    (nsmul_le_nsmul_left hU hlt.le)

end ThreeSumApsp
