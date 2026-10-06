/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem21
public import ThreeSumApsp.Sec3.Theorem21b.RepeatedSquaring
public import ThreeSumApsp.Spec.Sec3.Problems

/-!
# Repeated squaring on lists of integers

For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix `⌈log₂ n⌉`
times in the (min,+)-product yields the distance matrix, and all finite entries that occur have
absolute value at most `nU`, where `U` bounds the edge weights. The matrices of the repeated
squaring have entries that may be `+∞`, while a solver for the (min,+)-product works on integers.
Here `+∞` is written as the integer `3nU`.

* `squareList n U ADJ W t` is the list, row by row, after `t` rounds.  A round is a (min,+)-product
  of the list with itself, after which every entry above `nU` is set back to `3nU`.
* One round is right (`Encodes.square`): finite entries have absolute value at most `nU`, so a sum
  with an infinite term is at least `2nU`, and a finite sum is the sum of the two codes.
* By induction the list holds the matrix `minPlusSquares` of the repeated squaring, entry
  by entry (`encodes_squareList`), and after `⌈log₂ n⌉` rounds it holds the distances
  (`squareList_distances`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Entries that may be infinite, as integers -/

/-- The list `L` holds, row by row, the matrix `D`, with `INF` for `+∞`: the code `d.untopD INF` of
an entry `d` is the number itself, or `INF` if `d = +∞`. -/
def Encodes (n : ℕ) (INF : ℤ) (L : List ℤ) (D : Fin n → Fin n → WithTop ℤ) : Prop :=
  ∀ i j : Fin n, entry n L i j = (D i j).untopD INF

/-- Every number above `thr` becomes `INF`. -/
def clip (thr INF x : ℤ) : ℤ := if thr < x then INF else x

/-- A code is at least `-B` if `3B` stands for `+∞` and the numbers are bounded by `B`. -/
private theorem neg_le_untopD {B : ℤ} (hB : 0 ≤ B) {d : WithTop ℤ}
    (hd : ∀ x : ℤ, d = (x : WithTop ℤ) → |x| ≤ B) : -B ≤ d.untopD (3 * B) := by
  cases d with
  | top => rw [WithTop.untopD_top]; omega
  | coe x => exact (abs_le.1 (hd x rfl)).1

/-- If a sum of two entries is `+∞`, then the two codes add up to at least `2B`. -/
private theorem two_mul_le_untopD_add_untopD {B : ℤ} (hB : 0 ≤ B) {d d' : WithTop ℤ}
    (hd : ∀ x : ℤ, d = (x : WithTop ℤ) → |x| ≤ B) (hd' : ∀ x : ℤ, d' = (x : WithTop ℤ) → |x| ≤ B)
    (h : d + d' = ⊤) : 2 * B ≤ d.untopD (3 * B) + d'.untopD (3 * B) := by
  have hlow := neg_le_untopD hB hd
  have hlow' := neg_le_untopD hB hd'
  rcases WithTop.add_eq_top.1 h with rfl | rfl
  · rw [WithTop.untopD_top]; omega
  · rw [WithTop.untopD_top]; omega

/-- If a sum of two entries is a number, then the two codes add up to this number. -/
private theorem untopD_add_untopD_of_coe {INF y : ℤ} {d d' : WithTop ℤ}
    (h : d + d' = (y : WithTop ℤ)) : d.untopD INF + d'.untopD INF = y := by
  obtain ⟨a, b, rfl, rfl, hab⟩ := WithTop.add_eq_coe.1 h
  exact hab

/-! ## The lists of the repeated squaring -/

/-- The weight matrix of the graph (0 on the diagonal), row by row, with `INF` where there is no
edge. -/
def weightList (n : ℕ) (INF : ℤ) (ADJ W : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    if q / n = q % n then 0 else if ADJ.getD q 0 = 1 then W.getD q 0 else INF

/-- The matrix after `t` squarings, row by row, with `3nU` for `+∞`. -/
def squareList (n U : ℕ) (ADJ W : List ℤ) : ℕ → List ℤ
  | 0 => weightList n (3 * (n * U : ℕ)) ADJ W
  | t + 1 =>
    (minPlusList n (squareList n U ADJ W t) (squareList n U ADJ W t)).map
      (clip (n * U : ℕ) (3 * (n * U : ℕ)))

/-- Each list of the repeated squaring has `n²` entries. -/
theorem length_squareList (n U : ℕ) (ADJ W : List ℤ) (t : ℕ) :
    (squareList n U ADJ W t).length = n * n := by
  cases t <;> simp [squareList, weightList, length_minPlusList]

/-- The list of the weights holds the weight matrix of the graph. -/
theorem encodes_weightList (n : ℕ) (INF : ℤ) (ADJ W : List ℤ) :
    Encodes n INF (weightList n INF ADJ W) (weightMatrix (graphOf n ADJ W)) := by
  intro i j
  rw [entry, weightList, List.getD_map_range _ (Nat.mul_add_lt_mul i.isLt j.isLt),
    Nat.mul_add_div_of_lt j.isLt,
    Nat.mul_add_mod_of_lt j.isLt]
  simp only [weightMatrix, Matrix.of_apply, graphOf, Fin.ext_iff]
  split_ifs <;> rfl

/-- **One round.**  If a list holds a matrix `D` whose finite entries are bounded by `B`, with `3B`
for `+∞`, and the finite entries of the (min,+)-product of `D` with itself are bounded by `B` too,
then the (min,+)-product of the list with itself, with every entry above `B` set to `3B`, holds that
product. -/
theorem Encodes.square {n : ℕ} {B : ℤ} (hB : 1 ≤ B) {L : List ℤ}
    {D : Matrix (Fin n) (Fin n) (WithTop ℤ)} (hL : Encodes n (3 * B) L D)
    (hD : ∀ i j (x : ℤ), D i j = (x : WithTop ℤ) → |x| ≤ B)
    (hD' : ∀ i j (x : ℤ), minPlus D D i j = (x : WithTop ℤ) → |x| ≤ B) :
    Encodes n (3 * B) ((minPlusList n L L).map (clip B (3 * B))) (minPlus D D) := by
  intro i j
  have hB0 : 0 ≤ B := by omega
  rw [entry, minPlusList, List.map_map, List.getD_map_range _ (Nat.mul_add_lt_mul i.isLt j.isLt),
    Function.comp_apply, Nat.mul_add_div_of_lt j.isLt, Nat.mul_add_mod_of_lt j.isLt]
  -- The entry `m` of the product of the lists is the smallest sum of two codes, attained at `k₁`.
  obtain ⟨k₁, hk₁, hmin⟩ := exists_minPlusEntry_eq i.pos L L i j
  lift k₁ to Fin n using hk₁
  rw [hL i k₁, hL k₁ j] at hmin
  have hle : ∀ k : Fin n,
      minPlusEntry n L L i j ≤ (D i k).untopD (3 * B) + (D k j).untopD (3 * B) := fun k => by
    rw [← hL i k, ← hL k j]
    exact minPlusEntry_le n L L i j k.isLt
  generalize minPlusEntry n L L i j = m at hmin hle
  -- The entry of the product of the matrices is the smallest sum of two entries, attained at `k₀`.
  have hinf : ∀ k, minPlus D D i j ≤ D i k + D k j := fun k => Finset.inf_le (Finset.mem_univ k)
  obtain ⟨k₀, -, hk₀⟩ : ∃ k₀ ∈ Finset.univ, minPlus D D i j = D i k₀ + D k₀ j :=
    Finset.exists_mem_eq_inf Finset.univ ⟨i, Finset.mem_univ i⟩ fun k => D i k + D k j
  cases hx : minPlus D D i j with
  | top =>
    -- Every sum is `+∞`, so `m ≥ 2B > B`, and `m` is set to `3B`.
    have hbig := two_mul_le_untopD_add_untopD hB0 (hD i k₁) (hD k₁ j) (top_le_iff.1 (hx ▸ hinf k₁))
    rw [WithTop.untopD_top, clip, if_pos (by omega)]
  | coe x =>
    -- The smallest sum is a number `x ≤ B`.  Then `m = x`, and `m` is not changed.
    have hxB := abs_le.1 (hD' i j x hx)
    have hmx : m ≤ x := (hle k₀).trans_eq (untopD_add_untopD_of_coe (hk₀.symm.trans hx))
    have hxm : x ≤ m := by
      cases hy : D i k₁ + D k₁ j with
      | top =>
        -- `x ≤ B ≤ 2B ≤ m`
        have hbig := two_mul_le_untopD_add_untopD hB0 (hD i k₁) (hD k₁ j) hy
        omega
      | coe y =>
        rw [hmin, untopD_add_untopD_of_coe hy]
        exact WithTop.coe_le_coe.1 (hx ▸ hy ▸ hinf k₁)
    rw [WithTop.untopD_coe, clip, if_neg (by omega)]
    omega

/-- The edge weights of the graph read from lists are bounded if the list of the weights is. -/
theorem edgeWeightsBoundedBy_graphOf {n : ℕ} {ADJ W : List ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hW : AbsLe W U) : EdgeWeightsBoundedBy (graphOf n ADJ W) U := by
  intro i j x hx
  rw [graphOf] at hx
  split_ifs at hx
  · obtain rfl := WithTop.coe_injective hx
    exact AbsLe.abs_getD_le hU hW _
  · exact absurd hx WithTop.top_ne_coe

variable {n U : ℕ} {ADJ W : List ℤ}

/-- For Theorem 21(b): the finite entries of the matrices of the repeated squaring have absolute
value at most `nU`. -/
theorem abs_minPlusSquares_le (hW : AbsLe W U) (hc : NoNegativeCycle (graphOf n ADJ W)) (t : ℕ)
    (i j : Fin n) (x : ℤ)
    (hx : minPlusSquares (graphOf n ADJ W) t i j = (x : WithTop ℤ)) : |x| ≤ ((n * U : ℕ) : ℤ) := by
  simpa using theorem_21b_entries_bounded (graphOf n ADJ W) hc (U : ℤ) (by positivity)
    (edgeWeightsBoundedBy_graphOf (by positivity) hW) t i j x hx

/-- **Repeated squaring on lists.**  After `t` rounds the list holds the matrix after `t` squarings
(`minPlusSquares`). -/
theorem encodes_squareList (hn : 1 ≤ n) (hU : 1 ≤ U) (hW : AbsLe W U)
    (hc : NoNegativeCycle (graphOf n ADJ W)) (t : ℕ) :
    Encodes n (3 * (n * U : ℕ)) (squareList n U ADJ W t) (minPlusSquares (graphOf n ADJ W) t) := by
  induction t with
  | zero => exact encodes_weightList _ _ _ _
  | succ t ih =>
    exact Encodes.square (by exact_mod_cast Nat.mul_pos hn hU) ih (abs_minPlusSquares_le hW hc t)
      (abs_minPlusSquares_le hW hc (t + 1))

/-- The entries of the lists of the repeated squaring are bounded by `3nU`. -/
theorem abs_squareList_le (hn : 1 ≤ n) (hU : 1 ≤ U) (hW : AbsLe W U)
    (hc : NoNegativeCycle (graphOf n ADJ W)) (t : ℕ) :
    AbsLe (squareList n U ADJ W t) (3 * (n * U) : ℕ) := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul (length_squareList n U ADJ W t ▸ hq)
  rw [← List.getD_eq_getElem _ 0 hq, ← entry, encodes_squareList hn hU hW hc t ⟨a, ha⟩ ⟨b, hb⟩]
  cases hd : minPlusSquares (graphOf n ADJ W) t ⟨a, ha⟩ ⟨b, hb⟩ with
  | top =>
    rw [WithTop.untopD_top, abs_of_nonneg (by positivity)]
    exact le_of_eq (by push_cast; rfl)
  | coe y =>
    have hy := abs_minPlusSquares_le hW hc t _ _ y hd
    rw [WithTop.untopD_coe]
    omega

/-- **The answer.**  After `⌈log₂ n⌉` rounds the list holds the distances: an entry is `3nU` if and
only if the distance is `+∞`, and it is the distance otherwise. -/
theorem squareList_distances (hn : 1 ≤ n) (hU : 1 ≤ U) (hW : AbsLe W U)
    (hc : NoNegativeCycle (graphOf n ADJ W)) :
    ∃ dist : Fin n → Fin n → WithTop ℤ, IsDistanceMatrix (graphOf n ADJ W) dist ∧ ∀ i j : Fin n,
      (dist i j = ⊤ → entry n (squareList n U ADJ W (Nat.clog 2 n)) i j = 3 * (n * U : ℕ)) ∧
      ∀ z : ℤ, dist i j = (z : WithTop ℤ) →
        entry n (squareList n U ADJ W (Nat.clog 2 n)) i j = z ∧ z ≠ 3 * (n * U : ℕ) := by
  refine ⟨minPlusSquares (graphOf n ADJ W) (Nat.clog 2 n), theorem_21b_repeated_squaring _ hc,
    fun i j => ⟨fun h => ?_, fun z h => ?_⟩⟩
  · rw [encodes_squareList hn hU hW hc _ i j, h, WithTop.untopD_top]
  · rw [encodes_squareList hn hU hW hc _ i j, h, WithTop.untopD_coe]
    have hz := abs_le.1 (abs_minPlusSquares_le hW hc _ i j z h)
    have hpos : 1 ≤ n * U := Nat.mul_pos hn hU
    exact ⟨rfl, by omega⟩

end ThreeSumApsp.Spec
