/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.RingOps
public import ThreeSumApsp.Spec.Sec3.Theorem17.Strassen

/-!
# Strassen's algorithm in seven uniform phases: the pure side

An entry of a matrix is a vector of `p` numbers, an element of the ring ℤ[x]/(x^p - 1), whose
product is `cconv p`; `vlinList s A B` is the list `A + s B`, which the routine vlin writes.  The
routine for Strassen's algorithm clears the four quarters of the result and then runs seven
phases.  A phase forms `S = A₁ + s_A A₂`, `T = B₁ + s_B B₂`, `M = S · T` (recursively) and adds
`s₁ M` and `s₂ M` to two quarters of the result; the signs are 1, -1 or 0.  This file has the facts
about lists that the proof about the routine uses:

* lengths (`length_vlinList`, `length_quarter`, `length_strassenList`);
* magnitudes: for operands bounded by `α` and `β`, all numbers that are formed at level `j` are
  bounded by `strassenBound p j α β = 16^j p α β` (`absLe_strassenList`);
* the seven phases give `strassenList` (`strassenList_succ_eq_phases`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The list that vlin writes is as long as its operands. -/
theorem length_vlinList (s : ℤ) {A B : List ℤ} {n : ℕ} (hA : A.length = n) (hB : B.length = n) :
    (vlinList s A B).length = n := by
  simp [vlinList, hA, hB]

/-- With the sign 0 the first operand is kept. -/
theorem vlinList_zero {A B : List ℤ} (h : A.length = B.length) : vlinList 0 A B = A := by
  apply List.ext_getElem
  · simp [vlinList, h]
  · intro i h1 h2
    simp [vlinList]

/-- With the sign 0 and twice the same operand, the operand is kept. -/
theorem vlinList_zero_self (A : List ℤ) : vlinList 0 A A = A := vlinList_zero rfl

/-- Adding a list to zeros gives the list. -/
theorem vlinList_zeros_left {q : ℕ} {B : List ℤ} (h : B.length = q) :
    vlinList 1 (zeros q) B = B := by
  apply List.ext_getElem
  · simp [vlinList, zeros, h]
  · intro i h1 h2
    simp [vlinList, zeros]

/-- The bounds of the two operands add up. -/
theorem _root_.ThreeSumApsp.AbsLe.vlinList {s a b : ℤ} {A B : List ℤ} (hA : AbsLe A a)
    (hB : AbsLe B b)
    (hs : |s| ≤ 1) : AbsLe (vlinList s A B) (a + b) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hiA : i < A.length := by simp only [Sec3.vlinList, List.length_zipWith] at hi; omega
  have hiB : i < B.length := by simp only [Sec3.vlinList, List.length_zipWith] at hi; omega
  simp only [Sec3.vlinList, List.getElem_zipWith]
  have hsy : |s * B[i]| ≤ b := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (hB.getElem hiB)
  exact le_trans (abs_add_le _ _) (add_le_add (hA.getElem hiA) hsy)

/-- A larger bound. -/
theorem _root_.ThreeSumApsp.AbsLe.trans_le {l : List ℤ} {a b : ℤ} (h : AbsLe l a) (hab : a ≤ b) :
    AbsLe l b := fun x hx => (h x hx).trans hab

/-- Zeros are bounded by 0. -/
theorem absLe_zeros (q : ℕ) : AbsLe (zeros q) 0 := by
  intro x hx
  simp only [zeros, List.mem_replicate] at hx
  simp [hx.2]

/-- A quarter of a list of 4 q numbers has q numbers. -/
theorem length_quarter {q t : ℕ} {l : List ℤ} (h : l.length = 4 * q) (ht : t < 4) :
    (quarter q t l).length = q := by
  have h1 : (t + 1) * q ≤ 4 * q := Nat.mul_le_mul_right q (by omega)
  have h2 : (t + 1) * q = t * q + q := by ring
  rw [quarter, List.length_take, List.length_drop, h]
  omega

/-- A bound for a list is a bound for its quarters. -/
theorem _root_.ThreeSumApsp.AbsLe.quarter {q t : ℕ} {l : List ℤ} {a : ℤ} (h : AbsLe l a) :
    AbsLe (quarter q t l) a :=
  fun x hx => h x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

/-- A quarter of a segment is a segment. -/
theorem _root_.Light.Seg.quarter {μ : ℕ → ℤ} {a q t : ℕ} {l : List ℤ} (h : Seg μ a l) :
    Seg μ (a + t * q) (quarter q t l) :=
  (h.drop (t * q)).take q

/-- A quarter of an array of 4 q numbers is an array of q numbers. -/
theorem _root_.Light.ArrayAt.quarter {μ : ℕ → ℤ} {a q t top : ℕ} {l : List ℤ} {U : ℤ}
    (h : ArrayAt μ a l (4 * q) U top) (ht : t < 4) :
    ArrayAt μ (a + t * q) (quarter q t l) q U top :=
  h.drop_take (Nat.mul_add_le_mul ht le_rfl)

/-- The list A + s B, once it stands at dst, is an array, and the bounds of A and B add up. -/
theorem _root_.Light.ArrayAt.vlinList {μ μ' : ℕ → ℤ} {a dst n top top' : ℕ} {A B : List ℤ}
    {s U V W : ℤ} (hA : ArrayAt μ a A n U top) (lenB : B.length = n) (leB : AbsLe B V)
    (hs : |s| ≤ 1) (seg : Seg μ' dst (vlinList s A B)) (hW : U + V ≤ W := by light_arith)
    (below : dst + n ≤ top' := by light_arith) : ArrayAt μ' dst (vlinList s A B) n W top' :=
  { len := length_vlinList s hA.len lenB, seg, bound := (hA.bound.vlinList leB hs).trans_le hW
    below }

/-- A product in the ring has p numbers. -/
theorem length_cconv (p : ℕ) (A B : List ℤ) : (cconv p A B).length = p := by simp [cconv]

/-- The product of two matrices of 4^j vectors has 4^j vectors. -/
theorem length_strassenList (p : ℕ) :
    ∀ (j : ℕ) (A B : List ℤ), A.length = 4 ^ j * p → B.length = 4 ^ j * p →
      (strassenList p j A B).length = 4 ^ j * p
  | 0, A, B, _, _ => by simp [strassenList, length_cconv]
  | j + 1, A, B, hA, hB => by
    have hA' : A.length = 4 * (4 ^ j * p) := by rw [hA]; ring
    have hB' : B.length = 4 * (4 ^ j * p) := by rw [hB]; ring
    have qa : ∀ t < 4, (quarter (4 ^ j * p) t A).length = 4 ^ j * p :=
      fun t ht => length_quarter hA' ht
    have qb : ∀ t < 4, (quarter (4 ^ j * p) t B).length = 4 ^ j * p :=
      fun t ht => length_quarter hB' ht
    have hs : ∀ X Y : List ℤ, X.length = 4 ^ j * p → Y.length = 4 ^ j * p →
        (strassenList p j X Y).length = 4 ^ j * p := length_strassenList p j
    have ha : ∀ X Y : List ℤ, X.length = 4 ^ j * p → Y.length = 4 ^ j * p →
        (vadd X Y).length = 4 ^ j * p :=
      fun X Y hX hY => by simp [vadd, hX, hY]
    have hb : ∀ X Y : List ℤ, X.length = 4 ^ j * p → Y.length = 4 ^ j * p →
        (vsub X Y).length = 4 ^ j * p :=
      fun X Y hX hY => by simp [vsub, hX, hY]
    simp only [strassenList, List.length_append]
    rw [ha, ha, ha, ha]
    · ring
    all_goals
      repeat' first
        | apply ha | apply hb | apply hs | exact qa _ (by omega) | exact qb _ (by omega)

/-- The product of a phase. -/
def phaseM (p j : ℕ) (sA : ℤ) (A1 A2 : List ℤ) (sB : ℤ) (B1 B2 : List ℤ) : List ℤ :=
  strassenList p j (vlinList sA A1 A2) (vlinList sB B1 B2)

/-- The bound on all the numbers that the routine forms at level `j`, for operands bounded by `α`
and `β`. -/
def strassenBound (p j : ℕ) (α β : ℤ) : ℤ := 16 ^ j * (p * α * β)

/-- The bound is not negative. -/
theorem strassenBound_nonneg {p j : ℕ} {α β : ℤ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ strassenBound p j α β := by
  unfold strassenBound
  positivity

/-- The bound of level j + 1 in terms of the bound of level j, for operands that are sums of two. -/
theorem strassenBound_succ (p j : ℕ) (α β : ℤ) :
    strassenBound p (j + 1) α β = 4 * strassenBound p j (2 * α) (2 * β) := by
  unfold strassenBound
  ring

/-- The bound on the entries of the product of two matrices of zeros and ones. -/
theorem strassenBound_one_one (p K : ℕ) : strassenBound p K 1 1 = ((16 ^ K * p : ℕ) : ℤ) := by
  unfold strassenBound
  push_cast
  ring

/-- The bound is at least the bound α for the first operand. -/
theorem le_strassenBound_left {p j : ℕ} {α β : ℤ} (hp : 1 ≤ p) (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    α ≤ strassenBound p j α β := by
  have hpow : (1 : ℤ) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hα0 : 0 ≤ α := by omega
  calc α = 1 * (1 * α * 1) := by ring
    _ ≤ 16 ^ j * (p * α * β) := by gcongr

/-- The bound is at least the bound β for the second operand. -/
theorem le_strassenBound_right {p j : ℕ} {α β : ℤ} (hp : 1 ≤ p) (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    β ≤ strassenBound p j α β := by
  have hpow : (1 : ℤ) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hβ0 : 0 ≤ β := by omega
  calc β = 1 * (1 * 1 * β) := by ring
    _ ≤ 16 ^ j * (p * α * β) := by gcongr

/-- A product in the ring is bounded by p α β. -/
theorem absLe_cconv {p : ℕ} {A B : List ℤ} {α β : ℤ} (leA : AbsLe A α) (leB : AbsLe B β)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : AbsLe (cconv p A B) (p * α * β) := by
  intro x hx
  rw [cconv_eq_map_convPartialSum] at hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
  have := abs_convPartialSum_le (p := p) leA leB hα hβ r p
  rwa [← mul_assoc] at this

/-- The entries of a sum. -/
theorem _root_.ThreeSumApsp.AbsLe.vadd {X Y : List ℤ} {x y : ℤ} (hX : AbsLe X x) (hY : AbsLe Y y) :
    AbsLe (vadd X Y) (x + y) := by
  rw [← vlinList_one]
  exact hX.vlinList hY (by simp)

/-- The entries of a difference. -/
theorem _root_.ThreeSumApsp.AbsLe.vsub {X Y : List ℤ} {x y : ℤ} (hX : AbsLe X x) (hY : AbsLe Y y) :
    AbsLe (vsub X Y) (x + y) := by
  rw [← vlinList_neg_one]
  exact hX.vlinList hY (by simp)

/-- The entries of a sum of two lists with the same bound. -/
theorem _root_.ThreeSumApsp.AbsLe.vadd_self {X Y : List ℤ} {c : ℤ} (hX : AbsLe X c)
    (hY : AbsLe Y c) :
    AbsLe (vadd X Y) (2 * c) :=
  (hX.vadd hY).trans_le (by omega)

/-- The entries of a difference of two lists with the same bound. -/
theorem _root_.ThreeSumApsp.AbsLe.vsub_self {X Y : List ℤ} {c : ℤ} (hX : AbsLe X c)
    (hY : AbsLe Y c) :
    AbsLe (vsub X Y) (2 * c) :=
  (hX.vsub hY).trans_le (by omega)

/-- The entries of the result of the routine, and of the products of its phases, are bounded. -/
theorem absLe_strassenList (p : ℕ) :
    ∀ (j : ℕ) (A B : List ℤ) (α β : ℤ), AbsLe A α → AbsLe B β → 0 ≤ α → 0 ≤ β →
      AbsLe (strassenList p j A B) (strassenBound p j α β)
  | 0, A, B, α, β, leA, leB, hα, hβ => by
    simpa [strassenList, strassenBound] using absLe_cconv (p := p) leA leB hα hβ
  | j + 1, A, B, α, β, leA, leB, hα, hβ => by
    have ih : ∀ X Y : List ℤ, AbsLe X (2 * α) → AbsLe Y (2 * β) →
        AbsLe (strassenList p j X Y) (strassenBound p j (2 * α) (2 * β)) := fun X Y hX hY =>
      absLe_strassenList p j X Y _ _ hX hY (by omega) (by omega)
    have qa : ∀ t, AbsLe (quarter (4 ^ j * p) t A) α := fun t => leA.quarter
    have qb : ∀ t, AbsLe (quarter (4 ^ j * p) t B) β := fun t => leB.quarter
    have qa2 : ∀ t, AbsLe (quarter (4 ^ j * p) t A) (2 * α) := fun t => (qa t).trans_le (by omega)
    have qb2 : ∀ t, AbsLe (quarter (4 ^ j * p) t B) (2 * β) := fun t => (qb t).trans_le (by omega)
    -- the seven products of Strassen's algorithm
    have m1 := ih _ _ ((qa 0).vadd_self (qa 3)) ((qb 0).vadd_self (qb 3))
    have m2 := ih _ _ ((qa 2).vadd_self (qa 3)) (qb2 0)
    have m3 := ih _ _ (qa2 0) ((qb 1).vsub_self (qb 3))
    have m4 := ih _ _ (qa2 3) ((qb 2).vsub_self (qb 0))
    have m5 := ih _ _ ((qa 0).vadd_self (qa 1)) (qb2 3)
    have m6 := ih _ _ ((qa 2).vsub_self (qa 0)) ((qb 0).vadd_self (qb 1))
    have m7 := ih _ _ ((qa 1).vsub_self (qa 3)) ((qb 2).vadd_self (qb 3))
    have hR : 0 ≤ strassenBound p j (2 * α) (2 * β) :=
      strassenBound_nonneg (by omega) (by omega)
    rw [strassenBound_succ]
    simp only [strassenList]
    intro x hx
    simp only [List.mem_append] at hx
    -- each quadrant of the result is a sum of at most four of them
    rcases hx with ((hx | hx) | hx) | hx
    · exact (((m1.vadd m4).vsub m5).vadd m7).trans_le (by omega) x hx
    · exact (m3.vadd m5).trans_le (by omega) x hx
    · exact (m2.vadd m4).trans_le (by omega) x hx
    · exact (((m1.vsub m2).vadd m3).vadd m6).trans_le (by omega) x hx

/-- The product of a phase on quarters of the operands has the length of a quarter. -/
theorem length_phaseM_quarter {p j : ℕ} {A B : List ℤ} (hA : A.length = 4 * (4 ^ j * p))
    (hB : B.length = 4 * (4 ^ j * p)) (sA sB : ℤ) {t1 t2 t3 t4 : ℕ}
    (ht : t1 < 4 ∧ t2 < 4 ∧ t3 < 4 ∧ t4 < 4 := by omega) :
    (phaseM p j sA (quarter (4 ^ j * p) t1 A) (quarter (4 ^ j * p) t2 A) sB
      (quarter (4 ^ j * p) t3 B) (quarter (4 ^ j * p) t4 B)).length = 4 ^ j * p := by
  obtain ⟨h1, h2, h3, h4⟩ := ht
  exact length_strassenList p j _ _
    (length_vlinList _ (length_quarter hA h1) (length_quarter hA h2))
    (length_vlinList _ (length_quarter hB h3) (length_quarter hB h4))

/-- **The seven phases give Strassen's algorithm.** -/
theorem strassenList_succ_eq_phases (p j : ℕ) (A B : List ℤ) (hA : A.length = 4 ^ (j + 1) * p)
    (hB : B.length = 4 ^ (j + 1) * p) :
    let q := 4 ^ j * p
    let a := fun t => quarter q t A
    let b := fun t => quarter q t B
    let m1 := phaseM p j 1 (a 0) (a 3) 1 (b 0) (b 3)
    let m2 := phaseM p j 1 (a 2) (a 3) 0 (b 0) (b 0)
    let m3 := phaseM p j 0 (a 0) (a 0) (-1) (b 1) (b 3)
    let m4 := phaseM p j 0 (a 3) (a 3) (-1) (b 2) (b 0)
    let m5 := phaseM p j 1 (a 0) (a 1) 0 (b 3) (b 3)
    let m6 := phaseM p j (-1) (a 2) (a 0) 1 (b 0) (b 1)
    let m7 := phaseM p j (-1) (a 1) (a 3) 1 (b 2) (b 3)
    strassenList p (j + 1) A B
      = vlinList 1 (vlinList 0 (vlinList (-1) (vlinList 1 (vlinList 1 (zeros q) m1) m4) m5) m6) m7
        ++ vlinList 1 (vlinList 1 (zeros q) m3) m5
        ++ vlinList 1 (vlinList 1 (zeros q) m2) m4
        ++ vlinList 0 (vlinList 1 (vlinList 1 (vlinList (-1) (vlinList 1 (zeros q) m1) m2) m3) m6)
          m7 := by
  intro q a b m1 m2 m3 m4 m5 m6 m7
  have hA' : A.length = 4 * q := by rw [hA]; ring
  have hB' : B.length = 4 * q := by rw [hB]; ring
  have len1 : m1.length = q := length_phaseM_quarter hA' hB' _ _
  have len2 : m2.length = q := length_phaseM_quarter hA' hB' _ _
  have len3 : m3.length = q := length_phaseM_quarter hA' hB' _ _
  have len4 : m4.length = q := length_phaseM_quarter hA' hB' _ _
  have len5 : m5.length = q := length_phaseM_quarter hA' hB' _ _
  have len6 : m6.length = q := length_phaseM_quarter hA' hB' _ _
  have len7 : m7.length = q := length_phaseM_quarter hA' hB' _ _
  rw [vlinList_zeros_left len1, vlinList_zeros_left len3, vlinList_zeros_left len2,
    vlinList_zero (A := vlinList (-1) (vlinList 1 m1 m4) m5) (B := m6)
      (by rw [length_vlinList _ (length_vlinList _ len1 len4) len5, len6]),
    vlinList_zero (A := vlinList 1 (vlinList 1 (vlinList (-1) m1 m2) m3) m6) (B := m7)
      (by rw [length_vlinList _ (length_vlinList _ (length_vlinList _ len1 len2) len3) len6, len7])]
  simp only [m1, m2, m3, m4, m5, m6, m7, phaseM, vlinList_one, vlinList_neg_one, vlinList_zero_self]
  rfl

end Light.Sec3
