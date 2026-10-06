/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Phases
public import ThreeSumApsp.Lang.RowMajor
public import ThreeSumApsp.Spec.Sec5.Corollary40.Outputs

/-!
# The three hinted problems: where the inputs of the phases lie

The statements about v-hinted Mv, Mv-hinted Mv and uMv-hinted uMv (Section 5.4) fix the layout: the
inputs of the phases lie one after the other from cell 0 on (`InputsAt`).  This file names the
addresses.  For each problem, and for each phase in which its program works, a structure says what
the memory holds in that phase, and a lemma reads the structure off the list of the inputs so far,
together with the address of the first cell after them.

Matrices are written row by row (`MatAt`), Booleans as 0 and 1 (`toInt`), and a vector of indices
cell by cell (`VecAt`).
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.HintedMv ThreeSumApsp.Spec.Sec5

/-! ## Matrices in the memory -/

/-- The number of cells of a matrix. -/
private theorem length_rowMajor_mat {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℤ) :
    (rowMajor A).length = n * k :=
  length_rowMajor _

/-- The rows from the row s on lie where they lie in the matrix. -/
theorem matAt_rowsFrom {n k a : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} {μ : ℕ → ℤ} (h : MatAt μ a A)
    (s t : ℕ) (hs : s + t ≤ n) : MatAt μ (a + s * k) (rowsFrom A s t hs) := fun i j => by
  refine Eq.trans ?_ (h ⟨s + i.val, by omega⟩ j)
  congr 1
  simp only
  ring

/-! ## v-hinted Mv

n in cell 0, t in cell 1, M from cell 2 on, then V, the index i, and the n cells of the output. -/

/-- The address of V. -/
def vV (n t : ℕ) : ℕ := 2 + n * t
/-- The cell of the index i. -/
def vI (n t : ℕ) : ℕ := vV n t + t * n
/-- The first cell of the output. -/
def vOut (n t : ℕ) : ℕ := vI n t + 1

/-- The inputs of Phases 1 and 2. -/
structure VMem2 {n t : ℕ} (μ : ℕ → ℤ) (M : Matrix (Fin n) (Fin t) Bool)
    (V : Matrix (Fin t) (Fin n) Bool) : Prop where
  n_eq : μ 0 = n
  t_eq : μ 1 = t
  matM : MatAt μ 2 (toInt M)
  matV : MatAt μ (vV n t) (toInt V)

/-- The inputs of Phases 1 to 3. -/
structure VMem3 {n t : ℕ} (μ : ℕ → ℤ) (M : Matrix (Fin n) (Fin t) Bool)
    (V : Matrix (Fin t) (Fin n) Bool) (i : Fin n) : Prop extends VMem2 μ M V where
  i_eq : μ (vI n t) = (i.val : ℤ)

section vHinted

variable {n t off : ℕ} {μ : ℕ → ℤ} {M : Matrix (Fin n) (Fin t) Bool}
  {V : Matrix (Fin t) (Fin n) Bool} {i : Fin n}

/-- What the memory holds when the input of Phase 2 has been written. -/
theorem vMem2_of_inputs
    (h : InputsAt μ off ([(n : ℤ), (t : ℤ)] ++ rowMajor (toInt M) ++ rowMajor (toInt V))) :
    VMem2 μ M V ∧ off = vI n t := by
  obtain ⟨hseg, rfl⟩ := h
  simp only [seg_append, seg_cons, List.length_append, length_rowMajor_mat, Nat.zero_add,
    and_assoc] at hseg ⊢
  obtain ⟨hn, ht, -, hM, hV⟩ := hseg
  exact ⟨⟨hn, ht, matAt_of_seg hM, matAt_of_seg hV⟩, rfl⟩

/-- What the memory holds when the input of Phase 3 has been written. -/
theorem vMem3_of_inputs
    (h : InputsAt μ off
      ([(n : ℤ), (t : ℤ)] ++ rowMajor (toInt M) ++ rowMajor (toInt V) ++ [(i.val : ℤ)])) :
    VMem3 μ M V i ∧ off = vOut n t := by
  obtain ⟨hseg, rfl⟩ := h
  simp only [seg_append, seg_cons, List.length_append, length_rowMajor_mat, Nat.zero_add,
    and_assoc] at hseg ⊢
  obtain ⟨hn, ht, -, hM, hV, hi, -⟩ := hseg
  exact ⟨⟨⟨hn, ht, matAt_of_seg hM, matAt_of_seg hV⟩, hi⟩, rfl⟩

end vHinted

/-! ## Mv-hinted Mv

n in cell 0, t in cell 1, N from cell 2 on, then V, the t indices I, the index j, and the n cells of
the output. -/

/-- The address of V. -/
def mvV (n : ℕ) : ℕ := 2 + n * n
/-- The address of I. -/
def mvI (n t : ℕ) : ℕ := mvV n + t * n
/-- The cell of the index j. -/
def mvJ (n t : ℕ) : ℕ := mvI n t + t
/-- The first cell of the output. -/
def mvOut (n t : ℕ) : ℕ := mvJ n t + 1

/-- The inputs of Phases 1 and 2. -/
structure MvMem2 {n t : ℕ} (μ : ℕ → ℤ) (N : Matrix (Fin n) (Fin n) Bool)
    (V : Matrix (Fin t) (Fin n) Bool) (I : Fin t → Fin n) : Prop where
  n_eq : μ 0 = n
  t_eq : μ 1 = t
  matN : MatAt μ 2 (toInt N)
  matV : MatAt μ (mvV n) (toInt V)
  vecI : VecAt μ (mvI n t) I

/-- The inputs of Phases 1 to 3. -/
structure MvMem3 {n t : ℕ} (μ : ℕ → ℤ) (N : Matrix (Fin n) (Fin n) Bool)
    (V : Matrix (Fin t) (Fin n) Bool) (I : Fin t → Fin n) (j : Fin n) : Prop
    extends MvMem2 μ N V I where
  j_eq : μ (mvJ n t) = (j.val : ℤ)

section MvHinted

variable {n t off : ℕ} {μ : ℕ → ℤ} {N : Matrix (Fin n) (Fin n) Bool}
  {V : Matrix (Fin t) (Fin n) Bool} {I : Fin t → Fin n} {j : Fin n}

/-- What the memory holds when the input of Phase 2 has been written. -/
theorem mvMem2_of_inputs
    (h : InputsAt μ off ([(n : ℤ), (t : ℤ)] ++ rowMajor (toInt N) ++ rowMajor (toInt V) ++
      List.ofFn fun k => ((I k).val : ℤ))) :
    MvMem2 μ N V I ∧ off = mvJ n t := by
  obtain ⟨hseg, rfl⟩ := h
  simp only [seg_append, seg_cons, List.length_append, length_rowMajor_mat, List.length_ofFn,
    Nat.zero_add, and_assoc] at hseg ⊢
  obtain ⟨hn, ht, -, hN, hV, hI⟩ := hseg
  exact ⟨⟨hn, ht, matAt_of_seg hN, matAt_of_seg hV, vecAt_of_seg hI⟩, rfl⟩

/-- What the memory holds when the input of Phase 3 has been written. -/
theorem mvMem3_of_inputs
    (h : InputsAt μ off ([(n : ℤ), (t : ℤ)] ++ rowMajor (toInt N) ++ rowMajor (toInt V) ++
      (List.ofFn fun k => ((I k).val : ℤ)) ++ [(j.val : ℤ)])) :
    MvMem3 μ N V I j ∧ off = mvOut n t := by
  obtain ⟨hseg, rfl⟩ := h
  simp only [seg_append, seg_cons, List.length_append, length_rowMajor_mat, List.length_ofFn,
    Nat.zero_add, and_assoc] at hseg ⊢
  obtain ⟨hn, ht, -, hN, hV, hI, hj, -⟩ := hseg
  exact ⟨⟨⟨hn, ht, matAt_of_seg hN, matAt_of_seg hV, vecAt_of_seg hI⟩, hj⟩, rfl⟩

end MvHinted

/-! ## uMv-hinted uMv

n, t₁, t₂ in cells 0, 1, 2; U from cell 3 on; then N, V, I, J, the two indices i and j, the output
cell, and the free cells. -/

/-- The address of N. -/
def uMvN (n t₁ : ℕ) : ℕ := 3 + n * t₁
/-- The address of V. -/
def uMvV (n t₁ : ℕ) : ℕ := uMvN n t₁ + n * n
/-- The address of I. -/
def uMvI (n t₁ t₂ : ℕ) : ℕ := uMvV n t₁ + t₂ * n
/-- The address of J. -/
def uMvJ (n t₁ t₂ : ℕ) : ℕ := uMvI n t₁ t₂ + t₁
/-- The address of the indices i and j. -/
def uMvQ (n t₁ t₂ : ℕ) : ℕ := uMvJ n t₁ t₂ + t₂
/-- The output cell. -/
def uMvOut (n t₁ t₂ : ℕ) : ℕ := uMvQ n t₁ t₂ + 2
/-- The first free cell. -/
def uMvFree (n t₁ t₂ : ℕ) : ℕ := uMvOut n t₁ t₂ + 1

/-- The inputs of Phases 1 to 3. -/
structure UMvMem3 {n t₁ t₂ : ℕ} (μ : ℕ → ℤ) (U : Matrix (Fin n) (Fin t₁) Bool)
    (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin t₂) (Fin n) Bool) (I : Fin t₁ → Fin n)
    (J : Fin t₂ → Fin n) : Prop where
  n_eq : μ 0 = n
  t₁_eq : μ 1 = t₁
  t₂_eq : μ 2 = t₂
  matU : MatAt μ 3 (toInt U)
  matN : MatAt μ (uMvN n t₁) (toInt N)
  matV : MatAt μ (uMvV n t₁) (toInt V)
  vecI : VecAt μ (uMvI n t₁ t₂) I
  vecJ : VecAt μ (uMvJ n t₁ t₂) J

/-- The inputs of Phases 1 to 4. -/
structure UMvMem4 {n t₁ t₂ : ℕ} (μ : ℕ → ℤ) (U : Matrix (Fin n) (Fin t₁) Bool)
    (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin t₂) (Fin n) Bool) (I : Fin t₁ → Fin n)
    (J : Fin t₂ → Fin n) (i j : Fin n) : Prop extends UMvMem3 μ U N V I J where
  i_eq : μ (uMvQ n t₁ t₂) = (i.val : ℤ)
  j_eq : μ (uMvQ n t₁ t₂ + 1) = (j.val : ℤ)

section uMvHinted

variable {n t₁ t₂ off : ℕ} {μ : ℕ → ℤ} {U : Matrix (Fin n) (Fin t₁) Bool}
  {N : Matrix (Fin n) (Fin n) Bool} {V : Matrix (Fin t₂) (Fin n) Bool} {I : Fin t₁ → Fin n}
  {J : Fin t₂ → Fin n} {i j : Fin n}

/-- What the memory holds when the input of Phase 3 has been written. -/
theorem uMvMem3_of_inputs
    (h : InputsAt μ off ([(n : ℤ), (t₁ : ℤ), (t₂ : ℤ)] ++ rowMajor (toInt U) ++
      rowMajor (toInt N) ++ rowMajor (toInt V) ++ (List.ofFn fun k => ((I k).val : ℤ)) ++
      List.ofFn fun k => ((J k).val : ℤ))) :
    UMvMem3 μ U N V I J ∧ off = uMvQ n t₁ t₂ := by
  obtain ⟨hseg, rfl⟩ := h
  simp only [seg_append, seg_cons, List.length_append, length_rowMajor_mat, List.length_ofFn,
    Nat.zero_add, and_assoc] at hseg ⊢
  obtain ⟨hn, h₁, h₂, -, hU, hN, hV, hI, hJ⟩ := hseg
  exact ⟨⟨hn, h₁, h₂, matAt_of_seg hU, matAt_of_seg hN, matAt_of_seg hV, vecAt_of_seg hI,
    vecAt_of_seg hJ⟩, rfl⟩

/-- What the memory holds when the input of Phase 4 has been written. -/
theorem uMvMem4_of_inputs
    (h : InputsAt μ off ([(n : ℤ), (t₁ : ℤ), (t₂ : ℤ)] ++ rowMajor (toInt U) ++
      rowMajor (toInt N) ++ rowMajor (toInt V) ++ (List.ofFn fun k => ((I k).val : ℤ)) ++
      (List.ofFn fun k => ((J k).val : ℤ)) ++ [(i.val : ℤ), (j.val : ℤ)])) :
    UMvMem4 μ U N V I J i j ∧ off = uMvOut n t₁ t₂ := by
  obtain ⟨hseg, rfl⟩ := h
  simp only [seg_append, seg_cons, List.length_append, length_rowMajor_mat, List.length_ofFn,
    Nat.zero_add, and_assoc] at hseg ⊢
  obtain ⟨hn, h₁, h₂, -, hU, hN, hV, hI, hJ, hi, hj, -⟩ := hseg
  exact ⟨⟨⟨hn, h₁, h₂, matAt_of_seg hU, matAt_of_seg hN, matAt_of_seg hV, vecAt_of_seg hI,
    vecAt_of_seg hJ⟩, hi, hj⟩, rfl⟩

end uMvHinted

end Light.Sec5
