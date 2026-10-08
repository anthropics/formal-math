/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Frames
public import ThreeSumApsp.Lang.Lib.Pass

/-!
# Writing selected entries of a matrix

Phase 2 of Mv-hinted Mv writes X := N_{[n],I}, and Phase 3 of uMv-hinted uMv writes Y := N_{I,J}.
Both programs write their matrix row by row, and a row by the same loop, `pick`: cell c of the row
receives the content of the cell of a row of N whose number is the c-th of the given indices.
`Ends.pick` is the rule for this loop.  `RowsWritten μ a B r μ'` is the invariant of the loop over
the rows; it holds at the start (`RowsWritten.zero`), writing one more row keeps it
(`RowsWritten.succ`), and at the end the matrix is written (`RowsWritten.matAt`).
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## One row -/

/-- for c < len: dst[c] := mem[row + mem[idx + c]].  The arguments are local variables: the counter
c, the length, and the three addresses. -/
abbrev pick (c len dst row idx : ℕ) : Stmt :=
  pass c (v len) (v dst) (M (v row +' M (v idx +' v c)))

/-- **The rule for a row.**  The t indices J lie at aJ, and f b is the content of the cell
aRow + J_b.  The loop writes f 0, …, f (t - 1) to the cells from aDst on.  The cells that it reads
lie below aDst. -/
theorem Ends.pick {c len dst row idx t n aDst aRow aJ T : ℕ} {l : List ℤ} {μ : ℕ → ℤ}
    {Q : State → Prop} {J : Fin t → Fin n} (f : ℕ → ℤ) (vJ : VecAt μ aJ J)
    (hf : ∀ b : Fin t, μ (aRow + J b) = f b) (hJ : aJ + t ≤ aDst) (hrow : aRow + n ≤ aDst)
    (hsp : aDst + t ≤ lim.space) (hw : (lim.space : ℤ) ≤ lim.word)
    (done : Q ⟨frame (setLocal l c t), wrote μ aDst f t⟩)
    (hloc : frame l len = t ∧ frame l dst = aDst ∧ frame l row = aRow ∧ frame l idx = aJ := by
      simp)
    (hne : len ≠ c ∧ dst ≠ c ∧ row ≠ c ∧ idx ≠ c := by decide)
    (hT : 19 * t + 6 ≤ T := by light_time) :
    Ends lim P d (pick c len dst row idx) ⟨frame l, μ⟩ T Q := by
  obtain ⟨hlen, hdst, hrow', hidx⟩ := hloc
  obtain ⟨nlen, ndst, nrow, nidx⟩ := hne
  refine Ends.pass f (fun b hb => ?_) (update_frame_setLocal l c t ▸ done) hw hsp hlen hdst nlen
    ndst (le_trans (le_of_eq (by simp only [Expr.cost]; ring)) hT)
  have hlt := (J ⟨b, hb⟩).isLt
  have hreadJ : wrote μ aDst f b (aJ + b) = (J ⟨b, hb⟩ : ℕ) :=
    (wrote_rest (.inl (by omega))).trans (vJ ⟨b, hb⟩)
  have hreadN : wrote μ aDst f b (aRow + (J ⟨b, hb⟩ : ℕ)) = f b :=
    (wrote_rest (.inl (by omega))).trans (hf ⟨b, hb⟩)
  have qc : Function.update (frame l) c (b : ℤ) c = b := Function.update_self ..
  have qrow : Function.update (frame l) c (b : ℤ) row = aRow := by
    rw [Function.update_of_ne nrow, hrow']
  have qidx : Function.update (frame l) c (b : ℤ) idx = aJ := by
    rw [Function.update_of_ne nidx, hidx]
  simp only [Expr.Safe, Expr.val, Op.eval, Limits.Addr, qc, qrow, qidx, toNat_natCast_add_natCast,
    hreadJ, hreadN, true_and, and_true, abs_le]
  omega

/-! ## The rows -/

/-- In the memory μ' the rows below r of the matrix B are written from the address a on, and only
cells of the matrix differ from μ. -/
structure RowsWritten {m t : ℕ} (μ : ℕ → ℤ) (a : ℕ) (B : Matrix (Fin m) (Fin t) ℤ) (r : ℕ)
    (μ' : ℕ → ℤ) : Prop where
  same : SameOutside μ μ' a (m * t)
  rows : ∀ (r' : Fin m) (c : Fin t), r'.val < r → μ' (a + r'.val * t + c.val) = B r' c

section rows

variable {m t a r : ℕ} {μ μ' : ℕ → ℤ} {B : Matrix (Fin m) (Fin t) ℤ}

/-- No row is written yet. -/
theorem RowsWritten.zero : RowsWritten μ a B 0 μ :=
  ⟨SameOn.refl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- Row r of the matrix B, as a function on all natural numbers; it is 0 outside the matrix. -/
def rowFn (B : Matrix (Fin m) (Fin t) ℤ) (r c : ℕ) : ℤ :=
  if h : r < m ∧ c < t then B ⟨r, h.1⟩ ⟨c, h.2⟩ else 0

/-- Inside the matrix, `rowFn` gives the entries. -/
theorem rowFn_eq (B : Matrix (Fin m) (Fin t) ℤ) (hr : r < m) (c : Fin t) :
    rowFn B r c = B ⟨r, hr⟩ c :=
  dif_pos ⟨hr, c.isLt⟩

/-- One more row is written. -/
theorem RowsWritten.succ (h : RowsWritten μ a B r μ') (hr : r < m) :
    RowsWritten μ a B (r + 1) (wrote μ' (a + r * t) (rowFn B r) t) := by
  have hrt : r * t + t ≤ m * t := Nat.mul_add_le_mul hr le_rfl
  refine ⟨fun b hb => (wrote_rest (by omega)).trans (h.same b hb), fun r' c hr' => ?_⟩
  rcases Nat.lt_or_ge r' r with hlt | hge
  · have := Nat.mul_add_le_mul hlt (le_refl t)
    rw [wrote_rest (.inl (by omega))]
    exact h.rows r' c hlt
  · obtain rfl : r = r' := by omega
    exact (wrote_done c.isLt).trans (rowFn_eq B hr c)

/-- All rows are written. -/
theorem RowsWritten.matAt (h : RowsWritten μ a B m μ') : MatAt μ' a B :=
  fun r c => h.rows r c r.isLt

end rows

end Light.Sec5
