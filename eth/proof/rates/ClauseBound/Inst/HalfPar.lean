/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfIfc
public import ClauseBound.Gen.Defs
import ClauseBound.Part.Bits
import ClauseBound.Part.Bounds

/-! # For large enough constants the pieces with ρ = 1/√2 as programs have the parameters (1/√2, c)

`Par.par_of_cst`: if c₀ and c are large enough at every length (`Cst c₀ c lam` for every λ ≥ 1),
then `halfF c₀ c` has the parameters (1/√2, c) in the sense of `ClauseBound.Gen.Par`. That the
programs
are pieces at every length λ ≥ 1 (`PiecesF.Spec`) enters as the hypothesis `StSpec`.
The main field is the one on the sum of the two numbers of bits of a piece (`Par.cap_add_cap_le`):
each number is a minimum, so it is at most ⌈log₂ R^row_s⌉ or
⌈log₂ R^col_s⌉ with s = i − 2h, |s| ≤ 2h, and the program's h, R^row and R^col are the numbers of
the mathematics. -/

public section

namespace ClauseBound.Inst.Half

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Part ClauseBound.Inst.Rec

namespace Par

/-- |s| ≤ 2h for the number s of a piece. -/
theorem abs_sOf_le (h i : ℕ) : |sOf h i| ≤ 2 * (h : ℤ) := by
  unfold sOf
  have h1 : min i (4 * h) ≤ 4 * h := min_le_right _ _
  rw [abs_le]
  constructor <;> omega

/-- The two numbers of bits of a piece together are at most ⌈log₂ R^row_s⌉ + ⌈log₂ R^col_s⌉, s = i −
2h, h the least number ≥ 2 with p(h) ≥ 2^λ. -/
theorem cap_add_cap_le {c₀ lam : ℕ} (c h' i : ℕ) (hh : hOf lam ≤ c₀ * lam ^ 2) :
    (halfF c₀ c).cap false h' lam i + (halfF c₀ c).cap true h' lam i ≤
      Nat.clog 2 (Rrow (hOf lam) (sOf (hOf lam) i)) + Nat.clog 2 (Rcol (hOf lam) (sOf (hOf lam) i)) := by
  have hs := abs_le.1 (abs_sOf_le (hOf lam) i)
  have h1 : (halfF c₀ c).cap false h' lam i ≤ Nat.clog 2 (Rrow (hOf lam) (sOf (hOf lam) i)) := by
    change min (2 * c * lam) (Nat.clog 2 (RrowF (hF c₀ lam) (sOf (hF c₀ lam) i))) ≤ _
    rw [hF_eq hh, RrowF_eq hs.2]
    exact min_le_right _ _
  have h2 : (halfF c₀ c).cap true h' lam i ≤ Nat.clog 2 (Rcol (hOf lam) (sOf (hOf lam) i)) := by
    change min (2 * c * lam) (Nat.clog 2 (RcolF (hF c₀ lam) (sOf (hF c₀ lam) i))) ≤ _
    rw [hF_eq hh, RcolF_eq hs.1]
    exact min_le_right _ _
  exact Nat.add_le_add h1 h2

/-- If c₀ and c are large enough at every length, then `halfF c₀ c` has the parameters (1/√2, c). -/
theorem par_of_cst (hS : StSpec) {c₀ c : ℕ} (hC : ∀ lam : ℕ, 1 ≤ lam → Cst c₀ c lam) : ClauseBound.Gen.Par (halfF c₀ c) (1 / Real.sqrt 2) c where
  spec := fun h' lam hl => hS c₀ c lam h' hl (hC lam hl)
  caps := fun h' lam hl => by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.range ((halfF c₀ c).cnt h' lam))
      (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero (4 * hF c₀ lam)))
      fun i => (halfF c₀ c).cap false h' lam i + (halfF c₀ c).cap true h' lam i
    have h1 : capSum (halfF c₀ c) h' lam = (halfF c₀ c).cap false h' lam i + (halfF c₀ c).cap true h' lam i := hi
    rw [h1]
    refine le_trans ?_ ((hC lam hl).caps (sOf (hOf lam) i) (abs_sOf_le _ _)).2.2
    exact_mod_cast cap_add_cap_le c h' i (hC lam hl).h_le
  cnt := fun h' lam hl => by
    change 4 * hF c₀ lam + 1 ≤ _
    rw [hF_eq (hC lam hl).h_le]
    exact (hC lam hl).cnt
  bits := fun _ _ _ => le_rfl
  d := fun h' lam hl => by
    change factN (hF c₀ lam) < _
    rw [hF_eq (hC lam hl).h_le, factN_eq]
    exact (hC lam hl).fact
  need := fun _ _ _ => le_rfl
  m_le := le_rfl

end Par

end ClauseBound.Inst.Half
