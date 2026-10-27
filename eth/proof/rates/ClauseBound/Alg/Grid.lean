/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.GridNet
public import ClauseBound.Alg.GridPresents

/-! # The networks of one level on a grid with p rows and d columns, for any pieces

The interface statement `StGrid P` of proof/rates/ClauseBound/Alg/Interfaces.lean: the multiplier of
the pieces (the d of Definition 7, not the number of columns), raised to the power |R|, times the
sum Z of an instance on p·d nodes (p rows, d columns) is the sum of the terms of the patterns, and
for every pattern the plain functions `gridF P` present, with all rows merged and with all columns
merged, a network that has the value of the term, with its size, its total
and the bound on the bits that two parts share. The network is `gridN` of
proof/rates/ClauseBound/Alg/GridNet.lean. -/

public section

namespace ClauseBound.Alg.Grid

open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet

/-- What the networks use of the pieces follows from their specification, when the pad is long
enough. -/
theorem cutsOK_of_spec {P : PiecesF} {pad : U} {h ℓ : ℕ} (hS : P.Spec h ℓ) (hpad : 2 ^ P.need h ℓ ≤ pad.length) :
    ∃ A : ℕ → Pieces.Four ℓ, (∀ x y u v, ∑ i ∈ range (P.cnt h ℓ), A i x y u v = P.d h ℓ * Pieces.cross x y u v) ∧
      CutsOK P pad h ℓ A := by
  obtain ⟨A, hsum, habs, hfac⟩ := hS.ex
  refine ⟨A, hsum, hS.cnt_pos, hS.m_pos, fun tr i hi => ?_, fun tr i hi => hS.cap_le tr i hi, habs,
    fun tr i hi x y θ => ((hfac pad hpad i hi).2.2 tr x y θ).1, fun tr i hi x y θ => ((hfac pad hpad i hi).2.2 tr x y θ).2⟩
  cases tr
  · exact (hfac pad hpad i hi).1
  · exact fun x y u v => (hfac pad hpad i hi).2.1 x u y v

/-- The interface statement `StGrid` holds for all pieces `P`. -/
theorem stGrid (P : PiecesF) : StGrid P := by
  intro pad pu du hu ℓu T B _ hS hpad hB
  obtain ⟨A, hsum, hP⟩ := cutsOK_of_spec hS hpad
  have hc : P.cnt hu.length ℓu.length - 1 + 1 = P.cnt hu.length ℓu.length := Nat.sub_add_cancel hS.cnt_pos
  refine ⟨termZ pu.length du.length ℓu.length (instOf T) A (P.cnt hu.length ℓu.length - 1), ?_, fun y _ tr => ?_⟩
  · have h := ZW_mul_eq_sum pu.length du.length ℓu.length (instOf T) A (P.cnt hu.length ℓu.length - 1) (P.d hu.length ℓu.length)
      (by rw [hc]; exact hsum)
    rwa [hc] at h
  · exact ⟨gridN P pad pu.length du.length tr hu.length ℓu.length y (instOf T), GridPresents.presents P pad pu du hu ℓu tr y T,
      value_gridN hP _ _ tr y _, gridN_sized hP _ _ tr y hB, U_gridN P pad _ _ tr _ _ y _, fun a b _ => gridN_c_le hP _ _ tr y _ a b⟩

end ClauseBound.Alg.Grid
