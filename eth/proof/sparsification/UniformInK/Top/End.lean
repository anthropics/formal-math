/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.Defs
import ClauseBound.Both.End

/-! # Lemmas on the time bounds of the statement for all widths k

Four lemmas on the bounds of the statement for all widths k: the bound in n with k² in the exponent
grows with the constant (`boundNK_mono`); the bound with the minimum of the two exponents is the
bound in n
when that exponent is the smaller one (`boundBothK_of_le`) and the bound in m otherwise
(`boundBothK_of_ge`); and if every variable occurs and n ≥ 1, there is a clause (`one_le_length`). -/

public section

namespace UniformInK.End

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End

/-- The bound in n with k² in the exponent grows with the constant. -/
theorem boundNK_mono {r : ℕ → ℝ} {D D' : ℕ} (h : D ≤ D') (k n : ℕ) (hr : 0 ≤ r n) : SatM.boundNK r D k n ≤ SatM.boundNK r D' k n := by
  unfold SatM.boundNK
  have hD : (D : ℝ) ≤ D' := by exact_mod_cast h
  refine Nat.floor_le_floor (mul_le_mul hD (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (by positivity) (by positivity))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (by positivity)) (by positivity)) hr

/-- If the exponent in n is the smaller one, the bound with the minimum is the bound in n. -/
theorem boundBothK_of_le {rn rm : ℕ → ℝ} {C k n m : ℕ} (h : (k : ℝ) ^ 2 * n * rn n ≤ (k : ℝ) * m * rm m) : SatM.boundBothK rn rm C k n m = SatM.boundNK rn C k n := by
  unfold SatM.boundBothK SatM.boundNK
  rw [min_eq_left h]
  simp only [mul_assoc]

/-- If the exponent in m is the smaller one, the bound with the minimum is the bound in m. -/
theorem boundBothK_of_ge {rn rm : ℕ → ℝ} {C k n m : ℕ} (h : (k : ℝ) * m * rm m ≤ (k : ℝ) ^ 2 * n * rn n) : SatM.boundBothK rn rm C k n m = SatM.bound rm C k m := by
  unfold SatM.boundBothK SatM.bound
  rw [min_eq_right h]
  simp only [mul_assoc]

/-- If every variable occurs and there is a variable, there is a clause. -/
theorem one_le_length {n : ℕ} {φ : Sat3.CNF n} (hn : 1 ≤ n) (ho : SatM.AllOccur φ) : 1 ≤ φ.length := by
  obtain ⟨c, hc, _⟩ := ho ⟨0, hn⟩
  exact List.length_pos_of_mem hc

end UniformInK.End

namespace UniformInK

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End UniformInK.End

end UniformInK
