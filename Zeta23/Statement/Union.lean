/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Statement.SeamClosed
import Zeta23.Defs.UnionCounting

/-!
# Concrete zeta spelling of the simple-or-on-line union count
-/

noncomputable section

namespace Zeta23

/-- The direct union count for the abstract zeta-zero configuration is the paper's
inclusion-exclusion count. -/
theorem zetaZeros_Nu_eq (hs : ZetaSeam) (T₁ T₂ : ℝ) :
    (zetaZeros hs).Nu T₁ T₂ =
      N0 T₁ T₂ + Nsimple T₁ T₂ - N0simple T₁ T₂ := by
  rw [(zetaZeros hs).Nu_eq_N0_add_Ns_sub_N0s T₁ T₂]
  simp

@[simp] theorem zetaZeroConfig_Nu_eq (T₁ T₂ : ℝ) :
    zetaZeroConfig.Nu T₁ T₂ =
      N0 T₁ T₂ + Nsimple T₁ T₂ - N0simple T₁ T₂ := by
  simpa only [zetaZeroConfig] using zetaZeros_Nu_eq zetaSeam T₁ T₂

end Zeta23
