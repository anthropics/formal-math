/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.PairCeiling.CeilingLaw256
import Zeta23.PairCeiling.Signed

-- the bandwidth-one ceiling (no trusted statement file: every theorem below except the two kernel checks carries the
-- displayed hypothesis EnclOK; LawN256_check is by decide and depends on propext only, LawN256_edge on no axioms)
#print axioms Zeta23.PairCeiling.ceiling_stability
#print axioms Zeta23.PairCeiling.ceiling_nearCUE
#print axioms Zeta23.PairCeiling.lawN256_rows
#print axioms Zeta23.PairCeiling.ceiling_law256
#print axioms Zeta23.PairCeiling.ceiling_law256_decimal
#print axioms Zeta23.PairCeiling.ceiling_signed
#print axioms Zeta23.PairCeiling.ceiling_nearCUE_signed
#print axioms Zeta23.PairCeiling.ceiling_law256_signed
#print axioms Zeta23.PairCeiling.D1_nonneg_of_edgeNonneg
#print axioms Zeta23.PairCeiling.LawN256_check
#print axioms Zeta23.PairCeiling.LawN256_edge
