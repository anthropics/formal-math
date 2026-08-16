/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
comparator/PrintAxioms/Union.lean — axiom audit for the simple-or-on-line union
endpoint: lake build Solution.Union && lake env lean comparator/PrintAxioms/Union.lean
-/
import Solution.Union

#print axioms montgomery_taylor_simple_or_on_critical_line_union
#print axioms montgomery_taylor_simple_or_on_critical_line_union_cumulative
#print axioms montgomery_taylor_simple_or_on_critical_line_union_decimal
#print axioms montgomery_taylor_simple_or_on_critical_line_union_cumulative_decimal
