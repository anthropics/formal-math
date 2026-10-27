/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Prints the axioms behind the two theorems that Comparator compares:
    lake build Solution && lake env lean scripts/PrintAxioms.lean
No line of the output names an axiom other than propext, Classical.choice and Quot.sound.
This is a convenience for a reader, and not a check of files that one does not trust, because the
command runs
inside Lean with the library imported.  Comparator does not depend on that.
-/
import Solution

#print axioms MainResults.ethIsFalse
#print axioms MainResults.mainTheorem
