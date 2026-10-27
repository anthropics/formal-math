/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Defs
public import SparsificationLemma.Geo.Defs
public import SparsificationLemma.Cal.Defs
public import SparsificationLemma.Mach.Defs
public import SparsificationLemma.StepSparsifyDefs
public import SparsificationLemma.One
public import SparsificationLemma.Side
public import SparsificationLemma.Len
public import SparsificationLemma.Bound
public import SparsificationLemma.Shrink
public import SparsificationLemma.Iface
public import SparsificationLemma.Gen
public import SparsificationLemma.Geo.Thr
public import SparsificationLemma.Geo.Tau
public import SparsificationLemma.Geo.Eps
public import SparsificationLemma.Geo.S
public import UniformInKStatement
public import UniformInK.Top.Defs
public import SparsificationLemma.Cal.Real
public import SparsificationLemma.Cal.Alpha
public import SparsificationLemma.Cal.Beta
public import SparsificationLemma.Cal.Thr
public import SparsificationLemma.Cal.Facts
public import SparsificationLemma.Cal.Main
public import SparsificationLemma.Mach.Main
public import SparsificationLemma.Mach.Full
public import SparsificationLemma.Mach.LemSparsification
public import SparsificationLemma.TreeWalk.Walk
public import SparsificationLemma.Nodes
public import SparsificationLemma.StepSparsify
public import SparsificationLemma.Sketch

/-! # The sparsification: Lemma 4 in its form for deciding, without hypotheses

**What is proved.** Each file of proof/sparsification/SparsificationLemma proves one proposition,
some from those of other files. This file fills in the hypotheses of Lemma 4 and imports every proof
file of proof/sparsification/SparsificationLemma, so that a file which imports it sees all their
theorems.
Its one theorem is `SparsificationLemma.Mach.lemSparsification_holds : Mach.LemSparsification`:
Lemma 4, the Sparsification Lemma for clauses of at most 3 literals, with «one can compute in time
2^(εn) times a polynomial in n».
Among the theorems of the imported files is `SparsificationLemma.TreeWalk.lemSparsification_walk`
(Lemma 4 in the form that a machine uses which walks the tree and tests every leaf).
The theorems of proof/sparsification/SparsificationLemma/StepSparsify.lean and
proof/sparsification/SparsificationLemma/Sketch.lean follow Step 5 of Appendix D and the proof
sketch of Appendix C sentence by sentence.

**What a reader has to read.** The five files of definitions and propositions
(proof/sparsification/SparsificationLemma/Defs.lean, Geo/Defs.lean, Cal/Defs.lean, Mach/Defs.lean,
StepSparsifyDefs.lean), and the definitions of the tree on which they rest. Everything else is
proof.

**How it is proved.** The invariant along a path of the tree
(proof/sparsification/UniformInK/Spars/Step.lean) holds for all thresholds that are at least 1.
proof/sparsification/SparsificationLemma/Bound.lean derives the counts along a path from it under
the conditions `ThrC`, as
proof/sparsification/UniformInK/Spars/Bound.lean does for its thresholds.
proof/sparsification/SparsificationLemma/Iface.lean and
proof/sparsification/SparsificationLemma/Gen.lean carry the counts from finite sets to the program.
«Exactly one output» (proof/sparsification/SparsificationLemma/One.lean) follows from the sentences
on one branching by induction on
the depth of the tree, for all thresholds and wherever the paths are cut. No choice depends on the
side list (proof/sparsification/SparsificationLemma/Side.lean), so the tree is that of the procedure
without a side list. Two families of thresholds satisfy `ThrC`
(proof/sparsification/SparsificationLemma/Geo/Thr.lean,
proof/sparsification/SparsificationLemma/Cal/Thr.lean). The rest is arithmetic. The machine
(proof/sparsification/SparsificationLemma/Mach) is the padding machine of
proof/consequences/CountKSatRate/Pad.lean for a depth-first walk of the tree that collects the
outputs.

**What it does not say.** Nothing of Calabro's dissertation is used or checked: the three facts that
Step 5 of Appendix D cites from it are proved here by the analysis of
proof/sparsification/UniformInK/Spars. The machine runs the thresholds
θ i = 4·τ^(2i−1) and not Calabro's. Its input has a precision s in unary and not ε; the constant C
is not explicit, and s = `precE C k ε` depends on it
(proof/sparsification/SparsificationLemma/Mach/Defs.lean says why). In `LemSparsification` the
polynomial depends on ε.
ε is real in `LemSparsification`. -/

public section

namespace SparsificationLemma

end SparsificationLemma

namespace SparsificationLemma.Cal

end SparsificationLemma.Cal

namespace SparsificationLemma.Mach

/-- Lemma 4: the Sparsification Lemma for clauses of at most 3 literals, with its time clause. -/
theorem lemSparsification_holds : LemSparsification := lemSparsification prints

end SparsificationLemma.Mach
