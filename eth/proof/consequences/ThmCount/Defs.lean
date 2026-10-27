/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperSentencesStatement
public import MainTheoremFormsStatement
public import Wrap.Defs
public import SparsificationLemma.Cal.Defs

/-! # Appendix C: Theorem C from Theorem D(b), and the closing remark (definitions and statements only)

Theorem C: «One deterministic algorithm computes the number of satisfying assignments of a 3-CNF on
n ≥ 2 variables in time 2^{O(n/(log n)^{α/10})}», with α = 1/2. Its Lean sentence is
`PaperSentences.CountRate (1/20)`.
Here it is derived from Theorem D(b) (`MainTheoremForms.ThmVariablesB`: one algorithm, for all k ≥ 1
and n ≥ 4, time 2^{C·k²·n·log log n/√(log n)}) at k = 3.
THIS IS NOT THE ROUTE OF THE PRINTED SKETCH OF APPENDIX C, and this file does not make Lean's proof
of Theorem C «the paper's proof». It shows that Theorem C also follows from Theorem D(b) with k = 3.
There is no circle: Appendix D takes from Appendix C the changed sparsification procedure and
«exactly one output», not Theorem C.
Of the sketch, the sentences on the procedure are in
proof/sparsification/SparsificationLemma/Sketch.lean and «Φ has Z·2^{n−v} satisfying assignments» is
`Occ.StCountOcc` (proof/consequences/Occ/Defs.lean). Three steps have no statement anywhere: the
outputs are «produced in time 2^{εn} times a polynomial in n that does not depend on ε» (for the
thresholds taken to be Calabro's), «Theorem A(c) computes the number Z» at each output, and «The
time is bounded as in the proof of Theorem A(d), with M(ε)+2 in place of M(ε), and ε = (log
n)^{−α/10} gives the theorem».
Three things stand between the two sentences, and each is a named statement:
1. the input: the machine of D(b) reads 1ᵏ0 before the code; 2. the range: D(b) says nothing for n <
   4, Theorem C wants a machine that is right for every n and fast for n ≥ 2; so the front end adds
   four forced variables (`Wrap.pad4`), which keeps the number of satisfying assignments, and the
   last step takes the four highest bits off the output;
3. the rates: 9·(n+4)·log log(n+4)/√(log(n+4)) = O(n/(log n)^{1/20}) for n ≥ 2, also after the power
   q of the wrapper.
The statements `StFromVariablesB` and `StCanBeWrappedAndEveryWrapperCounts` are made for EVERY
machine with the body of D(b), so that they show the route.
This file has no theorem. -/

@[expose] public section

namespace ThmCount

open Turing Groundwork PaperSentences

/-- The front end: the plain code of a 3-CNF φ is mapped to the code of (3, φ with four forced
variables more). Nothing is asked on other words. -/
def MapsToPadded (pre : List Bool → List Bool) : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF 3 φ → pre (SatK.enc 3 φ) = SatM.enc 3 (Wrap.pad4 φ)

/-- There is a polynomial-time front end. -/
def StFrontEnd : Prop := ∃ pre : List Bool → List Bool, PolyT pre ∧ MapsToPadded pre

/-- The last step: the four highest bits are taken off. -/
def dropFour (y : List Bool) : List Bool := y.take (y.length - 4)

/-- The four forced variables keep the number of satisfying assignments, and the number in n + 5
bits without its four highest bits is the number in n + 1 bits. -/
def StPadKeepsCount : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF 3 φ →
  SatK.IsKCNF 3 (Wrap.pad4 φ) ∧ SatK.numSat (Wrap.pad4 φ) = SatK.numSat φ ∧ dropFour (SatK.binary (n + 4) (SatK.numSat (Wrap.pad4 φ))) = SatK.binary n (SatK.numSat φ)

/-- The plain code of a 3-CNF on n variables has length polynomial in n. -/
def StInputLength : Prop := ∃ a d : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF 3 φ → (SatK.enc 3 φ).length ≤ a * (n + 2) ^ d

/-- The comparison of the rates: for all constants C, q, a, d there is C' such that for every n ≥ 2,
q·(2^{C·9·(n+4)·log log(n+4)/√(log(n+4))} + a·(n+2)^d + 1)^q ≤ 2^{C'·n/(log n)^{1/20}}. -/
def StRates : Prop := ∀ C q a d : ℕ, ∃ C' : ℝ, ∀ n : ℕ, 2 ≤ n →
  (q : ℝ) * ((2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) + (a : ℝ) * ((n : ℝ) + 2) ^ d + 1) ^ q ≤ (2 : ℝ) ^ (C' * (n / lg n ^ ((1 : ℝ) / 20)))

/-- The last step is polynomial-time. -/
def StLastStep : Prop := PolyT dropFour

/-- **For EVERY machine M with the body of Theorem D(b)**, every front end as above (polynomial-time
or not) and every machine N that wraps M with it and with `dropFour`: N computes the number of
satisfying assignments of every 3-CNF, on n ≥ 2 variables in time 2^{C'·n/(log n)^{1/20}}. -/
def StFromVariablesB : Prop := ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), MainTheoremForms.ThmVariablesBFor M C → ∀ pre : List Bool → List Bool, MapsToPadded pre →
  ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Wrap.Wraps M pre dropFour N q →
    ∃ (C' : ℝ) (t : ℕ → ℕ), SatK.CountsTM 3 N t ∧ ∀ n : ℕ, 2 ≤ n → (t n : ℝ) ≤ (2 : ℝ) ^ (C' * (n / lg n ^ ((1 : ℝ) / 20)))

/-- Existence and the statement on every wrapper in one: for EVERY machine M with finite alphabets
and the body of Theorem D(b), (1) there are a polynomial-time front end, a machine N with finite
alphabets and q such that N wraps M with it and with `dropFour`; (2) every such N counts, as in
`StFromVariablesB`. -/
def StCanBeWrappedAndEveryWrapperCounts : Prop := ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) → MainTheoremForms.ThmVariablesBFor M C →
  (∃ (pre : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) (q : ℕ), PolyT pre ∧ MapsToPadded pre ∧ (∀ i, Finite (N.tm.Γ i)) ∧ Wrap.Wraps M pre dropFour N q) ∧
  ∀ pre : List Bool → List Bool, MapsToPadded pre → ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Wrap.Wraps M pre dropFour N q →
    ∃ (C' : ℝ) (t : ℕ → ℕ), SatK.CountsTM 3 N t ∧ ∀ n : ℕ, 2 ≤ n → (t n : ℝ) ≤ (2 : ℝ) ^ (C' * (n / lg n ^ ((1 : ℝ) / 20)))

/-- Theorem C from Theorem D(b). It follows, with the statements above, from
`StCanBeWrappedAndEveryWrapperCounts`. -/
def StTheorem : Prop := MainTheoremForms.ThmVariablesB → CountRate (1 / 20)

/-! ### The closing remark of Appendix C

«For clauses of 3 literals, a bound in Calabro's proof gives M(ε) = O(ε^{-2} log²(1/ε)), and with it
the time becomes 2^{O(n(log log n)^{2/3}/(log n)^{α/3})}.»
The first half is stated for the outputs of the procedure (`StMEpsClauses`). The second half is
stated only as a sentence that follows from Theorem D(b); the remark's own derivation of the time is
not stated. -/

/-- The bound on the occurrences of a literal in the formula ψ at a leaf, at k = 3: 2 + 4α·(32α), α =
`SparsificationLemma.Cal.alphaC 3 ε`. (A leaf has at most 2n times this many clauses; for the
outputs themselves see `StMEpsClauses`.) It is O(ε^{-2}·log²(1/ε)) for 0 < ε ≤ 1/2 (the paper's O is
for ε → 0; near ε = 1 the logarithm vanishes). -/
def StMEps : Prop := ∃ A : ℝ, ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 →
  ((2 + 4 * SparsificationLemma.Cal.alphaC 3 ε * (32 * SparsificationLemma.Cal.alphaC 3 ε) : ℕ) : ℝ) ≤ A * ((ε : ℝ) ^ (-2 : ℝ) * lg (1 / (ε : ℝ)) ^ 2)

/-- «gives M(ε) = O(ε^{-2} log²(1/ε))», at k = 3, for the outputs themselves: every output of the
procedure of Appendix C with the thresholds taken to be Calabro's
(`SparsificationLemma.Cal.sparsify 3 n ε φ`) has at most (A·ε^{-2}·log²(1/ε) + 2)·n clauses, for 0 <
ε ≤ 1/2. -/
def StMEpsClauses : Prop := ∃ A : ℝ, ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 → ∀ (n : ℕ) (φ : Groundwork.Sparsify.PFml), SparsificationLemma.IsKCNF 3 n φ →
  ∀ Φ ∈ SparsificationLemma.Cal.sparsify 3 n ε φ, (Φ.length : ℝ) ≤ (A * ((ε : ℝ) ^ (-2 : ℝ) * lg (1 / (ε : ℝ)) ^ 2) + 2) * n

/-- The time of the remark, as a sentence (α = 1/2), for n ≥ 4: one deterministic algorithm computes
the number of satisfying assignments of a 3-CNF on n ≥ 4 variables in time 2^{O(n(log log
n)^{2/3}/(log n)^{1/6})}. It is weaker than Theorem D(b) at k = 3 and is derived from it by
comparing the rates, not by the route of the remark. -/
def StRemarkTime : Prop := ∃ C : ℝ, CountsInTime 3 4 fun n => (2 : ℝ) ^ (C * (n * lg (lg n) ^ ((2 : ℝ) / 3) / lg n ^ ((1 : ℝ) / 6)))

end ThmCount
