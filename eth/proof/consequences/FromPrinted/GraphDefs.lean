/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FromPrinted.CountDefs
public import Consequences.Defs

/-! # Section 7: Corollary 7 (counting in graphs) and the circuit lower bound for E^NP on the machines of proof/threesat/Printed/ (definitions and statements only)

This file puts Corollary 7 and the circuit lower bound for E^NP (Section 7) on the procedure
`FromPrinted.SplitCount.ENGINEsplit`, which is `SplitCount.ENGINEsplit` with `Printed.COUNT ℓ` at
the leaves in the place of `Eight.ViaGrouping.COUNTp ℓ`; its definitions `SIZED`, `DOMcount`,
`StSetsCounted`, `StDominatingCounted`, `StColoringsCounted`, `StAlgoRuns` name this procedure.
`Consequences.CountsGraph` (proof/consequences/Consequences/Defs.lean), which names no machine, is
used as it stands.
This file has no theorem. -/

@[expose] public section

open Consequences

namespace FromPrinted.Consequences

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount SizeCircuit Complement

/-- The machine that counts the satisfying assignments with exactly s true variables: Γ from the
circuit `sizeGates` beside the formula, then the procedure of the printed proof of Corollary 6 at
width max(w, 3), level ℓ, threshold parameter τ. -/
def SIZED (w ℓ τ : ℕ) : StepMachine (List Unit × ℕ × Fml) ℕ := sizedBy sizeGates (ENGINEsplit (max w 3) ℓ τ)

/-- **Independent sets, cliques, vertex covers of size s, with the machines named.** For every δ > 0
there are ℓ, τ, c such that `SIZED 2 ℓ τ`, put after the reader of the formula for independent sets,
after `readClique` and after `readCover`, has polynomial-time steps and returns the three numbers
within c·2^{δn} steps, on states of size at most c·(n+2)^c. -/
def StSetsCounted : Prop := ∀ δ : ℝ, 0 < δ → ∃ ℓ τ c : ℕ,
  (PolyTimeSteps (Stepped.mapIn (readF indepF) (SIZED 2 ℓ τ)) ∧ CountsGraph (Stepped.mapIn (readF indepF) (SIZED 2 ℓ τ)) (fun _ G s => numIndepSets G s) δ c) ∧
  (PolyTimeSteps (Stepped.mapIn readClique (SIZED 2 ℓ τ)) ∧ CountsGraph (Stepped.mapIn readClique (SIZED 2 ℓ τ)) (fun _ G s => numCliques G s) δ c) ∧
  (PolyTimeSteps (Stepped.mapIn readCover (SIZED 2 ℓ τ)) ∧ CountsGraph (Stepped.mapIn readCover (SIZED 2 ℓ τ)) (fun _ G s => numVertexCovers G s) δ c)

/-- The machine for dominating sets: read the input, walk the tree that shortens the clauses to w
literals, count at each leaf by `SIZED w ℓ τ`, add up. -/
def DOMcount (w ℓ τ : ℕ) : StepMachine (List Bool) ℕ := Stepped.mapIn read2 (walkSum (stepD w) rootD (Stepped.mapIn leafD (SIZED w ℓ τ)))

/-- **Dominating sets of size s, with the machine named.** «Choose w so large that the number of
leaves is at most 2^{δn/2}, apply Corollary 6 to each leaf, and add up.» For every δ > 0 there are
w, ℓ, τ, c such that the tree that shortens the clauses to w literals has at most 2^{(δ/2)n} leaves
(`ShortensD w (δ / 2)`), and `DOMcount w ℓ τ` has polynomial-time steps and returns, on the code of
(G, s), s ≤ n, the number of dominating sets of size s within c·2^{δn} steps, on states of size at
most c·(n+2)^c. -/
def StDominatingCounted : Prop := ∀ δ : ℝ, 0 < δ → ∃ w ℓ τ c : ℕ, ShortensD w (δ / 2) ∧ PolyTimeSteps (DOMcount w ℓ τ) ∧ CountsGraph (DOMcount w ℓ τ) (fun _ G s => numDominatingSets G s) δ c

/-- **Proper colorings with k colors, with the machine named**: the k-CNF on kn variables, then the
procedure of the printed proof of Corollary 6; the number in kn + 1 bits. -/
def StColoringsCounted : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ ℓ τ c : ℕ, PolyTimeSteps (Stepped.mapIn (readC k) (ENGINEsplit (max k 2) ℓ τ)) ∧
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ T : ℕ, (Stepped.mapIn (readC k) (ENGINEsplit (max k 2) ℓ τ)).Runs (code G) T (c * (n + 2) ^ c) (SatK.binary (n * k) (numColorings G k)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)

/-- **The algorithm inside the circuit lower bound for E^NP (Section 7), with the procedure of
Corollary 6 named.** For every δ > 0 there are ℓ, τ, c such that `ENGINEsplit 3 ℓ τ` has
polynomial-time steps and `CircuitLowerBound.Alg.algo (ENGINEsplit 3 ℓ τ) F fb` ends on every input
x with the bit «the formula made from x is unsatisfiable» within c·2^{δN} steps, on states of size
at most c·(N + 2)^c, N the number of variables of that formula, for every F with
`CircuitLowerBound.Alg.FormOK` and every fb.
Only the steps of the procedure are counted: the formula `CircuitLowerBound.Alg.pre F fb x` is made
when the input is handed over. It is `Eight.ViaGrouping.ALGO_runs_of` at the family `ENGINEsplit`.
It stands beside the proof of the circuit lower bound (see `Circuits`). -/
def StAlgoRuns : Prop := ∀ δ : ℝ, 0 < δ → ∃ ℓ τ c : ℕ, PolyTimeSteps (ENGINEsplit 3 ℓ τ) ∧
  ∀ (a₀ : ℕ) (g : CircuitLowerBound.MCode → ℕ) (F : (CircuitLowerBound.MCode × List Unit × ℕ) × List CircuitLowerBound.GateD → List Unit × ENP.Cnf) (fb : List Unit → Bool), CircuitLowerBound.Alg.FormOK a₀ g F → ∀ x : List Bool,
    ∃ (T : ℕ) (b : Bool), (CircuitLowerBound.Alg.algo (ENGINEsplit 3 ℓ τ) F fb).Runs x T (c * ((CircuitLowerBound.Alg.pre F fb x).1.length + 2) ^ c) b ∧ (b = true ↔ ¬ENP.Sat (CircuitLowerBound.Alg.pre F fb x).2) ∧
      (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * (CircuitLowerBound.Alg.pre F fb x).1.length)

/-! ### The end theorems

Each is proved in two pieces: a theorem `…From` that has the statements named as HYPOTHESES, and a
one-line instance on their proofs. The theorems of this development (everything outside Lean's core,
Std, Batteries and Mathlib) that the proof of `…From` reaches say nothing about a particular machine
for k-SAT or #k-SAT
(the host theorem and the facts on graphs and formulas; for the circuit lower bound the theorems of
proof/consequences/CircuitLowerBound/ and `Eight.ViaGrouping.corCircuits_of`, `corCircuits'_of`,
`corCircuitsInf_of`, `stAlg_from`, `stEngine_of` and `Eight.stAlg_of`; all of these take the
procedure or the machine as a hypothesis; one exception, which is no fast machine: under
`circuitsFrom` lies proof/consequences/CircuitLowerBound/'s own exhaustive search
`CircuitLowerBound.TabF.tryAll` with `fb`, which answers the question at the last place of a chain
by trying all assignments; it belongs to the construction of the language). -/

/-- Corollary 7, by counting.
`FromPrinted.Consequences.graphsFrom : StSetsCounted → StDominatingCounted → StColoringsCounted → GraphsByCounting`:
the Turing machines simulate the five named machines (host theorem of
proof/consequences/GraphProblems/, `GraphProblems.tm_of_stepped`); «In particular, they decide …» by
`GraphProblems.stDecide`, `stDecideColor`, with the output that the number is not 0. -/
abbrev GraphsByCounting : Prop := GraphProblems.CorGraphs

/-- The circuit lower bound for E^NP (the paragraph «Circuit lower bounds» in Section 7), in its
three Lean forms. `FromPrinted.Consequences.circuitsFrom : EngineCounts ENGINEsplit → Circuits`,
from `Eight.ViaGrouping.corCircuits_of`, `corCircuits'_of`, `corCircuitsInf_of` applied to
`Eight.ViaGrouping.stEngine_of`.
(`StAlgoRuns` names the machine inside; it stands beside the path, since `corCircuits_of` takes the
procedure with the machine left open.) -/
abbrev Circuits : Prop := ENP.CorCircuits ∧ ENP.CorCircuits' ∧ ENP.CorCircuitsInf

end FromPrinted.Consequences
