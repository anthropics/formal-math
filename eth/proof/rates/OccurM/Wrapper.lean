/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import OccurM.TiedDefs
public import OccurM.Arith
import OccurM.Top

/-! # Every wrapper counts

Let M count within the bound C·2^{C·km/(log₂(m+2))^α} (`SatM.bound`) on formulas in which every
variable occurs, let `pre` number the variables that occur, and let N wrap M with `pre` before it
and nothing after it
(`Wrap.Wraps M pre id N q`). On the code x of (k, φ), `pre x` is the code of (k, ψ) with ψ as in
`Prepares`; M puts out the number wanted within t steps, t that bound at m; so N puts it out within
q·(t + |x| + 1)^q steps.
`bound_le_pow` gives t ≤ 2^E with E ≤ (2C+1)·km/(log m)^α, and `steps_le` the printed bound.
`wrapper_counts` is this for any coding; the two end theorems are its cases for the compact code and
for the code that writes the number of variables in unary. -/

public section

namespace OccurM

open Groundwork Turing MainTheoremForms ClausesOccur
open Sat3 (CNF)

/-- For any coding `code` by nonempty words and any `pre` that numbers the variables that occur:
every wrapper counts within the printed bound, with the constant `stepsC q (2·C + 1)`. -/
theorem wrapper_counts {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (code : ∀ (_ : ℕ) {V : ℕ}, CNF V → List Bool) {pre : List Bool → List Bool}
    (hpre : ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → ∃ ψ : CNF (numOcc φ), SatK.IsKCNF k ψ ∧ SatM.AllOccur ψ ∧ ψ.length = φ.length ∧
      SatK.numSat ψ = numSatOcc φ ∧ pre (code k φ) = SatM.enc k ψ)
    (hlen : ∀ (k V : ℕ) (φ : CNF V), 1 ≤ (code k φ).length)
    {M : TM2ComputableAux Bool Bool} {C : ℕ} (hM : SatM.CountsTM M (SatM.bound (SatM.rPow α) C))
    {N : TM2ComputableAux Bool Bool} {q : ℕ} (hW : Wrap.Wraps M pre id N q) :
    ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length →
      Nonempty (TM2OutputsInTime N.tm ((code k φ).map N.inputAlphabet.invFun) (some ((SatK.binary (numOcc φ) (numSatOcc φ)).map N.outputAlphabet.invFun))
        (timeClauses α (stepsC q (2 * C + 1)) k φ.length + stepsC q (2 * C + 1) * (code k φ).length ^ stepsC q (2 * C + 1))) := by
  intro k V φ hk hφ hm
  obtain ⟨ψ, hψ, ho, e1, e2, e3⟩ := hpre k V φ hk hφ
  have hrun := hM k _ ψ hk (by omega) hψ ho
  rw [e1, e2, ← e3] at hrun
  obtain ⟨ev⟩ := hW (code k φ) _ _ hrun
  obtain ⟨E, hE1, hE2⟩ := bound_le_pow h0 h1 C hk hm
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  calc q * (SatM.bound (SatM.rPow α) C k φ.length + (code k φ).length + 1) ^ q ≤ q * ((code k φ).length + 2 ^ E + 1) ^ q :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ ≤ _ := steps_le q (2 * C + 1) hE2 (one_le_expClauses h0 h1 hk hm) (hlen k V φ)

/-- Every machine that runs a preparation and then a machine that counts within the bound
`SatM.bound` on formulas in which every variable occurs counts within the printed bound on every
k-CNF with k ≥ 1 and m ≥ 2; compact code. -/
theorem everyWrapperCounts : EveryWrapperCounts := fun _ h0 h1 _ hpre _ _ hM _ _ hW =>
  ⟨_, wrapper_counts h0 h1 (fun k _ φ => encC k φ) hpre one_le_length_encC hM hW⟩

/-- The same for the code that writes the number of variables in unary (`SatM.enc`). -/
theorem everyWrapperCountsUnary : EveryWrapperCountsUnary := fun _ h0 h1 _ hpre _ _ hM _ _ hW =>
  ⟨_, wrapper_counts h0 h1 (fun k _ φ => SatM.enc k φ) hpre one_le_length_enc hM hW⟩

end OccurM
