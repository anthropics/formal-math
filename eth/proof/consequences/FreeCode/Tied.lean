/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FreeCode.Defs
public import FreeCode.Reader
import FreeCode.ReaderCert
import FreeCode.Behind
import SplitSat.Walk
import SplitSat.Cert
import SplitSat.Procedure
import SplitSat.Simulate
import SplitSat.Main
import SparsifyWidthK.Poly.Sparsify
import ToTuring.Poly.Basic
import Mathlib.Tactic

/-! # Corollary 5 with the code that does not depend on k, tied to its machines

The proof of Corollary 5 in the paper: «… Theorem 2 gives s_3 = 0 … s_3 = 0 implies s_k = 0 for
every k ≥ 3; the reduction (sparsify, then split every long clause into clauses of 3 literals with
new variables) …».
* `tied_of_decidesW`: any procedure D with polynomial-time steps that decides w-SAT on (N in unary,
  formula) with the exponent δ/2, put behind the reader `readFree`: the machine has polynomial-time
  steps and decides w-SAT on codes with the exponent δ; a Turing machine simulates it and decides
  w-SAT within ⌊c·2^{δn}⌋ steps.
* `stTiedThree` (= `FreeCode.StTiedThree`): D = `core3 ℓ τ`, the machine of Theorem 2 in its
  decision form without its own reader, by `SplitSat.stCore3`.
* `stTied` (= `FreeCode.StTied`): D = the reduction on `core3`, by `SplitSat.stSparsifyK`,
  `SplitSat.stCore3` and `SplitSat.stReduceCore`. -/

public section

namespace FreeCode

open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper SplitSat

/-- A procedure D with polynomial-time steps that decides w-SAT on (N in unary, formula) with the
exponent δ/2, behind the reader `readFree`: there are a Turing machine M with finite alphabets and
c, q such that the machine behind the reader has polynomial-time steps and decides w-SAT on codes
with the exponent δ and the constant c, M simulates it with polynomial overhead, and M decides w-SAT
on codes within ⌊c·2^{δn}⌋ steps. -/
theorem tied_of_decidesW {w : ℕ} {δ : ℝ} (hδ : 0 < δ) {D : StepMachine (List Unit × Fml) Bool} (hp : PolyTimeSteps D) {c₀ : ℕ} (hD : DecidesW w D (δ / 2) c₀) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ PolyTimeSteps (Stepped.mapIn readFree D) ∧
      DecidesFree (Stepped.mapIn readFree D) w δ c ∧ Simulates M (Stepped.mapIn readFree D) q ∧ SatFree.DecidesTM w M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  have hp' : PolyTimeSteps (Stepped.mapIn readFree D) := by
    obtain ⟨h⟩ := hp
    exact ⟨IsPolyT.mapIn readFree_polyT⟩
  have hd := stBehindReader readFree reads_readFree w D (δ / 2) c₀ hD
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp'
  obtain ⟨C, hcC, hTM⟩ := FreeCode.decidesTM_of_simulates hδ hs hd
  exact ⟨M, C, q, hfin, hp', decidesFree_mono (by linarith) hcC hd, hs, hTM⟩

/-- **«Theorem 2 gives s_3 = 0»**, for the code that does not depend on k, tied to the machine of
Theorem 2 in its decision form behind the reader: the statement `FreeCode.StTiedThree`. In the proof
the named machine has the exponent δ/2. -/
theorem stTiedThree : StTiedThree := fun δ hδ => by
  obtain ⟨ℓ, τ, hp, c₀, hD⟩ := stCore3 (δ / 2) (by positivity)
  obtain ⟨M, c, q, h⟩ := tied_of_decidesW hδ hp hD
  exact ⟨readFree, ℓ, τ, M, c, q, readFree_polyT, reads_readFree, h⟩

/-- **Corollary 5, tied to the reduction**, for the code that does not depend on k: the statement
`FreeCode.StTied`. With ε = (δ/2)/3 the tree at width k has at most 2^{εn} leaves of at most B·n
clauses; the machine of Theorem 2 in its decision form is taken with the exponent δ₃ = ε/(1 +
(k−3)·B). In the proof the named machine has the exponent δ/2. -/
theorem stTied : StTied := fun k hk δ hδ => by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨τ, Dd, B, Sk, hsp⟩ := stSparsifyK k hk (δ / 2 / 3) (by positivity)
  have hk3 : (0 : ℝ) ≤ (k : ℝ) - 3 := by
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hpos : (0 : ℝ) < 1 + ((k : ℝ) - 3) * B := by
    have := mul_nonneg hk3 (Nat.cast_nonneg (α := ℝ) B)
    linarith
  have h0 : 0 < δ / 2 / 3 / (1 + ((k : ℝ) - 3) * B) := div_pos (by positivity) hpos
  obtain ⟨ℓ₃, τ₃, hp, c₃, hD⟩ := stCore3 _ h0
  obtain ⟨c₀, hR⟩ := stReduceCore k hk (δ / 2) hδ2 τ Dd B Sk hsp (core3 ℓ₃ τ₃) _ c₃ h0.le (le_of_eq (div_mul_cancel₀ _ hpos.ne')) hD
  obtain ⟨M, c, q, h⟩ := tied_of_decidesW hδ (reduceCore_polyTimeSteps (certStep (thetaU τ) k) hp) hR
  exact ⟨readFree, τ, ℓ₃, τ₃, M, c, q, readFree_polyT, reads_readFree, h⟩

end FreeCode
