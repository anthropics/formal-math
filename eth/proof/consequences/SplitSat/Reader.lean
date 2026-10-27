/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitSat.Defs
import SplitSat.Leaf
import SplitSat.Walk
import CountKSat.InOut

/-! # Section 7, proof of Corollary 5: the reduction on the code of a k-CNF

No sentence of the paper stands behind this file: the paper does not fix a code of formulas as
words. `REDUCE k τ D` is the reader `CountKSat.decU k` followed by `reduceCore`. The reader turns
the code `SatK.enc k φ` of a k-CNF on n variables into (n in unary, φ with numbers as variables)
(`CountKSat.stDecU`).
The code has at least n + 1 bits, so a bound c·(n+2)^c on the sizes of the states is a bound
c·(length of the code + 1)^c. `stReduce` proves `SplitSat.StReduce` from `stReduceCore`. -/

public section

namespace SplitSat

open Groundwork Groundwork.Prog Paper CountKSat Eight.ViaGrouping

/-- A machine that decides k-SAT on (n in unary, formula), in the sense of `DecidesW k`, decides
k-SAT on codes, in the sense of `Eight.ViaGrouping.Decides`, when the reader `decU k` is put in
front of it; the exponent and the constant stay. -/
theorem decides_of_decidesW {k : ℕ} (hk : 1 ≤ k) {M : StepMachine (List Unit × Fml) Bool} {δ : ℝ} {c : ℕ} (h : DecidesW k M δ c) :
    Decides (Stepped.mapIn (decU k) M) k δ c := by
  intro n φ h3
  obtain ⟨T, b, r, hb, hT⟩ := h n (Decode.toN φ) (fun D hD => by
    obtain ⟨⟨C, hC, hl⟩, h'⟩ := Decode.mem_toN hD
    exact ⟨hl ▸ h3.1 C hC, h'⟩) (nodup_toN h3.2)
  refine ⟨T, b, ?_, hb.trans (Decode.satN_toN φ), hT⟩
  have r' : M.Runs (decU k (SatK.enc k φ)) T (c * (n + 2) ^ c) b := by
    rw [stDecU k n φ hk h3.1]
    exact r
  refine (Stepped.mapIn_runs r').mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ c))
  rw [DecodeK.length_enc]
  omega

/-- The reduction with the reader of the input in front decides k-SAT with the exponent δ, for every
procedure D: the statement `SplitSat.StReduce`. -/
theorem stReduce : StReduce := fun k hk δ hδ τ Dd B Sk hsp D δ₃ c h0 hδB hD => by
  obtain ⟨c', h⟩ := stReduceCore k hk δ hδ τ Dd B Sk hsp D δ₃ c h0 hδB hD
  exact ⟨c', decides_of_decidesW (by omega) h⟩

end SplitSat
