/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Paper.Rename.Math
import ClauseBound.Alg.Decode

/-! # Renaming the variables that occur: the program on the code of a formula

`renc_enc`: for k ≥ 1 and a formula φ with at most k literals in every clause, the front end `renc`
maps the code of (k, φ) to the code of (k, `ren φ`). So everything that is proved about codes of
formulas in which all variables occur applies to what the front end hands on. -/

public section

namespace VariableBound.Rename

open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)

/-- The number of a slot, with natural numbers as variables, is that of `Sat3.slot`. -/
theorem slotN_map {n : ℕ} (o : Option (Sat3.Lit n)) : slotN (o.map fun l => (l.1.val, l.2)) = Sat3.slot o := by
  cases o <;> rfl

/-- `encN` on k and n in unary and a formula over x₀ … x_(n−1), with natural numbers as variables,
is `SatM.enc`. -/
theorem encN_toN (k : ℕ) {n : ℕ} (φ : CNF n) : encN (List.replicate k ()) (List.replicate n (), toN φ) = SatM.enc k φ := by
  simp only [encN, SatM.enc, SatK.enc, toN, List.map_replicate, List.length_replicate, List.flatMap_map, List.getElem?_map, slotN_map]

/-- The front end maps the code of (k, φ) to the code of (k, φ renamed), for k ≥ 1 and φ with at
most k literals in every clause. -/
theorem renc_enc {k N : ℕ} (φ : CNF N) (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) : renc (SatM.enc k φ) = SatM.enc k (ren φ) := by
  obtain ⟨h1, h2⟩ := Decode.stDecM k N φ hk hφ
  rw [renc, h1, h2, ← encN_toN, toN_ren, renF, ← length_occL, List.map_const']

end VariableBound.Rename
