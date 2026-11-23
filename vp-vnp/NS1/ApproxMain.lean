/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.ApproxBack

/-!
# No approximate accelerators

An approximate accelerator is carried to scales that are large against the exponents and the number of its constants;
there it gives an exact accelerator, which does not exist.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree LaurentPolynomial

variable {A : Type} [CommRing A] {θ : List Bool → A} {E : Type} [CommRing E] [Algebra A E]

/-- **Paper: the definition of an approximate accelerator, with its size.** An approximate accelerator of size `s` at the scale `V = v ^ H`
over E: a trie of at most `s` nodes with constants in E[ε,ε⁻¹], and a program of size at most `s` whose values lie in
the universal plain sums + ε E[ε]. -/
def HasAccA (θ : List Bool → A) (E : Type) [CommRing E] [Algebra A E] (H v s : ℕ) : Prop :=
  ∃ (K : KT E[T;T⁻¹]) (B : ℕ) (D : Tree), IsAccA θ H v (v ^ (H - 16)) K B D ∧ K.nds ≤ s ∧ D.size ≤ s ∧
    K.ht ≤ lg (max (v ^ H) s) ^ 2 ∧ B ≤ lg (max (v ^ H) s) ^ 3

/-- **Paper: proof of Proposition prop:approx-acc, the invariant.** An approximate program at a scale, small; the exponents of its
constants are at most 2 to a power that is polylogarithmic in the scale; the numbers b₀, Δ and cΔ may depend on the
first program, not on the scale. -/
structure InvA (θ : List Bool → A) (h cB U Δ cΔ b₀ : ℕ) (u : ℕ) (K : KT E[T;T⁻¹]) (B : ℕ) (D : Tree) : Prop where
  acc : IsAccA θ (16 * h) u (u ^ (16 * h - 16)) K B D
  big : U ≤ u
  nds : K.nds ≤ u
  size : D.size ≤ u ^ (4 * h)
  ht : K.ht ≤ cB * lg u ^ 3
  B_le : B ≤ cB * lg u ^ 3
  ht_lin : K.ht ≤ b₀ + 2000 * h * lg u
  B_lin : B ≤ b₀ + 2000 * h * lg u
  span : K.All (Span (2 ^ (cΔ * lg u ^ 3)))
  thin : K.All (Thin Δ)

theorem le_lg_four {u : ℕ} (hu : 8 ≤ u) : 4 * lg u ≤ lg (u ^ 5) := by
  have h1 : 4 ≤ lg u := le_lg_of_two_pow_le (k := 3) (by omega)
  have := le_lg_pow (n := u) (k := 5) (by omega)
  omega

end NS1
