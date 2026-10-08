/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.Lemma27_28

/-!
# The two worked examples of Section 4.2

For `m = 4` and `t = 2`: the box of the leaf `P₁₂ P₀ P₃₁ P₂₂` is `∗ ∗ P₃₁ P₂₂`, in the first row of
Figure 10 (`boxOfLeaf_example_first`), and it has 100 leaves (`leaves_example_first`); the box of
the leaf `P₀ P₂₃ P₀ P₁₁` is `∗ P₂₃ P₀ P₁₁`, in the second row (`boxOfLeaf_example_second`). Nothing
else rests on this file.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

namespace BoxExamples

/-- Figure 10 and the two examples show the four levels `ℓ₁ < ℓ₂ < ℓ₃ < ℓ₄` of `Q` only. Here there
are no other levels: `L = m = 4`, the output string is `z₀ z₀ z₀ z₀`, and the four levels are
`0, 1, 2, 3`. -/
def allInner : OutStr 4 := fun _ => .z0

/-- Section 4.2, for `m = 4` and `t = 2`: "suppose that τ chooses the terms P₁₂, P₀, P₃₁, P₂₂ at the
four levels ℓ₁ < ℓ₂ < ℓ₃ < ℓ₄ of Q. We see P₂₂ at level ℓ₄ and P₃₁ at level ℓ₃, and we stop there,
so the box of τ is ∗ ∗ P₃₁ P₂₂ (in the first row of the figure)." The first row of Figure 10 is the
set `V = {ℓ₁, ℓ₂}`. Lean counts levels and indices from 0, so that `P₁₂` is `.P 0 1`. -/
theorem boxOfLeaf_example_first :
    boxOfLeaf 4 2 allInner ![.P 0 1, .P0, .P 2 0, .P 1 1]
        = ![.star, .star, .term (.P 2 0), .term (.P 1 1)]
      ∧ (![.star, .star, .term (.P 2 0), .term (.P 1 1)] : Cube 4) ∈ BV allInner {0, 1} := by
  refine ⟨by decide, ?_⟩
  rw [BV, mem_filter]
  exact ⟨mem_univ _, by decide⟩

/-- Section 4.2, on the box `∗ ∗ P₃₁ P₂₂` of the leaf `τ = P₁₂ P₀ P₃₁ P₂₂`: "This box contains τ
along with the 99 other leaves that differ from τ only at the levels ℓ₁ and ℓ₂." -/
theorem leaves_example_first :
    ![.P 0 1, .P0, .P 2 0, .P 1 1] ∈
        Cube.leaves (![.star, .star, .term (.P 2 0), .term (.P 1 1)] : Cube 4)
      ∧ (Cube.leaves (![.star, .star, .term (.P 2 0), .term (.P 1 1)] : Cube 4)).card = 100
      ∧ ∀ σ : Leaf 4, σ ∈ Cube.leaves (![.star, .star, .term (.P 2 0), .term (.P 1 1)] : Cube 4) ↔
          σ 2 = .P 2 0 ∧ σ 3 = .P 1 1 := by
  have hleaves : ∀ σ : Leaf 4,
      σ ∈ Cube.leaves (![.star, .star, .term (.P 2 0), .term (.P 1 1)] : Cube 4) ↔
        σ 2 = .P 2 0 ∧ σ 3 = .P 1 1 := fun σ => by
    simp [Fin.forall_fin_succ, eq_comm]
  refine ⟨(hleaves _).2 ⟨rfl, rfl⟩, ?_, hleaves⟩
  rw [Cube.card_leaves, show Cube.starLevels _ = ({0, 1} : Finset (Fin 4)) by decide]
  rfl

/-- Section 4.2, for `m = 4` and `t = 2`: "Similarly, for a leaf that chooses the terms P₀, P₂₃, P₀,
P₁₁, we stop at level ℓ₂, so its box is ∗ P₂₃ P₀ P₁₁ (in the second row of the figure)." The second
row of Figure 10 is the set `V = {ℓ₁, ℓ₃}`. -/
theorem boxOfLeaf_example_second :
    boxOfLeaf 4 2 allInner ![.P0, .P 1 2, .P0, .P 0 0]
        = ![.star, .term (.P 1 2), .term .P0, .term (.P 0 0)]
      ∧ (![.star, .term (.P 1 2), .term .P0, .term (.P 0 0)] : Cube 4) ∈ BV allInner {0, 2} := by
  refine ⟨by decide, ?_⟩
  rw [BV, mem_filter]
  exact ⟨mem_univ _, by decide⟩

end BoxExamples

end ThreeSumApsp
