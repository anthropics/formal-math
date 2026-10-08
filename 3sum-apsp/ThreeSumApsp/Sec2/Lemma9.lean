/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma7_8
public import ThreeSumApsp.Sec2.Levels

/-!
# Lemma 9: one run of `Full` computes all the products `X_Q Y_Q`

Section 2.3.3. The inner set of a string is the set of the levels at which it has
an inner variable (`p`, `q` or `z₀`). For a set `Q` of `m` levels, the left strings with inner set
`Q` index the entries of an `N₀ × D` matrix `X_Q`, the right strings those of a `D × N₀` matrix
`Y_Q`, and the output strings those of the product `X_Q Y_Q`. The arrays `a` and `b` hold all the
`X_Q` and all the `Y_Q` side by side. Lemma 9 says that `Mult(a, b)[w] = (X_Q Y_Q)[w]` for every
output string `w` with such an inner set.

* The strings with inner set `Q` are `leftStrOf Q hQ r π`, `rightStrOf Q hQ π c` and
  `outStrOf Q hQ r c` (`existsUnique_leftStr`, `existsUnique_rightStr`, `existsUnique_outStr`). At
  the first two the arrays hold `X_Q[r, π]` and `Y_Q[π, c]` (`arrayL_leftStrOf`,
  `arrayR_rightStrOf`).
* The two facts about `γ` that the proof needs are finite checks on the definition of `gamma`
  (`gamma_z0`, `gamma_x_y_z`); no other lemma is used for them.
* The proof of Lemma 9. By Lemma 8 the entry at `w` is a sum over all pairs `(u, v)`. In a summand
  that is not zero, `u` has inner set `Q`, the row of `w` as its outer part and some inner part `π`,
  and `v` has inner set `Q`, the column of `w` as its outer part and the same inner part
  (`exists_of_summand_ne_zero`). Each of these summands has coefficient 1 (`prod_gamma_eq_one`).
  Their sum is the entry of the matrix product (`Mult_arrays_eq_mul`, `lemma_9`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The sizes of the matrices, and Figure 4 -/

/-- Section 2.3.3: there are `N₀` strings of `L - m` outer left (or right) variables. -/
theorem card_outerStr (L m : ℕ) : Fintype.card (OuterStr L m) = N0 L m := by
  simp [N0]

/-- Section 2.3.3: there are `D` strings of `m` inner left (or right) variables. -/
theorem card_innerStr (m : ℕ) : Fintype.card (InnerStr m) = D m := by
  simp [D]

/-- Section 2.3.3: there are `K = binom(L, m)` subsets `Q` of `{1, …, L}` of size `m`. -/
theorem card_subsets_eq_K (L m : ℕ) :
    (univ.filter fun Q : Finset (Fin L) => Q.card = m).card = K L m := by
  rw [univ_filter_card_eq, card_powersetCard, card_univ, Fintype.card_fin, K]

/-- Figure 4, for `L = 6` and `m = 2`.  This docstring counts levels and indices from 1,
as the paper does; the Lean text counts them from 0, so that the inner set {2, 5} is `{1, 4}` and x₁
is `.x 0`.  The strings `u = x₁ p₁₁ x₂ x₃ p₂₂ x₁`, `v = y₃ q₁₁ y₁ y₃ q₂₂ y₂` and
`w = z₁₃ z₀ z₂₁ z₃₃ z₀ z₁₂` have the inner set `{2, 5}`; `u` has the outer part `x₁x₂x₃x₁` and the
inner part `p₁₁p₂₂`; `v` has the inner part `q₁₁q₂₂` and the outer part `y₃y₁y₃y₂`; `w` has the row
`x₁x₂x₃x₁` and the column `y₃y₁y₃y₂`.  The sizes `81 × 16`, `16 × 81` and `81 × 81` of the matrices
and the number `binom(6, 2) = 15` of products, which the figure also shows, are not stated here. -/
theorem figure_4 :
    innerSetL (![.x 0, .p 0 0, .x 1, .x 2, .p 1 1, .x 0] : LeftStr 6) = {1, 4}
      ∧ innerSetR (![.y 2, .q 0 0, .y 0, .y 2, .q 1 1, .y 1] : RightStr 6) = {1, 4}
      ∧ innerSetO (![.z 0 2, .z0, .z 1 0, .z 2 2, .z0, .z 0 1] : OutStr 6) = {1, 4}
      ∧ ∃ (hu : (innerSetL (![.x 0, .p 0 0, .x 1, .x 2, .p 1 1, .x 0] : LeftStr 6)).card = 2)
          (hv : (innerSetR (![.y 2, .q 0 0, .y 0, .y 2, .q 1 1, .y 1] : RightStr 6)).card = 2)
          (hw : (innerSetO (![.z 0 2, .z0, .z 1 0, .z 2 2, .z0, .z 0 1] : OutStr 6)).card = 2),
          outerPartL _ hu = ![0, 1, 2, 0] ∧ innerPartL _ hu = ![(0, 0), (1, 1)]
            ∧ innerPartR _ hv = ![(0, 0), (1, 1)] ∧ outerPartR _ hv = ![2, 0, 2, 1]
            ∧ rowO _ hw = ![0, 1, 2, 0] ∧ colO _ hw = ![2, 0, 2, 1] := by
  have hQ : ({1, 4} : Finset (Fin 6)).card = 2 := by decide
  -- The paper's levels 2 and 5 are the levels 1 and 4 here. These two and the other four, in order:
  have hinn : ⇑(innerLevel ({1, 4} : Finset (Fin 6)) hQ) = ![1, 4] :=
    (orderEmbOfFin_unique hQ (by decide) (by decide)).symm
  have hout : ⇑(outerLevel ({1, 4} : Finset (Fin 6)) hQ) = (![0, 2, 3, 5] : Fin (6 - 2) → Fin 6) :=
    (orderEmbOfFin_unique (card_compl_of_card_eq _ hQ) (by decide) (by decide)).symm
  have hL : innerSetL (![.x 0, .p 0 0, .x 1, .x 2, .p 1 1, .x 0] : LeftStr 6) = {1, 4} := by decide
  have hR : innerSetR (![.y 2, .q 0 0, .y 0, .y 2, .q 1 1, .y 1] : RightStr 6) = {1, 4} := by decide
  have hO : innerSetO (![.z 0 2, .z0, .z 1 0, .z 2 2, .z0, .z 0 1] : OutStr 6) = {1, 4} := by decide
  refine ⟨hL, hR, hO, hL.symm ▸ hQ, hR.symm ▸ hQ, hO.symm ▸ hQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    funext k
    simp only [outerPartL, innerPartL, innerPartR, outerPartR, rowO, colO, hinn, hout,
      innerLevel_congr _ hQ hL, outerLevel_congr _ hQ hL, innerLevel_congr _ hQ hR,
      outerLevel_congr _ hQ hR, outerLevel_congr _ hQ hO]
    decide +revert

/-! ### The input arrays -/

/-- The entry of the left input array at the string with inner set `Q`, outer part `r` and inner
part `π` is `X_Q[r, π]`. -/
@[simp]
theorem arrayL_leftStrOf {L m : ℕ} (X : Finset (Fin L) → LeftMat L m) (Q : Finset (Fin L))
    (hQ : Q.card = m) (r : OuterStr L m) (π : InnerStr m) :
    arrayL m X (leftStrOf Q hQ r π) = X Q r π := by
  have h : (innerSetL (leftStrOf Q hQ r π)).card = m := by rw [innerSetL_leftStrOf, hQ]
  rw [arrayL, dif_pos h, outerPartL_leftStrOf, innerPartL_leftStrOf, innerSetL_leftStrOf]

/-- The entry of the right input array at the string with inner set `Q`, inner part `π` and outer
part `c` is `Y_Q[π, c]`. -/
@[simp]
theorem arrayR_rightStrOf {L m : ℕ} (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L))
    (hQ : Q.card = m) (π : InnerStr m) (c : OuterStr L m) :
    arrayR m Y (rightStrOf Q hQ π c) = Y Q π c := by
  have h : (innerSetR (rightStrOf Q hQ π c)).card = m := by rw [innerSetR_rightStrOf, hQ]
  rw [arrayR, dif_pos h, innerPartR_rightStrOf, outerPartR_rightStrOf, innerSetR_rightStrOf]

/-! ### The proof of Lemma 9 -/

/-- In the proof of Lemma 9: "the only monomials of G + E that contain z₀ are the p_ij q_ij
z₀, with coefficient 1." Stated for `γ(s, t, z₀)`, which is the coefficient of `s t z₀` in `G + E`
by `gamma_eq_coeff`. -/
theorem gamma_z0 (s : LeftVar) (t : RightVar) :
    gamma s t .z0 = if ∃ i j, s = .p i j ∧ t = .q i j then 1 else 0 := by
  decide +revert

/-- In the proof of Lemma 9: "The only monomial of G + E that contains z_ij and no inner
variable is x_i y_j z_ij, with coefficient 1". Stated for `γ(x_i', y_j', z_ij)`, which is the
coefficient of `x_i' y_j' z_ij` in `G + E` by `gamma_eq_coeff`. -/
theorem gamma_x_y_z (i' j' i j : Fin 3) :
    gamma (.x i') (.y j') (.z i j) = if i' = i ∧ j' = j then 1 else 0 := by
  decide +revert

/-- The statement on `γ(x_i', y_j', z_ij)` as it is used: if `s` and `t` are outer and
`γ(s, t, z_ij) ≠ 0`, then `(s, t) = (x_i, y_j)`. -/
private theorem eq_x_y_of_gamma_ne_zero {s : LeftVar} {t : RightVar} {i j : Fin 3}
    (hs : ¬ s.IsInner) (ht : ¬ t.IsInner) (h : gamma s t (.z i j) ≠ 0) : s = .x i ∧ t = .y j := by
  rcases s with i' | _
  · rcases t with j' | _
    · by_contra hne
      exact h ((gamma_x_y_z i' j' i j).trans
        (if_neg fun ⟨hi, hj⟩ => hne ⟨hi ▸ rfl, hj ▸ rfl⟩))
    · exact (ht trivial).elim
  · exact (hs trivial).elim

/-- The summands of Lemma 8 that can be nonzero. Let `w` be the output string with inner
set `Q`, row `r` and column `c`. If `γ(u_ℓ, v_ℓ, w_ℓ) ≠ 0` at every level and the inner sets of `u`
and `v` have `m` elements, then `u` has inner set `Q`, outer part `r` and some inner part `π`, and
`v` has inner set `Q`, outer part `c` and the inner part with the same indices. -/
private theorem exists_of_summand_ne_zero {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) {u : LeftStr L} {v : RightStr L}
    (hγ : ∀ ℓ, gamma (u ℓ) (v ℓ) (outStrOf Q hQ r c ℓ) ≠ 0) (hu : (innerSetL u).card = m)
    (hv : (innerSetR v).card = m) : ∃ π, u = leftStrOf Q hQ r π ∧ v = rightStrOf Q hQ π c := by
  simp only [outStrOf, forall_level_iff Q hQ, glue_innerLevel, glue_outerLevel] at hγ
  obtain ⟨hγin, hγout⟩ := hγ
  -- "at a level ℓ ∈ Q we have w_ℓ = z₀ […] So (u_ℓ, v_ℓ) = (p_ij, q_ij) for some i, j."
  have hin : ∀ k, ∃ ij : Fin 2 × Fin 2,
      u (innerLevel Q hQ k) = .p ij.1 ij.2 ∧ v (innerLevel Q hQ k) = .q ij.1 ij.2 := fun k => by
    by_contra hne
    exact hγin k ((gamma_z0 _ _).trans (if_neg fun ⟨i, j, h⟩ => hne ⟨(i, j), h⟩))
  choose π hπ using hin
  -- "Thus u and v have an inner variable at every level of Q, and their inner sets are therefore
  -- exactly Q."  So "u_ℓ and v_ℓ are outer" at the levels outside Q.
  have huQ : innerSetL u = Q :=
    filter_eq_of_forall_innerLevel Q hQ (fun k => by rw [(hπ k).1]; trivial) hu
  have hvQ : innerSetR v = Q :=
    filter_eq_of_forall_innerLevel Q hQ (fun k => by rw [(hπ k).2]; trivial) hv
  have huout := ((filter_eq_iff_forall_level Q hQ).mp huQ).2
  have hvout := ((filter_eq_iff_forall_level Q hQ).mp hvQ).2
  -- "at a level ℓ ∉ Q we have w_ℓ = z_ij for some i, j […] so (u_ℓ, v_ℓ) = (x_i, y_j)."
  have hout : ∀ k, u (outerLevel Q hQ k) = .x (r k) ∧ v (outerLevel Q hQ k) = .y (c k) :=
    fun k => eq_x_y_of_gamma_ne_zero (huout k) (hvout k) (hγout k)
  exact ⟨π, (eq_glue_iff Q hQ).mpr ⟨fun k => (hπ k).1, fun k => (hout k).1⟩,
    (eq_glue_iff Q hQ).mpr ⟨fun k => (hπ k).2, fun k => (hout k).2⟩⟩

/-- In the proof of Lemma 9: the coefficient of the summand of `π` "is 1". -/
private theorem prod_gamma_eq_one {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) (π : InnerStr m) :
    ∏ ℓ, gamma (leftStrOf Q hQ r π ℓ) (rightStrOf Q hQ π c ℓ) (outStrOf Q hQ r c ℓ) = 1 := by
  have hone : ∀ ℓ,
      gamma (leftStrOf Q hQ r π ℓ) (rightStrOf Q hQ π c ℓ) (outStrOf Q hQ r c ℓ) = 1 := by
    simp only [forall_level_iff Q hQ, leftStrOf, rightStrOf, outStrOf, glue_innerLevel,
      glue_outerLevel]
    exact ⟨fun _ => (gamma_z0 _ _).trans (if_pos ⟨_, _, rfl, rfl⟩),
      fun _ => (gamma_x_y_z _ _ _ _).trans (if_pos ⟨rfl, rfl⟩)⟩
  exact prod_eq_one fun ℓ _ => hone ℓ

/-- Lemma 9 for the output string with inner set `Q`, row `r` and column `c`: by Lemma 8 the entry
is a sum over all pairs `(u, v)`, and the summands that remain are those of the matrix product. -/
theorem Mult_arrays_eq_mul {L m : ℕ} (X : Finset (Fin L) → LeftMat L m)
    (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) :
    Mult (arrayL m X) (arrayR m Y) (outStrOf Q hQ r c) = (X Q * Y Q) r c := by
  -- To show: `∑_{(u,v)} ∏_ℓ γ(u_ℓ, v_ℓ, w_ℓ) a[u] b[v] = ∑_π X_Q[r, π] Y_Q[π, c]`. The right-hand
  -- side is the part of the left-hand side over the pairs `(u, v)` that belong to some `π`.
  rw [lemma_8, Matrix.mul_apply, ← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_of_injective (fun π => (leftStrOf Q hQ r π, rightStrOf Q hQ π c)) ?_ _ _ ?_ ?_
  · -- "There is one such summand for each of the D strings π".
    exact fun π π' h => (leftStrOf_inj.mp (congrArg Prod.fst h)).2
  · -- Every other summand is zero.  "a[u] b[v] ≠ 0 requires the inner sets of u and v to have
    -- exactly m elements."
    rintro ⟨u, v⟩ hnot
    by_contra hne
    obtain ⟨⟨hγ, ha⟩, hb⟩ : ((∏ ℓ, gamma (u ℓ) (v ℓ) (outStrOf Q hQ r c ℓ)) ≠ 0
        ∧ arrayL m X u ≠ 0) ∧ arrayR m Y v ≠ 0 := by
      simpa only [mul_ne_zero_iff] using hne
    obtain ⟨π, rfl, rfl⟩ := exists_of_summand_ne_zero Q hQ r c
      (fun ℓ => prod_ne_zero_iff.mp hγ ℓ (mem_univ ℓ))
      (by_contra fun h => ha (dif_neg h)) (by_contra fun h => hb (dif_neg h))
    exact hnot ⟨π, rfl⟩
  · -- The summand of `π` is `1 · X_Q[r, π] · Y_Q[π, c]`.
    intro π
    rw [prod_gamma_eq_one, one_mul, arrayL_leftStrOf, arrayR_rightStrOf]

/-- **Lemma 9**.  "For the input arrays a, b above and every output string w whose inner
set Q has exactly m elements, Mult(a, b)[w] = (X_Q Y_Q)[w]."  (Equation (4).) -/
theorem lemma_9 {L m : ℕ} (X : Finset (Fin L) → LeftMat L m) (Y : Finset (Fin L) → RightMat L m)
    (w : OutStr L) (h : (innerSetO w).card = m) :
    Mult (arrayL m X) (arrayR m Y) w
      = (X (innerSetO w) * Y (innerSetO w)) (rowO w h) (colO w h) := by
  -- `w` is the output string with the inner set, the row and the column of `w`.
  conv_lhs => rw [outStr_eq_outStrOf h rfl h]
  exact Mult_arrays_eq_mul X Y (innerSetO w) h (rowO w h) (colO w h)

/-- Section 2.3.3: "one run of Full […] computes all K of the products X_Q Y_Q." -/
theorem Full_arrays_eq_mul {L m : ℕ} (X : Finset (Fin L) → LeftMat L m)
    (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) :
    Full L (arrayL m X) (arrayR m Y) (outStrOf Q hQ r c) = (X Q * Y Q) r c := by
  rw [Lemma7.returns_Mult]
  exact Mult_arrays_eq_mul X Y Q hQ r c

end ThreeSumApsp
