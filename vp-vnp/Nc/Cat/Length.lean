/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cat.Mean
import Nc.Cat.Len

/-!
# Mean squares of prices on `ℤ²` give a length function with the crossing inequality
-/

open Filter Topology Finset

namespace Cat

/-- For every `n` and every sheet a pseudometric on `ℤ²`, Lipschitz with one constant, with the
inequality (Q). -/
structure Lip (W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ) (Λ : ℝ) : Prop where
  nonneg : ∀ n b P P', 0 ≤ W n b P P'
  self : ∀ n b P, W n b P P = 0
  symm : ∀ n b P P', W n b P P' = W n b P' P
  tri : ∀ n b P P' P'', W n b P P'' ≤ W n b P P' + W n b P' P''
  lip : ∀ n b (P h : ℤ × ℤ), W n b P (P + h) ≤ Λ * (|(h.1 : ℝ)| + |(h.2 : ℝ)|)
  q : ∀ n b (X V Y U m m' k k' : ℤ × ℤ) (p q τ : ℝ), 0 ≤ p → 0 ≤ q → 0 < τ →
    2 * (p * W n b X V + q * W n b Y U) ≤
      p * (W n b X m + W n b V m' + W n b X k + W n b V k')
      + q * (W n b Y m + W n b U m' + W n b U k + W n b Y k')
      + τ * (p ^ 2 + q ^ 2) + (W n b m m' ^ 2 + W n b k k' ^ 2) / (2 * τ)

variable {W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ} {Λ : ℝ}

/-- The distance of two translates of the base point. -/
def df (W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ) (u v : ℤ × ℤ) : Fn :=
  fun n b i k => W n b ((i, k) + u) ((i, k) + v)

/-- The root mean square of the distances of `P` and `P+h`. -/
noncomputable def len (W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ) (h : ℤ × ℤ) : ℝ := nm (df W 0 h)

namespace Lip

variable (H : Lip W Λ)
include H

theorem bd (u v : ℤ × ℤ) : Bd (df W u v) := by
  refine ⟨Λ * (|((v - u).1 : ℝ)| + |((v - u).2 : ℝ)|), fun n b i k => ?_⟩
  rw [df, abs_of_nonneg (H.nonneg _ _ _ _)]
  have := H.lip n b ((i, k) + u) (v - u)
  rwa [add_assoc, add_sub_cancel] at this

theorem nm_df (u v : ℤ × ℤ) : nm (df W u v) = len W (u - v) := by
  have h1 : df W u v = df W v u := by
    funext n b i k
    exact H.symm _ _ _ _
  have h2 : df W v u = fun n b i k => df W 0 (u - v) n b (i + v.1) (k + v.2) := by
    funext n b i k
    simp only [df, add_zero]
    congr 1
    · ext <;> simp
  rw [h1, h2, nm_shift (H.bd _ _)]
  rfl

theorem nm_df' (u v : ℤ × ℤ) : nm (df W u v) = len W (v - u) := by
  rw [← H.nm_df v u]
  congr 1
  funext n b i k
  exact H.symm _ _ _ _

theorem len_zero : len W 0 = 0 := by
  have : df W 0 0 * df W 0 0 = fun _ _ _ _ => (0 : ℝ) := by
    funext n b i k
    simp [df, H.self]
  rw [len, nm, this, mean_const, Real.sqrt_zero]

/-- By translation invariance the root mean square is even. -/
theorem len_neg (h : ℤ × ℤ) : len W (-h) = len W h := by
  have := H.nm_df 0 h
  rw [zero_sub] at this
  exact this.symm

/-- By translation invariance and Minkowski's inequality the root mean square is subadditive. -/
theorem len_add (h h' : ℤ × ℤ) : len W (h + h') ≤ len W h + len W h' := by
  have h1 : nm (df W 0 (h + h')) ≤ nm (df W 0 h + df W h (h + h')) :=
    nm_mono (H.bd _ _) ((H.bd _ _).add (H.bd _ _)) (fun n b i k => H.nonneg _ _ _ _)
      (Eventually.of_forall fun n b i _ k _ => H.tri _ _ _ _ _)
  have h2 := nm_add_le (H.bd 0 h) (H.bd h (h + h'))
  rw [H.nm_df' h, add_sub_cancel_left] at h2
  exact h1.trans h2

/-- By the inequality of Cauchy and Schwarz the root mean square satisfies (Q), with the norms of differences for the
distances. -/
theorem len_q (X V Y U m m' k k' : ℤ × ℤ) (τ : ℝ) (hτ : 0 < τ) :
    2 * (len W (X - V) ^ 2 + len W (Y - U) ^ 2) ≤
      len W (X - V) * (len W (X - m) + len W (V - m') + len W (X - k) + len W (V - k'))
      + len W (Y - U) * (len W (Y - m) + len W (U - m') + len W (U - k) + len W (Y - k'))
      + τ * (len W (X - V) ^ 2 + len W (Y - U) ^ 2)
      + (len W (m - m') ^ 2 + len W (k - k') ^ 2) / (2 * τ) := by
  have hb := H.bd
  have key : mean ((2 : ℝ) • (df W X V * df W X V + df W Y U * df W Y U)) ≤
      mean (df W X V * df W X m + df W X V * df W V m' + df W X V * df W X k
        + df W X V * df W V k' + (df W Y U * df W Y m + df W Y U * df W U m'
        + df W Y U * df W U k + df W Y U * df W Y k')
        + τ • (df W X V * df W X V + df W Y U * df W Y U)
        + (1 / (2 * τ)) • (df W m m' * df W m m' + df W k k' * df W k k')) := by
    apply mean_le
    · repeat' first | exact hb _ _ | apply Bd.smul | apply Bd.add | apply Bd.mul
    · repeat' first | exact hb _ _ | apply Bd.smul | apply Bd.add | apply Bd.mul
    intro n b i j
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    have h := H.q n b ((i, j) + X) ((i, j) + V) ((i, j) + Y) ((i, j) + U) ((i, j) + m)
      ((i, j) + m') ((i, j) + k) ((i, j) + k') _ _ τ (H.nonneg n b ((i, j) + X) ((i, j) + V))
      (H.nonneg n b ((i, j) + Y) ((i, j) + U)) hτ
    simp only [df]
    rw [one_div, inv_mul_eq_div]
    simp only [pow_two] at h
    linarith
  have e1 : mean ((2 : ℝ) • (df W X V * df W X V + df W Y U * df W Y U)) =
      2 * (len W (X - V) ^ 2 + len W (Y - U) ^ 2) := by
    rw [mean_smul, mean_add, ← nm_sq (hb _ _), ← nm_sq (hb _ _), H.nm_df, H.nm_df]
    all_goals repeat' first | exact hb _ _ | apply Bd.smul | apply Bd.add | apply Bd.mul
  rw [e1] at key
  have e2 : mean (df W X V * df W X m + df W X V * df W V m' + df W X V * df W X k
        + df W X V * df W V k' + (df W Y U * df W Y m + df W Y U * df W U m'
        + df W Y U * df W U k + df W Y U * df W Y k')
        + τ • (df W X V * df W X V + df W Y U * df W Y U)
        + (1 / (2 * τ)) • (df W m m' * df W m m' + df W k k' * df W k k')) =
      mean (df W X V * df W X m) + mean (df W X V * df W V m') + mean (df W X V * df W X k)
        + mean (df W X V * df W V k') + (mean (df W Y U * df W Y m) + mean (df W Y U * df W U m')
        + mean (df W Y U * df W U k) + mean (df W Y U * df W Y k'))
        + τ * (len W (X - V) ^ 2 + len W (Y - U) ^ 2)
        + 1 / (2 * τ) * (len W (m - m') ^ 2 + len W (k - k') ^ 2) := by
    rw [mean_add, mean_add, mean_add, mean_add, mean_add, mean_add, mean_add, mean_add,
      mean_add, mean_smul, mean_smul, mean_add, mean_add, ← nm_sq (hb _ _), ← nm_sq (hb _ _),
      ← nm_sq (hb _ _), ← nm_sq (hb _ _), H.nm_df, H.nm_df, H.nm_df, H.nm_df]
    all_goals repeat' first | exact hb _ _ | apply Bd.smul | apply Bd.add | apply Bd.mul
  rw [e2] at key
  have cs : ∀ a b c d : ℤ × ℤ, mean (df W a b * df W c d) ≤ len W (a - b) * len W (c - d) := by
    intro a b c d
    rw [← H.nm_df, ← H.nm_df]
    exact mean_mul_le (hb _ _) (hb _ _)
  have c1 := cs X V X m
  have c2 := cs X V V m'
  have c3 := cs X V X k
  have c4 := cs X V V k'
  have c5 := cs Y U Y m
  have c6 := cs Y U U m'
  have c7 := cs Y U U k
  have c8 := cs Y U Y k'
  rw [one_div, inv_mul_eq_div] at key
  linarith

end Lip

end Cat
