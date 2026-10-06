/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Machine.Solving
public import ThreeSumApsp.Util.Asymptotics.Logarithms

/-!
# Changing the bounds of the running-time statements of Section 4

The running-time statements of Section 4 say "there are programs and a constant `C` such that the
time is at most `C f(x)` on the inputs `x` of a domain".  Such a statement stays true for a smaller
domain and for every bound `g` with `f = O(g)` there: `exists_isDataStructure_of_dominated` for a
data structure and `exists_solves_of_dominated` for a program that computes the wanted entries.

This file has the bounds `f = O(g)` that Section 4.4 uses, for functions `N`, `d`, `w` of the input
(the size, the inner dimension and the number of wanted entries):

* with `d ≥ 1`, the logarithmic factors are absorbed by a smaller `γ` and a larger `q`
  (`dominated_preprocessing`, `dominated_query`, `dominated_wanted_sparse`);
* with `d ≥ 2`, `log d + 1 = O(log d)` (`dominated_preprocessing_log`, `dominated_query_log`,
  `dominated_wanted_log`, `dominated_wanted_add`).
-/

public section

open ThreeSumApsp.WordRam
open EndStatement (Instr)

namespace ThreeSumApsp

/-! ## The hypotheses on the input -/

/-- The inner dimension of an input with `1 ≤ lo ≤ D` is at least 1, as a real number. -/
theorem WordRam.Items.thinDom.one_le_D {lo : ℕ} {ε : ℝ} {c₀ : ℕ} {x : ThinPair}
    (h : Items.thinDom lo ε c₀ x) (hlo : 1 ≤ lo := by norm_num) : (1 : ℝ) ≤ (x.D : ℝ) :=
  Nat.one_le_cast.2 (hlo.trans h.2.1)

/-- The inner dimension of an input with `2 ≤ D` is at least 2, as a real number. -/
theorem WordRam.Items.thinDom.two_le_D {ε : ℝ} {c₀ : ℕ} {x : ThinPair}
    (h : Items.thinDom 2 ε c₀ x) : (2 : ℝ) ≤ (x.D : ℝ) :=
  Nat.ofNat_le_cast.2 h.2.1

/-- The lower bound on the inner dimension may be lowered. -/
theorem WordRam.Items.thinDom.mono {lo lo' : ℕ} {ε : ℝ} {c₀ : ℕ} {x : ThinPair}
    (h : Items.thinDom lo' ε c₀ x) (hlo : lo ≤ lo') : Items.thinDom lo ε c₀ x :=
  ⟨h.1, hlo.trans h.2.1, h.2.2.1, h.2.2.2⟩

/-! ## The logarithmic factors are absorbed (`d ≥ 1`) -/

section Absorb

variable {α : Type*} {dom : α → Prop} {N d w : α → ℝ}

/-- `N² d^a (log d + 1)^e = O(N² / d^γ')` for `a < -γ'`. -/
private theorem dominated_sq_mul_rpow_mul_log (hd : ∀ x, dom x → 1 ≤ d x) {a γ' : ℝ}
    (h : a < -γ') (e : ℕ) :
    Dominated dom (fun x => N x ^ 2 * (d x ^ a * (Real.log (d x) + 1) ^ e))
      fun x => N x ^ 2 / d x ^ γ' :=
  (((dominated_rpow_mul_log_add_one_pow_rpow h e).comp d hd).mul_left
    fun x _ => sq_nonneg (N x)).congr (fun _ _ => rfl) fun x hx => by
      rw [Real.rpow_neg (zero_le_one.trans (hd x hx)), div_eq_mul_inv]

/-- The logarithmic factor of the preprocessing is absorbed by a smaller `γ`. -/
theorem dominated_preprocessing (hd : ∀ x, dom x → 1 ≤ d x) {γ γ' : ℝ} (h : γ' < γ) :
    Dominated dom (fun x => N x ^ 2 * (Real.log (d x) + 1) ^ 2 / d x ^ γ)
      fun x => N x ^ 2 / d x ^ γ' :=
  (dominated_sq_mul_rpow_mul_log hd (neg_lt_neg h) 2).congr (fun x hx => by
    rw [Real.rpow_neg (zero_le_one.trans (hd x hx)), div_eq_mul_inv]
    ring) fun _ _ => rfl

/-- The logarithmic factor of a query is absorbed by a larger exponent. -/
theorem dominated_query (hd : ∀ x, dom x → 1 ≤ d x) {q q' : ℝ} (h : q < q') :
    Dominated dom (fun x => d x ^ q * (Real.log (d x) + 1)) fun x => d x ^ q' := by
  simpa only [pow_one] using (dominated_rpow_mul_log_add_one_pow_rpow h 1).comp d hd

/-- Corollary 32: for at most `N² / d^κ` wanted entries, every `γ'` below `γ` and below `κ - q`
absorbs the logarithmic factors. -/
theorem dominated_wanted_sparse (hd : ∀ x, dom x → 1 ≤ d x) {γ γ' q κ : ℝ}
    (hw : ∀ x, dom x → w x ≤ N x ^ 2 / d x ^ κ) (hγ : γ' < γ) (hκ : γ' < κ - q) :
    Dominated dom (fun x => w x * (d x ^ q * (Real.log (d x) + 1))
        + N x ^ 2 * (Real.log (d x) + 1) ^ 2 / d x ^ γ)
      fun x => N x ^ 2 / d x ^ γ' := by
  refine Dominated.add ?_ (dominated_preprocessing hd hγ)
  refine (dominated_sq_mul_rpow_mul_log (a := q - κ) hd (by linarith) 1).mono_left fun x hx => ?_
  have hd0 : 0 < d x := zero_lt_one.trans_le (hd x hx)
  have hlog : 0 ≤ Real.log (d x) + 1 := add_nonneg (Real.log_nonneg (hd x hx)) zero_le_one
  calc w x * (d x ^ q * (Real.log (d x) + 1))
      ≤ N x ^ 2 / d x ^ κ * (d x ^ q * (Real.log (d x) + 1)) :=
        mul_le_mul_of_nonneg_right (hw x hx) (mul_nonneg (Real.rpow_nonneg hd0.le _) hlog)
    _ = N x ^ 2 * (d x ^ (q - κ) * (Real.log (d x) + 1) ^ 1) := by
        rw [Real.rpow_sub hd0, pow_one]
        ring

/-! ## `log d + 1 = O(log d)` (`d ≥ 2`) -/

/-- `log d + 1 = O(log d)`. -/
private theorem dominated_log_add_one (hd : ∀ x, dom x → 2 ≤ d x) :
    Dominated dom (fun x => Real.log (d x) + 1) fun x => Real.log (d x) :=
  dominated_log_add_one_log.comp d hd

private theorem log_add_one_nonneg (hd : ∀ x, dom x → 2 ≤ d x) (x : α) (hx : dom x) :
    0 ≤ Real.log (d x) + 1 :=
  add_nonneg (Real.log_nonneg (one_le_two.trans (hd x hx))) zero_le_one

/-- The preprocessing, with `log d` for `log d + 1`. -/
theorem dominated_preprocessing_log (hd : ∀ x, dom x → 2 ≤ d x) (γ : ℝ) :
    Dominated dom (fun x => N x ^ 2 * (Real.log (d x) + 1) ^ 2 / d x ^ γ)
      fun x => N x ^ 2 * Real.log (d x) ^ 2 / d x ^ γ :=
  ((((dominated_log_add_one hd).pow (log_add_one_nonneg hd) 2).mul_left
    fun x _ => sq_nonneg (N x)).div_right
      fun x hx => Real.rpow_nonneg (zero_le_two.trans (hd x hx)) γ)

/-- A query, with `log d` for `log d + 1`. -/
theorem dominated_query_log (hd : ∀ x, dom x → 2 ≤ d x) (q : ℝ) :
    Dominated dom (fun x => d x ^ q * (Real.log (d x) + 1)) fun x => d x ^ q * Real.log (d x) :=
  (dominated_log_add_one hd).mul_left fun x hx => Real.rpow_nonneg (zero_le_two.trans (hd x hx)) q

/-- Corollary 32: the time for at most `N² / d^κ` wanted entries is
`O(N² log² d (d^{-γ} + d^{q-κ}))`. -/
theorem dominated_wanted_log (hd : ∀ x, dom x → 2 ≤ d x) {γ q κ : ℝ}
    (hw : ∀ x, dom x → w x ≤ N x ^ 2 / d x ^ κ) :
    Dominated dom (fun x => w x * (d x ^ q * (Real.log (d x) + 1))
        + N x ^ 2 * (Real.log (d x) + 1) ^ 2 / d x ^ γ)
      fun x => N x ^ 2 * Real.log (d x) ^ 2 * (d x ^ (-γ) + d x ^ (q - κ)) := by
  have hd0 : ∀ x, dom x → 0 < d x := fun x hx => zero_lt_two.trans_le (hd x hx)
  -- `log d + 1 ≤ (log d + 1)² = O(log² d)`
  have hsq := (dominated_log_add_one hd).pow (log_add_one_nonneg hd) 2
  have hlog : Dominated dom (fun x => Real.log (d x) + 1) fun x => Real.log (d x) ^ 2 :=
    hsq.mono_left fun x hx => by
      nlinarith [Real.log_nonneg (one_le_two.trans (hd x hx))]
  have hqueries : Dominated dom (fun x => w x * (d x ^ q * (Real.log (d x) + 1)))
      fun x => N x ^ 2 * d x ^ (q - κ) * Real.log (d x) ^ 2 :=
    (hlog.mul_left (k := fun x => N x ^ 2 * d x ^ (q - κ)) fun x hx =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hd0 x hx).le _)).mono_left fun x hx => by
        calc w x * (d x ^ q * (Real.log (d x) + 1))
            ≤ N x ^ 2 / d x ^ κ * (d x ^ q * (Real.log (d x) + 1)) :=
              mul_le_mul_of_nonneg_right (hw x hx)
                (mul_nonneg (Real.rpow_nonneg (hd0 x hx).le _) (log_add_one_nonneg hd x hx))
          _ = N x ^ 2 * d x ^ (q - κ) * (Real.log (d x) + 1) := by
              rw [Real.rpow_sub (hd0 x hx)]
              ring
  refine (hqueries.add_add (dominated_preprocessing_log hd γ) (fun x hx => ?_)
    fun x hx => ?_).congr (fun _ _ => rfl) fun x hx => ?_
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hd0 x hx).le _)) (sq_nonneg _)
  · exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg (hd0 x hx).le _)
  · rw [Real.rpow_neg (hd0 x hx).le, div_eq_mul_inv]
    ring

/-- Proof of Theorem 25: the preprocessing and, for each of `w` positions, one query with an
exponent `q ≤ q'` take `O(N² log² d / d^γ + w d^{q'} log d)` time, with `log d` for `log d + 1`. -/
theorem dominated_wanted_add (hd : ∀ x, dom x → 2 ≤ d x) (hw : ∀ x, dom x → 0 ≤ w x) (γ : ℝ)
    {q q' : ℝ} (hq : q ≤ q') :
    Dominated dom (fun x => w x * (d x ^ q * (Real.log (d x) + 1))
        + N x ^ 2 * (Real.log (d x) + 1) ^ 2 / d x ^ γ)
      fun x => N x ^ 2 * Real.log (d x) ^ 2 / d x ^ γ + w x * d x ^ q' * Real.log (d x) := by
  have hd1 : ∀ x, dom x → 1 ≤ d x := fun x hx => one_le_two.trans (hd x hx)
  have hlog : ∀ x, dom x → 0 ≤ Real.log (d x) := fun x hx => Real.log_nonneg (hd1 x hx)
  have hrpow : ∀ (a : ℝ) x, dom x → 0 ≤ d x ^ a := fun a x hx =>
    Real.rpow_nonneg (zero_le_one.trans (hd1 x hx)) a
  have hqueries : Dominated dom (fun x => w x * (d x ^ q * (Real.log (d x) + 1)))
      fun x => w x * d x ^ q' * Real.log (d x) :=
    (((dominated_query_log hd q).mono_right fun x hx => mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (hd1 x hx) hq) (hlog x hx)).mul_left hw).congr
        (fun _ _ => rfl) fun _ _ => (mul_assoc _ _ _).symm
  exact (hqueries.add_add (dominated_preprocessing_log hd γ)
    (fun x hx => mul_nonneg (mul_nonneg (hw x hx) (hrpow q' x hx)) (hlog x hx))
    fun x hx => div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hrpow γ x hx)).congr
      (fun _ _ => rfl) fun _ _ => add_comm _ _

end Absorb

end ThreeSumApsp
