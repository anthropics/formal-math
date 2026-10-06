/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Bounds up to a constant factor, in several parameters

The paper writes `f = O(g)` for functions of several parameters that are tied by side conditions,
such as `D ^ 18 ≤ n` for the parameters `n`, `D`, `w`. `Dominated dom f g` says this: there is a
constant `C ≥ 0` with `f x ≤ C * g x` for every tuple `x` of parameters that satisfies `dom x`. If
there is no side condition, `dom` is `fun _ => True`. The type `α` of the parameters is best a
structure with one named field for each of them, so that a bound reads
`Dominated (fun p => p.D ^ 18 ≤ p.n) (fun p => cost p) fun p => p.n ^ 2 / p.D`.

The lemmas of this file are the steps that the paper takes without comment: such bounds can be
chained (`Dominated.trans`), added (`Dominated.add`, `Dominated.add_add`), multiplied and divided
(`Dominated.mul`, `Dominated.mul_left`, `Dominated.const_mul`, `Dominated.pow`,
`Dominated.div_right`), joined by a case distinction (`Dominated.ite`), restricted to a smaller
domain (`Dominated.mono_dom`) and specialized (`Dominated.comp`). With them no proof has to name a
constant. A bound enters the calculus by `Dominated.of_le`, `Dominated.of_le_const_mul` or
`Dominated.of_exists_const`, and leaves it by `obtain ⟨C, hC, hle⟩` or `Dominated.exists_const_and`.
For functions of one natural number, `Dominated.of_eventually` takes a bound for all large `n`,
`Dominated.isBigO` gives Mathlib's `f =O[atTop] g`, and `isBigO_comp_add_one` substitutes a size
that need not tend to infinity.

In every closure lemma the bound comes first and the side conditions follow.

For nonnegative `f` and `g` the notion is Mathlib's `f =O[𝓟 {x | dom x}] g`, big-O along the
principal filter of the domain (`dominated_iff_isBigO_principal`). The one-sided form is taken
because a running time is bounded from above only.

## The notions of "bounded up to a constant" in this library

* `f =O[atTop] g` of Mathlib bounds `|f|` for large `n`. In this sense `IsBigOPow f a` is `O(n^a)`,
  `IsPowPolylog f a` is `O(n^a (log n)^e)` for some `e`, and `IsPowLittleO f a` is `n^{a+o(1)}`.
  The exponents of the theorems are stated with them.
* `UpperBigOPow`, `UpperPowPolylog` and `UpperPowLittleO` are the same three classes as bounds on
  `f` and not on `|f|`, for running times. A two-sided bound gives the one-sided one
  (`IsBigOPow.upperBigOPow`, `IsPowPolylog.upperPowPolylog`, `IsPowLittleO.upperPowLittleO`).
* `Dominated dom f g` bounds `f` on the whole domain, for several parameters. It comes from a bound
  for large `n` by `Dominated.of_eventually` and gives one by `Dominated.isBigO`.
* `Scale.SoftO t e` says that a count `t` with values in `ℕ` is `Dominated` by a monomial with the
  exponents `e`, up to powers of one more quantity; the tactic `growth` reads the exponents off an
  explicit expression. It gives a `Dominated` bound by `Scale.SoftO.dominated`. Its instance
  `SoftOSqrtPow` gives `IsPowPolylog` by `SoftOSqrtPow.isPowPolylog`.
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp

/-- `f = O(g)` on the domain `dom`: there is a constant `C ≥ 0` with `f x ≤ C * g x` whenever
`dom x`. It is an upper bound on `f` and not on `|f|`. -/
def Dominated {α : Type*} (dom : α → Prop) (f g : α → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, dom x → f x ≤ C * g x

namespace Dominated

variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

/-! ### Entering the calculus -/

/-- A bound with an explicit nonnegative constant. -/
theorem of_le_const_mul {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ x, dom x → f x ≤ C * g x) :
    Dominated dom f g :=
  ⟨C, hC, hfg⟩

/-- A bound with constant one. -/
theorem of_le (hfg : ∀ x, dom x → f x ≤ g x) : Dominated dom f g :=
  ⟨1, zero_le_one, fun x hx => by simpa only [one_mul] using hfg x hx⟩

/-- Every function is bounded by itself. -/
protected theorem refl (dom : α → Prop) (f : α → ℝ) : Dominated dom f f :=
  of_le fun _ _ => le_rfl

/-- A bound with a constant of unknown sign, when `g` is nonnegative on the domain. -/
theorem of_exists_const (hfg : ∃ C : ℝ, ∀ x, dom x → f x ≤ C * g x) (hg : ∀ x, dom x → 0 ≤ g x) :
    Dominated dom f g := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨|C|, abs_nonneg C, fun x hx =>
    (hC x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hg x hx))⟩

/-- For nonnegative functions, `Dominated` is Mathlib's big-O along the principal filter of the
domain. -/
theorem _root_.ThreeSumApsp.dominated_iff_isBigO_principal (hf : ∀ x, dom x → 0 ≤ f x)
    (hg : ∀ x, dom x → 0 ≤ g x) : Dominated dom f g ↔ f =O[𝓟 {x | dom x}] g := by
  have hnorm : ∀ (C : ℝ) x, dom x → (‖f x‖ ≤ C * ‖g x‖ ↔ f x ≤ C * g x) := fun C x hx => by
    rw [Real.norm_of_nonneg (hf x hx), Real.norm_of_nonneg (hg x hx)]
  rw [isBigO_principal]
  exact ⟨fun ⟨C, _, h⟩ => ⟨C, fun x hx => (hnorm C x hx).2 (h x hx)⟩,
    fun ⟨C, h⟩ => of_exists_const ⟨C, fun x hx => (hnorm C x hx).1 (h x hx)⟩ hg⟩

/-- A constant is `O(g)` when `g ≥ 1` on the domain. -/
protected theorem const (c : ℝ) (hg : ∀ x, dom x → 1 ≤ g x) : Dominated dom (fun _ => c) g :=
  ⟨|c|, abs_nonneg c, fun x hx =>
    (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) (hg x hx))⟩

/-! ### Leaving the calculus -/

/-- Two bounds, by nonnegative functions, hold with one constant. -/
theorem exists_const_and (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂)
    (hg₁ : ∀ x, dom x → 0 ≤ g₁ x) (hg₂ : ∀ x, dom x → 0 ≤ g₂ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, dom x → f₁ x ≤ C * g₁ x ∧ f₂ x ≤ C * g₂ x := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  exact ⟨C + D, add_nonneg hC hD, fun x hx =>
    ⟨(h₁ x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (hg₁ x hx)),
      (h₂ x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (hg₂ x hx))⟩⟩

/-! ### Chaining, restricting, substituting -/

/-- `f = O(g)` and `g = O(h)` give `f = O(h)`. -/
protected theorem trans (hfg : Dominated dom f g) (hgh : Dominated dom g h) :
    Dominated dom f h := by
  obtain ⟨C, hC, hf⟩ := hfg
  obtain ⟨D, hD, hg⟩ := hgh
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => (hf x hx).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hg x hx) hC

/-- A bound holds on every smaller domain. -/
theorem mono_dom (hfg : Dominated dom f g) (hdom : ∀ x, dom' x → dom x) : Dominated dom' f g := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun x hx => hf x (hdom x hx)⟩

/-- The left side may be replaced by a smaller function. -/
theorem mono_left (hfg : Dominated dom f g) (hle : ∀ x, dom x → f' x ≤ f x) : Dominated dom f' g :=
  (of_le hle).trans hfg

/-- The right side may be replaced by a larger function. -/
theorem mono_right (hfg : Dominated dom f g) (hle : ∀ x, dom x → g x ≤ g' x) : Dominated dom f g' :=
  hfg.trans (of_le hle)

/-- Both sides may be replaced by functions that agree with them on the domain. -/
protected theorem congr (hfg : Dominated dom f g) (hf : ∀ x, dom x → f x = f' x)
    (hg : ∀ x, dom x → g x = g' x) : Dominated dom f' g' :=
  (hfg.mono_left fun x hx => (hf x hx).ge).mono_right fun x hx => (hg x hx).le

/-- Substituting the parameters: a bound in `x` gives a bound in `y` at `x = φ y`, on every domain
that `φ` maps into `dom`. -/
protected theorem comp (hfg : Dominated dom f g) (φ : β → α) {dom' : β → Prop}
    (hφ : ∀ y, dom' y → dom (φ y)) : Dominated dom' (fun y => f (φ y)) fun y => g (φ y) := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun y hy => hf (φ y) (hφ y hy)⟩

/-! ### Sums and case distinctions -/

/-- `O(h) + O(h) = O(h)`. -/
protected theorem add (hf : Dominated dom f h) (hg : Dominated dom g h) :
    Dominated dom (fun x => f x + g x) h := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  rw [add_mul]
  exact add_le_add (hf x hx) (hg x hx)

/-- `O(g₁) + O(g₂) = O(g₁ + g₂)` for nonnegative `g₁`, `g₂`. -/
theorem add_add (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂) (hg₁ : ∀ x, dom x → 0 ≤ g₁ x)
    (hg₂ : ∀ x, dom x → 0 ≤ g₂ x) : Dominated dom (fun x => f₁ x + f₂ x) fun x => g₁ x + g₂ x :=
  (h₁.mono_right fun x hx => le_add_of_nonneg_right (hg₂ x hx)).add
    (h₂.mono_right fun x hx => le_add_of_nonneg_left (hg₁ x hx))

/-- A case distinction: a bound on `f₁` where `p` holds and a bound on `f₂` where it does not, both
by the same nonnegative `g`. -/
protected theorem ite {p : α → Prop} [DecidablePred p]
    (h₁ : Dominated (fun x => dom x ∧ p x) f₁ g) (h₂ : Dominated (fun x => dom x ∧ ¬p x) f₂ g)
    (hg : ∀ x, dom x → 0 ≤ g x) : Dominated dom (fun x => if p x then f₁ x else f₂ x) g := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  change (if p x then f₁ x else f₂ x) ≤ (C + D) * g x
  split_ifs with hp
  · exact (h₁ x ⟨hx, hp⟩).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (hg x hx))
  · exact (h₂ x ⟨hx, hp⟩).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (hg x hx))

/-! ### Products and quotients -/

/-- A nonnegative constant factor on the left side is absorbed. -/
theorem const_mul (hfg : Dominated dom f g) {c : ℝ} (hc : 0 ≤ c) :
    Dominated dom (fun x => c * f x) g := by
  obtain ⟨C, hC, hf⟩ := hfg
  refine ⟨c * C, mul_nonneg hc hC, fun x hx => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x hx) hc

/-- A nonnegative constant factor on the left side is absorbed. -/
theorem mul_const (hfg : Dominated dom f g) {c : ℝ} (hc : 0 ≤ c) :
    Dominated dom (fun x => f x * c) g := by
  simpa only [mul_comm] using hfg.const_mul hc

/-- A constant factor of any sign in front of a function that is nonnegative on the domain is
absorbed. -/
theorem const_mul_of_nonneg (hfg : Dominated dom f g) (c : ℝ) (hf : ∀ x, dom x → 0 ≤ f x) :
    Dominated dom (fun x => c * f x) g :=
  (of_exists_const ⟨c, fun _ _ => le_rfl⟩ hf).trans hfg

/-- Both sides may be multiplied from the left by a function that is nonnegative on the domain. -/
theorem mul_left (hfg : Dominated dom f g) (hk : ∀ x, dom x → 0 ≤ k x) :
    Dominated dom (fun x => k x * f x) fun x => k x * g x := by
  obtain ⟨C, hC, hf⟩ := hfg
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hf x hx) (hk x hx)

/-- Both sides may be multiplied from the right by a function that is nonnegative on the domain. -/
theorem mul_right (hfg : Dominated dom f g) (hk : ∀ x, dom x → 0 ≤ k x) :
    Dominated dom (fun x => f x * k x) fun x => g x * k x := by
  simpa only [mul_comm] using hfg.mul_left hk

/-- Both sides may be divided by a function that is nonnegative on the domain. -/
theorem div_right (hfg : Dominated dom f g) (hk : ∀ x, dom x → 0 ≤ k x) :
    Dominated dom (fun x => f x / k x) fun x => g x / k x := by
  simpa only [div_eq_mul_inv] using hfg.mul_right fun x hx => inv_nonneg.2 (hk x hx)

/-- `O(g₁) · O(g₂) = O(g₁ g₂)` for nonnegative `f₁`, `f₂`. -/
protected theorem mul (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂)
    (hf₁ : ∀ x, dom x → 0 ≤ f₁ x) (hf₂ : ∀ x, dom x → 0 ≤ f₂ x) :
    Dominated dom (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => ?_⟩
  rw [mul_mul_mul_comm]
  exact mul_le_mul (h₁ x hx) (h₂ x hx) (hf₂ x hx) ((hf₁ x hx).trans (h₁ x hx))

/-- `O(g) ^ e = O(g ^ e)` for nonnegative `f`. -/
protected theorem pow (hfg : Dominated dom f g) (hf : ∀ x, dom x → 0 ≤ f x) (e : ℕ) :
    Dominated dom (fun x => f x ^ e) fun x => g x ^ e := by
  obtain ⟨C, hC, hle⟩ := hfg
  refine ⟨C ^ e, pow_nonneg hC e, fun x hx => ?_⟩
  rw [← mul_pow]
  exact pow_le_pow_left₀ (hf x hx) (hle x hx) e

/-! ### Functions of one natural number -/

/-- A bound that holds from some unknown point on. If `g` is positive from `n₀` on, the finitely
many values in between cost only a larger constant. -/
theorem of_eventually {f g : ℕ → ℝ} {C : ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ C * g n) {n₀ : ℕ}
    (hg : ∀ n, n₀ ≤ n → 0 < g n) : Dominated (fun n => n₀ ≤ n) f g := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hfg
  have hterm : ∀ m, 0 ≤ |f m| / |g m| := fun m => div_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsum : 0 ≤ ∑ m ∈ Finset.range N, |f m| / |g m| := Finset.sum_nonneg fun m _ => hterm m
  refine ⟨|C| + ∑ m ∈ Finset.range N, |f m| / |g m|, add_nonneg (abs_nonneg C) hsum, fun n hn => ?_⟩
  have hgn : 0 < g n := hg n hn
  rw [add_mul]
  obtain hlt | hge := lt_or_ge n N
  · calc f n ≤ |f n| / |g n| * g n := by
          rw [abs_of_pos hgn, div_mul_cancel₀ _ hgn.ne']
          exact le_abs_self _
      _ ≤ (∑ m ∈ Finset.range N, |f m| / |g m|) * g n :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun m => |f m| / |g m|)
            (fun m _ => hterm m) (Finset.mem_range.2 hlt)) hgn.le
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (abs_nonneg C) hgn.le)
  · exact ((hN n hge).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hgn.le)).trans
      (le_add_of_nonneg_right (mul_nonneg hsum hgn.le))

/-- A bound by a nonnegative `g` that holds from some unknown point on gives a bound by `g + 1`
everywhere. -/
theorem of_eventually_add_one {f g : ℕ → ℝ} {C : ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ C * g n)
    (hg : ∀ n, 0 ≤ g n) : Dominated (fun _ => True) f fun n => g n + 1 := by
  have hpos : ∀ n, 0 ≤ n → 0 < g n + 1 := fun n _ => add_pos_of_nonneg_of_pos (hg n) zero_lt_one
  refine (of_eventually (C := |C|) (hfg.mono fun n hn => hn.trans ?_) hpos).mono_dom
    fun n _ => n.zero_le
  exact (mul_le_mul_of_nonneg_right (le_abs_self C) (hg n)).trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (abs_nonneg C))

/-- A bound on `|f|` from some point on is Mathlib's `f =O[atTop] g`. -/
theorem isBigO {f g : ℕ → ℝ} {n₀ : ℕ} (hfg : Dominated (fun n => n₀ ≤ n) (fun n => |f n|) g) :
    f =O[atTop] g := by
  obtain ⟨C, hC, hle⟩ := hfg
  refine IsBigO.of_bound C (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hle n hn).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)

end Dominated

/-- If `G = O(g)` with `g ≥ 0`, then `G(size n) = O(g(size n) + 1)` for every `size : ℕ → ℕ`. The
sizes need not tend to infinity; the `+ 1` covers the finitely many sizes at which the bound does
not hold yet. -/
theorem isBigO_comp_add_one {G g : ℕ → ℝ} (hG : G =O[atTop] g) (hg : ∀ s, 0 ≤ g s)
    (size : ℕ → ℕ) : (fun n => G (size n)) =O[atTop] fun n => g (size n) + 1 := by
  obtain ⟨C, hC⟩ := hG.bound
  have hall : Dominated (fun _ => True) (fun s => |G s|) fun s => g s + 1 :=
    .of_eventually_add_one (C := C) (hC.mono fun s hs => by
      rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hg s)] at hs) hg
  exact Dominated.isBigO (n₀ := 0) (hall.comp size fun _ _ => trivial)

end ThreeSumApsp
