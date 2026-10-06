/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.Dominated
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Log

/-!
# Orders of growth of counts

The time and the need of a program are natural numbers, given by explicit expressions in the
parameters of the input.  Only their order of growth is needed.  This file has one calculus
that reads the order of growth off such an expression, so that no constant is ever written out.

A *scale* (`Scale α ι`) fixes the parameters `x : α` for which bounds are claimed (`dom`) and some
quantities that are at least 1 there: the *bases* `base i`, whose powers are counted, and one more,
`hidden`, whose powers are not.  `s.SoftO t e` says that the count `t` is at most a constant times a
power of `hidden` times the monomial `∏ i, base i ^ e i`.  Three examples:

* bases `n`, `√D`, `κ log n` and `hidden = 1`: `s.SoftO t ![2, 1, 1]` is `t = O(n² √D κ log n)`;
* one base `√n` and `hidden = log n`: `s.SoftO t ![3]` is `t = Õ(n^{3/2})`;
* no base and `hidden = n U`: `s.SoftO t ![]` says that `t` is polynomially bounded.

So `SoftO` is `O` up to powers of `hidden`: it is `O` itself if `hidden = 1`, and `Õ` if `hidden` is
a logarithm.  The bounds hold on the whole domain and not only from some point on.

The exponents follow the expression.  A constant has the exponents 0 (`SoftO.const`), a sum the
larger ones (`SoftO.add`), a product their sum (`SoftO.mul`), a power their multiple (`SoftO.pow`).
Exponents may be raised (`SoftO.mono`), and the count may be replaced by a smaller one
(`SoftO.of_le`, `SoftO.of_forall_le`).  If every base is at most `2 ^ hidden`, the binary logarithm
of a bounded count has the exponents 0 (`SoftO.log2`).

The tactic `growth [h₁, h₂, …]` applies these rules from the outside to the inside of the
expression.  The facts `hᵢ` bound the quantities at which the rules stop: parameters, and functions
whose bound is a lemma of its own.  A function that is to be followed into its definition is
unfolded first.

A bound leaves the calculus by `SoftO.exists_le`, or as a `Dominated` statement by
`SoftO.dominated`.
-/

@[expose] public section

namespace ThreeSumApsp

/-- What upper bounds are measured in: quantities that are at least 1 on a domain. -/
structure Scale (α ι : Type*) where
  /-- The parameters for which bounds are claimed. -/
  dom : α → Prop
  /-- The quantity whose powers are not counted. -/
  hidden : α → ℝ
  /-- The quantities whose powers are counted. -/
  base : ι → α → ℝ
  /-- `hidden ≥ 1` on the domain. -/
  one_le_hidden : ∀ x, dom x → 1 ≤ hidden x
  /-- Every base is at least 1 on the domain. -/
  one_le_base : ∀ i x, dom x → 1 ≤ base i x

namespace Scale

/-- The scale with the given bases in which nothing is hidden. -/
def ofBases {α ι : Type*} (dom : α → Prop) (base : ι → α → ℝ)
    (h : ∀ i x, dom x → 1 ≤ base i x) : Scale α ι where
  dom := dom
  hidden _ := 1
  base := base
  one_le_hidden _ _ := le_rfl
  one_le_base := h

variable {α ι : Type*} [Fintype ι] (s : Scale α ι)

/-- The monomial `∏ i, base i ^ e i`. -/
noncomputable def mon (e : ι → ℕ) (x : α) : ℝ := ∏ i, s.base i x ^ e i

/-- The count `t` is at most a constant times a power of `hidden` times the monomial with the
exponents `e`, on the domain of the scale. -/
def SoftO (t : α → ℕ) (e : ι → ℕ) : Prop :=
  ∃ c : ℕ, Dominated s.dom (fun x => (t x : ℝ)) fun x => s.hidden x ^ c * s.mon e x

theorem mon_zero (x : α) : s.mon 0 x = 1 := by simp [mon]

theorem mon_add (e e' : ι → ℕ) (x : α) : s.mon (e + e') x = s.mon e x * s.mon e' x := by
  simp only [mon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem mon_smul (k : ℕ) (e : ι → ℕ) (x : α) : s.mon (k • e) x = s.mon e x ^ k := by
  simp only [mon, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm k]

theorem mon_single [DecidableEq ι] (i : ι) (x : α) : s.mon (Pi.single i 1) x = s.base i x := by
  simp [mon, Pi.single_apply, pow_ite]

variable {s} {x : α} {e e' : ι → ℕ} {c c' : ℕ}

/-- All bases are at least 1, so a monomial grows with its exponents. -/
theorem mon_le_mon (he : ∀ i, e i ≤ e' i) (hx : s.dom x) : s.mon e x ≤ s.mon e' x :=
  Finset.prod_le_prod (fun i _ => pow_nonneg (zero_le_one.trans (s.one_le_base i x hx)) _)
    fun i _ => pow_le_pow_right₀ (s.one_le_base i x hx) (he i)

/-- A monomial is at least 1. -/
theorem one_le_mon (e : ι → ℕ) (hx : s.dom x) : 1 ≤ s.mon e x :=
  (s.mon_zero x).ge.trans (mon_le_mon (fun _ => Nat.zero_le _) hx)

/-- The bound grows with all exponents. -/
theorem pow_mul_mon_le (hc : c ≤ c') (he : ∀ i, e i ≤ e' i) (hx : s.dom x) :
    s.hidden x ^ c * s.mon e x ≤ s.hidden x ^ c' * s.mon e' x :=
  mul_le_mul (pow_le_pow_right₀ (s.one_le_hidden x hx) hc) (mon_le_mon he hx)
    (zero_le_one.trans (one_le_mon e hx)) (pow_nonneg (zero_le_one.trans (s.one_le_hidden x hx)) _)

namespace SoftO

variable {t t₁ t₂ : α → ℕ} {e₁ e₂ : ι → ℕ}

/-! ### Entering and leaving -/

/-- A count that is at most `hidden`. -/
theorem of_le_hidden (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.hidden x) : s.SoftO t 0 :=
  ⟨1, .of_le fun x hx => by simpa only [pow_one, mon_zero, mul_one] using h x hx⟩

/-- A count that is at most a constant times a base. -/
theorem of_dominated_base [DecidableEq ι] (i : ι)
    (h : Dominated s.dom (fun x => (t x : ℝ)) (s.base i)) : s.SoftO t (Pi.single i 1) :=
  ⟨0, h.congr (fun _ _ => rfl) fun x _ => by rw [pow_zero, mon_single, one_mul]⟩

/-- A count that is at most a base. -/
theorem of_le_base [DecidableEq ι] (i : ι) (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.base i x) :
    s.SoftO t (Pi.single i 1) :=
  of_dominated_base i (.of_le h)

/-- A count that is at most a constant times a monomial. -/
theorem of_dominated (h : Dominated s.dom (fun x => (t x : ℝ)) (s.mon e)) : s.SoftO t e :=
  ⟨0, by simpa only [pow_zero, one_mul] using h⟩

/-- The bound, written out. -/
theorem exists_le (h : s.SoftO t e) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ x, s.dom x → (t x : ℝ) ≤ C * (s.hidden x ^ c * s.mon e x) :=
  let ⟨c, C, hC, hle⟩ := h
  ⟨C, c, hC, hle⟩

/-- If `hidden = 1`, the bound is the monomial. -/
theorem dominated (h : s.SoftO t e) (hhidden : ∀ x, s.dom x → s.hidden x = 1) :
    Dominated s.dom (fun x => (t x : ℝ)) (s.mon e) :=
  let ⟨_, h⟩ := h
  h.congr (fun _ _ => rfl) fun x hx => by rw [hhidden x hx, one_pow, one_mul]

/-! ### The rules -/

/-- The exponents may be raised. -/
theorem mono (h : s.SoftO t e) (he : ∀ i, e i ≤ e' i) : s.SoftO t e' :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_right fun _ hx => pow_mul_mon_le le_rfl he hx⟩

/-- A smaller count has the same bound. -/
theorem of_le (h : s.SoftO t₂ e) (hle : ∀ x, s.dom x → t₁ x ≤ t₂ x) : s.SoftO t₁ e :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_left fun x hx => Nat.cast_le.2 (hle x hx)⟩

/-- A quantity `f` that is at most `g` everywhere has the bound of `g`, at any argument. -/
theorem of_forall_le {β : Type*} {f g : β → ℕ} (hle : ∀ y, f y ≤ g y) {u : α → β}
    (h : s.SoftO (fun x => g (u x)) e) : s.SoftO (fun x => f (u x)) e :=
  h.of_le fun _ _ => hle _

/-- A quantity `f` with two arguments that is at most `g` everywhere has the bound of `g`. -/
theorem of_forall_le₂ {β γ : Type*} {f g : β → γ → ℕ} (hle : ∀ y z, f y z ≤ g y z) {u : α → β}
    {v : α → γ} (h : s.SoftO (fun x => g (u x) (v x)) e) : s.SoftO (fun x => f (u x) (v x)) e :=
  h.of_le fun _ _ => hle _ _

/-- A constant has the exponents 0. -/
protected theorem const (k : ℕ) : s.SoftO (fun _ => k) 0 :=
  ⟨0, .const _ fun x _ => by rw [pow_zero, mon_zero, mul_one]⟩

/-- A sum has the larger exponents. -/
protected theorem add (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x + t₂ x) (e₁ ⊔ e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨max c₁ c₂, ?_⟩
  simpa only [Nat.cast_add] using
    (h₁.mono_right fun _ hx =>
      pow_mul_mon_le (e' := e₁ ⊔ e₂) (le_max_left _ _) (fun _ => le_sup_left) hx).add
      (h₂.mono_right fun _ hx => pow_mul_mon_le (le_max_right _ _) (fun _ => le_sup_right) hx)

/-- A sum of two counts with the same bound. -/
theorem add_le (h₁ : s.SoftO t₁ e) (h₂ : s.SoftO t₂ e) : s.SoftO (fun x => t₁ x + t₂ x) e :=
  (h₁.add h₂).mono fun _ => (sup_idem _).le

/-- In a product the exponents add up. -/
protected theorem mul (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x * t₂ x) (e₁ + e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨c₁ + c₂, ?_⟩
  simpa only [Nat.cast_mul] using
    (h₁.mul h₂ (fun _ _ => Nat.cast_nonneg _) fun _ _ => Nat.cast_nonneg _).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_add, pow_add, mul_mul_mul_comm]

/-- The `k`-th power multiplies the exponents by `k`. -/
protected theorem pow (h : s.SoftO t e) (k : ℕ) : s.SoftO (fun x => t x ^ k) (k • e) := by
  obtain ⟨c, h⟩ := h
  refine ⟨c * k, ?_⟩
  simpa only [Nat.cast_pow] using
    (h.pow (fun _ _ => Nat.cast_nonneg _) k).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_smul, mul_pow, pow_mul]

/-- A maximum has the larger exponents. -/
protected theorem max (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => max (t₁ x) (t₂ x)) (e₁ ⊔ e₂) :=
  (h₁.add h₂).of_le fun _ _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-- A difference has the exponents of its first term. -/
protected theorem sub (h : s.SoftO t₁ e) (t₂ : α → ℕ) : s.SoftO (fun x => t₁ x - t₂ x) e :=
  h.of_le fun _ _ => Nat.sub_le _ _

/-- A quotient has the exponents of its numerator. -/
protected theorem div (h : s.SoftO t₁ e) (t₂ : α → ℕ) : s.SoftO (fun x => t₁ x / t₂ x) e :=
  h.of_le fun _ _ => Nat.div_le_self _ _

/-- A quotient that is rounded up has the larger exponents of numerator and denominator. -/
protected theorem ceilDiv (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x ⌈/⌉ t₂ x) (e₁ ⊔ e₂) :=
  (h₁.add h₂).of_le fun _ _ =>
    (Nat.ceilDiv_eq_add_pred_div _ _).trans_le ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))

/-- A logarithm is at most the number. -/
protected theorem log (h : s.SoftO t e) (b : ℕ) : s.SoftO (fun x => Nat.log b (t x)) e :=
  h.of_le fun _ _ => Nat.log_le_self _ _

/-- A square root is at most the number. -/
protected theorem sqrt (h : s.SoftO t e) : s.SoftO (fun x => Nat.sqrt (t x)) e :=
  h.of_le fun _ _ => Nat.sqrt_le_self _

/-- The binary logarithm of a bounded count is at most a constant times `hidden`, if every base is
at most `2 ^ hidden`. -/
theorem log2 (hs : ∀ i x, s.dom x → s.base i x ≤ 2 ^ s.hidden x) (h : s.SoftO t e) :
    s.SoftO (fun x => Nat.log 2 (t x)) 0 := by
  obtain ⟨C, c, hC, hle⟩ := h.exists_le
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt C (one_lt_two (α := ℝ))
  refine ⟨1, K + c + ∑ i, e i, by positivity, fun x hx => ?_⟩
  have hf : 1 ≤ s.hidden x := s.one_le_hidden x hx
  have hhidden : s.hidden x ≤ 2 ^ s.hidden x := by
    have := one_add_mul_self_le_rpow_one_add (s := 1) (by norm_num) hf
    norm_num at this
    linarith
  have hbase := fun i => zero_le_one.trans (s.one_le_base i x hx)
  have hpow : (t x : ℝ) ≤ 2 ^ ((K + c + ∑ i, e i : ℕ) * s.hidden x) :=
    calc (t x : ℝ) ≤ C * (s.hidden x ^ c * s.mon e x) := hle x hx
      _ ≤ 2 ^ K * ((2 ^ s.hidden x) ^ c * ∏ i, (2 ^ s.hidden x) ^ e i) := by
          have hmon := zero_le_one.trans (one_le_mon e hx)
          gcongr
          exact Finset.prod_le_prod (fun i _ => pow_nonneg (hbase i) _)
            fun i _ => pow_le_pow_left₀ (hbase i) (hs i x hx) _
      _ ≤ (2 ^ s.hidden x) ^ K * ((2 ^ s.hidden x) ^ c * ∏ i, (2 ^ s.hidden x) ^ e i) := by
          gcongr
          exact (Real.rpow_one 2).ge.trans (Real.rpow_le_rpow_of_exponent_le one_le_two hf)
      _ = 2 ^ ((K + c + ∑ i, e i : ℕ) * s.hidden x) := by
          rw [Finset.prod_pow_eq_pow_sum, ← pow_add, ← pow_add, ← add_assoc, ← Real.rpow_natCast,
            ← Real.rpow_mul zero_le_two, mul_comm]
  simp only [pow_one, mon_zero, mul_one]
  rcases Nat.eq_zero_or_pos (t x) with h0 | hpos
  · rw [h0, Nat.log_zero_right, Nat.cast_zero]
    positivity
  · have hlog : (2 : ℝ) ^ (Nat.log 2 (t x) : ℝ) ≤ t x := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
    exact_mod_cast (Real.rpow_le_rpow_left_iff one_lt_two).1 (hlog.trans hpow)

end SoftO

end Scale

/-- Takes a goal `s.SoftO t ?e` apart, from the outside to the inside of the expression `t`, and
finds the exponents.  Constants, sums, products, powers with a constant exponent, maxima,
differences and quotients are treated by the rules of the calculus.  Every other quantity needs one
of the given facts.  A fact may be a rule with hypotheses, such as `SoftO.of_forall_le h` for an
inequality `h`, or `SoftO.log`.  The quantities for which no fact is given remain as goals. -/
macro "growth_rules" "[" hs:term,* "]" : tactic =>
  `(tactic|
    repeat' with_reducible first
      | exact Scale.SoftO.const _
      $[| apply $hs]*
      | apply Scale.SoftO.add
      | apply Scale.SoftO.mul
      | apply Scale.SoftO.pow
      | apply Scale.SoftO.max
      | apply Scale.SoftO.sub
      | apply Scale.SoftO.div)

/-- Proves `s.SoftO t e`: finds the exponents of the expression `t` with `growth_rules` and the
given facts, and compares them with `e`.  If they are larger than `e`, the summands of `t` whose
exponents are larger remain as goals. -/
macro "growth" "[" hs:term,* "]" : tactic =>
  `(tactic|
    first
      | (apply Scale.SoftO.mono
         · growth_rules [$hs,*]
         · first
             | decide
             | exact isEmptyElim)
      | (fail_if_success (fail_if_success
          (apply Scale.SoftO.mono
           on_goal 1 => (growth_rules [$hs,*]; done)))
         repeat' with_reducible apply Scale.SoftO.add_le
         all_goals try
           (apply Scale.SoftO.mono
            · growth_rules [$hs,*]
            · decide))
      | (apply Scale.SoftO.mono
         · growth_rules [$hs,*]))

end ThreeSumApsp
