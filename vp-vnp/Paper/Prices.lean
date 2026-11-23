/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Extension
import Nc.Price.Basic

/-!
# The paper, section "Tensors, prices and duality": prices

The subsection "Prices". The definitions are in Nc/Price/Basic.lean.
-/

namespace Paper

open Ov Ov.Ten Nc.Price Finset Filter MeasureTheory

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- **Paper: Definition def:price.** "A price on a finite set V is a limit of multiples s·d_φ, s ≥ 0, φ a spectral
point on V. A function on the pairs of an arbitrary set Y is a price if all its pull-backs to finite sets are prices." -/
theorem def_price :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℝ), IsPrice K d ↔
      ∀ δ : ℝ, 0 < δ → ∃ (φ : Spec K V) (s : ℝ), 0 ≤ s ∧ ∀ u v, |d u v - s * φ.e u v| < δ) ∧
    ∀ (Y : Type) (w : Y → Y → ℝ), IsPrice K w ↔
      ∀ (V : Type) [Fintype V] [DecidableEq V] (g : V → Y), IsPrice K fun u v => w (g u) (g v) := by
  refine ⟨fun V _ _ d => ⟨fun h δ hδ => h.exists_spec id hδ, fun h => isPrice_of_mem ?_⟩,
    fun Y w => ⟨fun h V _ _ g n f => h n fun i => g (f i), fun h n f => (h (Fin n) f).mem id⟩⟩
  rw [Prices, Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨φ, s, hs, hd⟩ := h δ hδ
  refine ⟨_, ⟨φ, s, hs, rfl⟩, (dist_pi_lt_iff hδ).2 fun u => (dist_pi_lt_iff hδ).2 fun v => ?_⟩
  rw [Real.dist_eq]
  exact hd u v

section Facts

variable {Y : Type*} {w : Y → Y → ℝ}

/-- "Prices are pseudometrics." By Lemma lem:exponents the d_φ are; the conditions are closed and kept by multiples. -/
theorem def_price_pseudometric (h : IsPrice K w) :
    (∀ a b, 0 ≤ w a b) ∧ (∀ a, w a a = 0) ∧ (∀ a b, w a b = w b a) ∧ ∀ a b c, w a c ≤ w a b + w b c := by
  refine ⟨fun a b => ?_, fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · have h2 : (fun i j : Fin 2 => w (![a, b] i) (![a, b] j)) ∈ {d : Fin 2 → Fin 2 → ℝ | 0 ≤ d 0 1} :=
      prices_induction (h 2 ![a, b]) (isClosed_le continuous_const (by fun_prop)) fun φ c hc => by
        obtain ⟨-, -, -, -, -, -, hI, -⟩ := lem_exponents φ
        exact mul_nonneg hc (hI 0 1).1
    exact h2
  · have h2 : (fun i j : Fin 1 => w (![a] i) (![a] j)) ∈ {d : Fin 1 → Fin 1 → ℝ | d 0 0 = 0} :=
      prices_induction (h 1 ![a]) (isClosed_eq (by fun_prop) continuous_const) fun φ c hc => by
        obtain ⟨-, -, -, h0, -⟩ := lem_exponents φ
        show c * φ.e 0 0 = 0
        rw [h0, mul_zero]
    exact h2
  · have h2 : (fun i j : Fin 2 => w (![a, b] i) (![a, b] j)) ∈ {d : Fin 2 → Fin 2 → ℝ | d 0 1 = d 1 0} :=
      prices_induction (h 2 ![a, b]) (isClosed_eq (by fun_prop) (by fun_prop)) fun φ c hc => by
        obtain ⟨-, -, -, -, hs, -⟩ := lem_exponents φ
        show c * φ.e 0 1 = c * φ.e 1 0
        rw [hs]
    exact h2
  · have h2 : (fun i j : Fin 3 => w (![a, b, c] i) (![a, b, c] j)) ∈
        {d : Fin 3 → Fin 3 → ℝ | d 0 2 ≤ d 0 1 + d 1 2} :=
      prices_induction (h 3 ![a, b, c]) (isClosed_le (by fun_prop) (by fun_prop)) fun φ c hc => by
        obtain ⟨-, -, -, -, -, ht, -⟩ := lem_exponents φ
        show c * φ.e 0 2 ≤ c * φ.e 0 1 + c * φ.e 1 2
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (ht _ _ _) hc
    exact h2

/-- "Pull-backs … of prices are prices; for g : V → W one uses t ↦ φ(gt)." (The latter is Nc.Price.specCone_comp, which
makes the two parts of Definition def:price consistent.) -/
theorem def_price_pullback {Z : Type*} (h : IsPrice K w) (g : Z → Y) : IsPrice K fun a b => w (g a) (g b) :=
  fun n f => h n fun i => g (f i)

/-- "Nonnegative multiples … of prices are prices". -/
theorem def_price_multiple (h : IsPrice K w) {c : ℝ} (hc : 0 ≤ c) : IsPrice K fun a b => c * w a b :=
  fun n f => prices_smul (h n f) hc

/-- The set of prices is closed under pointwise convergence. -/
theorem def_price_closed : IsClosed {w : Y → Y → ℝ | IsPrice K w} := by
  have : {w : Y → Y → ℝ | IsPrice K w} = ⋂ (n : ℕ) (f : Fin n → Y),
      (fun (w : Y → Y → ℝ) i j => w (f i) (f j)) ⁻¹' Prices K (Fin n) := by
    ext w
    simp [IsPrice]
  rw [this]
  exact isClosed_iInter fun n => isClosed_iInter fun f =>
    isClosed_closure.preimage (continuous_comp f)

/-- "Pointwise limits of prices are prices". -/
theorem def_price_limit {ι : Type*} {l : Filter ι} [l.NeBot] {d : ι → Y → Y → ℝ}
    (h : ∀ a b, Tendsto (fun i => d i a b) l (nhds (w a b))) (hd : ∀ᶠ i in l, IsPrice K (d i)) : IsPrice K w := by
  refine def_price_closed.mem_of_tendsto ?_ hd
  rw [tendsto_pi_nhds]
  intro a
  rw [tendsto_pi_nhds]
  exact h a

/-- "The prices below a given function form a compact set, by Tychonoff's theorem." -/
theorem def_price_compact (C : Y → Y → ℝ) : IsCompact {w : Y → Y → ℝ | IsPrice K w ∧ ∀ a b, w a b ≤ C a b} := by
  have h1 : IsCompact {w : Y → Y → ℝ | ∀ a, w a ∈ {v : Y → ℝ | ∀ b, v b ∈ Set.Icc 0 (C a b)}} :=
    isCompact_pi_infinite fun a => isCompact_pi_infinite fun b => isCompact_Icc
  have h2 : IsClosed {w : Y → Y → ℝ | ∀ a b, w a b ≤ C a b} := by
    have : {w : Y → Y → ℝ | ∀ a b, w a b ≤ C a b} = ⋂ (a : Y) (b : Y), {w | w a b ≤ C a b} := by
      ext w; simp
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (by fun_prop) continuous_const
  refine h1.of_isClosed_subset (def_price_closed.inter h2) ?_
  rintro w ⟨hw, hC⟩ a b
  exact ⟨(def_price_pseudometric hw).1 a b, hC a b⟩

end Facts

end Paper

/-! The same facts in the form in which the development cites them. -/

namespace Nc.Price

variable {K : Type} [Field K] {Y : Type*} {w : Y → Y → ℝ}

theorem IsPrice.nonneg (h : IsPrice K w) (a b : Y) : 0 ≤ w a b := (Paper.def_price_pseudometric h).1 a b

theorem IsPrice.self (h : IsPrice K w) (a : Y) : w a a = 0 := (Paper.def_price_pseudometric h).2.1 a

theorem IsPrice.symm (h : IsPrice K w) (a b : Y) : w a b = w b a := (Paper.def_price_pseudometric h).2.2.1 a b

theorem IsPrice.triangle (h : IsPrice K w) (a b c : Y) : w a c ≤ w a b + w b c :=
  (Paper.def_price_pseudometric h).2.2.2 a b c

theorem IsPrice.comp {Z : Type*} (h : IsPrice K w) (g : Z → Y) : IsPrice K fun a b => w (g a) (g b) :=
  Paper.def_price_pullback h g

theorem IsPrice.smul (h : IsPrice K w) {c : ℝ} (hc : 0 ≤ c) : IsPrice K fun a b => c * w a b :=
  Paper.def_price_multiple h hc

theorem isPrice_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {d : ι → Y → Y → ℝ}
    (h : ∀ a b, Filter.Tendsto (fun i => d i a b) l (nhds (w a b))) (hd : ∀ᶠ i in l, IsPrice K (d i)) : IsPrice K w :=
  Paper.def_price_limit h hd

theorem isCompact_isPrice_le (C : Y → Y → ℝ) : IsCompact {w : Y → Y → ℝ | IsPrice K w ∧ ∀ a b, w a b ≤ C a b} :=
  Paper.def_price_compact C

end Nc.Price

namespace Paper

open Ov Ov.Ten Nc.Price Finset Filter MeasureTheory

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

section Spectral

variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- Proof of Proposition prop:random, the finite case for w = d_φ: "Let C be the product of all wires ⟨2⟩_uv with u, v ∈ Y, and
apply Proposition prop:extend. For every pair e of Y ∪ Q we obtain d_φ′(e) ≤ ∑ θ_l d_φ(π_l e). On Y we have d_φ′ ≤ d_φ with
equality for the sum over all pairs, hence equality for each." -/
theorem prop_random_spectral (F : Spec K P) {m : ℕ} (θ : Fin m → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (σ : Fin m → Q → P) :
    ∃ F' : Spec K (P ⊕ Q), (∀ p p', F'.e (Sum.inl p) (Sum.inl p') = F.e p p') ∧
      ∀ a b, F'.e a b ≤ ∑ l, θ l * F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
  classical
  obtain ⟨F', hle, hC⟩ := prop_extend (K := K) (Sum.inl : P → P ⊕ Q)
    (fun l => Sum.elim id (σ l)) (fun l i => rfl) θ hθ hθ1 F
    (Ten.prod fun e : P × P => Ten.wire K 2 e.1 e.2)
  have hb : ∀ a b, F'.e a b ≤ ∑ l, θ l * F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
    intro a b
    have h1 := hle (Ten.wire K 2 a b)
    have h2 : ∀ l, F.F (Ten.push (Sum.elim id (σ l)) (Ten.wire K 2 a b)) =
        2 ^ F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
      intro l
      rw [← F.pull_F, (F.pull _).wire_two, F.pull_e]
    simp only [h2] at h1
    rw [F'.wire_two] at h1
    have h3 : ∏ l, ((2 : ℝ) ^ F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)) ^ θ l =
        2 ^ ∑ l, θ l * F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
      rw [Real.rpow_sum_of_pos (by norm_num)]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [← Real.rpow_mul (by norm_num), mul_comm]
    rw [h3] at h1
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h1
  refine ⟨F', ?_, hb⟩
  have hle' : ∀ p p', F'.e (Sum.inl p) (Sum.inl p') ≤ F.e p p' := by
    intro p p'
    refine (hb (Sum.inl p) (Sum.inl p')).trans (le_of_eq ?_)
    simp only [Sum.elim_inl, id]
    rw [← Finset.sum_mul, hθ1, one_mul]
  have hsum : ∑ e : P × P, F'.e (Sum.inl e.1) (Sum.inl e.2) = ∑ e : P × P, F.e e.1 e.2 := by
    rw [← F'.pull_F, (F'.pull _).prod, F.prod] at hC
    simp only [Spec.wire_two, Spec.pull_e] at hC
    rw [← Real.rpow_sum_of_pos (by norm_num), ← Real.rpow_sum_of_pos (by norm_num)] at hC
    have h2 := congrArg (Real.logb 2) hC
    rwa [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]
      at h2
  intro p p'
  have h1 := (Finset.sum_eq_sum_iff_of_le
    (fun (e : P × P) _ => hle' e.1 e.2)).1 hsum (p, p') (Finset.mem_univ _)
  exact h1

end Spectral

section Random

/-- Proof of Proposition prop:random, the reduction to finite sets: "It is enough to find, for all finite Y₀ ⊆ Y and Q₀ ⊆ Q
such that σ maps Q₀ into Y₀, a price on Y₀ ∪ Q₀ with the two properties: these prices form compact sets, so then there is
one that works for all of them at once." Here Z is Y ∪ Q, the two properties are bounds A ≤ |oo′| ≤ B, and the compact
sets are those of def_price_compact. -/
theorem prop_random_compact {Z : Type*} (A B : Z → Z → ℝ)
    (h : ∀ S : Finset Z, ∃ d : S → S → ℝ, IsPrice K d ∧ ∀ a b : S, A a b ≤ d a b ∧ d a b ≤ B a b) :
    ∃ w' : Z → Z → ℝ, IsPrice K w' ∧ ∀ a b, A a b ≤ w' a b ∧ w' a b ≤ B a b := by
  classical
  choose d hd hAB using h
  -- the price on T, as a function on all pairs
  let D : Finset Z → Z → Z → ℝ := fun T a b => if h : a ∈ T ∧ b ∈ T then d T ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
  have hD : ∀ {S T : Finset Z} (hT : S ⊆ T) (a b : S), D T a b = d T ⟨a, hT a.2⟩ ⟨b, hT b.2⟩ :=
    fun hT a b => dif_pos ⟨hT a.2, hT b.2⟩
  let U : Ultrafilter (Finset Z) := Ultrafilter.of atTop
  have hmem : ∀ S : Finset Z, ∀ᶠ T in (U : Filter (Finset Z)), S ⊆ T := fun S =>
    Ultrafilter.of_le _ (eventually_ge_atTop S)
  -- on every finite set S the restrictions have a limit, in the compact set of the prices on S below B
  have key : ∀ S : Finset Z, ∃ v : S → S → ℝ, (IsPrice K v ∧ ∀ a b : S, v a b ≤ B a b) ∧
      ∀ a b : S, Tendsto (fun T => D T a b) U (nhds (v a b)) := by
    intro S
    obtain ⟨v, hv, hlim⟩ := (def_price_compact (K := K) fun a b : S => B a b).ultrafilter_le_nhds
      (U.map fun T (a b : S) => D T a b) (by
        rw [le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
        filter_upwards [hmem S] with T hT
        have e : (fun a b : S => D T a b) = fun a b : S => d T ⟨a, hT a.2⟩ ⟨b, hT b.2⟩ := by
          funext a b
          exact hD hT a b
        refine ⟨?_, fun a b => (hD hT a b).le.trans (hAB T _ _).2⟩
        show IsPrice K fun a b : S => D T a b
        rw [e]
        exact def_price_pullback (hd T) fun a : S => (⟨a, hT a.2⟩ : T))
    have h1 : Tendsto (fun T (a b : S) => D T a b) U (nhds v) := hlim
    exact ⟨v, hv, fun a b => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h1 a) b⟩
  choose v hv hlim using key
  have ha : ∀ a b : Z, a ∈ ({a, b} : Finset Z) := fun a b => by simp
  have hb : ∀ a b : Z, b ∈ ({a, b} : Finset Z) := fun a b => by simp
  -- the limits fit together
  have hfit : ∀ (S : Finset Z) (a b : S), v S a b = v {a.1, b.1} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩ := fun S a b =>
    tendsto_nhds_unique (hlim S a b) (hlim {a.1, b.1} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩)
  refine ⟨fun a b => v {a, b} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩, isPrice_of_finset fun S => ?_, fun a b => ⟨?_, ?_⟩⟩
  · have e : (fun a b : S => v {a.1, b.1} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩) = v S := by
      funext a b
      exact (hfit S a b).symm
    rw [e]
    exact (hv S).1
  · refine ge_of_tendsto (hlim {a, b} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩) ?_
    filter_upwards [hmem {a, b}] with T hT
    exact ((hAB T _ _).1.trans (hD hT ⟨a, ha _ _⟩ ⟨b, hb _ _⟩).ge :)
  · exact (hv {a, b}).2 ⟨a, ha _ _⟩ ⟨b, hb _ _⟩

/-- Proof of Proposition prop:random, the finite case: "So let Y and Q be finite, and let σ take the values π_l with
probabilities θ_l. By a limit we may assume w = s·d_φ, and then s = 1 by homogeneity." The prices that
prop_random_spectral gives for approximations s·d_φ of w have a limit, since they lie in a compact set (def_price_compact). -/
theorem prop_random_limit {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {w : P → P → ℝ}
    (hw : IsPrice K w) {m : ℕ} (θ : Fin m → ℝ) (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1) (σ : Fin m → Q → P) :
    ∃ w' : P ⊕ Q → P ⊕ Q → ℝ, IsPrice K w' ∧ (∀ p p', w' (Sum.inl p) (Sum.inl p') = w p p') ∧
      ∀ a b, w' a b ≤ ∑ l, θ l * w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have hle1 : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  -- w is s·d_φ up to 1/(n+1)
  choose φ s hs hφ using fun n : ℕ => hw.exists_spec (id : P → P) (hpos n)
  choose φ' h1 h2 using fun n => prop_random_spectral (φ n) θ hθ hθ1 σ
  let B : P ⊕ Q → P ⊕ Q → ℝ := fun a b => ∑ l, θ l * w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)
  let d : ℕ → P ⊕ Q → P ⊕ Q → ℝ := fun n a b => s n * (φ' n).e a b
  have hd : ∀ n, IsPrice K (d n) := fun n => def_price_multiple (isPrice_spec (φ' n)) (hs n)
  have hdB : ∀ n a b, d n a b ≤ B a b + 1 / (n + 1) := by
    intro n a b
    calc s n * (φ' n).e a b
        ≤ s n * ∑ l, θ l * (φ n).e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) :=
          mul_le_mul_of_nonneg_left (h2 n a b) (hs n)
      _ = ∑ l, θ l * (s n * (φ n).e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      _ ≤ ∑ l, θ l * (w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) + 1 / (n + 1)) := by
        refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hθ l)
        have h3 := (abs_lt.1 (hφ n (Sum.elim id (σ l) a) (Sum.elim id (σ l) b))).1
        simp only [id] at h3
        linarith
      _ = B a b + 1 / (n + 1) := by
        simp only [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hθ1, one_mul]
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨w', ⟨hw', -⟩, hlim⟩ := (def_price_compact (K := K) fun a b => B a b + 1).ultrafilter_le_nhds (U.map d) (by
    rw [le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact univ_mem' fun n => ⟨hd n, fun a b => (hdB n a b).trans (by linarith [hle1 n])⟩)
  have hlim' : ∀ a b, Tendsto (fun n => d n a b) U (nhds (w' a b)) := by
    intro a b
    have h3 : Tendsto d U (nhds w') := hlim
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h3 a) b
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) U (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (Ultrafilter.of_le _)
  refine ⟨w', hw', fun p p' => ?_, fun a b => ?_⟩
  · have h3 : Tendsto (fun n => d n (Sum.inl p) (Sum.inl p') - w p p') U (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_) hzero
      have h4 := hφ n p p'
      simp only [id] at h4
      rw [Real.norm_eq_abs, abs_sub_comm]
      show |w p p' - s n * (φ' n).e (Sum.inl p) (Sum.inl p')| ≤ _
      rw [h1]
      exact h4.le
    have h4 := tendsto_nhds_unique h3 ((hlim' (Sum.inl p) (Sum.inl p')).sub_const (w p p'))
    linarith
  · exact le_of_tendsto_of_tendsto (hlim' a b) ((hzero.const_add (B a b)).trans (by rw [add_zero]))
      (Eventually.of_forall fun n => hdB n a b)

/-- Proof of Proposition prop:random: "let σ take the values π_l with probabilities θ_l". On a finite set T of new points a
random map, each σ(o) having finitely many values, takes finitely many values π_l; with their probabilities θ_l, the
expectation of any function of the map is a finite mean. -/
theorem prop_random_values {Y Q Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Q → Ω → Y)
    (hfin : ∀ κ, (Set.range (σ κ)).Finite) (hmeas : ∀ κ y, MeasurableSet (σ κ ⁻¹' {y})) (T : Finset Q) :
    ∃ (m : ℕ) (θ : Fin m → ℝ) (π : Fin m → T → Y), (∀ l, 0 ≤ θ l) ∧ ∑ l, θ l = 1 ∧
      ∀ f : (T → Y) → ℝ, ∫ ω, f (fun κ : T => σ κ ω) ∂μ = ∑ l, θ l * f (π l) := by
  classical
  have hfin' : (Set.range fun ω (κ : T) => σ κ ω).Finite := by
    refine (Set.Finite.pi' fun κ : T => hfin κ).subset ?_
    rintro _ ⟨ω, rfl⟩ κ
    exact ⟨ω, rfl⟩
  let V : Finset (T → Y) := hfin'.toFinset
  have hV : ∀ ω, (fun κ : T => σ κ ω) ∈ V := fun ω => by simp [V]
  have hmeas' : ∀ f : T → Y, MeasurableSet {ω | (fun κ : T => σ κ ω) = f} := by
    intro f
    have : {ω | (fun κ : T => σ κ ω) = f} = ⋂ κ : T, σ κ ⁻¹' {f κ} := by
      ext ω
      simp [funext_iff]
    rw [this]
    exact MeasurableSet.iInter fun κ => hmeas _ _
  let e : Fin V.card ≃ V := V.equivFin.symm
  have hmean : ∀ f : (T → Y) → ℝ, ∫ ω, f (fun κ : T => σ κ ω) ∂μ =
      ∑ l : Fin V.card, μ.real {ω | (fun κ : T => σ κ ω) = (e l : T → Y)} * f (e l) := by
    intro f
    have h1 : ∀ ω, f (fun κ : T => σ κ ω) = ∑ g ∈ V,
        ({ω | (fun κ : T => σ κ ω) = g}).indicator (fun _ => f g) ω := by
      intro ω
      rw [Finset.sum_eq_single (fun κ : T => σ κ ω)]
      · rw [Set.indicator_of_mem]; rfl
      · intro g _ hg
        rw [Set.indicator_of_notMem]
        exact fun h => hg h.symm
      · intro h
        exact absurd (hV ω) h
    simp only [h1]
    rw [integral_finsetSum]
    · rw [← Finset.sum_coe_sort V]
      refine (Fintype.sum_equiv e _ _ fun l => ?_).symm
      rw [integral_indicator (hmeas' _), setIntegral_const, smul_eq_mul]
    · intro g _
      exact (integrable_const _).indicator (hmeas' g)
  refine ⟨V.card, fun l => μ.real {ω | (fun κ : T => σ κ ω) = (e l : T → Y)}, fun l => e l,
    fun l => measureReal_nonneg, ?_, hmean⟩
  have := hmean fun _ => 1
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at this
  exact this.symm

end Random

/-- **Paper: Proposition prop:random.** "Let w be a price on Y, let Q be a set disjoint from Y, and let σ be a random
map Y ∪ Q → Y that is the identity on Y, each σ(o) having finitely many values. Then a price on Y ∪ Q extends w and
satisfies |oo′| ≤ E |σ(o)σ(o′)| for all o, o′." -/
theorem prop_random {Y Q : Type} {w : Y → Y → ℝ} (hw : IsPrice K w) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : Q → Ω → Y) (hfin : ∀ κ, (Set.range (σ κ)).Finite)
    (hmeas : ∀ κ y, MeasurableSet (σ κ ⁻¹' {y})) :
    ∃ w' : Y ⊕ Q → Y ⊕ Q → ℝ, IsPrice K w' ∧ (∀ y y', w' (Sum.inl y) (Sum.inl y') = w y y') ∧
      ∀ o o', w' o o' ≤
        ∫ ω, w (Sum.elim id (fun κ => σ κ ω) o) (Sum.elim id (fun κ => σ κ ω) o') ∂μ := by
  classical
  -- the two properties: at least w on Y, and at most the expectation
  let A : Y ⊕ Q → Y ⊕ Q → ℝ := fun o o' => match o, o' with
    | Sum.inl y, Sum.inl y' => w y y'
    | _, _ => 0
  let E : Y ⊕ Q → Y ⊕ Q → ℝ := fun o o' =>
    ∫ ω, w (Sum.elim id (fun κ => σ κ ω) o) (Sum.elim id (fun κ => σ κ ω) o') ∂μ
  suffices hS : ∀ S : Finset (Y ⊕ Q), ∃ d : S → S → ℝ, IsPrice K d ∧ ∀ a b : S, A a b ≤ d a b ∧ d a b ≤ E a b by
    obtain ⟨w', hw', h⟩ := prop_random_compact A E hS
    refine ⟨w', hw', fun y y' => le_antisymm ?_ (h (Sum.inl y) (Sum.inl y')).1, fun o o' => (h o o').2⟩
    simpa [E] using (h (Sum.inl y) (Sum.inl y')).2
  intro S
  -- Q₀: the new points of S; Y₀: the old points of S and all values of σ on Q₀
  let T : Finset Q := S.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨m, θ, π, hθ, hθ1, hmean⟩ := prop_random_values μ σ hfin hmeas T
  let R : Finset Y := S.preimage Sum.inl Sum.inl_injective.injOn ∪
    Finset.univ.biUnion fun κ : T => Finset.univ.image fun l => π l κ
  have hR : ∀ l κ, π l κ ∈ R := fun l κ => Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨κ, Finset.mem_univ κ, Finset.mem_image_of_mem _ (Finset.mem_univ l)⟩)
  obtain ⟨v, hv, hv1, hv2⟩ := prop_random_limit (def_price_pullback hw (Subtype.val : R → Y)) θ hθ hθ1
    fun l κ => (⟨π l κ, hR l κ⟩ : R)
  -- the points of S among those of Y₀ ∪ Q₀, and their places under a map Q₀ → Y
  let g : S → R ⊕ T := fun a => match a with
    | ⟨Sum.inl y, hy⟩ => Sum.inl ⟨y, Finset.mem_union_left _ (Finset.mem_preimage.2 hy)⟩
    | ⟨Sum.inr κ, hκ⟩ => Sum.inr ⟨κ, Finset.mem_preimage.2 hκ⟩
  let place : (T → Y) → S → Y := fun f a => match a with
    | ⟨Sum.inl y, _⟩ => y
    | ⟨Sum.inr κ, hκ⟩ => f ⟨κ, Finset.mem_preimage.2 hκ⟩
  have hg : ∀ l (a : S), ((Sum.elim id (fun κ => (⟨π l κ, hR l κ⟩ : R)) (g a) : R) : Y) = place (π l) a := by
    rintro l ⟨y | κ, ha⟩ <;> rfl
  have hσ : ∀ ω (a : S), Sum.elim id (fun κ => σ κ ω) a.1 = place (fun κ : T => σ κ ω) a := by
    rintro ω ⟨y | κ, ha⟩ <;> rfl
  refine ⟨fun a b => v (g a) (g b), def_price_pullback hv g, fun a b => ⟨?_, ?_⟩⟩
  · obtain ⟨y | κ, ha⟩ := a <;> obtain ⟨y' | κ', hb⟩ := b
    · exact (hv1 ⟨y, _⟩ ⟨y', _⟩).ge
    all_goals exact hv.nonneg _ _
  · refine (hv2 (g a) (g b)).trans (le_of_eq ?_)
    show _ = ∫ ω, w (Sum.elim id (fun κ => σ κ ω) a.1) (Sum.elim id (fun κ => σ κ ω) b.1) ∂μ
    simp only [hg, hσ]
    exact (hmean fun f => w (place f a) (place f b)).symm

/-- Proposition prop:random for a random map with finitely many values σ_l, taken with probabilities θ_l. -/
theorem prop_random_finite {Y Q : Type} {w : Y → Y → ℝ} (hw : IsPrice K w) {Λ : Type} [Fintype Λ] (θ : Λ → ℝ)
    (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1) (σ : Λ → Q → Y) :
    ∃ w' : Y ⊕ Q → Y ⊕ Q → ℝ, IsPrice K w' ∧ (∀ y y', w' (Sum.inl y) (Sum.inl y') = w y y') ∧
      ∀ o o', w' o o' ≤ ∑ l, θ l * w (Sum.elim id (σ l) o) (Sum.elim id (σ l) o') := by
  classical
  let _ : MeasurableSpace Λ := ⊤
  have : MeasurableSingletonClass Λ := ⟨fun _ => trivial⟩
  let p : PMF Λ := PMF.ofFintype (fun l => ENNReal.ofReal (θ l))
    (by rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => hθ l, hθ1, ENNReal.ofReal_one])
  obtain ⟨w', h1, h2, h3⟩ := prop_random hw p.toMeasure (fun κ l => σ l κ) (fun κ => Set.toFinite _)
    fun κ y => trivial
  refine ⟨w', h1, h2, fun o o' => (h3 o o').trans (le_of_eq ?_)⟩
  rw [PMF.integral_eq_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hθ l), smul_eq_mul]

/-- **Paper: Lemma lem:hubs.** "Let I = I₁ ⊔ I₂, let a tensor t on I be a sum of r products of a tensor on I₁ and one
on I₂, and let n_p be its index sizes. For two further parties o₁, o₂ it is a restriction of
∏_{p ∈ I₁} ⟨n_p⟩_{p o₁} · ⟨r⟩_{o₁ o₂} · ∏_{p ∈ I₂} ⟨n_p⟩_{p o₂}, and this remains true when o₁, o₂ are identified with given
parties." In Lean the paper's I is A, its part I₁ is given by the predicate S, and α j, β j are the factors of the j-th
product, functions of the indices in I₁ and in I₂. The map π places the parties of A among those of a set I that also
contains o₁ and o₂, in any way; lem_hubs_further is the case of two further parties. -/
theorem lem_hubs {A : Type} [Fintype A] [DecidableEq A] (π : A → I) (t : Ten K A) (S : A → Prop) [DecidablePred S]
    {r : ℕ} (α β : Fin r → (∀ a, t.ι a) → K)
    (hα : ∀ j x x', (∀ a, S a → x a = x' a) → α j x = α j x')
    (hβ : ∀ j x x', (∀ a, ¬ S a → x a = x' a) → β j x = β j x')
    (hs : ∀ x, t.val x = ∑ j, α j x * β j x) (o₁ o₂ : I) :
    Restr (Ten.push π t)
      (Ten.prod (fun a => Ten.wire K (Fintype.card (t.ι a)) (π a) (if S a then o₁ else o₂)) * Ten.wire K r o₁ o₂) := by
  classical
  let Λ : Option A → Type := fun o => match o with
    | none => Fin r
    | some a => t.ι a
  let iΛ : ∀ o, Fintype (Λ o) := fun o => match o with
    | none => inferInstanceAs (Fintype (Fin r))
    | some a => t.fin a
  let ξ : A ⊕ Bool → I := Sum.elim π fun b => if b then o₁ else o₂
  let src : Option A → A ⊕ Bool := fun o => o.elim (Sum.inr true) Sum.inl
  let tgt : Option A → A ⊕ Bool := fun o => o.elim (Sum.inr false) fun a => Sum.inr (decide (S a))
  let tab : A ⊕ Bool → (∀ a, t.ι a) → (∀ o, Λ o) → K := fun v x l => match v with
    | Sum.inl a => if x a = l (some a) then 1 else 0
    | Sum.inr true => α (l none) fun a => l (some a)
    | Sum.inr false => β (l none) fun a => l (some a)
  have key := Restr.of_edges π ξ t Λ src tgt tab (by
    rintro (a | b) x x' l l' hx hl
    · have h1 := hx a rfl
      have h2 : l (some a) = l' (some a) := hl (some a) (Or.inl rfl)
      show (if x a = l (some a) then (1 : K) else 0) = if x' a = l' (some a) then 1 else 0
      rw [h1, h2]
    · cases b
      · have h1 : l none = l' none := hl none (Or.inr rfl)
        show β (l none) _ = β (l' none) _
        rw [h1]
        refine hβ _ _ _ fun a ha => hl (some a) (Or.inr ?_)
        show Sum.inr (decide (S a)) = _
        simp [ha]
      · have h1 : l none = l' none := hl none (Or.inl rfl)
        show α (l none) _ = α (l' none) _
        rw [h1]
        refine hα _ _ _ fun a ha => hl (some a) (Or.inr ?_)
        show Sum.inr (decide (S a)) = _
        simp [ha]) (by
    intro x
    have e1 : ∀ l : ∀ o, Λ o, ∏ v, tab v x l =
        (∏ a, if x a = l (some a) then (1 : K) else 0) *
          (α (l none) (fun a => l (some a)) * β (l none) fun a => l (some a)) := by
      intro l
      rw [Fintype.prod_sum_type]
      congr 1
      rw [Fintype.prod_bool]
    simp only [e1]
    rw [hs]
    symm
    refine (Fintype.sum_equiv (Equiv.piOptionEquivProd (β := Λ)) _
      (fun z : Λ none × (∀ a, Λ (some a)) => (∏ a, if x a = z.2 a then (1 : K) else 0) *
          (α z.1 z.2 * β z.1 z.2)) fun l => rfl).trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hy
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (if_neg fun hxy => ha hxy.symm), zero_mul]
    · simp)
  refine key.trans ((Equi.prod_reindex _ (Equiv.optionEquivSumPUnit A).symm).1.trans
    ((Equi.prod_sum _).1.trans (Restr.mul (Restr.prod fun a => ?_) ((Equi.prod_unique _).1.trans ?_))))
  · show Restr (Ten.wire K (Fintype.card (t.ι a)) (π a) (if decide (S a) then o₁ else o₂)) _
    simp only [decide_eq_true_eq]
    exact Restr.refl _
  · show Restr (Ten.wire K (Fintype.card (Fin r)) o₁ o₂) _
    rw [Fintype.card_fin]
    exact Restr.refl _

/-- Lemma lem:hubs as printed, "for two further parties o₁, o₂": the parties are I₁ ⊔ I₂ and the two hubs. -/
theorem lem_hubs_further {I₁ I₂ : Type} [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    (t : Ten K (I₁ ⊕ I₂)) {r : ℕ} (α : Fin r → (∀ p, t.ι (Sum.inl p)) → K) (β : Fin r → (∀ p, t.ι (Sum.inr p)) → K)
    (hs : ∀ x, t.val x = ∑ j, α j (fun p => x (Sum.inl p)) * β j fun p => x (Sum.inr p)) :
    Restr (Ten.push (Sum.inl : I₁ ⊕ I₂ → (I₁ ⊕ I₂) ⊕ Bool) t)
      (Ten.prod (fun p : I₁ => Ten.wire K (Fintype.card (t.ι (Sum.inl p))) (Sum.inl (Sum.inl p)) (Sum.inr true)) *
        Ten.wire K r (Sum.inr true) (Sum.inr false) *
        Ten.prod fun p : I₂ => Ten.wire K (Fintype.card (t.ι (Sum.inr p))) (Sum.inl (Sum.inr p)) (Sum.inr false)) := by
  have key := lem_hubs (Sum.inl : I₁ ⊕ I₂ → (I₁ ⊕ I₂) ⊕ Bool) t (fun a => a.isLeft = true)
    (fun j x => α j fun p => x (Sum.inl p)) (fun j x => β j fun p => x (Sum.inr p))
    (fun j x x' h => congrArg (α j) (funext fun p => h (Sum.inl p) rfl))
    (fun j x x' h => congrArg (β j) (funext fun p => h (Sum.inr p) (by simp))) hs (Sum.inr true) (Sum.inr false)
  refine key.trans ((Restr.mul (Equi.prod_sum _).1 (Restr.refl _)).trans ?_)
  exact ((Equi.mul_assoc _ _ _).trans (((Equi.refl _).mul (Equi.mul_comm _ _)).trans (Equi.mul_assoc _ _ _).symm)).1

end Paper
