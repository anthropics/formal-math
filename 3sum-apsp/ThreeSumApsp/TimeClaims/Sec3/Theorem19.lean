/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem19
public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic
public import ThreeSumApsp.Util.Asymptotics.LogU

/-!
# Theorem 19 from Theorem 17 and Corollaries 15 and 16

Theorem 17 reduces Exact Triangle to `4 n g` calls of Lop-AE-SparseTri plus some extra time.  The
proof of Theorem 19 puts in the cost of one call (Corollary 15 or Corollary 16) and the parameters
`D` and `g`, and adds up.  Both routes have the same three steps:

1. the parameters satisfy the hypotheses of Theorem 17 and of the corollary (`Theorem19.choice_*`);
2. one call, with the reading of its answers, costs `O(I)` (`call_cost_corollary_15` and
   `call_cost_corollary_16`);
3. the sum of all terms is `O(κ P)` (`Theorem19.total_*`, the calculation of the proof of
   Theorem 19).

`time_le_of_calls` puts the three steps together.  The result keeps the dependence on `κ`
(`Claim.Theorem_19_explicit`).  From it follow the two bounds as printed, for every constant `κ`
(`Claim.Theorem_19_explicit.eventually_le`), and a bound for all sizes and all bounds on the
weights, which is what Theorem 21 is applied to (`exactTriangleUniform_of_explicit`): small sizes by
brute force (`dominated_bruteForce`), large sizes by the explicit bound with
`κ = max 1 (log u / log s)` (`dominated_explicit`).
-/

@[expose] public section

namespace ThreeSumApsp

/-- **How both routes of Theorem 19 end.**  Theorem 17 bounds the time by
`calls · call + C · extra`.  If one call costs at most `c I`, and if the calculation of the proof of
Theorem 19 bounds `calls · c I + C · extra` by `B`, then the time is at most `B`. -/
theorem time_le_of_calls {T calls call I extra B C c : ℝ}
    (h17 : T ≤ calls * call + C * extra) (hcall : call ≤ c * I)
    (hsum : calls * (c * I) + C * extra ≤ B) (hcalls : 0 ≤ calls) : T ≤ B :=
  (h17.trans (add_le_add (mul_le_mul_of_nonneg_left hcall hcalls) le_rfl)).trans hsum

/-- One call on the route through Corollary 16, with the reading of its answers, costs
`O(n²/D^{0.063})`: an instance has `|W| ≤ n²/√D` query pairs, so `|W| D^{0.437} ≤ n²/D^{0.063}`. -/
theorem call_cost_corollary_16 {n D : ℕ} {t C C₁₆ : ℝ} (hD : 1 ≤ D) (hC : 0 ≤ C) (hC₁₆ : 0 ≤ C₁₆)
    (ht : t ≤ C₁₆ * wantedBound n D (queryCap n D)) :
    t + C * ((n : ℝ) ^ 2 / Real.sqrt D)
      ≤ (2 * C₁₆ + C) * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hpos₁ : 0 < (D : ℝ) ^ (0.437 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hpos₂ : 0 < (D : ℝ) ^ (0.063 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hsqrt : Real.sqrt D = (D : ℝ) ^ (0.437 : ℝ) * (D : ℝ) ^ (0.063 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hD0]
    norm_num
  have hquery : (queryCap n D : ℝ) * (D : ℝ) ^ (0.437 : ℝ)
      ≤ (n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ) :=
    calc (queryCap n D : ℝ) * (D : ℝ) ^ (0.437 : ℝ)
        ≤ (n : ℝ) ^ 2 / Real.sqrt D * (D : ℝ) ^ (0.437 : ℝ) :=
          mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hpos₁.le
      _ = (n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ) := by
          rw [hsqrt]
          field_simp
  have hread := sq_div_sqrt_le_sq_div_rpow n hD (a := 0.063) (by norm_num)
  calc t + C * ((n : ℝ) ^ 2 / Real.sqrt D)
      ≤ C₁₆ * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ) + (n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ))
          + C * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)) :=
        add_le_add (ht.trans (mul_le_mul_of_nonneg_left (add_le_add hquery le_rfl) hC₁₆))
          (mul_le_mul_of_nonneg_left hread hC)
    _ = (2 * C₁₆ + C) * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)) := by ring

/-- One call on the route through Corollary 15, with the reading of its answers, costs
`O(n² log² D / D^{1/18})`. -/
theorem call_cost_corollary_15 {n D : ℕ} {t C C₁₅ : ℝ} (hD : 4 ≤ D) (hC : 0 ≤ C)
    (ht : t ≤ C₁₅ * thinBound n D) :
    t + C * ((n : ℝ) ^ 2 / Real.sqrt D) ≤ (C₁₅ + C) * thinBound n D :=
  calc t + C * ((n : ℝ) ^ 2 / Real.sqrt D) ≤ C₁₅ * thinBound n D + C * thinBound n D :=
        add_le_add ht (mul_le_mul_of_nonneg_left (sq_div_sqrt_le_thinBound n hD) hC)
    _ = _ := by ring

/-- The deduction "By Theorem 5" in the proof of Theorem 19: from Theorem 17 (with
Strassen's algorithm) and the first case of Corollary 15, with `D` the largest power of four at most
`n^{1/18}` and `g = ⌈D^{1/36}⌉`. -/
theorem Theorem19.explicit_of_theorem_17_corollary_15 (M : DetTimeModel)
    (h17 : Claim.Theorem_17 M strassen paramD₅ paramG₅)
    (h15 : Claim.Corollary_15_first M) : Claim.Theorem_19_explicit M (1 / 648) 2 := by
  obtain ⟨C, hC, h17⟩ := h17
  obtain ⟨C₁₅, _, Td, hC₁₅, -, hTd, h15⟩ := h15
  obtain ⟨T, hT, h17⟩ := h17 Td hTd
  obtain ⟨C₀, -, htotal⟩ := Theorem19.total_theorem_5
  refine ⟨C₀ * (C₁₅ + C + C), T, hT, fun n κ u hn hκ hu => ?_⟩
  -- Step 1: the parameters.
  have P := Theorem19.choice_theorem_5 hn
  have hD16 := P.sixteen_le
  have h17 := h17 n κ u hD16 P.le_n P.one_le_ceil P.ceil_le_sqrt hκ hu
  -- Step 2: one call.
  have hcall := call_cost_corollary_15 (by omega) hC
    (h15 n (paramD₅ n) (queryCap n (paramD₅ n)) ⟨_, rfl⟩ (by omega) P.pow_eighteen_le
      (Nat.floor_le (by positivity))).2
  -- Step 3: the sum of the proof of Theorem 19.
  have hsum := htotal hn (a := C₁₅ + C) (b := C) (by positivity) hC hκ
  exact (time_le_of_calls h17 hcall hsum (by positivity)).trans_eq (by ring)

/-- The deduction "By Corollary 26" in the proof of Theorem 19: from Theorem 17 (with
Strassen's algorithm) and Corollary 16, with `D = ⌊n^{1/18}⌋` and `g = ⌈D^{0.0315}⌉`. -/
theorem Theorem19.explicit_of_theorem_17_corollary_16 (M : DetTimeModel)
    (h17 : Claim.Theorem_17 M strassen paramD₂₆ paramG₂₆)
    (h16 : Claim.Corollary_16 M) : Claim.Theorem_19_explicit M 0.00175 1 := by
  obtain ⟨C, hC, h17⟩ := h17
  obtain ⟨C₁₆, _, Td, hC₁₆, -, hTd, h16⟩ := h16
  obtain ⟨T, hT, h17⟩ := h17 Td hTd
  obtain ⟨C₀, -, htotal⟩ := Theorem19.total_corollary_26
  refine ⟨C₀ * (2 * C₁₆ + C + C), T, hT, fun n κ u hn hκ hu => ?_⟩
  -- Step 1: the parameters.
  have P := Theorem19.choice_corollary_26 hn
  have hD16 := P.sixteen_le
  have h17 := h17 n κ u hD16 P.le_n P.one_le_ceil P.ceil_le_sqrt hκ hu
  -- Step 2: one call.
  have hcall := call_cost_corollary_16 (by omega) hC hC₁₆
    (h16 n _ (queryCap n (paramD₂₆ n)) (by omega) P.pow_eighteen_le).2
  -- Step 3: the sum of the proof of Theorem 19.
  have hsum := htotal hn (a := 2 * C₁₆ + C) (b := C) (by positivity) hC hκ
  rw [pow_one]
  exact (time_le_of_calls h17 hcall hsum (by positivity)).trans_eq (by ring)

/-! ## The bounds as printed -/

/-- The explicit form along `u = n^κ`: for every `κ` and all large `n` the time is at most
`K max(κ, 1) n^{3-δ} (log n)^e`. -/
theorem Claim.Theorem_19_explicit.eventually_le {M : DetTimeModel} {δ : ℝ} {e : ℕ}
    (h : Claim.Theorem_19_explicit M δ e) :
    ∃ (K : ℝ) (T : ℕ → ℝ → ℝ), M.exactTriangle T ∧ ∀ κ : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      T n ((n : ℝ) ^ κ) ≤ K * max κ 1 * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e) := by
  obtain ⟨K, T, hT, hb⟩ := h
  refine ⟨K, T, hT, fun κ => ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (16 ^ 18)] with n hn
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 (le_trans (by norm_num) hn)
  exact (hb n (max κ 1) _ hn (le_max_right _ _)
    (Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _))).trans_eq (mul_assoc _ _ _).symm

/-- The first bound of Theorem 19 in the printed form, for every constant `κ ≥ 1`, from
the explicit form. -/
theorem Theorem19.first_of_explicit (M : DetTimeModel)
    (h : Claim.Theorem_19_explicit M (1 / 648) 2) : Claim.Theorem_19_first M := by
  obtain ⟨K, T, hT, hb⟩ := h.eventually_le
  exact fun κ _ => ⟨_, T, hT, hb κ⟩

/-- The second bound of Theorem 19 in the printed form, with
"O(n^{3-ε'} log n) ≤ O(n^{3-ε_T})", from the explicit form. -/
theorem Theorem19.second_of_explicit (M : DetTimeModel)
    (h : Claim.Theorem_19_explicit M 0.00175 1) : Claim.Theorem_19_second M := by
  obtain ⟨K, T, hT, hb⟩ := h.eventually_le
  exact fun κ _ => ⟨_, T, hT, by simpa only [pow_one] using hb κ,
    UpperPowPolylog.upperBigOPow ⟨_, _, hb κ⟩ (by norm_num)⟩

/-- The first deterministic line of Theorem 2, "Exact Triangle on n-vertex graphs in
O(n^{2.9983}) time", for the tripartite form of the problem, from the explicit form of Theorem 19
(`3 - ε_T = 2.9983`). -/
theorem exactTriangleIn_of_explicit (M : DetTimeModel)
    (h : Claim.Theorem_19_explicit M 0.00175 1) : Claim.ExactTriangleIn M 2.9983 := by
  obtain ⟨K, T, hT, hb⟩ := h.eventually_le
  exact fun κ _ => ⟨T, hT, UpperPowPolylog.upperBigOPow ⟨_, _, hb κ⟩ (by norm_num)⟩

/-! ## A bound for all sizes and all bounds on the weights -/

/-- The number `s` of vertices per part and the bound `u` on the weights. -/
structure SizeBound where
  /-- The number of vertices per part. -/
  s : ℕ
  /-- The bound on the absolute values of the weights. -/
  u : ℝ

/-- The time `uniformTime` without its constant: `s^{3-δ} (log s + 1)^e (1 + log u)²`. -/
private noncomputable abbrev uniformShape (δ : ℝ) (e : ℕ) (p : SizeBound) : ℝ :=
  (p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e * (1 + logU p.u) ^ 2

/-- Each of the three factors of `uniformShape` is at least 1. -/
private theorem one_le_uniformShape {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1) {p : SizeBound} (hs : 1 ≤ p.s) :
    1 ≤ uniformShape δ e p :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (Nat.one_le_cast.2 hs) (by linarith)) (one_le_log_add_one_pow p.s e))
    (one_le_pow₀ (one_le_one_add_logU p.u))

/-- "Smaller instances are solved by brute force": below a fixed size `n₀`, the time
`s³ (1 + log u)` is `O(s^{3-δ} (log s + 1)^e (1 + log u)²)`, because `s^δ ≤ n₀^δ`. -/
private theorem dominated_bruteForce {δ : ℝ} (e n₀ : ℕ) (hδ0 : 0 ≤ δ) :
    Dominated (fun p : SizeBound => (1 ≤ p.s ∧ 1 ≤ p.u) ∧ p.s < n₀)
      (fun p => (p.s : ℝ) ^ 3 * (1 + logU p.u)) (uniformShape δ e) := by
  refine .of_le_const_mul (C := (n₀ : ℝ) ^ δ) (by positivity) fun p hp => ?_
  have hlog := one_le_log_add_one_pow p.s e
  have hwords := one_le_one_add_logU p.u
  have hs0 : (0 : ℝ) < p.s := Nat.cast_pos.2 hp.1.1
  have hsplit : (p.s : ℝ) ^ 3 = (p.s : ℝ) ^ δ * (p.s : ℝ) ^ (3 - δ) := by
    rw [← Real.rpow_add hs0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hsmall : (p.s : ℝ) ^ δ ≤ (n₀ : ℝ) ^ δ :=
    Real.rpow_le_rpow hs0.le (Nat.cast_le.2 hp.2.le) hδ0
  calc (p.s : ℝ) ^ 3 * (1 + logU p.u)
      = (p.s : ℝ) ^ δ * ((p.s : ℝ) ^ (3 - δ) * 1 * (1 + logU p.u) ^ 1) := by rw [hsplit]; ring
    _ ≤ (n₀ : ℝ) ^ δ * ((p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e * (1 + logU p.u) ^ 2) := by
        gcongr
        norm_num

/-- Weights up to `u` are weights up to `s^κ` for `κ = max 1 (log u / log s)`. -/
private theorem le_rpow_max_log_div {s : ℕ} {u : ℝ} (hs : 3 ≤ s) (hu : 1 ≤ u) :
    u ≤ (s : ℝ) ^ max 1 (Real.log u / Real.log s) := by
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.2 (by omega)
  have hlogs : 1 ≤ Real.log s := Real.one_le_log_natCast_of_three_le hs
  calc u = (s : ℝ) ^ (Real.log u / Real.log s) := by
        rw [Real.rpow_def_of_pos hs0, mul_div_cancel₀ _ (by linarith),
          Real.exp_log (zero_lt_one.trans_le hu)]
    _ ≤ (s : ℝ) ^ max 1 (Real.log u / Real.log s) :=
        Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 (by omega)) (le_max_right _ _)

/-- The exponent `max 1 (log u / log s)` is at most `1 + log u`. -/
private theorem max_log_div_le {s : ℕ} {u : ℝ} (hs : 3 ≤ s) (hu : 1 ≤ u) :
    max 1 (Real.log u / Real.log s) ≤ 1 + logU u := by
  refine max_le (one_le_one_add_logU u) ?_
  linarith [div_le_self (Real.log_nonneg hu) (Real.one_le_log_natCast_of_three_le hs),
    log_le_logU (zero_lt_one.trans_le hu)]

/-- From the size `16^18` on: the explicit bound of Theorem 19 with `κ = max 1 (log u / log s)`. -/
private theorem dominated_explicit {T : ℕ → ℝ → ℝ} {K δ : ℝ} {e : ℕ}
    (hb : ∀ (n : ℕ) (κ u : ℝ), 16 ^ 18 ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))) :
    Dominated (fun p : SizeBound => (1 ≤ p.s ∧ 1 ≤ p.u) ∧ ¬ p.s < 16 ^ 18) (fun p => T p.s p.u)
      (uniformShape δ e) := by
  have h3 : ∀ p : SizeBound, ¬ p.s < 16 ^ 18 → 3 ≤ p.s := fun p hp =>
    (by norm_num : 3 ≤ 16 ^ 18).trans (not_lt.1 hp)
  refine (Dominated.of_exists_const (g := fun p => max 1 (Real.log p.u / Real.log p.s) *
    ((p.s : ℝ) ^ (3 - δ) * Real.log p.s ^ e)) ⟨K, fun p hp => ?_⟩ fun p _ => ?_).trans
    (.of_le fun p hp => ?_)
  · exact hb p.s _ p.u (not_lt.1 hp.2) (le_max_left _ _) (le_rpow_max_log_div (h3 p hp.2) hp.1.2)
  · positivity
  · have hκ := max_log_div_le (h3 p hp.2) hp.1.2
    have hlog := Real.log_natCast_nonneg p.s
    have hwords := le_self_pow₀ (one_le_one_add_logU p.u) two_ne_zero
    calc max 1 (Real.log p.u / Real.log p.s) * ((p.s : ℝ) ^ (3 - δ) * Real.log p.s ^ e)
        ≤ (1 + logU p.u) ^ 2 * ((p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e) := by
          gcongr
          · exact hκ.trans hwords
          · linarith
      _ = uniformShape δ e p := by ring

/-- From the explicit form of Theorem 19, brute force for small instances
("smaller instances are solved by brute force") and two closure properties: Exact Triangle in time
`K s^{3-δ} (log s + 1)^e (1 + log u)²` for all `s` and `u`.

NOTE.  This step is not in the paper; see `Claim.ExactTriangleUniform` for why our rendering of
"Plug Theorem 19 into Theorem 21" needs it. -/
theorem exactTriangleUniform_of_explicit (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hex : Claim.Theorem_19_explicit M δ e) (hbf : Claim.BruteForce M)
    (hch : Closure.ChooseBySize M) (hmono : Closure.MonoExactTriangle M) :
    Claim.ExactTriangleUniform M δ e := by
  obtain ⟨K, T, hT, hb⟩ := hex
  obtain ⟨C, hbf⟩ := hbf
  obtain ⟨C₀, hch⟩ := hch (16 ^ 18)
  have hshape : ∀ p : SizeBound, 1 ≤ p.s ∧ 1 ≤ p.u → 1 ≤ uniformShape δ e p := fun p hp =>
    one_le_uniformShape e hδ1 hp.1
  have hsmall := (dominated_bruteForce e (16 ^ 18) hδ0).const_mul_of_nonneg C fun p _ =>
    mul_nonneg (by positivity) (zero_le_one.trans (one_le_one_add_logU p.u))
  obtain ⟨K', hK'0, hK'⟩ := (Dominated.ite hsmall (dominated_explicit hb) fun p hp =>
    zero_le_one.trans (hshape p hp)).add (.const C₀ hshape)
  refine ⟨1 + K', le_add_of_nonneg_right hK'0,
    hmono _ _ (fun s u hs hu => ?_) (hch _ T hbf hT)⟩
  exact (hK' ⟨s, u⟩ ⟨hs, hu⟩).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
    (zero_le_one.trans (hshape ⟨s, u⟩ ⟨hs, hu⟩)))

end ThreeSumApsp
