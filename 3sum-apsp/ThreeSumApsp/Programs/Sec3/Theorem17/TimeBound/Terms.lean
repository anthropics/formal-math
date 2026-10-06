/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Claim
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.ChoosePrime
public import ThreeSumApsp.Programs.Sec3.Theorem17.Instances.Chunks
public import ThreeSumApsp.Programs.Sec3.Theorem17.Instances.WriteMatrices
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes
public import ThreeSumApsp.Util.Asymptotics.Scale

/-!
# Theorem 17: the time of each routine, up to a constant

The running time of the reduction of Theorem 17 is a sum of the time functions of its routines.  The
theorem bounds the additional time by "O(ν n³ log n/g + n^{ω+o(1)} D^{3/2} + n² D g)", where ν is
the exponent in `|w(e)| ≤ n^ν`; it is `κ` below.  The form for programs, `Claim.Theorem_17`, has,
here, Strassen's exponent `log₂ 7` in the second term.  This file bounds each
routine by a monomial in `n`, `√D` and `κ log n`, uniformly in `n`, `D`, `g`, `U` and `κ` under the
hypotheses of the theorem, and says which monomials are within which of the three terms.  No
constant is computed.

* `Steps t B` says that the number `t` of steps is `O(B)`, uniformly in the parameters.  Such bounds
  can be added and multiplied, and they absorb constant factors.
* Every time function is a polynomial in a few quantities, and each of these is at most a monomial
  `mon a b c = n^a (√D)^b (κ log n)^c`: `⌊√D⌋`, `g` and the size `⌈s/g⌉` of a piece are at most
  `√D`; `2^⌈log₂ n⌉ ≤ 2n`; the number of binary digits of `U ≤ n^κ` is `O(κ log n)` (section "The
  basic quantities").  So a routine takes `O(mon a b c)` steps (`StepsMon t a b c`), and the
  exponents are read off its time function, in the calculus `Scale.SoftO` on the scale `costScale`.
* All three bases are at least 1.  So a monomial is within the first term if its exponents are at
  most `(2, 1, 1)`, within the second if they are at most `(2, 3, 0)`, within the third if they are
  at most `(2, 2, 0)` (`Scale.SoftO.withinScans`, `Scale.SoftO.withinPrime`,
  `Scale.SoftO.withinBuild`).
* The choice of the prime runs through at most `√D` primes (`steps_chooseTime`).  The product of the
  two matrices is within the second term, as in the paper: Strassen's recursion makes
  `7^⌈log₂ n⌉ = O(n^{log₂ 7})` products of polynomials of degree below `p ≤ √D`
  (`steps_sqrt_mul_strSteps`).  The residues of the weights, computed bit by bit for each prime,
  take `O(√D n² κ log n)` steps, which is within the first term.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The hypotheses -/

/-- The parameters of Theorem 17 as one record, so that a bound up to a constant can be stated
uniformly in all of them. -/
structure CostParams where
  /-- The number of vertices per part. -/
  n : ℕ
  /-- The parameter `D` of the reduction. -/
  D : ℕ
  /-- The parameter `g` of the reduction. -/
  g : ℕ
  /-- The bound on the absolute values of the weights. -/
  U : ℕ
  /-- The exponent in `U ≤ n^κ`. -/
  κ : ℝ

/-- The hypotheses of Theorem 17, with the bound `U` on the weights.  The claim for
programs adds `κ ≥ 1`, as in Theorem 19. -/
structure CostParams.Hyp (θ : CostParams) : Prop where
  /-- `D ≥ 16`. -/
  hD16 : 16 ≤ θ.D
  /-- `D ≤ n`. -/
  hDn : θ.D ≤ θ.n
  /-- `g ≥ 1`. -/
  hg : 1 ≤ θ.g
  /-- `g ≤ √D`. -/
  hgD : (θ.g : ℝ) ≤ Real.sqrt θ.D
  /-- `κ ≥ 1`. -/
  hκ : 1 ≤ θ.κ
  /-- The weights are at most `n^κ` in absolute value. -/
  hUn : (θ.U : ℝ) ≤ (θ.n : ℝ) ^ θ.κ

namespace CostParams.Hyp

variable {θ : CostParams} (h : θ.Hyp)
include h

/-- `D ≥ 1`, as a natural number. -/
theorem one_le_D_nat : 1 ≤ θ.D := (by norm_num : 1 ≤ 16).trans h.hD16

/-- `n ≥ 16`. -/
theorem sixteen_le_n : 16 ≤ θ.n := h.hD16.trans h.hDn

/-- `n ≥ 1`, as a natural number. -/
theorem one_le_n_nat : 1 ≤ θ.n := (by norm_num : 1 ≤ 16).trans h.sixteen_le_n

/-- `n ≥ 1`. -/
theorem one_le_n : (1 : ℝ) ≤ θ.n := Nat.one_le_cast.2 h.one_le_n_nat

/-- `g ≥ 1`. -/
theorem one_le_g : (1 : ℝ) ≤ θ.g := Nat.one_le_cast.2 h.hg

/-- `g > 0`. -/
theorem g_pos : (0 : ℝ) < θ.g := zero_lt_one.trans_le h.one_le_g

/-- `√D ≥ g ≥ 1`. -/
theorem one_le_sqrt : 1 ≤ Real.sqrt θ.D := h.one_le_g.trans h.hgD

/-- `√D > 0`. -/
theorem sqrt_pos : 0 < Real.sqrt θ.D := zero_lt_one.trans_le h.one_le_sqrt

/-- `log n ≥ 1`, because `n ≥ 16`. -/
theorem one_le_log : 1 ≤ Real.log θ.n :=
  Real.one_le_log_natCast_of_three_le ((by norm_num : 3 ≤ 16).trans h.sixteen_le_n)

/-- `κ log n ≥ 1`. -/
theorem one_le_κ_mul_log : 1 ≤ θ.κ * Real.log θ.n :=
  one_le_mul_of_one_le_of_one_le h.hκ h.one_le_log

/-- `√D g ≤ D ≤ n`. -/
theorem sqrt_mul_g_le : Real.sqrt θ.D * θ.g ≤ θ.n :=
  calc Real.sqrt θ.D * θ.g ≤ Real.sqrt θ.D * Real.sqrt θ.D := by
        gcongr
        exact h.hgD
    _ = θ.D := Real.mul_self_sqrt θ.D.cast_nonneg
    _ ≤ θ.n := Nat.cast_le.2 h.hDn

/-- `√D ≤ n`. -/
theorem sqrt_le_n : Real.sqrt θ.D ≤ θ.n :=
  (le_mul_of_one_le_right (Real.sqrt_nonneg _) h.one_le_g).trans h.sqrt_mul_g_le

end CostParams.Hyp

/-! ## Numbers of steps up to a constant -/

/-- The number `t` of steps is `O(B)`, uniformly in the parameters, under the hypotheses of
Theorem 17. -/
def Steps (t : CostParams → ℕ) (B : CostParams → ℝ) : Prop :=
  Dominated CostParams.Hyp (fun θ => (t θ : ℝ)) B

namespace Steps

variable {t t₁ t₂ : CostParams → ℕ} {B B₁ B₂ : CostParams → ℝ}

/-- A smaller number of steps. -/
theorem mono_left (h : Steps t₂ B) (hle : ∀ θ, θ.Hyp → t₁ θ ≤ t₂ θ) : Steps t₁ B :=
  Dominated.mono_left h fun θ hθ => Nat.cast_le.2 (hle θ hθ)

/-- A larger bound. -/
theorem mono_right (h : Steps t B₁) (hle : ∀ θ, θ.Hyp → B₁ θ ≤ B₂ θ) : Steps t B₂ :=
  Dominated.mono_right h hle

/-- `O(B) + O(B) = O(B)`. -/
protected theorem add (h₁ : Steps t₁ B) (h₂ : Steps t₂ B) : Steps (fun θ => t₁ θ + t₂ θ) B := by
  simpa only [Steps, Nat.cast_add] using Dominated.add h₁ h₂

/-- `O(B₁) · O(B₂) = O(B₁ B₂)`. -/
protected theorem mul (h₁ : Steps t₁ B₁) (h₂ : Steps t₂ B₂) :
    Steps (fun θ => t₁ θ * t₂ θ) fun θ => B₁ θ * B₂ θ := by
  simpa only [Steps, Nat.cast_mul] using
    Dominated.mul h₁ h₂ (fun _ _ => Nat.cast_nonneg _) fun _ _ => Nat.cast_nonneg _

/-- A constant factor is absorbed. -/
theorem const_mul {c : ℕ} (h : Steps t B) : Steps (fun θ => c * t θ) B := by
  simpa only [Steps, Nat.cast_mul] using Dominated.const_mul h c.cast_nonneg

/-- A constant number of steps is `O(B)` if `B ≥ 1`. -/
protected theorem const {c : ℕ} (hB : ∀ θ, θ.Hyp → 1 ≤ B θ) : Steps (fun _ => c) B :=
  Dominated.const _ hB

end Steps

/-! ## Monomials -/

/-- The scale of Theorem 17: monomials in `n`, `√D` and `κ log n`, under the hypotheses of the
theorem. -/
noncomputable def costScale : Scale CostParams (Fin 3) :=
  .ofBases CostParams.Hyp ![fun θ => θ.n, fun θ => Real.sqrt θ.D, fun θ => θ.κ * Real.log θ.n]
    fun i θ h => by
      fin_cases i
      exacts [h.one_le_n, h.one_le_sqrt, h.one_le_κ_mul_log]

/-- The monomial `n^a (√D)^b (κ log n)^c`. -/
noncomputable abbrev mon (a b c : ℕ) : CostParams → ℝ := costScale.mon ![a, b, c]

theorem mon_eq (a b c : ℕ) (θ : CostParams) :
    mon a b c θ = (θ.n : ℝ) ^ a * Real.sqrt θ.D ^ b * (θ.κ * Real.log θ.n) ^ c := by
  simp [Scale.mon, costScale, Scale.ofBases, Fin.prod_univ_three]

/-- The number `t` of steps is `O(n^a (√D)^b (κ log n)^c)`. -/
abbrev StepsMon (t : CostParams → ℕ) (a b c : ℕ) : Prop := costScale.SoftO t ![a, b, c]

/-- A bound by a monomial, as a bound up to a constant. -/
theorem steps_of_softO {t : CostParams → ℕ} {e : Fin 3 → ℕ} (h : costScale.SoftO t e) :
    Steps t (costScale.mon e) :=
  h.dominated fun _ _ => rfl

/-! ## The basic quantities -/

/-- The number of vertices per part. -/
theorem steps_n : StepsMon (fun θ => θ.n) 1 0 0 :=
  (Scale.SoftO.of_le_base 0 fun _ _ => le_rfl).mono (by decide)

/-- `s = ⌊√D⌋ ≤ √D`. -/
theorem steps_sqrt : StepsMon (fun θ => Nat.sqrt θ.D) 0 1 0 :=
  (Scale.SoftO.of_le_base 1 fun _ _ => Real.nat_sqrt_le_real_sqrt).mono (by decide)

/-- `D = (√D)²`. -/
theorem steps_D : StepsMon (fun θ => θ.D) 0 2 0 :=
  .of_dominated <| .of_le fun θ _ => by
    simp only [mon_eq, pow_zero, mul_one, one_mul, Real.sq_sqrt θ.D.cast_nonneg, le_refl]

/-- `g ≤ √D`. -/
private theorem steps_g : StepsMon (fun θ => θ.g) 0 1 0 :=
  (Scale.SoftO.of_le_base (s := costScale) 1 fun _ hθ => hθ.hgD).mono (by decide)

/-- `2^⌈log₂ n⌉ ≤ 2n`. -/
private theorem steps_two_pow_clog : StepsMon (fun θ => 2 ^ Nat.clog 2 θ.n) 1 0 0 :=
  (by growth [steps_n] : StepsMon (fun θ => 2 * θ.n) 1 0 0).of_le fun _ hθ =>
    Nat.pow_clog_le_mul one_lt_two hθ.one_le_n_nat

/-- `⌈log₂ n⌉ ≤ 2^⌈log₂ n⌉`. -/
private theorem steps_clog : StepsMon (fun θ => Nat.clog 2 θ.n) 1 0 0 :=
  steps_two_pow_clog.of_le fun _ _ => Nat.lt_two_pow_self.le

/-- The number of binary digits of `U ≤ n^κ` is `O(κ log n)`: `2^{len - 1} ≤ U` gives
`(len - 1) log 2 ≤ κ log n`. -/
private theorem steps_bitLen : StepsMon (fun θ => bitLen θ.U) 0 0 1 := by
  refine .of_dominated (Dominated.of_le_const_mul (C := 3) (by norm_num) fun θ hθ => ?_)
  simp only [mon_eq, pow_zero, one_mul, pow_one]
  have hΛ : 1 ≤ θ.κ * Real.log θ.n := hθ.one_le_κ_mul_log
  rcases Nat.eq_zero_or_pos θ.U with hU | hU
  · rw [hU, bitLen, Nat.size_zero, Nat.cast_zero]
    linarith [hΛ]
  · have hlen : 1 ≤ bitLen θ.U := Nat.size_pos.2 hU
    have hpow : 2 ^ (bitLen θ.U - 1) ≤ θ.U := Nat.lt_size.1 (Nat.sub_lt hlen one_pos)
    have hlog := Real.log_le_log (by positivity)
      (le_trans (by exact_mod_cast hpow : (2 : ℝ) ^ (bitLen θ.U - 1) ≤ θ.U) hθ.hUn)
    rw [Real.log_pow, Real.log_rpow (zero_lt_one.trans_le hθ.one_le_n), Nat.cast_sub hlen,
      Nat.cast_one] at hlog
    have hhalf := mul_le_mul_of_nonneg_left Real.one_half_lt_log_two.le
      (sub_nonneg.2 (Nat.one_le_cast.2 hlen : (1 : ℝ) ≤ bitLen θ.U))
    -- `(len - 1)/2 ≤ (len - 1) log 2 ≤ κ log n` and `1 ≤ κ log n`.
    linarith [hlog, hhalf, hΛ]

/-- A piece has `⌈s/g⌉ ≤ s` vertices. -/
private theorem steps_pieceSizeNat : StepsMon (fun θ => pieceSizeNat θ.D θ.g) 0 1 0 :=
  steps_sqrt.of_le fun _ hθ => (Nat.ceilDiv_le_iff hθ.hg).2 (Nat.le_mul_of_pos_right _ hθ.hg)

/-- `⌊n²/√D⌋ ≤ n²/√D`. -/
theorem cast_queryCapNat_le {θ : CostParams} (hθ : θ.Hyp) :
    (queryCapNat θ.n θ.D : ℝ) ≤ (θ.n : ℝ) ^ 2 / Real.sqrt θ.D := by
  rw [queryCapNat_eq θ.n hθ.one_le_D_nat]
  exact Nat.floor_le (by positivity)

/-- `⌊n²/√D⌋ ≤ n²`. -/
private theorem steps_queryCapNat : StepsMon (fun θ => queryCapNat θ.n θ.D) 2 0 0 :=
  .of_dominated <| .of_le fun θ hθ => (cast_queryCapNat_le hθ).trans (by
    simpa only [mon_eq, pow_zero, mul_one] using div_le_self (by positivity) hθ.one_le_sqrt)

/-! ## The routines -/

/-- The number of binary digits of `U`. -/
theorem steps_tBitLen : StepsMon (fun θ => tBitLen θ.U) 0 0 1 := by
  unfold tBitLen
  growth [steps_bitLen]

/-- The table of the doubles of the prime. -/
theorem steps_tDblTable : StepsMon (fun θ => tDblTable (bitLen θ.U)) 0 0 1 := by
  unfold tDblTable
  growth [steps_bitLen]

/-- The residues of the `n²` weights of one kind: `O(log U)` steps for each. -/
theorem steps_tResidues : StepsMon (fun θ => tResidues (θ.n * θ.n) (bitLen θ.U)) 2 0 1 := by
  unfold tResidues tResid
  growth [steps_n, steps_bitLen]

/-- Sorting the pairs into classes. -/
theorem steps_tClasses : StepsMon (fun θ => tClasses θ.n (Nat.sqrt θ.D)) 2 1 0 := by
  unfold tClasses
  growth [steps_n, steps_sqrt]

/-- Cutting the classes into chunks. -/
theorem steps_tChunks : StepsMon (fun θ => tChunks (Nat.sqrt θ.D) (4 * θ.n * θ.g)) 1 1 0 := by
  unfold tChunks
  growth [steps_n, steps_sqrt, steps_g]

/-- The list of the primes in `[√D/2, √D)`. -/
private theorem steps_tPrimes : StepsMon (fun θ => tPrimes θ.D) 0 3 0 := by
  unfold tPrimes
  growth [steps_sqrt]

/-- Writing the matrix `X` of an instance takes `O(nD)` steps. -/
theorem steps_tWriteX : StepsMon (fun θ => tWriteX θ.n θ.D (pieceSizeNat θ.D θ.g)) 1 2 0 := by
  unfold tWriteX
  growth [steps_n, steps_D, steps_pieceSizeNat]

/-- Writing the matrix `Y` of an instance takes `O(nD)` steps. -/
theorem steps_tWriteY : StepsMon (fun θ => tWriteY θ.n θ.D (pieceSizeNat θ.D θ.g)) 1 2 0 := by
  unfold tWriteY
  growth [steps_n, steps_D, steps_pieceSizeNat]

/-- The table of the sizes of the blocks. -/
private theorem steps_tSzTable : StepsMon (fun θ => tSzTable (Nat.clog 2 θ.n)) 1 0 0 := by
  unfold tSzTable
  growth [steps_clog]

/-- One of the matrices `P`, `Q` over `ℤ[x]/(x^p - 1)` in Z-order: `O(n² √D)`. -/
private theorem steps_buildZTime :
    StepsMon (fun θ => buildZTime θ.n (2 ^ Nat.clog 2 θ.n) (Nat.sqrt θ.D)) 2 1 0 := by
  unfold buildZTime
  growth [steps_n, steps_sqrt, steps_two_pow_clog]

/-- Reading the count off the product. -/
private theorem steps_countZeroTime : StepsMon (fun θ => countZeroTime θ.n) 2 0 0 := by
  unfold countZeroTime
  growth [steps_n]

/-- `⌊n²/√D⌋`, by counting up. -/
theorem steps_tQueryCapNat : StepsMon (fun θ => tQueryCapNat θ.n θ.D) 2 0 0 := by
  unfold tQueryCapNat
  growth [steps_queryCapNat]

/-- The number `⌈s/g⌉` of vertices of a piece, by counting up. -/
theorem steps_tCeilDiv_piece : StepsMon (fun θ => tCeilDiv (Nat.sqrt θ.D) θ.g) 0 1 0 := by
  have hpiece : StepsMon (fun θ => Nat.sqrt θ.D ⌈/⌉ θ.g) 0 1 0 := steps_pieceSizeNat
  unfold tCeilDiv
  growth [hpiece]

/-- The number of pieces, by counting up. -/
theorem steps_tCeilDiv_num : StepsMon (fun θ => tCeilDiv θ.n (pieceSizeNat θ.D θ.g)) 1 0 0 := by
  have hnum : StepsMon (fun θ => θ.n ⌈/⌉ pieceSizeNat θ.D θ.g) 1 0 0 :=
    steps_n.of_le fun θ hθ => by
      have hsqrt : 0 < Nat.sqrt θ.D := Nat.sqrt_pos.2 ((by norm_num : 0 < 16).trans_le hθ.hD16)
      have hpiece : 0 < pieceSizeNat θ.D θ.g := (Nat.lt_ceilDiv_iff hθ.hg).2 (by rwa [zero_mul])
      exact (Nat.ceilDiv_le_iff hpiece).2 (Nat.le_mul_of_pos_right _ hpiece)
  unfold tCeilDiv
  growth [hnum]

/-! ## The three terms of the bound dominate the monomials -/

/-- `D^{3/2} = (√D)³`. -/
private theorem rpow_three_half (D : ℕ) : (D : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt D ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul D.cast_nonneg]
  norm_num

/-- `n² √D κ log n ≤ κ n³ log n/g`, because `√D g ≤ n`. -/
private theorem mon_le_termScans {θ : CostParams} (hθ : θ.Hyp) :
    mon 2 1 1 θ ≤ termScans θ.n θ.g θ.κ := by
  have hκ : 0 ≤ θ.κ := zero_le_one.trans hθ.hκ
  rw [termScans, le_div_iff₀ hθ.g_pos]
  calc mon 2 1 1 θ * θ.g
      = (θ.n : ℝ) ^ 2 * θ.κ * Real.log θ.n * (Real.sqrt θ.D * θ.g) := by
        rw [mon_eq]
        ring
    _ ≤ (θ.n : ℝ) ^ 2 * θ.κ * Real.log θ.n * θ.n := by
        gcongr _ * ?_
        exact hθ.sqrt_mul_g_le
    _ = θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n := by ring

/-- `n² (√D)³ ≤ n^{log₂ 7} D^{3/2}`. -/
private theorem mon_le_termPrime {θ : CostParams} (hθ : θ.Hyp) :
    mon 2 3 0 θ ≤ termPrime strassen θ.n θ.D := by
  have htwo : (2 : ℝ) ≤ Real.logb 2 7 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
    norm_num
  rw [termPrime, strassen, rpow_three_half, mon_eq, pow_zero, mul_one, ← Real.rpow_ofNat]
  gcongr
  exact hθ.one_le_n

/-- `n² (√D)² ≤ n² D g`. -/
private theorem mon_le_termBuild {θ : CostParams} (hθ : θ.Hyp) :
    mon 2 2 0 θ ≤ termBuild θ.n θ.D θ.g := by
  rw [termBuild, mon_eq, pow_zero, mul_one, Real.sq_sqrt θ.D.cast_nonneg]
  exact le_mul_of_one_le_right (by positivity) hθ.one_le_g

/-- The sum of the three terms of the bound of Theorem 17. -/
noncomputable def budget (θ : CostParams) : ℝ :=
  termScans θ.n θ.g θ.κ + termPrime strassen θ.n θ.D + termBuild θ.n θ.D θ.g

/-- The first term is not negative. -/
private theorem termScans_nonneg {θ : CostParams} (hθ : θ.Hyp) : 0 ≤ termScans θ.n θ.g θ.κ := by
  have hκ : 0 ≤ θ.κ := zero_le_one.trans hθ.hκ
  unfold termScans
  positivity

/-- The second term is not negative. -/
private theorem termPrime_nonneg (θ : CostParams) : 0 ≤ termPrime strassen θ.n θ.D := by
  unfold termPrime strassen
  positivity

/-- The third term is not negative. -/
private theorem termBuild_nonneg (θ : CostParams) : 0 ≤ termBuild θ.n θ.D θ.g := by
  unfold termBuild
  positivity

/-- The sum is not negative. -/
theorem budget_nonneg {θ : CostParams} (hθ : θ.Hyp) : 0 ≤ budget θ :=
  add_nonneg (add_nonneg (termScans_nonneg hθ) (termPrime_nonneg θ)) (termBuild_nonneg θ)

/-- The first term is at most the sum. -/
theorem termScans_le_budget (θ : CostParams) : termScans θ.n θ.g θ.κ ≤ budget θ := by
  unfold budget
  linarith [termPrime_nonneg θ, termBuild_nonneg θ]

/-- The second term is at most the sum. -/
private theorem termPrime_le_budget {θ : CostParams} (hθ : θ.Hyp) :
    termPrime strassen θ.n θ.D ≤ budget θ := by
  unfold budget
  linarith [termScans_nonneg hθ, termBuild_nonneg θ]

/-- The third term is at most the sum. -/
theorem termBuild_le_budget {θ : CostParams} (hθ : θ.Hyp) :
    termBuild θ.n θ.D θ.g ≤ budget θ := by
  unfold budget
  linarith [termScans_nonneg hθ, termPrime_nonneg θ]

section within

variable {t : CostParams → ℕ} {e : Fin 3 → ℕ}

/-- Within the first term, `κ n³ log n/g`. -/
theorem _root_.ThreeSumApsp.Scale.SoftO.withinScans (h : costScale.SoftO t e)
    (he : ∀ i, e i ≤ ![2, 1, 1] i := by decide) : Steps t budget :=
  (steps_of_softO (h.mono he)).mono_right fun θ hθ =>
    (mon_le_termScans hθ).trans (termScans_le_budget θ)

/-- Within the second term, `n^{log₂ 7} D^{3/2}`. -/
theorem _root_.ThreeSumApsp.Scale.SoftO.withinPrime (h : costScale.SoftO t e)
    (he : ∀ i, e i ≤ ![2, 3, 0] i := by decide) : Steps t budget :=
  (steps_of_softO (h.mono he)).mono_right fun _ hθ =>
    (mon_le_termPrime hθ).trans (termPrime_le_budget hθ)

/-- Within the third term, `n² D g`. -/
theorem _root_.ThreeSumApsp.Scale.SoftO.withinBuild (h : costScale.SoftO t e)
    (he : ∀ i, e i ≤ ![2, 2, 0] i := by decide) : Steps t budget :=
  (steps_of_softO (h.mono he)).mono_right fun _ hθ =>
    (mon_le_termBuild hθ).trans (termBuild_le_budget hθ)

end within

namespace Steps

variable {t₁ t₂ m : CostParams → ℕ} {B : CostParams → ℝ}

/-- A factor is distributed over a sum. -/
theorem mul_add (h₁ : Steps (fun θ => m θ * t₁ θ) B) (h₂ : Steps (fun θ => m θ * t₂ θ) B) :
    Steps (fun θ => m θ * (t₁ θ + t₂ θ)) B :=
  (h₁.add h₂).mono_left fun _ _ => (Nat.mul_add _ _ _).le

end Steps

/-! ## The choice of the prime -/

/-- A sequence with `a(j+1) = 7 a(j) + b 4^j x + c` grows like `7^j`. -/
private theorem le_mul_seven_pow {a : ℕ → ℕ} {b c x : ℕ}
    (h : ∀ j, a (j + 1) = 7 * a j + b * (4 ^ j * x) + c) (j : ℕ) :
    a j + b * (4 ^ j * x) + c ≤ (a 0 + a 1) * 7 ^ j := by
  induction j with
  | zero =>
    rw [h 0]
    omega
  | succ j ih =>
    rw [h j, pow_succ 4, pow_succ 7]
    -- `7 a(j) + 5 b 4^j x + 2c ≤ 7 (a(j) + b 4^j x + c)`.
    linarith [ih, Nat.zero_le (b * (4 ^ j * x)), Nat.zero_le c]

/-- `7^⌈log₂ n⌉ = O(n^{log₂ 7})`. -/
private theorem steps_seven_pow_clog :
    Steps (fun θ => 7 ^ Nat.clog 2 θ.n) fun θ => (θ.n : ℝ) ^ Real.logb 2 7 :=
  Dominated.of_le_const_mul (C := 7) (by norm_num) fun θ hθ => by
    have hn : 1 ≤ θ.n := hθ.one_le_n_nat
    exact_mod_cast seven_pow_clog_le hn

/-- Strassen's recursion on matrices over `ℤ[x]/(x^p - 1)`, for all primes of the range:
`O(√D · 7^⌈log₂ n⌉ p²) = O(n^{log₂ 7} D^{3/2})`. -/
private theorem steps_sqrt_mul_strSteps :
    Steps (fun θ => Nat.sqrt θ.D * strSteps (Nat.sqrt θ.D) (Nat.clog 2 θ.n)) budget := by
  -- `strSteps p 0` is a quadratic polynomial in `p`, and
  -- `strSteps p (j + 1) = 7 strSteps p j + b 4^j p + c` with two numerals `b`, `c`.
  have hbase : StepsMon (fun θ => strSteps (Nat.sqrt θ.D) 0 + strSteps (Nat.sqrt θ.D) 1) 0 2 0 := by
    simp only [strSteps]
    growth [steps_sqrt]
  refine (((steps_of_softO steps_sqrt).mul ((steps_of_softO hbase).mul
    steps_seven_pow_clog)).mono_left fun θ _ => ?_).mono_right fun θ hθ => ?_
  · exact Nat.mul_le_mul_left _ (le_trans (by omega)
      (le_mul_seven_pow (a := strSteps (Nat.sqrt θ.D)) (fun _ => rfl) (Nat.clog 2 θ.n)))
  · refine le_trans (le_of_eq ?_) (termPrime_le_budget hθ)
    simp only [termPrime, strassen, rpow_three_half, mon_eq]
    ring

/-- The counts for all primes of the range: at most `√D` times the time of one count and a constant
`k`.  The summands stand in the order of `countTime`. -/
private theorem steps_sqrt_mul_countTime {k : ℕ} :
    Steps (fun θ => Nat.sqrt θ.D *
      (countTime θ.n (Nat.sqrt θ.D) (bitLen θ.U) (Nat.clog 2 θ.n) + k)) budget :=
  -- the table of doubles
  (steps_sqrt.mul steps_tDblTable).withinScans
  -- the residues of the three kinds of weights
  |>.mul_add (by growth [steps_sqrt, steps_tResidues] : StepsMon _ 2 1 1).withinScans
  -- the table for the Z-order
  |>.mul_add (by growth [steps_sqrt, steps_two_pow_clog] : StepsMon _ 1 1 0).withinScans
  -- the table of the sizes of the blocks
  |>.mul_add (steps_sqrt.mul steps_tSzTable).withinScans
  -- the matrices `P` and `Q`
  |>.mul_add (by growth [steps_sqrt, steps_buildZTime] : StepsMon _ 2 2 0).withinPrime
  -- their product
  |>.mul_add steps_sqrt_mul_strSteps
  -- the count
  |>.mul_add (steps_sqrt.mul steps_countZeroTime).withinScans
  -- calls and returns
  |>.mul_add (steps_sqrt.mul (.const _)).withinScans
  |>.mul_add (steps_sqrt.mul (.const _)).withinScans

/-- **The choice of the prime** is within the bound.  The summands stand in the order of
`chooseTime`: the list of the primes, the number of binary digits of `U`, `⌈log₂ n⌉`, and the
counts. -/
theorem steps_chooseTime : Steps (fun θ => chooseTime θ.n θ.U θ.D) budget :=
  steps_tPrimes.withinPrime
  |>.add steps_tBitLen.withinScans
  |>.add ((Scale.SoftO.const _).mul steps_clog).withinScans
  |>.add steps_sqrt_mul_countTime
  |>.add (Scale.SoftO.const _).withinScans

end Light.Sec3
