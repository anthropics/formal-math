/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters
public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize

/-!
# Section 4.4: the limits of the programs with rational parameters

`lim31` gives the limits within which the programs run, in two regimes: for m < m₀ queries compute
inner products; for m ≥ m₀ the limits are those of Theorem 30 plus the numbers formed in the
computation of L and t. They are what the programs need (`lim31_ok`), they allow exactly the cells
of the structure (`lim31_space`), and they are polynomial in N (`small_lim31`): every summand is at
most a constant, which depends on the parameters only, times ((N + 1) (D₀ + 1))^(20 + 2c).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

/-! ## The limits -/

/-- The numbers that the computation of L and t and the comparison with the threshold form. -/
def extraWord31 (G : RatParams) (D₀ : ℕ) : ℕ := G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q +
    G.m₀

/-- The word bound when m is below the threshold. -/
def wordSmall31 (G : RatParams) (N D₀ fr c : ℕ) : ℕ :=
  fr + 3 + 100 + 4 ^ logFour D₀ + extraWord31 G D₀ + D₀ * (N ^ c * N ^ c) + N ^ c

/-- The word bound of Theorem 30 at the parameters of the programs. -/
private abbrev word30At (G : RatParams) (N D₀ fr c : ℕ) : ℕ :=
  word30 (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) c

/-- The limits of the programs. -/
def lim31 (G : RatParams) (N D₀ fr c : ℕ) : Limits :=
  if logFour D₀ < G.m₀ then ⟨(wordSmall31 G N D₀ fr c : ℤ), fr + 3, G.L G.m₀ + 10⟩
  else ⟨((word30 (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) c + extraWord31 G D₀ : ℕ) : ℤ),
    G.blockEnd N D₀ fr, G.L (logFour D₀) + 10⟩

/-- Larger words do no harm. -/
theorem Lim30.of_word_le {w w' : ℤ} {sp dp : ℕ} {p : Sec2.Par} {t b0 : ℕ} {U : ℤ}
    (h : Lim30 ⟨w, sp, dp⟩ p t b0 U) (hw : w ≤ w') : Lim30 ⟨w', sp, dp⟩ p t b0 U :=
  ⟨⟨h.std.space_le.trans hw, h.std.const_le.trans hw⟩, h.space, h.value.trans hw, h.enc.trans hw,
    h.pow.trans hw⟩

theorem lim31_small {G : RatParams} {D₀ : ℕ} (h : logFour D₀ < G.m₀) (N fr c : ℕ) :
    lim31 G N D₀ fr c = ⟨(wordSmall31 G N D₀ fr c : ℤ), fr + 3, G.L G.m₀ + 10⟩ :=
  if_pos h

theorem lim31_large {G : RatParams} {D₀ : ℕ} (h : ¬ logFour D₀ < G.m₀) (N fr c : ℕ) :
    lim31 G N D₀ fr c =
      ⟨((word30 (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) c + extraWord31 G D₀ : ℕ) : ℤ),
        G.blockEnd N D₀ fr, G.L (logFour D₀) + 10⟩ :=
  if_neg h

/-- Below the threshold every number that the programs form is a summand of the word bound. -/
private theorem lim31_ok_small {G : RatParams} {D₀ : ℕ} (h : logFour D₀ < G.m₀) (N fr c : ℕ) :
    Lim31 ⟨(wordSmall31 G N D₀ fr c : ℤ), fr + 3, G.L G.m₀ + 10⟩ G N D₀ fr ((N : ℤ) ^ c) := by
  have sum : wordSmall31 G N D₀ fr c = fr + 3 + 100 + 4 ^ logFour D₀ +
      (G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q + G.m₀) + D₀ * (N ^ c * N ^ c) + N ^ c := rfl
  refine {
    std := ⟨?_, ?_⟩
    space := (if_pos h).le
    pow := ?_
    mword := ?_
    m0word := ?_
    ip := ?_
    large := fun h' => absurd h' (by omega) }
  all_goals
    dsimp only
    norm_cast
    generalize 4 ^ logFour D₀ = pow4 at *
    omega

/-- From the threshold on the word bound of Theorem 30 covers 4^m and the inner products, and the
numbers on the way to L and t are added to it. -/
private theorem lim31_ok_large {G : RatParams} {D₀ : ℕ} (h : ¬ logFour D₀ < G.m₀) (N fr c : ℕ) :
    Lim31 ⟨((word30At G N D₀ fr c + extraWord31 G D₀ : ℕ) : ℤ), G.blockEnd N D₀ fr,
      G.L (logFour D₀) + 10⟩ G N D₀ fr ((N : ℤ) ^ c) := by
  have hok := Lim30.of_word_le (w' := ((word30At G N D₀ fr c + extraWord31 G D₀ : ℕ) : ℤ))
    (lim30_ok (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) c)
        (by exact_mod_cast Nat.le_add_right _ _)
  obtain ⟨-, -, hvalue, -, hpow, -, -⟩ := word30_parts (parOf G N D₀) (switchOf31 G D₀)
      (blockAt N D₀ fr) c
  have extra : extraWord31 G D₀ = G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q + G.m₀ := rfl
  -- 4^m ≤ 10^m ≤ 10^(L + 1)
  have h4 : 4 ^ logFour D₀ ≤ 10 ^ logFour D₀ := Nat.pow_le_pow_left (by norm_num) _
  have h10 : 10 ^ logFour D₀ ≤ 10 ^ (G.L (logFour D₀) + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := G.ten_le_L (logFour D₀); omega)
  -- D₀ U² ≤ 10^m (7^L U)²
  have hU : N ^ c ≤ 7 ^ G.L (logFour D₀) * N ^ c := Nat.le_mul_of_pos_left _ (by positivity)
  have hip : D₀ * (N ^ c * N ^ c) ≤ word30At G N D₀ fr c :=
    (Nat.mul_le_mul ((le_D_logFour D₀).trans h4) (Nat.mul_le_mul hU hU)).trans hvalue
  have hpow4 : 4 ^ logFour D₀ ≤ word30At G N D₀ fr c := h4.trans (h10.trans hpow)
  refine {
    std := hok.std
    space := (if_neg h).le
    pow := ?_
    mword := ?_
    m0word := ?_
    ip := ?_
    large := fun _ => hok }
  all_goals
    dsimp only
    norm_cast
    omega

/-- The limits are what the programs need. -/
theorem lim31_ok (G : RatParams) (N D₀ fr c : ℕ) :
    Lim31 (lim31 G N D₀ fr c) G N D₀ fr ((N : ℤ) ^ c) := by
  by_cases h : logFour D₀ < G.m₀
  · exact lim31_small h N fr c ▸ lim31_ok_small h N fr c
  · exact lim31_large h N fr c ▸ lim31_ok_large h N fr c

/-- The limits allow for the nesting of calls and for the numbers of the input. -/
theorem lim31_facts (G : RatParams) (N D₀ fr c : ℕ) :
    G.L (logFour D₀) + 10 ≤ (lim31 G N D₀ fr c).depth ∧ (N : ℤ) ^ c ≤ (lim31 G N D₀ fr c).word := by
  by_cases h : logFour D₀ < G.m₀
  · rw [lim31_small h]
    have hentry : N ^ c ≤ wordSmall31 G N D₀ fr c := Nat.le_add_left _ _
    exact ⟨Nat.add_le_add_right (G.L_mono h.le) 10, by dsimp only; exact_mod_cast hentry⟩
  · rw [lim31_large h]
    obtain ⟨-, -, -, -, -, hentry, -⟩ := word30_parts (parOf G N D₀) (switchOf31 G D₀)
        (blockAt N D₀ fr) c
    have hentry' : N ^ c ≤ word30At G N D₀ fr c + extraWord31 G D₀ := hentry.trans
        (Nat.le_add_right _ _)
    exact ⟨le_rfl, by dsimp only; exact_mod_cast hentry'⟩

/-! ## The limits are polynomial in N

All limits are at most `slopeConst31 G` times the polynomial B = ((N + 1) (D₀ + 1))^(20 + 2c): the
summands that grow with N and D₀ are at most a numeral times B, and each summand that depends on the
parameters only occurs in `slopeConst31 G`. -/

/-- The constant factor in the polynomial bound on the limits; it depends on the parameters only. -/
def slopeConst31 (G : RatParams) : ℕ :=
  1200 + 4 ^ G.m₀ + 4 * (G.a + G.p) * (G.m₀ + 1) + G.b + G.q + G.m₀ + G.L G.m₀

/-- The exponent of two in the polynomial bound on the limits: the number of binary digits of the
constant factor. -/
def slopeExp31 (G : RatParams) : ℕ := Nat.size (slopeConst31 G)

theorem nine_le_slopeExp31 (G : RatParams) : 9 ≤ slopeExp31 G := by
  refine Nat.lt_size.2 ?_
  unfold slopeConst31
  generalize 4 ^ G.m₀ = x1
  generalize 4 * (G.a + G.p) * (G.m₀ + 1) = x2
  norm_num
  omega

/-- The base address of the block of Theorem 30 is polynomial in N, for a free pointer behind an
input of 3 + 2 N D₀ + 3 w cells, w ≤ N². -/
theorem blockAt_le {D₀ N w : ℕ} (hD : 1 ≤ D₀) (hDN : D₀ ≤ N) (hw : w ≤ N * N) :
    blockAt N D₀ (3 + 2 * (N * D₀) + 3 * w) ≤ 10 * (N + 1) ^ 3 := by
  have h4 := Nat.pow_clog_le_mul (b := 4) (by norm_num) hD
  change 3 + 2 * (N * D₀) + 3 * w + 3 + N * 4 ^ Nat.clog 4 D₀ + N * 4 ^ Nat.clog 4 D₀ ≤ _
  generalize 4 ^ Nat.clog 4 D₀ = F at *
  -- N D₀ ≤ N² and N 4^m ≤ 4 N D₀; the right side is 10 N³ + 30 N² + 30 N + 10
  have hND : N * D₀ ≤ N * N := Nat.mul_le_mul_left _ hDN
  have hNF : N * F ≤ 4 * (N * D₀) := (Nat.mul_le_mul_left _ h4).trans_eq (by ring)
  have hcube : 10 * (N + 1) ^ 3 = 10 * (N * N * N) + 30 * (N * N) + 30 * N + 10 := by ring
  omega

section poly

variable {G : RatParams} {N D₀ fr c : ℕ}

/-- The polynomial B = ((N + 1) (D₀ + 1))^(20 + 2c). -/
private def limPoly31 (N D₀ c : ℕ) : ℕ := ((N + 1) * (D₀ + 1)) ^ (20 + 2 * c)

private theorem pow_le_limPoly31 {x j : ℕ} (hx : x ≤ (N + 1) * (D₀ + 1)) (hj : j ≤ 20 + 2 * c) :
    x ^ j ≤ limPoly31 N D₀ c :=
  (Nat.pow_le_pow_left hx j).trans (Nat.pow_le_pow_right (Nat.mul_pos N.succ_pos D₀.succ_pos) hj)

private theorem le_mul_limPoly31 (N D₀ c x : ℕ) : x ≤ x * limPoly31 N D₀ c :=
  Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.mul_pos N.succ_pos D₀.succ_pos))

private theorem N_le_base (N D₀ : ℕ) : N + 1 ≤ (N + 1) * (D₀ + 1) :=
  Nat.le_mul_of_pos_right _ D₀.succ_pos

private theorem D_le_base (N D₀ : ℕ) : D₀ + 1 ≤ (N + 1) * (D₀ + 1) :=
  Nat.le_mul_of_pos_left _ N.succ_pos

/-- The constant times B, summand by summand. -/
private theorem slopeConst31_mul (G : RatParams) (B : ℕ) :
    slopeConst31 G * B = 1200 * B + 4 ^ G.m₀ * B + 4 * (G.a + G.p) * (G.m₀ + 1) * B + G.b * B + G.q
        * B +
      G.m₀ * B + G.L G.m₀ * B := by
  unfold slopeConst31
  ring

/-- Limits below the constant times B are small. -/
private theorem small_of_le {w sp dp : ℕ} (hw : w ≤ slopeConst31 G * limPoly31 N D₀ c)
    (hsp : sp ≤ slopeConst31 G * limPoly31 N D₀ c) (hdp : dp ≤ slopeConst31 G * limPoly31 N D₀ c) :
    Small (slopeExp31 G) (20 + 2 * c) [N, D₀] ⟨(w : ℤ), sp, dp⟩ := by
  have hfin :
      slopeConst31 G * limPoly31 N D₀ c ≤ polyBound (slopeExp31 G) (20 + 2 * c) [N, D₀] := by
    rw [show polyBound (slopeExp31 G) (20 + 2 * c) [N, D₀] = 2 ^ slopeExp31 G * limPoly31 N D₀ c by
      simp [polyBound, limPoly31]]
    exact Nat.mul_le_mul_right _ (Nat.lt_size_self (slopeConst31 G)).le
  exact ⟨Int.natCast_nonneg w, Int.ofNat_le.2 (hw.trans hfin), hsp.trans hfin, hdp.trans hfin⟩

/-- The numbers a m and p m on the way to L and t. -/
private theorem am_add_pm_le (G : RatParams) {m B : ℕ} (hm : m ≤ 4 * (G.m₀ + 1) * B) :
    G.a * m + G.p * m ≤ 4 * (G.a + G.p) * (G.m₀ + 1) * B :=
  calc G.a * m + G.p * m = (G.a + G.p) * m := by ring
    _ ≤ (G.a + G.p) * (4 * (G.m₀ + 1) * B) := Nat.mul_le_mul_left _ hm
    _ = 4 * (G.a + G.p) * (G.m₀ + 1) * B := by ring

/-- The word bound below the threshold. -/
private theorem wordSmall31_le (h : logFour D₀ < G.m₀) (hfr : fr + 3 ≤ 10 * limPoly31 N D₀ c) :
    wordSmall31 G N D₀ fr c ≤ slopeConst31 G * limPoly31 N D₀ c := by
  have up := le_mul_limPoly31 N D₀ c
  have hN := N_le_base N D₀
  have hD := D_le_base N D₀
  have hentry : N ^ c ≤ limPoly31 N D₀ c := pow_le_limPoly31 (by omega) (by omega)
  have hip : D₀ * (N ^ c * N ^ c) ≤ limPoly31 N D₀ c :=
    calc D₀ * (N ^ c * N ^ c)
        ≤ (N + 1) * (D₀ + 1) * (((N + 1) * (D₀ + 1)) ^ c * ((N + 1) * (D₀ + 1)) ^ c) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) c)
            (Nat.pow_le_pow_left (by omega) c))
      _ = ((N + 1) * (D₀ + 1)) ^ (1 + c + c) := by ring
      _ ≤ limPoly31 N D₀ c := pow_le_limPoly31 le_rfl (by omega)
  have h4 : 4 ^ logFour D₀ ≤ 4 ^ G.m₀ * limPoly31 N D₀ c :=
    (Nat.pow_le_pow_right (by norm_num) h.le).trans (up _)
  have ham := am_add_pm_le G (m := logFour D₀) (B := limPoly31 N D₀ c)
    (by have := up (4 * (G.m₀ + 1)); omega)
  have hb := up G.b
  have hq := up G.q
  have hm₀ := up G.m₀
  -- fr + 3 ≤ 10 B, 100 ≤ 100 B, and two summands are at most B
  have h100 := up 100
  rw [slopeConst31_mul]
  unfold wordSmall31 extraWord31
  omega

/-- The word bound from the threshold on. -/
private theorem word30At_add_le (hD : 1 ≤ D₀) (hb0 : blockAt N D₀ fr ≤ 10 * (N + 1) ^ 3)
    (hyp : G.Hyp N D₀) :
    word30At G N D₀ fr c + extraWord31 G D₀ ≤ slopeConst31 G * limPoly31 N D₀ c := by
  have up := le_mul_limPoly31 N D₀ c
  have hword : word30At G N D₀ fr c ≤ 512 * limPoly31 N D₀ c :=
    (word30_le hyp (blockAt N D₀ fr) c hb0).trans
      (Nat.mul_le_mul_left _ (pow_le_limPoly31 (N_le_base N D₀) le_rfl))
  -- m ≤ 4 D₀ ≤ 4 B
  have hm : logFour D₀ ≤ 4 * limPoly31 N D₀ c := by
    have h1 : logFour D₀ ≤ 4 * D₀ := logFour_le_four_mul hD
    have h2 : (N + 1) * (D₀ + 1) ≤ limPoly31 N D₀ c := by
      simpa using pow_le_limPoly31 (c := c) (j := 1) (le_refl ((N + 1) * (D₀ + 1))) (by omega)
    have := D_le_base N D₀
    omega
  have ham := am_add_pm_le G (m := logFour D₀) (B := limPoly31 N D₀ c)
    (hm.trans (Nat.mul_le_mul_right _ (by omega)))
  have hb := up G.b
  have hq := up G.q
  have hm₀ := up G.m₀
  rw [slopeConst31_mul]
  unfold extraWord31
  omega

end poly

/-- **The limits are polynomial in N.** -/
theorem small_lim31 {G : RatParams} {N D₀ fr : ℕ} (c : ℕ) (hD : 1 ≤ D₀) (_ : D₀ ≤ N)
    (hb0 : blockAt N D₀ fr ≤ 10 * (N + 1) ^ 3)
    (hyp : G.m₀ ≤ logFour D₀ → G.Hyp N D₀) :
    Small (slopeExp31 G) (20 + 2 * c) [N, D₀] (lim31 G N D₀ fr c) := by
  by_cases h : logFour D₀ < G.m₀
  · have hfr : fr + 3 ≤ 10 * limPoly31 N D₀ c := by
      have h1 : fr + 3 ≤ blockAt N D₀ fr := by unfold blockAt; omega
      have h2 : (N + 1) ^ 3 ≤ limPoly31 N D₀ c := pow_le_limPoly31 (N_le_base N D₀) (by omega)
      omega
    have hword := wordSmall31_le (G := G) h hfr
    have hdepth : G.L G.m₀ + 10 ≤ slopeConst31 G * limPoly31 N D₀ c :=
      le_trans (by unfold slopeConst31; generalize 4 ^ G.m₀ = pow4; omega)
          (le_mul_limPoly31 N D₀ c (slopeConst31 G))
    have hspace : fr + 3 ≤ wordSmall31 G N D₀ fr c := by
      unfold wordSmall31
      generalize 4 ^ logFour D₀ = pow4
      omega
    rw [lim31_small h]
    exact small_of_le hword (hspace.trans hword) hdepth
  · have hword := word30At_add_le (c := c) hD hb0 (hyp (by omega))
    obtain ⟨htop, -, -, -, -, -, hdepth⟩ :=
      word30_parts (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) c
    rw [lim31_large h]
    exact small_of_le hword ((htop.trans (Nat.le_add_right _ _)).trans hword)
      ((hdepth.trans (Nat.le_add_right _ _)).trans hword)


/-! ## Cells and natural numbers -/

/-- The limits allow exactly the cells of the structure. -/
theorem lim31_space (G : RatParams) (N D₀ fr c : ℕ) :
    (lim31 G N D₀ fr c).space = structEnd G N D₀ fr := by
  unfold lim31 structEnd
  split_ifs <;> rfl

/-- A natural number up to the free pointer fits in a word. -/
theorem lim31_natCast_le (G : RatParams) (N D₀ fr c : ℕ) {z : ℕ} (hz : z ≤ fr) :
    (z : ℤ) ≤ (lim31 G N D₀ fr c).word := by
  have hlim := lim31_ok G N D₀ fr c
  have hz' : z ≤ (lim31 G N D₀ fr c).space :=
    le_trans (by have := add_three_le_structEnd G N D₀ fr; omega) hlim.space
  exact le_trans (by exact_mod_cast hz') hlim.std.space_le


end Light.Sec4
