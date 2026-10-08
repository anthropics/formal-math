/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters

/-!
# Corollaries 26 and 31 in the light language: the preprocessing, with rational parameters

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D with
zero columns of X and zero rows of Y." Proof of Corollary 31: "We repeat the proof of Corollary 26
with L := ⌈cm⌉ and t := ⌈θm⌉". Then the preprocessing of Theorem 30 on the padded matrices; "for
smaller m the corollary again holds trivially".

The routine meets its specification (`pre31_meets`). It computes m and branches. Below the threshold
it writes the flag 0 (`PreInput31.ready_small`). From the threshold on it computes L, t and the
addresses, pads X, and pads Y by a copy and a fill with zeros (`prePad31_ends`,
`matAt_padInnerRows`); then it calls the preprocessing of Theorem 30 and writes the base address and
the flag 1 (`preBuild31_ends`, `PreInput31.ready_large`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## What the routine is given, and what it leaves -/

/-- The routines that the preprocessing calls meet their specifications. -/
structure PreCalls31 (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop where
  log4 : Log4Spec lim P
  levels : CeilMulSpec lim P Proc.levels31 G.a G.b
  switch : CeilMulSpec lim P Proc.switch31 G.p G.q
  padX : PadXSpec lim P
  copy : CopySpec lim P
  fill : FillSpec lim P
  preCore : PreCoreSpec lim P c

/-- What the preprocessing is given: besides what both routines are given, the matrices X and Y
stand at aX and aY. -/
structure PreInput31 (lim : Limits) (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (U : ℤ) (μ : ℕ → ℤ) : Prop
    extends Input31 lim G X Y aX aY fr U where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y

/-- Below the threshold the flag 0 is all that a query needs. -/
theorem PreInput31.ready_small (h : PreInput31 lim G X Y aX aY fr U μ) (hm : logFour D₀ < G.m₀)
    (hkept : SameOn (· < fr) μ μ') (hflag : μ' fr = 0) : Ready31 G X Y aX aY fr μ' :=
  ⟨h.matX.congr_below hkept h.belowX, h.matY.congr_below hkept h.belowY, fun _ => hflag,
    fun hm' => absurd hm' (by omega)⟩

/-- From the threshold on a query needs the flag 1, the base address, and the data structure of
Theorem 30 for the padded matrices. -/
theorem PreInput31.ready_large (h : PreInput31 lim G X Y aX aY fr U μ) (hm : G.m₀ ≤ logFour D₀)
    (hkept : SameOn (· < fr) μ μ') (hflag : μ' fr = 1) (hbase : μ' (fr + 1) = blockAt N D₀ fr)
    (hDS : Built31 G X Y fr μ') : Ready31 G X Y aX aY fr μ' :=
  ⟨h.matX.congr_below hkept h.belowX, h.matY.congr_below hkept h.belowY,
    fun hm' => absurd hm (by omega), fun _ => ⟨hflag, hbase, hDS⟩⟩

/-- **Y with zero rows**: a copy of Y followed by zeros is the padded matrix. -/
theorem matAt_padInnerRows {F a : ℕ} (mY : MatAt μ aY Y)
    (hcopy : ∀ i < D₀ * N, μ' (a + i) = μ (aY + i))
    (hzero : ∀ i < (F - D₀) * N, μ' (a + D₀ * N + i) = 0) : MatAt μ' a (padInnerRows F Y) := by
  intro i j
  unfold padInnerRows
  by_cases hi : (i : ℕ) < D₀
  · rw [dif_pos hi, Nat.add_assoc, hcopy _ (Nat.mul_add_lt_mul hi j.isLt), ← Nat.add_assoc]
    exact mY ⟨i, hi⟩ j
  · have hrow : (i : ℕ) * N = D₀ * N + ((i : ℕ) - D₀) * N := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' (not_lt.mp hi)]
    have hidx := Nat.mul_add_lt_mul (by have := i.isLt; omega : (i : ℕ) - D₀ < F - D₀) j.isLt
    rw [dif_neg hi, hrow, ← Nat.add_assoc, Nat.add_assoc (a + D₀ * N), hzero _ hidx]

/-! ## From the threshold on -/

/-- The areas from the free pointer on: fr, fr + 1, fr + 2 | X' | Y' | the block of Theorem 30 from
b0 on. F = 4^m is the padded inner dimension, and R the number of cells in the zero rows of Y'. -/
structure Areas31 (lim : Limits) (N D₀ fr F R : ℕ) : Prop where
  F_eq : F = D (logFour D₀)
  R_eq : R = (F - D₀) * N
  base : blockAt N D₀ fr = fr + 3 + N * F + N * F
  base_lt : blockAt N D₀ fr < lim.space
  D_le : D₀ ≤ F
  rows : D₀ * N + R = N * F
  F_le : F ≤ N * F

theorem PreInput31.areas (h : PreInput31 lim G X Y aX aY fr U μ) (hm : G.m₀ ≤ logFour D₀) :
    Areas31 lim N D₀ fr (D (logFour D₀)) ((D (logFour D₀) - D₀) * N) where
  F_eq := rfl
  R_eq := rfl
  base := rfl
  base_lt := (G.blockAt_lt_blockEnd N D₀ fr).trans_le (structEnd_large hm N fr ▸ h.lim.space)
  D_le := le_D_logFour D₀
  rows := by rw [← Nat.add_mul, Nat.add_sub_cancel' (le_D_logFour D₀), Nat.mul_comm]
  F_le := Nat.le_mul_of_pos_left _ h.one_le_N

/-- The time of prePad31. -/
def tPrePad31 (G : RatParams) (N D₀ : ℕ) : ℕ :=
  tCeilMul G.a (logFour D₀) + tCeilMul G.p (logFour D₀) + tPadX N (D (logFour D₀)) + tCopy (D₀ * N)
    + tFill ((D (logFour D₀) - D₀) * N) + 60

/-- The state after prePad31: the locals hold the parameters and the addresses, the padded matrices
stand at their places, and only cells between fr and b0 have changed. -/
def Padded31 (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (aX aY fr : ℕ) (μ : ℕ → ℤ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [N, D₀, aX, aY, fr, logFour D₀, (D (logFour D₀) : ℕ), (G.L (logFour D₀) : ℕ),
      (G.t (logFour D₀) : ℕ), (paddedXAt fr : ℕ), (paddedYAt N D₀ fr : ℕ), (blockAt N D₀ fr : ℕ), r,
      (N * D (logFour D₀) : ℕ)], μ'⟩ ∧
    MatAt μ' (paddedXAt fr) (padInnerCols (D (logFour D₀)) X) ∧
    MatAt μ' (paddedYAt N D₀ fr) (padInnerRows (D (logFour D₀)) Y) ∧
    SameOutside μ μ' fr (blockAt N D₀ fr - fr)

/-- **Setting up**: L, t, the addresses, and the padded matrices. The cell fr + 2 holds 4^m. -/
theorem prePad31_ends {c d : ℕ} (C : PreCalls31 lim P c G) (h : PreInput31 lim G X Y aX aY fr U μ)
    (hm : G.m₀ ≤ logFour D₀) (hd : d + (G.L (logFour D₀) + 7) ≤ lim.depth) :
    Ends lim P d prePad31
      ⟨frame [N, D₀, aX, aY, fr, logFour D₀], Function.update μ (fr + 2) ((D (logFour D₀) : ℕ) : ℤ)⟩
      (tPrePad31 G N D₀) (Padded31 G X Y aX aY fr μ) := by
  have A := h.areas hm
  unfold prePad31 tPrePad31 Padded31 paddedXAt paddedYAt
  rw [A.base]
  generalize D (logFour D₀) = F at A ⊢
  generalize (F - D₀) * N = R at A ⊢
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁, μ₁ = Function.update μ (fr + 2) ((F : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hμ₁]
  obtain ⟨-, hR, hb0, hb0lt, hDF, hrows, hFN⟩ := A
  have hw := h.lim.std.space_le
  have h100 := h.lim.std.const_le
  have hD := h.one_le_D
  have hbX := h.belowX
  have hbY := h.belowY
  have hRZ : ((F : ℤ) - D₀) * N = R := by rw [hR]; push_cast [Nat.cast_sub hDF]; rfl
  have hread : μ₁ (fr + 2) = F := by rw [hμ₁]; exact Function.update_self ..
  have hout₁ : SameOutside μ μ₁ (fr + 2) 1 := hμ₁ ▸ SameOn.refl.write (by omega) _
  have hkept₁ : ∀ b < fr, μ₁ b = μ b := fun b hb => hout₁ b (.inl (by omega))
  have haddr : ((fr : ℤ) + 2).toNat = fr + 2 := by omega
  -- F := mem[fr + 2]
  light_set F using haddr, hread
  -- L := ⌈a m / b⌉
  light_call (C.levels (logFour D₀) μ₁ h.lim.wordL _ (by omega)) with _ μ₁ ⟨rfl, rfl⟩
  -- t := ⌈p m / q⌉
  light_call (C.switch (logFour D₀) μ₁ h.lim.wordT _ (by omega)) with _ μ₁ ⟨rfl, rfl⟩
  -- aX' := fr + 3 ; NF := N * F ; aY' := aX' + NF ; b0 := aY' + NF
  light_set (fr + 3 : ℕ)
  light_set (N * F : ℕ)
  light_set (fr + 3 + N * F : ℕ)
  light_set (fr + 3 + N * F + N * F : ℕ)
  -- padX(N, D, F, aX, aX')
  light_call (C.padX N D₀ F aX (fr + 3) X μ₁ hDF (by omega)
    (h.matX.congr_below hkept₁ hbX) (by omega) (by omega) _ (by omega)) with - μ₂ ⟨hpadX, hout₂⟩
  -- copy(aY, aY', D N)
  light_call (C.copy aY (fr + 3 + N * F) (D₀ * N) μ₂ (by omega) (by omega) (by omega)
    (.inl (by omega)) _ (by omega)) with - μ₃ ⟨hcopy, hout₃⟩
  -- fill(aY' + D N, (F - D) N, 0)
  light_call (C.fill (fr + 3 + N * F + D₀ * N) R 0 μ₃ (by omega) (by omega) _
    (by omega)) using hRZ with r μ₄ ⟨hfill, hout₄⟩
  refine ⟨r, μ₄, rfl, ?_, ?_, fun b hb => ?_⟩
  · exact hpadX.congr fun b _ hb => by rw [hout₄ b (.inl (by omega)), hout₃ b (.inl (by omega))]
  · refine matAt_padInnerRows (h.matY.congr_below hkept₁ hbY) (fun i hi => ?_) (hR ▸ hfill)
    rw [hout₄ _ (.inl (by omega)), hcopy i hi, hout₂ _ (.inl (by omega))]
  · rw [hout₄ b (by omega), hout₃ b (by omega), hout₂ b (by omega), hout₁ b (by omega)]

/-- **The preprocessing of Theorem 30** on the padded matrices, the base address and the flag 1. -/
theorem preBuild31_ends {c d : ℕ} (C : PreCalls31 lim P c G) (h : PreInput31 lim G X Y aX aY fr U μ)
    (hm : G.m₀ ≤ logFour D₀) (hd : d + (G.L (logFour D₀) + 7) ≤ lim.depth) {σ : State}
    (hσ : Padded31 G X Y aX aY fr μ σ) :
    Ends lim P d preBuild31 σ (tPreCore c (parOf G N D₀) (switchOf31 G D₀) + 60) fun σ' =>
      Ready31 G X Y aX aY fr σ'.mem ∧ SameOutside μ σ'.mem fr (structEnd G N D₀ fr - fr) := by
  obtain ⟨r, μ₄, rfl, mX, mY, hout₄⟩ := hσ
  have hb0 := (h.areas hm).base
  have hb0lt := (h.areas hm).base_lt
  have hw := h.lim.std.space_le
  have h100 := h.lim.std.const_le
  have hb0top := G.blockAt_lt_blockEnd N D₀ fr
  have hfr3 := add_three_le_structEnd G N D₀ fr
  unfold preBuild31
  -- preCore(L, m, t, N, F, aX', aY', b0)
  light_call (C.preCore (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
      (paddedYAt N D₀ fr)
    (blockAt N D₀ fr) _ _ U μ₄ (G.t_le _) (h.lim.large hm) (abs_padInnerCols_le h.absX h.zero_le_U)
    (abs_padInnerRows_le h.absY h.zero_le_U) mX mY
    (by change fr + 3 + N * D (logFour D₀) ≤ _; omega)
    (by change fr + 3 + N * D (logFour D₀) + D (logFour D₀) * N ≤ _
        rw [Nat.mul_comm (D (logFour D₀)) N]; omega) _
    (by change d + 1 + (G.L (logFour D₀) + 6) ≤ _; omega)) using parOf, switchOf31, Sec2.Par.D
    with - μ₅ ⟨hDS, hout₅⟩
  have hout₅ : SameOutside μ₄ μ₅ (blockAt N D₀ fr) (G.blockEnd N D₀ fr - blockAt N D₀ fr) := hout₅
  -- mem[fr + 1] := b0
  light_store (fr + 1) (blockAt N D₀ fr)
  -- mem[fr] := 1
  light_store fr 1
  -- outside the cells from fr to the end of the block nothing has changed
  have hsame : SameOutside μ μ₅ fr (structEnd G N D₀ fr - fr) := by
    rw [structEnd_large hm]
    exact fun b hb => (hout₅ b (by omega)).trans (hout₄ b (by omega))
  dsimp only
  refine ⟨h.ready_large hm (fun b (hb : b < fr) => ?_) (Function.update_self ..) ?_
    (dsReady_congr hDS fun a ha => ?_), (hsame.write (by omega) _).write (by omega) _⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hsame b (.inl hb)]
  · rw [Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-! ## The routine -/

theorem pre31_meets {c : ℕ} (G : RatParams) (hP : P[Proc.pre31]? = some (pre31Body G))
    (C : PreCalls31 lim P c G) : PreSpec31 lim P c G :=
        by
  intro N D₀ aX aY fr X Y U μ hin mX mY
  have h : PreInput31 lim G X Y aX aY fr U μ := ⟨hin, mX, mY⟩
  have hlim := hin.lim
  refine fun d hd => ⟨pre31Body G, hP, ?_⟩
  have hw := hlim.std.space_le
  have h100 := hlim.std.const_le
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hsp := hlim.space
  have hm₀word := hlim.m0word
  have hmword : (logFour D₀ : ℤ) ≤ lim.word := by
    have : logFour D₀ ≤ G.a * logFour D₀ := Nat.le_mul_of_pos_left _ (by have := G.hc; omega)
    exact le_trans (by exact_mod_cast (by omega :
      logFour D₀ ≤ G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q)) hlim.mword
  unfold pre31Body
  -- m := log4(D, fr + 2), which writes 4^m to the cell fr + 2
  refine Ends.callToThen (C.log4 D₀ (fr + 2) μ (by omega) hlim.pow hmword _ (by omega)) ?_
    (hT := by simp [tPre31, logFour]; omega)
  rintro _ _ ⟨rfl, rfl⟩
  -- if m < m₀
  refine Ends.iteLast (fun hsmall => ?_) (fun hlarge => ?_) (hT := by simp [tPre31, logFour]; omega)
  · -- mem[fr] := 0
    have hm : logFour D₀ < G.m₀ := by simpa [logFour] using hsmall
    have htop : structEnd G N D₀ fr - fr = 3 := by rw [structEnd_small hm]; omega
    refine Ends.storeTo fr 0 ⟨h.ready_small hm (fun b (hb : b < fr) => ?_)
      (Function.update_self ..), ?_⟩ (hT := by simp [tPre31, logFour]; omega)
    · change Function.update (Function.update μ _ _) fr 0 b = μ b
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rw [htop]
      exact (SameOn.refl.write (by omega) _).write (by omega) _
  · have hm : G.m₀ ≤ logFour D₀ := by simpa [logFour] using hlarge
    -- the padded matrices, then the data structure of Theorem 30
    refine Ends.next (tPrePad31 G N D₀) ((prePad31_ends C h hm hd).mono le_rfl fun σ hσ =>
      (preBuild31_ends C h hm hd hσ).mono ?_ fun _ hQ => hQ) ?_
    all_goals
      simp only [tPre31, tPrePad31, if_neg (not_lt.mpr hm)]
      simp [logFour]
      omega

end Light.Sec4
