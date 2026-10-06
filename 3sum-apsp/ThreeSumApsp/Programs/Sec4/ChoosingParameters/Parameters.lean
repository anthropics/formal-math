/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Setup
public import ThreeSumApsp.Programs.Sec4.Theorem30.Time

/-!
# Corollaries 26 and 31 in the light language: rational parameters in the program text

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D";
proof of Corollary 31: "with L := ⌈cm⌉ and t := ⌈θm⌉". A program is a finite text, so it can hold c
and θ only if they are rational: c = a/b and θ = p/q (`RatParams`). For real c and θ the statements
follow by approximation (`exists_ratParams`). Corollary 26 is the case c = 21, θ = 1/9, with the
threshold 60 (`ratParams26`).

This file has the parameters, what a structure at the free pointer fr consists of (`structEnd`,
`Ready31`), what the routines ask of the limits (`Lim31`), the query with its specification and its
proof (`QuerySpec31`, `query31_meets`), and the text and the specification of the preprocessing
(`pre31Body`, `PreSpec31`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters -/

/-- The parameters in the program text: c = a/b > 10, θ = p/q in (0, 0.9), and the threshold m₀ ≥ 1
below which queries compute inner products. -/
structure RatParams where
  a : ℕ
  b : ℕ
  p : ℕ
  q : ℕ
  m₀ : ℕ
  hb : 1 ≤ b
  hq : 1 ≤ q
  hc : 10 * b < a
  hp : 1 ≤ p
  hθ : 10 * p < 9 * q
  hm₀ : 1 ≤ m₀

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-- L = ⌈(a/b) m⌉. -/
def RatParams.L (G : RatParams) (m : ℕ) : ℕ := (G.a * m + G.b - 1) / G.b
/-- t = ⌈(p/q) m⌉. -/
def RatParams.t (G : RatParams) (m : ℕ) : ℕ := (G.p * m + G.q - 1) / G.q

/-- 10 m ≤ L. -/
theorem RatParams.ten_le_L (G : RatParams) (m : ℕ) : 10 * m ≤ G.L m := by
  unfold RatParams.L
  rw [Nat.le_div_iff_mul_le G.hb]
  have h1 : 10 * G.b * m ≤ G.a * m := Nat.mul_le_mul_right _ G.hc.le
  have h2 : 10 * m * G.b = 10 * G.b * m := by ring
  have := G.hb
  omega

/-- t ≤ m. -/
theorem RatParams.t_le (G : RatParams) (m : ℕ) : G.t m ≤ m := by
  unfold RatParams.t
  have hq := G.hq
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have h1 : 10 * G.p * m ≤ 9 * G.q * m := Nat.mul_le_mul_right _ G.hθ.le
  have h2 : G.p * m ≤ G.q * m := by
    have e1 : 10 * G.p * m = 10 * (G.p * m) := by ring
    have e2 : 9 * G.q * m = 9 * (G.q * m) := by ring
    omega
  omega

theorem RatParams.L_mono (G : RatParams) {m m' : ℕ} (h : m ≤ m') : G.L m ≤ G.L m' := by
  unfold RatParams.L
  have := Nat.mul_le_mul_left G.a h
  exact Nat.div_le_div_right (by omega)

/-- a m ≤ b L. -/
theorem RatParams.am_le (G : RatParams) (m : ℕ) : G.a * m ≤ G.b * G.L m := by
  unfold RatParams.L
  have hb := G.hb
  have hdiv := Nat.div_add_mod (G.a * m + G.b - 1) G.b
  have hmod := Nat.mod_lt (G.a * m + G.b - 1) (by omega : 0 < G.b)
  omega

/-- p m ≤ q m. -/
theorem RatParams.pm_le (G : RatParams) (m : ℕ) : G.p * m ≤ G.q * m :=
  Nat.mul_le_mul_right _ (by have := G.hθ; omega)

/-- The parameters of Theorem 30. -/
def parOf (G : RatParams) (N D₀ : ℕ) : Sec2.Par := ⟨G.L (logFour D₀), logFour D₀, N⟩
/-- The switching order. -/
def switchOf31 (G : RatParams) (D₀ : ℕ) : ℕ := G.t (logFour D₀)
/-- The hypotheses of Theorem 30 at these parameters. -/
abbrev RatParams.Hyp (G : RatParams) (N D₀ : ℕ) : Prop := Hyp30 (parOf G N D₀) (switchOf31 G D₀)
/-- The cost (8) of the preprocessing of Theorem 30 at these parameters. -/
noncomputable abbrev RatParams.preCost (G : RatParams) (N D₀ : ℕ) : ℝ :=
  cost8 (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N
/-- The cost L ∑ α_d of a query of Theorem 30 at these parameters. -/
noncomputable abbrev RatParams.queryCost (G : RatParams) (D₀ : ℕ) : ℝ :=
  costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀)
/-- The first address after the block of Theorem 30. -/
abbrev RatParams.blockEnd (G : RatParams) (N D₀ fr : ℕ) : ℕ :=
  top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr)
/-- The first address that is not used. -/
def structEnd (G : RatParams) (N D₀ fr : ℕ) : ℕ :=
  if logFour D₀ < G.m₀ then fr + 3 else top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr)

/-- Below the threshold a structure has three cells. -/
theorem structEnd_small (h : logFour D₀ < G.m₀) (N fr : ℕ) : structEnd G N D₀ fr = fr + 3 :=
  if_pos h

/-- For m ≥ m₀ a structure ends with the block of Theorem 30. -/
theorem structEnd_large (h : G.m₀ ≤ logFour D₀) (N fr : ℕ) :
    structEnd G N D₀ fr = G.blockEnd N D₀ fr :=
  if_neg (not_lt.2 h)

/-- The block of Theorem 30 begins after the first three cells. -/
theorem add_three_le_blockAt (N D₀ fr : ℕ) : fr + 3 ≤ blockAt N D₀ fr := by
  unfold blockAt
  omega

/-- The block of Theorem 30 is not empty. -/
theorem RatParams.blockAt_lt_blockEnd (G : RatParams) (N D₀ fr : ℕ) :
    blockAt N D₀ fr < G.blockEnd N D₀ fr :=
  base_lt_top _ _ _

/-- The cells that a query of Theorem 30 writes lie in the block. -/
theorem RatParams.scratch_in_block (G : RatParams) (N D₀ fr : ℕ) :
    blockAt N D₀ fr ≤ aWD (parOf G N D₀) (blockAt N D₀ fr) ∧
      aWD (parOf G N D₀) (blockAt N D₀ fr) + (3 * (parOf G N D₀).L + (parOf G N D₀).m)
        ≤ G.blockEnd N D₀ fr :=
  Sec4.scratch_in_block _ _ _

/-- A structure has at least three cells. -/
theorem add_three_le_structEnd (G : RatParams) (N D₀ fr : ℕ) : fr + 3 ≤ structEnd G N D₀ fr := by
  have hblock := add_three_le_blockAt N D₀ fr
  have hend := G.blockAt_lt_blockEnd N D₀ fr
  by_cases h : logFour D₀ < G.m₀
  · rw [structEnd_small h]
  · rw [structEnd_large (not_lt.1 h)]
    omega

/-- m ≤ L. -/
theorem logFour_le_levels (G : RatParams) (N D₀ : ℕ) : (parOf G N D₀).m ≤ (parOf G N D₀).L := by
  change logFour D₀ ≤ G.L (logFour D₀)
  have := G.ten_le_L (logFour D₀)
  omega

/-- The data structure of Theorem 30 for the padded matrices has been built in the cells after fr.
-/
abbrev Built31 (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (fr : ℕ) (μ : ℕ → ℤ) : Prop :=
  DSReady (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
    (paddedYAt N D₀ fr) (blockAt N D₀ fr) (padInnerCols (D (logFour D₀)) X)
    (padInnerRows (D (logFour D₀)) Y) μ

/-- **The cells from fr on hold what a query needs.** -/
structure Ready31 (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (μ : ℕ → ℤ) : Prop where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  small : logFour D₀ < G.m₀ → μ fr = 0
  large : G.m₀ ≤ logFour D₀ → μ fr = 1 ∧ μ (fr + 1) = blockAt N D₀ fr ∧ Built31 G X Y fr μ

/-- The limits that the two routines need. -/
structure Lim31 (lim : Limits) (G : RatParams) (N D₀ fr : ℕ) (U : ℤ) : Prop where
  std : Std lim
  space : structEnd G N D₀ fr ≤ lim.space
  pow : ((4 ^ logFour D₀ : ℕ) : ℤ) ≤ lim.word
  /-- For the computation of L and t. -/
  mword : ((G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q : ℕ) : ℤ) ≤ lim.word
  m0word : (G.m₀ : ℤ) ≤ lim.word
  ip : (D₀ : ℤ) * (U * U) ≤ lim.word
  large : G.m₀ ≤ logFour D₀ → Lim30 lim (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) U

/-- The numbers formed on the way to L fit in a word. -/
theorem Lim31.wordL (h : Lim31 lim G N D₀ fr U) : ((G.a * logFour D₀ + G.b : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast (by omega :
    G.a * logFour D₀ + G.b ≤ G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q)) h.mword

/-- The numbers formed on the way to t fit in a word. -/
theorem Lim31.wordT (h : Lim31 lim G N D₀ fr U) : ((G.p * logFour D₀ + G.q : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast (by omega :
    G.p * logFour D₀ + G.q ≤ G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q)) h.mword

/-- **What both routines are given**: matrices X and Y with entries bounded by U, the addresses aX
and aY of their cells, which lie below the free pointer fr, and limits that suffice. -/
structure Input31 (lim : Limits) (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (U : ℤ) : Prop where
  one_le_D : 1 ≤ D₀
  one_le_N : 1 ≤ N
  lim : Lim31 lim G N D₀ fr U
  absX : ∀ i j, |X i j| ≤ U
  absY : ∀ i j, |Y i j| ≤ U
  belowX : aX + N * D₀ ≤ fr
  belowY : aY + D₀ * N ≤ fr

theorem Input31.zero_le_U (h : Input31 lim G X Y aX aY fr U) : 0 ≤ U :=
  le_trans (abs_nonneg _) (h.absX ⟨0, h.one_le_N⟩ ⟨0, h.one_le_D⟩)

/-! ## The query: the text is query31Body -/

/-- The time of a query. -/
def tQuery31 (G : RatParams) (D₀ : ℕ) : ℕ :=
  (if logFour D₀ < G.m₀ then tIpAt D₀ else tQueryAt (G.L (logFour D₀)) (logFour D₀)
      (switchOf31 G D₀)) + 20

/-- query31 returns the entry (XY)[I, J], keeps the structure ready, and changes only cells of the
structure behind its first three. -/
def QuerySpec31 (lim : Limits) (P : Program) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ)
      (μ : ℕ → ℤ) (I J : Fin N), Input31 lim G X Y aX aY fr U → Ready31 G X Y aX aY fr μ →
    ∀ d, d + 3 ≤ lim.depth → Meets lim P Proc.query31 d [(I : ℕ), (J : ℕ), N, D₀, aX, aY, fr] μ
        (tQuery31 G D₀) fun r μ' =>
      r = (X * Y) I J ∧ Ready31 G X Y aX aY fr μ' ∧
          SameOutside μ μ' (fr + 3) (structEnd G N D₀ fr - (fr + 3))

/-- A query to the data structure of Theorem 30 changes only cells of its block, so that the
structure stays ready. -/
theorem Ready31.of_query (h : Ready31 G X Y aX aY fr μ) (bX : aX + N * D₀ ≤ fr)
    (bY : aY + D₀ * N ≤ fr) (hm : G.m₀ ≤ logFour D₀) (hkept : ∀ a < blockAt N D₀ fr, μ' a = μ a)
    (hDS : Built31 G X Y fr μ') : Ready31 G X Y aX aY fr μ' := by
  have hb0 := add_three_le_blockAt N D₀ fr
  obtain ⟨hflag, hbase, -⟩ := h.large hm
  exact ⟨h.matX.congr_below hkept (by omega), h.matY.congr_below hkept (by omega),
    fun hm' => absurd hm (by omega),
    fun _ => ⟨(hkept _ (by omega)).trans hflag, (hkept _ (by omega)).trans hbase, hDS⟩⟩

/-- query31 reads the flag and calls the query of Theorem 30 if it is 1 and the inner product
otherwise; it returns the entry (XY)[I, J] and keeps the structure ready. -/
theorem query31_meets (G : RatParams) (hP : P[Proc.query31]? = some query31Body)
    (hq : QueryAtSpec lim P) (hip : IpAtSpec lim P) : QuerySpec31 lim P G := by
  intro N D₀ aX aY fr X Y U μ I J hin hR
  have hlim := hin.lim
  have bX := hin.belowX
  have bY := hin.belowY
  refine fun d hd => ⟨query31Body, hP, ?_⟩
  have hw := hlim.std.space_le
  have h100 := hlim.std.const_le
  have hU0 := hin.zero_le_U
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hsp := hlim.space
  unfold query31Body
  -- if mem[fr] = 1
  refine Ends.iteLast (fun hflag => ?_) (fun hflag => ?_) (hT := by simp [tQuery31])
  · -- the data structure has been built: return queryAt(I, J, mem[fr + 1])
    have hlarge : G.m₀ ≤ logFour D₀ := by
      by_contra hc
      have hzero := hR.small (by omega)
      have hone : μ fr = 1 := by simpa using hflag
      omega
    obtain ⟨-, hbase, hDS⟩ := hR.large hlarge
    have haddr : ((fr : ℤ) + 1).toNat = fr + 1 := by omega
    refine Ends.callTo
      (hq (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
        (paddedYAt N D₀ fr) (blockAt N D₀ fr) _ _ U μ I J (G.t_le _) (hlim.large hlarge)
        (abs_padInnerCols_le hin.absX hU0) (abs_padInnerRows_le hin.absY hU0) hDS _ (by omega)) ?_
      (by light_side [haddr, hbase])
      (hT := by simp [tQuery31, if_neg (not_lt.mpr hlarge), parOf]; omega)
    rintro r μ' ⟨hr, hDS', hout⟩
    have hscratch := G.scratch_in_block N D₀ fr
    have hb0 := add_three_le_blockAt N D₀ fr
    have htop := structEnd_large hlarge N fr
    refine ⟨?_, hR.of_query bX bY hlarge (fun a ha => hout a (by omega)) hDS',
      fun a ha => hout a (by omega)⟩
    -- padding changes no entry of the product
    exact hr.trans (congrFun (congrFun
      (Corollary26.padding (D (logFour D₀)) (le_D_logFour D₀) X Y) I) J)
  · -- m is below the threshold: return the inner product ipAt(I, J, N, D, aX, aY)
    have hsmall : logFour D₀ < G.m₀ := by
      by_contra hc
      exact hflag (by simpa using (hR.large (by omega)).1)
    refine Ends.callTo (hip N D₀ aX aY X Y U μ I J hin.one_le_D hR.matX hR.matY hin.absX hin.absY
      (by omega) (by omega) hlim.ip _ (by omega)) ?_
      (hT := by simp [tQuery31, if_pos hsmall]; omega)
    rintro r μ' ⟨hr, rfl⟩
    exact ⟨hr, hR, .refl⟩

/-! ## The preprocessing: text and interface -/

/-- The time of ceilMul: it counts up to ⌈a m / b⌉. -/
def tCeilMul (a m : ℕ) : ℕ := 20 * (a * m) + 40

/-- Procedure number pn returns ⌈a m / b⌉ on the argument m, and changes no cell. -/
def CeilMulSpec (lim : Limits) (P : Program) (pn a b : ℕ) : Prop :=
  ∀ (m : ℕ) (μ : ℕ → ℤ), ((a * m + b : ℕ) : ℤ) ≤ lim.word → ∀ d, d ≤ lim.depth →
    Meets lim P pn d [m] μ (tCeilMul a m) fun r μ' => r = ((a * m + b - 1) / b : ℕ) ∧ μ' = μ

namespace Pre31

/-- The locals of pre31. The first five are its arguments N, D, aX, aY, fr. Then come m, 4^m, L, t,
the addresses of the padded matrices, the base address b0 of the block of Theorem 30, a result that
is not used, and the product N 4^m. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Dim : ℕ := 1
@[inherit_doc Size] abbrev MatX : ℕ := 2
@[inherit_doc Size] abbrev MatY : ℕ := 3
@[inherit_doc Size] abbrev Free : ℕ := 4
@[inherit_doc Size] abbrev Log : ℕ := 5
@[inherit_doc Size] abbrev Padded : ℕ := 6
@[inherit_doc Size] abbrev Levels : ℕ := 7
@[inherit_doc Size] abbrev Switch : ℕ := 8
@[inherit_doc Size] abbrev PadX : ℕ := 9
@[inherit_doc Size] abbrev PadY : ℕ := 10
@[inherit_doc Size] abbrev Block : ℕ := 11
@[inherit_doc Size] abbrev Res : ℕ := 12
@[inherit_doc Size] abbrev Area : ℕ := 13

end Pre31

open Pre31 in
/-- The first part of pre31 for m ≥ m₀: L, t, the addresses, and the padded matrices. -/
def prePad31 : Stmt :=
  .set Padded (M (v Free +' k 2)) ;;
  .call Proc.levels31 [v Log] Levels ;;
  .call Proc.switch31 [v Log] Switch ;;
  .set PadX (v Free +' k 3) ;;
  .set Area (v Size *' v Padded) ;;
  .set PadY (v PadX +' v Area) ;;
  .set Block (v PadY +' v Area) ;;
  .call Proc.padX [v Size, v Dim, v Padded, v MatX, v PadX] Res ;;
  .call Proc.copy [v MatY, v PadY, v Dim *' v Size] Res ;;
  .call Proc.fill [v PadY +' v Dim *' v Size, (v Padded -' v Dim) *' v Size, k 0] Res

open Pre31 in
/-- The second part: the preprocessing of Theorem 30, the base address and the flag 1. -/
def preBuild31 : Stmt :=
  .call Proc.preCore [v Levels, v Log, v Switch, v Size, v Padded, v PadX, v PadY, v Block] Res ;;
  .store (v Free +' k 1) (v Block) ;;
  .store (v Free) (k 1)

/-- The part of pre31 for m ≥ m₀. -/
def preLarge31 : Stmt := prePad31 ;; preBuild31

open Pre31 in
/-- pre31(N, D, aX, aY, fr): m and 4^m; for m < m₀ the flag 0, for m ≥ m₀ preLarge31. -/
def pre31Body (G : RatParams) : Stmt :=
  .call Proc.log4 [v Dim, v Free +' k 2] Log ;;
  .ite (v Log <' k G.m₀) (.store (v Free) (k 0)) preLarge31

/-- The time of the preprocessing; c is the constant of the shared stage. -/
def tPre31 (c : ℕ) (G : RatParams) (N D₀ : ℕ) : ℕ :=
  tLog4 (logFour D₀) + 30 +
    if logFour D₀ < G.m₀ then 0 else
      tCeilMul G.a (logFour D₀) + tCeilMul G.p (logFour D₀) + tPadX N (D (logFour D₀))
        + tCopy (D₀ * N) + tFill ((D (logFour D₀) - D₀) * N)
        + tPreCore c (parOf G N D₀) (switchOf31 G D₀) + 120

/-- pre31 prepares the cells from fr on, about which nothing is assumed, for queries to XY. -/
def PreSpec31 (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ)
      (μ : ℕ → ℤ), Input31 lim G X Y aX aY fr U → MatAt μ aX X → MatAt μ aY Y →
    ∀ d, d + (G.L (logFour D₀) + 7) ≤ lim.depth → Meets lim P Proc.pre31 d [N, D₀, aX, aY, fr] μ
        (tPre31 c G N D₀) fun _ μ' =>
      Ready31 G X Y aX aY fr μ' ∧ SameOutside μ μ' fr (structEnd G N D₀ fr - fr)

end Light.Sec4
