/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Instance
public import Mathlib.Data.Nat.Log

/-!
# The regime of Theorem 5

"Let D ≥ 4 be a power of four and N ≥ D^18 … a set W of at most N²/√D positions".  The procedure
regime(N, D, w), where w is the number of positions in W, tests whether the sizes of an instance are
in this regime.  It returns the exponent m with D = 4^m if they are, and 0 if they are not.  With
√D = 2^m, the condition on W reads w 2^m ≤ N².

The program has these parts, each with its own lemma.  regimeExp multiplies by four until D is
reached, which gives the only candidate m = ⌈log₄ D⌉ together with 4^m and 2^m = √D.  regimePow
compares D^18 with N by at most eighteen multiplications, none of which exceeds N D (but for the
first product, which is D).  regimeTests combines the four tests, the last two of which are
regimeSizes.  That the candidate is the only one is RegimeAnswer.zero.
-/

@[expose] public section

namespace Light.Sec2

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The number r is the exponent m of the regime if the sizes are in the regime, and 0 if not. -/
def RegimeAnswer (N D w : ℕ) (r : ℤ) : Prop :=
  (∃ m : ℕ, Regime N D w m ∧ r = m) ∨ (r = 0 ∧ ¬ InRegime N D w)

/-- regime(N, D, w) changes no cell.  It returns m if 1 ≤ m, D = 4^m, D^18 ≤ N and w 2^m ≤ N², and
0 if there is no such m. -/
def RegimeSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (N D w : ℕ) (μ : ℕ → ℤ), ((4 * D + N * D + w * D + N * N + 100 : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P pRegime d [N, D, w] μ (c * (D + 1)) fun r μ' => μ' = μ ∧ RegimeAnswer N D w r

/-! ## The local variables -/

namespace RegimeLocal

/-- The argument N. -/
abbrev Rows : ℕ := 0
/-- The argument D. -/
abbrev Cols : ℕ := 1
/-- The argument w. -/
abbrev Wanted : ℕ := 2
/-- The power 4^m. -/
abbrev PowFour : ℕ := 3
/-- The power 2^m. -/
abbrev PowTwo : ℕ := 4
/-- The exponent m. -/
abbrev Expo : ℕ := 5
/-- The result. -/
abbrev Result : ℕ := 6
/-- A power of D. -/
abbrev Power : ℕ := 7
/-- The exponent of that power. -/
abbrev Count : ℕ := 8
/-- 1 as long as no power of D has exceeded N, then 0. -/
abbrev Fits : ℕ := 9

end RegimeLocal

open RegimeLocal

/-! ## The text -/

/-- The search for the exponent m, with 4^m and 2^m. -/
def regimeExp : Stmt :=
  .while (v PowFour <' v Cols) (
    .set PowFour (v PowFour *' k 4) ;;
    .set PowTwo (v PowTwo *' k 2) ;;
    .set Expo (v Expo +' k 1))

/-- One round of regimePow: if the next power of D exceeds N, give up; if not, go on to it. -/
def regimePowRound : Stmt :=
  .ite (v Rows <' v Power *' v Cols)
    (.set Fits (k 0) ;; .set Count (k 18))
    (.set Power (v Power *' v Cols) ;; .set Count (v Count +' k 1))

/-- The test D^18 ≤ N: the power of D is at most N unless it is D^0. -/
def regimePow : Stmt :=
  .set Power (k 1) ;;
  .set Count (k 0) ;;
  .set Fits (k 1) ;;
  .while (v Count <' k 18) regimePowRound

/-- The last two tests, after regimePow: D^18 ≤ N and w 2^m ≤ N².  If both hold, the result becomes
m. -/
def regimeSizes : Stmt :=
  .ite (v Fits =' k 1)
    (.ite (v Rows *' v Rows <' v Wanted *' v PowTwo) .skip (.set Result (v Expo)))
    .skip

/-- The four tests: 4^m = D, m ≥ 1, D^18 ≤ N and w 2^m ≤ N².  If all hold, the result becomes m. -/
def regimeTests : Stmt :=
  .ite (v PowFour =' v Cols)
    (.ite (k 0 <' v Expo) (regimePow ;; regimeSizes) .skip)
    .skip

/-- regime(N, D, w). -/
def regimeBody : Stmt :=
  .set PowFour (k 1) ;;
  .set PowTwo (k 1) ;;
  .set Expo (k 0) ;;
  regimeExp ;;
  .set Result (k 0) ;;
  regimeTests ;;
  .set Rows (v Result)

/-- The constant of the running time. -/
def cRegime : ℕ := 400

/-! ## What the procedure returns -/

/-- The only candidate for the exponent is ⌈log₄ D⌉: if it fails one of the tests, the sizes are not
in the regime. -/
theorem RegimeAnswer.zero {N D w : ℕ} (h : ¬ Regime N D w (Nat.clog 4 D)) :
    RegimeAnswer N D w 0 := by
  refine Or.inr ⟨rfl, ?_⟩
  rintro ⟨m, reg⟩
  obtain rfl : m = Nat.clog 4 D := by rw [reg.hD, Nat.clog_pow 4 m (by norm_num)]
  exact h reg

/-! ## The exponent -/

/-- regimeExp ends with 4^m, 2^m and m in the locals 3, 4 and 5, for m = ⌈log₄ D⌉. -/
theorem regimeExp_spec (N D w : ℕ) (hword : ((4 * D + 100 : ℕ) : ℤ) ≤ lim.word) (μ : ℕ → ℤ) :
    Ends lim P d regimeExp ⟨frame [(N : ℤ), D, w, 1, 1, 0], μ⟩ (16 * Nat.clog 4 D + 4) fun σ' =>
      σ' = ⟨frame [(N : ℤ), D, w, ((4 ^ Nat.clog 4 D : ℕ) : ℤ), ((2 ^ Nat.clog 4 D : ℕ) : ℤ),
        (Nat.clog 4 D : ℕ)], μ⟩ := by
  push_cast at hword
  -- while p < D: p := 4 p; r := 2 r; m := m + 1.  Before round i: p = 4^i, r = 2^i, m = i.
  refine Ends.whileBlock
    (fun i σ => σ = ⟨frame [(N : ℤ), D, w, ((4 ^ i : ℕ) : ℤ), ((2 ^ i : ℕ) : ℤ), (i : ℕ)], μ⟩)
    (Nat.clog 4 D) (by simp) ?round ?done
  case round =>
    rintro i _ hi rfl
    have hlt : 4 ^ i < D := (Nat.lt_clog_iff_pow_lt (by norm_num)).1 hi
    have hroot : 2 ^ i ≤ 4 ^ i := Nat.pow_le_pow_left (by omega) i
    have hexp : i < 4 ^ i := Nat.lt_pow_self (by norm_num)
    rw [pow_succ 4 i, pow_succ 2 i]
    generalize 4 ^ i = p at *
    generalize 2 ^ i = r at *
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hle := Nat.le_pow_clog (b := 4) (by norm_num) D
    generalize 4 ^ Nat.clog 4 D = p at *
    exact ⟨by light_side, by light_side, rfl⟩

/-! ## The eighteenth power -/

/-- The states of the loop of regimePow.  The memory and the locals below 7 are as at the start.
Either the loop is still counting: local 8 is an exponent j ≤ 18, local 7 is D^j, which is at most N
unless j = 0, and local 9 is 1.  Or it has stopped because a power exceeded N: local 8 is 18 and
local 9 is 0. -/
def PowInv (N D : ℕ) (loc μ : ℕ → ℤ) (σ : State) : Prop :=
  σ.mem = μ ∧ (∀ x < 7, σ.loc x = loc x) ∧
    ((∃ j : ℕ, j ≤ 18 ∧ σ.loc 8 = j ∧ σ.loc 9 = 1 ∧ σ.loc 7 = ((D ^ j : ℕ) : ℤ) ∧
        (j = 0 ∨ D ^ j ≤ N)) ∨
      (σ.loc 8 = 18 ∧ σ.loc 9 = 0 ∧ N < D ^ 18))

/-- A round of regimePow keeps PowInv and brings local 8 closer to 18. -/
theorem regimePowRound_spec {N D : ℕ} (hD : 1 ≤ D)
    (hword : (4 * D + N * D + 100 : ℤ) ≤ lim.word) {μ loc : ℕ → ℤ} (e0 : loc 0 = N)
    (e1 : loc 1 = D) {σ : State} (hinv : PowInv N D loc μ σ) (htest : (v 8 <' k 18).Holds σ) :
    Ends lim P d regimePowRound σ 14 fun σ' =>
      PowInv N D loc μ σ' ∧ 18 - (σ'.loc 8).toNat < 18 - (σ.loc 8).toNat := by
  unfold regimePowRound Rows Cols Power Count Fits
  obtain ⟨loc', μ'⟩ := σ
  obtain ⟨hmem, hkept, hcase⟩ := hinv
  dsimp only at hmem hkept hcase
  subst hmem
  have hN := (hkept 0 (by omega)).trans e0
  have hDloc := (hkept 1 (by omega)).trans e1
  obtain ⟨j, -, hexp, hok, hpow, hle⟩ | ⟨hexp, -, -⟩ := hcase
  swap
  · simp [hexp] at htest
  have hj : j < 18 := by simpa [hexp] using htest
  have hnext : D ^ j * D ≤ 4 * D + N * D := by
    rcases hle with rfl | hle
    · simp
      omega
    · exact (Nat.mul_le_mul_right D hle).trans (Nat.le_add_left _ _)
  have hsucc : D ^ (j + 1) = D ^ j * D := pow_succ D j
  have hmono : D ^ (j + 1) ≤ D ^ 18 := Nat.pow_le_pow_right hD hj
  generalize D ^ j = q at *
  have hnextZ : (q : ℤ) * D ≤ 4 * D + N * D := by exact_mod_cast hnext
  have hq0 : (0 : ℤ) ≤ (q : ℤ) * D := by positivity
  have hsafe : (v 0 <' v 7 *' v 1).Safe lim ⟨loc', μ'⟩ := by
    simp [hpow, hDloc, abs_le, -abs_mul]
    omega
  by_cases hlt : N < q * D
  · -- ok := 0; j := 18
    have hltZ : (N : ℤ) < q * D := by exact_mod_cast hlt
    refine Ends.block (.ite_pos ⟨by simp; omega, ⟨rfl, fun x hx => ?_,
      Or.inr ⟨by simp, by simp, by omega⟩⟩, by simp [hexp]; omega⟩
      (by simp [hN, hpow, hDloc]; omega) hsafe)
    simp only [Stmt.after, Function.update_apply]
    split_ifs <;> first | omega | exact hkept x hx
  · -- q := q D; j := j + 1
    have hgeZ : (q : ℤ) * D ≤ N := by exact_mod_cast not_lt.1 hlt
    refine Ends.block (.ite_neg ⟨by light_side [hpow, hDloc, hexp],
      ⟨rfl, fun x hx => ?_, Or.inl ⟨j + 1, hj, by simp [hexp], by simp [hok],
        by simp [hpow, hDloc, hsucc], Or.inr (by omega)⟩⟩, by simp [hexp]; omega⟩
      (by simp [hN, hpow, hDloc]; omega) hsafe)
    simp only [Stmt.after, Function.update_apply]
    split_ifs <;> first | omega | exact hkept x hx

/-- regimePow leaves the memory and the locals below 7 as they are.  Afterwards local 9 is 1 if
D^18 ≤ N and 0 if not. -/
theorem regimePow_spec (N D : ℕ) (hD : 1 ≤ D)
    (hword : ((4 * D + N * D + 100 : ℕ) : ℤ) ≤ lim.word) (μ : ℕ → ℤ) (loc : ℕ → ℤ)
    (e0 : loc 0 = N) (e1 : loc 1 = D) :
    Ends lim P d regimePow ⟨loc, μ⟩ 334 fun σ' =>
      σ'.mem = μ ∧ (∀ x < 7, σ'.loc x = loc x) ∧
        ((σ'.loc 9 = 1 ∧ D ^ 18 ≤ N) ∨ (σ'.loc 9 = 0 ∧ N < D ^ 18)) := by
  push_cast at hword
  have hND : (0 : ℤ) ≤ (N : ℤ) * D := by positivity
  unfold regimePow Power Count Fits
  -- q := 1; j := 0; ok := 1
  refine Ends.setThen (Ends.setThen (Ends.setThen ?_))
  -- while j < 18: one round
  refine Ends.whileVariant (PowInv N D loc μ) (fun σ => 18 - (σ.loc 8).toNat) 14
    ?start ?safe (fun σ => regimePowRound_spec hD hword e0 e1) ?done (by simp)
  case start =>
    refine ⟨rfl, fun x hx => ?_, Or.inl ⟨0, by omega, by simp, by simp, by simp, Or.inl rfl⟩⟩
    simp only [Function.update_apply]
    split_ifs <;> omega
  case safe =>
    rintro σ -
    light_side
  case done =>
    rintro ⟨loc', μ'⟩ ⟨hmem, hkept, hcase⟩ htest
    dsimp only at hmem hkept hcase
    obtain ⟨j, hj, hexp, hok, -, hle⟩ | ⟨-, hok, hlt⟩ := hcase
    · obtain rfl : j = 18 := by
        have : ¬ j < 18 := by simpa [hexp] using htest
        omega
      exact ⟨hmem, hkept, Or.inl ⟨hok, by omega⟩⟩
    · exact ⟨hmem, hkept, Or.inr ⟨hok, hlt⟩⟩

/-! ## The four tests -/

/-- regimeSizes, started after the first two tests have succeeded and regimePow has run, puts the
answer into local 6. -/
theorem regimeSizes_spec {N D w : ℕ} (hword : (w * D + N * N + 100 : ℤ) ≤ lim.word)
    (hm : 0 < Nat.clog 4 D) (hD : D = 4 ^ Nat.clog 4 D) {loc μ : ℕ → ℤ} (hN : loc 0 = N)
    (hwanted : loc 2 = w) (hroot : loc 4 = ((2 ^ Nat.clog 4 D : ℕ) : ℤ))
    (hexp : loc 5 = (Nat.clog 4 D : ℕ)) (hres : loc 6 = 0)
    (hpow : (loc 9 = 1 ∧ D ^ 18 ≤ N) ∨ (loc 9 = 0 ∧ N < D ^ 18)) :
    Ends lim P d regimeSizes ⟨loc, μ⟩ 14 fun σ' =>
      σ'.mem = μ ∧ RegimeAnswer N D w (σ'.loc 6) := by
  have hwD : (0 : ℤ) ≤ (w : ℤ) * D := by positivity
  have hNN : (0 : ℤ) ≤ (N : ℤ) * N := by positivity
  have hno : ¬ Regime N D w (Nat.clog 4 D) → RegimeAnswer N D w (loc 6) :=
    fun h => hres.symm ▸ .zero h
  have hwr : w * 2 ^ Nat.clog 4 D ≤ w * D := by
    conv_rhs => rw [hD]
    exact Nat.mul_le_mul_left w (Nat.pow_le_pow_left (by omega) _)
  -- if ok = 1
  refine Ends.iteLast (fun hok => ?_) (fun hok => Ends.skip ⟨rfl, hno fun h => ?_⟩)
    (by simp; omega)
  swap
  · obtain ⟨hone, -⟩ | ⟨-, hlt⟩ := hpow
    · exact hok (by simpa using hone)
    · exact absurd h.hN (by omega)
  have hpow18 : D ^ 18 ≤ N := by
    obtain ⟨-, hle⟩ | ⟨hzero, -⟩ := hpow
    · exact hle
    · simp [hzero] at hok
  -- if N N < w r then skip else result := m
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ Nat.clog 4 D = r := ⟨_, rfl⟩
  rw [hr] at hroot hwr
  have hwrZ : (w : ℤ) * r ≤ w * D := by exact_mod_cast hwr
  have hwr0 : (0 : ℤ) ≤ (w : ℤ) * r := by positivity
  refine Ends.iteLast (fun hmany => Ends.skip ⟨rfl, hno fun h => ?_⟩)
    (fun hmany => Ends.setLast ⟨rfl, Or.inl ⟨_, ⟨hm, hD, hpow18, ?_⟩, by simp [hexp]⟩⟩)
    (by light_side [hN, hwanted, hroot])
  · have hlt : (N : ℤ) * N < w * r := by simpa [hN, hwanted, hroot] using hmany
    have hle := h.hw
    rw [hr, pow_two] at hle
    exact absurd hle (not_le.2 (by exact_mod_cast hlt))
  · have hle : ¬ (N : ℤ) * N < w * r := by simpa [hN, hwanted, hroot] using hmany
    rw [hr, pow_two]
    exact_mod_cast not_lt.1 hle

/-- regimeTests, started with 4^m, 2^m and m for m = ⌈log₄ D⌉ in the locals 3 to 5 and with 0 in
local 6, puts the answer into local 6. -/
theorem regimeTests_spec (N D w : ℕ)
    (hword : ((4 * D + N * D + w * D + N * N + 100 : ℕ) : ℤ) ≤ lim.word) (μ : ℕ → ℤ) :
    Ends lim P d regimeTests
      ⟨frame [(N : ℤ), D, w, ((4 ^ Nat.clog 4 D : ℕ) : ℤ), ((2 ^ Nat.clog 4 D : ℕ) : ℤ),
        (Nat.clog 4 D : ℕ), 0], μ⟩ 356
      fun σ' => σ'.mem = μ ∧ RegimeAnswer N D w (σ'.loc 6) := by
  push_cast at hword
  have hND : (0 : ℤ) ≤ (N : ℤ) * D := by positivity
  have hwD : (0 : ℤ) ≤ (w : ℤ) * D := by positivity
  have hNN : (0 : ℤ) ≤ (N : ℤ) * N := by positivity
  -- if p = D
  refine Ends.iteLast (fun hfour => ?_) fun hfour =>
    Ends.skip ⟨rfl, .zero fun reg =>
      hfour (by simpa using congrArg (Nat.cast (R := ℤ)) reg.hD.symm)⟩
  have hD : D = 4 ^ Nat.clog 4 D := by
    have : ((4 ^ Nat.clog 4 D : ℕ) : ℤ) = D := by simpa using hfour
    exact_mod_cast this.symm
  -- if 0 < m
  refine Ends.iteLast (fun hpos => ?_) fun hpos =>
    Ends.skip ⟨rfl, .zero fun reg => hpos (by simpa using Nat.lt_of_succ_le reg.hm)⟩
  have hm : 0 < Nat.clog 4 D := by simpa using hpos
  -- the test D^18 ≤ N
  light_piece (regimePow_spec N D (hD ▸ Nat.pow_pos (by norm_num)) (by push_cast; omega) μ _
    (by simp) (by simp)) with ⟨loc', μ'⟩ ⟨hmem, hkept, hpow⟩
  dsimp only at hmem hkept hpow
  subst hmem
  -- the last two tests
  exact (regimeSizes_spec (by omega) hm hD (by simpa using hkept 0 (by omega))
    (by simpa using hkept 2 (by omega)) (by simpa using hkept 4 (by omega))
    (by simpa using hkept 5 (by omega)) (by simpa using hkept 6 (by omega)) hpow).mono
      (by simp) fun _ h => h

/-! ## The whole procedure -/

/-- **regime** meets its specification. -/
theorem regime_entry (hP : P[pRegime]? = some regimeBody) : RegimeSpec lim P cRegime := by
  unfold cRegime
  intro N D w μ hword d _
  refine .of_body hP ?_
  have hexp : Nat.clog 4 D ≤ D := Nat.clog_le_of_le_pow (Nat.lt_pow_self (by norm_num)).le
  have hword' := hword
  push_cast at hword'
  have hND : (0 : ℤ) ≤ (N : ℤ) * D := by positivity
  have hwD : (0 : ℤ) ≤ (w : ℤ) * D := by positivity
  have hNN : (0 : ℤ) ≤ (N : ℤ) * N := by positivity
  -- p := 1; r := 1; m := 0
  light_set 1
  light_set 1
  light_set 0
  -- the search for the exponent
  refine Ends.next _ ((regimeExp_spec N D w (by push_cast; omega) μ).mono le_rfl ?_)
    (by simp; omega)
  rintro _ rfl
  -- result := 0
  light_set 0
  -- the four tests
  refine Ends.next _ ((regimeTests_spec N D w hword μ).mono le_rfl ?_) (by simp; omega)
  rintro ⟨loc', μ'⟩ ⟨hmem, hanswer⟩
  -- return result
  exact Ends.setLast ⟨hmem, by simpa using hanswer⟩ (by simp) (by simp; omega)

end Light.Sec2
