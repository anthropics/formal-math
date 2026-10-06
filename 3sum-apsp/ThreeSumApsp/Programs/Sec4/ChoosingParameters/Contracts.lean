/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# Corollaries 26 and 31 in the light language: procedure numbers, time functions and interfaces

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D with
zero columns of X and zero rows of Y." Proof of Corollary 31: "We repeat the proof of Corollary 26
with L := ⌈cm⌉ and t := ⌈θm⌉"; "for smaller m the corollary again holds trivially". Here a query
then computes an inner product, which takes a bounded number of steps since D is bounded.

The routines are relocatable: they receive the addresses of X and Y and a free pointer fr. From fr
on they use

    flag (1) | b0 (1) | 4^m (1) | X' (N 4^m) | Y' (4^m N) | the block of Theorem 30 from b0 on

flag = 1 says that the data structure of Theorem 30 has been built for the padded matrices X', Y';
flag = 0 that m is below the threshold m₀ (a constant of the program text) and that queries compute
inner products. Nothing is assumed about the cells from fr on.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace Proc
abbrev copy : ℕ := 58
abbrev fill : ℕ := 59
abbrev log4 : ℕ := 60
abbrev padX : ℕ := 62
abbrev ipAt : ℕ := 63
abbrev pre31 : ℕ := 64
abbrev query31 : ℕ := 65
abbrev preMain31 : ℕ := 66
abbrev queryMain31 : ℕ := 67
abbrev offline32 : ℕ := 68
abbrev offlineMain32 : ℕ := 69
abbrev allInstances26 : ℕ := 70
abbrev regimeTest26 : ℕ := 71
abbrev levels31 : ℕ := 72
abbrev switch31 : ℕ := 73
end Proc

/-! ## Time functions -/

def tCopy (n : ℕ) : ℕ := 16 * n + 6
def tFill (n : ℕ) : ℕ := 13 * n + 6
def tLog4 (m : ℕ) : ℕ := 20 * m + 20
/-- For each row: a copy, a fill, and the arithmetic of the addresses. -/
def tPadX (N D' : ℕ) : ℕ := N * (16 * D' + 80) + 10
def tIpAt (D : ℕ) : ℕ := 40 * D + 20

/-! ## The small routines -/

/-- copy(src, dst, n). -/
def CopySpec (lim : Limits) (P : Program) : Prop :=
  ∀ (src dst n : ℕ) (μ : ℕ → ℤ), src + n ≤ lim.space → dst + n ≤ lim.space → n < lim.space →
      (src + n ≤ dst ∨ dst + n ≤ src) →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.copy d [src, dst, n] μ (tCopy n) fun _ μ' =>
        (∀ i < n, μ' (dst + i) = μ (src + i)) ∧ SameOutside μ μ' dst n

/-- fill(dst, n, x). -/
def FillSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (dst n : ℕ) (x : ℤ) (μ : ℕ → ℤ), dst + n ≤ lim.space → n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.fill d [dst, n, x] μ (tFill n) fun _ μ' =>
        (∀ i < n, μ' (dst + i) = x) ∧ SameOutside μ μ' dst n

/-- log4(D, a) returns m = ⌈log₄ D⌉ and writes 4^m to the cell a. -/
def Log4Spec (lim : Limits) (P : Program) : Prop :=
  ∀ (D₀ a : ℕ) (μ : ℕ → ℤ), a < lim.space → ((4 ^ Nat.clog 4 D₀ : ℕ) : ℤ) ≤ lim.word →
      (Nat.clog 4 D₀ : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.log4 d [D₀, a] μ (tLog4 (Nat.clog 4 D₀)) fun r μ' =>
      r = Nat.clog 4 D₀ ∧ μ' = Function.update μ a ((4 ^ Nat.clog 4 D₀ : ℕ) : ℤ)

/-- padX(N, D, D', aX, aX') writes X, padded with zero columns to D' columns, to aX'. -/
def PadXSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (N D₀ D' aX aX' : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (μ : ℕ → ℤ), D₀ ≤ D' → 1 ≤ D' →
      MatAt μ aX X → aX + N * D₀ ≤ aX' →
    aX' + N * D' < lim.space →
    ∀ d, d + 1 ≤ lim.depth → Meets lim P Proc.padX d [N, D₀, D', aX, aX'] μ (tPadX N D') fun _ μ' =>
      MatAt μ' aX' (padInnerCols D' X) ∧ SameOutside μ μ' aX' (N * D')

/-- ipAt(I, J, N, D, aX, aY) returns (XY)[I, J] as an inner product. -/
def IpAtSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (N D₀ aX aY : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ)
      (μ : ℕ → ℤ) (I J : Fin N),
    1 ≤ D₀ → MatAt μ aX X → MatAt μ aY Y → (∀ i j, |X i j| ≤ U) →
        (∀ i j, |Y i j| ≤ U) → aX + N * D₀ < lim.space →
    aY + D₀ * N < lim.space → (D₀ : ℤ) * (U * U) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.ipAt d [(I : ℕ), (J : ℕ), N, D₀, aX, aY] μ (tIpAt D₀) fun r μ' =>
        r = (X * Y) I J ∧ μ' = μ

/-! ### copy and fill are those of the library -/

theorem copy_ok {lim : Limits} {P : Program} (hP : P[Proc.copy]? = some copyBody)
    (hstd : Std lim) : CopySpec lim P := by
  intro src dst n μ h1 h2 _ h4 d _
  exact copy_meets hP hstd.space_le h1 h2 h4

theorem fill_ok {lim : Limits} {P : Program} (hP : P[Proc.fill]? = some fillBody)
    (hstd : Std lim) : FillSpec lim P := by
  intro dst n x μ h1 _ d _
  refine (fill_meets hP hstd.space_le h1).mono le_rfl fun _ μ' h => ⟨fun i hi => ?_, h.2⟩
  have := h.1 i (by simpa using hi)
  simpa using this

/-! ### ⌈log₄ D⌉ -/

namespace Log4

/-- The locals of log4: the argument D, which the result replaces; the address a; the power of 4;
and its exponent. -/
abbrev Dim : ℕ := 0
@[inherit_doc Dim] abbrev Cell : ℕ := 1
@[inherit_doc Dim] abbrev Power : ℕ := 2
@[inherit_doc Dim] abbrev Exp : ℕ := 3

end Log4

open Log4 in
/-- log4(D, a): multiply by 4 until D is reached; store the power at a and return the exponent. -/
def log4Body : Stmt :=
  .set Power (k 1) ;; .set Exp (k 0) ;;
  .while (v Power <' v Dim) (.set Power (v Power *' k 4) ;; .set Exp (v Exp +' k 1)) ;;
  .store (v Cell) (v Power) ;; .set Dim (v Exp)

theorem log4_meets {lim : Limits} {P : Program} (hP : P[Proc.log4]? = some log4Body)
    (hstd : Std lim) : Log4Spec lim P := by
  intro D₀ a μ ha hw hmw
  refine fun d _ => ⟨log4Body, hP, ?_⟩
  have h100 := hstd.const_le
  obtain ⟨F, hF⟩ : ∃ F, F = 4 ^ Nat.clog 4 D₀ := ⟨_, rfl⟩
  have hge : D₀ ≤ F := hF ▸ Nat.le_pow_clog (by norm_num) D₀
  rw [← hF] at hw ⊢
  unfold log4Body tLog4
  -- pow := 1 ; exp := 0
  light_set 1
  light_set 0
  -- while pow < D: pow := pow * 4 ; exp := exp + 1.  Before round i, pow = 4^i and exp = i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [D₀, a, ((4 ^ i : ℕ) : ℤ), i], μ⟩)
    (Nat.clog 4 D₀) rfl ?round ?done (hT := le_rfl))
  case round =>
    rintro i _ hi rfl
    have hlt := (Nat.lt_clog_iff_pow_lt (by norm_num)).1 hi
    have hpow : 4 ^ i * 4 ≤ F := by
      rw [hF, ← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) hi
    rw [pow_succ]
    generalize 4 ^ i = p at hlt hpow ⊢
    exact ⟨by light_side, by simp; omega, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    rw [← hF]
    refine ⟨by light_side, by simp; omega, ?_⟩
    -- mem[a] := pow ; return exp
    light_store a F
    light_set (Nat.clog 4 D₀ : ℤ)
    exact ⟨rfl, rfl⟩

end Light.Sec4
