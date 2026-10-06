/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program
public import ThreeSumApsp.Programs.Sec4.Corollary26.Regime

/-!
# Corollary 26: the program

Proof of Corollary 26: "Let L := 21m and t := ⌈m/9⌉. We will apply Theorem 30 with these
parameters". `program26` is the program with rational parameters in its text (`program31`) at 21,
1/9 and the threshold 60 (`ratParams26`). Its preprocessing finds m = ⌈log₄ D⌉ and compares it with
60 (`program26_pre31`).

Only the definition `program26` is used elsewhere. The lemmas of this file show a reader of the
paper what the general program does at the parameters of Corollary 26; nothing rests on them.

* "For m ≥ 60, Theorem 30 thus applies": the preprocessing calls the procedures for L and t, which
  find ⌈21 m / 1⌉ and ⌈1 m / 9⌉ by counting (`program26_levels31`, `program26_switch31`), writes the
  padded matrices, calls the preprocessing of Theorem 30, and stores the base address and the flag
  1; this leaves the data structure of Theorem 30 with L = 21 m and t = ⌈m/9⌉
  (`pre31_program26_above`). A query reads the flag and calls the query of Theorem 30
  (`program26_query31`, `query31_program26_above`).
* "(For m < 60, D is bounded by a constant, and the corollary holds trivially.)": the preprocessing
  stores the flag 0 (`pre31_program26_below`), and a query reads the flag and computes an inner
  product (`program26_query31`, `query31_program26_below`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

/-- **The program of Corollary 26**: the parameters in its text are 21, 1/9 and 60. -/
def program26 : Program := program31 ratParams26

/-! ## The parameters in the text -/

/-- pre31(N, D, aX, aY, fr) in the program of Corollary 26 finds m and 4^m; for m < 60 it stores the
flag 0, for m ≥ 60 it runs preLarge31. -/
theorem program26_pre31 : program26[Proc.pre31]? = some (.call Proc.log4 [v 1, v 4 +' k 2] 5 ;;
      .ite (v 5 <' k 60) (.store (v 4) (k 0)) preLarge31) :=
  program31_at ratParams26 Proc.pre31

/-- "L := 21m": the procedure that preLarge31 calls for L counts up to 21 m in steps of 1. -/
theorem program26_levels31 : program26[Proc.levels31]? = some (ceilMulBody 21 1) :=
  program31_at ratParams26 Proc.levels31

/-- "t := ⌈m/9⌉": the procedure that preLarge31 calls for t counts up to m in steps of 9. -/
theorem program26_switch31 : program26[Proc.switch31]? = some (ceilMulBody 1 9) :=
  program31_at ratParams26 Proc.switch31

/-- query31(I, J, N, D, aX, aY, fr) in the program of Corollary 26 reads the flag: if it is 1, it
calls the query of Theorem 30, and otherwise the inner product. -/
theorem program26_query31 : program26[Proc.query31]? = some
    (.ite (M (v 6) =' k 1) (.call Proc.queryAt [v 0, v 1, M (v 6 +' k 1)] 0)
      (.call Proc.ipAt [v 0, v 1, v 2, v 3, v 4, v 5] 0)) :=
  program31_at ratParams26 Proc.query31

section stages

variable {lim : Limits} {N D₀ aX aY fr : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {U : ℤ} {μ : ℕ → ℤ}

/-! ## From the threshold on -/

/-- The data structure of Theorem 30 with L and t written in another way. -/
private theorem DSReady.of_eq {m L L' t t' b0 : ℕ} {X' : Matrix (Fin N) (Fin (D m)) ℤ}
    {Y' : Matrix (Fin (D m)) (Fin N) ℤ} {hmL : m ≤ L} (hL : L = L') (ht : t = t')
    (h : DSReady ⟨L, m, N⟩ t hmL aX aY b0 X' Y' μ) :
    DSReady ⟨L', m, N⟩ t' (hL ▸ hmL) aX aY b0 X' Y' μ := by
  subst hL ht
  exact h

/-- The cells from fr on hold the flag 1, the base address, and the data structure of Theorem 30
with L = 21 m and t = ⌈m/9⌉ for the padded matrices. -/
structure Built26 (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (fr : ℕ)
    (μ : ℕ → ℤ) : Prop where
  flag : μ fr = 1
  base : μ (fr + 1) = blockAt N D₀ fr
  structure30 : DSReady (par26 N D₀) (switch26 D₀) (Nat.le_mul_of_pos_left _ (by norm_num))
    (paddedXAt fr) (paddedYAt N D₀ fr) (blockAt N D₀ fr) (padInnerCols (D (logFour D₀)) X)
    (padInnerRows (D (logFour D₀)) Y) μ

/-- "For m ≥ 60, Theorem 30 thus applies": the preprocessing leaves the flag 1, the base address,
and the data structure of Theorem 30 with L = 21 m and t = ⌈m/9⌉, which makes the cells ready for
queries, and changes no cell outside the structure. -/
theorem pre31_program26_above (hm : 60 ≤ logFour D₀) (hin : Input31 lim ratParams26 X Y aX aY fr U)
    (hX : MatAt μ aX X) (hY : MatAt μ aY Y) :
    ∀ d, d + (21 * logFour D₀ + 7) ≤ lim.depth →
    Meets lim program26 Proc.pre31 d [N, D₀, aX, aY, fr] μ
      (tPre31 cShared30 ratParams26 N D₀) fun _ μ' =>
        Built26 X Y fr μ' ∧ Ready31 ratParams26 X Y aX aY fr μ' ∧
          SameOutside μ μ' fr (top (par26 N D₀) (switch26 D₀) (blockAt N D₀ fr) - fr) := by
  have hpre := pre31_program31 ratParams26 lim N D₀ aX aY fr X Y U μ hin hX hY
  rw [ratParams26_L] at hpre
  refine fun d hd => (hpre d hd).mono le_rfl ?_
  rintro - μ' ⟨hready, hsame⟩
  obtain ⟨hflag, hbase, hDS⟩ := hready.large hm
  rw [structEnd, ratParams26_m₀, if_neg (not_lt.mpr hm), parOf_ratParams26,
    switchOf31_ratParams26] at hsame
  exact ⟨⟨hflag, hbase, hDS.of_eq (ratParams26_L _) (switchOf31_ratParams26 _)⟩, hready, hsame⟩

/-- For m ≥ 60 a query returns the entry in the time of a query of Theorem 30 with L = 21 m and t =
⌈m/9⌉, keeps the cells ready, and changes only cells of the structure behind its first three. -/
theorem query31_program26_above (hm : 60 ≤ logFour D₀)
    (hin : Input31 lim ratParams26 X Y aX aY fr U) (hready : Ready31 ratParams26 X Y aX aY fr μ)
    (I J : Fin N) :
    ∀ d, d + 3 ≤ lim.depth →
    Meets lim program26 Proc.query31 d [(I : ℕ), (J : ℕ), N, D₀, aX, aY, fr] μ
      (tQueryAt (21 * logFour D₀) (logFour D₀) (switch26 D₀) + 20) fun r μ' =>
        r = (X * Y) I J ∧ Ready31 ratParams26 X Y aX aY fr μ' ∧ SameOutside μ μ' (fr + 3)
          (top (par26 N D₀) (switch26 D₀) (blockAt N D₀ fr) - (fr + 3)) := by
  have hquery := query31_program31 ratParams26 lim N D₀ aX aY fr X Y U μ I J hin hready
  rwa [tQuery31, structEnd, ratParams26_m₀, if_neg (not_lt.mpr hm), if_neg (not_lt.mpr hm),
    ratParams26_L, parOf_ratParams26, switchOf31_ratParams26] at hquery

/-! ## Below the threshold -/

/-- "(For m < 60, D is bounded by a constant, and the corollary holds trivially.)" The preprocessing
takes the time of finding m and 4^m, stores the flag 0, which makes the cells ready for queries, and
changes no cell but the three from fr on. -/
theorem pre31_program26_below (hm : logFour D₀ < 60) (hin : Input31 lim ratParams26 X Y aX aY fr U)
    (hX : MatAt μ aX X) (hY : MatAt μ aY Y) :
    ∀ d, d + (21 * logFour D₀ + 7) ≤ lim.depth →
    Meets lim program26 Proc.pre31 d [N, D₀, aX, aY, fr] μ (tLog4 (logFour D₀) + 30) fun _ μ' =>
        μ' fr = 0 ∧ Ready31 ratParams26 X Y aX aY fr μ' ∧ SameOutside μ μ' fr 3 := by
  have hpre := pre31_program31 ratParams26 lim N D₀ aX aY fr X Y U μ hin hX hY
  rw [ratParams26_L] at hpre
  refine fun d hd => (hpre d hd).mono (by simp [tPre31, ratParams26_m₀, hm]) ?_
  rintro - μ' ⟨hready, hsame⟩
  exact ⟨hready.small hm, hready, by simpa [structEnd, ratParams26_m₀, hm] using hsame⟩

/-- "(For m < 60, D is bounded by a constant, and the corollary holds trivially.)" A query returns
the entry in the time of an inner product of length D, and changes no cell. -/
theorem query31_program26_below (hm : logFour D₀ < 60)
    (hin : Input31 lim ratParams26 X Y aX aY fr U) (hready : Ready31 ratParams26 X Y aX aY fr μ)
    (I J : Fin N) :
    ∀ d, d + 3 ≤ lim.depth →
    Meets lim program26 Proc.query31 d [(I : ℕ), (J : ℕ), N, D₀, aX, aY, fr] μ
      (tIpAt D₀ + 20) fun r μ' => r = (X * Y) I J ∧ μ' = μ := by
  refine fun d hd => (query31_program31 ratParams26 lim N D₀ aX aY fr X Y U μ I J hin hready d
    hd).mono (by simp [tQuery31, ratParams26_m₀, hm]) ?_
  rintro r μ' ⟨hr, -, hsame⟩
  exact ⟨hr, funext fun a => hsame a (by simp [structEnd, ratParams26_m₀, hm]; omega)⟩

end stages

end Light.Sec4
