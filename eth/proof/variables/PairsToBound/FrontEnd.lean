/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PairsToBound.Width
public import VariableBound.Paper.Rename.Defs
import VariableBound.Paper.Rename.Code
import VariableBound.Paper.Rename.Cert
import ClauseBound.Alg.Decode
import ToTuring.Poly.NetFun
import ToTuring.Closure.Basic
import ToTuring.Lib.Bool
import ToTuring.Lib.List1b
import ToTuring.Lib.Unary
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The front end and the test of the algorithm of Step 6

**The sentences answered** (Step 6 of Appendix D). «As in Step 5, k is the largest number of
literals in a clause, or 3 if that is larger». «In the other cases, that is, if n < K₀^17 or this k
exceeds (log n)^(1/4), the algorithm tries all assignments».

**What is proved.** `frontEndAndTestExist : FrontEndAndTestExist`: there is a polynomial-time
function that maps the code of (k, φ) to the code of (`widthOr3 φ`, φ), and for every K₀ there is a
polynomial-time test that is true on the code of (k, φ) exactly if n ≥ K₀^17 and `widthOr3 φ` ≤ (log
n)^(1/4).

**The two programs.** Both read the input with `ClauseBound.Alg.fmlOf`, which returns n in unary and
the list of clauses with natural numbers as variables. `widthN ψ` is the width of Step 6 of such a
list.
* `atWidthOr3 x` writes the formula read from x as a bit string again, by the formula of `SatM.enc`
  (`VariableBound.Rename.encN`), with `widthN` in the place of the width that x declares.
* `inMainRegime K₀ x` compares natural numbers only: K₀^17 ≤ n and 2^(k⁴) ≤ n, for k = `widthN`. For
  natural numbers k ≥ 1 and n, k⁴ ≤ log n holds exactly if 2^(k⁴) ≤ n (`pow_four_le_lg_iff`); for n =
  0 both sides are false, because Mathlib's logarithm of 0 is 0.

**Polynomial time.** The width is at most 3 plus the number of all literals written in the formula,
so it can be written in unary (`widthN_unary`); hence so can its fourth power, and the number 2^(k⁴)
has polynomially many binary digits. -/

public section

namespace PairsToBound

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg MainTheoremForms VariableBound.Rename
open Sat3 (CNF)

/-! ### The two programs -/

/-- The width of Step 6 of a formula with natural numbers as variables: the largest number of
literals in a clause, or 3 if that is larger. -/
@[expose] def widthN (ψ : Fml) : ℕ := (ψ.map List.length).foldr max 3

/-- The front end: the formula written in x, written again with the width of Step 6 as its declared
width. -/
@[expose] def atWidthOr3 (x : List Bool) : List Bool := encN (List.replicate (widthN (fmlOf x).2) ()) (fmlOf x)

/-- The test: K₀^17 ≤ n and 2^(k⁴) ≤ n, for the number n of variables written in x and the width k
of Step 6 of the formula written in x. -/
@[expose] def inMainRegime (K₀ : ℕ) (x : List Bool) : Bool :=
  decide (K₀ ^ 17 ≤ (fmlOf x).1.length) && decide (2 ^ (widthN (fmlOf x).2 ^ 4) ≤ (fmlOf x).1.length)

/-! ### What they compute -/

/-- Writing the variables as natural numbers does not change the width. -/
theorem widthN_toN {n : ℕ} (φ : CNF n) : widthN (Decode.toN φ) = widthOr3 φ := by
  simp [widthN, widthOr3, Decode.toN, Function.comp_def]

/-- For natural numbers k ≥ 1 and n: k⁴ ≤ log n if and only if 2^(k⁴) ≤ n. -/
theorem pow_four_le_lg_iff {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : (k : ℝ) ^ 4 ≤ lg n ↔ 2 ^ (k ^ 4) ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (0 : ℝ) < (k : ℝ) ^ 4 := by
      have : (0 : ℝ) < k := by exact_mod_cast hk
      positivity
    have h1 : 0 < 2 ^ (k ^ 4) := Nat.pos_of_ne_zero (by positivity)
    constructor
    · intro h
      rw [lg, Nat.cast_zero, Real.logb_zero] at h
      linarith
    · intro h
      omega
  · have e : (2 : ℝ) ^ ((k : ℝ) ^ 4) = ((2 ^ (k ^ 4) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, Real.rpow_natCast]
      push_cast
      rfl
    rw [lg, Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hn), e, Nat.cast_le]

/-- The front end maps the code of (k, φ) to the code of (`widthOr3 φ`, φ). -/
theorem atWidthOr3_rewrites : RewritesAtWidthOr3 atWidthOr3 := by
  intro k n φ hk hφ
  obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk hφ.1
  rw [atWidthOr3, hdec, widthN_toN]
  exact encN_toN _ φ

/-- The test is true on the code of (k, φ) if and only if n ≥ K₀^17 and `widthOr3 φ` is at most (log
n)^(1/4). -/
theorem inMainRegime_tests (K₀ : ℕ) : TestsTheMainRegime K₀ (inMainRegime K₀) := by
  intro k n φ hk hφ
  obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk hφ.1
  rw [inMainRegime, hdec, widthN_toN, List.length_replicate, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    pow_four_le_lg_iff (le_trans (by norm_num) (three_le_widthOr3 φ))]

/-! ### Polynomial time -/

variable {α : Type} [Enc α]

/-- The maximum with the start value 3 is the maximum, with the start value 0, of the list with 3
put behind it. -/
theorem widthN_eq (ψ : Fml) : widthN ψ = (ψ.map List.length ++ [3]).foldr max 0 := by
  simp [widthN]

/-- The width is at most 3 plus the number of all literals written in the formula. -/
theorem widthN_le (ψ : Fml) : widthN ψ ≤ (ψ.flatMap fun C => C).length + 3 := by
  induction ψ with
  | nil => simp [widthN]
  | cons C ψ ih =>
    simp only [widthN, List.map_cons, List.foldr_cons, List.flatMap_cons, List.length_append] at ih ⊢
    omega

/-- The width is polynomial-time. -/
theorem widthN_polyT {ψ : α → Fml} (hψ : PolyT ψ) : PolyT fun x => widthN (ψ x) :=
  (NetE.foldr_max_polyT (l := fun x => (ψ x).map List.length ++ [3]) (by fun_prop)).congr fun x => (widthN_eq (ψ x)).symm

/-- The width is polynomial-time even with its value written in unary. -/
theorem widthN_unary {ψ : α → Fml} (hψ : PolyT ψ) : Unary fun x => widthN (ψ x) :=
  Unary.of_le (g := fun x => ((ψ x).flatMap fun C => C).length + 3) ((Unary.of_length (by fun_prop)).add (Unary.const 3)) (widthN_polyT hψ) fun x => widthN_le (ψ x)

/-- The front end is polynomial-time. -/
theorem atWidthOr3_polyT : PolyT atWidthOr3 :=
  encN_polyT (widthN_unary Decode.stCertDecM.2.snd) Decode.stCertDecM.2

/-- Comparing two polynomial-time numbers with a third is polynomial-time. -/
theorem both_le_polyT {a b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) : PolyT fun x => decide (a x ≤ c x) && decide (b x ≤ c x) := by
  fun_prop

/-- The test is polynomial-time. -/
theorem inMainRegime_polyT (K₀ : ℕ) : PolyT (inMainRegime K₀) := by
  have hd : PolyT fmlOf := Decode.stCertDecM.2
  have hw : Unary fun x => widthN (fmlOf x).2 := widthN_unary hd.snd
  have h4 : Unary fun x => widthN (fmlOf x).2 ^ 4 := by
    have h := ((hw.mul hw).mul hw).mul hw
    unfold Unary at h ⊢
    exact h.congr fun x => by congr 1; ring
  have h2 : PolyT fun x => 2 ^ (widthN (fmlOf x).2 ^ 4) := PolyT.two_pow h4
  have hn : PolyT fun x => (fmlOf x).1.length := PolyT.length hd.fst
  exact both_le_polyT (PolyT.const _) h2 hn

/-- For every K₀ there are a polynomial-time front end and a polynomial-time test as in Step 6. -/
theorem frontEndAndTestExist : FrontEndAndTestExist :=
  ⟨⟨atWidthOr3, atWidthOr3_polyT, atWidthOr3_rewrites⟩, fun K₀ => ⟨inMainRegime K₀, inMainRegime_polyT K₀, inMainRegime_tests K₀⟩⟩

end PairsToBound
