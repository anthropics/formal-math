/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-! # Step 3: bounds that do not depend on the formula

The program of Step 4 hands the clique solver one bound for the total U, one for the size P and one
for the number B of bits of the values, for all networks of all lists of checks that are tried.
These bounds
(`UbD`, `PbD`, `BbD`) are the right side of the bound on U displayed in Step 3 of Appendix D, and P =
⌈2P₀⌉ and B = (k + 1)M + 1 of that Step, with the logarithms rounded up and with r̄ ≤ 10n, M ≤ 14n,
s̄ < 32Δ·log(2Δ) and t̄ ≤ log m + 33·log(2Δ) + 1 put in. Proved here:
`stTbMax` (the bound for t̄), `stFit` (a list with the three bounds displayed at the end of Step 2,
on r, on |Λ_j| and on load(E), is fit for an evaluation), `stNPrMax` (the number of profiles),
`stBounds` (the bounds in closed form) and `stSize` (every network of an
admissible profile is within the bounds, the case m ≤ n̄ included). Arithmetic and gluing only: the
bound on U as printed (`StUPrinted`), «The parameters» (`StSized`), the case m ≤ n̄ (`StSmall`), the
bound on gP displayed in «The parameters» (`StP`),
the count of profiles (`StNPr`) and s̄ < 32Δ·log(2Δ) (`ParamIneq`) come in as hypotheses;
proof/variables/VariableBound/Net/Main.lean discharges them. -/

public section

namespace VariableBound.Net.FitL

open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)

/-! ### Logarithms -/

/-- 2Δ ≤ 2^⌈log(2Δ)⌉. -/
theorem two_mul_le (Δ : ℕ) : 2 * Δ ≤ 2 ^ LD Δ := Nat.le_pow_clog (by norm_num) _

/-- ⌈log(2Δ)⌉ ≥ 2 for Δ ≥ 2. -/
theorem two_le_LD {Δ : ℕ} (hΔ : 2 ≤ Δ) : 2 ≤ LD Δ := by
  have h : Nat.clog 2 (2 ^ 2) ≤ Nat.clog 2 (2 * Δ) := Nat.clog_mono_right 2 (by omega)
  rwa [Nat.clog_pow 2 2 (by norm_num)] at h

/-- log x ≤ log y for 0 < x ≤ y. -/
theorem lg_mono {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : lg x ≤ lg y := Real.logb_le_logb_of_le (by norm_num) hx h

/-- log x ≤ ⌈log x⌉ for a natural number x. -/
theorem lg_le_clog (x : ℕ) : lg x ≤ Nat.clog 2 x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [lg]
  · unfold lg
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hx), Real.rpow_natCast]
    exact_mod_cast Nat.le_pow_clog (by norm_num) x

/-- log(2Δ) ≤ ⌈log(2Δ)⌉. -/
theorem lg_two_mul_le (Δ : ℕ) : lg (2 * Δ) ≤ LD Δ := by
  have h := lg_le_clog (2 * Δ)
  push_cast at h
  exact h

/-- ⌈log(96Δ·⌈log(2Δ)⌉)⌉ ≤ 2·⌈log(2Δ)⌉ + 5 for Δ ≥ 2. -/
theorem clog_le {Δ : ℕ} (hΔ : 2 ≤ Δ) : Nat.clog 2 (96 * Δ * LD Δ) ≤ 2 * LD Δ + 5 := by
  refine Nat.clog_le_of_le_pow ?_
  have h1 := two_mul_le Δ
  have hL := two_le_LD hΔ
  generalize LD Δ = L at h1 hL ⊢
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have h2 : Δ ≤ 2 ^ L' := by rw [pow_succ] at h1; omega
  have h3 : L' + 1 ≤ 2 ^ L' := Nat.lt_two_pow_self
  calc 96 * Δ * (L' + 1) ≤ 128 * 2 ^ L' * 2 ^ L' := Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) h2) h3
    _ = 2 ^ (2 * (L' + 1) + 5) := by ring

/-! ### The number n̄ -/

/-- n̄ ≥ 1. -/
theorem nb_pos {n Δ nb : ℕ} (h : AppVariables.IsNb n Δ nb) : 0 < nb := by
  obtain ⟨a, rfl⟩ := h.1
  positivity

/-- n̄ ≤ n/log(2Δ) gives n̄ ≤ n, for Δ ≥ 1. -/
theorem nb_le {n Δ nb : ℕ} (h : AppVariables.IsNb n Δ nb) (hΔ : 1 ≤ Δ) : nb ≤ n :=
  (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 ((Nat.pow_le_pow_left (by omega : 2 ≤ 2 * Δ) nb).trans h.2.1)

/-- n/(2·log(2Δ)) < n̄ gives n < 2n̄·⌈log(2Δ)⌉. -/
theorem n_lt {n Δ nb : ℕ} (h : AppVariables.IsNb n Δ nb) : n < LD Δ * (2 * nb) := by
  refine (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (h.2.2.trans_le ?_)
  rw [pow_mul 2]
  exact Nat.pow_le_pow_left (two_mul_le Δ) _

/-- A check of at most s̄ = 16m/n̄ clauses, with m ≤ Δn and n̄ as in «Setting and parameters» of
Appendix D, has at most 32Δ·⌈log(2Δ)⌉ clauses. -/
theorem row_le {n Δ nb m l : ℕ} (h : AppVariables.IsNb n Δ nb) (hm : m ≤ Δ * n) (hl : nb * l ≤ 16 * m) : l ≤ sbMax Δ := by
  refine Nat.le_of_mul_le_mul_left ?_ (nb_pos h)
  unfold sbMax
  calc nb * l ≤ 16 * (Δ * n) := hl.trans (Nat.mul_le_mul_left _ hm)
    _ ≤ 16 * (Δ * (LD Δ * (2 * nb))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (n_lt h).le)
    _ = nb * (32 * Δ * LD Δ) := by ring

/-! ### The statements -/

/-- «Setting and parameters»: t̄ ≤ log m + 33·log(2Δ) + 1 gives t̄ ≤ ⌈log(Δn)⌉ + 33·⌈log(2Δ)⌉ + 1,
for 1 ≤ m ≤ Δn. -/
theorem stTbMax : StTbMax := by
  intro n Δ m tb hm hmΔ h
  have h1 : lg m ≤ Nat.clog 2 (Δ * n) := (lg_mono (by exact_mod_cast hm) (by exact_mod_cast hmΔ)).trans (lg_le_clog (Δ * n))
  have h2 := lg_two_mul_le Δ
  have h3 : (tb : ℝ) ≤ ((tbMax n Δ : ℕ) : ℝ) := by
    unfold tbMax
    push_cast
    linarith
  exact_mod_cast h3

/-- For a formula ψ with clauses of 1 to k literals on variables below n, every variable in at most
Δ ≥ 2 clauses, m ≤ Δn, n̄ as in «Setting and parameters» of Appendix D and M ≤ 14n: if m > n̄, a
list with the three bounds displayed at the end of Step 2, for
r̄ ≤ 10n, r̄ ≤ M, 1 ≤ M and t̄ ≤ `tbMax` is fit for an evaluation; if m ≤ n̄, the empty list is. -/
theorem stFit : StFit := by
  intro k n Δ nb rb tb M ψ L hW hΔ hocc hm hnb hM
  refine ⟨fun hlt hS hrb hrM h1 htb => ?_, fun hle => ?_⟩
  · obtain ⟨hl, hrow, hcol⟩ := hS
    exact
      { wf := ⟨hW, fun l hl' => ⟨(hrow l hl').1.imp fun h => ne_of_lt h, (hrow l hl').2.1⟩⟩
        two := hΔ
        occ_le := hocc
        m_le := hm
        isNb := hnb
        M_le := hM
        r_le := hl.trans hrb
        col := fun e he => (hcol e he).trans (by omega)
        big := fun _ => ⟨hl.trans hrM, h1, fun l hl' => (hrow l hl').2.2⟩
        small := fun h => absurd h (Nat.not_le.2 hlt) }
  · exact
      { wf := ⟨hW, fun l hl' => absurd hl' List.not_mem_nil⟩
        two := hΔ
        occ_le := hocc
        m_le := hm
        isNb := hnb
        M_le := hM
        r_le := Nat.zero_le _
        col := fun e _ => Nat.zero_le _
        big := fun h => absurd hle (Nat.not_le.2 h)
        small := fun _ => rfl }

/-- Every check of a list that is fit for an evaluation has at most 32Δ·⌈log(2Δ)⌉ clauses. -/
theorem Fit.row_le {k n Δ nb M : ℕ} {D : Dat} (hF : Fit k n Δ nb M D) : ∀ L ∈ D.2, L.length ≤ sbMax Δ := by
  intro L hL
  rcases Nat.lt_or_ge nb D.1.length with hlt | hle
  · exact FitL.row_le hF.isNb hF.m_le ((hF.big hlt).2.2 L hL)
  · rw [hF.small hle] at hL
    exact absurd hL List.not_mem_nil

/-- Step 3, «Profiles»: for a list that is fit for an evaluation, the number of numbers that are
tried as profiles is at most `nPrMax`, which does not depend on the formula. Uses I ≤ r·s (`StNPr`). -/
theorem stNPrMax (h : StNPr) : StNPrMax := by
  intro k K n Δ nb M D hF
  have h1 := (h (3 * K ^ 8) D (sbMax Δ) (Fit.row_le hF)).1
  unfold nPr nPrMax nProf objMax
  exact Nat.pow_le_pow_left (Nat.succ_le_succ (h1.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hF.r_le) hF.m_le))) _

/-- The bounds in closed form, for n ≥ 1 and Δ ≥ 2: the bounds on U and gP displayed in Step 3 of
Appendix D with the logarithms rounded up, U ≤ 140kn·⌈log(2Δ)⌉ + 2g² and gP ≤ 2(n + g)(1 + Δ(t̄ + 3)) +
2(10n + g)·s̄ + g, on g = 3K⁸ nodes, with the
bounds `tbMax` and `sbMax` for t̄ and s̄. Uses the displayed bound on gP (`StP`). -/
theorem stBounds (h : StP) : StBounds := by
  intro k K n Δ hn hΔ
  constructor
  · unfold UbD
    have hc := clog_le hΔ
    have hL := two_le_LD hΔ
    generalize Nat.clog 2 (96 * Δ * LD Δ) = c at hc ⊢
    generalize LD Δ = L at hc hL ⊢
    refine Nat.add_le_add_right ?_ _
    have h1 : n * c ≤ n * (2 * L + 5) := Nat.mul_le_mul_left _ hc
    have e1 : n * (2 * L + 5) = 2 * (n * L) + 5 * n := by ring
    have h2 : n * 2 ≤ n * L := Nat.mul_le_mul_left _ hL
    have h3 : L ≤ n * L := Nat.le_mul_of_pos_left _ hn
    have h4 : 6 * (n + L) + 28 * (n * c) ≤ 140 * (n * L) := by omega
    calc 6 * k * (n + L) + 28 * k * n * c = k * (6 * (n + L) + 28 * (n * c)) := by ring
      _ ≤ k * (140 * (n * L)) := Nat.mul_le_mul_left _ h4
      _ = 140 * k * n * L := by ring
  · rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · have h1 := h (3 * K ^ 8) n Δ (tbMax n Δ) (10 * n) (sbMax Δ : ℚ) (by positivity) (by positivity) le_rfl
      unfold PbD
      exact_mod_cast h1

/-- A network of size P with values of at most B bits is one of every larger size, with values of
any larger number of bits. -/
theorem sized_mono {J σ τ : Type} [Fintype J] [LinearOrder J] {N : Network J σ τ} {P P' B B' : ℕ} (h : N.Sized P B) (hP : P ≤ P') (hB : B ≤ B') : N.Sized P' B' where
  card_S a := (h.card_S a).trans (Nat.pow_le_pow_right (by norm_num) hP)
  c_symm := h.c_symm
  sum_c a := (h.sum_c a).trans hP
  card_lab := h.card_lab
  abs_W a z := (h.abs_W a z).trans (pow_le_pow_right₀ (by norm_num) hB)
  abs_f a b z θ := (h.abs_f a b z θ).trans (pow_le_pow_right₀ (by norm_num) hB)
  abs_Ψ a b z z' hab := (h.abs_Ψ a b z z' hab).trans (pow_le_pow_right₀ (by norm_num) hB)

/-- The right side of the bound on U displayed in Step 3 of Appendix D, on g = 3K⁸ nodes, is at most
`UbD`, for Δ ≥ 2. -/
theorem ub_real (k K n : ℕ) {Δ : ℕ} (hΔ : 2 ≤ Δ) :
    6 * (k : ℝ) * (n + lg (2 * Δ)) + 28 * k * n * lg (96 * Δ * lg (2 * Δ)) + 2 * ((3 * K ^ 8 : ℕ) : ℝ) ^ 2 ≤ ((UbD k K n Δ : ℕ) : ℝ) := by
  have hΔ' : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have h1 := lg_two_mul_le Δ
  have h0 : 0 < lg (2 * Δ) := Real.logb_pos (by norm_num) (by linarith)
  have h2 : lg (96 * Δ * lg (2 * Δ)) ≤ Nat.clog 2 (96 * Δ * LD Δ) := by
    refine le_trans (lg_mono (by positivity) ?_) (lg_le_clog _)
    push_cast
    gcongr
  unfold UbD
  push_cast
  gcongr

/-- On g = 3K⁸ nodes, P = 2⌈n/g⌉(1 + Δ), the size for m ≤ n̄, is at most `PbD`. -/
theorem small_le_PbD (K n Δ : ℕ) : 2 * (qv (3 * K ^ 8) n * (1 + Δ)) ≤ PbD K n Δ := by
  unfold PbD PD
  have h : ((2 * (qv (3 * K ^ 8) n * (1 + Δ)) : ℕ) : ℚ) ≤ 2 * P0 (3 * K ^ 8) n Δ (tbMax n Δ) (10 * n) (sbMax Δ) := by
    unfold P0
    push_cast
    have a : (Δ : ℚ) ≤ Δ * (tbMax n Δ + 3) := le_mul_of_one_le_right (by positivity) (by linarith [(Nat.cast_nonneg (tbMax n Δ) : (0 : ℚ) ≤ _)])
    have b : (0 : ℚ) ≤ (qv (3 * K ^ 8) (10 * n) : ℚ) * sbMax Δ := by positivity
    have c : (qv (3 * K ^ 8) n : ℚ) * (1 + Δ) ≤ (qv (3 * K ^ 8) n : ℚ) * (1 + Δ * (tbMax n Δ + 3)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  exact Nat.cast_le.1 (h.trans (Nat.le_ceil _))

/-- Step 3, «The total» and «The parameters», with bounds that do not depend on the formula: on g =
3K⁸ nodes, K > 0, for a list that is fit for an evaluation, the network of an admissible profile has
size `PbD`,
values of at most `BbD` bits and total at most `UbD`. For m > n̄ by the bound on U of Step 3 as
printed (`StUPrinted`), by «The parameters» (`StSized`) and by s̄ < 32Δ·log(2Δ) (`ParamIneq`); for m
≤ n̄ by the last sentence
of Step 3 (`StSmall`). -/
theorem stSize (hp : VariableBound.ParamIneq) (hU : StUPrinted) (hS : StSized) (hs : StSmall) : StSize := by
  intro k K n Δ nb M D fl y hK hF hy
  have hg : 0 < 3 * K ^ 8 := by positivity
  rcases Nat.lt_or_ge nb D.1.length with hlt | hle
  · obtain ⟨hr, h1, hrow⟩ := hF.big hlt
    constructor
    · have hsb : ∀ L ∈ D.2, (L.length : ℚ) ≤ (sbMax Δ : ℚ) := by
        intro L hL
        have hnb : (0 : ℝ) < nb := by exact_mod_cast nb_pos hF.isNb
        have a : (L.length : ℝ) ≤ 16 * (D.1.length : ℝ) / nb := by
          rw [le_div_iff₀ hnb, mul_comm]
          exact_mod_cast hrow L hL
        have b := (hp.sb_lt n Δ D.1.length nb hF.two hF.m_le hF.isNb).2
        have c : 32 * (Δ : ℝ) * lg (2 * Δ) ≤ 32 * Δ * LD Δ := by
          have := lg_two_mul_le Δ
          gcongr
        have d : (L.length : ℝ) ≤ ((sbMax Δ : ℕ) : ℝ) := by
          unfold sbMax
          push_cast
          linarith
        exact_mod_cast d
      refine sized_mono (hS k (3 * K ^ 8) n Δ nb M (tbMax n Δ) (10 * n) (sbMax Δ : ℚ) D fl y hg (Nat.cast_nonneg _) hF.wf hF.occ_le hF.r_le hsb hF.col hy) le_rfl ?_
      unfold BbD BD
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hF.M_le) _
    · have h2 := (hU k (3 * K ^ 8) n Δ nb M D fl y hg ⟨hF.wf, hF.two, hF.occ_le, hF.m_le, hF.isNb, hlt, hr, h1, hrow⟩ hF.M_le hy).trans (ub_real k K n hF.two)
      exact_mod_cast h2
  · obtain ⟨ψ, Lam⟩ := D
    obtain rfl : Lam = [] := hF.small hle
    obtain ⟨h1, h2⟩ := hs k (3 * K ^ 8) n Δ nb M ψ fl y hg hF.wf hF.occ_le hle hy
    refine ⟨sized_mono h1 (small_le_PbD K n Δ) (by unfold BbD BD; omega), h2.trans ?_⟩
    have hnb : nb ≤ n := nb_le hF.isNb (by have := hF.two; omega)
    unfold UbD
    have e : 6 * k * (n + LD Δ) = 6 * (k * n) + 6 * (k * LD Δ) := by ring
    have h3 : 2 * (k - 1) * nb ≤ 2 * k * n := Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le k 1)) hnb
    have e2 : 2 * k * n = 2 * (k * n) := by ring
    omega

end VariableBound.Net.FitL
