/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Enumerate.Defs
import Enumerate.Enumeration
import SparsificationLemma.Mach.Full
import SparsificationLemma.Mach.LemSparsification
import SparsificationLemma.Mach.Len
import SparsificationLemma.Mach.Main
import all UniformInK.Top.Leaves
import UniformInK.Top.Budget
import WidthK.Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Lemma 4 as worded, with the list named: proofs

Lemma 4 (cited): for every ε > 0 there is a constant M(ε) ≥ 1 such that for every 3-CNF φ on n
variables one can compute, in time 2^{εn} times a polynomial in n, at most 2^{εn} 3-CNFs on the same
variables, each with at most M(ε)·n clauses, such that φ is satisfiable if and only if at least one
of them is (the paper's Lemma 4 states more: every satisfying assignment of φ satisfies exactly one
of them). Line 2 of Algorithm 1: «for each Φ in the list that Lemma 4 computes from φ and ε do».
This file proves `StNamedOf`, `StNamed` and `StNamedGives` of proof/threesat/Enumerate/Defs.lean.
Below, the walk with parameter τ is the sparsification procedure of this development run on φ with
the parameter τ, and `produced τ n φ` is the list of the formulas that it produces, in its order.
`import all UniformInK.Top.Leaves`: the lemma `UniformInK.Leaves.tauOf_worksU` (τ = 2^(4s+17) is
large enough for ε = 1/2^s) is not public in that module.
`stNamedOf` follows proof/sparsification/SparsificationLemma/Mach/Full.lean and
Mach/LemSparsification.lean, but keeps the list named. The machine and its constant C₀ are those of
`SparsificationLemma.Mach.Prints`. Given ε > 0 take a rational q with 0 < q < min(ε, 1) and the
precision s = `precE (C₀ + 1) 3 q`, so that s ≥ `s0U 3` and (C₀ + 1)/ε ≤ (C₀ + 1)/q ≤ 2^s.
* The parameter τ = `tauOf s` = 2^(4s+17) is large enough for ε: τ ≥ 24, and (3/τ)·log₂(e·τ·τ⁶) ≤
  1/2^s ≤ ε (`enumerates_tauOf`). So the hypothesis `StEnumeratesTau` gives `Enumerates ε (τ⁶) τ`;
  M(ε) = τ⁶.
* The machine prints the code of `outTau 3 n τ φ`, which by the hypothesis `StProducedIsList` is the
  list that the walk produces.
* The time: C₀·(length of the input + 8)^C₀ ≤ c·(n+1)^c with c = C₀·(s+412)^C₀ + 4C₀, and C₀·⌊n/2^s⌋
  ≤ εn (`time_le_poly`).
`stNamedGives` unpacks: the list of the worded lemma `SparsificationLemma.Mach.LemSparsification` is
the list that the walk produces, and what the lemma says of it are the fields `few`, `sparse` and
`sat` of `Enumerates`. -/

public section

namespace Enumerate

open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo SparsificationLemma.Mach Turing

/-- The parameter τ = 2^(4s+17) is large enough for ε as soon as s ≥ `s0U 3` and C/ε ≤ 2^s for some
C ≥ 1; so, by the enumeration for every parameter that is large enough, the walk with this parameter
is an enumeration for ε with M(ε) = τ⁶. (Lemma 4: «For every ε > 0 there is a constant M(ε) ≥ 1 such
that …».) -/
theorem enumerates_tauOf (hE : StEnumeratesTau) {ε : ℝ} {C s : ℕ} (h0 : 0 < ε) (hC : 1 ≤ C) (hs0 : s0U 3 ≤ s) (hs : (C : ℝ) / ε ≤ (2 : ℝ) ^ s) :
    Enumerates ε (tauOf s ^ 6) (tauOf s) := by
  have hτ : 8 * 3 ≤ tauOf s := ((stParU 3 s (by norm_num)).2 hs0).2
  have hw := Leaves.tauOf_worksU (k := 3) (s := s) (by norm_num) hs0
  rw [Nat.cast_ofNat] at hw
  have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have h2 : (C : ℝ) ≤ (2 : ℝ) ^ s * ε := (div_le_iff₀ h0).1 hs
  have h3 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have h4 : (1 : ℝ) / 2 ^ s ≤ ε := by
    rw [div_le_iff₀ hp]
    linarith
  exact hE (tauOf s) ε (by omega) (hw.trans h4)

/-- «in time 2^{εn} times a polynomial in n»: the bound C₀·(length of the input + 8)^C₀·2^(C₀·⌊n/2^s⌋)
of the machine is at most 2^{εn}·c(n+1)^c with c = C₀·(s+412)^C₀ + 4C₀, if C₀ ≤ C and C/ε ≤ 2^s. -/
theorem time_le_poly {C₀ C n s : ℕ} {φ : Sat3.CNF n} {ε : ℝ} (h3 : SatK.IsKCNF 3 φ) (hc : C₀ ≤ C) (h0 : 0 < ε) (hs : (C : ℝ) / ε ≤ (2 : ℝ) ^ s) :
    ((C₀ * ((encIn s 3 φ).length + 2 ^ 3) ^ C₀ * 2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ (ε * (n : ℝ)) * (((C₀ * (s + 412) ^ C₀ + 4 * C₀ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (C₀ * (s + 412) ^ C₀ + 4 * C₀)) := by
  have hR : ((C₀ * ((encIn s 3 φ).length + 2 ^ 3) ^ C₀ : ℕ) : ℝ) ≤ ((C₀ * (s + 412) ^ C₀ + 4 * C₀ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (C₀ * (s + 412) ^ C₀ + 4 * C₀) := by
    exact_mod_cast poly_le C₀ s h3
  have e1 : ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := by
    calc ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) = (2 : ℝ) ^ (((C₀ * (n / 2 ^ s) : ℕ)) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_div_le_eps hc h0 hs)
  calc ((C₀ * ((encIn s 3 φ).length + 2 ^ 3) ^ C₀ * 2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ)
      = ((C₀ * ((encIn s 3 φ).length + 2 ^ 3) ^ C₀ : ℕ) : ℝ) * ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) := Nat.cast_mul _ _
    _ ≤ (((C₀ * (s + 412) ^ C₀ + 4 * C₀ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (C₀ * (s + 412) ^ C₀ + 4 * C₀)) * (2 : ℝ) ^ (ε * (n : ℝ)) :=
        mul_le_mul hR e1 (by positivity) (by positivity)
    _ = _ := mul_comm _ _

/-- **Lemma 4 as worded, with the list named, from its three parts**: the machine that prints the
list, «what the walk produces is that list», and the enumeration for every parameter that is large
enough: for every ε > 0 a constant M(ε) ≥ 1 and, for every 3-CNF φ on n variables, at most 2^{εn}
3-CNFs on the same variables, computed in time 2^{εn} times a polynomial in n, … -/
theorem stNamedOf : StNamedOf := by
  intro hP hL hE
  obtain ⟨M, C₀, hfin, hM⟩ := hP
  refine ⟨M, hfin, fun ε hε => ?_⟩
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (lt_min hε one_pos)
  have hqε : (q : ℝ) ≤ ε := (hq1.trans_le (min_le_left _ _)).le
  have hs0 : s0U 3 ≤ precE (C₀ + 1) 3 q := le_max_left _ _
  have hsq := div_le_two_pow_precE (C₀ + 1) 3 q
  generalize precE (C₀ + 1) 3 q = s at hs0 hsq
  have hs : ((C₀ + 1 : ℕ) : ℝ) / ε ≤ (2 : ℝ) ^ s :=
    (div_le_iff₀ hε).2 (((div_le_iff₀ hq0).1 hsq).trans (mul_le_mul_of_nonneg_left hqε (by positivity)))
  have hτ : 8 * 3 ≤ tauOf s := ((stParU 3 s (by norm_num)).2 hs0).2
  refine ⟨tauOf s ^ 6, s, C₀ * (s + 412) ^ C₀ + 4 * C₀, Nat.one_le_pow _ _ (by omega), enumerates_tauOf hE hε (by omega) hs0 hs, fun n φ h3 hne => ?_⟩
  have h3' : SatK.IsKCNF 3 φ := ⟨h3.1, h3.2⟩
  refine ⟨C₀ * ((encIn s 3 φ).length + 2 ^ 3) ^ C₀ * 2 ^ (C₀ * (n / 2 ^ s)), ?_, time_le_poly h3' (by omega) hε hs⟩
  rw [hL]
  exact hM 3 n s φ (by norm_num) hs0 h3' hne

/-- **Lemma 4 as worded, with the list named.** One machine of Mathlib for all ε; for every ε > 0 it
prints, «in time 2^{εn} times a polynomial in n», the code of the list of the formulas which the
walk with the parameter 2^(4s+17), s = s(ε), produces, in that order; and that walk is an
enumeration for ε and M(ε). -/
theorem stNamed : StNamed := stNamedOf prints stProducedIsList stEnumeratesTau

/-- The form with the list named gives the lemma as worded, in its deciding form (at most 2^{εn}
3-CNFs on the same variables, computed in time 2^{εn} times a polynomial in n, each with at most
M(ε)·n clauses, such that φ is satisfiable if and only if at least one of them is), and the
enumeration. -/
theorem stNamedGives : StNamedGives := by
  rintro ⟨M, hfin, h⟩
  refine ⟨⟨M, hfin, fun ε hε => ?_⟩, fun ε hε => ?_⟩
  · obtain ⟨Mε, s, c, h1, hE, hrun⟩ := h ε hε
    refine ⟨Mε, s, c, h1, fun n φ h3 hne => ?_⟩
    obtain ⟨T, hT, hTle⟩ := hrun n φ h3 hne
    have hk : IsKCNF 3 n (Decode.toN φ) := isKCNF_toN h3.1 hne
    refine ⟨produced (tauOf s) n (Decode.toN φ), T, hT, hTle, hE.few n _ hk, hE.sparse n _ hk, ?_⟩
    rw [← Decode.satN_toN]
    exact hE.sat n _ hk
  · obtain ⟨Mε, s, -, h1, hE, -⟩ := h ε hε
    exact ⟨Mε, tauOf s, h1, hE⟩

end Enumerate
