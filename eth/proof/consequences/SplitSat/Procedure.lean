/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitSat.Defs
import SplitSat.Leaf
import ThreeSatPrinted.ThmEveryDelta
import GraphProblems.Engine
import WidthK.Top.Poly
import SparsifyWidthK.Poly.Sparsify
import Eight.ViaGrouping.Alg
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 5: «Theorem 2 gives s_3 = 0», for the machine of Theorem 2 in its decision form without its reader

`stCore3Eq`: the machine `ThreeSatPrinted.SATCp ℓ τ` of Theorem 2 is a reader of the input followed
by `core3 ℓ τ`; the two sides are the same by definition.
`stCore3`: what the tied form of Theorem 2 (`ThreeSatPrinted.algPseudocode_decides_viaC`) says of
`SATCp ℓ τ` on codes is said of `core3 ℓ τ` on pairs (N in unary, formula). A formula ψ with
variables below N is `Decode.toN φ` for an instance φ; a run of `SATCp ℓ τ` on the code of φ is a
run of `core3 ℓ τ` on what the reader returns (`GraphProblems.runs_of_mapIn`),
and that is (N in unary, ψ). The code has length below 25·(N+2)^4, so the sizes of the states are
polynomial in N. Nothing about the algorithm is proved anew. Only the certificate of polynomial-time
steps is built again (`core3_polyTimeSteps`), because `ThreeSatPrinted.SATCp_polyTimeSteps` is for
the machine with the reader in front, and `core3 ℓ τ` has none. -/

public section

namespace SplitSat

open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight Eight.ViaGrouping GraphProblems

/-- The machine of Theorem 2 is the reader of the input followed by `core3`: the statement
`SplitSat.StCore3Eq`. -/
theorem stCore3Eq : StCore3Eq := fun _ _ => rfl

/-- The steps of `core3 ℓ τ` are polynomial time. -/
theorem core3_polyTimeSteps (ℓ τ : ℕ) : PolyTimeSteps (core3 ℓ τ) := by
  obtain ⟨h⟩ := COUNTp_polyTimeSteps ℓ
  have := IsPolyT.mapOut (M := COUNTp ℓ) posZ_polyT
  have := IsPolyT.walk (T := Stepped.mapOut (COUNTp ℓ) posZ) (step := stepK (thetaU τ) 3) (root := rootP) (certStep (thetaU τ) 3) (by fun_prop)
  have : IsPolyT (Stepped.const false : Stepped Fml Bool) := IsPolyT.const false
  have := IsPolyT.ite (M := (Stepped.const false : Stepped Fml Bool))
    (N := Stepped.walk (stepK (thetaU τ) 3) rootP (Stepped.mapOut (COUNTp ℓ) posZ)) hasNil_polyT
  exact ⟨IsPolyT.mapIn (f := (Prod.snd : List Unit × Fml → Fml)) (by fun_prop)⟩

/-- If `SATCp ℓ τ` decides 3-SAT on codes within c·2^{δn} steps, then `core3 ℓ τ` decides 3-SAT on
pairs (N in unary, formula) with the exponent δ. -/
theorem core3_decides {ℓ τ : ℕ} {δ : ℝ} (h : Paper.DecidesInSteps (ThreeSatPrinted.SATCp ℓ τ) δ) : ∃ c : ℕ, Decides3 (core3 ℓ τ) δ c := by
  obtain ⟨c, h⟩ := h
  refine ⟨c * (3 * 2 ^ 3 + 1) ^ c + (3 + 1) * c, fun N ψ hψ hnd => ?_⟩
  obtain ⟨φ, h3, rfl⟩ := exists_instance hψ hnd
  obtain ⟨T, b, hr, hb, hT⟩ := h N φ h3
  refine ⟨T, b, ?_, hb.trans (Decode.satN_toN φ).symm, hT.trans ?_⟩
  swap
  · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h1 : 1 ≤ (3 * 2 ^ 3 + 1) ^ c := Nat.one_le_pow _ _ (by omega)
    have h2 : c ≤ c * (3 * 2 ^ 3 + 1) ^ c + (3 + 1) * c := (Nat.le_mul_of_pos_right c h1).trans (Nat.le_add_right _ _)
    exact_mod_cast h2
  rw [stCore3Eq] at hr
  have hr' := runs_of_mapIn hr
  have he : DecodeK.decK 3 (Sat3.enc φ) = (N, Decode.toN φ) := DecodeK.decK_enc (k := 3) (by omega) h3.1
  rw [he] at hr'
  refine hr'.mono le_rfl ?_
  have hl : (Sat3.enc φ).length + 1 ≤ (3 * 2 ^ 3 + 1) * (N + 2) ^ (3 + 1) := DecodeK.length_enc_succ_le (k := 3) h3
  calc c * ((Sat3.enc φ).length + 1) ^ c ≤ c * ((3 * 2 ^ 3 + 1) * (N + 2) ^ (3 + 1)) ^ c :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl c)
    _ = (c * (3 * 2 ^ 3 + 1) ^ c) * (N + 2) ^ ((3 + 1) * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
    _ ≤ (c * (3 * 2 ^ 3 + 1) ^ c + (3 + 1) * c) * (N + 2) ^ (c * (3 * 2 ^ 3 + 1) ^ c + (3 + 1) * c) :=
        Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))

/-- **«Theorem 2 gives s_3 = 0»**, for the machine of Theorem 2 in its decision form without its
reader: for every δ > 0 there are ℓ and τ such that `core3 ℓ τ` has polynomial-time steps and
decides 3-SAT with the exponent δ. This is the statement `SplitSat.StCore3`; ℓ and τ are those of
`ThreeSatPrinted.algPseudocode_decides_viaC`. -/
theorem stCore3 : StCore3 := fun _ hδ => by
  obtain ⟨ℓ, τ, -, -, h⟩ := ThreeSatPrinted.algPseudocode_decides_viaC hδ
  exact ⟨ℓ, τ, core3_polyTimeSteps ℓ τ, core3_decides h⟩

end SplitSat
