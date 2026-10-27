/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FromPrinted.SatDefs
import Printed.End
import Printed.Count
import SplitSat.Leaf
import GraphProblems.Engine
import Enumerate.Enumeration
import Exits.Poly
import CountKSat.InOut
import CountKSat.Poly
import WidthK.Top.Poly
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 5: that Theorem 2 gives s_3 = 0, for `Printed.SAT` (lines 1 to 4 of Algorithm 1 in their deciding form) in proof/threesat/Printed/, without its reader

`stCore3Eq`: the machine `Printed.SAT ℓ τ` is the reader `decU 3` of the input followed by
`core3 ℓ τ`; the two sides are the same by definition.
`stCore3`: what Theorem 2 in the form `Printed.stDecides` says of `Printed.SAT ℓ τ` on codes is said
of `core3 ℓ τ` on pairs (N in unary, formula). A formula ψ with variables below N is `Decode.toN φ`
for an instance φ; a run of `Printed.SAT ℓ τ` on the code of φ is a run of `core3 ℓ τ` on what the
reader returns (`GraphProblems.runs_of_mapIn`),
and that is (N in unary, ψ). The code has length below 25·(N+2)^4, so the sizes of the states are
polynomial in N. Nothing about the algorithm is proved anew. Only the certificate of polynomial-time
steps is built again (`core3_polyTimeSteps`), because that of `Printed.stDecides` is for the machine
with the reader in front, and `core3 ℓ τ` has none; it is put together as in
`Suffices.satLoop_polyTimeSteps_of`, from the certificates of Clique(ℓ) (`Printed.stClique`), of the
machine of Lemma 1 (`Printed.stGroupingPoly`) and of Count (`Printed.onFormula_poly`,
`Printed.firstLine_poly`), and holds at every ℓ and τ. -/

public section

section

open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight Eight.ViaGrouping GraphProblems SplitSat

namespace FromPrinted.SplitSat

/-- The machine of Theorem 2 is the reader of the input followed by `core3`: the statement
`FromPrinted.SplitSat.StCore3Eq`. -/
theorem stCore3Eq : StCore3Eq := fun _ _ => rfl

/-- The steps of `core3 ℓ τ` are polynomial time. -/
theorem core3_polyTimeSteps (ℓ τ : ℕ) : PolyTimeSteps (core3 ℓ τ) := by
  obtain ⟨h⟩ : PolyTimeSteps (Printed.COUNT ℓ) :=
    Printed.firstLine_poly (Printed.onFormula_poly _ 3 (Printed.NETWORK ℓ) (Printed.stGroupingPoly _ _ _ (Printed.stClique ℓ).1))
  have hrule : PolyT (Enumerate.rule τ) := Poly.certStepC (thetaU τ) 3
  have hr := CountKSat.Poly.rootC_polyT
  have := IsPolyT.mapOut (M := Printed.COUNT ℓ) posZ_polyT
  have := IsPolyT.mapIn (M := Stepped.mapOut (Printed.COUNT ℓ) posZ) Enumerate.out_polyT
  have := IsPolyT.guard (T := Stepped.mapIn SparsificationLemma.out (Stepped.mapOut (Printed.COUNT ℓ) posZ)) (d := false) (IsPolyT.walkSel_polyT hrule)
  obtain ⟨hw⟩ := Exits.stFoldUntilPoly (List Unit × Fml) Bool Bool (List CNode) (fun a => some [rootC a]) (walkNext (Enumerate.rule τ))
    (Stepped.guard (walkSel (Enumerate.rule τ)) (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut (Printed.COUNT ℓ) posZ)) false)
    (fun c _ b => c || b) id (fun _ => false) (by fun_prop) (IsPolyT.walkNext_polyT hrule) (by fun_prop) PolyT.id' (by fun_prop)
  have : IsPolyT (Exits.walkUntil (Enumerate.rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut (Printed.COUNT ℓ) posZ))) := hw
  have : IsPolyT (Stepped.const false : Stepped (List Unit × Fml) Bool) := IsPolyT.const false
  have hi := IsPolyT.ite (M := (Stepped.const false : Stepped (List Unit × Fml) Bool))
    (N := Exits.walkUntil (Enumerate.rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut (Printed.COUNT ℓ) posZ)))
    (p := fun p => hasNil p.2) (by have := hasNil_polyT; fun_prop)
  exact ⟨hi⟩

/-- If `Printed.SAT ℓ τ` decides 3-SAT on codes within c·2^{δn} steps, then `core3 ℓ τ` decides
3-SAT on pairs (N in unary, formula) with the exponent δ. -/
theorem core3_decides {ℓ τ : ℕ} {δ : ℝ} (h : Paper.DecidesInSteps (Printed.SAT ℓ τ) δ) : ∃ c : ℕ, Decides3 (core3 ℓ τ) δ c := by
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
  have he : decU 3 (Sat3.enc φ) = (List.replicate N (), Decode.toN φ) := stDecU 3 N φ (by omega) h3.1
  rw [he] at hr'
  refine hr'.mono le_rfl ?_
  have hl : (Sat3.enc φ).length + 1 ≤ (3 * 2 ^ 3 + 1) * (N + 2) ^ (3 + 1) := DecodeK.length_enc_succ_le (k := 3) h3
  calc c * ((Sat3.enc φ).length + 1) ^ c ≤ c * ((3 * 2 ^ 3 + 1) * (N + 2) ^ (3 + 1)) ^ c :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl c)
    _ = (c * (3 * 2 ^ 3 + 1) ^ c) * (N + 2) ^ ((3 + 1) * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
    _ ≤ (c * (3 * 2 ^ 3 + 1) ^ c + (3 + 1) * c) * (N + 2) ^ (c * (3 * 2 ^ 3 + 1) ^ c + (3 + 1) * c) :=
        Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))

/-- **Theorem 2 gives s_3 = 0**, for the machine of Theorem 2 in its decision form without its
reader: for every δ > 0 there are ℓ and τ such that `core3 ℓ τ` has polynomial-time steps and
decides 3-SAT with the exponent δ. This is the statement `FromPrinted.SplitSat.StCore3`; ℓ and τ are
those of `Printed.stDecides`. -/
theorem stCore3 : StCore3 := fun _ hδ => by
  obtain ⟨ℓ, τ, -, h⟩ := Printed.stDecides _ hδ
  exact ⟨ℓ, τ, core3_polyTimeSteps ℓ τ, core3_decides h⟩

end FromPrinted.SplitSat

end
