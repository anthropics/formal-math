/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Suffices.Sizes
public import Exits.Runs
import CountKSat.InOut
import CountKSat.Poly

/-! # The run of lines 1 to 4 of Algorithm 1

«for each Φ in the list that Lemma 4 computes from φ and ε do», with the test "Count(Φ) > 0" in
place of the paper's sum of counts, stopping at the first Φ that passes (the deciding form of
Algorithm 1, lines 2 to 4).
`stLoopRunsOf` takes the run of the walk that halts at the first leaf that passes
(`Exits.StWalkUntil`) as its hypothesis and applies it to the tree of an enumeration: the rule is
`Enumerate.rule τ`, the depth `Enumerate.depth τ n`, and the test of a leaf is Mc on the output ψ ∪
𝒩 of the leaf. The formulas tested are the outputs of the leaves tested (`tested_map`); the size of
the stack comes from the field `stack` of the enumeration.
`satLoop_polyTimeSteps_of` takes the polynomial-time steps of the loop that can be left
(`Exits.StFoldUntilPoly`) as its hypothesis; the moves of the walk and the passage from a leaf to
its output are polynomial-time by the fields `rule_poly` and `out_poly`. -/

public section

namespace Suffices

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
open Groundwork.Sparsify (leaves)

/-- What is read from the code of a 3-CNF without an empty clause is a 3-CNF in the sense of
`SparsificationLemma.IsKCNF` (nonempty clauses of at most 3 literals on variables below n). (The
case k = 3 of `SparsificationLemma.Mach.isKCNF_toN`, proved here so that this file need not import
the files on the Turing machine of Lemma 4.) -/
theorem isKCNF_toN {n : ℕ} {φ : Sat3.CNF n} (h3 : Sat3.Is3CNF φ) (hnil : [] ∉ φ) : IsKCNF 3 n (Decode.toN φ) := by
  intro D hD
  obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN hD
  refine ⟨?_, hl ▸ h3.1 C hC, h⟩
  rintro rfl
  exact hnil ((Decode.nil_mem_toN φ).1 hD)

/-- The number of variables and the number of clauses are at most N, the length of the code plus 1. -/
theorem le_length_enc {n : ℕ} (φ : Sat3.CNF n) : n ≤ (Sat3.enc φ).length + 1 ∧ φ.length ≤ (Sat3.enc φ).length + 1 := by
  have hlen := Decode.length_enc φ
  have := Nat.le_mul_of_pos_right φ.length (show 0 < 3 * (Nat.log2 (2 * n) + 1) by omega)
  omega

/-- **The run of lines 1 to 4 of Algorithm 1**, from the walk that halts at the first leaf that
passes: «for each Φ in the list that Lemma 4 computes from φ and ε do» (line 2), the test Count(Φ) >
0 in place of the paper's line 3, which counts. -/
theorem stLoopRunsOf : StLoopRunsOf := by
  intro HW ε M τ hE
  refine ⟨143 * (UniformInK.bsumU τ 3 + 1) + 5, fun Mc n φ h3 hnil v t Sm hMc => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, N = (Sat3.enc φ).length + 1 := ⟨_, rfl⟩
  obtain ⟨hn, hm⟩ := le_length_enc φ
  rw [← hN] at hn hm ⊢
  have h1 : 1 ≤ N := by omega
  have hk := isKCNF_toN h3 hnil
  have hdec : decU 3 (Sat3.enc φ) = (List.replicate n (), Decode.toN φ) := stDecU 3 n φ (by norm_num) h3.1
  have hψl : (Decode.toN φ).length ≤ N := by rw [Decode.length_toN]; exact hm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fml, ψ = Decode.toN φ := ⟨_, rfl⟩
  rw [← hψ] at hMc hk hdec hψl ⊢
  have hnilψ : hasNil ψ = false := by
    rw [hasNil, List.any_eq_false]
    intro C hC
    simpa using (hk C hC).1
  -- the formulas tested are the outputs of the leaves tested
  have el : (tested (fun x => posZ (v (SparsificationLemma.out x))) (leaves (rule τ) (depth τ n) (rootC (List.replicate n (), ψ)))).length = (tested (fun Φ => posZ (v Φ)) (produced τ n ψ)).length := by
    unfold produced start
    rw [tested_map, List.length_map]
  have ea : (leaves (rule τ) (depth τ n) (rootC (List.replicate n (), ψ))).any (fun x => posZ (v (SparsificationLemma.out x))) = (produced τ n ψ).any fun Φ => posZ (v Φ) :=
    (List.any_map (f := SparsificationLemma.out) (p := fun Φ => posZ (v Φ))).symm
  have hT : ∀ x ∈ tested (fun x => posZ (v (SparsificationLemma.out x))) (leaves (rule τ) (depth τ n) (rootC (List.replicate n (), ψ))),
      (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ)).Runs x t Sm (posZ (v (SparsificationLemma.out x))) := by
    intro x hx
    refine Stepped.mapIn_runs (Stepped.mapOut_runs (hMc (SparsificationLemma.out x) ?_))
    unfold produced start
    rw [tested_map]
    exact List.mem_map_of_mem hx
  -- the stack
  have hS : ∀ i, size ((Sparsify.round (rule τ))^[i] ([rootC (List.replicate n (), ψ)], [])).1 ≤ (143 * (UniformInK.bsumU τ 3 + 1) + 1) * N ^ 3 := by
    intro i
    obtain ⟨s1, s2⟩ := hE.stack n ψ hk i
    exact size_stack_le s1 (fun x hx => size_node_le (s2 x hx).1 (s2 x hx).2.1 (s2 x hx).2.2.1 (s2 x hx).2.2.2 hψl hn h1) hn h1
  have w := HW (List Unit × Fml) CNode (rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ)) (depth τ n) (List.replicate n (), ψ) (hE.stops n ψ hk)
    (fun x => posZ (v (SparsificationLemma.out x))) t Sm ((143 * (UniformInK.bsumU τ 3 + 1) + 1) * N ^ 3) hT hS
  rw [el, ea] at w
  have r := Stepped.ite_runs_false (p := fun p : List Unit × Fml => hasNil p.2) (M := Stepped.const false) (a := (List.replicate n (), ψ)) hnilψ w
  rw [← hdec] at r
  have hb := loop_bound (UniformInK.bsumU τ 3) N h1
  exact (Stepped.mapIn_runs r).mono (by omega) (by omega)

/-- **The run of lines 1 to 4 of Algorithm 1**: «for each Φ in the list that Lemma 4 computes from φ
and ε do» (line 2), the test Count(Φ) > 0 in place of the paper's line 3, which counts; only the
formulas up to the first with a positive count are tested. -/
theorem stLoopRuns : StLoopRuns := stLoopRunsOf stWalkUntil

/-- If the machine Mc in the place of Count has polynomial-time steps, so does `satLoop τ Mc` (lines
1 to 4 of Algorithm 1). Uses the hypothesis `StFoldUntilPoly` for the loop that can be left early,
and the fields `rule_poly` and `out_poly` of the enumeration (Lemma 4: «in time 2^{εn} times a
polynomial in n»). -/
theorem satLoop_polyTimeSteps_of (HP : StFoldUntilPoly) {ε : ℝ} {M τ : ℕ} (hE : Enumerates ε M τ) (Mc : StepMachine Formula ℤ) (hMc : PolyTimeSteps Mc) : PolyTimeSteps (satLoop τ Mc) := by
  obtain ⟨h⟩ := hMc
  have hr := CountKSat.Poly.rootC_polyT
  have := IsPolyT.mapOut (M := Mc) posZ_polyT
  have := IsPolyT.mapIn (M := Stepped.mapOut Mc posZ) hE.out_poly
  have := IsPolyT.guard (T := Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ)) (d := false) (IsPolyT.walkSel_polyT hE.rule_poly)
  obtain ⟨hw⟩ := HP (List Unit × Fml) Bool Bool (List CNode) (fun a => some [rootC a]) (walkNext (rule τ)) (Stepped.guard (walkSel (rule τ)) (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ)) false)
    (fun c _ b => c || b) id (fun _ => false) (by fun_prop) (IsPolyT.walkNext_polyT hE.rule_poly) (by fun_prop) PolyT.id' (by fun_prop)
  have : IsPolyT (walkUntil (rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ))) := hw
  have : IsPolyT (Stepped.const false : Stepped (List Unit × Fml) Bool) := IsPolyT.const false
  have := IsPolyT.ite (M := (Stepped.const false : Stepped (List Unit × Fml) Bool)) (N := walkUntil (rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ)))
    (p := fun p => hasNil p.2) (by have := hasNil_polyT; fun_prop)
  exact ⟨IsPolyT.mapIn (stCertDecU 3)⟩

end Suffices
