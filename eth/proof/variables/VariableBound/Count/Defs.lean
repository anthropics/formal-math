/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
public import VariableBound.Search.Defs
public import VariableBound.Params.Defs

/-! # One sparse formula counted as in Steps 1 to 4 of Appendix D: the program and its interface statements

ψ has m clauses of 1 to k literals on n variables, and every variable occurs in at most Δ clauses.
The program computes the parameters n̄, β, r̄, M, t̄ defined under «Setting and parameters» in
Appendix D. If m ≤ n̄, it outputs F of the empty list. Otherwise it lists the
family of Lemma 13 for v = n̄, finds the checks by the search of Step 2, in which X(𝓛) is computed
by the networks of Step 3 through a clique solver, and outputs F(𝓛).
This file has definitions only. The statements are propositions; proof/variables/VariableBound/Count
proves them. -/

@[expose] public section

namespace VariableBound

open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The count of Steps 1 to 4 for ψ on n variables; under the hypotheses of `StCountD` it is the
number of satisfying assignments among the 2ⁿ assignments. -/
def countD (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (ψ : Fml) : ℕ :=
  let m := ψ.length
  let nb := nbD n Δ
  let β := beta n m nb
  let rb := rbD β
  let M := Mb β rb
  bif decide (m ≤ nb) then (evF S k pad i n Δ nb M (ψ, [])).toNat
  else (evF S k pad i n Δ nb M
    (ψ, searchD pad (fun L => evX S k pad i n Δ nb M β (ψ, L)) (Fld.famD m (Nat.log 2 nb)) m nb β rb (tbD m nb rb))).toNat

/-- What the count of one formula needs of the length of the pad, written F here (not the count F(𝓛)
of Step 1): it must be at least the bounds below for the networks, the list of profiles and the list
of checks. None of the three depends on the formula. -/
structure FitsD (k : ℕ) (i : Idx) (n Δ : ℕ) (F : ℕ) : Prop where
  net : 2 ^ needNet S i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n) ≤ F
  prof : nPrMax (S.K i) n Δ ≤ F
  lists : 8 * (10 * n + 1) * (sbMax Δ + 1) * (Nat.size (Δ * n) + 2) + 8 ≤ F

end

/-- Steps 1 to 4: the count is right. Hypotheses: the clique solver S is correct (`S.Correct ok`) at
the index i (`ok i`) and has K ≥ 2 there; every clause of ψ has 1 to k literals on the variables 0,
…, n − 1 (`WfL`); every variable occurs in
at most Δ clauses; m ≤ Δ·n; 2 ≤ Δ; n ≥ 29·⌈log₂(2Δ)⌉ + 19 (with the inequalities of «Setting and
parameters» in Appendix D this gives n ≥ 2·log(2Δ), r̄ ≤ 10n and M ≤ 14n); and the pad fits
(`FitsD`). -/
def StCountD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (ψ : Fml),
  ok i → 2 ≤ S.K i → WfL k n [ψ] → (∀ v, (occ ψ v).length ≤ Δ) → ψ.length ≤ Δ * n → 2 ≤ Δ → 29 * LD Δ + 19 ≤ n → FitsD S k i n Δ pad.length →
  countD S k pad i n Δ ψ = nSat n ψ

/-- For every polynomial-time clique solver (`S.Poly`), the count of one sparse formula is
polynomial-time, jointly in its input: the width k, given in unary as the first component; then the
pad, the index, (n, Δ) in unary and the formula. -/
def StCertCountD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly →
  PolyT fun x : U × U × Idx × (U × U) × Fml => countD S x.1.length x.2.1 x.2.2.1 x.2.2.2.1.1.length x.2.2.2.1.2.length x.2.2.2.2

end VariableBound
