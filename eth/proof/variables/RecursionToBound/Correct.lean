/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Defs
import RecursionToBound.Tree
import PairsToBound.Width
import PairsToBound.Exhaust
import SparsificationLemma.StepSparsify
import SparsificationLemma.Side
import SparsificationLemma.One
import SparsificationLemma.Gen
import SparsificationLemma.Len
import SparsificationLemma.Cal.Facts
import SparsificationLemma.Cal.Beta
import SparsificationLemma.Cal.Thr
import SparsificationLemma.Cal.Alpha
import StepSparsify.Walk
import UniformInK.Tree.Stack
import CountKSat.InOut
import CountKSatRate.Walk
import CountKSatRate.Brute
import RecursionWithPieces.Main
import VariableBound.Printed.VariablesA.Level
import ClauseBound.Alg.Decode
import WidthK.Decode
import ToTuring.Poly.NetFun
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! # Theorem D (a) along the printed Step 5: the function is right

`countIsRight_of` proves `CountIsRight` from three statements taken as hypotheses,
`OutputsAreWithinTheSetting`, `CutOffIsIdle` and `PlanFailsOnlyAboveN`, and uses `widthOnTheCode`,
`walkTreeIsSparsify` and `ownDeltaIsBounded` (Tree.lean) directly.

1. **The input** (`countIsRight_of`). On the code of (k, φ) the function reads n, the clauses, k′ =
   «the largest number of literals in a clause, or 3», the index of the level ℓ of n and the number
   r in [e_ℓ, 2e_ℓ] (`widthOnTheCode`). φ is a k′-CNF and 3 ≤ k′ ≤ k, so k′ ≤ (log n)^(1/4), and the
   cut-off of k′ does nothing.
2. **Without a plan** the padding string has at least 2ⁿ units and the function tries all
   assignments (`CountKSatRate.stBruteC`).
3. **With a plan** n ≥ n₁ and the padding string has at least 2^(`needOutputs` + `needWalk`) units.
   `countAll_eq` shows that the walk returns the number of satisfying assignments:
   * `walk_eq`: the walk returns the sum of the values at the leaves. What is known of the tree
     comes from the general theorem `SparsificationLemma.stTreeG` at Calabro's thresholds, with τ =
     α ≥ k′² and paths cut after (32α)^(2k′)·n steps, which is at least (β₁ + … + β_(k′−1))·n by
     fact (iv) on Calabro's thresholds, `SparsificationLemma.Cal.factIV` (`depth_le`). So the bound
     `stackLenCU` on the length of the walk's state applies (`UniformInK.stStateLenU`).
   * There are at most 2^(εn) leaves (`walkTreeIsSparsify`,
     `SparsificationLemma.StepSparsify.outputs_le`), so 2^(⌈εn⌉+2) units suffice for the rounds.
   * `countOutput_eq`: the value at a leaf is the number of satisfying assignments of its output.
     «An output without clauses counts 2^n.» Every other output Φ is counted by Steps 2 to 4 with
     its own Δ; this count is right by `VariableBound.StCountD`, in the proof
     `RecursionWithPieces.countAB`. Its hypotheses: Φ is a k′-CNF; a variable occurs in at most Δ
     clauses, by the definition of Δ
     (`occ_le_DeltaOf`); so Φ has at most Δ·n clauses; Δ ≤ `occBound` (`ownDeltaIsBounded`), hence Δ
     ≤ n + 1 and n ≥ 29·⌈log₂(2Δ)⌉ + 19; and the padding string fits, because Δ is one of the
     numbers over which `needOutputs` is the maximum (`fitsD_of`).
   * The sum of these numbers over the outputs is the number of satisfying assignments of φ
     (`SparsificationLemma.StepSparsify.count_eq_sum`).
The lemmas stand in the namespace `RecursionToBound.Correct`. -/

public section

namespace RecursionToBound

open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
open PaddedDescent.F.Mark (WfL nSat)
open Groundwork.Sparsify (PFml leaves round)

namespace Correct

/-! ### The number kept by the walk never goes down -/

/-- One round does not lower the number. -/
theorem le_roundS {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (st : List σ × ℕ) : st.2 ≤ (roundS step val st).2 := by
  obtain ⟨l, c⟩ := st
  cases l with
  | nil => exact le_rfl
  | cons s r =>
    rcases h : step s with _ | ⟨l, hh⟩
    · simp [roundS, h]
    · simp [roundS, h]

/-- Further rounds do not lower the number. -/
theorem iterate_le_iterate {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (st : List σ × ℕ) (i j : ℕ) :
    ((roundS step val)^[i] st).2 ≤ ((roundS step val)^[j + i] st).2 := by
  induction j with
  | zero => rw [Nat.zero_add]
  | succ j ih =>
    rw [Nat.succ_add, Function.iterate_succ_apply']
    exact ih.trans (le_roundS step val _)

/-- The number after any number of rounds is at most the sum of the values of the leaves. -/
theorem iterate_le_sum {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (d : ℕ) (s : σ)
    (hd : ∀ x ∈ leaves step d s, step x = none) (i : ℕ) : ((roundS step val)^[i] ([s], 0)).2 ≤ ((leaves step d s).map val).sum := by
  have h := iterate_le_iterate step val ([s], 0) i (2 * (leaves step d s).length - 1)
  rwa [stRoundSEnd σ step val d s hd _ (Nat.le_add_right _ _)] at h

/-! ### The walk -/

/-- (β₁ + … + β_(k−1))·n ≤ (32α)^(2k)·n, for α ≥ 1 and k ≥ 2: by `SparsificationLemma.Cal.factIV`
the sum is at most 4·(32α)^(k−2). -/
theorem depth_le {α k : ℕ} (hα : 1 ≤ α) (hk : 2 ≤ k) (n : ℕ) : (∑ i ∈ range k, Cal.betaC α i) * n ≤ bsumU (32 * α) k * n := by
  refine Nat.mul_le_mul_right n ?_
  have h0 : Cal.betaC α 0 = 0 := by simp [Cal.betaC]
  have e : ∑ i ∈ range k, Cal.betaC α i = ∑ c ∈ Ico 1 k, Cal.betaC α c := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < k), h0]
    simp only [Nat.zero_add]
  rw [e, bsumU]
  calc ∑ c ∈ Ico 1 k, Cal.betaC α c ≤ 4 * (32 * α) ^ (k - 2) := Cal.factIV α k hα hk
    _ ≤ (32 * α) * (32 * α) ^ (k - 2) := Nat.mul_le_mul_right _ (by omega)
    _ = (32 * α) ^ (k - 2 + 1) := (pow_succ' _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

/-- The walk with Calabro's thresholds for α returns the sum of the values at the leaves of the tree
whose paths are cut after (32α)^(2k)·n steps. Hypotheses: k ≥ 2, α ≥ k²; ψ is a k-CNF on n variables
with at most m clauses; the padding string has at least 2·(number of leaves) − 1 units and at least
`stackLenCU k (32α) n m` units;
the sum is below 2^(n+1). -/
theorem walk_eq {α k n m : ℕ} {ψ : PFml} (hk : 2 ≤ k) (hα : k ^ 2 ≤ α) (hψ : IsKCNF k n ψ) (hm : ψ.length ≤ m) (pad : U) (val : CNode → ℕ)
    (h1 : 2 * (leaves (stepC (Cal.thetaC α) k) (bsumU (32 * α) k * n) (rootC (List.replicate n (), ψ))).length ≤ pad.length + 1)
    (h2 : stackLenCU k (32 * α) n m ≤ pad.length)
    (h3 : ((leaves (stepC (Cal.thetaC α) k) (bsumU (32 * α) k * n) (rootC (List.replicate n (), ψ))).map val).sum < 2 ^ (n + 1)) :
    _root_.StepSparsify.walkSG (Cal.thetaC α) k pad val (rootC (List.replicate n (), ψ)) =
      ((leaves (stepC (Cal.thetaC α) k) (bsumU (32 * α) k * n) (rootC (List.replicate n (), ψ))).map val).sum := by
  have hα1 : 1 ≤ α := le_trans (Nat.one_le_pow _ _ (by omega)) hα
  obtain ⟨-, t2, -, t4⟩ := stTreeG stExactlyOne stCountOfExactlyOne stOutputsSame k α n (bsumU (32 * α) k * n) (Cal.thetaC α) (Cal.betaC α) (by omega) hα
    (Cal.stThrCal α k hα1) (depth_le hα1 hk n) ψ hψ
  obtain ⟨r, hr⟩ : ∃ r, r = rootC (List.replicate n (), ψ) := ⟨_, rfl⟩
  rw [← hr] at t2 t4 h1 h3 ⊢
  have hleaf : ∀ x ∈ leaves (stepC (Cal.thetaC α) k) (bsumU (32 * α) k * n) r, stepC (Cal.thetaC α) k x = none := fun x hx => (t2 x hx).1
  refine _root_.StepSparsify.stWalkSG (Cal.thetaC α) k pad val r (bsumU (32 * α) k * n) hleaf h1 fun i => le_trans ?_ h2
  obtain ⟨s1, s2⟩ := t4 i
  have hc : ((roundS (stepC (Cal.thetaC α) k) val)^[i] ([r], 0)).2 < 2 ^ (n + 1) := lt_of_le_of_lt (iterate_le_sum _ val _ r hleaf i) h3
  have e := stRoundS _ (stepC (Cal.thetaC α) k) val i [r] []
  rw [List.map_nil, List.sum_nil] at e
  rw [e] at hc ⊢
  exact stStateLenU k (32 * α) n m _ _ s1 (fun x hx => ⟨(s2 x hx).1.trans (Nat.mul_le_mul_right _ hm), (s2 x hx).2⟩) hc

/-! ### One output -/

/-- In a k-CNF Φ on n variables every variable, below n or not, occurs in at most Δ clauses, Δ =
`DeltaOf n Φ`: a variable that is not below n does not occur. -/
theorem occ_le_DeltaOf {k n : ℕ} {Φ : PFml} (hΦ : IsKCNF k n Φ) (v : ℕ) : (occ Φ v).length ≤ SparsificationLemma.StepSparsify.DeltaOf n Φ := by
  by_cases hv : v < n
  · exact (Finset.le_sup (f := fun v => occN Φ v) (Finset.mem_range.2 hv)).trans (le_max_right _ _)
  · have h0 : occ Φ v = [] := by
      refine List.filter_eq_nil_iff.2 fun C hC h => ?_
      obtain ⟨l, hl, hlv⟩ := List.any_eq_true.1 h
      have h1 := (hΦ C hC).2.2 l hl
      have h2 : l.1 = v := beq_iff_eq.1 hlv
      omega
    rw [h0]
    exact Nat.zero_le _

/-- The two definitions here of the number of satisfying assignments of ψ among the 2ⁿ assignments,
`nSat` and `cntN`, agree. -/
theorem nSat_eq_cntN (n : ℕ) (ψ : Fml) : nSat n ψ = cntN n ψ := by
  unfold nSat cntN
  congr 1

/-- A number Δ with 2 ≤ Δ ≤ `occBound k r` and Δ ≤ n + 1 is one of the numbers over which
`needOutputs` is the maximum. -/
theorem mem_deltas_of {k n Δ : ℕ} {r : ℕ × ℕ} (h2 : 2 ≤ Δ) (hb : Δ ≤ occBound k r) (hn : Δ ≤ n + 1) : Δ ∈ deltas k r n := by
  unfold deltas
  refine List.mem_map.2 ⟨Δ - 2, List.mem_range.2 (by omega), ?_⟩
  omega

/-- A padding string of at least 2^(`needOutputs`) units fits the count of an output with such a Δ. -/
theorem fitsD_of {Idx : Type} [Enc Idx] (S : Solver Idx) {k n Δ F : ℕ} {r : ℕ × ℕ} (i : Idx) (hΔ : Δ ∈ deltas k r n) (hF : 2 ^ needOutputs S k r i n ≤ F) : FitsD S k i n Δ F := by
  have h1 : needAt S k i n Δ ≤ needOutputs S k r i n := Groundwork.Prog.NetE.le_foldr_max (List.mem_map.2 ⟨Δ, hΔ, rfl⟩)
  have h2 : 2 ^ needAt S k i n Δ ≤ F := (Nat.pow_le_pow_right (by norm_num) h1).trans hF
  have hp : ∀ a : ℕ, a ≤ needAt S k i n Δ → 2 ^ a ≤ F := fun a ha => (Nat.pow_le_pow_right (by norm_num) ha).trans h2
  refine ⟨hp _ ?_, (Nat.lt_size_self _).le.trans (hp _ ?_), (Nat.lt_size_self _).le.trans (hp _ ?_)⟩ <;> (unfold needAt; omega)

/-- The value at a node whose output Φ is a k-CNF on n variables is the number of satisfying
assignments of Φ. Hypotheses: i is the index of a level; the Δ of Φ is at most n + 1 and at most
`occBound k r`, and n ≥ 29·⌈log₂(2Δ)⌉ + 19; the padding string has at least 2^(`needOutputs`) units. -/
theorem countOutput_eq {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) {k n l : ℕ} {r : ℕ × ℕ} (pad : U) (x : CNode) (hΦ : IsKCNF k n (out x))
    (hb : SparsificationLemma.StepSparsify.DeltaOf n (out x) ≤ occBound k r) (hn : SparsificationLemma.StepSparsify.DeltaOf n (out x) ≤ n + 1) (hL : 29 * LD (SparsificationLemma.StepSparsify.DeltaOf n (out x)) + 19 ≤ n)
    (hpad : 2 ^ needOutputs S k r (Q.idx l) n ≤ pad.length) : countOutput S k pad (Q.idx l) n x = cntN n (out x) := by
  unfold countOutput
  cases hx : out x with
  | nil => exact (SparsificationLemma.StepSparsify.count_no_clause n).symm
  | cons C Φ =>
    rw [← hx]
    have h2 : 2 ≤ SparsificationLemma.StepSparsify.DeltaOf n (out x) := le_max_left _ _
    have hne : (out x).isEmpty = false := by rw [hx]; rfl
    rw [hne, cond_false]
    have hwf : WfL k n [out x] := by
      intro y hy
      rw [List.mem_singleton.1 hy]
      exact hΦ
    exact (RecursionWithPieces.countAB Idx S (fun i => ∃ l, i = Q.idx l) Q.correct k pad (Q.idx l) n (SparsificationLemma.StepSparsify.DeltaOf n (out x)) (out x) ⟨l, rfl⟩ (Q.K_two l)
      hwf (occ_le_DeltaOf hΦ) (stLenOfOcc k n _ (out x) hΦ (occ_le_DeltaOf hΦ)) h2 hL (fitsD_of S (Q.idx l) (mem_deltas_of h2 hb hn) hpad)).trans (nSat_eq_cntN n _)

/-! ### All outputs -/

/-- There are at most 2ⁿ satisfying assignments. -/
theorem numSat_le {n : ℕ} (φ : CNF n) : SatK.numSat φ ≤ 2 ^ n := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- A formula with an empty clause has no satisfying assignment. -/
theorem numSat_of_nil {n : ℕ} {φ : CNF n} (h : [] ∈ φ) : SatK.numSat φ = 0 := by
  rw [SatK.numSat, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  obtain ⟨l, hl, -⟩ := ha [] h
  simp at hl

/-- A k-CNF on n variables without repeated clauses has at most `inLen k n` clauses, for k ≥ 1. -/
theorem length_le_inLen {k n : ℕ} {φ : CNF n} (hk : 1 ≤ k) (hφ : SatK.IsKCNF k φ) : φ.length ≤ inLen k n := by
  have h := DecodeK.length_enc k φ
  have h' := DecodeK.length_enc_succ_le (φ := φ) hφ
  have hB : 0 < k * (Nat.log2 (2 * n) + 1) := Nat.mul_pos hk (Nat.succ_pos _)
  have := Nat.le_mul_of_pos_right φ.length hB
  unfold inLen
  omega

/-- «Run Steps 2 to 4 on each of the … outputs and add the results.» For k ≥ 3, a k-CNF φ on n
variables without repeated clauses, 0 < r, the index of a level, and a padding string of at least
2^(`needOutputs` + `needWalk`) units, `countAll` on (n, φ) is the number of satisfying assignments
of φ; provided that every Δ with
2 ≤ Δ ≤ `occBound k r` has Δ ≤ n + 1 and n ≥ 29·⌈log₂(2Δ)⌉ + 19. -/
theorem countAll_eq {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) {k n l : ℕ} {r : ℕ × ℕ} (φ : CNF n) (pad : U) (hk : 3 ≤ k) (hφ : SatK.IsKCNF k φ)
    (hr1 : 0 < r.1) (hr2 : 0 < r.2) (hΔ : ∀ Δ : ℕ, 2 ≤ Δ → Δ ≤ occBound k r → Δ ≤ n + 1 ∧ 29 * LD Δ + 19 ≤ n)
    (hpad : 2 ^ (needOutputs S k r (Q.idx l) n + needWalk k r n) ≤ pad.length) :
    countAll S k r (Q.idx l) (List.replicate n (), Decode.toN φ) pad = SatK.numSat φ := by
  unfold countAll
  dsimp only
  rw [List.length_replicate]
  have hnilψ : hasNil (Decode.toN φ) = true ↔ [] ∈ φ := by
    rw [← Decode.nil_mem_toN]
    simp [hasNil, List.any_eq_true]
  by_cases hnil : [] ∈ φ
  · rw [hnilψ.2 hnil, cond_true, numSat_of_nil hnil]
  · have hn' : hasNil (Decode.toN φ) = false := by
      rw [← Bool.not_eq_true]
      exact fun h => hnil (hnilψ.1 h)
    rw [hn', cond_false]
    have h0 := Eps.pos hr1 hr2
    have h1 := Eps.le_one r
    obtain ⟨-, -, hα, -, -⟩ := Cal.stAlpha k (epsOf r) hk h0 h1
    have hψ0 : IsKCNF k n (Decode.toN φ) := by
      intro D hD'
      obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN hD'
      refine ⟨?_, hl ▸ hφ.1 C hC, h⟩
      rintro rfl
      exact hnil ((Decode.nil_mem_toN φ).1 hD')
    have hψ : IsKCNF k n (noTaut (Decode.toN φ)) := (stNoTaut _).2.1 k n hψ0
    have hm : (noTaut (Decode.toN φ)).length ≤ inLen k n :=
      (List.length_filter_le _ _).trans (by rw [Decode.length_toN]; exact length_le_inLen (by omega) hφ)
    have hpa : 2 ^ needOutputs S k r (Q.idx l) n ≤ pad.length := (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)).trans hpad
    have hpw : ∀ a : ℕ, a ≤ needWalk k r n → 2 ^ a ≤ pad.length := fun a ha =>
      (Nat.pow_le_pow_right (by norm_num) (ha.trans (Nat.le_add_left _ _))).trans hpad
    have hout := walkTreeIsSparsify k n (bsumU (32 * Cal.alphaC k (epsOf r)) k * n) r (Decode.toN φ) hk hr1 hr2 hψ0
      (depth_le (Eps.one_le_alpha hk hr1 hr2) (by omega) n)
    unfold thresholds at hout ⊢
    obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepC (Cal.thetaC (Cal.alphaC k (epsOf r))) k) (bsumU (32 * Cal.alphaC k (epsOf r)) k * n) (rootC (List.replicate n (), noTaut (Decode.toN φ))) := ⟨_, rfl⟩
    rw [← hL] at hout
    have hval : ∀ x ∈ L, countOutput S k pad (Q.idx l) n x = cntN n (out x) := by
      intro x hx
      have hmem : out x ∈ Cal.sparsify k n (epsOf r) (Decode.toN φ) := by
        rw [← hout]
        exact List.mem_map.2 ⟨x, hx, rfl⟩
      have hb := ownDeltaIsBounded k n r (Decode.toN φ) hk hr1 hr2 hψ0 (out x) hmem
      obtain ⟨c1, c2⟩ := hΔ (SparsificationLemma.StepSparsify.DeltaOf n (out x)) (le_max_left _ _) hb
      exact countOutput_eq Q pad x ((SparsificationLemma.StepSparsify.sparsABC k n (epsOf r) (Decode.toN φ) hk h0 h1 hψ0).1 _ hmem).1 hb c1 c2 hpa
    have hsum : (L.map (countOutput S k pad (Q.idx l) n)).sum = SatK.numSat φ := by
      calc (L.map (countOutput S k pad (Q.idx l) n)).sum = (L.map fun x => cntN n (out x)).sum := by rw [List.map_congr_left hval]
        _ = ((L.map out).map (cntN n)).sum := by simp only [List.map_map, Function.comp_def]
        _ = cntN n (Decode.toN φ) := by
          rw [hout]
          exact (SparsificationLemma.StepSparsify.count_eq_sum hk h0 h1 hψ0).symm
        _ = _ := stCntToN n φ
    have hlen : L.length ≤ 2 ^ ⌈epsOf r * (n : ℚ)⌉₊ := by
      have a1 := SparsificationLemma.StepSparsify.outputs_le hk h0 h1 hψ0
      rw [← hout, List.length_map] at a1
      have a2 : ((epsOf r : ℚ) : ℝ) * (n : ℝ) ≤ ((⌈epsOf r * (n : ℚ)⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_ceil (epsOf r * (n : ℚ))
      have a3 : (L.length : ℝ) ≤ ((2 ^ ⌈epsOf r * (n : ℚ)⌉₊ : ℕ) : ℝ) := by
        calc (L.length : ℝ) ≤ (2 : ℝ) ^ (((epsOf r : ℚ) : ℝ) * (n : ℝ)) := a1
          _ ≤ (2 : ℝ) ^ ((⌈epsOf r * (n : ℚ)⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two a2
          _ = _ := by rw [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
      exact_mod_cast a3
    have hrounds : 2 * L.length ≤ pad.length + 1 := by
      have b1 := hpw (⌈epsOf r * (n : ℚ)⌉₊ + 2) (by unfold needWalk; omega)
      rw [pow_add] at b1
      omega
    have hstack : stackLenCU k (32 * Cal.alphaC k (epsOf r)) n (inLen k n) ≤ pad.length :=
      (Nat.lt_size_self _).le.trans (hpw _ (by unfold needWalk; omega))
    have hlt : (L.map (countOutput S k pad (Q.idx l) n)).sum < 2 ^ (n + 1) := by
      rw [hsum]
      exact (numSat_le φ).trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n))
    rw [hL] at hrounds hlt hsum
    rw [walk_eq (by omega) hα hψ hm pad _ hrounds hstack hlt, hsum]

end Correct

/-! ### The function -/

/-- The function is right in the range of Theorem D (a); from `OutputsAreWithinTheSetting`,
`CutOffIsIdle` and `PlanFailsOnlyAboveN`. The number n₀ is the one that `OutputsAreWithinTheSetting`
gives for the constant C₀ of the sequence of levels. -/
theorem countIsRight_of (hSet : OutputsAreWithinTheSetting) (hCut : CutOffIsIdle) (hPlan : PlanFailsOnlyAboveN) : CountIsRight := by
  intro Idx _ S e C₀ Q hS num hnum
  obtain ⟨n₀, hn₀⟩ := hSet C₀ (VariableBound.VariablesA.one_le_C₀ Q)
  refine ⟨n₀, fun n₁ hn₁ k n φ hK hk hk4 hφ pad hpad => ?_⟩
  have hk1 : 1 ≤ k := by omega
  obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk1 hφ.1
  have hn : nU (SatM.enc k φ) = n := by rw [nU, hdec, List.length_replicate]
  obtain ⟨l, hl⟩ : ∃ l, IsLevel S Q n l := ⟨_, VariableBound.VariablesA.isLevel_pick Q hK⟩
  obtain ⟨hw3, hwk, hwle⟩ := widthOr3Stmt n φ
  obtain ⟨k', hk'⟩ : ∃ k', k' = widthOr3 φ := ⟨_, rfl⟩
  rw [← hk'] at hw3 hwk hwle
  have hwU : widthU (SatM.enc k φ) = k' := (widthOnTheCode.1 k n φ hk1 hφ).trans hk'.symm
  obtain ⟨hnumU, hidx⟩ := widthOnTheCode.2 Idx S e C₀ Q num k n l φ hk1 hφ hl
  obtain ⟨r, hr⟩ : ∃ r, r = num (List.replicate l (), List.replicate (S.K (Q.idx l)) ()) := ⟨_, rfl⟩
  rw [← hr] at hnumU
  have hk'k : k' ≤ k := (hwle k hk1 hφ).1.trans (max_le le_rfl hk)
  have hk'4 : (k' : ℝ) ^ 4 ≤ MainTheoremForms.lg n := (pow_le_pow_left₀ (Nat.cast_nonneg k') (by exact_mod_cast hk'k) 4).trans hk4
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by have := Q.K_two 0; omega)) hK
  have hcut : kcU k' n = k' := hCut k' n hn1 hk'4
  have hplan : plan S n₁ Q.pick num (SatM.enc k φ) = planAt S n₁ k' n (Q.idx l) r := by rw [plan, hwU, hn, hcut, hidx, hnumU]
  have hnumber : (bif (plan S n₁ Q.pick num (SatM.enc k φ)).isNone then bruteU (SatM.enc k φ, pad)
      else countAll S (kcU (widthU (SatM.enc k φ)) (nU (SatM.enc k φ))) (numU S Q.pick num (SatM.enc k φ)) (idxU Q.pick (SatM.enc k φ)) (fmlOf (SatM.enc k φ)) pad) = SatK.numSat φ := by
    rw [expo, hplan, hn] at hpad
    rw [hplan, hwU, hn, hcut, hidx, hnumU, hdec]
    cases hpl : planAt S n₁ k' n (Q.idx l) r with
    | none =>
      rw [hpl, Option.getD_none] at hpad
      have hb := stBruteC k n φ hk1 hφ pad hpad
      rw [bruteN, nK, stDecU k n φ hk1 hφ.1] at hb
      simp only [List.length_replicate] at hb
      simp only [Option.isNone_none, cond_true, bruteU, hdec, List.length_replicate]
      exact hb
    | some v =>
      rw [hpl, Option.getD_some] at hpad
      obtain ⟨c1, c2, -⟩ := (hPlan Idx S hS n₁ k' n (Q.idx l) r).1 v hpl
      rw [c2] at hpad
      obtain ⟨hlo, hhi⟩ := hnum.2 l
      rw [← hr] at hlo hhi
      obtain ⟨hr1, hr2⟩ := Eps.pos_of_le (VariableBound.VariablesA.e_pos Q l) hlo
      simp only [Option.isNone_some, cond_false]
      refine Correct.countAll_eq Q φ pad hw3 (hwk hφ.2) hr1 hr2 (fun Δ h2 hb => ?_) hpad
      obtain ⟨-, -, -, d1, d2⟩ := hn₀ k' n Δ r (e l) (hn₁.trans c1) hw3 hk'4 (VariableBound.VariablesA.e_ge_n Q hl) (Q.e_le l) hlo hhi h2 hb
      exact ⟨d1, d2⟩
  unfold count
  dsimp only
  rw [hnumber, hdec]
  exact outW_replicate _ _ _

end RecursionToBound
