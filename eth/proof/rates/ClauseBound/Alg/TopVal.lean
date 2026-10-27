/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Top
import PaddedDescent.F.RebalG
import CountKSat.Value
import CountKSat.InOut
import StepMachines.Prog.NetVal
import StepMachines.Prog.Count
import StepMachines.Math.SatNet
import all CountKSatRate.Brute
import all CountKSat.Top.Count

/-! # The top level in m: correctness

Two statements of `proof/rates/ClauseBound/Alg/Interfaces.lean` and
`proof/rates/ClauseBound/Alg/Top.lean`. (1) The plain functions `satFk`, with the number g of nodes
and the width k in the context, present the
network of a formula (`stSatPresentsK`). (2) The function `AM` returns the number of satisfying
assignments of a k-CNF all of whose variables occur, as n + 1 bits, if the pad has length at
least 2^eM (`stCorrectM`), under the hypothesis that this network on 3K⁸ nodes, rebalanced to K
nodes with labels of `lamTopK` bits and handed to a correct clique solver, gives its value if the
pad has length at least 2^needTop;
`AM` counts exhaustively when that needs a pad at most as long as the clique solver's. The text
followed is the paper's network of a formula (Section 6) and the proof of part (c) of Theorem A. -/

namespace ClauseBound.Alg.TopVal

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F CountKSat

/-- The plain functions satFk, in the context ((g, k) in unary, ψ), present the network of ψ on g
nodes at width k. -/
public theorem stSatPresentsK : StSatPresentsK := fun _ _ _ _ =>
  { S_eq := fun _ => rfl
    c_eq := fun _ _ _ => rfl
    lab_eq := fun a b _ => lab_wordNet a b
    W_runs := fun _ _ _ => RebalF.freeM_runs _ _
    f_runs := fun _ _ _ _ _ _ _ => RebalF.freeM_runs _ _ }

/-- What the computation under a bound returns is the exponent needTop. -/
private theorem needTopC_eq {Idx : Type} [Enc Idx] {S : Solver Idx} (hP : S.Poly) {b : U} {i : Idx} {k m v : ℕ} (h : needTopC S b i k m = some v) :
    v = needTop S i k m := by
  unfold needTopC at h
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := hP.needC_eq _ _ _ hw
  split_ifs at h
  exact (Option.some.inj h).symm

/-- The function AM returns the number of satisfying assignments, as n + 1 bits, if the pad has
length at least 2^eM. -/
public theorem stCorrectM (hD : StDecM) (hC : StCountG) : StCorrectM := by
  intro Idx _ S e C₀ Q hP k n φ hk _ hφ hocc pad hpad
  obtain ⟨hkO, hdec⟩ := hD k n φ hk hφ.1
  simp only [eM, planM, hdec, hkO, List.length_replicate, Decode.length_toN] at hpad
  simp only [AM, planM, hdec, hkO, List.length_replicate, Decode.length_toN]
  rw [CountKSatRate.Brute.outW_eq_binary]
  congr 1
  rcases hm : needTopC S (List.replicate n ()) (Q.pick (root9 φ.length)).2 k φ.length with _ | v
  · rw [hm, Option.getD_none] at hpad
    rw [Option.isNone_none, cond_true, rng_eq hpad, CountKSatRate.Brute.length_filter_satAt]
  · rw [hm, Option.getD_some, needTopC_eq hP hm] at hpad
    rw [Option.isNone_some, cond_false]
    have hnilψ : hasNil (Decode.toN φ) = true ↔ [] ∈ φ := by
      rw [← Decode.nil_mem_toN]
      simp [hasNil, List.any_eq_true]
    by_cases hnil : [] ∈ φ
    · rw [hnilψ.2 hnil, cond_true, CountTop.numSat_of_nil hnil]
    · have hn' : hasNil (Decode.toN φ) = false := by
        rw [← Bool.not_eq_true]; exact fun h => hnil (hnilψ.1 h)
      rw [hn', cond_false]
      obtain ⟨i, hi⟩ : ∃ i, i = (Q.pick (root9 φ.length)).2 := ⟨_, rfl⟩
      rw [← hi] at hpad ⊢
      have hidx : i = Q.idx (Q.pick (root9 φ.length)).1.length := hi.trans (Q.pick_idx _)
      have hK : 2 ≤ S.K i := hidx ▸ Q.K_two _
      have hg : 0 < 3 * S.K i ^ 8 := by
        have : 0 < S.K i ^ 8 := Nat.pow_pos (by omega)
        omega
      have hw : ∀ C ∈ Decode.toN φ, C.length ≤ k := fun D hD' => by
        obtain ⟨⟨C, hC', hl⟩, -⟩ := Decode.mem_toN hD'
        exact hl ▸ hφ.1 C hC'
      rw [hC Idx S _ Q.correct pad i k (Decode.toN φ) ⟨_, hidx⟩ hK hk hw (by rw [Decode.length_toN]; exact hpad),
        Value.value_wordNet_eq_cntN hg hw (fun D hD' => (Decode.mem_toN hD').2) (fun v hv => ?_), Int.toNat_natCast, stCntToN n φ]
      obtain ⟨C, hC', l, hl, hlv⟩ := hocc ⟨v, hv⟩
      exact ⟨C.map fun l => (l.1.val, l.2), List.mem_map.2 ⟨C, hC', rfl⟩, (l.1.val, l.2), List.mem_map.2 ⟨l, hl, rfl⟩, by simp [hlv]⟩

end ClauseBound.Alg.TopVal
