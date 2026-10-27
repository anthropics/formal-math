/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Exits.AlgDefs
import Eight.ViaGrouping.Main
import Eight.ViaGrouping.Keeps
import ToTuring.Poly.Range
import Mathlib.Tactic.GCongr

/-! # Lemma 1 for the algorithm of its proof, with the search that halts at the first good grouping

Proof of Lemma 1, «The algorithm»: «Go through all K^g groupings (a constant) and fix the first good
one.» Line 10 of Algorithm 1: «try all groupings into K_ℓ groups until one is good».
This file proves three implications of proof/threesat/Exits/AlgDefs.lean, each from its hypotheses.
* `stSearchStopsOf`: from «try all … until one is good» for any loop (`StFirstUntil`), the search
  halts at the first good grouping number x, within 2·(x + 1) steps: one step for a test and one to
  go on.
* `stGroupingLemmaOf`: Lemma 1 for `Exits.netAlg`, from the run of the search and the three steps of
  the proof: a good grouping exists and the first good one is fixed (`ViaGrouping.StSearch`), the
  cost of one entry (`ViaGrouping.StTable`), the value equals Z (`ViaGrouping.StValue`). The proof
  is that of `Eight.ViaGrouping.netAlg_correct` (proof/networks/Eight/ViaGrouping/Main.lean) with
  this search in the place of the one used there; the steps of «Cost» are called as they stand there
  (`Cost.run_clique`, `Cost.bound_follows`, `Groundwork.RebalanceArith.size_le`), since they do not
  speak of the search. The search takes 2·(x + 1) ≤ 2·K^g steps: «(a constant)».
* `stKeepsOf`: the algorithm has polynomial-time steps if the loop `foldUntil` has
  (`StFoldUntilPoly`); the certificates of L, of the test of a grouping and of the tables are those
  of proof/networks/Eight/ViaGrouping/Keeps.lean.
`correct_of_searchStops` and `search_isPolyT` are steps inside the proofs of the last two, not
statements of AlgDefs.lean. -/

public section

namespace Exits

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset Paper Eight Eight.SecNetworks Eight.ViaGrouping Eight.ViaGrouping.Cost

/-- **Line 10 of Algorithm 1**: «try all groupings into K_ℓ groups until one is good». If x is the
first number below K^g to which the test says yes, the search halts within 2·(x + 1) steps and
returns x. From the same sentence for any loop. -/
theorem stSearchStopsOf : StSearchStopsOf := by
  intro hF K g C _ Np c x hfind
  have hx : x < K ^ g := List.mem_range.1 (List.mem_of_find?_eq_some hfind)
  have hreach : reach (fun y => goodP K g Np (c, y)) (K ^ g) = x + 1 := by simp only [reach, hfind]
  have h : (search K g Np).Runs c (∑ _y ∈ range (reach (fun y => goodP K g Np (c, y)) (K ^ g)), (1 + 1))
      (size c + size (K ^ g) + (size (K ^ g) + 1 + (size c + size (K ^ g) + 1)) + 1) ((List.range (K ^ g)).find? fun y => goodP K g Np (c, y)) :=
    hF C Bool (nCol K g) (ofFun (goodP K g Np)) id c (fun _ => 1) (fun y => goodP K g Np (c, y)) (size c + size (K ^ g) + 1) fun y hy =>
      (ofFun_runs (goodP K g Np) (c, y)).mono le_rfl (by
        have hy' : y < reach (fun y => goodP K g Np (c, y)) (K ^ g) := hy
        rw [hreach] at hy'
        have := Nat.size_le_size (show y ≤ K ^ g by omega)
        simp only [size_prod, size_nat, size_bool]
        omega)
  rw [hreach, hfind] at h
  refine h.mono ?_ (by omega)
  rw [sum_const, card_range, smul_eq_mul]
  omega

/-- The bound of Lemma 1 for the algorithm of its proof with the search of line 10, on networks on
[g], for every g ≥ K for which a good grouping is found (hypothesis `hS`). The proof runs through
the paragraphs «The algorithm» and «Cost»: «Go through all K^g groupings (a constant) and fix the
first good one» (`hR`: the search halts there), «Run the algorithm for (K, e) with L, B' in the
roles of λ, B» (`Cost.run_clique`), «the bound follows» (`Cost.bound_follows`), and the same for the
sizes of the states. -/
theorem correct_of_searchStops (hR : StSearchStops) (hT : ViaGrouping.StTable) (hV : ViaGrouping.StValue) {K g : ℕ} {e : ℝ} {E : CliqueAlgorithm} (hK : 2 ≤ K) (hKg : K ≤ g) (h0 : 0 ≤ e) (h : E.Within K e)
    (hS : ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
      ∃ x < K ^ g, (List.range (K ^ g)).find? (fun x => goodP K g Np (c, x)) = some x ∧ Good N.c P (Paper.grouping (g := g) (by omega : 0 < K) x)) :
    Correct (netAlg K g E) g K e (e + 2) := by
  have hK0 : 0 < K := by omega
  -- the constants
  obtain ⟨A, c₁, hc₁1, hrunE⟩ := run_clique hT hV g hK0 (by omega) h
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, c₂ = c₁ + 5 * size (K ^ g) + 20 := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ := bound_follows (K := K) (g := g) A c₁ (2 * K ^ g + 1) (by omega) (by omega) h0
  obtain ⟨A2, hA2⟩ := RebalanceArith.size_le (K := K) (g := g) A c₂ (2 * g + g ^ 2) hK hKg
  refine ⟨max A1 A2, fun C _ Np c N P B τ S hN => ?_⟩
  have hP := hN.is.P_pos
  have hU := U_le hN.is
  -- «fix the first good one», number x; the search halts at it
  obtain ⟨x, hxlt, hfind, hgood⟩ := hS C Np c N P B τ S hN
  have hsearch := hR K g C Np c x hfind
  -- «run the algorithm for (K, e) …»
  obtain ⟨TE, hrun, hTE⟩ := hrunE C Np c N P B τ S hN x hxlt hgood
  have hall := optBind_runs_some (dflt := zeroOf) hsearch hrun
  have hZ1 : 1 ≤ size c + P + B := by omega
  have hpow : ∀ {a b : ℕ}, a ≤ b → a * (size c + P + B) ^ a ≤ b * (size c + P + B) ^ b := fun hab =>
    Nat.mul_le_mul hab (Nat.pow_le_pow_right hZ1 hab)
  refine ⟨2 * (x + 1) + 1 + TE, hall.mono le_rfl ?_, ?_⟩
  · -- the sizes of the states
    refine (hA2 P B N.U (Paper.groupedLength K g N.U P) (Bp K g P B) S (S + c₁ * (size c + P + B) ^ c₁) (size c) (size (c, x)) _ hP hU (K2L_le K g N.U P)
      (Bp_le g P B (by omega)) (Nat.add_le_add_left (hpow (by omega)) _) ?_ ?_).trans (Nat.add_le_add_left (hpow (le_max_right _ _)) _)
    · have hx : size x ≤ size (K ^ g) := by
        simp only [size_nat]
        exact Nat.succ_le_succ (Nat.size_le_size hxlt.le)
      have h3 : size c + size (K ^ g) ≤ c₂ * (size c + P) := by
        have h4 : 1 * size c ≤ c₂ * size c := Nat.mul_le_mul_right _ (by omega)
        have h5 : c₂ * 1 ≤ c₂ * P := Nat.mul_le_mul_left _ hP
        rw [Nat.mul_add]
        omega
      simp only [size_prod]
      omega
    · have h3 : c₂ * (size c + P + B) ≤ c₂ * (size c + P + B) ^ c₂ :=
        Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) _)
      have h4 : 5 * size c + 5 * size (K ^ g) + 20 ≤ c₂ * (size c + P + B) := by
        have h5 : 5 * size c ≤ c₂ * size c := Nat.mul_le_mul_right _ (by omega)
        have h6 : c₂ * 1 ≤ c₂ * P := Nat.mul_le_mul_left _ hP
        rw [Nat.mul_add, Nat.mul_add]
        omega
      omega
  · -- «the bound follows»; 2·(x + 1) ≤ 2·K^g: «(a constant)»
    refine (hA1 P B τ N.U TE (2 * (x + 1) + 1 + TE) hP hN.τ_pos hU hTE (by omega)).trans ?_
    have hY : (1 : ℝ) ≤ (P : ℝ) + B := by exact_mod_cast (by omega : 1 ≤ P + B)
    have hAm : (A1 : ℝ) ≤ ((max A1 A2 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hYp : ((P : ℝ) + B) ^ A1 ≤ ((P : ℝ) + B) ^ (max A1 A2) := pow_le_pow_right₀ hY (le_max_left _ _)
    gcongr

/-- **Lemma 1 for the algorithm of its proof**, with the search of line 10. «Let (K, e) be
achievable and g = 3K⁸. There is a constant C₁ = C₁(K, e) such that the value of every network on
[g] with parameters P, B, τ and total U is computed within C₁·2^{e(U + gP/K) + 2gP/K}·(P + B)^{C₁}·τ
operations.» From the run of the search and the three steps «a good grouping exists … fix the first
good one», «one entry costs …» and «so the value equals Z». -/
theorem stGroupingLemmaOf : StGroupingLemmaOf := fun hR hS hT hV K _ _ hK h0 h =>
  correct_of_searchStops hR hT hV hK (by
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
    omega) h0 h fun C _ Np c N P B τ S hN => hS K hK C Np c N P B τ S hN

/-- The search of line 10, «try all groupings into K_ℓ groups until one is good», has
polynomial-time steps, if the loop that can be left early has. -/
theorem search_isPolyT (hF : StFoldUntilPoly) (K g : ℕ) {C : Type} [HasSize C] [Enc C] [Carried C] {Np : Procs C} (h : KeepsP Np) : Nonempty (IsPolyT (search K g Np)) := by
  have := IsPolyT.ofFun (goodP_polyT K g h)
  have hg0 : PolyT fun q : Option ℕ × ℕ × Bool => firstG id q.1 q.2.1 q.2.2 :=
    (by fun_prop : PolyT fun q : Option ℕ × ℕ × Bool => q.1.elim (if q.2.2 = true then some q.2.1 else none) fun i => some i).congr
      fun q => by rcases q with ⟨_ | i, y, b⟩ <;> rfl
  exact hF C Bool (Option ℕ) (C × ℕ) (rangeStart (nCol K g)) (rangeNext (nCol K g)) (ofFun (goodP K g Np)) (rangeG (firstG id)) Option.isSome noneC
    (IsPolyT.rangeStart_poly (nCol_polyT K g)) (IsPolyT.rangeNext_poly (nCol_polyT K g))
    (by unfold rangeG; exact PolyT.comp (g := fun p : Option ℕ × (C × ℕ) × Bool => (p.1, p.2.1.2, p.2.2)) hg0 (by fun_prop))
    (by fun_prop) (by unfold noneC; fun_prop)

/-- **The algorithm of the proof of Lemma 1, with the search of line 10, has polynomial-time steps**
if the algorithm E for cliques has. A bound on the number of steps («… is computed within C₁·2^{e(U +
gP/K) + 2gP/K}·(P + B)^{C₁}·τ operations») bounds the time only if each step takes polynomial time;
this is that half. From the polynomial-time steps of the loop. -/
theorem stKeepsOf : StKeepsOf := by
  intro hF K g E hE C _ _ _ Np hN
  have hk := keeps_toPaperNetwork hN.keeps
  obtain ⟨hm⟩ := hN.keeps.mem
  obtain ⟨hW⟩ := hN.keeps.W
  obtain ⟨hΨ⟩ := hN.keeps.Ψ
  obtain ⟨hf⟩ := hN.keeps.f
  obtain ⟨hE'⟩ := hE (C × ℕ) (lamP K g Np) (tableM K g Np) (lamP_unary K g hN) ⟨tableM_isPolyT K g hk⟩
  obtain ⟨hs⟩ := search_isPolyT hF K g hN
  exact ⟨IsPolyT.optBind zeroOf_polyT⟩

end Exits
