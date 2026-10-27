/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.Col.Good
public import PaddedDescent.F.RebalF

/-! # The rebalancing with a given label length

`rebalG` is `rebalF` with the label length β of the new instance as an argument and the test `goodG`
in place of `goodB`. `rebalG_spec` is the value statement, the
analogue of `RebalF.stR` for `goodG`, with the existence of a good colouring as a hypothesis; `stRG`
gets that from `exists_goodG` and is the interface statement `StRG`. -/

public section

namespace PaddedDescent.F.RebalF

open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.Col Finset

/-- The rebalancing with a given label length β: if some colouring below K^g is good for β and the
pad is long enough, `rebalG` returns an explicit instance on K nodes
with labels of β bits and the value of the network. -/
theorem rebalG_spec {C : Type} (pad : U) (K g β : ℕ) (F : FNet C) (c : C) (N : Network (Fin g) (List Bool) (List Bool)) (P B : ℕ)
    (hK : 2 ≤ K) (hg0 : 0 < g) (hβ1 : 1 ≤ β) (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B)
    (hex : ∃ x < K ^ g, goodG K g F.toP β (c, x) = true)
    (f1 : K ^ g ≤ pad.length) (f2 : 2 ^ (P * (2 * g / K)) ≤ pad.length) (f3 : 2 ^ P ≤ pad.length)
    (f4 : 2 ^ ((K - 1) * β) ≤ pad.length) :
    ∃ J, rebalG pad K g β F c = some J ∧ zval K J = N.value ∧ J.1.length = β ∧
      WF K β (P * (2 * g / K) + B * (2 * g / K + 2 * g / K * (2 * g / K)) * K) J := by
  have hK0 : 0 < K := by omega
  obtain ⟨x', hx', hgood'⟩ := hex
  obtain ⟨x, hfind⟩ : ∃ x, (List.range (K ^ g)).find? (fun x => goodG K g F.toP β (c, x)) = some x := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨x', List.mem_range.2 hx', hgood'⟩
  have hgood : goodG K g F.toP β (c, x) = true := List.find?_some (p := fun x => goodG K g F.toP β (c, x)) hfind
  obtain ⟨hg1, hg2⟩ := (goodG_iff F.toP hK0 hN β x).1 hgood
  obtain ⟨m, hmdef⟩ : ∃ m, m = 2 * g / K := ⟨_, rfl⟩
  rw [← hmdef] at f2 ⊢
  have hm : ∀ G, #{a : Fin g | chi hK0 x a = G} ≤ m := fun G => by
    rw [hmdef, Nat.le_div_iff_mul_le hK0, Nat.mul_comm]
    exact (hg1 G).le
  have hSm := Network.merge_sized N (chi hK0 x) [] [] hS hm
  have hm' : ∀ G < K, (members K g x G).length ≤ m := fun G hG => by
    rw [length_members hK0 x ⟨G, hG⟩]; exact hm _
  have hβ' : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g F.toP c x G G' ≤ β := fun G hG G' hG' hne => by
    have hne' : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e => hne (congrArg Fin.val e)
    rw [lbLen_eq F.toP hK0 hN x hne']
    exact hg2 _ _ hne'
  have hentry : ∀ (G : Fin K) (θ : Fin K → List Bool), WFQ β G θ →
      mergedF pad K g F ((c, x), (G.1, List.ofFn θ)) =
        (N.merge (chi hK0 x) [] []).toInst (mD K g F.toP c x β) (mdec K g F.toP c x) G θ := by
    rintro G θ ⟨hθ, hG⟩
    rw [toInst_eq_mergedVal F.toP hK0 hN x β G θ hθ, ← mergedP_eq hN hS x β m hm' hβ' G θ hθ hG]
    refine mergedF_eq ?_ fun y i hi hW => ?_
    · exact (Nat.pow_le_pow_right (by norm_num) (stLen_le hN hS (hm' G G.2))).trans f2
    · have ha : i / g < g := Nat.div_lt_of_lt_mul hi
      have hb : i % g < g := Nat.mod_lt _ hg0
      have hab : (⟨i / g, ha⟩ : Fin g) ≠ ⟨i % g, hb⟩ := by
        intro e
        have e' : i / g = i % g := congrArg Fin.val e
        simp [isW, e'] at hW
      exact (Nat.pow_le_pow_right (by norm_num) (cap_le hN hS hab)).trans f3
  have habs : ∀ (G : Fin K) (θ : Fin K → List Bool), WFQ β G θ →
      (mergedF pad K g F ((c, x), (G.1, List.ofFn θ))).natAbs ≤ 2 ^ (P * m + B * (m + m * m) * K) := by
    intro G θ hq
    rw [hentry G θ hq]
    have h : |(N.merge (chi hK0 x) [] []).toInst (mD K g F.toP c x β) (mdec K g F.toP c x) G θ| ≤
        2 ^ (P * m + B * (m + m * m) * K) := by
      simpa only [Fintype.card_fin] using Network.abs_toInst_le _ _ _ hSm G θ
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  refine ⟨(List.replicate β (), tabulate pad K β fun q => mergedF pad K g F ((c, x), q)), ?_, ?_, by simp, ?_⟩
  · unfold rebalG
    rw [rng_eq f1, hfind]
    rfl
  · unfold zval
    simp only [List.length_replicate]
    rw [Table.stT1 K β _ ((N.merge (chi hK0 x) [] []).toInst (mD K g F.toP c x β) (mdec K g F.toP c x))
      fun G θ hq => by rw [instOf, Table.stT2 pad K β _ f4 G θ hq, hentry G θ hq]]
    exact ZW_merged F.toP hK0 hN x β fun G G' hlt => by
      rw [lbLen_eq F.toP hK0 hN x hlt.ne]; exact hg2 _ _ hlt.ne
  · exact Table.stT3a pad K β β _ _ f4 hβ1 le_rfl habs

/-- From `ColOK K g` and K ≥ 1: g is positive. -/
theorem pos_of_colOK {K g : ℕ} (hK : 1 ≤ K) (h : ColOK K g) : 0 < g := by
  obtain ⟨m, h1, h2⟩ := h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : 1 ≤ (g + 2) * K := Nat.mul_pos (by omega) hK
    simp at h2
    omega
  · have : 0 < 4 * Dcol ^ 2 * m * K := by
      have : 0 < Dcol := by unfold Dcol; positivity
      positivity
    omega

/-- The interface statement `StRG`: under `ColOK K g`, `exists_goodG` supplies a colouring below K^g
that is good for β, and `rebalG_spec` then gives the rebalanced instance and its value. -/
theorem stRG : StRG := by
  intro C pad K g β F c N P B M hK hcol hN hS hM0 hM hβ1 hβ f1 f2 f3 f4
  obtain ⟨m, h1, h2⟩ := id hcol
  exact rebalG_spec pad K g β F c N P B hK (pos_of_colOK (by omega) hcol) hβ1 hN hS
    (exists_goodG F.toP (by omega) hN hM0 (by unfold Dcol; exact Nat.one_le_two_pow) hM h1 h2 hβ) f1 f2 f3 f4

end PaddedDescent.F.RebalF
