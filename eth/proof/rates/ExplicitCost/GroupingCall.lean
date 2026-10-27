/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ExplicitCost.GroupingDefs
import ExplicitCost.GroupingSearch
import ExplicitCost.Cost
import Printed.GroupingEntry
import Printed.GroupingRun
import QueryMachines.CombRuns
import Value.End
import GeneralPieces.Main
import Mathlib.Tactic

/-! # Lemma 8 (the grouping lemma of Appendix A) up to the call

The procedure `groupingCall` of Lemma 8 runs the search and then asks one query, the call, whose
answer is its result. With the call answered by the value of the clique of the groups, that result
is the value of the network (in the proof of Lemma 8: «whose value is that of the network»,
`Value.StValueEqualsZ`).

* `abs_value_le`, `size_value_le`: the value of a network on [g] with parameters P, B is at most
  2^{gP + gB + g²B} in absolute value. The last state of the procedure holds the value, so its size
  has to be bounded.
* `Sizes.add_three_le`, `value_sizes`: arithmetic of the sizes.
* `groupingWithCallFrom`: how the steps give the lemma up to the call; with the constant C of the
  search the constant is C + 12.
* `groupingWithCall`: the lemma up to the call. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

/-- The value of a network: at most (2^P)^g terms, each a product of g values of the W_a and at most
g² values of the Ψ_{a,b}. -/
theorem abs_value_le {g : ℕ} {N : Net g} {P B : ℕ} (h : N.Is P B) : |N.value| ≤ 2 ^ (g * P + g * B + g ^ 2 * B) := by
  have hm1 : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
  have hterm : ∀ z ∈ Fintype.piFinset N.S, |(∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)| ≤ (2 ^ B) ^ g * (2 ^ B) ^ (g ^ 2) := by
    intro z hz
    have hz' := Fintype.mem_piFinset.1 hz
    rw [abs_mul]
    refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
    · have := abs_prod_le_pow univ (fun a => N.W a (z a)) (2 ^ B) fun a _ => (h.ii_W a _ (hz' a)).le
      rwa [Finset.card_univ, Fintype.card_fin] at this
    · refine (abs_prod_le_pow (pairs (Fin g)) (fun p => N.Ψ p.1 p.2 (z p.1) (z p.2)) (2 ^ B) fun p hp =>
        (h.ii_Ψ _ _ (ne_of_lt (mem_filter.1 hp).2) _ (hz' _) _ (hz' _)).le).trans ?_
      refine pow_le_pow_right₀ hm1 ?_
      calc #(pairs (Fin g)) ≤ #(univ : Finset (Fin g × Fin g)) := card_le_card (filter_subset _ _)
        _ = g ^ 2 := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  have hcard : #(Fintype.piFinset N.S) ≤ (2 ^ P) ^ g := by
    rw [Fintype.card_piFinset]
    calc ∏ a, #(N.S a) ≤ ∏ _a : Fin g, 2 ^ P := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun a _ =>
          calc #(N.S a) ≤ #(words (N.len a)) := card_le_card fun z hz => mem_words.2 (h.len_S a z hz)
            _ = 2 ^ N.len a := card_words _
            _ ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) (h.len_le a)
      _ = (2 ^ P) ^ g := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold Net.value
  calc |∑ z ∈ Fintype.piFinset N.S, (∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)|
      ≤ ∑ z ∈ Fintype.piFinset N.S, |(∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ Fintype.piFinset N.S, ((2 : ℤ) ^ B) ^ g * (2 ^ B) ^ (g ^ 2) := Finset.sum_le_sum hterm
    _ = (#(Fintype.piFinset N.S) : ℤ) * (((2 : ℤ) ^ B) ^ g * (2 ^ B) ^ (g ^ 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 : ℤ) ^ P) ^ g * (((2 : ℤ) ^ B) ^ g * (2 ^ B) ^ (g ^ 2)) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = 2 ^ (g * P + g * B + g ^ 2 * B) := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring

/-- The value of a network has at most gP + gB + g²B + 1 binary digits. -/
theorem size_value_le {g : ℕ} {N : Net g} {P B : ℕ} (h : N.Is P B) : size N.value ≤ g * P + g * B + g ^ 2 * B + 2 := by
  rw [size_int]
  refine Nat.succ_le_succ (Nat.size_le.2 ?_)
  have h1 : (N.value.natAbs : ℤ) ≤ 2 ^ (g * P + g * B + g ^ 2 * B) := by
    rw [Int.natCast_natAbs]
    exact abs_value_le h
  have h2 : N.value.natAbs ≤ 2 ^ (g * P + g * B + g ^ 2 * B) := by exact_mod_cast h1
  exact h2.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))

namespace Sizes

/-- u + v + w ≤ Z^{n+2} if u, v, w ≤ Z^n and Z ≥ 2. -/
theorem add_three_le {Z n u v w : ℕ} (hZ : 2 ≤ Z) (hu : u ≤ Z ^ n) (hv : v ≤ Z ^ n) (hw : w ≤ Z ^ n) : u + v + w ≤ Z ^ (n + 2) := by
  have h : 2 * 2 * Z ^ n ≤ Z * Z * Z ^ n := Nat.mul_le_mul_right _ (Nat.mul_le_mul hZ hZ)
  have e : Z ^ (n + 2) = Z * Z * Z ^ n := by ring
  rw [e]
  omega

end Sizes

open Sizes

/-- gP + gB + g²B + 2 ≤ (g(P+B) + s)^{10}. -/
private theorem value_sizes {g P B : ℕ} (s : ℕ) (hg : 1 ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) : g * P + g * B + g ^ 2 * B + 2 ≤ (g * (P + B) + s) ^ 10 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := basic_facts hg hP hB
  refine le_trans ?_ (sq_le_pow (X := g * (P + B) + s) (by omega))
  have e : (g * (P + B) + s) * (g * (P + B) + s) = g * (P + B) * (g * (P + B)) + 2 * (g * (P + B) * s) + s * s := by ring
  have e1 : g * P + g * B = g * (P + B) := by ring
  have e2 : g ^ 2 * B = B * (g * g) := by ring
  rw [e, e1, e2]
  omega

/-- How the search, its cost, the size bounds and the equality of the values (the clique of the
groups has the value of the network) give Lemma 8 up to the call. -/
theorem groupingWithCallFrom : GroupingWithCallFrom := by
  intro hF hSC hS hV
  obtain ⟨C, hC⟩ := hSC
  refine ⟨C + 12, fun a b K g hK0 N P B tc hK hg ha hab hN hCases => ?_⟩
  have hb : 0 < b := by omega
  have hζ0 : (0 : ℝ) < (a : ℝ) / b := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hζ1 : (a : ℝ) / b ≤ 1 := (div_le_one (by exact_mod_cast hb)).2 (by exact_mod_cast hab)
  obtain ⟨hKg, -⟩ := hS K g _ P N.c hK hg hζ0 hζ1 hN.P_pos hN.i hCases
  obtain ⟨x, hx, hfind, h1, h2⟩ := hF a b K g hK0 N P B hK hg ha hab hN hCases
  refine ⟨x, hx, hfind, h1, h2, fun O hO => ?_⟩
  have hval : (Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).value = N.value :=
    hV NetInput g K hK0 (asked.close (netOracle N)) (netInput N P B) N P B 1 _ (asked_isNetworkP N hN) x _ h2
  rw [hval] at hO
  have hsearch := hC a b K g N P B x hK0 hKg hN hfind
  have hquery : (QueryMachine.query callOf : QueryMachine CliqueCall ℤ (GroupingInput × ℕ) ℤ).Within O (fun _ => tc) (groupingInput a b K N P B, x) tc
      (max (size (groupingInput a b K N P B, x)) (size N.value) + 1) N.value :=
    ⟨0, [callOf (groupingInput a b K N P B, x)], stQueryRuns _ _ _ callOf O _ _ hO, by simp⟩
  refine (optBind_within (dflt := zeroOf) hsearch hquery).mono ?_ ?_
  · have : 1 ≤ K ^ g := Nat.one_le_pow _ _ hK0
    have e : (C + 12) * K ^ g = C * K ^ g + 12 * K ^ g := by ring
    omega
  · obtain ⟨Z, hZ⟩ : ∃ Z, Z = g * (P + B) + size (a, b) := ⟨_, rfl⟩
    rw [← hZ]
    have hX := (basic_facts (hK0.trans_le hKg) hN.P_pos hN.B_pos).1
    have hZ2 : 2 ≤ Z := by omega
    have hm : Z ^ 10 ≤ Z ^ (C + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    have hm' : Z ^ C ≤ Z ^ (C + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    have s1 := search_sizes (s := size (a, b)) hK0 hKg hN.P_pos hN.B_pos (size_netInput_le N hN) (size_pow_le hKg)
    have s2 := value_sizes (size (a, b)) (hK0.trans_le hKg) hN.P_pos hN.B_pos
    have s3 := size_value_le hN
    have s4 := size_groupingInput a b K N P B
    have s5 : size x ≤ size (K ^ g) := by
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size hx.le)
    have s6 : size (groupingInput a b K N P B, x) = size (groupingInput a b K N P B) + size x := rfl
    rw [← hZ] at s1 s2
    have key := add_three_le (n := C + 10) (u := size (groupingInput a b K N P B) + size x + 4) (v := Z ^ C) (w := size N.value) hZ2 (by omega) hm' (by omega)
    have e : C + 12 = C + 10 + 2 := by omega
    rw [e]
    omega

/-- **Lemma 8 up to the call.** -/
theorem groupingWithCall : GroupingWithCall :=
  groupingWithCallFrom searchFinds searchCost AppRunningTime.groupingSizes Value.stValueEqualsZ

end ExplicitCost
