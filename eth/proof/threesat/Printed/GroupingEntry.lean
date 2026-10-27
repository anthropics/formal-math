/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Close
public import Printed.Coding
public import Printed.Achievable
public import Eight.ViaGrouping.Display
import Mathlib.Tactic

/-! # Proof of Lemma 1, «Cost», first half: one entry of W̃_γ

Proof of Lemma 1, «Cost»: the sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} = 2^{2gP/K} terms, each
a product of at most g² values; so |W̃_γ| < 2^{B'} with B' = ⌈2gP/K⌉ + g²B, and one entry costs
2^{2gP/K}·poly(P + B)·τ operations.
* `asked_isNetworkP`: the four procedures «ask», with the oracle of a network built in, give that
  network in the sense of `Eight.ViaGrouping.IsNetworkP`, each within ONE step; `size_netInput_le`:
  the input of Definition 2(iii) has size linear in P + B;
* `card_factors_le`, `abs_term_le`: «each a product of at most g² values»; each value is below 2^B,
  so at most 2^B − 1;
* `card_settings_le`: «at most (2^P)^{2g/K} = 2^{2gP/K} terms»;
* `abs_display_lt`: «So |W̃_γ| < 2^{B'}», strictly, as Definition 4 asks (the proof goes through the
  bound 2^{P⌊2g/K⌋ + g²B}, which equals 2^{B'} when K divides 2g);
* `stEntryCost`: the count of `Eight.ViaGrouping.tableM_display` at one step per procedure is a
  count of own steps and queries (`QueryMachines.stClose`, `Printed.tableQ_close`); at τ operations
  per query it is multiplied by τ (`QueryMachines.stSlowDown`). -/

public section

namespace Printed

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

/-! ## The procedures «ask» give the network -/

/-- The entry number a of a list written with `List.ofFn`. -/
theorem getD_ofFn {α : Type} {g : ℕ} (f : Fin g → α) (a : Fin g) (d : α) : (List.ofFn f).getD a.val d = f a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos a.2]
  rfl

/-- A list of g things of size at most M. -/
theorem size_listOfFn_le {α : Type} [HasSize α] {g : ℕ} (f : Fin g → α) (M : ℕ) (h : ∀ a, size (f a) ≤ M) : size (List.ofFn f) ≤ g * (M + 1) + 1 := by
  rw [size_list]
  have := Table.sum_map_le (List.ofFn f) (fun l => size l + 1) (M + 1) (fun l hl => by
    obtain ⟨a, rfl⟩ : ∃ a, f a = l := by simpa [List.mem_ofFn] using hl
    exact Nat.succ_le_succ (h a))
  rw [List.length_ofFn] at this
  omega

/-- «Is z ∈ S_a?», asked, with the oracle built in: one step, then the answer is read as yes if it
is not 0. -/
theorem asked_mem_close (O : NetQuery → Option ℤ) :
    (asked.close O).mem = Stepped.mapOut (Stepped.ofOption fun a : NetInput × WQ => O (Sum.inl a.2)) fun v : ℤ => decide (v ≠ 0) := by
  change (QueryMachine.mapOut (QueryMachine.query fun x : NetInput × WQ => (Sum.inl x.2 : NetQuery)) fun v : ℤ => decide (v ≠ 0)).close O = _
  rw [close_mapOut, close_query]

/-- W_a(z), asked, with the oracle built in: one step. -/
theorem asked_W_close (O : NetQuery → Option ℤ) : (asked.close O).W = Stepped.ofOption fun a : NetInput × WQ => O (Sum.inr (Sum.inl a.2)) := close_query _ _

/-- Ψ_{a,b}(z, z'), asked, with the oracle built in: one step. -/
theorem asked_Ψ_close (O : NetQuery → Option ℤ) : (asked.close O).Ψ = Stepped.ofOption fun a : NetInput × PsiQ => O (Sum.inr (Sum.inr (Sum.inl a.2))) := close_query _ _

/-- f_{a,b}(z, θ), asked, with the oracle built in: one step. -/
theorem asked_f_close (O : NetQuery → Option ℤ) : (asked.close O).f = Stepped.ofOption fun a : NetInput × FQ => O (Sum.inr (Sum.inr (Sum.inr a.2))) := close_query _ _

/-- c_{a,b} ≤ P, by (i) of Definition 2. -/
theorem c_le {g : ℕ} {N : Net g} {P B : ℕ} (h : N.Is P B) {a b : Fin g} (hab : a ≠ b) : N.c a b ≤ P :=
  (Finset.single_le_sum (f := fun b => N.c a b) (fun _ _ => Nat.zero_le _) (Finset.mem_erase.2 ⟨hab.symm, mem_univ b⟩)).trans (h.i a)

/-- **Definition 2(iii) by queries.** The four procedures «ask», with the oracle of the network N
built in, give N in the context `netInput N P B`, each within one step. -/
theorem asked_isNetworkP {g : ℕ} (N : Net g) {P B : ℕ} (h : N.Is P B) :
    IsNetworkP (asked.close (netOracle N)) (netInput N P B) N P B 1 (size (netInput N P B) + 2 * size g + 4 * P + B + 4) where
  is := h
  τ_pos := le_rfl
  given :=
    { P_eq := length_unary P
      len_eq := fun a => by
        change ((List.ofFn fun a : Fin g => unary (N.len a)).getD a.val []).length = _
        rw [getD_ofFn, length_unary]
      cap_eq := fun a b hab => by
        change (((List.ofFn fun a : Fin g => List.ofFn fun b : Fin g => if a = b then [] else unary (N.c a b)).getD a.val []).getD b.val []).length = _
        rw [getD_ofFn, getD_ofFn, if_neg hab, length_unary]
      mem_runs := fun a z hz => by
        rw [asked_mem_close]
        have e : netOracle N (Sum.inl (a.val, z)) = some (if z ∈ N.S a then 1 else 0) := by simp [netOracle, hz]
        have r : (Stepped.mapOut (Stepped.ofOption fun a : NetInput × WQ => netOracle N (Sum.inl a.2)) fun v : ℤ => decide (v ≠ 0)).Runs (netInput N P B, (a.val, z)) 1 _
            (decide ((if z ∈ N.S a then (1 : ℤ) else 0) ≠ 0)) := Stepped.mapOut_runs (Stepped.ofOption_runs e)
        have e2 : decide ((if z ∈ N.S a then (1 : ℤ) else 0) ≠ 0) = decide (z ∈ N.S a) := by by_cases hm : z ∈ N.S a <;> simp [hm]
        rw [e2] at r
        refine r.mono le_rfl ?_
        have h1 := size_fin a
        have h2 := size_word z
        have h3 := h.len_le a
        have h4 := size_ite_le (z ∈ N.S a)
        simp only [size_prod]
        omega
      W_runs := fun a z hz => by
        rw [asked_W_close]
        have e : netOracle N (Sum.inr (Sum.inl (a.val, z))) = some (N.W a z) := by simp [netOracle, hz]
        refine (Stepped.ofOption_runs (g := fun a : NetInput × WQ => netOracle N (Sum.inr (Sum.inl a.2))) (a := (netInput N P B, (a.val, z))) e).mono le_rfl ?_
        have h1 := size_fin a
        have h2 := size_word z
        have h3 := h.len_le a
        have h4 := size_entry (h.ii_W a z hz)
        have h5 := h.len_S a z hz
        simp only [size_prod]
        omega
      Ψ_runs := fun a b hab z hz z' hz' => by
        rw [asked_Ψ_close]
        have hv : a.val ≠ b.val := fun e => hab (Fin.ext e)
        have e : netOracle N (Sum.inr (Sum.inr (Sum.inl ((a.val, b.val), (z, z'))))) = some (N.Ψ a b z z') := by simp [netOracle, hv, hz, hz']
        refine (Stepped.ofOption_runs (g := fun a : NetInput × PsiQ => netOracle N (Sum.inr (Sum.inr (Sum.inl a.2)))) (a := (netInput N P B, ((a.val, b.val), (z, z')))) e).mono le_rfl ?_
        have h1 := size_fin a
        have h1' := size_fin b
        have h2 := size_word z
        have h2' := size_word z'
        have h3 := h.len_le a
        have h3' := h.len_le b
        have h4 := size_entry (h.ii_Ψ a b hab z hz z' hz')
        have h5 := h.len_S a z hz
        have h5' := h.len_S b z' hz'
        simp only [size_prod]
        omega
      f_runs := fun a b hab z hz θ hθ => by
        rw [asked_f_close]
        have hv : a.val ≠ b.val := fun e => hab (Fin.ext e)
        have e : netOracle N (Sum.inr (Sum.inr (Sum.inr ((a.val, b.val), (z, θ))))) = some (N.f a b z θ) := by simp [netOracle, hv, hz, mem_words.1 hθ]
        refine (Stepped.ofOption_runs (g := fun a : NetInput × FQ => netOracle N (Sum.inr (Sum.inr (Sum.inr a.2)))) (a := (netInput N P B, ((a.val, b.val), (z, θ)))) e).mono le_rfl ?_
        have h1 := size_fin a
        have h1' := size_fin b
        have h2 := size_word z
        have h2' := size_word θ
        have h3 := h.len_le a
        have h3' := c_le h hab
        have h4 := size_entry (h.ii_f a b hab z hz θ hθ)
        have h5 := h.len_S a z hz
        have h5' := mem_words.1 hθ
        simp only [size_prod]
        omega }

/-- The input of Definition 2(iii), all numbers in unary, has size linear in P + B. -/
theorem size_netInput_le {g : ℕ} (N : Net g) {P B : ℕ} (h : N.Is P B) : size (netInput N P B) ≤ (4 * g ^ 2 + 6 * g + 6) * (P + B) := by
  have hP := h.P_pos
  have s1 : size (List.ofFn fun a : Fin g => unary (N.len a)) ≤ g * (2 * P + 1 + 1) + 1 := size_listOfFn_le _ _ fun a => by
    have := h.len_le a
    rw [size_unary]
    omega
  have s2 : size (List.ofFn fun a : Fin g => List.ofFn fun b : Fin g => if a = b then [] else unary (N.c a b)) ≤ g * (g * (2 * P + 1 + 1) + 1 + 1) + 1 :=
    size_listOfFn_le _ _ fun a => size_listOfFn_le _ _ fun b => by
      by_cases hab : a = b
      · rw [if_pos hab]
        change 1 ≤ _
        omega
      · have := c_le h hab
        rw [if_neg hab, size_unary]
        omega
  have e : size (netInput N P B) = size (unary P) + size (unary B) + (size (List.ofFn fun a : Fin g => unary (N.len a)) +
      size (List.ofFn fun a : Fin g => List.ofFn fun b : Fin g => if a = b then [] else unary (N.c a b))) := rfl
  rw [e, size_unary, size_unary]
  have t1 : g * (2 * P + 1 + 1) ≤ g * (4 * (P + B)) := Nat.mul_le_mul_left _ (by omega)
  have t2 : g * (g * (2 * P + 1 + 1) + 1 + 1) ≤ g * (g * (4 * (P + B)) + 2 * (P + B)) := Nat.mul_le_mul_left _ (by omega)
  have t3 : (4 * g ^ 2 + 6 * g + 6) * (P + B) = g * (4 * (P + B)) + g * (g * (4 * (P + B)) + 2 * (P + B)) + 6 * (P + B) := by ring
  omega

/-! ## «each a product of at most g² values» -/

/-- Of three conditions that exclude one another at most one holds. -/
theorem three_le_one (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] (hab : A → ¬B) (hac : A → ¬C) (hbc : B → ¬C) :
    (if A then 1 else 0) + (if B then 1 else 0) + (if C then 1 else 0) ≤ 1 := by
  by_cases a : A <;> by_cases b : B <;> by_cases c : C <;> simp [a, b, c] <;> first | exact hab a b | exact hac a c | exact hbc b c

/-- A term of the display has at most g² factors: one for each node of the group, one for each pair
of nodes of the group, one for each pair of a node of the group and a node outside. -/
theorem card_factors_le {g K : ℕ} (χ : Fin g → Fin K) (γ : Fin K) :
    #{a | χ a = γ} + #{p ∈ pairs (Fin g) | χ p.1 = γ ∧ χ p.2 = γ} + #{p : Fin g × Fin g | χ p.1 = γ ∧ χ p.2 ≠ γ} ≤ g ^ 2 := by
  have e1 : #{a | χ a = γ} ≤ #{p : Fin g × Fin g | p.1 = p.2 ∧ χ p.1 = γ} :=
    Finset.card_le_card_of_injOn (fun a => (a, a)) (fun a ha => by simpa using ha) (fun a _ b _ hab => congrArg Prod.fst hab)
  have e2 : #{p ∈ pairs (Fin g) | χ p.1 = γ ∧ χ p.2 = γ} = #{p : Fin g × Fin g | p.1 < p.2 ∧ χ p.1 = γ ∧ χ p.2 = γ} := by
    unfold pairs
    rw [Finset.filter_filter]
  calc #{a | χ a = γ} + #{p ∈ pairs (Fin g) | χ p.1 = γ ∧ χ p.2 = γ} + #{p : Fin g × Fin g | χ p.1 = γ ∧ χ p.2 ≠ γ}
      ≤ #{p : Fin g × Fin g | p.1 = p.2 ∧ χ p.1 = γ} + #{p : Fin g × Fin g | p.1 < p.2 ∧ χ p.1 = γ ∧ χ p.2 = γ} + #{p : Fin g × Fin g | χ p.1 = γ ∧ χ p.2 ≠ γ} := by
        rw [e2]
        omega
    _ = ∑ p : Fin g × Fin g, ((if p.1 = p.2 ∧ χ p.1 = γ then 1 else 0) + (if p.1 < p.2 ∧ χ p.1 = γ ∧ χ p.2 = γ then 1 else 0) + (if χ p.1 = γ ∧ χ p.2 ≠ γ then 1 else 0)) := by
        simp only [Finset.card_filter, Finset.sum_add_distrib]
    _ ≤ ∑ _p : Fin g × Fin g, 1 := Finset.sum_le_sum fun p _ => three_le_one _ _ _ (fun a b => b.1.ne a.1) (fun a c => c.2 (a.1 ▸ a.2)) (fun b c => c.2 b.2.2)
    _ = g ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul, mul_one, sq]

/-- A product of n integers, each at most m in absolute value, is at most m^n in absolute value. -/
theorem abs_prod_le_pow {ι : Type} (s : Finset ι) (f : ι → ℤ) (m : ℤ) (h : ∀ i ∈ s, |f i| ≤ m) : |∏ i ∈ s, f i| ≤ m ^ #s := by
  rw [Finset.abs_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _) h

/-- 1 ≤ 2^B − 1 for B ≥ 1. -/
theorem one_le_two_pow_sub {B : ℕ} (hB : 1 ≤ B) : (1 : ℤ) ≤ 2 ^ B - 1 := by
  have h2 : (2 : ℤ) ^ 1 ≤ 2 ^ B := pow_le_pow_right₀ (by norm_num) hB
  rw [pow_one] at h2
  linarith

section Display

variable {C : Type} [HasSize C] {g K : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

/-- «each a product of at most g² values»: each value is below 2^B, so a term of the display is at
most (2^B − 1)^{g²} in absolute value. -/
theorem abs_term_le (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ) (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L)
    (γ : Fin K) (Θ : Fin K → List Bool) (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) {z : Fin g → List Bool} (hz : z ∈ tuples (fun a => Paper.grouping hK0 x a = γ) N.S []) :
    |(∏ a with Paper.grouping hK0 x a = γ, N.W a (z a)) *
        (∏ p ∈ pairs (Fin g) with Paper.grouping hK0 x p.1 = γ ∧ Paper.grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
        ∏ p : Fin g × Fin g with Paper.grouping hK0 x p.1 = γ ∧ Paper.grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np.toPaperNetwork c hK0 x Θ p.1 p.2)| ≤ (2 ^ B - 1) ^ g ^ 2 := by
  rw [mem_tuples] at hz
  have hm1 := one_le_two_pow_sub h.is.B_pos
  have hm0 : (0 : ℤ) ≤ 2 ^ B - 1 := by linarith
  have hL' : ∀ γ γ' : Fin K, γ ≠ γ' → (N.toPaperNetwork.merge (Paper.grouping hK0 x) [] []).c γ γ' ≤ L := fun γ γ' hne => by
    rw [Groundwork.Network.merge_c]
    exact hY γ γ' hne
  rw [abs_mul, abs_mul]
  refine (mul_le_mul (mul_le_mul (abs_prod_le_pow _ _ (2 ^ B - 1) ?_) (abs_prod_le_pow _ _ (2 ^ B - 1) ?_) (abs_nonneg _) (pow_nonneg hm0 _)) (abs_prod_le_pow _ _ (2 ^ B - 1) ?_) (abs_nonneg _)
    (mul_nonneg (pow_nonneg hm0 _) (pow_nonneg hm0 _))).trans ?_
  · exact fun a ha => Int.le_sub_one_of_lt (h.is.ii_W a _ ((hz a).1 (mem_filter.1 ha).2))
  · intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := mem_filter.1 hp
    have hlt : p.1 < p.2 := (mem_filter.1 hp1).2
    exact Int.le_sub_one_of_lt (h.is.ii_Ψ _ _ hlt.ne _ ((hz _).1 hp2) _ ((hz _).1 hp3))
  · intro p hp
    obtain ⟨hp1, hp2⟩ := (mem_filter.1 hp).2
    have hne : Paper.grouping hK0 x p.1 ≠ Paper.grouping hK0 x p.2 := fun e => hp2 (e ▸ hp1)
    have hlen : (thetaAt Np.toPaperNetwork c hK0 x Θ p.1 p.2).length = N.c p.1 p.2 := length_thetaAt Np.toPaperNetwork hK0 (Table.isPaperNetwork h) x L hL' Θ hne (hΘ _ hp2)
    exact Int.le_sub_one_of_lt (h.is.ii_f _ _ (fun e : p.1 = p.2 => hne (by rw [e])) _ ((hz _).1 hp1) _ (mem_words.2 hlen))
  · rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hm1 (card_factors_le _ γ)

omit [HasSize C] in
/-- «The sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} = 2^{2gP/K} terms», with ⌊2g/K⌋, the largest
number of nodes that (G1) allows in a group. -/
theorem card_settings_le (h : N.Is P B) (hK0 : 0 < K) (x : ℕ) (γ : Fin K) (hG1 : K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) :
    #(tuples (fun a => Paper.grouping hK0 x a = γ) N.S []) ≤ 2 ^ (P * (2 * g / K)) := by
  rw [card_tuples]
  calc ∏ a with Paper.grouping hK0 x a = γ, #(N.S a) ≤ ∏ a with Paper.grouping hK0 x a = γ, 2 ^ P := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun a _ =>
        calc #(N.S a) ≤ #(words (N.len a)) := card_le_card fun z hz => mem_words.2 (h.len_S a z hz)
          _ = 2 ^ N.len a := card_words _
          _ ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) (h.len_le a)
    _ = (2 ^ P) ^ #{a : Fin g | Paper.grouping hK0 x a = γ} := Finset.prod_const _
    _ ≤ (2 ^ P) ^ (2 * g / K) := Nat.pow_le_pow_right Nat.one_le_two_pow (by
        rw [Nat.le_div_iff_mul_le hK0, Nat.mul_comm]
        exact hG1)
    _ = 2 ^ (P * (2 * g / K)) := (pow_mul 2 P _).symm

/-- P·⌊2g/K⌋ + g²B ≤ B'. -/
theorem le_bitsOut {K : ℕ} (hK0 : 0 < K) (g P B : ℕ) : P * (2 * g / K) + g ^ 2 * B ≤ bitsOut K g P B := by
  unfold bitsOut
  refine Nat.add_le_add_right ?_ _
  rw [Nat.le_div_iff_mul_le hK0]
  calc P * (2 * g / K) * K = P * (2 * g / K * K) := Nat.mul_assoc _ _ _
    _ ≤ P * (2 * g) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ = 2 * (g * P) := by ring
    _ ≤ 2 * (g * P) + (K - 1) := Nat.le_add_right _ _

/-- **«So |W̃_γ| < 2^{B'} with B' = ⌈2gP/K⌉ + g²B»**, strictly: at most 2^{P⌊2g/K⌋} terms, each at
most (2^B − 1)^{g²} < 2^{g²B}, since g, B ≥ 1. -/
theorem abs_display_lt (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (hg : 0 < g) (x L : ℕ) (hG1 : ∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g)
    (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) (γ : Fin K) (Θ : Fin K → List Bool) (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) :
    |display Np c N hK0 x γ Θ| < 2 ^ bitsOut K g P B := by
  have hm1 := one_le_two_pow_sub h.is.B_pos
  have hm0 : (0 : ℤ) ≤ 2 ^ B - 1 := by linarith
  have hlt : ((2 : ℤ) ^ B - 1) ^ g ^ 2 < (2 ^ B) ^ g ^ 2 := pow_lt_pow_left₀ (sub_one_lt _) hm0 (pow_ne_zero 2 hg.ne')
  have hfinal : (2 : ℤ) ^ (P * (2 * g / K)) * (2 ^ B - 1) ^ g ^ 2 < 2 ^ bitsOut K g P B :=
    calc (2 : ℤ) ^ (P * (2 * g / K)) * (2 ^ B - 1) ^ g ^ 2 < 2 ^ (P * (2 * g / K)) * (2 ^ B) ^ g ^ 2 := mul_lt_mul_of_pos_left hlt (by positivity)
      _ = 2 ^ (P * (2 * g / K) + g ^ 2 * B) := by rw [← pow_mul, ← pow_add, Nat.mul_comm B]
      _ ≤ 2 ^ bitsOut K g P B := pow_le_pow_right₀ (by norm_num) (le_bitsOut hK0 g P B)
  unfold display
  rw [abs_mul]
  refine lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) (by split_ifs <;> simp)) ?_
  refine lt_of_le_of_lt ((Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ _ fun z hz => abs_term_le h hK0 x L hY γ Θ hΘ hz).trans ?_)) hfinal
  rw [nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hm0 _)
  exact_mod_cast card_settings_le h.is hK0 x γ (hG1 γ)

end Display

/-! ## One entry -/

/-- D·X + M·X^k ≤ c·X^c. -/
theorem poly_le {D M k c X : ℕ} (hX : 1 ≤ X) (hk : k ≤ c) (h1 : 1 ≤ c) (hc : D + M ≤ c) : D * X + M * X ^ k ≤ c * X ^ c :=
  calc D * X + M * X ^ k ≤ D * X ^ c + M * X ^ c := Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) X)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hk))
    _ = (D + M) * X ^ c := by ring
    _ ≤ c * X ^ c := Nat.mul_le_mul_right _ hc

/-- **Proof of Lemma 1, «Cost», first half**, from the coding of a setting of a node of a clique. -/
theorem stEntryCost_of (hTL : StToLists) : StEntryCost := by
  intro K g
  obtain ⟨c₁, h1, hc₁⟩ := tableM_display K g
  obtain ⟨D, hD⟩ : ∃ D, D = 4 * g ^ 2 + 6 * g + 6 := ⟨_, rfl⟩
  refine ⟨(D + 2 * size g + 8) + c₁ * (D + 1) ^ c₁ + c₁, fun hK0 hg N P B τ hN hτ x hx L hL hG1 hY γ Θ hΘ => ?_⟩
  have hnet := asked_isNetworkP N hN
  obtain ⟨e1, e2, -⟩ := hTL K L γ Θ hΘ
  have hΘ' : ∀ γ', γ' ≠ γ → ((fun u : Fin K => if u = γ then [] else copyAt L γ u Θ) γ').length = L := fun γ' hne => by
    simp only [if_neg hne]
    exact e2 γ' hne
  have hγ : (fun u : Fin K => if u = γ then [] else copyAt L γ u Θ) γ = [] := if_pos rfl
  obtain ⟨hrun, -⟩ := hc₁ hK0 _ _ _ N P B 1 _ hnet x hx L hL hG1 hY γ _ hΘ' hγ
  refine ⟨?_, abs_display_lt hnet hK0 hg x L hG1 hY γ _ hΘ'⟩
  rw [e1]
  rw [← tableQ_close] at hrun
  have hw := stSlowDown _ _ _ _ _ _ _ _ _ τ _ hτ ((stClose _ _ _ _ _ _ _ _ _ _).1 hrun)
  refine hw.mono ?_ ?_
  · rw [Nat.mul_one]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  · have hs := size_netInput_le N hN
    rw [← hD] at hs
    have hP := hN.P_pos
    obtain ⟨X, hX⟩ : ∃ X, X = P + B := ⟨_, rfl⟩
    rw [← hX] at hs ⊢
    have a1 : size (netInput N P B) + 2 * size g + 4 * P + B + 4 ≤ (D + 2 * size g + 8) * X := by
      have : (D + 2 * size g + 8) * X = D * X + 2 * size g * X + 8 * X := by ring
      have h2 : 2 * size g * 1 ≤ 2 * size g * X := Nat.mul_le_mul_left _ (by omega)
      omega
    have a2 : c₁ * (size (netInput N P B) + P + B) ^ c₁ ≤ c₁ * (D + 1) ^ c₁ * X ^ c₁ := by
      rw [Nat.mul_assoc, ← Nat.mul_pow]
      refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
      have : (D + 1) * X = D * X + X := by ring
      omega
    exact (Nat.add_le_add a1 a2).trans (poly_le (by omega) (by omega) (by omega) (by omega))

/-- **Proof of Lemma 1, «Cost», first half.** -/
theorem stEntryCost : StEntryCost := stEntryCost_of stToLists

end Printed
