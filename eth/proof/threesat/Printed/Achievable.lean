/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Close
public import Printed.Coding
public import Printed.Absorb
public import QueryMachines.Poly
public import ToTuring.Poly.Brute
import Mathlib.Tactic

/-! # Around Definition 4

The sentences that the paper prints with Definition 4, for `Printed.Achievable`
(PrintedStatement.lean), in which own steps and queries are counted once each.
* `stMono`: «If (K, e) is achievable, so is (K, e₁) for every e₁ ≥ e.»
* `stBrute`, `stHalf`: «Trying all 2^{λK(K−1)/2} choices of one string per edge shows that (K, ½) is
  achievable for every K, so e* ≤ ½.» The count is not made again: with the tables built in,
  `bruteMachine K` is the step machine `Groundwork.brute` of this development on a procedure that
  answers in one step (`bruteMachine_close`), `Groundwork.Prog.bruteE_correct` bounds its steps, and
  `QueryMachines.stClose` reads that number as own steps plus queries.
* `stAnswerEachQuery`: the step that the proof of Lemma 1 makes with Definition 4.
* `eStar_le`, `eStar_nonneg`, `achievable_of_eStar_lt`: what an infimum gives, for the proof of
  «Hence e* = 0». -/

public section

namespace Printed

open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines

/-! ### Monotone in e -/

/-- The same machine and the same constant do for every larger e. -/
theorem AchievedBy.mono {M : CliqueMachine} {Cc K : ℕ} {e e₁ : ℝ} (h : AchievedBy M Cc K e) (he : e ≤ e₁) : AchievedBy M Cc K e₁ := fun lam B W hl hB hW => by
  obtain ⟨T, hr, hT⟩ := h lam B W hl hB hW
  refine ⟨T, hr, hT.trans ?_⟩
  gcongr
  norm_num

/-- «If (K, e) is achievable, so is (K, e₁) for every e₁ ≥ e.» -/
theorem stMono : StMono := fun _ _ _ ⟨hK, h0, M, Cc, hp, hM⟩ he => ⟨hK, h0.trans he, M, Cc, hp, hM.mono he⟩

/-! ### The input in unary, and the answers of the tables -/

/-- The number n in unary has n units. -/
theorem length_unary (n : ℕ) : (unary n).length = n := List.length_replicate

/-- The number n in unary has size 2n + 1. -/
theorem size_unary (n : ℕ) : size (unary n) = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [unary, List.replicate_succ, size_list, List.map_cons, List.sum_cons, size_unit] at ih ⊢
    omega

/-- The tables answer only the queries of Definition 3, and with the entry. -/
theorem tables_eq_some {K lam : ℕ} {W : ℕ → List Bool → ℤ} {x : TableQuery} {v : ℤ} (h : tables K lam W x = some v) :
    x.1 < K ∧ x.2 ∈ words ((K - 1) * lam) ∧ v = W x.1 x.2 := by
  change (if x.1 < K ∧ x.2.length = (K - 1) * lam then some (W x.1 x.2) else none) = some v at h
  by_cases hx : x.1 < K ∧ x.2.length = (K - 1) * lam
  · rw [if_pos hx] at h
    exact ⟨hx.1, mem_words.2 hx.2, (Option.some.inj h).symm⟩
  · rw [if_neg hx] at h
    cases h

/-! ### Brute force -/

/-- Brute force has polynomial-time steps. -/
theorem bruteMachine_poly (K : ℕ) : (bruteMachine K).PolyTimeSteps := by
  have hl : Unary fun c : List Unit × List Unit => c.1.length := Unary.of_length (by fun_prop)
  have : QueryMachine.IsPolyQ (askTable : QueryMachine TableQuery ℤ ((List Unit × List Unit) × IQ) ℤ) := QueryMachine.IsPolyQ.query (by unfold toTable; fun_prop)
  have := QueryMachine.IsPolyQ.mapIn (bruteQuery_polyT K hl (dflt := nilC) (by unfold nilC; fun_prop)) (askTable : QueryMachine TableQuery ℤ ((List Unit × List Unit) × IQ) ℤ)
  have := QueryMachine.IsPolyQ.prodRange (N := Function.const ((List Unit × List Unit) × ℕ) K)
    (QueryMachine.mapIn (bruteQuery K (fun c : List Unit × List Unit => c.1.length) nilC) askTable) (by unfold Function.const; fun_prop)
  exact ⟨QueryMachine.IsPolyQ.sumRange _ (bruteBound_polyT K hl)⟩

/-- «Trying all 2^{λK(K−1)/2} choices of one string per edge»: brute force does what Definition 4
asks for (K, ½). -/
theorem bruteMachine_achieves (K : ℕ) (hK : 2 ≤ K) : ∃ Cc : ℕ, AchievedBy (bruteMachine K) Cc K (1 / 2) := by
  obtain ⟨A, hA⟩ := bruteE_correct K
  obtain ⟨Cc, hle, hCc⟩ := absorb_le A (4 * K + size K + 8)
  refine ⟨Cc, fun lam B W hl hB hW => ?_⟩
  have h := hA (List Unit × List Unit) (fun c => c.1.length) (askTable.close (tables K lam W)) (unary lam, unary B) B 1
    (size (unary lam, unary B) + size K + K * (2 * lam + 2) + B + 3) (listTables K W)
  simp only [length_unary] at h
  obtain ⟨T, hr, hT⟩ := h hl le_rfl (stAskServes _ K lam B W _ hW)
  refine ⟨T, (QueryMachines.stClose _ _ _ _ _ _ _ _ _ _).1 ?_, ?_⟩
  · rw [bruteMachine_close, stCliqueValue K lam W hK hl]
    have hs : size (unary lam, unary B) = 2 * lam + 1 + (2 * B + 1) := by simp only [size_prod, size_unary]
    have e : (4 * K + size K + 8) * (B + lam) = 4 * (K * (B + lam)) + size K * (B + lam) + 8 * (B + lam) := by ring
    have a1 : K * lam ≤ K * (B + lam) := Nat.mul_le_mul_left _ (by omega)
    have a2 : K ≤ K * (B + lam) := Nat.le_mul_of_pos_right _ (by omega)
    have a3 : size K ≤ size K * (B + lam) := Nat.le_mul_of_pos_right _ (by omega)
    have a4 : K * (2 * lam + 2) = 2 * (K * lam) + 2 * K := by ring
    exact hr.mono le_rfl (hCc (B + lam) _ _ (by omega) (by rw [hs, e, a4]; omega) (by rw [hs, e]; omega))
  · have hx : (1 : ℝ) ≤ (B : ℝ) + lam := by exact_mod_cast (by omega : 1 ≤ B + lam)
    rw [Nat.cast_one, mul_one] at hT
    exact hT.trans (absorb_time hle (by positivity) hx)

/-- «(K, ½) is achievable», by brute force. -/
theorem stBrute : StBrute := fun K hK => ⟨bruteMachine_poly K, bruteMachine_achieves K hK⟩

/-! ### e* -/

/-- «(K, ½) is achievable for every K». -/
theorem achievable_half {K : ℕ} (hK : 2 ≤ K) : Achievable K (1 / 2) :=
  have ⟨Cc, h⟩ := bruteMachine_achieves K hK
  ⟨hK, by norm_num, bruteMachine K, Cc, bruteMachine_poly K, h⟩

/-- ½ is one of the numbers of which e* is the infimum. -/
theorem half_mem : (1 / 2 : ℝ) ∈ {e : ℝ | ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e} :=
  fun K₀ => ⟨max K₀ 2, le_max_left _ _, achievable_half (le_max_right _ _)⟩

/-- All of these numbers are at least 0, since e ≥ 0 is a part of Definition 4. -/
theorem nonneg_of_mem {e : ℝ} (h : e ∈ {e : ℝ | ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e}) : 0 ≤ e :=
  have ⟨_, _, hA⟩ := h 0
  hA.2.1

/-- If (K, e) is achievable for infinitely many K, then e* ≤ e. -/
theorem eStar_le {e : ℝ} (h : ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e) : eStar ≤ e := csInf_le ⟨0, fun _ he => nonneg_of_mem he⟩ h

/-- 0 ≤ e*. -/
theorem eStar_nonneg : 0 ≤ eStar := le_csInf ⟨1 / 2, half_mem⟩ fun _ he => nonneg_of_mem he

/-- If e > e*, then (K, e) is achievable for infinitely many K. -/
theorem achievable_of_eStar_lt {e : ℝ} (he : eStar < e) (K₀ : ℕ) : ∃ K, K₀ ≤ K ∧ Achievable K e := by
  obtain ⟨e', he', hlt⟩ := exists_lt_of_csInf_lt ⟨1 / 2, half_mem⟩ he
  obtain ⟨K, hK, hA⟩ := he' K₀
  exact ⟨K, hK, stMono K e' e hA hlt.le⟩

/-- «… shows that (K, ½) is achievable for every K, so e* ≤ ½.» -/
theorem stHalf : StHalf := ⟨fun _ hK => achievable_half hK, eStar_le half_mem, eStar_nonneg⟩

/-! ### «Answer each of its at most … queries by computing the entry» -/

/-- The machine of Definition 4 asks at most as many queries as it takes operations; and with each
query answered by a step machine within t steps it takes at most 3·t times as many steps (t + 2 ≤ 3t
steps for a query, one for an own step). -/
theorem stAnswerEachQuery : StAnswerEachQuery := fun M Cc K e h lam B W hl hB hW => by
  obtain ⟨T, hw, hT⟩ := h lam B W hl hB hW
  obtain ⟨own, L, hr, hle⟩ := QueryMachines.stQueriesLe _ _ _ _ M _ _ _ _ _ hw
  refine ⟨⟨own, L, hr, le_trans (by exact_mod_cast (by omega : L.length ≤ T)) hT⟩, fun C _ R c t S ht hR => ?_⟩
  have hp := QueryMachines.stPlug _ _ C _ _ M R (tables K lam W) c _ own _ S L _ (fun _ => t) hr fun x _ v hv => by
    obtain ⟨h1, h2, rfl⟩ := tables_eq_some hv
    exact hR x.1 h1 x.2 h2
  refine ⟨_, hp, ?_⟩
  rw [QueryMachine.sum_map_const]
  have h1 : own + L.length * (t + 2) ≤ T * (3 * t) :=
    calc own + L.length * (t + 2) ≤ own * (3 * t) + L.length * (3 * t) := Nat.add_le_add (Nat.le_mul_of_pos_right _ (by omega)) (Nat.mul_le_mul_left _ (by omega))
      _ = (own + L.length) * (3 * t) := by ring
      _ ≤ T * (3 * t) := Nat.mul_le_mul_right _ hle
  calc ((own + L.length * (t + 2) : ℕ) : ℝ) ≤ ((T * (3 * t) : ℕ) : ℝ) := by exact_mod_cast h1
    _ = 3 * (T : ℝ) * t := by push_cast; ring
    _ ≤ 3 * (Cc * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * lam) * ((B : ℝ) + lam) ^ Cc) * t := by gcongr

end Printed
