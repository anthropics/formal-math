/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.Within
public import Printed.Coding
import Mathlib.Tactic

/-! # Brute force, at any price of a query

Proof of Theorem A (b), the case ℓ = 0: brute force sums 2^{λK₀(K₀−1)/2} ≤ 2^{e₀K₀²λ} terms, each at
a cost of at most (K₀(λ+B))^{C₅}. The machine is `Printed.bruteMachine K`: the sum over all choices
of one string per edge of the product over the nodes of the table entries.
A term costs K queries and K + 1 own steps. So if a query costs tq operations, the whole costs
2^{λK(K−1)/2}·(K(tq + 1) + 1), for every tq, also 0 (`brute_within`); all numbers are explicit, for
every K (also K = 1).
The count follows `Groundwork.brute_runs` (proof/machines/StepMachines/Prog/Brute.lean), which is
the same count for step machines. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed

/-- The value of the clique as the network of Definition 3 is the sum over one string per edge, for
every K and λ. By `Value.stCliqueValue`, which has no condition on K and λ. (`Printed.stCliqueValue`
says the same for K ≥ 2 and λ ≥ 1.) -/
theorem clique_value_eq (K lam : ℕ) (W : ℕ → List Bool → ℤ) : (clique K lam fun w => W w.val).value = Paper.cliqueValue lam (listTables K W) := by
  refine (Eq.trans ?_ (Value.stCliqueValue K lam (listTables K W)) : _ = Paper.cliqueValue lam (listTables K W))
  unfold Net.value
  refine sum_congr rfl fun z hz => congrArg₂ (· * ·) (prod_congr rfl fun a _ => ?_) rfl
  have ha : (z a).length = (K - 1) * lam := mem_words.1 (Fintype.mem_piFinset.1 hz a)
  change W a.val (z a) = W a.val (List.ofFn fun u : Fin K => if u = a then [] else copyAt lam a u (z a)).flatten
  rw [flatten_copies a ha]

/-- Brute force on K nodes, if a query to the tables costs tq operations. The input is (λ, B) in
unary. -/
theorem brute_within (K : ℕ) (c : List Unit × List Unit) (W : ℕ → List Bool → ℤ) (hW : ∀ w < K, ∀ z ∈ words ((K - 1) * c.1.length), |W w z| < 2 ^ c.2.length) (tq : ℕ) :
    (bruteMachine K).Within (tables K c.1.length W) (fun _ => tq) c (2 ^ (K * (K - 1) / 2 * c.1.length) * (K * (tq + 1) + 1))
      (3 * size c + 3 * (K * (K - 1) / 2 * c.1.length) + 2 * (c.2.length * K) + 2 * size K + K * (2 * c.1.length + 2) + c.2.length + 13) (clique K c.1.length fun w => W w.val).value := by
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = c.1.length := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = c.2.length := ⟨_, rfl⟩
  rw [← hlam, ← hB] at hW ⊢
  obtain ⟨n, hn⟩ : ∃ n, n = K * (K - 1) / 2 * lam := ⟨_, rfl⟩
  rw [← hn]
  -- the strings at the node v under the choice number y
  let θ : ℕ → Fin K → Fin K → List Bool := fun y v => star (labelling K lam [] (toWord n y)) v
  have hθ : ∀ y (v u : Fin K), u ≠ v → (θ y v u).length = lam := fun y v u hu => by
    change (star (labelling K lam [] (toWord n y)) v u).length = lam
    rw [star_labelling_ne _ _ _ _ hu]
    refine length_block ?_
    rw [length_toWord, hn]
    have hne : v.1 ≠ u.1 := fun h => hu (Fin.ext h.symm)
    exact Nat.mul_le_mul_right _ (tri_lt (min_lt_max.2 hne) (max_lt v.2 u.2))
  have hθ0 : ∀ y (v : Fin K), θ y v v = [] := fun y v => star_labelling_self _ _ _ _ v
  have hθle : ∀ y (v u : Fin K), (θ y v u).length ≤ lam := fun y v u => by
    by_cases hu : u = v
    · rw [hu, hθ0]
      exact Nat.zero_le _
    · exact (hθ y v u hu).le
  let val : ℕ → ℕ → ℤ := fun y v => if h : v < K then listTables K W ⟨v, h⟩ (θ y ⟨v, h⟩) else 1
  have hval : ∀ y (v : Fin K), val y v.val = listTables K W v (θ y v) := fun y v => by simp only [val, v.2, dif_pos]
  have hfl : ∀ y (v : Fin K), (List.ofFn (θ y v)).flatten.length = (K - 1) * lam := fun y v => length_flatten_ofFn v _ (hθ y v) (hθ0 y v)
  have hb : ∀ y (v : Fin K), |val y v.val| < 2 ^ B := fun y v => by
    rw [hval]
    exact hW v.val v.2 _ (mem_words.2 (hfl y v))
  have hb' : ∀ y, ∀ v < K, (val y v).natAbs ≤ 2 ^ B := fun y v hv => by
    have := hb y ⟨v, hv⟩
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this.le
  -- one entry: one query
  have hq : ∀ y (v : Fin K), (QueryMachine.mapIn (bruteQuery K (fun c : List Unit × List Unit => c.1.length) nilC) askTable).Within (tables K lam W) (fun _ => tq) ((c, y), v.val) tq
      (size c + size K + (K * (2 * lam + 2) + 1) + (B + 1) + 1) (val y v.val) := fun y v => by
    have e : bruteQuery K (fun c : List Unit × List Unit => c.1.length) nilC ((c, y), v.val) = (c, (v.val, List.ofFn (θ y v))) := by
      change (c, query0 K c.1.length [] (toWord (K * (K - 1) / 2 * c.1.length) y) v.val) = _
      rw [← hlam, ← hn, query0_eq]
    have hO : tables K lam W (toTable (bruteQuery K (fun c : List Unit × List Unit => c.1.length) nilC ((c, y), v.val)).2) = some (val y v.val) := by
      rw [e, hval]
      exact if_pos ⟨v.2, hfl y v⟩
    refine (mapIn_within (query_within (h := fun x : (List Unit × List Unit) × IQ => toTable x.2) (w := fun _ => tq) hO)).mono le_rfl ?_
    rw [e]
    have h1 := size_ofFn_le (θ y v) (hθle y v)
    have h2 := size_entry (hb y v)
    have h3 := Nat.size_le_size v.2.le
    simp only [size_prod, size_nat] at h1 h2 h3 ⊢
    omega
  -- one term: K entries
  have hin : ∀ y < 2 ^ n, (QueryMachine.prodRange (Function.const ((List Unit × List Unit) × ℕ) K) (QueryMachine.mapIn (bruteQuery K (fun c : List Unit × List Unit => c.1.length) nilC) askTable)).Within
      (tables K lam W) (fun _ => tq) (c, y) (K * (tq + 1)) (size c + size (2 ^ n) + size K + (size ((2 ^ B) ^ K) + (size c + size K + (K * (2 * lam + 2) + 1) + (B + 1) + 1)) + 1)
      (∏ v ∈ range K, val y v) := fun y hy => by
    have := prodRange_within (N := Function.const ((List Unit × List Unit) × ℕ) K) (a := (c, y)) (fun _ => tq) (val y) (2 ^ B) _ Nat.one_le_two_pow (fun v hv => hq y ⟨v, hv⟩) (hb' y)
    simp only [Function.const_apply] at this
    refine this.mono (by simp) ?_
    have := Nat.size_le_size hy.le
    simp only [size_prod, size_nat]
    omega
  -- all terms
  have hout : (bruteMachine K).Within (tables K lam W) (fun _ => tq) c (∑ _y ∈ range (2 ^ n), (K * (tq + 1) + 1))
      (size c + size (2 ^ n) + (size (2 ^ n * (2 ^ B) ^ K) + (size c + size (2 ^ n) + size K + (size ((2 ^ B) ^ K) + (size c + size K + (K * (2 * lam + 2) + 1) + (B + 1) + 1)) + 1)) + 1)
      (∑ y ∈ range (2 ^ n), ∏ v ∈ range K, val y v) := by
    have e : bruteBound K (fun c : List Unit × List Unit => c.1.length) c = 2 ^ n := by rw [hn, hlam]; rfl
    have := sumRange_within (N := bruteBound K fun c : List Unit × List Unit => c.1.length) (a := c) (fun _ => K * (tq + 1)) (fun y => ∏ v ∈ range K, val y v) ((2 ^ B) ^ K) _
      (fun y hy => hin y (e ▸ hy)) (fun y _ => Stepped.natAbs_prod_le (val y) (2 ^ B) K (hb' y))
    rw [e] at this
    exact this
  have e1 : ∑ _y ∈ range (2 ^ n), (K * (tq + 1) + 1) = 2 ^ n * (K * (tq + 1) + 1) := by simp
  have e2 : ∑ y ∈ range (2 ^ n), ∏ v ∈ range K, val y v = Inst.ZW lam [] (listTables K W) := by
    unfold Inst.ZW
    rw [← sum_blocks_pairs K lam [] fun Λ => ∏ v, listTables K W v (star Λ v), ← hn, ← sum_toWord]
    refine sum_congr rfl fun y _ => ?_
    rw [prod_range]
    exact prod_congr rfl fun v _ => hval y v
  rw [e1, e2] at hout
  rw [clique_value_eq]
  refine hout.mono le_rfl ?_
  rw [← pow_mul, ← pow_add]
  simp only [size_nat, Nat.size_pow]
  omega

end ExplicitCost
