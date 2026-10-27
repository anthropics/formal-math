/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Range
public import StepMachines.Prog.Chunks
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn

/-! Brute force for the sum Z over all labellings of the edges of the complete graph on K nodes:
`brute` computes Z, the sum over all labellings of the product of the tensors'
entries, by a loop over all labellings. A labelling is a counter y below 2^(K(K-1)/2 · λ), read as a
word and cut into
K(K-1)/2 blocks of λ bits. -/

namespace Groundwork

open Finset Stepped

/-- The sum Z, over all labellings of the edges, of the product of the tensors R; the labels are
words of ℓ bits, kept as plain lists. -/
@[expose] public def Inst.ZW {J : Type*} [Fintype J] [LinearOrder J] (ℓ : ℕ) (d : List Bool) (R : Inst J (List Bool)) : ℤ :=
  ∑ Λ ∈ tuples (fun p : J × J => p.1 < p.2) (fun _ => words ℓ) d, ∏ v, R v (star Λ v)

/-- The labelling written by the word w. -/
@[expose] public def labelling (K ℓ : ℕ) (d w : List Bool) : Fin K × Fin K → List Bool :=
  fun p => if p.1 < p.2 then block ℓ (tri p.1 p.2) w else d

/-- The query at the node v: v and the labels of the edges {v,u}, u = 0, …, K-1 (d at u = v). -/
@[expose] public def query0 (K ℓ : ℕ) (d w : List Bool) (v : ℕ) : ℕ × List (List Bool) :=
  (v, (List.range K).map fun u => if u = v then d else block ℓ (tri (min v u) (max v u)) w)

public theorem star_labelling_self (K ℓ : ℕ) (d w : List Bool) (v : Fin K) :
    star (labelling K ℓ d w) v v = d := by
  have : ¬ (pr v v).1 < (pr v v).2 := by simp [pr]
  unfold star labelling
  rw [if_neg this]

public theorem star_labelling_ne (K ℓ : ℕ) (d w : List Bool) {v u : Fin K} (h : u ≠ v) :
    star (labelling K ℓ d w) v u = block ℓ (tri (min v.1 u.1) (max v.1 u.1)) w := by
  have hlt : (pr v u).1 < (pr v u).2 := min_lt_max.2 h.symm
  unfold star labelling
  rw [if_pos hlt]
  rcases le_total v u with h' | h'
  · rw [pr, min_eq_left h', max_eq_right h', min_eq_left (Fin.le_def.1 h'), max_eq_right (Fin.le_def.1 h')]
  · rw [pr, min_eq_right h', max_eq_left h', min_eq_right (Fin.le_def.1 h'), max_eq_left (Fin.le_def.1 h')]

public theorem query0_eq (K ℓ : ℕ) (d w : List Bool) (v : Fin K) :
    query0 K ℓ d w v = (v.1, List.ofFn (star (labelling K ℓ d w) v)) := by
  unfold query0
  congr 1
  refine List.ext_getElem (by simp) fun u h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  have hu : u < K := by simpa using h1
  by_cases huv : u = v.1
  · have : (⟨u, hu⟩ : Fin K) = v := Fin.ext huv
    rw [if_pos huv, this, star_labelling_self]
  · have hne : (⟨u, hu⟩ : Fin K) ≠ v := fun h => huv (by rw [← h])
    rw [if_neg huv, star_labelling_ne K ℓ d w hne]

variable {C : Type} [HasSize C]

/-- The number of labellings. -/
@[expose] public def bruteBound (K : ℕ) (lam : C → ℕ) (c : C) : ℕ := 2 ^ (K * (K - 1) / 2 * lam c)

/-- The query sent to R at the point ((c, y), v): context c, labelling y, node v. -/
@[expose] public def bruteQuery (K : ℕ) (lam : C → ℕ) (dflt : C → List Bool) (x : (C × ℕ) × ℕ) :
    C × ℕ × List (List Bool) :=
  (x.1.1, query0 K (lam x.1.1) (dflt x.1.1) (toWord (K * (K - 1) / 2 * lam x.1.1) x.1.2) x.2)

/-- Brute force: the sum over all labellings of the product over the nodes of the answers of R. R
answers the queries
(context, node, labels at the node). -/
@[expose] public def brute (K : ℕ) (lam : C → ℕ) (dflt : C → List Bool) (R : Stepped (C × ℕ × List (List Bool)) ℤ) :
    Stepped C ℤ :=
  sumRange (bruteBound K lam) (prodRange (Function.const (C × ℕ) K) (mapIn (bruteQuery K lam dflt) R))

/-- `brute` computes Z in 2^(K(K-1)/2 · λ) · (K (t + 1) + 1) steps if R answers every query in t
steps. -/
public theorem brute_runs {K : ℕ} {lam : C → ℕ} {dflt : C → List Bool} {R : Stepped (C × ℕ × List (List Bool)) ℤ}
    {c : C} (Rm : Inst (Fin K) (List Bool)) (t S V : ℕ) (hV : 1 ≤ V)
    (hR : ∀ (v : Fin K) (θ : Fin K → List Bool), (∀ u, u ≠ v → (θ u).length = lam c) → θ v = dflt c →
      R.Runs (c, v.1, List.ofFn θ) t S (Rm v θ) ∧ (Rm v θ).natAbs ≤ V) :
    (brute K lam dflt R).Runs c (2 ^ (K * (K - 1) / 2 * lam c) * (K * (t + 1) + 1))
      (size c + size (2 ^ (K * (K - 1) / 2 * lam c)) + (size (2 ^ (K * (K - 1) / 2 * lam c) * V ^ K) +
        (size c + size (2 ^ (K * (K - 1) / 2 * lam c)) + size K + (size (V ^ K) + S) + 1)) + 1)
      (Inst.ZW (lam c) (dflt c) Rm) := by
  set n := K * (K - 1) / 2 * lam c with hn
  -- the value at the node v under the labelling y
  let val : ℕ → ℕ → ℤ := fun y v =>
    if h : v < K then Rm ⟨v, h⟩ (star (labelling K (lam c) (dflt c) (toWord n y)) ⟨v, h⟩) else 1
  have hq : ∀ y (v : Fin K), R.Runs (c, query0 K (lam c) (dflt c) (toWord n y) v) t S (val y v) ∧
      (val y v).natAbs ≤ V := by
    intro y v
    rw [query0_eq]
    have e : val y v = Rm v (star (labelling K (lam c) (dflt c) (toWord n y)) v) := by
      simp only [val, v.2, dif_pos]
    rw [e]
    refine hR v _ (fun u hu => ?_) ?_
    · rw [star_labelling_ne _ _ _ _ hu]
      refine length_block ?_
      rw [length_toWord]
      have hne : v.1 ≠ u.1 := fun h => hu (Fin.ext h.symm)
      exact Nat.mul_le_mul_right _ (tri_lt (min_lt_max.2 hne) (max_lt v.2 u.2))
    · exact star_labelling_self _ _ _ _ v
  have hin : ∀ y < 2 ^ n, (prodRange (Function.const (C × ℕ) K) (mapIn (bruteQuery K lam dflt) R)).Runs
      (c, y) (K * (t + 1)) (size c + size (2 ^ n) + size K + (size (V ^ K) + S) + 1)
      (∏ v ∈ range K, val y v) := by
    intro y hy
    have := prodRange_runs (N := Function.const (C × ℕ) K) (a := (c, y))
      (M := mapIn (bruteQuery K lam dflt) R)
      (fun _ => t) (val y) V S hV
      (fun v hv => mapIn_runs (hq y ⟨v, hv⟩).1) (fun v hv => (hq y ⟨v, hv⟩).2)
    simp only [Function.const_apply] at this
    refine this.mono (by simp) ?_
    have := Nat.size_le_size hy.le
    simp only [size_prod, size_nat]; omega
  have hout := sumRange_runs (N := bruteBound K lam) (a := c)
    (fun _ => K * (t + 1)) (fun y => ∏ v ∈ range K, val y v) (V ^ K) _ hin
    (fun y _ => natAbs_prod_le (val y) V K fun v hv => (hq y ⟨v, hv⟩).2)
  have e1 : ∑ y ∈ range (2 ^ n), (K * (t + 1) + 1) = 2 ^ n * (K * (t + 1) + 1) := by simp
  have e2 : ∑ y ∈ range (2 ^ n), ∏ v ∈ range K, val y v = Inst.ZW (lam c) (dflt c) Rm := by
    unfold Inst.ZW
    rw [← sum_blocks_pairs K (lam c) (dflt c) fun Λ => ∏ v, Rm v (star Λ v), ← sum_toWord]
    refine sum_congr rfl fun y _ => ?_
    rw [prod_range]
    refine prod_congr rfl fun v _ => ?_
    simp only [val, v.2, dif_pos]
    rfl
  rw [← e1, ← e2]
  exact hout

/-- The same with |R| ≤ 2^B and the size bound written out. -/
public theorem brute_runs_pow {K : ℕ} {lam : C → ℕ} {dflt : C → List Bool}
    {R : Stepped (C × ℕ × List (List Bool)) ℤ} {c : C} (Rm : Inst (Fin K) (List Bool)) (t S B : ℕ)
    (hR : ∀ (v : Fin K) (θ : Fin K → List Bool), (∀ u, u ≠ v → (θ u).length = lam c) → θ v = dflt c →
      R.Runs (c, v.1, List.ofFn θ) t S (Rm v θ) ∧ (Rm v θ).natAbs ≤ 2 ^ B) :
    (brute K lam dflt R).Runs c (2 ^ (K * (K - 1) / 2 * lam c) * (K * (t + 1) + 1))
      (2 * size c + 3 * (K * (K - 1) / 2 * lam c) + 2 * (B * K) + size K + S + 10)
      (Inst.ZW (lam c) (dflt c) Rm) := by
  refine (brute_runs Rm t S (2 ^ B) Nat.one_le_two_pow hR).mono le_rfl ?_
  rw [← pow_mul, ← pow_add]
  simp only [size_nat, Nat.size_pow]
  omega

end Groundwork
