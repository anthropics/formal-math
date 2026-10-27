/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Count
public import StepMachines.Prog.Walk
public import StepMachines.Prog.Comb
public import StepMachines.Prog.Decode
public import StepMachines.Prog.Sat
public import StepMachines.Math.SparsifyTree
public import KSatStatement
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import all StepMachines.Prog.Sat

/-! k-SAT in c·2^{δn} steps as a program: decode the input, walk the sparsification tree
depth-first, test every leaf.

This file follows `proof/machines/StepMachines/Prog/Sat.lean` (the same for 3-SAT) line by line,
with the width 3 replaced by k ≥ 1. The decoder, the step and the
root of the tree are parameters here; what is needed of the last two is the definition `Sparsifies`.
The result is `sat_correct`. -/

namespace Groundwork.Prog.SatTopK

open Groundwork.Sparsify (leaves)

/-- The formula written in the input, as read by `dec`. -/
@[expose] public def decF (dec : List Bool → ℕ × Fml) (x : List Bool) : Fml := (dec x).2

/-- The k-SAT machine: decode the input by `dec`, answer false if there is an empty clause,
otherwise walk the tree of `step` from `root`
and answer true iff some leaf passes the test. M is the test of a leaf (a count that is positive iff
the leaf is satisfiable). -/
@[expose] public def satMK (dec : List Bool → ℕ × Fml) (step : Fml → Option (Fml × Fml)) (root : Fml → Fml)
    (M : Stepped Fml ℤ) : Stepped (List Bool) Bool :=
  Stepped.mapIn (decF dec) (Stepped.ite hasNil (Stepped.const false)
    (Stepped.walk step root (Stepped.mapOut M posZ)))

/-- `step` and `root` sparsify width k. For ψ with variables below n and nonempty clauses of at most
k literals, the tree of depth Dd·n has at most
2^{εn} leaves, a leaf has at most Bl·n clauses, ψ is satisfied exactly if some leaf is, and after
every round of the walk the stack holds at most
Dd·n + 1 formulas of at most |ψ|·Sk clauses. -/
@[expose] public def Sparsifies (k : ℕ) (ε : ℝ) (step : Fml → Option (Fml × Fml)) (root : Fml → Fml) (Dd Bl Sk : ℕ) : Prop :=
  ∀ (n : ℕ) (ψ : Fml), (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
    ((leaves step (Dd * n) (root ψ)).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
    (∀ x ∈ leaves step (Dd * n) (root ψ),
      step x = none ∧ x.length ≤ Bl * n ∧ ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧
    (∀ v : ℕ × Bool → Prop, (∀ C ∈ ψ, ∃ a ∈ C, v a) ↔ ∃ x ∈ leaves step (Dd * n) (root ψ), ∀ C ∈ x, ∃ a ∈ C, v a) ∧
    ∀ i, ((Sparsify.round step)^[i] ([root ψ], [])).1.length ≤ Dd * n + 1 ∧
      ∀ x ∈ ((Sparsify.round step)^[i] ([root ψ], [])).1, x.length ≤ ψ.length * Sk ∧
        ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n

/-! ### Sizes -/

/-- A bound on the size of a formula of at most m clauses of at most k literals with variables below
n. -/
theorem size_fml_le {k : ℕ} {x : Fml} {m n : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    size x ≤ m * (k * (n + 2 + 1) + 1 + 1) + 1 :=
  size_list_le hm fun C hC => size_list_le (hx C hC).1 fun l hl => size_lit_le ((hx C hC).2 l hl)

/-- The length of the code: n + 1 bits for n, then k slots of ⌊log₂(2n)⌋ + 1 bits for every clause. -/
public theorem length_enc (k : ℕ) {n : ℕ} (φ : Sat3.CNF n) :
    (SatK.enc k φ).length = n + 1 + φ.length * (k * (Nat.log2 (2 * n) + 1)) := by
  simp [SatK.enc, List.length_flatMap, Nat.add_assoc, Nat.add_comm]

/-- The constant c of `sat_correct`, from the constants of the three size bounds in its proof and
the constant A of the test of a leaf. -/
def cOf (P₁ P₂ Q A : ℕ) : ℕ := P₂ + A * P₁ ^ A + 2 * A + Q + 20

/-- The sizes that occur in the proof of `sat_correct` are at most c·N^c, where N is the length of
the input plus 1. -/
theorem final_bound (P₁ P₂ Q A N : ℕ) (h1 : 1 ≤ N) :
    P₂ * N ^ 3 + A * (P₁ * N ^ 2) ^ A + 4 ≤ cOf P₁ P₂ Q A * N ^ cOf P₁ P₂ Q A ∧
      Q * N ^ 2 + 3 ≤ cOf P₁ P₂ Q A * N ^ cOf P₁ P₂ Q A := by
  have e3 : N ^ 3 ≤ N ^ cOf P₁ P₂ Q A := Nat.pow_le_pow_right h1 (by unfold cOf; omega)
  have e2 : N ^ 2 ≤ N ^ cOf P₁ P₂ Q A := Nat.pow_le_pow_right h1 (by unfold cOf; omega)
  have eA : N ^ (2 * A) ≤ N ^ cOf P₁ P₂ Q A := Nat.pow_le_pow_right h1 (by unfold cOf; omega)
  have e0 : 1 ≤ N ^ cOf P₁ P₂ Q A := Nat.one_le_pow _ _ h1
  generalize N ^ cOf P₁ P₂ Q A = P at e3 e2 eA e0
  have hc : cOf P₁ P₂ Q A * P = P₂ * P + A * P₁ ^ A * P + 2 * A * P + Q * P + 20 * P := by
    unfold cOf; ring
  have h3 : P₂ * N ^ 3 ≤ P₂ * P := Nat.mul_le_mul_left _ e3
  have h2 : Q * N ^ 2 ≤ Q * P := Nat.mul_le_mul_left _ e2
  have hA : A * (P₁ * N ^ 2) ^ A ≤ A * P₁ ^ A * P := by
    rw [mul_pow, ← pow_mul, ← mul_assoc]
    exact Nat.mul_le_mul_left _ eA
  rw [hc]
  constructor <;> omega

/-! ### k-SAT in c·2^{δn} steps -/

/-- Let `step`, `root` sparsify width k with at most 2^{δn/3} leaves of at most Bl·n clauses, let
`dec` decode, and let M return, on m clauses of ≤ k
literals, within A·2^{δ'm} steps (δ'·Bl ≤ δ/3) and size A·(size φ)^A, an integer that is positive
iff φ is satisfiable. Then `satMK dec step root M`
decides every encoded k-CNF on n variables within c·2^{δn} steps and within size polynomial in the
length of the input. -/
public theorem sat_correct {k : ℕ} (hk : 1 ≤ k) {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 ≤ δ')
    {dec : List Bool → ℕ × Fml} {step : Fml → Option (Fml × Fml)} {root : Fml → Fml} {Dd Bl Sk : ℕ}
    (hdec : ∀ (n : ℕ) (φ : Sat3.CNF n), (∀ C ∈ φ, C.length ≤ k) → dec (SatK.enc k φ) = (n, Decode.toN φ))
    (hsp : Sparsifies k (δ / 3) step root Dd Bl Sk) (hδB : δ' * Bl ≤ δ / 3) (M : Stepped Fml ℤ) (A : ℕ)
    (hM : ∀ φ : Fml, (∀ C ∈ φ, C.length ≤ k) →
      ∃ (T : ℕ) (v : ℤ), M.Runs φ T (A * size φ ^ A) v ∧ (0 < v ↔ φ.Sat) ∧
        (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * φ.length)) :
    ∃ c : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
      ∃ (T : ℕ) (b : Bool), (satMK dec step root M).Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) b ∧
        (b = true ↔ Sat3.Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 4 * k + 2 := ⟨_, rfl⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P₁, P₁ = Bl * Q + 1 := ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂, P₂ = (Dd + 1) * (Sk * Q + 2) + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = cOf P₁ P₂ Q A := ⟨_, rfl⟩
  refine ⟨c, fun n φ h3 => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, N = (SatK.enc k φ).length + 1 := ⟨_, rfl⟩
  rw [← hN]
  have h1 : 1 ≤ N := by omega
  have hlen := length_enc k φ
  have hn : n ≤ N := by omega
  have hm : φ.length ≤ N := by
    have hB : 0 < k * (Nat.log2 (2 * n) + 1) := Nat.mul_pos hk (by omega)
    have := Nat.le_mul_of_pos_right φ.length hB
    omega
  obtain ⟨hb1, hb2⟩ := final_bound P₁ P₂ Q A N h1
  rw [← hc] at hb1 hb2
  have hdec' : decF dec (SatK.enc k φ) = Decode.toN φ := by rw [decF, hdec n φ h3.1]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fml, ψ = Decode.toN φ := ⟨_, rfl⟩
  rw [← hψ] at hdec'
  have hψl : ψ.length ≤ N := by rw [hψ, Decode.length_toN]; exact hm
  have hψcl : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
    intro D hD
    obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN (hψ ▸ hD)
    exact ⟨hl ▸ h3.1 C hC, h⟩
  have hq : k * (n + 2 + 1) + 1 + 1 ≤ Q * N := by
    have a1 : k * (n + 2 + 1) ≤ k * (4 * N) := Nat.mul_le_mul_left _ (by omega)
    have a2 : Q * N = k * (4 * N) + 2 * N := by rw [hQ]; ring
    omega
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ h1
  have hN3 : 1 ≤ N ^ 3 := Nat.one_le_pow _ _ h1
  have hc2 : ((A : ℝ) + 2) ≤ (c : ℝ) := by
    have : A + 2 ≤ c := by rw [hc]; unfold cOf; omega
    exact_mod_cast this
  have hδn : 0 ≤ δ * (n : ℝ) := by positivity
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := Real.one_le_rpow one_le_two hδn
  have hnilψ : hasNil ψ = true ↔ [] ∈ φ := by
    rw [← Decode.nil_mem_toN, ← hψ]
    simp [hasNil, List.any_eq_true]
  by_cases hnil : [] ∈ φ
  · refine ⟨1, false, ?_, ?_, ?_⟩
    · have r : (Stepped.ite hasNil (Stepped.const false)
          (Stepped.walk step root (Stepped.mapOut M posZ))).Runs (decF dec (SatK.enc k φ)) 1
          (max (size ψ) (size false) + 1 + 1) false := by
        rw [hdec']
        exact Stepped.ite_runs_true (hnilψ.2 hnil) (Stepped.const_runs false ψ)
      refine (Stepped.mapIn_runs r).mono le_rfl ?_
      have hs := size_fml_le hψl hψcl
      have : N * (k * (n + 2 + 1) + 1 + 1) ≤ Q * N ^ 2 := by
        calc N * (k * (n + 2 + 1) + 1 + 1) ≤ N * (Q * N) := Nat.mul_le_mul_left _ hq
          _ = Q * N ^ 2 := by ring
      rw [size_bool]
      omega
    · simp only [Bool.false_eq_true, false_iff]
      rintro ⟨a, ha⟩
      obtain ⟨l, hl, -⟩ := ha [] hnil
      simp at hl
    · have : (1 : ℝ) ≤ (c : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) A]
      push_cast
      nlinarith
  · have hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
      intro C hC
      refine ⟨?_, hψcl C hC⟩
      rintro rfl
      exact hnil ((Decode.nil_mem_toN φ).1 (hψ ▸ hC))
    obtain ⟨t1, t2, t3, t4⟩ := hsp n ψ hψne
    obtain ⟨L, hL⟩ : ∃ L, L = leaves step (Dd * n) (root ψ) := ⟨_, rfl⟩
    rw [← hL] at t1 t2 t3
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 3 * n) := ⟨_, rfl⟩
    have hE0 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
    have hLE : (L.length : ℝ) ≤ E := by rw [hE]; exact t1
    have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    have hT : ∀ x ∈ L, (Stepped.mapOut M posZ).Runs x ⌊(A : ℝ) * E⌋₊ (A * (P₁ * N ^ 2) ^ A)
        (decide (Fml.Sat x)) := by
      intro x hx
      obtain ⟨-, hxl, hxc⟩ := t2 x hx
      obtain ⟨T, v, r, hv, hTle⟩ := hM x fun C hC => (hxc C hC).1
      have e : decide (Fml.Sat x) = posZ v := by
        rw [posZ]; exact decide_eq_decide.2 hv.symm
      rw [e]
      refine (Stepped.mapOut_runs r).mono (Nat.le_floor (hTle.trans ?_))
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ A))
      · refine mul_le_mul_of_nonneg_left ?_ hA0
        rw [hE]
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have hxl' : (x.length : ℝ) ≤ (Bl : ℝ) * n := by exact_mod_cast hxl
        calc δ' * x.length ≤ δ' * ((Bl : ℝ) * n) := mul_le_mul_of_nonneg_left hxl' hδ'
          _ = δ' * Bl * n := by ring
          _ ≤ δ / 3 * n := mul_le_mul_of_nonneg_right hδB (Nat.cast_nonneg n)
      · refine (size_fml_le hxl hxc).trans ?_
        calc Bl * n * (k * (n + 2 + 1) + 1 + 1) + 1
            ≤ Bl * N * (Q * N) + 1 :=
              Nat.succ_le_succ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hn) hq)
          _ = Bl * Q * N ^ 2 + 1 := by ring
          _ ≤ Bl * Q * N ^ 2 + N ^ 2 := Nat.add_le_add_left hN2 _
          _ = P₁ * N ^ 2 := by rw [hP₁]; ring
    have hS : ∀ i, size ((Sparsify.round step)^[i] ([root ψ], [])).1 ≤ P₂ * N ^ 3 := by
      intro i
      obtain ⟨s1, s2⟩ := t4 i
      have hf : ∀ x ∈ ((Sparsify.round step)^[i] ([root ψ], [])).1, size x ≤ (Sk * Q + 1) * N ^ 2 := by
        intro x hx
        refine (size_fml_le (s2 x hx).1 (s2 x hx).2).trans ?_
        calc ψ.length * Sk * (k * (n + 2 + 1) + 1 + 1) + 1
            ≤ N * Sk * (Q * N) + 1 := Nat.succ_le_succ (Nat.mul_le_mul (Nat.mul_le_mul_right _ hψl) hq)
          _ = Sk * Q * N ^ 2 + 1 := by ring
          _ ≤ Sk * Q * N ^ 2 + N ^ 2 := Nat.add_le_add_left hN2 _
          _ = (Sk * Q + 1) * N ^ 2 := by ring
      refine (size_list_le s1 hf).trans ?_
      have hp : Dd * n + 1 ≤ (Dd + 1) * N := by
        have a1 : Dd * n ≤ Dd * N := Nat.mul_le_mul_left _ hn
        have a3 : (Dd + 1) * N = Dd * N + N := by ring
        omega
      have hp2 : (Sk * Q + 1) * N ^ 2 + 1 ≤ (Sk * Q + 2) * N ^ 2 := by
        have a3 : (Sk * Q + 2) * N ^ 2 = (Sk * Q + 1) * N ^ 2 + N ^ 2 := by ring
        omega
      calc (Dd * n + 1) * ((Sk * Q + 1) * N ^ 2 + 1) + 1
          ≤ (Dd + 1) * N * ((Sk * Q + 2) * N ^ 2) + 1 := Nat.succ_le_succ (Nat.mul_le_mul hp hp2)
        _ = (Dd + 1) * (Sk * Q + 2) * N ^ 3 + 1 := by ring
        _ ≤ (Dd + 1) * (Sk * Q + 2) * N ^ 3 + N ^ 3 := Nat.add_le_add_left hN3 _
        _ = P₂ * N ^ 3 := by rw [hP₂]; ring
    have w := Stepped.walk_runs step (root := root) (T := Stepped.mapOut M posZ) (Dd * n) ψ
      (fun x hx => (t2 x (hL ▸ hx)).1) (fun x => decide (Fml.Sat x)) ⌊(A : ℝ) * E⌋₊ (A * (P₁ * N ^ 2) ^ A)
      (P₂ * N ^ 3) (fun x hx => hT x (hL ▸ hx)) hS
    rw [← hL] at w
    refine ⟨L.length * (⌊(A : ℝ) * E⌋₊ + 2), L.any fun x => decide (Fml.Sat x), ?_, ?_, ?_⟩
    · have r : (Stepped.ite hasNil (Stepped.const false)
          (Stepped.walk step root (Stepped.mapOut M posZ))).Runs (decF dec (SatK.enc k φ))
          (L.length * (⌊(A : ℝ) * E⌋₊ + 2))
          (P₂ * N ^ 3 + (1 + (A * (P₁ * N ^ 2) ^ A + 1)) + 1 + 1)
          (L.any fun x => decide (Fml.Sat x)) := by
        rw [hdec']
        exact Stepped.ite_runs_false (by simpa using fun h => hnil (hnilψ.1 h)) w
      exact (Stepped.mapIn_runs r).mono le_rfl (by omega)
    · rw [← Decode.satN_toN, ← hψ]
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨x, hx, a, ha⟩
        exact ⟨a, (t3 fun l => a l.1 = l.2).2 ⟨x, hx, ha⟩⟩
      · rintro ⟨a, ha⟩
        obtain ⟨x, hx, h⟩ := (t3 fun l => a l.1 = l.2).1 ha
        exact ⟨x, hx, a, h⟩
    · have hfl : ((⌊(A : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (A : ℝ) * E := Nat.floor_le (by positivity)
      have hEE : E * E ≤ (2 : ℝ) ^ (δ * n) := by
        rw [hE, ← Real.rpow_add two_pos]
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        nlinarith
      have hE00 : 0 ≤ E := by linarith
      push_cast
      calc (L.length : ℝ) * (((⌊(A : ℝ) * E⌋₊ : ℕ) : ℝ) + 2)
          ≤ E * ((A : ℝ) * E + 2 * E) :=
            mul_le_mul hLE (by linarith) (by positivity) hE00
        _ = ((A : ℝ) + 2) * (E * E) := by ring
        _ ≤ (c : ℝ) * (2 : ℝ) ^ (δ * n) :=
            mul_le_mul hc2 hEE (by positivity) (Nat.cast_nonneg _)

end Groundwork.Prog.SatTopK
