/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Occ.Defs
import GraphProblems.Engine
import CountKSat.InOut
import VariableBound.Paper.Rename.Math
import ToTuring.Lib.List3
import ToTuring.Lib.Unary
import ToTuring.Lib.Int
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi

/-! # Variables that do not occur: «Z·2^{n'}» (proofs)

Every statement of proof/consequences/Occ/Defs.lean is proved here.
* `stSameAsFin`: for a formula φ with variables in `Fin N`, the variables that occur in
  `Decode.toN φ` are the values of the variables that occur in φ (`occEquiv`); carrying assignments
  along this bijection gives the equality of the two counts.
* `stCountOcc`: a formula on x₀ … xₙ₋₁ is `Decode.toN φ` for some φ (`GraphProblems.exists_toN`);
  its count on n variables is `SatK.numSat φ` (`CountKSat.stCntToN`); the sentence after Corollary
  11,
  `VariableBound.Rename.numSat_eq`, gives 2^(n−v)·Z in the vocabulary of `Fin N`, and `stSameAsFin`
  carries it over.
* The certificates: v is the length of the list of the variables with repetitions removed; n − v is
  at most n, which is given in unary, so 2^(n−v) is polynomial-time (`PolyT.two_pow`). -/

public section

namespace Occ

open Groundwork Groundwork.Prog CountKSat

/-- The variable v occurs in Φ if and only if some clause of Φ has a literal on v. -/
theorem mem_occurring {Φ : Fml} {v : ℕ} : v ∈ Eight.occurring Φ ↔ ∃ C ∈ Φ, ∃ l ∈ C, l.1 = v := by
  simp only [Eight.occurring, List.mem_toFinset, List.mem_map, List.mem_flatten]
  constructor
  · rintro ⟨l, ⟨C, hC, hl⟩, rfl⟩
    exact ⟨C, hC, l, hl, rfl⟩
  · rintro ⟨C, hC, l, hl, rfl⟩
    exact ⟨l, ⟨C, hC, hl⟩, rfl⟩

/-- In a formula on x₀ … xₙ₋₁ the variables that occur are below n. -/
theorem lt_of_mem_occurring {n : ℕ} {Φ : Fml} (h : Below n Φ) {v : ℕ} (hv : v ∈ Eight.occurring Φ) : v < n := by
  obtain ⟨C, hC, l, hl, rfl⟩ := mem_occurring.1 hv
  exact h C hC l hl

/-- A formula with variables in `Fin N`, read with numbers as variables, is a formula on x₀ …
x_(N−1). -/
theorem below_toN {N : ℕ} (φ : Sat3.CNF N) : Below N (Decode.toN φ) := by
  intro C' hC' l' hl'
  obtain ⟨C, -, rfl⟩ := List.mem_map.1 hC'
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hl'
  exact l.1.2

/-- The number i occurs in `Decode.toN φ` if and only if the variable xᵢ occurs in φ. -/
theorem val_mem_occurring {N : ℕ} (φ : Sat3.CNF N) (i : Fin N) : i.val ∈ Eight.occurring (Decode.toN φ) ↔ MainTheoremForms.Occurs φ i := by
  rw [mem_occurring]
  constructor
  · rintro ⟨C', hC', l', hl', h⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    exact ⟨C, hC, l, hl, Fin.ext h⟩
  · rintro ⟨C, hC, l, hl, rfl⟩
    exact ⟨_, List.mem_map_of_mem hC, _, List.mem_map_of_mem hl, rfl⟩

/-- The bijection between the variables that occur in `Decode.toN φ` (numbers) and the variables
that occur in φ (elements of `Fin N`): the number v goes to x_v. -/
def occEquiv {N : ℕ} (φ : Sat3.CNF N) : {v : ℕ // v ∈ Eight.occurring (Decode.toN φ)} ≃ {i : Fin N // MainTheoremForms.Occurs φ i} where
  toFun v := ⟨⟨v.1, lt_of_mem_occurring (below_toN φ) v.2⟩, (val_mem_occurring φ _).1 v.2⟩
  invFun i := ⟨i.1.val, (val_mem_occurring φ i.1).2 i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- At most n variables occur in a formula on x₀ … xₙ₋₁. -/
theorem stNumOccLe : StNumOccLe := fun n Φ h => by
  have h1 : Eight.occurring Φ ⊆ Finset.range n := fun v hv => Finset.mem_range.2 (lt_of_mem_occurring h hv)
  have h2 := Finset.card_le_card h1
  rwa [Finset.card_range] at h2

/-- For a formula φ with variables in `Fin N`, the number of variables that occur in `Decode.toN φ`
is `MainTheoremForms.numOcc φ`, and the number of assignments of these variables that satisfy
`Decode.toN φ` is `MainTheoremForms.numSatOcc φ`. -/
theorem stSameAsFin : StSameAsFin := fun N φ => by
  constructor
  · rw [numOcc, MainTheoremForms.numOcc, ← Nat.card_congr (occEquiv φ)]
    exact (Nat.subtype_card _ fun _ => Iff.rfl).symm
  · rw [Eight.numSat, MainTheoremForms.numSatOcc, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr ((Equiv.arrowCongr (occEquiv φ) (Equiv.refl Bool)).subtypeEquiv fun a => ?_)
    constructor
    · intro H C hC
      obtain ⟨l', hl', h, ha⟩ := H _ (List.mem_map_of_mem hC)
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
      exact ⟨l, hl, (val_mem_occurring φ l.1).1 h, ha⟩
    · intro H C' hC'
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC'
      obtain ⟨l, hl, h, ha⟩ := H C hC
      exact ⟨_, List.mem_map_of_mem hl, (val_mem_occurring φ l.1).2 h, ha⟩

/-- «Z·2^{n'}»: a formula Φ on x₀ … xₙ₋₁ in which v variables occur has `Eight.numSat Φ`·2^(n−v)
satisfying assignments on x₀ … xₙ₋₁. -/
theorem stCountOcc : StCountOcc := fun n Φ h => by
  obtain ⟨φ, rfl⟩ := GraphProblems.exists_toN h
  rw [stCntToN, VariableBound.Rename.numSat_eq φ, (stSameAsFin n φ).1, (stSameAsFin n φ).2, mul_comm]

/-- «with no clause it has 2^n»: the formula without clauses has 2^n satisfying assignments on x₀ …
xₙ₋₁. -/
theorem stCountNil : StCountNil := fun n => by
  simp [cntN]

/-- If every one of x₀ … xₙ₋₁ occurs in Φ and no other variable does, the number of satisfying
assignments on x₀ … xₙ₋₁ is `Eight.numSat Φ`. -/
theorem stCountAllOccur : StCountAllOccur := fun n Φ h h2 => by
  have h3 : Eight.occurring Φ = Finset.range n := by
    ext v
    rw [Finset.mem_range]
    exact ⟨lt_of_mem_occurring h, fun hv => mem_occurring.2 (h2 v hv)⟩
  rw [stCountOcc n Φ h, numOcc, h3, Finset.card_range, Nat.sub_self, pow_zero, mul_one]

/-- The number of variables that occur in Φ, written in unary, is computed from Φ in polynomial
time: list the variables of all literals, remove repetitions, take the length. -/
theorem stNumOccCert : StNumOccCert := by
  have h : Unary fun Φ : Fml => ((Φ.flatten.map fun l => l.1).dedup).length := Unary.of_length (by fun_prop)
  exact PolyT.congr h fun Φ => by rw [numOcc, Eight.occurring, List.card_toFinset]

/-- The number of variables of Φ that occur, as a number, is computed from ((n in unary, Φ), Z) in
polynomial time. -/
theorem numOcc_polyT : PolyT fun q : (List Unit × Fml) × ℤ => numOcc q.1.2 :=
  Unary.poly (Unary.comp (f := numOcc) stNumOccCert (h := fun q : (List Unit × Fml) × ℤ => q.1.2) (by fun_prop))

/-- n − v in unary is computed from ((n in unary, Φ), Z) in polynomial time: it is at most n. -/
theorem free_unary : Unary fun q : (List Unit × Fml) × ℤ => q.1.1.length - numOcc q.1.2 :=
  Unary.of_le (g := fun q : (List Unit × Fml) × ℤ => q.1.1.length) (Unary.of_length (by fun_prop))
    (PolyT.sub (Unary.poly (Unary.of_length (by fun_prop))) numOcc_polyT) fun _ => Nat.sub_le _ _

/-- 2^(n−v) is computed from ((n in unary, Φ), Z) in polynomial time. -/
theorem twoPowFree_polyT : PolyT fun q : (List Unit × Fml) × ℤ => 2 ^ (q.1.1.length - numOcc q.1.2) :=
  PolyT.two_pow free_unary

/-- From ((n in unary, Φ), Z) the number Z·2^(n−v) is computed in polynomial time. -/
theorem stTimesFreeCert : StTimesFreeCert :=
  PolyT.mul (f := fun q : (List Unit × Fml) × ℤ => q.2.toNat) (PolyT.toNat (by fun_prop)) twoPowFree_polyT

end Occ
