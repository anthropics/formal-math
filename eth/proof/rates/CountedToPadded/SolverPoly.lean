/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedToPadded.Tables
import ToTuring.Lib.Nat2
import ToTuring.Lib.Nat1b

/-! # The solver is polynomial-time

Proof of `SolverOfMachinePolyFrom` (Defs.lean). The certificate of `onTables M` is
`QueryMachine.plug_isPolyT M lookup` over `lookupIsPoly`; its coding of the states is the one that
`solverOfMachine` uses. -/

public section

namespace QueryMachines.Bridge.Proof

open Groundwork Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed

/-- Rounding up is polynomial-time. -/
theorem ceilMul_poly {α : Type} [Enc α] {a b n : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hn : PolyT n) : PolyT fun x => ceilMul (a x) (b x) (n x) := by
  unfold ceilMul; fun_prop

/-- The exponent is polynomial-time. -/
theorem needOf_poly {num : U × U → ℕ × ℕ} (hnum : PolyT num) (C₀ : ℕ) : PolyT (needOf num C₀) := by
  have hK : PolyT fun x : (U × U) × U × U => x.1.2.length := by fun_prop
  have hlam : PolyT fun x : (U × U) × U × U => x.2.1.length := by fun_prop
  have hB : PolyT fun x : (U × U) × U × U => x.2.2.length := by fun_prop
  have hn : PolyT fun x : (U × U) × U × U => num x.1 := comp hnum (by fun_prop)
  exact PolyT.add (PolyT.add (ceilMul_poly (fst hn) (snd hn) (PolyT.mul (PolyT.pow_const hK 2) hlam))
    (PolyT.mul (PolyT.mul (PolyT.const C₀) (PolyT.pow_const hK 2)) (PolyT.size' (PolyT.mul hK (PolyT.add (PolyT.add hlam hB) (PolyT.const 1)))))) (PolyT.const 2)

/-- The certificate of `onTables M`. Its coding of the states is the one in `solverOfMachine`. -/
@[expose, instance_reducible] def onTablesIsPoly (M : QueryMachine TableQuery ℤ (U × U × U) ℤ) [QueryMachine.IsPolyQ M] : IsPolyT (onTables M) :=
  letI := lookupIsPoly
  QueryMachine.plug_isPolyT M lookup

end QueryMachines.Bridge.Proof

namespace QueryMachines.Bridge

open Groundwork Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed Proof

/-- `SolverOfMachinePoly` follows from `RunForPoly`. -/
theorem solverOfMachinePolyFrom : SolverOfMachinePolyFrom := by
  intro hRun M _ num C₀ hnum
  have hneed := needOf_poly hnum C₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := @hRun _ _ _ _ (onTables M) (onTablesIsPoly M)
    have hroom : Unary fun x : U × (U × U) × PInst => 7 * x.1.length + 14 * len x.2.2.2 + 2 :=
      (((Unary.const 7).mul (Unary.of_length (by fun_prop))).add ((Unary.const 14).mul (len_tab_unary.comp (by fun_prop)))).add (Unary.const 2)
    have hbits : PolyT fun x : U × (U × U) × PInst => unary (bitsOfTables x.2.2.2) := Unary.comp bitsOfTables_unary (by fun_prop)
    have hc := PolyT.comp h (PolyT.prodMk (PolyT.prodMk (by fun_prop : PolyT fun x : U × (U × U) × PInst => x.1) hroom)
      (PolyT.prodMk (by fun_prop : PolyT fun x : U × (U × U) × PInst => x.2.2.2) (PolyT.prodMk (by fun_prop : PolyT fun x : U × (U × U) × PInst => x.2.1.1)
        (PolyT.prodMk (by fun_prop : PolyT fun x : U × (U × U) × PInst => x.2.2.1) hbits))))
    refine (PolyT.optionGetD hc (PolyT.const 0)).congr fun x => ?_
    simp only [List.length_replicate]
    rfl
  · exact (Unary.of_length (by fun_prop : PolyT fun i : U × U => i.2) : Unary fun i : U × U => i.2.length)
  · show PolyT fun x : U × (U × U) × U × U => if needOf num C₀ x.2 ≤ x.1.length then some (needOf num C₀ x.2) else none
    generalize needOf num C₀ = f at hneed ⊢
    fun_prop
  · intro b x v h
    replace h : (if needOf num C₀ x ≤ b.length then some (needOf num C₀ x) else none) = some v := h
    split at h
    · exact (Option.some.inj h).symm
    · cases h
  · intro b x h
    exact if_pos h

end QueryMachines.Bridge
