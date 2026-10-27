/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Paper.Rename.Defs
import ClauseBound.Alg.Decode

/-! # Renaming the variables that occur is polynomial-time

`renc_polyT : PolyT renc`. Every step of the program is an operation on lists for which
proof/machines/ToTuring/Lib has a closure lemma. -/

public section

namespace VariableBound.Rename

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg

variable {α : Type} [Enc α]

/-- The list of the variables that occur is polynomial-time. -/
theorem occL_polyT {ψ : α → Fml} (hψ : PolyT ψ) : PolyT fun x => occL (ψ x) := by
  unfold occL
  fun_prop

/-- Replacing every variable by its position in a list is polynomial-time. -/
theorem renL_polyT {L : α → List ℕ} {ψ : α → Fml} (hL : PolyT L) (hψ : PolyT ψ) : PolyT fun x => renL (L x) (ψ x) := by
  unfold renL
  fun_prop

/-- The renamed formula is polynomial-time. -/
theorem renF_polyT {ψ : α → Fml} (hψ : PolyT ψ) : PolyT fun x => renF (ψ x) := by
  have h1 := occL_polyT hψ
  have h2 := renL_polyT h1 hψ
  unfold renF
  fun_prop

/-- The number of a slot is polynomial-time. -/
theorem slotN_polyT {o : α → Option (ℕ × Bool)} (ho : PolyT o) : PolyT fun x => slotN (o x) := by
  unfold slotN
  fun_prop

/-- Writing (k, n, ψ) as a bit string is polynomial-time, with k and n in unary. -/
theorem encN_polyT {ku : α → U} {d : α → U × Fml} (hk : PolyT ku) (hd : PolyT d) : PolyT fun x => encN (ku x) (d x) := by
  have hk' : Unary fun x => (ku x).length := Unary.of_length hk
  have hw : Unary fun x => Nat.log2 (2 * (d x).1.length) + 1 :=
    Unary.of_le (g := fun x => 2 * (d x).1.length + 1) (((Unary.const 2).mul (Unary.of_length hd.fst)).add (Unary.const 1)) (by fun_prop) fun x => by
      have := Nat.log2_le_self (2 * (d x).1.length)
      omega
  have hr1 : PolyT fun p : (α × List (ℕ × Bool)) => List.range (ku p.1).length := PolyT.range (hk'.comp PolyT.id'.fst)
  have hr2 : PolyT fun p : ((α × List (ℕ × Bool)) × ℕ) => List.range (Nat.log2 (2 * (d p.1.1).1.length) + 1) := PolyT.range (hw.comp PolyT.id'.fst.fst)
  have hs : PolyT fun p : (((α × List (ℕ × Bool)) × ℕ) × ℕ) => (slotN p.1.1.2[p.1.2]?).testBit p.2 :=
    PolyT.testBit (slotN_polyT (by fun_prop)) (by fun_prop)
  unfold encN
  fun_prop

/-- `renc` is polynomial-time: it decodes the input, replaces every variable by its position in the
list of the variables that occur, and writes the result as a bit string. -/
theorem renc_polyT : PolyT renc :=
  encN_polyT Decode.stCertDecM.1 (renF_polyT Decode.stCertDecM.2.snd)

end VariableBound.Rename
