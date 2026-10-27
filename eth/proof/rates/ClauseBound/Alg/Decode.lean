/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Top
public import CountKSat.InOut

/-! # Reading the input 1ᵏ 0 code(φ)

The input of the machine that counts for all k at once is `SatM.enc k φ`: k ones, a zero, then the
code `SatK.enc k φ` of φ as an instance of k-SAT.
`kOf` returns k in unary and `fmlOf` returns n in unary and the formula with natural numbers as
variables (`stDecM`), both in polynomial time (`stCertDecM`).
Here k is part of the input, in unary. The certificates of
proof/consequences/WidthK/Poly/Decode.lean have k as a constant; this file proves its three lemmas
with k a function of the input. -/

public section

namespace ClauseBound.Alg.Decode

open Groundwork CountKSat
open Groundwork.Decode (slotDec width width_polyT)
open Groundwork.DecodeK (clauseDec decK)

/-! ### What is read -/

/-- `kOf` reads k from 1ᵏ 0 w. -/
theorem kOf_ones (k : ℕ) (w : List Bool) : kOf (List.replicate k true ++ false :: w) = List.replicate k () := by
  simp [kOf]

/-- `restOf` reads w from 1ᵏ 0 w. -/
theorem restOf_ones (k : ℕ) (w : List Bool) : restOf (List.replicate k true ++ false :: w) = w := by
  simp [restOf]

/-- For k ≥ 1, reading the code of (k, φ), where φ has at most k literals in every clause, gives
back k in unary, n in unary and the formula with natural numbers as variables. -/
theorem stDecM : StDecM := fun k n φ hk hφ => by
  refine ⟨kOf_ones k _, ?_⟩
  rw [fmlOf, SatM.enc, kOf_ones, restOf_ones, List.length_replicate]
  exact stDecU k n φ hk hφ

/-! ### Polynomial time, with k as data in unary -/

variable {α : Type} [Enc α]

/-- Reading one clause from a block of k slots of w bits is polynomial-time, k in unary. -/
theorem clauseDec_polyT {k w : α → ℕ} {b : α → List Bool} (hk : Unary k) (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => clauseDec (k x) (w x) (b x) := by
  unfold clauseDec
  exact PolyT.filterMap (f := fun x j => slotDec (ofWord (block (w x) j (b x)))) (by fun_prop) (PolyT.range hk)

/-- Reading the list of clauses from the body b, one block of k·w bits per clause, is
polynomial-time, k in unary. -/
theorem clauses_polyT {k w : α → ℕ} {b : α → List Bool} (hk : Unary k) (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => ((List.range (b x).length).take ((b x).length / (k x * w x))).map fun c =>
      clauseDec (k x) (w x) (block (k x * w x) c (b x)) := by
  have hk' : PolyT k := hk.poly
  have hr : PolyT fun x => List.range (b x).length := PolyT.range (Unary.of_length hb)
  have ht : PolyT fun x => (List.range (b x).length).take ((b x).length / (k x * w x)) :=
    PolyT.take (by fun_prop) hr
  refine PolyT.map (f := fun x c => clauseDec (k x) (w x) (block (k x * w x) c (b x))) ?_ ht
  exact clauseDec_polyT (hk.comp PolyT.id'.fst) (by fun_prop) (by fun_prop)

/-- The decoder `decK` is polynomial-time jointly in k, in unary, and the word. -/
theorem decK_polyT {k : α → ℕ} {v : α → List Bool} (hk : Unary k) (hv : PolyT v) : PolyT fun x => decK (k x) (v x) := by
  have hn : PolyT fun x => ((v x).takeWhile id).length := by fun_prop
  have hb : PolyT fun x => ((v x).dropWhile id).tail := by fun_prop
  exact PolyT.prodMk hn (clauses_polyT hk (width_polyT hn) hb)

/-- The reader `decU` is polynomial-time jointly in k, in unary, and the word. -/
theorem decU_polyT {k : α → ℕ} {v : α → List Bool} (hk : Unary k) (hv : PolyT v) : PolyT fun x => decU (k x) (v x) := by
  have h1 : Unary fun x => ((v x).takeWhile id).length := Unary.of_length (by fun_prop)
  have h2 : PolyT fun x => (decK (k x) (v x)).2 := (decK_polyT hk hv).snd
  exact PolyT.prodMk h1 h2

/-- `kOf` is polynomial-time. -/
theorem kOf_polyT : PolyT kOf := by
  unfold kOf; fun_prop

/-- `restOf` is polynomial-time. -/
theorem restOf_polyT : PolyT restOf := by
  unfold restOf; fun_prop

/-- `kOf` and `fmlOf` are polynomial-time. -/
theorem stCertDecM : StCertDecM :=
  ⟨kOf_polyT, decU_polyT (Unary.of_length kOf_polyT) restOf_polyT⟩

end ClauseBound.Alg.Decode
