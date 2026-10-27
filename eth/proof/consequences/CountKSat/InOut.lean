/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSat.Interfaces
public import WidthK.Poly.Decode

/-! # What the counting machine reads, and the count of what it reads

This file proves three of the interface statements of proof/consequences/CountKSat/Interfaces.lean.
For k ≥ 1, `decU k` turns the code `SatK.enc k φ` of a formula with at most k literals per clause
into n in unary and the formula with natural numbers
as variables (`stDecU`), in polynomial time (`stCertDecU`). They follow from `decK_enc` in
proof/consequences/WidthK/Decode.lean and `decK_polyT` in
proof/consequences/WidthK/Poly/Decode.lean, on the decoder `decK k`.
The formula with natural numbers as variables has the same number of satisfying assignments on n
variables (`stCntToN`). -/

namespace CountKSat

open Groundwork Groundwork.Prog Groundwork.Decode Groundwork.DecodeK
open SatK (enc numSat)

/-- For k ≥ 1, reading the code of a formula with at most k literals in every clause gives back n,
in unary, and the formula with natural numbers as variables. -/
public theorem stDecU : StDecU := fun k n φ hk hφ => by
  have h := decK_enc hk hφ
  have h1 : ((enc k φ).takeWhile id).length = n := congrArg Prod.fst h
  rw [decU, h, h1]

/-- The reader `decU k` is polynomial-time. -/
public theorem stCertDecU : StCertDecU := fun k => by
  have h1 : Unary fun x : List Bool => (x.takeWhile id).length := Unary.of_length (by fun_prop)
  have h2 : PolyT fun x : List Bool => (decK k x).2 := by have := decK_polyT k; fun_prop
  exact PolyT.prodMk h1 h2

/-- The formula read with natural numbers as variables has the same number of satisfying
assignments. -/
public theorem stCntToN : StCntToN := fun n φ => by
  unfold cntN numSat
  congr 1
  refine Finset.filter_congr fun a _ => ?_
  have he : ∀ i : Fin n, ext a i.val = a i := fun i => by simp [ext, i.2]
  simp only [toN, List.forall_mem_map]
  refine forall₂_congr fun C _ => ⟨?_, ?_⟩
  · rintro ⟨l, hl, h⟩
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact ⟨l', hl', (he _).symm.trans h⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, (he _).trans h⟩

end CountKSat
