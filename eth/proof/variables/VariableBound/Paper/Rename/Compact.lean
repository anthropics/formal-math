/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Paper.Rename.Math
import VariableBound.Paper.Rename.Code
import VariableBound.Paper.Rename.Cert
import ClauseBound.Alg.Decode
import WidthK.Decode

/-! # The front end for the compact code

The compact code `MainTheoremForms.encC k φ` is `SatM.enc k φ` with 1ʷ in place of 1ᴺ, where w =
⌊log₂(2N)⌋ + 1 is the number of bits of a slot. `decC` reads the clauses from it: the width w is
read, not computed from N.
`rencC` is the front end: decode, rename the variables that occur, write the result in the code
`SatM.enc`.
* `rencC_encC`: for k ≥ 1 and φ with at most k literals in every clause, `rencC` maps the compact
  code of (k, φ) to `SatM.enc k (ren φ)`.
* `rencC_polyT`: it is polynomial-time. `lengthEncC`: the length of the compact code. -/

public section

namespace VariableBound.Rename

open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Groundwork.DecodeK (clauseDec decK decK_enc)
open Sat3 (CNF)

/-- The clauses written in the body b: one block of k slots of w bits per clause. -/
@[expose] def clausesOf (k w : ℕ) (b : List Bool) : Fml :=
  ((List.range b.length).take (b.length / (k * w))).map fun c => clauseDec k w (block (k * w) c b)

/-- The clauses written in a compact code: after 1ᵏ 0 comes 1ʷ 0, then the body. -/
@[expose] def decC (x : List Bool) : Fml :=
  clausesOf (kOf x).length ((restOf x).takeWhile id).length ((restOf x).dropWhile id).tail

/-- The front end for the compact code: from the compact code of (k, φ) to the code of (k, φ with
the variables that occur renamed to 0, …, n − 1). -/
@[expose] def rencC (x : List Bool) : List Bool := encN (kOf x) (renF (decC x))

/-- The bits of the clauses of φ: k slots per clause, ⌊log₂(2N)⌋ + 1 bits per slot. -/
def bodyOf (k : ℕ) {N : ℕ} (φ : CNF N) : List Bool :=
  φ.flatMap fun C => (List.range k).flatMap fun j => (List.range (Nat.log2 (2 * N) + 1)).map (Sat3.slot C[j]?).testBit

/-- The leading 1s of 1ᵃ 0 v. -/
theorem takeWhile_ones (a : ℕ) (v : List Bool) : ((List.replicate a true ++ false :: v).takeWhile id).length = a := by
  simp

/-- What follows 1ᵃ 0 in 1ᵃ 0 v. -/
theorem dropWhile_ones (a : ℕ) (v : List Bool) : ((List.replicate a true ++ false :: v).dropWhile id).tail = v := by
  simp

/-- Reading the bits of the clauses with the width ⌊log₂(2N)⌋ + 1 gives the formula back, for k ≥ 1
and φ with at most k literals in every clause. -/
theorem clausesOf_bodyOf {k N : ℕ} (hk : 1 ≤ k) {φ : CNF N} (hφ : ∀ C ∈ φ, C.length ≤ k) : clausesOf k (Nat.log2 (2 * N) + 1) (bodyOf k φ) = toN φ := by
  have h := congrArg Prod.snd (decK_enc hk hφ)
  have e : SatK.enc k φ = List.replicate N true ++ false :: bodyOf k φ := rfl
  simp only [decK, e, takeWhile_ones, dropWhile_ones, width_eq] at h
  exact h

/-- Reading the compact code of (k, φ) gives the formula back, for k ≥ 1 and φ with at most k
literals in every clause. -/
theorem decC_encC {k N : ℕ} (hk : 1 ≤ k) {φ : CNF N} (hφ : ∀ C ∈ φ, C.length ≤ k) : decC (encC k φ) = toN φ := by
  have e : encC k φ = List.replicate k true ++ false :: (List.replicate (Nat.log2 (2 * N) + 1) true ++ false :: bodyOf k φ) := rfl
  rw [decC, e, Decode.kOf_ones, Decode.restOf_ones, takeWhile_ones, dropWhile_ones, List.length_replicate]
  exact clausesOf_bodyOf hk hφ

/-- The front end maps the compact code of (k, φ) to the code of (k, φ renamed), for k ≥ 1 and φ
with at most k literals in every clause. -/
theorem rencC_encC {k N : ℕ} (φ : CNF N) (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) : rencC (encC k φ) = SatM.enc k (ren φ) := by
  have e : encC k φ = List.replicate k true ++ false :: (List.replicate (Nat.log2 (2 * N) + 1) true ++ false :: bodyOf k φ) := rfl
  rw [rencC, decC_encC hk hφ, e, Decode.kOf_ones, ← encN_toN, toN_ren, renF, ← length_occL, List.map_const']

/-- The front end for the compact code is polynomial-time. -/
theorem rencC_polyT : PolyT rencC := by
  have hk : PolyT kOf := Decode.stCertDecM.1
  have hr : PolyT restOf := Decode.restOf_polyT
  have hd : PolyT decC := Decode.clauses_polyT (Unary.of_length hk) (by fun_prop) (by fun_prop)
  exact encN_polyT hk (renF_polyT hd)

/-- The length of the compact code: k + w + 2 + m·k·w with w = ⌊log₂(2N)⌋ + 1. -/
theorem lengthEncC : LengthEncCStmt := by
  intro k N φ
  have h := Groundwork.DecodeK.length_enc k φ
  have e1 : SatK.enc k φ = List.replicate N true ++ false :: bodyOf k φ := rfl
  have e : encC k φ = List.replicate k true ++ false :: (List.replicate (Nat.log2 (2 * N) + 1) true ++ false :: bodyOf k φ) := rfl
  rw [e1] at h
  simp only [List.length_append, List.length_replicate, List.length_cons] at h
  simp only [e, List.length_append, List.length_replicate, List.length_cons]
  omega

end VariableBound.Rename
