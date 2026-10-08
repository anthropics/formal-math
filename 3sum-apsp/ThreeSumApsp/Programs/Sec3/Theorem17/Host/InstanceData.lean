/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.ScanPairs
public import ThreeSumApsp.Spec.Sec3.Theorem17.Chunks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing

/-!
# The host of Theorem 17: the list of its instances, as pure data

Proof of Theorem 17, "For each chunk 𝒬 ⊆ W_ϱ and each piece C_k form the instance".  After the prime
has been chosen, the host runs one loop over all instances: instance number `t` belongs to the piece
number `t / chunkCount` of `C` and to the chunk number `t % chunkCount` of the table of chunks.
This file defines what the host writes (`matX`, `matY`, `WI`, `WJ`), what the solver answers
(`ans`), which query pairs are accepted and which scans succeed (`acc`, `hit`), and whether a zero
triangle has been found before instance `t` (`found`).  The class of a residue `ϱ < p` is the
paper's `W_ϱ`: the pairs `(a, b)` whose weight is congruent to `ϱ` modulo `p`.  The pairs are listed
class after class, in the order of the residues, and a chunk is a segment of a class.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The hypotheses of Theorem 17 on its parameters, in natural numbers: "Let 16 ≤ D ≤ n, and let
1 ≤ g ≤ √D be an integer." -/
structure BigCase (n D g : ℕ) : Prop where
  sixteen_le : 16 ≤ D
  le_n : D ≤ n
  one_le_g : 1 ≤ g
  g_le_sqrt : g ≤ Nat.sqrt D

/-- The data on which the loop over the instances depends. -/
structure HostData : Type where
  /-- The number of vertices of each part. -/
  n : ℕ
  /-- The bound on the number of middle vertices of an instance of Lop-AE-SparseTri, that is, the
  inner dimension of its matrices `X` and `Y`. -/
  D : ℕ
  /-- The prime. -/
  p : ℕ
  /-- The number of vertices of a piece of `C`. -/
  q : ℕ
  /-- The largest number of query pairs of an instance. -/
  cap : ℕ
  /-- The weights of the edges `(a, b)`, row by row. -/
  AB : List ℤ
  /-- The weights of the edges `(b, c)`, row by row. -/
  BC : List ℤ
  /-- The weights of the edges `(a, c)`, row by row. -/
  AC : List ℤ

namespace HostData

variable (X : HostData)

/-- The residues modulo `p` of the weights of the edges `(a, b)`. -/
def RAB : List ℕ := residList X.p X.AB
/-- The residues modulo `p` of the weights of the edges `(b, c)`. -/
def RBC : List ℕ := residList X.p X.BC
/-- The residues modulo `p` of the weights of the edges `(a, c)`. -/
def RAC : List ℕ := residList X.p X.AC
/-- The rows `a` of all pairs `(a, b)`, class after class. -/
def QI : List ℕ := queryRows X.n X.p X.RAB
/-- The columns `b` of all pairs `(a, b)`, class after class. -/
def QJ : List ℕ := queryCols X.n X.p X.RAB
/-- The table of the chunks. -/
def CT : List Chunk := chunkTab X.n X.p X.cap X.RAB
/-- The number of chunks. -/
def chunkCount : ℕ := X.CT.length
/-- The number of pieces. -/
def h : ℕ := X.n ⌈/⌉ X.q
/-- The number of instances. -/
def m : ℕ := X.h * X.chunkCount

/-- The first vertex of the piece of instance t. -/
def c0 (t : ℕ) : ℕ := t / X.chunkCount * X.q
/-- The number of vertices of the piece of instance t. -/
def len (t : ℕ) : ℕ := min X.q (X.n - X.c0 t)
/-- The chunk of instance t. -/
def chunk (t : ℕ) : Chunk := X.CT.getD (t % X.chunkCount) ⟨0, 0, 0⟩
/-- The residue `ϱ` of the chunk of instance t. -/
def rho (t : ℕ) : ℕ := (X.chunk t).residue
/-- The first place of the chunk of instance t in the list of all pairs. -/
def lo (t : ℕ) : ℕ := (X.chunk t).start
/-- The number of query pairs of instance t. -/
def w (t : ℕ) : ℕ := (X.chunk t).len

/-- The matrix `X` of instance t. -/
def matX (t : ℕ) : List ℤ := xList X.n X.D X.p (X.c0 t) (X.len t) (X.rho t) X.RAC
/-- The matrix `Y` of instance t. -/
def matY (t : ℕ) : List ℤ := yList X.n X.D X.p (X.c0 t) (X.len t) X.RBC
/-- The rows of the query pairs of instance t. -/
def WI (t : ℕ) : List ℕ := (X.QI.drop (X.lo t)).take (X.w t)
/-- The columns of the query pairs of instance t. -/
def WJ (t : ℕ) : List ℕ := (X.QJ.drop (X.lo t)).take (X.w t)

/-- The answers of a solver of Lop-AE-SparseTri to instance t. -/
def ans (t : ℕ) : List ℤ :=
  (thinOut X.n X.D (X.matX t) (X.matY t) (X.WI t) (X.WJ t)).map fun v => if v = 0 then 0 else 1

/-- The query pair number i of instance t is accepted. -/
def acc (t i : ℕ) : Bool := decide ((X.ans t).getD i 0 ≠ 0)
/-- The scan for the query pair number i of instance t succeeds. -/
def hit (t i : ℕ) : Bool :=
  scanHit X.n X.AB X.BC X.AC ((X.WI t).getD i 0) ((X.WJ t).getD i 0) (X.c0 t) (X.len t)

/-- A zero triangle has been found before instance t. -/
def found : ℕ → Bool
  | 0 => false
  | t + 1 => foundAt (X.acc t) (X.hit t) (found t) (X.w t)

/-- The number of scans made for instance t. -/
def execs (t : ℕ) : ℕ := execsUpto (X.acc t) (X.hit t) (X.found t) (X.w t)
/-- The number of accepted query pairs of instance t whose scan fails or would fail. -/
def fails (t : ℕ) : ℕ := failsUpto (X.acc t) (X.hit t) (X.w t)

end HostData

end Light.Sec3
