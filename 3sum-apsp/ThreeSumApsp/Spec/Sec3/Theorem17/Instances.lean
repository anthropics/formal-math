/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation

/-!
# The instances and the scans (proofs of Theorems 17 and 19), as functions on lists

The reduction of Theorem 17 makes one instance of Lop-AE-SparseTri for each chunk of a residue class
`W_ϱ` and each piece `C_k` of `C`.  The middle vertices of the instance are the pairs `(c, σ)` with
`c ∈ C_k` and `σ ∈ ℤ_p`.  This file has the two 0/1 matrices of an instance in the form in which a
routine fills them (`xList`, `yList`), the scan of a piece for a witness (`scanHit`), and the search
through all triples for small instances (`hasZero`).

The weights of an instance of Exact Triangle on `n` vertices per part are three lists `AB`, `BC`,
`AC` of `n²` integers: `w(a,b)` at `a n + b`, `w(b,c)` at `b n + c`, `w(a,c)` at `a n + c`.  The
lists `RAC` and `RBC` hold the residues of the weights modulo `p`, and
`S(a,b,c) = w(a,b) + w(b,c) + w(a,c)`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- The matrix `X` of the instance for the residue `ϱ` and the piece `{c0, …, c0 + len - 1}`: the
middle vertex `(c, σ)` is the column `(c - c0) p + σ`, and `a ∼ (c, σ)` iff `σ ≡ w(a,c) + ϱ`.  `n`
rows of `D` entries. -/
def xList (n D p c0 len rho : ℕ) (RAC : List ℕ) : List ℤ :=
  (List.range (n * D)).map fun i =>
    if i % D / p < len ∧ i % D % p = (RAC.getD (i / D * n + c0 + i % D / p) 0 + rho) % p then 1
    else 0

/-- The matrix `Y`: `(c, σ) ∼ b` iff `σ ≡ -w(b,c)`.  `D` rows of `n` entries. -/
def yList (n D p c0 len : ℕ) (RBC : List ℕ) : List ℤ :=
  (List.range (D * n)).map fun i =>
    if i / n / p < len ∧ i / n % p = (p - RBC.getD (i % n * n + c0 + i / n / p) 0) % p then 1
    else 0

/-- "scan the piece C_k of its instance for a c with S(a,b,c) = 0". -/
def scanHit (n : ℕ) (AB BC AC : List ℤ) (a b c0 len : ℕ) : Bool :=
  (List.range len).any fun c =>
    AB.getD (a * n + b) 0 + BC.getD (b * n + c0 + c) 0 + AC.getD (a * n + c0 + c) 0 = 0

/-- Whether there is a zero triangle, by trying all triples (proof of Theorem 19: "smaller instances
are solved by brute force"). -/
def hasZero (n : ℕ) (AB BC AC : List ℤ) : Bool :=
  (List.range n).any fun a => (List.range n).any fun b => scanHit n AB BC AC a b 0 n

end ThreeSumApsp.Spec
