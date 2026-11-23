/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Tensors over a finite set of parties

Paper: the subsection "Tensors". A tensor over a set I of parties is an array
with one index for each party. This file defines local maps, restrictions, sums of restrictions,
products, powers, push-forwards (`push`), and spectral points. The field is any field (where more is
needed, it is a hypothesis).
-/

namespace Ov

open Finset

/-- A tensor over the parties I with entries in K: for each party p a finite index set ι p, and an
array. The zero array is allowed. -/
structure Ten (K : Type) (I : Type) where
  ι : I → Type
  [fin : ∀ p, Fintype (ι p)]
  [dec : ∀ p, DecidableEq (ι p)]
  val : (∀ p, ι p) → K

attribute [instance] Ten.fin Ten.dec

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Linear maps on the legs, as matrices: from the legs of t to the legs of s. -/
abbrev Loc (s t : Ten K I) : Type := ∀ p, s.ι p → t.ι p → K

/-- The array obtained from t by the local maps L. -/
def app {s t : Ten K I} (L : Loc s t) (x : ∀ p, s.ι p) : K :=
  ∑ y : ∀ p, t.ι p, (∏ p, L p (x p) (y p)) * t.val y

/-- s is a restriction of t: s arises from t by local maps. -/
def Restr (s t : Ten K I) : Prop := ∃ L : Loc s t, ∀ x, s.val x = app L x

/-- s is covered by the tensors b k: it is a sum of restrictions of them. There is one
restriction of each b k; it may be 0. -/
def SumRestr {κ : Type} [Fintype κ] (s : Ten K I) (b : κ → Ten K I) : Prop :=
  ∃ L : ∀ k, Loc s (b k), ∀ x, s.val x = ∑ k, app (L k) x

/-- s and t are restrictions of one another. (The paper identifies such tensors.) -/
def Equi (s t : Ten K I) : Prop := Restr s t ∧ Restr t s

/-- The tensor 1: all legs one-dimensional, the entry 1. -/
def one : Ten K I where
  ι := fun _ => Unit
  val := fun _ => 1

instance : One (Ten K I) := ⟨one⟩

/-- The product (Kronecker product, party by party). -/
def mul (s t : Ten K I) : Ten K I where
  ι := fun p => s.ι p × t.ι p
  val := fun x => s.val (fun p => (x p).1) * t.val (fun p => (x p).2)

instance : Mul (Ten K I) := ⟨mul⟩

/-- The k-th power: indices are k-tuples. -/
def kpow (t : Ten K I) (k : ℕ) : Ten K I where
  ι := fun p => Fin k → t.ι p
  val := fun x => ∏ i, t.val (fun p => x p i)

/-- The product of a finite family. -/
def prod {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I) : Ten K I where
  ι := fun p => ∀ k, (b k).ι p
  val := fun x => ∏ k, (b k).val (fun p => x p k)

/-- The push-forward πt: the index j of a tensor on J is given to the party π j. A party may get several
indices, or none (then its index set has one element). -/
def push (π : J → I) (t : Ten K J) : Ten K I where
  ι := fun q => ∀ j : {j : J // π j = q}, t.ι j.1
  val := fun x => t.val (fun j => x (π j) ⟨j, rfl⟩)

/-- The unit tensor ⟨r⟩_J of size r on J. -/
def unit (K : Type) [Field K] (J : Type) [Fintype J] [DecidableEq J] (r : ℕ) : Ten K J where
  ι := fun _ => Fin r
  val := fun x => if ∀ i j, x i = x j then 1 else 0

/-- The wire ⟨n⟩_pq of dimension n between p and q. If p = q and n > 0 it is equivalent to 1. -/
def wire (K : Type) [Field K] {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) (p q : I) : Ten K I :=
  push ![p, q] (unit K (Fin 2) n)

/-- A tensor has rank at most r if it is a restriction of the unit tensor of size r. (If there is a
party, this is the same as being a sum of r products of vectors: `rankLE_iff`.) -/
def RankLE (t : Ten K I) (r : ℕ) : Prop := Restr t (unit K I r)

end Ten

/-- A spectral point over the parties I: a real function F ≥ 0 on the tensors over I that is
multiplicative, with F(1) = 1 and F(s) ≤ ∑ F(b k) whenever s is a sum of restrictions of the b k. This
is the paper's definition, a multiplicative gauge; with the empty family it gives F(0) = 0. -/
structure Spec (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] where
  F : Ten K I → ℝ
  nonneg : ∀ t, 0 ≤ F t
  one : F 1 = 1
  mul : ∀ s t, F (s * t) = F s * F t
  le_sum : ∀ {κ : Type} [Fintype κ] (s : Ten K I) (b : κ → Ten K I), Ten.SumRestr s b → F s ≤ ∑ k, F (b k)

namespace Spec

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- The paper's d_φ(p,q), the exponent of a wire: log₂ of the value at the wire of dimension 2 between p and q. -/
noncomputable def e (F : Spec K I) (p q : I) : ℝ := Real.logb 2 (F.F (Ten.wire K 2 p q))

end Spec

end Ov
