/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Sizes
public import ThreeSumApsp.Sec3.Theorem21a.Convolution

/-!
# Theorem 21(a): from 3SUM to Convolution-3SUM, and on to Exact Triangle

Theorem 21(a) reduces 3SUM to Exact Triangle.  Here it is composed of two
reductions.

* From 3SUM to Convolution-3SUM, cited from [CH20, Theorem 5.1].
  `theorem_21a_threeSum_to_convolution` states it for the explicit function `ChanHe.instances`.  It
  collects the correctness of the reduction (`ChanHe.threeSum_iff_exists_convolution3SUM`), the
  number of instances (`ChanHe.length_instances_pow_le`), the size of their entries
  (`ChanHe.abs_instances_pow_le`), the count for the searches (`ChanHe.scanPairs_pow_le`), and the
  asymptotic form of the three bounds.
* From Convolution-3SUM to Exact Triangle, cited from [VW13, Theorem 4.3]:
  `theorem_21a_convolution_to_exact`.  `theorem_21a_threeSum_to_exact` applies it to each array that
  the first reduction makes.

Nothing is stated here about running times, and the forms `n^{1/2+o(1)}` of Theorem 21(a) are not
derived; see the two docstrings.

Of the facts about `ChanHe.instances`, the programs for the reduction use only the correctness
(`ChanHe.instances_correct`).  Their running time is counted on the programs themselves, with the
bound on the number of nodes of a tree (`ChanHe.length_nodes_le`) and the orders of growth of the
parameters; the count `ChanHe.scanPairs` and the bounds `numBound` and `workBound` serve the
compared statement only.
-/

public section

open Finset

namespace ThreeSumApsp

/-! ## From 3SUM to Convolution-3SUM -/

/-- The reduction from 3SUM to Convolution-3SUM in the form needed for **Theorem 21(a)**.  The list
of instances may depend on the input, so a statement that such a list exists would be true for
trivial reasons.  The statement is therefore about the explicitly defined function
`ChanHe.instances`, and it is to be read together with the definitions of the namespace `ChanHe`.

What is stated: the input (`n ≥ 2` integers of absolute value at most `n^κ`, for a natural number
`κ`, the ν of Theorem 21, to which a real exponent can be rounded up; 3SUM asks for three numbers at
different positions), the number of instances, `(log n)^{O(1)}` (at most `ChanHe.numBound κ n`),
their length, `Õ(n)` (`ChanHe.lenOf κ n`, the common length), the absolute value of their numbers,
`n^{O(1)}` (at most `120 n^κ + 40`), and the one-array problem.

What is not stated: that the reduction is deterministic and takes `Õ(n^{3/2})` time.  This is about
a machine, and nothing here is about a machine.  In its place stands `ChanHe.scanPairs`, the number
of pairs (candidate prime, element) that the searches for the moduli go through.  It is a count that
we define, not a running time that we derive. It is at most `ChanHe.workBound κ n`, which is
`n^{3/2}` times a polylogarithm.

NOTE.
* `κ` is a natural number.
* Theorem 5.1 of [CH20] is a statement about running times, for 3SUM on three sets and
  Convolution-3SUM on three arrays.  The reduction stated here, with its count of instances, their
  length and the Õ(n^{3/2}), follows the proof of that theorem, and passes to `n` numbers and to one
  array by elementary devices; see `docs/REMARKS.md`, "Section 3: cited results". -/
theorem theorem_21a_threeSum_to_convolution (κ : ℕ) :
    IsPowPolylog (fun n => (ChanHe.numBound κ n : ℝ)) 0 ∧
    IsPowPolylog (fun n => (ChanHe.lenOf κ n : ℝ)) 1 ∧
    IsPowPolylog (fun n => (ChanHe.workBound κ n : ℝ)) (3 / 2) ∧
    ∀ (n : ℕ) (x : Fin n → ℤ), 2 ≤ n → (∀ i, |x i| ≤ (n : ℤ) ^ κ) →
      (ChanHe.instances n (n ^ κ) x).length ≤ ChanHe.numBound κ n ∧
      ChanHe.scanPairs n (n ^ κ) x ≤ ChanHe.workBound κ n ∧
      (∀ y ∈ ChanHe.instances n (n ^ κ) x, ∀ u < ChanHe.lenOf κ n,
        |y u| ≤ 120 * (n : ℤ) ^ κ + 40) ∧
      (ThreeSum x ↔
        ∃ y ∈ ChanHe.instances n (n ^ κ) x,
          Convolution3SUM fun i : Fin (ChanHe.lenOf κ n) => y i) :=
  ⟨ChanHe.isPowPolylog_numBound κ, ChanHe.isPowPolylog_lenOf κ, ChanHe.isPowPolylog_workBound κ,
    fun n x hn hx => ⟨ChanHe.length_instances_pow_le n κ hn x, ChanHe.scanPairs_pow_le hn hx,
      fun _ hy u _ => ChanHe.abs_instances_pow_le hn hx hy u,
      ChanHe.threeSum_iff_exists_convolution3SUM hn hx⟩⟩

/-! ## On to Exact Triangle -/

/-- The weights that a template produces are bounded by the filler, if the entries of the input
are. -/
theorem TriangleTemplate.weightsBoundedBy_instantiate {t N : ℕ} (τ : TriangleTemplate t N)
    {x : Fin N → ℤ} {fill : ℤ} (hx : ∀ i, |x i| ≤ fill) (h0 : 0 ≤ fill) :
    (τ.instantiate x fill).WeightsBoundedBy fill := by
  have hw : ∀ e, |templateWeight x fill e| ≤ fill := by
    rintro (_ | ⟨_ | _, i⟩)
    · exact (abs_of_nonneg h0).le
    · exact hx i
    · exact (abs_neg _).trans_le (hx i)
  exact ⟨fun _ _ => hw _, fun _ _ => hw _, fun _ _ => hw _⟩

/-- The two reductions of **Theorem 21(a)** composed.  For `n ≥ 2` put
`N = ChanHe.lenOf κ n`. There are `t ≤ √N + 1` and at most `2t` templates such that, for every input
`x` of `n` integers of absolute value at most `n^κ`: the list `ChanHe.instances n (n^κ) x` has at
most `ChanHe.numBound κ n` arrays; each template turns each array into an instance of Exact Triangle
on `t` vertices per part, with the filler weight `240 n^κ + 81` and all weights of absolute value at
most that; and three entries of `x` at different positions sum to 0 iff one of these instances has a
zero triangle.

So there are at most `2t · ChanHe.numBound κ n` triangle instances.  As above, `κ` is a natural
number; it is the paper's ν.

What is not stated.  The words "deterministically, in n^{3/2+o(1)} time" are about a machine, and
nothing here is about a machine. The forms `n^{1/2+o(1)}` of Theorem 21(a) for the number of
instances and for `t` are not part of this statement: they follow from the bounds on `numBound` and
`lenOf` in `theorem_21a_threeSum_to_convolution` by the arithmetic of `theorem_21a_compose`, but
this last step is not carried out here.  No lower bound on `t` is stated, so the weights are not
bounded by a power of the number of vertices, which is the form in which Theorem 19 takes them. -/
theorem theorem_21a_threeSum_to_exact (κ n : ℕ) (hn : 2 ≤ n) :
    ∃ (t : ℕ) (L : List (TriangleTemplate t (ChanHe.lenOf κ n))),
      (t : ℝ) ≤ Real.sqrt (ChanHe.lenOf κ n) + 1 ∧
      L.length ≤ 2 * t ∧
      ∀ x : Fin n → ℤ, (∀ i, |x i| ≤ (n : ℤ) ^ κ) →
        (ChanHe.instances n (n ^ κ) x).length ≤ ChanHe.numBound κ n ∧
        (∀ y ∈ ChanHe.instances n (n ^ κ) x, ∀ τ ∈ L,
          (τ.instantiate (fun i : Fin (ChanHe.lenOf κ n) => y i)
            (240 * (n : ℤ) ^ κ + 81)).WeightsBoundedBy (240 * (n : ℤ) ^ κ + 81)) ∧
        (ThreeSum x ↔ ∃ y ∈ ChanHe.instances n (n ^ κ) x, ∃ τ ∈ L,
          (τ.instantiate (fun i : Fin (ChanHe.lenOf κ n) => y i)
            (240 * (n : ℤ) ^ κ + 81)).HasZeroTriangle) := by
  obtain ⟨t, L, ht, hL, hexact⟩ :=
    theorem_21a_convolution_to_exact (ChanHe.lenOf κ n) (ChanHe.one_le_lenOf κ n)
  refine ⟨t, L, ht, hL, fun x hx => ⟨ChanHe.length_instances_pow_le n κ hn x, ?_, ?_⟩⟩
  · intro y hy τ _
    have hpos : (0 : ℤ) ≤ (n : ℤ) ^ κ := by positivity
    exact τ.weightsBoundedBy_instantiate
      (fun i => (ChanHe.abs_instances_pow_le hn hx hy i).trans (by omega)) (by omega)
  · rw [ChanHe.threeSum_iff_exists_convolution3SUM hn hx,
      show 240 * (n : ℤ) ^ κ + 81 = 2 * (120 * (n : ℤ) ^ κ + 40) + 1 by ring]
    exact exists_congr fun y => and_congr_right fun hy =>
      hexact _ _ fun i => ChanHe.abs_instances_pow_le hn hx hy i

end ThreeSumApsp
