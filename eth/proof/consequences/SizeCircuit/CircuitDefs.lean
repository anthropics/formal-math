/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SizeCircuit.Defs
public import CircuitLowerBound.Circ.Blocks

/-! # Section 7, proof of Corollary 7: the circuit that tests |S| = s (definitions only)

The paper: «a circuit with O(n) gates of two inputs tests whether |S| = s». The paper cites
Impagliazzo, Paturi and Zane for it and does not write the circuit down. This file writes one down.

**The idea.** The circuit counts the ones among x₀ … xₙ₋₁ in binary and compares the result with s.
Every wire that still has to be counted has a weight 2^j; at the start these are the n inputs, all
of weight 1. Wires are added level by level, first all wires of weight 1, then all of weight 2, and
so on.
* Three wires of weight 2^j go through a full adder (5 gates): it gives one wire of weight 2^j
  (their sum modulo 2) and one of weight 2^{j+1} (the carry).
* If exactly two wires of weight 2^j are left, they go through a half adder (2 gates): the sum is
  digit j of the number of ones, the carry has weight 2^{j+1}.
* If exactly one wire of weight 2^j is left, it is digit j of the number of ones (no gate).
Each of the three steps makes the number of wires that still have to be counted smaller by exactly
one. So after n steps no wire is left, at most 5n gates have been written, and there are at most n
digits (in fact about log₂ n).
* Then the digits are compared with those of s: one gate with a constant value (1 if s has no more
  digits than were found, that is s < 2^{number of digits}; 0 if not), and for each digit one gate
  «the result so far, and this digit is that of s». These are at most n + 1 gates.
Together at most 6n + 1 gates.

**Numbers of wires.** As in proof/consequences/SizeCircuit/Defs.lean: the inputs are the wires 0 …
n−1, and the gate at place t of the list has the wire n + t. So the next gate written after the list
K has the wire n + K.length.

The tables of the functions (`opXor`, `opAnd`, `opOr`, `opAndN` «the first and not the second»,
`opOne`, `opZero`) are those of proof/consequences/CircuitLowerBound/Circ/Blocks.lean.
This file has no theorem; `StSizeGates` is the statement about the circuit, and `StCircuitExists` of
Defs.lean follows from it. -/

@[expose] public section

namespace SizeCircuit

open CircuitLowerBound CircuitLowerBound.Blocks

/-- A full adder for the wires a, u, v; its five gates get the wires N, …, N + 4.
N = a ⊕ u; N + 1 = (a ⊕ u) ⊕ v, the sum; N + 2 = a ∧ u; N + 3 = (a ⊕ u) ∧ v; N + 4 = (a ∧ u) ∨ ((a ⊕
u) ∧ v), the carry. -/
def fullAdder (N a u v : ℕ) : List GateD :=
  [(opXor, a, u), (opXor, N, v), (opAnd, a, u), (opAnd, N, v), (opOr, N + 2, N + 3)]

/-- A half adder for the wires a, u: the first gate is a ⊕ u, the sum; the second is a ∧ u, the
carry. -/
def halfAdder (a u : ℕ) : List GateD := [(opXor, a, u), (opAnd, a, u)]

/-- What has been written so far: (the wires of the present weight 2^j that still have to be
counted, the wires of the next weight 2^{j+1} found so far, the wires that carry the digits 0 … j−1
of the number of ones, lowest first, the gates written so far). -/
abbrev AddState : Type := List ℕ × List ℕ × List ℕ × List GateD

/-- One step of the addition, on n inputs. With N = n + (number of gates so far), the wire of the
next gate:
* at least three wires a, u, v of the present weight: a full adder; its sum N + 1 stays at the
  present weight in place of the three, its carry N + 4 goes to the next weight;
* exactly two wires a, u: a half adder; its sum N is the next digit; the next weight becomes the
  present one, with the carry N + 1;
* exactly one wire a: it is the next digit; the next weight becomes the present one;
* no wire: nothing is done. -/
def addStep (n : ℕ) (st : AddState) : AddState :=
  match st.1 with
  | a :: u :: v :: r => ((n + st.2.2.2.length + 1) :: r, (n + st.2.2.2.length + 4) :: st.2.1, st.2.2.1, st.2.2.2 ++ fullAdder (n + st.2.2.2.length) a u v)
  | [a, u] => ((n + st.2.2.2.length + 1) :: st.2.1, [], st.2.2.1 ++ [n + st.2.2.2.length], st.2.2.2 ++ halfAdder a u)
  | [a] => (st.2.1, [], st.2.2.1 ++ [a], st.2.2.2)
  | [] => st

/-- The start: the n inputs have weight 1; no digit and no gate yet. -/
def addStart (n : ℕ) : AddState := (List.range n, [], [], [])

/-- The addition: n steps from the start. -/
def added (n : ℕ) : AddState := (addStep n)^[n] (addStart n)

/-- The comparison of the digits carried by the wires `digits` (lowest first) with the number s; its
gates get the wires N, N + 1, ….
The first gate has a constant value: 1 if s < 2^(number of digits), 0 if not (it names the wire 0
twice and ignores it).
For each digit i, lowest first, one more gate follows, on the wire N + 1 + i: it reads the wire N +
i (the result so far) and the wire of digit i; it is «the result so far, and digit i is 1» if digit
i of s is 1, and «the result so far, and digit i is not 1» if it is 0. -/
def compareGates (N s : ℕ) (digits : List ℕ) : List GateD :=
  ((if s < 2 ^ digits.length then opOne else opZero), 0, 0) ::
    (List.range digits.length).map fun i => ((if s.testBit i then opAnd else opAndN), N + i, digits.getD i 0)

/-- **The circuit on n inputs that tests whether exactly s of them are 1**: the gates of the
addition, then the gates of the comparison of its digits with s. -/
def sizeGates (n s : ℕ) : List GateD :=
  (added n).2.2.2 ++ compareGates (n + (added n).2.2.2.length) s (added n).2.2.1

/-- **«a circuit with O(n) gates of two inputs tests whether |S| = s»**, for the circuit written
down here: `sizeGates` tests the size with at most a·(n+1) gates, for some constant a, and is
computed in polynomial time from (n in unary, s in binary). -/
def StSizeGates : Prop := ∃ a : ℕ, TestsSize sizeGates a ∧ CertGates sizeGates

end SizeCircuit
