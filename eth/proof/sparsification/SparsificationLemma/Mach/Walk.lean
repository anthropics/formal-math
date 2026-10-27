/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Mach.Defs
public import ClauseBound.Alg.Top
import all PaddedDescent.F.Top

/-! # The walk that collects the outputs

Definitions: the walk `walkL`, which makes one round of the depth-first walk
`Groundwork.Sparsify.round` for each unit of a pad and replaces a state whose word is longer than
the pad by the empty state (`cap`); the code `codeP`, which is `code` with
every unary number cut off at the length of the pad (a variable is a natural number written in
binary, and writing it in unary can take exponentially long, so `code` itself is not polynomial-time
on all lists of formulas); the function `BL` of (input, pad) that writes the outputs; and
the exponent `eL` of the length of the pad.
Theorems, for every step function: the number of nodes on the stack and in the list of results
together never decreases in a round, so it is at most the number of leaves (`total_le_leaves`); what
holds of all
nodes that are ever on the stack holds of all results (`out_of_stack`). Then `walkL_eq`: if the pad
has at least 2·(number of leaves) − 1 units and every state fits under it, `walkL` returns the
leaves. -/

@[expose] public section

namespace SparsificationLemma.Mach

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg

/-! ### Definitions -/

/-- The depth-first walk of the tree for width k with the thresholds `thetaU τ`, one round for each
unit of the pad; it returns the nodes at which the procedure stops, from left to right. -/
def walkL (k : ℕ) (pad : U) (τ : ℕ) (r : CNode) : List CNode :=
  (pad.foldl (fun st _ => cap pad ([], []) (round (stepC (thetaU τ) k) st)) (cap pad ([], []) ([r], []))).2.reverse

/-- `codeNat`, cut off at the length of the pad. -/
def codeNatP (pad : U) (v : ℕ) : List Bool := (pad.take v).map (fun _ => true) ++ [false]

/-- `codeLit`, with the variable cut off at the length of the pad. -/
def codeLitP (pad : U) (l : PLit) : List Bool := l.2 :: codeNatP pad l.1

/-- `codeCl`, with the variables cut off at the length of the pad. -/
def codeClP (pad : U) (C : PCl) : List Bool := C.flatMap (fun l => true :: codeLitP pad l) ++ [false]

/-- `codeFml`, with the variables cut off at the length of the pad. -/
def codeFmlP (pad : U) (ψ : PFml) : List Bool := ψ.flatMap (fun C => true :: codeClP pad C) ++ [false]

/-- `code`, with the variables cut off at the length of the pad. -/
def codeP (pad : U) (L : List PFml) : List Bool := L.flatMap (fun ψ => true :: codeFmlP pad ψ) ++ [false]

/-- The precision written in the input 1^s 0 1^k 0 …. -/
def sL (x : List Bool) : ℕ := (kOf x).length

/-- The width written in the input. -/
def kL (x : List Bool) : ℕ := (kOf (restOf x)).length

/-- The number of variables, in unary, and the formula written in the input. -/
def dL (x : List Bool) : U × Fml := fmlOf (restOf x)

/-- The exponent of the length of the pad: ⌊n/2^s⌋ + k + 3·(number of binary digits of the length of
the input) + 9. -/
def eL (x : List Bool) : ℕ := (dL x).1.length / 2 ^ sL x + kL x + 3 * Nat.size x.length + 9

/-- The function of (input, pad): the code of the list of outputs, if the pad is long enough. The
width is cut off at ⌊log₂(length of the pad)⌋, so that 2^k can be written in unary on every input. -/
def BL (p : List Bool × U) : List Bool :=
  codeP p.2 ((walkL (min (kL p.1) (Nat.log 2 p.2.length)) p.2 (tauOf (sL p.1)) (rootC (dL p.1))).map out)

/-- An upper bound for the length of the word of a node: a formula of at most 2^k·m clauses of at
most k literals and a side list of at most 2n clauses of at most 2 literals, all on variables below
n. -/
def nodeLen (k n m : ℕ) : ℕ := 2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 6

/-! ### The walk, for every step function -/

section
variable {σ : Type} (step : σ → Option (σ × σ))

/-- A round does not decrease the number of nodes on the stack and in the list of results together. -/
theorem total_le_round (st : List σ × List σ) : st.1.length + st.2.length ≤ (round step st).1.length + (round step st).2.length := by
  obtain ⟨_ | ⟨s, r⟩, out⟩ := st
  · simp [Sparsify.round]
  · simp only [Sparsify.round]
    cases step s <;> (simp only [List.length_cons]; omega)

/-- The same for any number of further rounds. -/
theorem total_mono (a : List σ × List σ) : Monotone fun i => ((round step)^[i] a).1.length + ((round step)^[i] a).2.length :=
  monotone_nat_of_le_succ fun i => by
    simp only [Function.iterate_succ_apply']
    exact total_le_round step _

/-- After any number of rounds, the stack and the list of results together have at most as many
nodes as there are leaves. -/
theorem total_le_leaves (d : ℕ) (s : σ) (hd : ∀ x ∈ leaves step d s, step x = none) (i : ℕ) :
    ((round step)^[i] ([s], [])).1.length + ((round step)^[i] ([s], [])).2.length ≤ (leaves step d s).length := by
  have h := total_mono step ([s], []) (le_max_left i (2 * (leaves step d s).length - 1))
  simp only [round_iterate_of_le step d s hd _ (le_max_right i (2 * (leaves step d s).length - 1))] at h
  simpa using h

/-- What holds of all nodes that are ever on the stack holds of all results: a result was on the
stack one round before. -/
theorem out_of_stack (P : σ → Prop) (s : σ) (h : ∀ i, ∀ x ∈ ((round step)^[i] ([s], [])).1, P x) (i : ℕ) :
    ∀ x ∈ ((round step)^[i] ([s], [])).2, P x := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := h i
    rw [Function.iterate_succ_apply']
    generalize (round step)^[i] ([s], []) = a at ih h1 ⊢
    obtain ⟨_ | ⟨y, r⟩, out⟩ := a
    · exact ih
    · simp only [Sparsify.round]
      cases step y with
      | none =>
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h1 x (by simp)
        · exact ih x hx
      | some lh => exact ih

end

/-- If the pad has at least 2·(number of leaves) − 1 units and the word of every state of the walk
is no longer than the pad, then `walkL` returns the leaves. -/
theorem walkL_eq (k : ℕ) (pad : U) (τ : ℕ) (r : CNode) (d : ℕ) (hd : ∀ x ∈ leaves (stepC (thetaU τ) k) d r, stepC (thetaU τ) k x = none)
    (hlen : 2 * (leaves (stepC (thetaU τ) k) d r).length ≤ pad.length + 1) (hst : ∀ i, len ((round (stepC (thetaU τ) k))^[i] ([r], [])) ≤ pad.length) :
    walkL k pad τ r = leaves (stepC (thetaU τ) k) d r := by
  unfold walkL
  rw [Top.foldl_capped_eq_iterate (cap pad ([], [])) (round (stepC (thetaU τ) k)) (fun x => len x ≤ pad.length)
    (fun x hx => cap_eq hx) pad ([r], []) (fun i _ => hst i),
    round_iterate_of_le (stepC (thetaU τ) k) d r hd pad.length (by omega)]
  simp

end SparsificationLemma.Mach
