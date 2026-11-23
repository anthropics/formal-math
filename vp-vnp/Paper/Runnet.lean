/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.Start
import Nc.Dl.Facts

/-!
# The paper, section "Cutting computations": runs as networks
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset

/-- **Paper: Lemma lem:runnet.** "Let K, T ≥ 1, let T′ ≤ T, and let an input word of at most KT′ symbols be cut into K
consecutive parts of T′ symbols, the last ones possibly shorter or empty. Order the 2K nodes: the K blocks of T steps,
then the K parts; regard the input as one more tape, written by the parts and read by the blocks. Data ρ say, for every
tape and every node, whether the node writes nothing on the tape, and otherwise the first and the last node that read
its symbols. They are valid if on every tape the first reader of a node is not before the last reader of the node
before it; a node that writes nothing repeats that last reader, so that ρ is determined by the sequence. For the first
node, the first node itself takes the place of that last reader. The value in KT steps is the sum, over boundary states
q ∈ Q^(K+1) with q₀ = q⁻ and q_K = q⁺, over valid ρ, and over the numbers of units of ℓ bits between any two nodes,
each at most (T+|S|+1)c/ℓ+1, of the values of networks on these 2K nodes; here S is the set of tapes, and symbols and
an end mark are coded by c bits. A node whose table is not 0 has at most 2((T+2K(|S|+1))c/ℓ+2K) units." Here ub is the
paper's ℓ, and the parts are consecutive parts of ℓ = T′ symbols (Cut.parts), the only cuts stated. The numbers run up
to any U0 ≥ (T+|S|+1)c/ub+1. -/
theorem lem_runnet {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
    [Fintype Q] [DecidableEq Q] (mu : Nc.Letter S Unit Γ → Matrix Q Q F) {T c ub K A' U0 U1 : ℕ}
    (cb : Option Γ → Fin c → Bool) {N : Type} [Fintype N] [DecidableEq N] (hcb : Function.Injective cb) (hc : 0 < c)
    (hub : 0 < ub) (hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ U0) (np : N → Bool → Fin (K + K + A')) (i e : Q)
    (u : Unit → List Γ) {ℓ : ℕ} (hℓ : ℓ ≤ T) (hu : (u ()).length ≤ K * ℓ) :
    open Classical in
    (Nc.runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ ρ : Option S → Fin (K + K) → Nc.Cut.RowData (K + K), if Nc.Cut.ValidRows ρ then
        ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1),
          Nc.posVal (Nc.G.hold0 np) (Nc.G.hold1 np) (none : Nc.UW ub) (Nc.G.seen0 (N := N) (U1 := U1) n) (Nc.G.seen0 n)
            fun y => ∏ p : Fin (K + K), Nc.G.tabInit mu T cb q (Nc.Cut.parts ℓ (u ())) (fun s => ρ s p)
              (fun a b => (n a b).1) p (y (Fin.castAdd A' p))
      else 0
    else 0) ∧
    ∀ (q : Fin (K + 1) → Q) (ρ : Option S → Nc.Cut.RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
      (p : Fin (K + K)) (y : Nc.G.Uid (K + K) U0 N U1 → Nc.UW ub),
      Nc.G.tabInit mu T cb q (Nc.Cut.parts ℓ (u ())) ρ (fun a b => (n a b).1) p y ≠ 0 →
        ∑ b, ((n p b).val + (n b p).val) ≤ 2 * ((T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K)) := by
  classical
  refine ⟨Nc.G.start hcb hc hub hU np i e u hℓ hu, fun q ρ n p y h => ?_⟩
  rw [Nc.G.tabInit_eq] at h
  obtain ⟨R, -, h3⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨C, -, h4⟩ := Finset.exists_ne_zero_of_sum_ne_zero h3
  split_ifs at h4 with h5
  · exact Nc.Dl.init_count (fun κ => (Nc.Cut.length_parts_le _ _ _).trans hℓ) h5 h4
  · exact absurd rfl h4

end Paper
