/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Accel

/-!
# The paper, section "One scale is all scales": constants are postponed
-/

namespace Paper

open NS1
open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- The instance z_e of the paper: run p on the argument and accept exactly the runs whose bill uses each name the
prescribed number of times. -/
def postponed (p z : Tree) (e : Bt) : Tree := zq p z e

/-- **Paper: Lemma lem:postpone.** "Let all runs of a program p on an argument halt, the accepting ones within T < 2^J
steps and with names among the leaves of a binary trie with Q′ nodes and height η; let its leaves stand for powers
λ_1, λ_2, … Its value is ∑_e λ^e sum(z_e) over the vectors e with one entry in {0, …, 2^J−1} for every leaf, where the
instance z_e accepts exactly the runs of p whose bill uses each name the prescribed number of times. It is plain within
O(T(J + η + 1) + Q′J) steps, and its size is that of p and the argument plus O(Q′J)." The trie is L and L.budg J lists
the exponent vectors e with their λ^e. "Accepts exactly": the accepting runs of z_e, in their order, are those of p with ok e bill (every counter of e is 0
after the bill), with the same weights; pv(z_e) is therefore the sum of these weights. -/
theorem lem_postpone (p z : Tree) {T J : ℕ} (hJ : T < 2 ^ J) (hh : Hl θ (Fm.ofTree p) z)
    (hc : ∀ r ∈ evl θ (Fm.ofTree p) z, r.cost ≤ T) (L : KT R) (κ : List Bool → R)
    (hκ : ∀ r ∈ evl θ (Fm.ofTree p) z, ∀ n ∈ r.bill, κ n = L.lookup n) :
    val κ (evl θ (Fm.ofTree p) z) = ((L.budg J).map fun e => e.2 * algebraMap A R (pv θ (postponed p z e.1))).sum ∧
      ∀ e ∈ L.budg J,
        Plain θ ((1000 + 100 * (L.ht + J + 1)) * T + 40 * (L.nds * (J + 1)) + 40) (postponed p z e.1) ∧
        (postponed p z e.1).size ≤ WF.code.size + p.size + z.size + 4 * (L.nds * (J + 1)) + 3 ∧
        pv θ (postponed p z e.1) = ((evl θ (Fm.ofTree p) z).map fun r => if ok e.1 r.bill = true then r.th else 0).sum ∧
        (evl θ (Fm.ofTree (postponed p z e.1).hd) (postponed p z e.1).tl).map Run.th =
          ((evl θ (Fm.ofTree p) z).filter fun r => ok e.1 r.bill).map Run.th := by
  have hp : ∀ e ∈ L.budg J, Plain θ ((1000 + 100 * (L.ht + J + 1)) * T + 40 * (L.nds * (J + 1)) + 40) (zq p z e.1) ∧
      pv θ (zq p z e.1) = ((evl θ (Fm.ofTree p) z).map fun r => if ok e.1 r.bill = true then r.th else 0).sum ∧
      (evl θ (Fm.ofTree (zq p z e.1).hd) (zq p z e.1).tl).map Run.th =
        ((evl θ (Fm.ofTree p) z).filter fun r => ok e.1 r.bill).map Run.th :=
    fun e he => zq_plain hh.ev hc (KT.ht_budg he) (by
      have := Nat.mul_le_mul_left 40 (KT.nds_budg he)
      unfold MM
      omega)
  refine ⟨?_, fun e he => ⟨(hp e he).1, ?_, (hp e he).2⟩⟩
  · rw [val_eq_sum_budg (J := J) (K := L) (fun r hr => lt_of_le_of_lt ((bill_le hh.ev r hr).trans (hc r hr)) hJ) hκ]
    refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    rw [← (hp e he).2.1]
    rfl
  · have h1 := Bt.size_enc e.1
    have h2 := KT.nds_budg he
    simp only [postponed, zq, Tree.size]
    omega

end Paper
