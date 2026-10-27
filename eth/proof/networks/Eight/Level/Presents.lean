/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Level.Defs
public import SingleBitPieces.Level.Presents
import Mathlib.Tactic

/-! # Proposition 3 through Lemma 2 from the eight-square identity: the procedures present the network

The counterpart of proof/networks/SingleBitPieces/Level/Presents.lean for the pieces of Lemma 2 from
the eight-square identity. `stPresents_of`: the procedures `levelNet g tr` (a weight by g queries to
the tables of the clique, a value of a factor in one step) compute the weights and the factors of
the network
`netOfι g tr λ y Rm`, the row network or the column network of ι : ℛ → {0, …, ⌈λ/3⌉}, within a·(B +
λ)^a·t steps (t the cost of a query to the tables of the clique, not ⌈λ/3⌉) and size S + a·(size c +
B + λ)^a. In the paper it is the sentence «Both networks satisfy
Definition 2 with … τ = poly(B + λ)» in the proof of Proposition 3.
Here the values of the pieces have ⌈λ/3⌉ ≤ 2λ bits, so `presentsP8` proves the statement for pieces
whose values have at most 2λ bits. The lemmas of proof/networks/SingleBitPieces/Level/Presents.lean
that hold for any family of pieces
(`W_eq`, `f_eq`, `time_W`, `time_f`, `size_f`) are used as they are; they ask for y < (λ + 1)^{|ℛ|},
which follows from y < (⌈λ/3⌉ + 1)^{|ℛ|}. -/

public section

namespace Eight.Level

open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped SingleBitPieces.Level.Presents

namespace Presents

/-- ⌈λ/3⌉ ≤ λ. -/
theorem tOf_le (lam : ℕ) : tOf lam ≤ lam := by unfold tOf; omega

/-- The network of a level given by procedures, for any pieces. -/
def netP8 (P : PiecesF) (g : ℕ) (tr : Bool) : NetFormer := fun lam R =>
  { n := fun c _ => nMemb g g tr * (g * g) * lam c.1
    cap := fun c a b => capG P g g tr 0 (lam c.1) c.2 a b
    W := sideWP g tr lam R
    f := ofFun fun x => gridFf P [] g g tr 0 (lam x.1.1) x.1.2 x.2 }

/-- The procedures present the network, for any pieces that factor through at most 2λ bits and have
values of at most 2λ bits. -/
theorem presentsP8 (P : PiecesF) (hm : P.m = 1) (hbits : ∀ ℓ, P.bits 0 ℓ ≤ 2 * ℓ) (g : ℕ) (tr : Bool) {C : Type} [HasSize C] (lam : C → ℕ)
    (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) {A : ℕ → Pieces.Four (lam c)}
    (hcuts : CutsOK P [] 0 (lam c) A) (hl : 1 ≤ lam c) (ht : 1 ≤ t) (hy : y < (lam c + 1) ^ nRect g) (hR : ServesInst R c (lam c) B t S Rm) :
    (netP8 P g tr lam R).Presents (c, y) (gridN P [] g g tr 0 (lam c) y Rm) (sideA g * (B + lam c) ^ sideA g * t)
      (S + sideA g * (size c + B + lam c) ^ sideA g) := by
  have hB : BoundedInst (lam c) B Rm := fun v θ h1 h2 => (hR v θ h1 h2).2
  have hlen : ∀ z : List Bool, z.length = nMemb g g tr * (g * g) * lam c → z.length = g ^ 3 * lam c := by
    intro z hz
    rw [hz, nMemb_self]
    ring
  refine ⟨fun a => gridN_S _ _ _ _ _ _ _ _ _ a, fun a b hab => gridN_c _ _ _ _ _ _ _ _ _ hab, fun a b hab => gridN_lab _ _ _ _ _ _ _ _ _ hab,
    fun a z hz => ?_, fun a b z θ hab hz hθ => ?_⟩
  · have hz' : z.length = nMemb g g tr * (g * g) * lam c := hz
    have ha : a.val < g := lt_of_lt_of_eq a.2 (nParts_self g tr)
    rw [W_eq P tr lam Rm c y a hz']
    exact (sideWP_runs hR y ha (hlen z hz')).mono (time_W g B (lam c) hl ht) (side_size_W g B S (lam c) hl c hy ha (hlen z hz'))
  · have hz' : z.length = nMemb g g tr * (g * g) * lam c := hz
    have hθ' : θ.length = capG P g g tr 0 (lam c) y a b := hθ
    have ha : a.val < g := lt_of_lt_of_eq a.2 (nParts_self g tr)
    have hb : b.val < g := lt_of_lt_of_eq b.2 (nParts_self g tr)
    have hθl : θ.length ≤ g ^ 2 * lam c := by
      have h1 := gridN_c_le hcuts g g tr y Rm a b
      rw [gridN_c _ _ _ _ _ _ _ _ _ hab, nMemb_self, hm, Nat.one_mul] at h1
      rw [hθ']
      exact h1
    have hv : |(gridN P [] g g tr 0 (lam c) y Rm).f a b z θ| ≤ 2 ^ (g * B + g ^ 2 * (2 * lam c)) := by
      have h1 := (gridN_sized hcuts g g tr y hB).abs_f a b z θ
      rw [nMemb_self] at h1
      exact h1.trans (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hbits _)) _))
    have hrun : (ofFun fun x : (C × ℕ) × FQ => gridFf P [] g g tr 0 (lam x.1.1) x.1.2 x.2).Runs ((c, y), ((a.val, b.val), (z, θ))) 1
        (max (size ((c, y), ((a.val, b.val), (z, θ)))) (size (gridFf P [] g g tr 0 (lam c) y ((a.val, b.val), (z, θ)))) + 1)
        (gridFf P [] g g tr 0 (lam c) y ((a.val, b.val), (z, θ))) :=
      ofFun_runs (fun x : (C × ℕ) × FQ => gridFf P [] g g tr 0 (lam x.1.1) x.1.2 x.2) ((c, y), ((a.val, b.val), (z, θ)))
    rw [f_eq P tr (lam c) y Rm hab hz' hθ'] at hrun
    exact hrun.mono (time_f g B (lam c) hl ht) (size_f g B S (lam c) hl c hy ha hb (hlen z hz') hθl hv)

end Presents

open Presents

/-- **Proof of Proposition 3**, «Both networks satisfy Definition 2 … with τ = poly(B + λ)»: the
procedures of a level present the row network and the column network of ι : ℛ → {0, …, ⌈λ/3⌉},
within a·(B + λ)^a·t steps, where t is the cost of a
query to the tables of the clique. Same as in the paper; the paper does not speak of sizes. -/
theorem stPresents_of (hP : StPieces) : StPresents := fun g tr =>
  ⟨sideA g, fun _ _ lam R c B t S Rm y hl ht hy hR =>
    presentsP8 eightF rfl (fun ℓ => (tOf_le ℓ).trans (Nat.le_mul_of_pos_left ℓ (by norm_num))) g tr lam R c B t S Rm y (hP (lam c) hl).2 hl ht
      (hy.trans_le (Nat.pow_le_pow_left (Nat.succ_le_succ (tOf_le (lam c))) _)) hR⟩

end Eight.Level
