/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.ProgDefs

/-! # One evaluation is exact

`stEvW : StEvW`, from the interface statements on the network of marks (its value, the sum over the
profiles, that the programs present it, its size) and on the evaluation of any network on
3K⁸ nodes through a clique solver. One evaluation `evW` is the sum over the admissible profiles of a
weight times the number that the solver returns for the network of marks of the profile. The
solver returns the value of that network, because the size of the network is at most `PbOL` and its
total at most `UbOL` (`StMarkSized`; the two bounds grow with the number of variables, the cap
and the number of layers, which are at most 7n, 11n and 3) and the pad is long enough (`StValS`).
Then `ClauseBound.TopN.EvalW.evalV_truncW_ctx` gives the product form `truncW`. -/

public section

namespace ClauseBound.ParityChecks.Ev

open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW

/-- The length of n in unary. -/
theorem length_rep (n : ℕ) : (rep n).length = n := List.length_replicate

/-- The bound for the total of the network of marks grows with the number of variables, the cap and
the number of layers. -/
theorem Ub_mono (k g β : ℕ) {n n' w w' R R' : ℕ} (hn : n ≤ n') (hw : w ≤ w') (h : R ≤ R') : Ub k g n w β R ≤ Ub k g n' w' β R' := by
  unfold Ub
  refine Nat.mul_le_mul (Nat.mul_le_mul_left _ h) (Nat.add_le_add_right (Nat.add_le_add ?_ ?_) _)
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hw)
  · exact Nat.mul_le_mul_left _ (by omega)

/-- The bound for the size of the network of marks grows with the number of variables. -/
theorem Pb_mono (g β D : ℕ) {n n' : ℕ} (hn : n ≤ n') : Pb g n β D ≤ Pb g n' β D := by
  unfold Pb qv
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.div_le_div_right (by omega)))

/-- A network of size P is a network of every larger size. -/
theorem sized_mono {J σ τ : Type} [Fintype J] [LinearOrder J] {N : Network J σ τ} {P P' B : ℕ} (h : N.Sized P B) (hP : P ≤ P') : N.Sized P' B where
  card_S a := (h.card_S a).trans (Nat.pow_le_pow_right (by norm_num) hP)
  c_symm := h.c_symm
  sum_c a := (h.sum_c a).trans hP
  card_lab := h.card_lab
  abs_W := h.abs_W
  abs_f := h.abs_f
  abs_Ψ := h.abs_Ψ

/-- One evaluation is exact; the numbers of nodes and of variables, the cap and the two code
parameters are the lengths of any lists of units, and U₀ and P₀ are any bounds for the total and the
size of the networks. -/
theorem evalV_valS (hV : StMarkVal) (hP : StProfSum) (hPr : StMarkPresents) (hSz : StMarkSized) (hVal : StValS)
    {Idx : Type} [Enc Idx] (S : Solver Idx) (ok : Idx → Prop) (hC : S.Correct ok) (k : ℕ) (pad : U) (i : Idx) (gu nu wu βu bu : U) (D U₀ P₀ : ℕ)
    (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) (hok : ok i) (hK : 2 ≤ S.K i) (hgu : gu.length = 3 * S.K i ^ 8) (hb : 0 < bu.length)
    (hb' : bu.length ≤ 2 ^ βu.length) (hW : WfL k nu.length Ls) (hocc : ∀ v, (occ Ls.flatten v).length ≤ D)
    (hfl : Ls.flatten.length ≤ bu.length * (nu.length + 1)) (hhi : ∀ l < Ls.length, hi.getD l 0 ≤ wu.length)
    (hprof : nProf gu.length (cls Ls).length Ls.length ≤ pad.length)
    (hU : Ub k gu.length nu.length wu.length βu.length Ls.length ≤ U₀) (hP₀ : Pb gu.length nu.length βu.length D ≤ P₀)
    (hnet : 2 ^ needNet S i U₀ P₀ 0 ≤ pad.length) :
    evalV k pad gu (fun c => GW c.2.1.length ws lo hi (tl c.1.1.length c.2.1 c.2.2) * valS S pad i U₀ P₀ markF c) (nu, wu, βu, bu) Ls =
      truncW nu.length ws lo hi Ls := by
  have hg : 0 < gu.length := by
    rw [hgu]
    have : 0 < S.K i := by omega
    positivity
  have hVal' : ∀ g : ℕ, g = 3 * S.K i ^ 8 → ∀ (c : MCtx) (N : Network (Fin g) (List Bool) (List Bool)),
      markF.toP.Presents c N 0 0 → N.Sized P₀ 0 → N.U ≤ U₀ → valS S pad i U₀ P₀ markF c = N.value := by
    intro g hg'
    subst hg'
    intro c N h1 h2 h3
    exact hVal Idx S ok hC MCtx markF c pad i N U₀ P₀ 0 hok hK h1 h2 h3 hnet
  refine evalV_truncW_ctx hV hP k pad gu _ (nu, wu, βu, bu) Ls ws lo hi hg hb hb' hW hprof hhi fun y hy _ => ?_
  obtain ⟨h1, h2⟩ := hSz k gu nu βu bu wu.length D Ls y hg hb hb' hW hocc hfl hy
  exact hVal' gu.length hgu ((gu, nu, βu, bu), (Ls, y)) _ (hPr ((gu, nu, βu, bu), (Ls, y))) (sized_mono h1 hP₀) (h2.trans hU)

/-- One evaluation is exact on three layers (or two) of clauses of 1 to k + 1 literals on n + r
variables in which no variable occurs too often. -/
theorem stEvW (hV : StMarkVal) (hP : StProfSum) (hPr : StMarkPresents) (hSz : StMarkSized) (hVal : StValS) : StEvW := by
  intro Idx _ S ok hC k pad i n Δ q ws lo hi Ls hok hK hr hcap hlen hW hocc hfl hhi hprof hnet
  have h := evalV_valS hV hP hPr hSz hVal S ok hC (k + 1) pad i (rep (3 * S.K i ^ 8)) (rep (n + q.r)) (rep (capM q)) (rep (bitOL Δ)) (rep (blkOL Δ))
    (occOL n Δ) (UbOL k (S.K i) n Δ) (PbOL (S.K i) n Δ) ws lo hi Ls hok hK (length_rep _) (by rw [length_rep]; unfold blkOL; omega)
    (by rw [length_rep, length_rep]; exact Nat.le_pow_clog (by norm_num) _) (by rw [length_rep]; exact hW) hocc
    (by rw [length_rep, length_rep]; exact hfl) (by rw [length_rep]; exact hhi) (by rw [length_rep]; exact hprof)
    (by simp only [length_rep]; exact Ub_mono _ _ _ (by omega) hcap hlen) (by simp only [length_rep]; exact Pb_mono _ _ _ (by omega)) hnet
  simp only [length_rep] at h
  exact h

end ClauseBound.ParityChecks.Ev
