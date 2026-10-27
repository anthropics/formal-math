/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import PaddedDescent.F.CertSparsify
public import ToTuring.Poly.Sat

/-! Polynomial-time certificates (`PolyT`) for the top part of the function `A` of
proof/rates/PaddedDescent/F/Prog.lean: the schedule (`schedF_polyT`) and the walk of the
sparsification tree with τ as data (`certWalk`), which proves the interface statement `StCertWalk`
of proof/rates/PaddedDescent/F/Interfaces.lean. The
file also shows that numbers that `A` computes from the number n of variables are given in unary (τ,
the number of levels, the number of layers), and that
the parameters of the evaluations are computed in polynomial time (`markPar_polyT`). The
certificates of the evaluations are in proof/rates/PaddedDescent/F/CertEval.lean, that of `A` itself
in
proof/rates/PaddedDescent/F/CertA.lean. -/

@[expose] public section

namespace PaddedDescent.F.CertTop

open Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Sparsify
open WidthK (theta)
open WidthK.Prog (stepK)

variable {α : Type} [Enc α]

/-! ### The schedule -/

/-- 3K⁸ in unary is polynomial-time in K in unary. -/
@[fun_prop] theorem gU_polyT {K : α → U} (hK : PolyT K) : PolyT fun x => gU (K x) := by
  unfold gU; fun_prop

/-- K·L in unary is polynomial-time in K and L in unary. -/
@[fun_prop] theorem mulU_polyT {K L : α → U} (hK : PolyT K) (hL : PolyT L) : PolyT fun x => mulU (K x) (L x) := by
  unfold mulU; fun_prop

/-- g² in unary is polynomial-time in g in unary. -/
@[fun_prop] theorem sqU_polyT {g : α → U} (hg : PolyT g) : PolyT fun x => sqU (g x) := by
  unfold sqU; fun_prop

/-- The schedule, jointly in the pad and the number t of levels (in unary). Its start does not
depend on the input, and the pad caps every round. -/
theorem schedF_polyT {pad : α → U} {t : α → ℕ} (hp : PolyT pad) (ht : Unary t) : PolyT fun x => schedF (pad x) (t x) := by
  unfold schedF
  exact foldl_cap (pad := pad) (l := fun x => List.replicate (t x) ())
    (a := fun _ => (([] : List Lvl), (List.replicate 256 () : U), (List.replicate (Lseq 0) () : U)))
    (g := fun _ st _ => ((st.2.1, mulU st.2.1 st.2.2) :: st.1, sqU (mulU st.2.1 st.2.2), st.2.2 ++ st.2.2)) ([], [], []) hp ht
    (PolyT.const _) (by fun_prop)

/-! ### The walk -/

/-- The walk of the sparsification tree is polynomial-time jointly in the pad, τ, the root and
whatever the test depends on. -/
theorem certWalk : StCertWalk := by
  intro k α _ pad τ test r hp hτ ht hr
  have h := foldl_cap (pad := pad) (l := pad) (a := fun x => ([r x], false))
    (g := fun x st _ => roundB (stepK (theta (τ x)) k) (test x) st) ([], false) hp hp (by fun_prop)
    (polyT_roundB (step := fun p : α × (List PFml × Bool) × Unit => stepK (theta (τ p.1)) k) (test := fun p => test p.1) (st := fun p => p.2.1)
      (by fun_prop) (by fun_prop) (by fun_prop))
  unfold walkF
  exact PolyT.snd h

/-! ### The parameters read off the input, in unary -/

/-- 2^(sOf n) is at most n + 1. -/
theorem two_pow_sOf_le (n : ℕ) : 2 ^ sOf n ≤ n + 1 := by
  have h1 : sOf n ≤ Nat.log2 (Nat.log2 n) := by unfold sOf; omega
  have h2 : 2 ^ sOf n ≤ 2 ^ Nat.log2 (Nat.log2 n) := Nat.pow_le_pow_right (by norm_num) h1
  rcases Nat.eq_zero_or_pos (Nat.log2 n) with h | h
  · rw [h] at h2
    simp only [Nat.log2_zero, pow_zero] at h2
    omega
  · have h3 := Nat.log2_self_le (Nat.pos_iff_ne_zero.1 h)
    have h4 := Nat.log2_le_self n
    omega

/-- sOf n is at most n. -/
theorem sOf_le (n : ℕ) : sOf n ≤ n := by
  have h1 := two_pow_sOf_le n
  have h2 : sOf n < 2 ^ sOf n := Nat.lt_two_pow_self
  omega

/-- The precision sOf n is polynomial-time in n. -/
@[fun_prop] theorem sOf_polyT {n : α → ℕ} (hn : PolyT n) : PolyT fun x => sOf (n x) := by
  unfold sOf
  exact PolyT.div (PolyT.mul (PolyT.const 3) (PolyT.sub (PolyT.log2' (PolyT.log2' hn)) (PolyT.const 911))) (PolyT.const 19)

/-- The precision sOf n is given in unary if n is. -/
@[fun_prop] theorem sOf_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => sOf (n x) :=
  hn.of_le (sOf_polyT hn.poly) fun x => sOf_le (n x)

/-- The number of levels is given in unary if n is. -/
@[fun_prop] theorem depthOf_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => depthOf (sOf (n x)) := by
  unfold depthOf; fun_prop

/-- 2^(a·s + c) is given in unary if n is, for s = sOf n and any numbers a and c, since 2^(sOf n) ≤
n + 1. -/
theorem two_pow_lin_unary (a c : ℕ) {n : α → ℕ} (hn : Unary n) : Unary fun x => 2 ^ (a * sOf (n x) + c) := by
  refine Unary.of_le (g := fun x => (n x + 1) ^ a * 2 ^ c) (by fun_prop) (by fun_prop) fun x => ?_
  rw [pow_add, Nat.mul_comm a, pow_mul]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (two_pow_sOf_le (n x)) a)

/-- The threshold τ of the sparsification is given in unary if n is, since 2^(sOf n) ≤ n + 1. -/
@[fun_prop] theorem tauOf_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => tauOf (sOf (n x)) := by
  unfold tauOf
  exact two_pow_lin_unary 4 17 hn

/-- The cap of the cut-off sums is given in unary if n is. -/
@[fun_prop] theorem capOf_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => capOf (n x) := by
  unfold capOf; fun_prop

/-- The logarithm of the length of a block of the code is given in unary if n is. -/
@[fun_prop] theorem betaOf_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => betaOf (sOf (n x)) := by
  unfold betaOf; fun_prop

/-- The number of layers is given in unary if n is. -/
@[fun_prop] theorem layersOf_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => layersOf (sOf (n x)) := by
  have := betaOf_unary hn
  unfold layersOf; fun_prop

/-- 2^(betaOf (sOf n)) is at most n + 2^49. For sOf n = 0 it is 2^49. For s = sOf n ≥ 1 the
logarithm of the logarithm of n is at least 2s + 6, so that
betaOf s = (s + 7)² ≤ 2^(2s + 6) is at most the logarithm of n. -/
theorem two_pow_betaOf_le (n : ℕ) : 2 ^ betaOf (sOf n) ≤ n + 2 ^ 49 := by
  rcases Nat.eq_zero_or_pos (sOf n) with h | h
  · rw [h, show betaOf 0 = 49 from rfl]
    exact Nat.le_add_left _ _
  · have h1 : 2 * sOf n + 6 ≤ Nat.log2 (Nat.log2 n) := by unfold sOf at h ⊢; omega
    have h0 : Nat.log2 n ≠ 0 := by
      intro h0
      rw [h0, Nat.log2_zero] at h1
      omega
    have hn : n ≠ 0 := by
      rintro rfl
      exact h0 Nat.log2_zero
    have h2 := Nat.log2_self_le h0
    have h3 := Nat.log2_self_le hn
    have h4 : sOf n + 7 ≤ 2 ^ (sOf n + 3) := by
      have : sOf n < 2 ^ sOf n := Nat.lt_two_pow_self
      rw [pow_add]
      omega
    have h5 : betaOf (sOf n) ≤ Nat.log2 n :=
      calc (sOf n + 7) ^ 2 ≤ (2 ^ (sOf n + 3)) ^ 2 := Nat.pow_le_pow_left h4 2
        _ = 2 ^ (2 * sOf n + 6) := by rw [← pow_mul]; congr 1; ring
        _ ≤ 2 ^ Nat.log2 (Nat.log2 n) := Nat.pow_le_pow_right (by norm_num) h1
        _ ≤ Nat.log2 n := h2
    exact ((Nat.pow_le_pow_right (by norm_num) h5).trans h3).trans (Nat.le_add_right _ _)

/-- The length of a block of the code is given in unary if n is, since it is at most n + 2^49. -/
@[fun_prop] theorem two_pow_betaOf_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => 2 ^ betaOf (sOf (n x)) :=
  Unary.of_le (hn.add (Unary.const (2 ^ 49))) (PolyT.pow_unary (PolyT.const 2) (betaOf_unary hn)) fun x => two_pow_betaOf_le (n x)

/-- The parameters of the evaluations are polynomial-time in n in unary. -/
theorem markPar_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun x => markPar (n x) (sOf (n x)) :=
  PolyT.prodMk hn (PolyT.prodMk (capOf_unary hn) (PolyT.prodMk (betaOf_unary hn) (two_pow_betaOf_unary hn)))

/-- The number of variables written in the input is given in unary. -/
theorem nOf_unary : Unary fun x : List Bool => (Decode.dec x).1 :=
  Unary.of_length (w := fun x : List Bool => x.takeWhile id) (by fun_prop)

end PaddedDescent.F.CertTop
