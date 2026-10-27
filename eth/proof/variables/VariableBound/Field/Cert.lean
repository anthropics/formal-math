/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Field.Defs
public import PaddedDescent.F.FuelCert
public import ClauseBound.ParityChecks.CertLib
public import Mathlib.Data.List.Find

/-! # Lemma 13 (Family of checks), the claim that the sets Γ_u, u ∈ Ω, are listed in time polynomial in m: the list is computed in polynomial time

One certificate (`PolyT`) for each program of proof/variables/VariableBound/Field/Defs.lean, jointly
in all its arguments as functions of a context x. No mathematics of fields is used, only lengths of
words:
the sum of two words is as long as the shorter one, X·w is at most as long as w, and a product is at
most as long as the word g of the polynomial.
In every certificate the arguments are polynomial-time functions of the context. A number that a
program counts up to must moreover be given in unary (`Unary`), and the docstring says so:
the exponent of a power, the number s of bits together with 2^s, the number m of clauses, and, in
the last theorem, a. -/

public section

namespace VariableBound.Fld.Cert

open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib

variable {α : Type} [Enc α]

/-! ### Lengths -/

/-- The sum of two words is as long as the shorter of them. -/
theorem length_xorW (x y : List Bool) : (xorW x y).length = min x.length y.length := by
  simp [xorW]

/-- X·w is at most as long as w. -/
theorem length_mulX_le (g w : List Bool) : (mulX g w).length ≤ w.length := by
  unfold mulX
  split_ifs
  · rw [length_xorW, List.length_take, List.length_cons]
    omega
  · rw [List.length_take, List.length_cons]
    omega

/-- A product is at most as long as the word g. -/
theorem length_mulW_le (g x y : List Bool) : (mulW g x y).length ≤ g.length := by
  unfold mulW
  induction y with
  | nil => simp [zeroW]
  | cons b y ih =>
    rw [List.foldr_cons]
    split_ifs
    · rw [length_xorW]
      exact (min_le_right _ _).trans ((length_mulX_le _ _).trans ih)
    · exact (length_mulX_le _ _).trans ih

/-! ### The arithmetic -/

/-- The sum of two words is polynomial-time. -/
@[fun_prop] theorem xorW_polyT {x y : α → List Bool} (hx : PolyT x) (hy : PolyT y) : PolyT fun c => xorW (x c) (y c) := by
  unfold xorW; fun_prop

/-- The word 0 of the length of g is polynomial-time. -/
@[fun_prop] theorem zeroW_polyT {g : α → List Bool} (hg : PolyT g) : PolyT fun c => zeroW (g c) := by
  unfold zeroW; fun_prop

/-- The word 1 of the length of g is polynomial-time. -/
@[fun_prop] theorem oneW_polyT {g : α → List Bool} (hg : PolyT g) : PolyT fun c => oneW (g c) := by
  unfold oneW; fun_prop

/-- Multiplication by X is polynomial-time. -/
@[fun_prop] theorem mulX_polyT {g w : α → List Bool} (hg : PolyT g) (hw : PolyT w) : PolyT fun c => mulX (g c) (w c) := by
  unfold mulX; fun_prop

/-- The inner product of two words is polynomial-time. -/
@[fun_prop] theorem ipW_polyT {x y : α → List Bool} (hx : PolyT x) (hy : PolyT y) : PolyT fun c => ipW (x c) (y c) := by
  unfold ipW; fun_prop

/-- Multiplication is polynomial-time. -/
@[fun_prop] theorem mulW_polyT {g x y : α → List Bool} (hg : PolyT g) (hx : PolyT x) (hy : PolyT y) : PolyT fun c => mulW (g c) (x c) (y c) := by
  unfold mulW
  refine PolyT.foldr_add (a := fun c => zeroW (g c)) (g := fun c b r => if b then xorW (x c) (mulX (g c) r) else mulX (g c) r) hy (by fun_prop) (by fun_prop)
    ⟨fun _ => 0, PB.const 0, fun c r b _ => ?_⟩
  rw [len_bools, len_bools]
  have h := length_mulX_le (g c) r
  split_ifs
  · rw [length_xorW]
    omega
  · omega

/-- Powers are polynomial-time, if the exponent is given in unary. -/
@[fun_prop] theorem powW_polyT {g u : α → List Bool} {e : α → ℕ} (hg : PolyT g) (hu : PolyT u) (he : Unary e) : PolyT fun c => powW (g c) (u c) (e c) := by
  unfold powW
  obtain ⟨t, ht, -, hlen⟩ := PolyT.len_bound hg
  refine PolyT.foldl_add (l := fun c => List.range (e c)) (a := fun c => oneW (g c)) (g := fun c r _ => mulW (g c) r (u c)) (by fun_prop) (by fun_prop) (by fun_prop) ⟨t, ht, fun c r _ _ => ?_⟩
  have h1 := length_mulW_le (g c) r (u c)
  have h2 := hlen c
  rw [len_bools] at h2 ⊢
  omega

/-! ### The search for the polynomial -/

/-- The list of all words of s bits is polynomial-time, if s and 2^s are given in unary. -/
theorem wordsL_polyT {s : α → ℕ} (hs : Unary s) (h2 : Unary fun c => 2 ^ s c) : PolyT fun c => wordsL (s c) := by
  have hr := PolyT.range h2
  have hw : PolyT fun p : α × ℕ => toWord (s p.1) p.2 := PolyT.toWord' (hs.comp (by fun_prop)) (by fun_prop)
  unfold wordsL
  fun_prop

/-- The test `irrW` with the number s of bits as an argument of its own. -/
def irrS (s : ℕ) (g : List Bool) : Bool :=
  (wordsL s).all fun x => decide (x = zeroW g) || (wordsL s).any fun y => decide (mulW g x y = oneW g)

/-- The test with the number s of bits as an argument is polynomial-time, if s and 2^s are given in
unary. -/
theorem irrS_polyT {s : α → ℕ} {g : α → List Bool} (hs : Unary s) (h2 : Unary fun c => 2 ^ s c) (hg : PolyT g) : PolyT fun c => irrS (s c) (g c) := by
  have h1 := wordsL_polyT hs h2
  have h3 : PolyT fun p : α × List Bool => wordsL (s p.1) := PolyT.comp (g := fun p : α × List Bool => p.1) h1 (by fun_prop)
  unfold irrS
  fun_prop

/-- Every word in the list of the words of s bits has s bits. -/
theorem length_of_mem_wordsL {s : ℕ} {g : List Bool} (h : g ∈ wordsL s) : g.length = s := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 h
  exact length_toWord s y

/-- The search for the polynomial is polynomial-time, if s and 2^s are given in unary. -/
theorem modW_polyT {s : α → ℕ} (hs : Unary s) (h2 : Unary fun c => 2 ^ s c) : PolyT fun c => modW (s c) := by
  have h1 := wordsL_polyT hs h2
  have h3 : PolyT fun p : α × List Bool => irrS (s p.1) p.2 :=
    irrS_polyT (hs.comp (by fun_prop)) (h2.comp (h := fun p : α × List Bool => p.1) (by fun_prop)) (by fun_prop)
  have h : PolyT fun c => ((wordsL (s c)).find? fun g => irrS (s c) g).getD [] := by fun_prop
  refine h.congr fun c => ?_
  unfold modW
  rw [List.find?_congr fun g hg => ?_]
  rw [irrS, irrW, length_of_mem_wordsL hg]

/-! ### The family -/

/-- The set Γ_u is polynomial-time jointly in m, a, g and u, if m is given in unary. -/
theorem gamW_polyT {m a : α → ℕ} {g : α → List Bool} {u : α → List Bool × List Bool × List Bool × List Bool} (hm : Unary m) (ha : PolyT a) (hg : PolyT g) (hu : PolyT u) :
    PolyT fun c => gamW (m c) (a c) (g c) (u c) := by
  have h0 := hm.poly
  have h1 : Unary fun p : α × ℕ => min p.2 (m p.1) := unary_min_right (by fun_prop) (hm.comp (by fun_prop))
  have h : PolyT fun c => (List.range (m c)).filter fun E =>
      (((xorW (mulW (g c) (u c).1 (toWord (g c).length E)) (u c).2.1).take (a c - 1)).all fun b => !b)
        && ipW (powW (g c) (u c).2.2.1 (min E (m c))) (u c).2.2.2 := by fun_prop
  refine h.congr fun c => ?_
  unfold gamW
  refine List.filter_congr fun E hE => ?_
  rw [min_eq_left (List.mem_range.1 hE).le]

/-- The number s of bits is given in unary, for any polynomial-time m. -/
theorem sD_unary {m : α → ℕ} (hm : PolyT m) : Unary fun c => sD (m c) := by
  unfold sD
  exact clog_unary (by fun_prop)

/-- 2^s ≤ 32m + 1 for the number s of bits. -/
theorem two_pow_sD_le (m : ℕ) : 2 ^ sD m ≤ 32 * m + 1 := by
  unfold sD
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : 1 < 16 * m := by omega
    have h2 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
    have h3 : 0 < Nat.clog 2 (16 * m) := Nat.clog_pos (by norm_num) (by omega)
    have h4 : 2 ^ Nat.clog 2 (16 * m) = 2 * 2 ^ (Nat.clog 2 (16 * m)).pred := by
      rw [← pow_succ', Nat.pred_eq_sub_one, Nat.sub_add_cancel h3]
    omega

/-- 2^s is given in unary for the number s of bits, if m is. -/
theorem two_pow_sD_unary {m : α → ℕ} (hm : Unary m) : Unary fun c => 2 ^ sD (m c) := by
  have h0 := hm.poly
  have h1 := sD_unary h0
  exact Unary.of_le (g := fun c => 32 * m c + 1) (by fun_prop) (by fun_prop) fun c => two_pow_sD_le (m c)

/-- Lemma 13 (Family of checks), the claim that the sets Γ_u, u ∈ Ω, are listed in time polynomial
in m: the list is computed in polynomial time, jointly in m and a, both given in unary. -/
theorem stCertFamD : StCertFamD := by
  intro α _ m a hm ha
  have h0 := hm.poly
  have h0' := ha.poly
  have hs := sD_unary h0
  have h2 := two_pow_sD_unary hm
  have hw := wordsL_polyT hs h2
  have hg := modW_polyT hs h2
  have hG : PolyT fun p : α × List Bool × List Bool × List Bool × List Bool => gamW (m p.1) (a p.1) (modW (sD (m p.1))) p.2 :=
    gamW_polyT (hm.comp (by fun_prop)) (by fun_prop) (PolyT.comp (g := fun p : α × List Bool × List Bool × List Bool × List Bool => p.1) hg (by fun_prop)) (by fun_prop)
  unfold famD
  fun_prop

end VariableBound.Fld.Cert
