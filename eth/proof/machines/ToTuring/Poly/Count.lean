/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.Spec
public import ToTuring.Poly.IsPoly
public import ToTuring.Lib.List3
public import StepMachines.Prog.Count

/-! The network of a k-CNF of Section 6 and of the proof of Theorem A (c) (clauses cut into g
groups, one bit for each literal slot, one-bit equality
wires), defined in StepMachines/Prog/CountNet.lean (functions) and Prog/Count.lean (`satP`). The
plain functions that define it are
polynomial-time (`PolyT`). Its two
lengths, the state bits of a node (`n_unary`) and the label bits of a pair of nodes (`capF_unary`),
are `Unary`. -/

@[expose] public section

namespace Groundwork.Prog.Count

variable {α : Type} [Enc α] (g k : ℕ)

@[fun_prop] theorem mu_polyT {φ : α → Fml} (hφ : PolyT φ) : PolyT fun x => mu g (φ x) := by
  unfold mu; fun_prop

@[fun_prop] theorem litAt_polyT {φ : α → Fml} {i : α → ℕ} (hφ : PolyT φ) (hi : PolyT i) :
    PolyT fun x => litAt k (φ x) (i x) := by
  unfold litAt; fun_prop

@[fun_prop] theorem varAt_polyT {φ : α → Fml} {i : α → ℕ} (hφ : PolyT φ) (hi : PolyT i) :
    PolyT fun x => varAt k (φ x) (i x) := by
  unfold varAt; fun_prop

@[fun_prop] theorem slotsOf_polyT {φ : α → Fml} (hφ : PolyT φ) : PolyT fun x => slotsOf k (φ x) := by
  unfold slotsOf
  exact PolyT.range (Unary.of_length (by fun_prop))

@[fun_prop] theorem linkB_polyT {φ : α → Fml} {i i' : α → ℕ} (hφ : PolyT φ) (hi : PolyT i) (hi' : PolyT i') :
    PolyT fun x => linkB k (φ x) (i x) (i' x) := by
  unfold linkB; fun_prop

@[fun_prop] theorem locals_polyT {φ : α → Fml} (hφ : PolyT φ) : PolyT fun x => locals g k (φ x) := by
  unfold locals; fun_prop

@[fun_prop] theorem rows_polyT {φ : α → Fml} (hφ : PolyT φ) : PolyT fun x => rows g (φ x) := by
  have h : PolyT fun x => List.range (φ x).length := PolyT.range (Unary.of_length hφ)
  unfold rows; fun_prop

@[fun_prop] theorem links_polyT {φ : α → Fml} {a b : α → ℕ} (hφ : PolyT φ) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => links g k (φ x) (a x) (b x) := by
  have h : PolyT fun x => ((locals g k (φ x)).product (locals g k (φ x))).filter fun p =>
      linkB k (φ x) (a x * (mu g (φ x) * k) + p.1) (b x * (mu g (φ x) * k) + p.2) := by fun_prop
  exact h

/-- The weight of a group of clauses at a state word is polynomial-time. -/
theorem wF_polyT : PolyT (wF g k) := by unfold wF; fun_prop

/-- The factor of two groups of clauses at a state word and a label word is polynomial-time. -/
theorem fF_polyT : PolyT (fF g k) := by unfold fF; fun_prop

/-- The number of label bits of two groups is given in unary: it is the length of the list of their
links. -/
theorem capF_unary : Unary fun p : Fml × ℕ × ℕ => capF g k p.1 p.2.1 p.2.2 :=
  Unary.of_length (w := fun p : Fml × ℕ × ℕ => links g k p.1 (min p.2.1 p.2.2) (max p.2.1 p.2.2)) (by fun_prop)

/-- A group has at most as many clauses as the formula, for every g (`mu_le` of
StepMachines/Prog/CountNet.lean needs 0 < g). -/
theorem mu_le_length (φ : Fml) : mu g φ ≤ φ.length := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp [mu]
  · exact mu_le hg φ

/-- The number of state bits of a group is given in unary. -/
theorem n_unary : Unary fun p : Fml × ℕ => mu g p.1 * k := by
  have h1 : Unary fun p : Fml × ℕ => p.1.length := Unary.of_length (by fun_prop)
  have h2 : Unary fun p : Fml × ℕ => mu g p.1 := h1.of_le (by fun_prop) fun p => mu_le_length g p.1
  exact h2.mul (Unary.const k)

end Groundwork.Prog.Count

namespace Groundwork.Prog

/-- The network `satP g k` of a k-CNF cut into g groups (Section 6, proof of Theorem A (c))
satisfies `Keeps`: its weights `W` and label
factors `f` are polynomial-time, and its lengths `n` and `cap` are unary. -/
theorem satP_keeps (g k : ℕ) : (satP g k).Keeps where
  n := Count.n_unary g k
  cap := Count.capF_unary g k
  W := ⟨IsPolyT.ofFun (Count.wF_polyT g k)⟩
  f := ⟨IsPolyT.ofFun (Count.fF_polyT g k)⟩

end Groundwork.Prog
