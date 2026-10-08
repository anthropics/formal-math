/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tasks
public import ThreeSumApsp.Util.Asymptotics.SoftOSqrtPow
public import Mathlib.Data.Nat.Size

/-!
# Polynomially bounded needs

The need of a program is given by explicit expressions in the size n of the input and the bound U on
its numbers.  `PolyBounded F` says that F(n, U) is at most a polynomial in (n + 1)(U + 1).  It is
the calculus `ThreeSumApsp.Scale.SoftO` on the scale `polyScale`, and the tactic `growth_poly`
proves it by following the expression.

Three such functions make a polynomially bounded need (`PolyBounded.polyNeed`), and the need of a
solver that a host calls has three such parts (`PolyNeed.word`, `PolyNeed.cells`, `PolyNeed.depth`).
So the need of a host is polynomially bounded if the need of its solver is; the tactic `poly_need`
proves this from the definition of the need of the host.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Upper bounds that are polynomial in (n + 1)(U + 1) -/

/-- The scale of the polynomial bounds in a size `n` and a bound `U`: powers of `(n + 1)(U + 1)` are
not counted, and there is no other quantity. -/
noncomputable def polyScale : Scale (ℕ × ℕ) (Fin 0) where
  dom _ := True
  hidden p := ((p.1 + 1) * (p.2 + 1) : ℕ)
  base i := i.elim0
  one_le_hidden p _ := Nat.one_le_cast.2 (Nat.mul_pos p.1.succ_pos p.2.succ_pos)
  one_le_base i := i.elim0

/-- `F(n, U) ≤ K ((n + 1)(U + 1))^e` for some `K` and `e`. -/
abbrev PolyBounded (F : ℕ → ℕ → ℕ) : Prop := polyScale.SoftO (fun p => F p.1 p.2) ![]

namespace PolyBounded

variable {F : ℕ → ℕ → ℕ}

/-- The size `n` is polynomially bounded. -/
theorem fst : PolyBounded (fun n _ => n) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ p.2.succ_pos)).mono (by decide)

/-- The bound `U` is polynomially bounded. -/
theorem snd : PolyBounded (fun _ U => U) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ p.1.succ_pos)).mono (by decide)

/-- A smaller function has the same bound. -/
theorem of_le {G : ℕ → ℕ → ℕ} (h : PolyBounded G) (hle : ∀ n U, F n U ≤ G n U) : PolyBounded F :=
  Scale.SoftO.of_le h fun _ _ => hle _ _

/-- The bound with natural numbers. -/
theorem exists_nat_le (h : PolyBounded F) :
    ∃ K e : ℕ, ∀ n U, F n U ≤ K * ((n + 1) * (U + 1)) ^ e := by
  obtain ⟨C, e, hC, hle⟩ := h.exists_le
  refine ⟨⌈C⌉₊, e, fun n U => ?_⟩
  have hceil : (F n U : ℝ) ≤ ⌈C⌉₊ * (((n + 1) * (U + 1) : ℕ) : ℝ) ^ e := by
    simpa [polyScale, Scale.mon] using (hle (n, U) trivial).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by simp [polyScale, Scale.mon]; positivity))
  exact_mod_cast hceil

end PolyBounded

/-- Proves `PolyBounded F` as `growth` does.  The given facts bound the quantities that occur, other
than `n` and `U`.  A logarithm or a square root is bounded by its argument. -/
macro "growth_poly" "[" hs:term,* "]" : tactic =>
  `(tactic| growth [PolyBounded.fst, PolyBounded.snd, Scale.SoftO.log, Scale.SoftO.sqrt, $hs,*])

namespace PolyBounded

/-- A polynomial bound at polynomially bounded parameters. -/
theorem polyBound {A B : ℕ → ℕ → ℕ} (hA : PolyBounded A) (hB : PolyBounded B) (s k : ℕ) :
    PolyBounded (fun n U => polyBound s k [A n U, B n U]) :=
  of_le (G := fun n U => 2 ^ s * ((A n U + 1) * (B n U + 1)) ^ k) (by growth_poly [hA, hB])
    fun n U => by simp [Light.polyBound]

/-- Three polynomially bounded functions make a polynomially bounded need. -/
theorem polyNeed {need : ℕ → ℕ → Need} (hw : PolyBounded fun n U => (need n U).word)
    (hc : PolyBounded fun n U => (need n U).cells) (hd : PolyBounded fun n U => (need n U).depth) :
    PolyNeed need := by
  obtain ⟨K, e, hK⟩ := exists_nat_le (F := fun n U => (need n U).word + (need n U).cells +
    (need n U).depth) (by growth_poly [hw, hc, hd])
  refine ⟨Nat.size K, e, fun n U => ?_⟩
  have hsum := hK n U
  have hpoly : K * ((n + 1) * (U + 1)) ^ e ≤ Light.polyBound (Nat.size K) e [n, U] := by
    simp only [Light.polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact Nat.mul_le_mul_right _ (Nat.lt_size_self K).le
  exact ⟨by omega, by omega, by omega⟩

end PolyBounded

/-! ## The need of a solver that a host calls

A polynomially bounded need, at a size `A(n, U)` and a bound `B(n, U)` that are polynomially
bounded, has polynomially bounded parts. -/

namespace PolyNeed

variable {need : ℕ → ℕ → Need} {A B : ℕ × ℕ → ℕ} {a b : Fin 0 → ℕ}

private theorem part (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    ∃ R : ℕ → ℕ → ℕ, PolyBounded R ∧ ∀ n U, (need (A (n, U)) (B (n, U))).word ≤ R n U ∧
      (need (A (n, U)) (B (n, U))).cells ≤ R n U ∧ (need (A (n, U)) (B (n, U))).depth ≤ R n U :=
  let ⟨s, k, hle⟩ := h
  ⟨_, PolyBounded.polyBound (A := fun n U => A (n, U)) (B := fun n U => B (n, U))
    (hA.mono isEmptyElim) (hB.mono isEmptyElim) s k, fun _ _ => hle _ _⟩

/-- The numbers of the solver. -/
theorem word (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).word) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).1

/-- The cells of the solver. -/
theorem cells (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).cells) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).2.1

/-- The depth of the calls of the solver. -/
theorem depth (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).depth) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).2.2

end PolyNeed

/-- Proves `PolyNeed need`, where `need` is a record of three explicit expressions: takes the three
parts out of the record and treats each as `growth_poly` does.  The given facts bound the quantities
that occur, other than `n` and `U`; for a solver whose need `r` occurs, with `hr : PolyNeed r`, they
are `hr.word`, `hr.cells` and `hr.depth`. -/
macro "poly_need" "[" hs:term,* "]" : tactic =>
  `(tactic| (refine PolyBounded.polyNeed ?_ ?_ ?_ <;> dsimp only <;> growth_poly [$hs,*]))

end Light
