/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.PM
import NS1.Accel

/-!
# The rules of the universal machine
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset

/-- Kinds of records: nil, cons, garbage, frames. -/
inductive Kd where
  | N | C | G | HT | PE | PA | PB | HD | TL | CO1 | CO2 | IT | RU1 | RU2 | TH
  deriving DecidableEq

instance : Fintype Kd := ⟨{.N, .C, .G, .HT, .PE, .PA, .PB, .HD, .TL, .CO1, .CO2, .IT, .RU1, .RU2, .TH}, by
  intro x; cases x <;> simp⟩

/-- The prefixes of the names. -/
def pre (supp : Finset (List Bool)) : Finset (List Bool) := supp.biUnion fun q => q.inits.toFinset

theorem mem_pre {supp : Finset (List Bool)} {p : List Bool} : p ∈ pre supp ↔ ∃ q ∈ supp, p <+: q := by
  simp [pre]

/-- Prefixes of names. -/
abbrev Nm (supp : Finset (List Bool)) := {p : List Bool // p ∈ pre supp}

/-- Modes. -/
inductive Md (N : Type) where
  | S0 | S1 | S2 | P | PR | E | D (j : Fin 11) | K4 | K5 | K6 | R | H | T | I | I1 | I2 | TH (p : N) | TB (p : N) | Z
  deriving DecidableEq, Fintype

/-- Rules without names. -/
inductive Ra where
  | s0 | s1 | pr0 | pr1 | pa | pb | pe | s2 (b : Bool) | en | ec | dc (j : Fin 10) | d0 | d1 | d2 | d3 | d4 | d5 | d6
  | d7 (b : Bool) | d9 | k4 (b : Bool) | k5 (b : Bool) | k6 (b : Bool) | rhd | rtl | h (b : Bool) | t (b : Bool)
  | rco1 | rco2 | rit | ic | inn | i1 (b : Bool) | i2 (b : Bool) | rru1 | rru2 | rht
  deriving DecidableEq, Fintype

/-- Rules. -/
abbrev Ru (supp : Finset (List Bool)) := Ra ⊕ ({_u : Unit // [] ∈ pre supp} ⊕ (Nm supp ⊕ (Nm supp ⊕
  {x : Nm supp × Nm supp × Bool // x.2.1.1 = x.1.1 ++ [x.2.2]})))

/-- Cons or nil. -/
def kb (b : Bool) : Kd := if b then .C else .N

/-- The data of a rule. -/
structure RD (A N : Type) where
  src : Md N
  dst : Md N
  rd : Option Bool
  lk : Kd
  la : Fin 5
  ak : Kd
  af : Fin 3 → Fin 9
  dr : Fin 5 → Fin 9
  wt : A

variable {A : Type} [CommRing A] (θ : List Bool → A) (supp : Finset (List Bool))

/-- A rule without input and weight. -/
def rl {N : Type} (src dst : Md N) (lk : Kd) (la : Fin 5) (ak : Kd) (f0 f1 f2 : Fin 9) (d1 d2 d3 d4 : Fin 9) : RD A N :=
  ⟨src, dst, none, lk, la, ak, ![f0, f1, f2], ![0, d1, d2, d3, d4], 1⟩

/-- The rules without names. -/
def ruleA {N : Type} : Ra → RD A N
  | .s0 => rl .S0 .S1 .N 0 .HT 0 0 0 8 0 0 0
  | .s1 => rl .S1 .P .N 0 .PE 1 0 0 8 0 0 0
  | .pr0 => { (rl .P .PR .N 0 .G 0 0 0 0 1 0 0 : RD A N) with rd := some false }
  | .pr1 => { (rl .P .P .N 0 .PA 1 0 0 8 0 0 0 : RD A N) with rd := some true }
  | .pa => rl .PR .P .PA 2 .PB 1 5 0 8 0 0 0
  | .pb => rl .PR .PR .PB 2 .C 5 1 0 8 6 0 0
  | .pe => rl .PR .S2 .PE 2 .G 0 0 0 1 5 0 0
  | .s2 b => rl .S2 .E (kb b) 1 .G 0 0 0 5 6 2 0
  | .en => rl .E .R .N 1 .G 0 0 0 1 3 0 0
  | .ec => rl .E (.D 0) .C 1 .G 0 0 0 5 6 2 3
  | .dc j => rl (.D j.castSucc) (.D j.succ) .C 1 .G 0 0 0 6 2 3 4
  | .d0 => rl (.D 0) .R .N 1 .G 0 0 0 2 4 0 0
  | .d1 => rl (.D 1) .R .N 1 .G 0 0 0 3 4 0 0
  | .d2 => rl (.D 2) .E .N 1 .HD 4 0 0 2 3 8 0
  | .d3 => rl (.D 3) .E .N 1 .TL 4 0 0 2 3 8 0
  | .d4 => rl (.D 4) .K4 .N 1 .G 0 0 0 2 3 4 0
  | .d5 => rl (.D 5) .K5 .N 1 .G 0 0 0 2 3 4 0
  | .d6 => rl (.D 6) .K6 .N 1 .G 0 0 0 2 3 4 0
  | .d7 b => if b then rl (.D 7) .R .N 1 .C 0 0 0 8 4 0 0 else rl (.D 7) .R .N 1 .G 0 0 0 0 4 0 0
  | .d9 => rl (.D 9) .E .N 1 .TH 4 0 0 2 3 8 0
  | .k4 b => rl .K4 .E (kb b) 1 .CO1 6 2 3 5 2 8 0
  | .k5 b => rl .K5 .E (kb b) 1 .IT 6 2 3 5 2 8 0
  | .k6 b => rl .K6 .E (kb b) 1 .RU1 6 2 3 5 2 8 0
  | .rhd => rl .R .H .HD 2 .G 0 0 0 1 5 0 0
  | .rtl => rl .R .T .TL 2 .G 0 0 0 1 5 0 0
  | .h b => rl .H .R (kb b) 1 .G 0 0 0 5 2 0 0
  | .t b => rl .T .R (kb b) 1 .G 0 0 0 6 2 0 0
  | .rco1 => rl .R .E .CO1 2 .CO2 1 7 0 5 6 8 0
  | .rco2 => rl .R .R .CO2 2 .C 5 1 0 8 6 0 0
  | .rit => rl .R .I .IT 2 .G 0 0 0 1 5 6 7
  | .ic => rl .I .I1 .C 1 .G 0 0 0 2 3 4 0
  | .inn => rl .I .I2 .N 1 .G 0 0 0 2 3 4 0
  | .i1 b => rl .I1 .E (kb b) 1 .G 0 0 0 5 2 3 0
  | .i2 b => rl .I2 .E (kb b) 1 .G 0 0 0 6 2 3 0
  | .rru1 => rl .R .E .RU1 2 .RU2 1 7 0 5 6 8 0
  | .rru2 => rl .R .E .RU2 2 .G 0 0 0 5 1 6 0
  | .rht => rl .R .Z .HT 2 .G 0 0 0 0 0 0 0

/-- The rules. -/
def rule : Ru supp → RD A (Nm supp)
  | .inl r => ruleA r
  | .inr (.inl u) => rl .R (.TH ⟨[], u.2⟩) .TH 2 .G 0 0 0 1 5 0 0
  | .inr (.inr (.inl p)) => { (rl (.TH p) .R .N 1 .G 0 0 0 0 2 0 0 : RD A (Nm supp)) with wt := θ p.1 }
  | .inr (.inr (.inr (.inl p))) => rl (.TH p) (.TB p) .C 1 .G 0 0 0 5 6 2 0
  | .inr (.inr (.inr (.inr x))) => rl (.TB x.1.1) (.TH x.1.2.1) (kb x.1.2.2) 1 .G 0 0 0 2 3 0 0

/-- The universal machine. -/
noncomputable def UM : Mach A (Md (Nm supp)) Kd where
  Rl := Ru supp
  fR := Fintype.ofFinite _
  dR := Classical.decEq _
  src r := (rule θ supp r).src
  dst r := (rule θ supp r).dst
  rd r := (rule θ supp r).rd
  lk r := (rule θ supp r).lk
  la r := (rule θ supp r).la
  ak r := (rule θ supp r).ak
  af r := (rule θ supp r).af
  dr r := (rule θ supp r).dr
  wt r := (rule θ supp r).wt
  m0 := .S0
  mh := .Z
  kN := .N

/-- The register that is loaded depends on the mode only. -/
def laM {N : Type} : Md N → Fin 5
  | .S0 => 0
  | .S1 => 0
  | .P => 0
  | .PR => 2
  | .R => 2
  | _ => 1

theorem la_eq (r : Ru supp) : (rule θ supp r).la = laM (rule θ supp r).src := by
  rcases r with r | u | p | p | x
  · cases r <;> first | rfl | (rename_i b; cases b <;> rfl)
  all_goals rfl

end Nc.Uni
