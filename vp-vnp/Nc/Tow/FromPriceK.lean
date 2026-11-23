/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.FromPrice

/-!
# Laws with tables in a subring
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Nc.Price

section Descent

variable {K : Type} [CommRing K]

/-- A law with tables in a subring. -/
noncomputable def restrictLaw (L : Law K) (A : Subring K)
    (hA : ∀ p i x g, L.tab p i x g ∈ A) : Law A where
  Ro := L.Ro
  Sl := L.Sl
  Cn := L.Cn
  I := L.I
  a := L.a
  b := L.b
  ab := L.ab
  c := L.c
  d := L.d
  cd := L.cd
  lam := L.lam
  lab := L.lab
  lab_inj := L.lab_inj
  len := L.len
  tab p i x g := ⟨L.tab p i x g, hA p i x g⟩
  law X := by
    apply Subtype.ext
    have h := L.law X
    have e : ((if ∀ e, X (L.a e) e = X (L.b e) e then (1 : A) else 0 : A) : K) =
        if ∀ e, X (L.a e) e = X (L.b e) e then 1 else 0 := by
      split_ifs <;> rfl
    rw [e, h]
    push_cast
    rfl
  conn := L.conn

/-- The entries of a law. -/
def entries (L : Law K) : Set K := {y | ∃ p i x g, L.tab p i x g = y}

theorem entries_finite (L : Law K) : (entries L).Finite := by
  classical
  have : entries L = Set.range fun s : (Σ (p : L.Ro) (i : L.I), ({e // L.a e = p ∨ L.b e = p} → Bool) ×
      ((ν : {ν // L.c ν = p ∨ L.d ν = p}) → Fin (L.len i ν) → Bool)) =>
      L.tab s.1 s.2.1 s.2.2.1 s.2.2.2 := by
    ext y
    constructor
    · rintro ⟨p, i, x, g, rfl⟩
      exact ⟨⟨p, i, x, g⟩, rfl⟩
    · rintro ⟨⟨p, i, x, g⟩, rfl⟩
      exact ⟨p, i, x, g, rfl⟩
  rw [this]
  exact Set.finite_range _

end Descent

end Nc.Tow
