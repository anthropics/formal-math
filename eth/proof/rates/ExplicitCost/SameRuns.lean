/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ExplicitCost.EntryDefs
public import ExplicitCost.Mirror
import Mathlib.Tactic

/-! # The machine that reads K and g runs as `Printed.tableQ K g`

`entrySameRuns : EntrySameRuns`. The input of `Printed.tableQ K g asked` is widened by K and g in
unary (`widen`). Along this map every plain function of `entryData` agrees with that of `tableQ K g`
(after K and g have been read off as lengths, by definition), so the lemmas of Mirror.lean, one for
each construction, give a map of states.
The growth of the states is counted by these lemmas, from the state types: one copy of (K, g) in a
pending query, one more beside the test before a factor, one more in the point of the loop over the
factors, one more in the point of the loop over the terms: four. -/

@[expose] public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

variable (K g : ℕ)

/-- K and g, in unary, put beside the input of Definition 2(iii). -/
def widenC (c : NetInput) : DataInput := ((unary K, unary g), c)

/-- The same for the input of the machine for an entry. -/
def widen (u : X0 NetInput) : X0 DataInput := ((widenC K g u.1.1, u.1.2), u.2)

/-- The size of a number in unary. -/
private theorem size_unary (n : ℕ) : size (unary n) = 2 * n + 1 := by
  rw [unary, size_list, List.map_replicate, List.sum_replicate, size_unit, smul_eq_mul]
  omega

/-- One copy of K and g in unary. -/
theorem size_widenC (c : NetInput) : size (widenC K g c) = size c + (2 * K + 2 * g + 2) := by
  change size (unary K) + size (unary g) + size c = _
  rw [size_unary, size_unary]
  omega

/-- The widened input of the machine is larger by one copy of K and g in unary. -/
theorem size_widen (u : X0 NetInput) : size (widen K g u) = size u + (2 * K + 2 * g + 2) := by
  change size (widenC K g u.1.1) + size u.1.2 + size u.2 = size u.1.1 + size u.1.2 + size u.2 + _
  rw [size_widenC]
  omega

/-- A pair grows as its first component does. -/
theorem size_map_fst {α α' β : Type} [HasSize α] [HasSize α'] [HasSize β] {w : α → α'} {d : ℕ} (hw : ∀ a, size (w a) ≤ size a + d) (p : α × β) : size (Prod.map w id p) ≤ size p + d := by
  change size (w p.1) + size p.2 ≤ size p.1 + size p.2 + d
  have := hw p.1
  omega

/-- The K that the machine reads off the widened input. -/
theorem kOf_widen (u : X0 NetInput) : kOf (widen K g u) = K := List.length_replicate

/-- The g that the machine reads off the widened input. -/
theorem gOf_widen (u : X0 NetInput) : gOf (widen K g u) = g := List.length_replicate

/-! ## The four procedures: one query each -/

/-- «Is z ∈ S_a?»: one query, the same with K and g beside the input. -/
theorem mirrors_mem : Mirrors asked.mem askedData.mem (Prod.map (widenC K g) id) (2 * K + 2 * g + 2) :=
  (mirrors_query (fun _ => rfl) (size_map_fst fun c => (size_widenC K g c).le)).mapOut _

/-- W_a(z): one query, the same with K and g beside the input. -/
theorem mirrors_W : Mirrors asked.W askedData.W (Prod.map (widenC K g) id) (2 * K + 2 * g + 2) :=
  mirrors_query (fun _ => rfl) (size_map_fst fun c => (size_widenC K g c).le)

/-- Ψ_{a,b}(z, z'): one query, the same with K and g beside the input. -/
theorem mirrors_Ψ : Mirrors asked.Ψ askedData.Ψ (Prod.map (widenC K g) id) (2 * K + 2 * g + 2) :=
  mirrors_query (fun _ => rfl) (size_map_fst fun c => (size_widenC K g c).le)

/-- f_{a,b}(z, θ): one query, the same with K and g beside the input. -/
theorem mirrors_f : Mirrors asked.f askedData.f (Prod.map (widenC K g) id) (2 * K + 2 * g + 2) :=
  mirrors_query (fun _ => rfl) (size_map_fst fun c => (size_widenC K g c).le)

/-! ## The plain functions agree -/

/-- The input of a term, widened. -/
abbrev widen₁ : X0 NetInput × ℕ → X0 DataInput × ℕ := Prod.map (widen K g) id

/-- The input of a factor, widened. -/
abbrev widen₂ : (X0 NetInput × ℕ) × ℕ → (X0 DataInput × ℕ) × ℕ := Prod.map (widen₁ K g) id

/-- The widened input of a term is larger by at most one copy of K and g in unary. -/
theorem size_widen₁ (u : X0 NetInput × ℕ) : size (widen₁ K g u) ≤ size u + (2 * K + 2 * g + 2) := size_map_fst (fun c => (size_widen K g c).le) u

/-- The widened input of a factor is larger by at most one copy of K and g in unary. -/
theorem size_widen₂ (u : (X0 NetInput × ℕ) × ℕ) : size (widen₂ K g u) ≤ size u + (2 * K + 2 * g + 2) := size_map_fst (size_widen₁ K g) u

/-- The query (a, z_a) is the same on the widened input. -/
theorem qW_widen (u : (X0 NetInput × ℕ) × ℕ) :
    qW (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) askedData.under.toPaperNetwork (widen₂ K g u) = Prod.map (widenC K g) id (qW K g asked.under.toPaperNetwork u) := by
  change qW (kOf (widen K g u.1.1)) (gOf (widen K g u.1.1)) _ _ = _
  rw [kOf_widen, gOf_widen]
  rfl

/-- The query ((a, b), (z_a, θ_{a,b})) is the same on the widened input. -/
theorem qF_widen (u : (X0 NetInput × ℕ) × ℕ) :
    qF (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) askedData.under.toPaperNetwork (widen₂ K g u) = Prod.map (widenC K g) id (qF K g asked.under.toPaperNetwork u) := by
  change qF (kOf (widen K g u.1.1)) (gOf (widen K g u.1.1)) _ _ = _
  rw [kOf_widen, gOf_widen]
  rfl

/-- The query (b, z_b) is the same on the widened input. -/
theorem qMb_widen (u : (X0 NetInput × ℕ) × ℕ) :
    qMb (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) askedData.under (widen₂ K g u) = Prod.map (widenC K g) id (qMb K g asked.under u) := by
  change qMb (kOf (widen K g u.1.1)) (gOf (widen K g u.1.1)) _ _ = _
  rw [kOf_widen, gOf_widen]
  rfl

/-- The query ((a, b), (z_a, z_b)) is the same on the widened input. -/
theorem qPsi_widen (u : (X0 NetInput × ℕ) × ℕ) :
    qPsi (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) askedData.under (widen₂ K g u) = Prod.map (widenC K g) id (qPsi K g asked.under u) := by
  change qPsi (kOf (widen K g u.1.1)) (gOf (widen K g u.1.1)) _ _ = _
  rw [kOf_widen, gOf_widen]
  rfl

/-- The test «this factor is 1» is the same on the widened input. -/
theorem isOne_widen (u : (X0 NetInput × ℕ) × ℕ) : isOne (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) (widen₂ K g u) = isOne K g u := by
  change isOne (kOf (widen K g u.1.1)) (gOf (widen K g u.1.1)) _ = _
  rw [kOf_widen, gOf_widen]
  rfl

/-- The test «this factor is a value of W_a» is the same on the widened input. -/
theorem isW_widen (u : (X0 NetInput × ℕ) × ℕ) : isW (gOf (widen₂ K g u).1.1) (widen₂ K g u) = isW g u := by
  change isW (gOf (widen K g u.1.1)) _ = _
  rw [gOf_widen]
  rfl

/-- The test «this factor is a value of Ψ_{a,b}» is the same on the widened input. -/
theorem isPsi_widen (u : (X0 NetInput × ℕ) × ℕ) : isPsi (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) (widen₂ K g u) = isPsi K g u := by
  change isPsi (kOf (widen K g u.1.1)) (gOf (widen K g u.1.1)) _ = _
  rw [kOf_widen, gOf_widen]
  rfl

/-- The number of factors of a term is the same on the widened input. -/
theorem nPairs_widen (v : X0 NetInput × ℕ) : nPairs (gOf (widen₁ K g v).1) (widen₁ K g v) = nPairs g v := by
  change nPairs (gOf (widen K g v.1)) _ = _
  rw [gOf_widen]
  rfl

/-- The number of terms of an entry is the same on the widened input. -/
theorem nStates_widen (u : X0 NetInput) : nStates (kOf (widen K g u)) (gOf (widen K g u)) askedData.under.toPaperNetwork (widen K g u) = nStates K g asked.under.toPaperNetwork u := by
  rw [kOf_widen, gOf_widen]
  rfl

/-- The test «all appended bits are 0» is the same on the widened input. -/
theorem validB_widen (u : X0 NetInput) : validB (kOf (widen K g u)) (gOf (widen K g u)) askedData.under.toPaperNetwork (widen K g u) = validB K g asked.under.toPaperNetwork u := by
  rw [kOf_widen, gOf_widen]
  rfl

/-! ## The machines -/

/-- [z_a ∈ S_a]·W_a(z_a): the pending query and the copy beside the test. -/
theorem mirrors_wData : Mirrors (wQ K g asked) wData (widen₂ K g) (2 * (2 * K + 2 * g + 2)) :=
  Mirrors.gated ((mirrors_mem K g).mapIn (qW_widen K g)) ((mirrors_W K g).mapIn (qW_widen K g)) (size_widen₂ K g) (by omega) (by omega)

/-- [z_a ∈ S_a][z_b ∈ S_b]·Ψ_{a,b}(z_a, z_b). When the second test begins the copy beside the first
is gone. -/
theorem mirrors_psiData : Mirrors (psiQ K g asked) psiData (widen₂ K g) (2 * (2 * K + 2 * g + 2)) :=
  Mirrors.gated ((mirrors_mem K g).mapIn (qW_widen K g))
    (Mirrors.gated (d := 2 * (2 * K + 2 * g + 2)) ((mirrors_mem K g).mapIn (qMb_widen K g)) ((mirrors_Ψ K g).mapIn (qPsi_widen K g)) (size_widen₂ K g) (by omega) (by omega))
    (size_widen₂ K g) (by omega) le_rfl

/-- [z_a ∈ S_a]·f_{a,b}(z_a, θ_{a,b}). -/
theorem mirrors_fData : Mirrors (fQ K g asked) fData (widen₂ K g) (2 * (2 * K + 2 * g + 2)) :=
  Mirrors.gated ((mirrors_mem K g).mapIn (qW_widen K g)) ((mirrors_f K g).mapIn (qF_widen K g)) (size_widen₂ K g) (by omega) (by omega)

/-- One factor. -/
theorem mirrors_termData : Mirrors (termQ K g asked) termData (widen₂ K g) (2 * (2 * K + 2 * g + 2)) :=
  Mirrors.ite ((mirrors_const 1 (size_widen₂ K g)).mono (by omega))
    (Mirrors.ite (mirrors_wData K g) (Mirrors.ite (mirrors_psiData K g) (mirrors_fData K g) (isPsi_widen K g)) (isW_widen K g)) (isOne_widen K g)

/-- **One entry**: four copies of K and g. -/
theorem mirrors_entryData : Mirrors (tableQ K g asked) entryData (widen K g) (4 * (2 * K + 2 * g + 2)) :=
  Mirrors.ite
    (Mirrors.sumRange (d₁ := 3 * (2 * K + 2 * g + 2))
      (Mirrors.prodRange (mirrors_termData K g) (nPairs_widen K g) (size_widen₁ K g) (by omega))
      (nStates_widen K g) (fun u => (size_widen K g u).le) (by omega))
    ((mirrors_const 0 fun u => (size_widen K g u).le).mono (by omega)) (validB_widen K g)

/-- **For each K and g the machine runs as `Printed.tableQ K g` does.** -/
theorem entrySameRuns : EntrySameRuns := fun K g _ _ _ _ _ _ _ _ h => (mirrors_entryData K g).runs h

end ExplicitCost
