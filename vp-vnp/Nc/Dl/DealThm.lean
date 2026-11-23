/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Total
import NS1.Parts
import NS1.Compose
import Nc.G.Exact

/-!
# The dealing program
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

section Program

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- The dealing program: the brackets of the argument, cut into parts; steps; steps; templates. -/
def dealF (t0 t1 : Tree) (names : List (List Bool)) (nl nub : List Bool) (sts sts' : List DStep) (ts : List Tm) : Fm :=
  lett (dstepsF nub sts (partsF names nl (wordF t0 t1 .id))) (lett (dstepsF nub sts' .id) (tmsF ts .id))

theorem dealF_does (t0 t1 : Tree) (names : List (List Bool)) (nl nub : List Bool) (sts sts' : List DStep) (ts : List Tm)
    (z : Tree) {Ln : ℕ} (hn : ∀ p ∈ names, p.length ≤ Ln)
    {I : List DStep → (List Bool → Tree) → Prop} {c : DStep → ℕ} {ct c9 : ℕ}
    (hI : ∀ st sts' σ, I (st :: sts') σ → st.cost (KT.val nub) nub.length σ ≤ c st ∧
      ∀ σ' ∈ st.exec (KT.val nub) σ, I sts' σ')
    (hI0 : I sts (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z))))
    (h9 : ∀ σ ∈ execAll (KT.val nub) sts (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z))),
      (∃ I' : List DStep → (List Bool → Tree) → Prop, ∃ c' : DStep → ℕ,
        (∀ st sts'' σ, I' (st :: sts'') σ → st.cost (KT.val nub) nub.length σ ≤ c' st ∧
          ∀ σ' ∈ st.exec (KT.val nub) σ, I' sts'' σ') ∧ I' sts' σ ∧ (sts'.map fun st => c' st + 30).sum ≤ c9) ∧
      ∀ σ' ∈ execAll (KT.val nub) sts' σ, ∀ t ∈ ts, t.cost σ' ≤ ct) : ∃ Q : List (A × Tree),
    Does θ (dealF t0 t1 names nl nub sts sts' ts) z Q (60 * z.size + (z.size + names.length) * (60 * nl.length + 100) +
      names.length * (60 * Ln + 130) + (sts.map fun st => c st + 30).sum + c9 + ts.length * (ct + 60) + 300) ∧
    (∀ q ∈ Q, ∃ σ ∈ execAll (KT.val nub) (sts ++ sts') (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z))),
      q.2 = listT (ts.map fun t => t.expand σ)) ∧
    wsum Q (pvs θ) = ((execAll (KT.val nub) (sts ++ sts') (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z)))).map
      fun σ => (ts.map fun t => pv θ (t.expand σ)).prod).sum := by
  obtain ⟨σ0, hσ0⟩ : ∃ σ, σ = gets (partsT (KT.val nl) names .nil (wordT t0 t1 z)) := ⟨_, rfl⟩
  rw [← hσ0] at hI0 h9 ⊢
  have hw := partsF_gives (wordF_gives (t0 := t0) (t1 := t1) (Gives.id (θ := θ) z)) names nl Ln hn
  rw [length_wordT] at hw
  obtain ⟨Q1, d1, m1, s1⟩ := dstepsF_does (θ := θ) nub sts hw hI (by rw [← hσ0]; exact hI0)
  rw [← hσ0] at m1 s1
  -- the second part
  have h2 : ∀ W : Tree, ∃ Q : List (A × Tree), gets W ∈ execAll (KT.val nub) sts σ0 →
      Does θ (lett (dstepsF nub sts' .id) (tmsF ts .id)) W Q (c9 + ts.length * (ct + 60) + 150) ∧
      (∀ q ∈ Q, ∃ σ ∈ execAll (KT.val nub) sts' (gets W), q.2 = listT (ts.map fun t => t.expand σ)) ∧
      wsum Q (pvs θ) = ((execAll (KT.val nub) sts' (gets W)).map fun σ => (ts.map fun t => pv θ (t.expand σ)).prod).sum := by
    intro W
    by_cases hW : gets W ∈ execAll (KT.val nub) sts σ0
    swap
    · exact ⟨[], fun h => absurd h hW⟩
    obtain ⟨⟨I', c', hI', hI0', hc'⟩, ht⟩ := h9 _ hW
    obtain ⟨Q2, d2, m2, s2⟩ := dstepsF_does (θ := θ) nub sts' (Gives.id (θ := θ) W) hI' hI0'
    have d3 := Gives.after (G := tmsF ts .id) (f := fun W' => listT (ts.map fun t => t.expand (gets W'))) d2
      (d := 1 + ts.length * (ct + 60) + 30) fun q hq => tmsF_gives (Gives.id (θ := θ) q.2) fun t htt => ht _ (m2 q hq) t htt
    refine ⟨_, fun _ => ⟨d3.mono (by omega), ?_, ?_⟩⟩
    · intro q hq
      rw [List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      exact ⟨_, m2 q' hq', rfl⟩
    · rw [← s2]
      simp only [wsum, List.map_map, Function.comp_def, pvs, toList_listT]
  choose R hR using h2
  have d4 := d1.lett (G := lett (dstepsF nub sts' .id) (tmsF ts .id)) (R := R) (d := c9 + ts.length * (ct + 60) + 150)
    fun q hq => (hR q.2 (m1 q hq)).1
  refine ⟨_, d4.mono ?_, ?_, ?_⟩
  · omega
  · intro p hp
    obtain ⟨q, hq, r, hr, e, -⟩ := mem_bindW hp
    obtain ⟨σ, hσ, h⟩ := (hR q.2 (m1 q hq)).2.1 r hr
    refine ⟨σ, ?_, by rw [e, h]⟩
    rw [execAll_append, List.mem_flatMap]
    exact ⟨_, m1 q hq, hσ⟩
  · rw [wsum_bindW, wsum_congr (φ' := fun W => ((execAll (KT.val nub) sts' (gets W)).map
      fun σ => (ts.map fun t => pv θ (t.expand σ)).prod).sum) fun q hq => (hR q.2 (m1 q hq)).2.2, execAll_append,
      sum_flatMap_map]
    exact s1 fun σ => ((execAll (KT.val nub) sts' σ).map fun σ' => (ts.map fun t => pv θ (t.expand σ')).prod).sum

end Program

section Parts

variable {ν : Type} [DecidableEq ν] {nm : ν → List Bool} (hnm : Function.Injective nm)

include hnm

/-- The trie with the parts, as values by name. -/
theorem gets_partsT (m : ℕ) (xs : List ν) (hxs : xs.Nodup) (W : Tree) (l : List Tree) (st : ν → Tree)
    (hW : gets W = byPath nm st) : ∃ st' : ν → Tree, gets (partsT m (xs.map nm) W l) = byPath nm st' ∧
      (∀ k (h : k < xs.length), st' xs[k] = listT ((l.drop (k * m)).take m).reverse) ∧ ∀ y, y ∉ xs → st' y = st y := by
  induction xs generalizing W l st with
  | nil => exact ⟨st, hW, fun k h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | cons x xs ih =>
    rw [List.nodup_cons] at hxs
    rw [List.map_cons, partsT]
    obtain ⟨st', h1, h2, h3⟩ := ih hxs.2 (tset (nm x) (listT (l.take m).reverse) W) (l.drop m)
      (Function.update st x (listT (l.take m).reverse)) (by rw [gets_tset, hW, update_byPath hnm])
    refine ⟨st', h1, fun k h => ?_, fun y hy => ?_⟩
    · cases k with
      | zero =>
        rw [List.getElem_cons_zero, h3 x hxs.1, Function.update_self]
        simp
      | succ k =>
        rw [List.getElem_cons_succ, h2 k (by simpa using h), List.drop_drop]
        congr 4
        ring
    · rw [List.mem_cons, not_or] at hy
      rw [h3 y hy.2, Function.update_of_ne hy.1]

end Parts

end Nc.Dl
