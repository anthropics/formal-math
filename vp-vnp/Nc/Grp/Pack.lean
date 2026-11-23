/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.BaseProg

/-!
# The program of a base party: cutting and writing
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {S : Type} [Fintype S] [DecidableEq S]

variable (A) in
/-- What a base party does with its letters. -/
noncomputable def packSem (sep : List Bool) (ub : ℕ) (B : Body) (o : Outs S) (t : Tree) : List (A × Tree) :=
  bindL (segsL A sep (itemsR B.flags o) (List.replicate B.kR.length [true])) fun sR =>
    bindL (encT (A := A) (putsL ub B.kR sR.reverse t)) fun t1 =>
      bindL (segsL A sep (itemsC B.kR.length o) (List.replicate B.kR.length [true])) fun sC =>
        encT (putsL ub B.kC sC.reverse t1)

/-- Costs of writing. -/
def putCost (ub : ℕ) (kss : List (List (List Bool))) : ℕ :=
  (kss.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum

/-- The number of flags. -/
def flen (l : List (List ℕ)) : ℕ := (l.map List.length).sum

theorem length_getD_le (l : List (List ℕ)) (i : ℕ) : (l.getD i []).length ≤ flen l := by
  rcases lt_or_ge i l.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨_, List.getElem_mem h, rfl⟩)
  · rw [List.getD_eq_default _ _ h]
    exact Nat.zero_le _

theorem length_segsL {sep : List Bool} {items : List Item} {accs : List (List Bool)} {N : ℕ}
    (h : ∀ it ∈ items, it.1.length ≤ N) (ha : accs.length ≤ N) : ∀ r ∈ segsL A sep items accs, r.2.length ≤ N := by
  refine mem_foldL_induct (f := segOne A sep) (xs := items) (Inv := fun _ s => s.length ≤ N) (m := 0)
    (fun it hit s m _ q hq => ?_) ha
  obtain ⟨out, hout, rfl⟩ := List.mem_map.1 hq
  have := length_segRow out hout
  have := h it hit
  simp only [List.length_reverse]
  omega

theorem row_gives (v : Tree) {k : Fm} {x : Tree} {ck : ℕ} {kss : List (List (List Bool))}
    (hk : Gives θ k x (keysT kss) ck) :
    Gives θ (mapF (.quote v) (.quote .nil) k) x (listT (List.replicate kss.length v)) (ck + kss.length * 41 + 21) := by
  have hk' : Gives θ k x (listT (kss.map fun ks => listT (ks.map ofBits))) ck := hk
  have := mapF_gives (θ := θ) (x := x) (step := .quote v) (ef := .quote .nil) (e := .nil) (l := k)
    (xs := kss.map fun ks => listT (ks.map ofBits)) (g := fun _ => v) (d := fun _ => 1) (Gives.quote _ _) hk'
    (fun _ _ => Gives.quote _ _)
  rw [List.map_map] at this
  simp only [Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at this
  exact this.mono (by omega)

theorem rev_encA {k : Fm} {x : Tree} {ck : ℕ} {l : List (List Bool)} (hk : Gives θ k x (encA l) ck) :
    Gives θ (foldF .id (.quote .nil) k) x (listT (l.reverse.map ofBits)) (ck + l.length * 31 + 21) := by
  have := rev_gives (θ := θ) (x := x) (ys := []) (xs := l.map ofBits) (s := .quote .nil) (l := k) (Gives.quote _ _) hk
  rw [List.append_nil, ← List.map_reverse, List.length_map] at this
  exact this.mono (by omega)

theorem sum_items_le {items : List Item} {n c N : ℕ} (hn : items.length = n)
    (h : ∀ it ∈ items, it.1.length + it.2.length + 1 ≤ N) :
    (items.map fun it => (62 * c + 700) * (it.1.length + it.2.length + 1) + 30).sum ≤ n * ((62 * c + 730) * N) := by
  rw [← hn]
  have h1 : ∀ y ∈ items.map (fun it => (62 * c + 700) * (it.1.length + it.2.length + 1) + 30), y ≤ (62 * c + 730) * N := by
    intro y hy
    obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hy
    have := h it hit
    have h2 : (62 * c + 700) * (it.1.length + it.2.length + 1) ≤ (62 * c + 700) * N := Nat.mul_le_mul_left _ this
    have h3 : 1 ≤ N := by omega
    nlinarith
  have := List.sum_le_card_nsmul _ _ h1
  simpa using this

/-- **Cutting and writing.** -/
theorem ex_pack (sep : List Bool) (c : ℕ) (hsep : sep.length ≤ c) : ∃ F κ, ∀ (ub : ℕ) (B : Body) (o : Outs S) (t : Tree)
    (O : ℕ), (∀ j, (o j).length ≤ O) → (∀ j, ∀ a ∈ o j, a.length ≤ c) →
    Does θ F (.cons (encO o) (.cons (num ub) (.cons t B.tree))) (packSem A sep ub B o t)
      (κ * (O + flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1)) := by
  obtain ⟨GR, κR, hGR⟩ := itemsR_gives (θ := θ) (S := S)
  obtain ⟨GC, κC, hGC⟩ := itemsC_gives (θ := θ) (S := S)
  refine ⟨lett (.cons .id (lett (.cons .id (lett (.cons (GR (.hd (.tl (.tl (.tl .id)))) (.hd .id))
      (mapF (.quote (ofBits [true])) (.quote .nil) (.hd (.tl (.tl (.tl (.tl .id))))))) (segsF sep)))
      (lett (.cons (.hd (.tl (.hd .id))) (.cons (.hd (.tl (.tl (.tl (.tl (.hd .id))))))
        (.cons (foldF .id (.quote .nil) (.tl .id)) (.hd (.tl (.tl (.hd .id))))))) putsF)))
    (lett (.cons .id (lett (.hd .id) (lett (.cons (GC (mapF (.quote (num 2)) (.quote .nil) (.hd (.tl (.tl (.tl (.tl .id))))))
        (.hd .id)) (mapF (.quote (ofBits [true])) (.quote .nil) (.hd (.tl (.tl (.tl (.tl .id))))))) (segsF sep))))
      (lett (.cons (.hd (.tl (.hd (.hd .id)))) (.cons (.tl (.tl (.tl (.tl (.tl (.hd (.hd .id)))))))
        (.cons (foldF .id (.quote .nil) (.tl .id)) (.tl (.hd .id))))) putsF)),
    10 * κR + κC * 100 + 2 * (nT S * (62 * c + 730)) + 2000, fun ub B o t O hO hc => ?_⟩
  set x : Tree := .cons (encO o) (.cons (num ub) (.cons t B.tree)) with hx
  set m := B.kR.length with hm
  set N := O + flen B.flags + m + putCost ub B.kR + putCost ub B.kC + 1 with hN
  have gO : Gives θ (.hd .id) x (encO o) 2 := (Gives.id _).hd
  have gF : Gives θ (.hd (.tl (.tl (.tl .id)))) x (listT (B.flags.map fun l => listT (l.map num))) 5 :=
    (Gives.id _).tl.tl.tl.hd
  have gK : Gives θ (.hd (.tl (.tl (.tl (.tl .id))))) x (keysT B.kR) 6 := (Gives.id _).tl.tl.tl.tl.hd
  -- what is written
  have a1 : Gives θ (mapF (.quote (ofBits [true])) (.quote .nil) (.hd (.tl (.tl (.tl (.tl .id)))))) x
      (encA (List.replicate m [true])) (6 + m * 41 + 21) := by
    have := row_gives (ofBits [true]) gK
    rw [encA, List.map_replicate]
    exact this
  have a2 := Gives.cons (hGR _ _ x B.flags o 5 2 gF gO) a1
  have hcR : ∀ it ∈ itemsR B.flags o, ∀ a ∈ it.2, a.length ≤ c := by
    intro it hit a ha
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hit
    exact hc _ a ha
  have hlR : ∀ it ∈ itemsR B.flags o, it.1.length + it.2.length + 1 ≤ N ∧ it.1.length ≤ flen B.flags := by
    intro it hit
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hit
    have h1 := length_getD_le B.flags i.rev
    have h2 := hO (Fin.castAdd (nT S) i.rev)
    exact ⟨by simp only; omega, h1⟩
  have a3 := Does.of_gives a2 (segsF_does (θ := θ) sep c hsep _ _ hcR)
  have a4 := Does.letkT (G := lett (.cons (.hd (.tl (.hd .id))) (.cons (.hd (.tl (.tl (.tl (.tl (.hd .id))))))
      (.cons (foldF .id (.quote .nil) (.tl .id)) (.hd (.tl (.tl (.hd .id))))))) putsF)
    (f := fun sR => (encT (A := A) (putsL ub B.kR sR.reverse t)).map (Prod.map id id))
    (d := (flen B.flags + m) * 31 + putCost ub B.kR + 300) a3 (by
      intro b hb
      have h1 := length_segsL (N := flen B.flags + m) (fun it hit => (hlR it hit).2.trans (Nat.le_add_right _ _))
        (by rw [List.length_replicate]; exact Nat.le_add_left _ _) b hb
      have e1 := rev_encA (θ := θ) (x := .cons x (encA b.2)) (k := .tl .id) (l := b.2) (Gives.id _).tl
      have e2 := Gives.cons (Gives.id (θ := θ) (.cons x (encA b.2))).hd.tl.hd (Gives.cons
        (Gives.id _).hd.tl.tl.tl.tl.hd (Gives.cons e1 (Gives.id _).hd.tl.tl.hd))
      have e3 := Does.of_gives e2 (putsF_does (θ := θ) ub B.kR b.2.reverse t)
      refine (e3.replace ?_).mono ?_
      · simp
      · simp only [putCost]
        omega)
  rw [bindL_map] at a4
  -- what is read
  have gO' : ∀ t1, Gives θ (.hd .id) (.cons x t1) x 2 := fun t1 => (Gives.id _).hd
  have b1 : Gives θ (mapF (.quote (num 2)) (.quote .nil) (.hd (.tl (.tl (.tl (.tl .id)))))) x
      (listT ((List.replicate m 2).map num)) (6 + m * 41 + 21) := by
    have := row_gives (num 2) gK
    rw [List.map_replicate]
    exact this
  have b2 := Gives.cons (hGC _ _ x m o _ 2 b1 gO) a1
  have hcC : ∀ it ∈ itemsC m o, ∀ a ∈ it.2, a.length ≤ c := by
    intro it hit a ha
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hit
    exact hc _ a ha
  have hlC : ∀ it ∈ itemsC m o, it.1.length + it.2.length + 1 ≤ N ∧ it.1.length ≤ m := by
    intro it hit
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hit
    have h2 := hO (Fin.natAdd (nT S) i.rev)
    refine ⟨?_, ?_⟩
    · simp only [List.length_replicate]
      omega
    · simp
  have b3 := Does.of_gives b2 (segsF_does (θ := θ) sep c hsep _ _ hcC)
  have b4 := Does.letkT (G := _) (f := fun t1 => bindL (segsL A sep (itemsC m o) (List.replicate m [true])) fun sC =>
      encT (A := A) (putsL ub B.kC sC.reverse t1))
    (d := 2 + (κC * (6 + m * 41 + 21 + 2 + 1) + (6 + m * 41 + 21) + 1 +
        (((itemsC m o).map fun it => (62 * c + 700) * (it.1.length + it.2.length + 1) + 30).sum + 30) + 2) + 2 +
        (m * 31 + putCost ub B.kC + 300) + 4) a4 (by
      intro b hb
      have c1 := Does.of_gives (gO' b.2) b3
      have c2 := Does.letkT (G := lett (.cons (.hd (.tl (.hd (.hd .id)))) (.cons (.tl (.tl (.tl (.tl (.tl (.hd (.hd .id)))))))
          (.cons (foldF .id (.quote .nil) (.tl .id)) (.tl (.hd .id))))) putsF)
        (f := fun sC => encT (A := A) (putsL ub B.kC sC.reverse b.2)) (d := m * 31 + putCost ub B.kC + 300) c1 (by
          intro r hr
          have h1 := length_segsL (N := m) (fun it hit => (hlC it hit).2) (by rw [List.length_replicate]) r hr
          have e1 := rev_encA (θ := θ) (x := .cons (.cons x b.2) (encA r.2)) (k := .tl .id) (l := r.2) (Gives.id _).tl
          have e2 := Gives.cons (Gives.id (θ := θ) (.cons (.cons x b.2) (encA r.2))).hd.hd.tl.hd (Gives.cons
            (Gives.id _).hd.hd.tl.tl.tl.tl.tl (Gives.cons e1 (Gives.id _).hd.tl))
          have e3 := Does.of_gives e2 (putsF_does (θ := θ) ub B.kC r.2.reverse b.2)
          refine e3.mono ?_
          simp only [putCost]
          omega)
      exact c2)
  refine (b4.replace ?_).mono ?_
  · unfold packSem
    rw [bindL_assoc]
  · have h1 := sum_items_le (c := c) (N := N) (n := nT S) (by simp [itemsR]) (fun it hit => (hlR it hit).1)
    have h2 := sum_items_le (c := c) (N := N) (n := nT S) (by simp [itemsC]) (fun it hit => (hlC it hit).1)
    have h3 : m ≤ N := by omega
    have h4 : 1 ≤ N := by omega
    have h5 : κC * (6 + m * 41 + 21 + 2 + 1) ≤ κC * 71 * N := by
      calc κC * (6 + m * 41 + 21 + 2 + 1) ≤ κC * (71 * N) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring
    have h6 : κR * (5 + 2 + 1) ≤ κR * 8 * N := by nlinarith
    have h7 : nT S * ((62 * c + 730) * N) = nT S * (62 * c + 730) * N := by ring
    have h8 : (10 * κR + κC * 100 + 2 * (nT S * (62 * c + 730)) + 2000) * N =
      10 * (κR * N) + 100 * (κC * N) + 2 * (nT S * (62 * c + 730) * N) + 2000 * N := by ring
    have h9 : κC * 71 * N = 71 * (κC * N) := by ring
    have h10 : κR * 8 * N = 8 * (κR * N) := by ring
    rw [h8]
    rw [h7] at h1 h2
    rw [h9] at h5
    rw [h10] at h6
    omega

end Nc.Grp
