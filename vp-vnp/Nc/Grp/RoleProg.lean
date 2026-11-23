/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Role

/-!
# The program of a role: the loop
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

variable (θ) in
open Classical in
/-- A formula for an element of the ring. -/
noncomputable def we (a : A) : WE := if h : ∃ e : WE, e.val θ = a then h.choose else .zero

theorem we_val {a : A} (h : ∃ e : WE, e.val θ = a) : (we θ a).val θ = a := by
  rw [we, dif_pos h]
  exact h.choose_spec

/-- Slots of a role, as a list. -/
noncomputable def slList (L : G.Law A) (p : L.Ro) : List (L.SlAt p) := (univ : Finset (L.SlAt p)).toList

/-- Channels of a role, as a list. -/
noncomputable def cnList (L : G.Law A) (p : L.Ro) : List (L.CnAt p) := (univ : Finset (L.CnAt p)).toList

/-- The number of a slot. -/
noncomputable def slIdx (L : G.Law A) (p : L.Ro) (e : L.SlAt p) : Fin (slList L p).length :=
  ⟨(slList L p).idxOf e, List.idxOf_lt_length_of_mem (Finset.mem_toList.2 (mem_univ e))⟩

variable (θ) in
/-- The transducer of a role. -/
noncomputable def roleTab (L : G.Law A) (p : L.Ro) (_ : Fin 1) (v : Fin (slList L p).length → Bool) :
    List (Opt 1 (cnList L p).length Bool) :=
  (univ : Finset (Bk L p)).toList.map fun z => ⟨we θ (L.tab p z.1 (fun e => v (slIdx L p e)) z.2), 0,
    fun j => (List.ofFn (L.lab z.1) ++ List.ofFn (z.2 ((cnList L p).get j))).reverse⟩

/-- The yardstick: argument (yardstick `num ub`, (trie, (num t, …))). -/
def yardF : Fm := .tl (foldF (.cons (.hd (.tl .id)) (appF (.hd (.tl .id)) (.tl (.tl .id)))) (.cons (.hd .id) (.quote .nil))
  (.hd (.tl (.tl .id))))

theorem foldl_yard (tt ub m : ℕ) : (List.replicate tt ()).foldl (fun (k : ℕ) _ => ub + k) m = tt * ub + m := by
  induction tt generalizing m with
  | zero => simp
  | succ tt ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    ring

theorem yardF_gives (ub tt : ℕ) (t y : Tree) :
    Gives θ yardF (.cons (num ub) (.cons t (.cons (num tt) y))) (num (tt * ub)) (tt * (ub * 62 + 100) + 60) := by
  have h0 : Gives θ (.cons (.hd .id) (.quote .nil)) (.cons (num ub) (.cons t (.cons (num tt) y)))
      (.cons (num ub) (num 0)) 4 := (Gives.cons (Gives.id _).hd (Gives.quote _ _)).mono (by omega)
  have hl : Gives θ (.hd (.tl (.tl .id))) (.cons (num ub) (.cons t (.cons (num tt) y)))
      (listT ((List.replicate tt ()).map fun _ => .nil)) 4 := by
    rw [List.map_replicate, ← num_eq_listT]
    exact (Gives.id _).tl.tl.hd
  have h1 := foldTG (θ := θ) (encE := fun _ : Unit => (.nil : Tree)) (enc := fun k : ℕ => .cons (num ub) (num k)) (s₀ := 0)
    (g := fun _ k => ub + k) (Inv := fun _ _ => True) (d := fun _ => ub * 62 + 60)
    (step := .cons (.hd (.tl .id)) (appF (.hd (.tl .id)) (.tl (.tl .id)))) h0 hl (fun _ _ k _ _ => ⟨by
      have e1 : Gives θ (.hd (.tl .id)) (.cons .nil (.cons (num ub) (num k))) (ofBits (List.replicate ub false)) 3 := by
        rw [← num_eq_ofBits]
        exact (Gives.id _).tl.hd
      have e2 : Gives θ (.tl (.tl .id)) (.cons .nil (.cons (num ub) (num k))) (ofBits (List.replicate k false)) 3 := by
        rw [← num_eq_ofBits]
        exact (Gives.id _).tl.tl
      have e3 := appB_gives e1 e2
      rw [← List.replicate_add, ← num_eq_ofBits, List.length_replicate] at e3
      exact (Gives.cons (Gives.id _).tl.hd e3).mono (by omega), trivial⟩) trivial
  have h2 : (List.replicate tt ()).foldl (fun (k : ℕ) _ => ub + k) 0 = tt * ub := by
    rw [foldl_yard, add_zero]
  rw [h2] at h1
  refine h1.tl.mono ?_
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
  ring_nf
  omega

variable (θ) in
/-- What a role does with a trie with the contents `ct`. -/
noncomputable def roleSem (L : G.Law A) (p : L.Ro) (ub : ℕ) (ct : List Bool → List Bool) (tt : ℕ)
    (slots keys : List (List (List Bool))) (t : Tree) : List (A × Tree) :=
  if ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ [] then
    bindL (runL θ (roleTab θ L p) (tt * ub)
      (0, fun i => ((slots.map fun es => es.reverse.flatMap ct).getD i []), fun _ => [])) fun s =>
      encT (putsL ub keys (List.ofFn fun j => (s.2.2 j).reverse ++ [true]) t)
  else []

/-- The last part: argument ((yardstick, (trie, (num t, (slots, keys)))), state of the transducer). -/
def roleEnd : Fm := lett (.cons (.hd (.hd .id)) (.cons (.tl (.tl (.tl (.tl (.hd .id)))))
  (.cons (mapF (foldF .id (.quote (ofBits [true])) (.tl .id)) (.quote .nil) (.tl (.tl (.tl .id))))
    (.hd (.tl (.hd .id)))))) putsF

theorem roleEnd_does (ub : ℕ) (t y sl ins : Tree) (c0 : Tree) (keys : List (List (List Bool))) (m : ℕ) (outs : List (List Bool))
    (hm : ∀ w ∈ outs, w.length ≤ m) :
    Does θ roleEnd (.cons (.cons (num ub) (.cons t (.cons y (.cons sl (keysT keys)))))
        (.cons c0 (.cons ins (listT (outs.map ofBits)))))
      (encT (putsL ub keys (outs.map fun w => w.reverse ++ [true]) t))
      (outs.length * (m * 31 + 100) + ((keys.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum + 200)) := by
  set x : Tree := .cons (.cons (num ub) (.cons t (.cons y (.cons sl (keysT keys)))))
    (.cons c0 (.cons ins (listT (outs.map ofBits)))) with hx
  have h1 := mapF_gives (θ := θ) (x := x) (step := foldF .id (.quote (ofBits [true])) (.tl .id)) (ef := .quote .nil)
    (l := .tl (.tl (.tl .id))) (e := .nil) (xs := outs.map ofBits) (g := fun y => ofBits (y.path.reverse ++ [true]))
    (d := fun _ => m * 31 + 30) (Gives.quote _ _) (Gives.id _).tl.tl.tl (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
      rw [path_ofBits]
      have := reverse_gives (θ := θ) (x := .cons (.nil : Tree) (ofBits w)) (l := .tl .id) (w := w) (Gives.id _).tl [true]
      have h2 := hm w hw
      exact this.mono (by omega))
  have h2 : ((outs.map ofBits).map fun y => ofBits (y.path.reverse ++ [true])) =
      (outs.map fun w => w.reverse ++ [true]).map ofBits := by
    simp [Function.comp_def]
  rw [h2] at h1
  have h3 := Gives.cons (Gives.id (θ := θ) x).hd.hd (Gives.cons (Gives.id _).hd.tl.tl.tl.tl (Gives.cons h1
    (Gives.id _).hd.tl.hd))
  have h4 := putsF_does (θ := θ) ub keys (outs.map fun w => w.reverse ++ [true]) t
  refine (Does.of_gives h3 h4).mono ?_
  simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul]
  ring_nf
  omega

/-- **The program of a role.** -/
theorem ex_role (L : G.Law A) (p : L.Ro) : ∃ F κ, ∀ (ub : ℕ) (ct : List Bool → List Bool) (tt : ℕ)
    (slots keys : List (List (List Bool))) (t : Tree),
    (∀ k, tget k t = ofBits (ct k)) → (∀ k, (ct k).length ≤ ub) → slots.length = (slList L p).length →
    Does θ F (.cons (num ub) (.cons t (.cons (num tt) (.cons (keysT slots)
        (keysT keys))))) (roleSem θ L p ub ct tt slots keys t)
      (κ * (tt * (ub + 1) + (slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum +
        (keys.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum + 1)) := by
  obtain ⟨F, κ, hF⟩ := ex_run (θ := θ) bit (roleTab θ L p)
  obtain ⟨κ', hκ'⟩ := exists_runL_length (θ := θ) (roleTab θ L p)
  set nO := (cnList L p).length with hnO
  refine ⟨lett (.cons .id (lett (.cons yardF (.cons (.quote (num 0)) (.cons
    (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl (.tl .id))))) streamsF)
    (.quote (listT (List.replicate nO .nil)))))) F)) roleEnd, κ + nO * (κ' * 31 + 100) + 1000,
    fun ub ct tt slots keys t hct hlen hslots => ?_⟩
  set x : Tree := .cons (num ub) (.cons t (.cons (num tt) (.cons (keysT slots)
        (keysT keys)))) with hx
  have h1 := yardF_gives (θ := θ) ub tt t (.cons (keysT slots) (keysT keys))
  have h2 : Gives θ (.cons (.hd (.tl .id)) (.hd (.tl (.tl (.tl .id))))) x (.cons t (keysT slots)) 15 :=
    (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.tl.hd).mono (by omega)
  have h3 := Does.of_gives h2 (streamsF_does (θ := θ) hct hlen slots)
  set bs := slots.map fun es => es.reverse.flatMap ct with hbs
  -- the state at the beginning
  let s₀ : TSt 1 (slList L p).length nO Bool := (0, fun i => bs.getD i [], fun _ => [])
  have hs₀ : encS bit s₀ = .cons (num 0) (.cons (listT (bs.map ofBits)) (listT (List.replicate nO .nil))) := by
    have e1 : (List.ofFn fun i : Fin (slList L p).length => ofBits (bs.getD i [])) = bs.map ofBits := by
      apply List.ext_getElem
      · simp [hbs, hslots]
      · intro k h1 h2
        simp only [List.length_map] at h2
        rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem _ _ h2]
    have e2 : (List.ofFn fun _ : Fin nO => listT (([] : List Bool).map bit)) = List.replicate nO .nil := by
      rw [List.ofFn_const]
      rfl
    simp only [encS, s₀, e1, e2]
    rfl
  have h4 := Does.cons h1 (Does.cons (Gives.quote (θ := θ) (num 0) x) (Does.cons h3
    (Gives.quote (listT (List.replicate nO .nil)) x)))
  have h5 : Does θ (.cons yardF (.cons (.quote (num 0)) (.cons
      (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl (.tl .id))))) streamsF)
      (.quote (listT (List.replicate nO .nil)))))) x
      ((if ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ [] then [((1 : A), ())] else []).map
        (Prod.map id fun _ => .cons (num (tt * ub)) (encS bit s₀)))
      (tt * (ub * 62 + 100) + ((slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum) + 200) := by
    refine (h4.replace ?_).mono (by omega)
    rw [hs₀]
    split_ifs <;> simp
  have h6 := Does.lettE (G := F) (f := fun _ => runL θ (roleTab θ L p) (tt * ub) s₀) (enc' := encS bit)
    (d := κ * (tt * ub + 1)) h5 (fun _ _ => hF (tt * ub) s₀)
  have h7 := Does.letkT (G := roleEnd) (f := fun s => encT (putsL ub keys (List.ofFn fun j => (s.2.2 j).reverse ++ [true]) t))
    (d := nO * (κ' * (tt * ub) * 31 + 100) + ((keys.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum
      + 200)) h6 (by
      intro b hb
      obtain ⟨a, ha, r, hr, hbr⟩ := mem_bindL hb
      have h8 := hκ' (tt * ub) s₀ (fun j => rfl) r hr
      rw [hbr]
      have e1 : (List.ofFn fun j => listT ((r.2.2.2 j).map bit)) = (List.ofFn r.2.2.2).map ofBits := by
        rw [List.map_ofFn]
        congr 1
        funext j
        exact listT_ofBits _
      have e2 : (List.ofFn fun j => (r.2.2.2 j).reverse ++ [true]) =
          (List.ofFn r.2.2.2).map fun w => w.reverse ++ [true] := by
        rw [List.map_ofFn]
        rfl
      rw [e2]
      unfold encS
      rw [e1]
      have h9 := roleEnd_does (θ := θ) ub t (num tt) (keysT slots)
        (listT (List.ofFn fun i => ofBits (r.2.2.1 i))) (num r.2.1) keys (κ' * (tt * ub)) (List.ofFn r.2.2.2) (by
          intro w hw
          obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hw
          exact h8 j)
      rw [List.length_ofFn] at h9
      exact h9)
  refine (h7.replace ?_).mono ?_
  · unfold roleSem
    split_ifs
    · rw [bindL_single]
    · rfl
  · set Z := (slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum
    set Y := (keys.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum
    have a1 : nO * (κ' * (tt * ub) * 31 + 100) ≤ nO * (κ' * 31 + 100) * (tt * (ub + 1) + 1) := by
      have : tt * ub ≤ tt * (ub + 1) + 1 := by nlinarith
      calc nO * (κ' * (tt * ub) * 31 + 100) ≤ nO * (κ' * (tt * (ub + 1) + 1) * 31 + 100 * (tt * (ub + 1) + 1)) := by
            gcongr
            omega
        _ = _ := by ring
    have a2 : κ * (tt * ub + 1) ≤ κ * (tt * (ub + 1) + 1) := by gcongr; omega
    have a3 : tt * (ub * 62 + 100) ≤ 100 * (tt * (ub + 1)) := by nlinarith
    nlinarith [Nat.zero_le (κ * Z), Nat.zero_le (κ * Y), Nat.zero_le (nO * (κ' * 31 + 100) * Z),
      Nat.zero_le (nO * (κ' * 31 + 100) * Y)]

end Nc.Grp
