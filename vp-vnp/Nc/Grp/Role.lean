/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Put
import Nc.Grp.Script

/-!
# The program of a role: streams

The contents of the units given at the slots are put together to streams of bits.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- Step: argument (key, (trie, bits)). -/
def streamStep : Fm := .ite (getF (.hd .id) (.hd (.tl .id)))
  (.cons (.hd (.tl .id)) (appF (getF (.hd .id) (.hd (.tl .id))) (.tl (.tl .id)))) .fail

/-- A stream: argument (trie, keys). -/
def streamF : Fm := lett (foldF streamStep (.cons (.hd .id) (.quote .nil)) (.tl .id)) (.tl .id)

/-- Step for several streams: argument (keys, (trie, streams)). -/
def streamsStep : Fm := .cons (.hd (.tl .id))
  (.cons (lett (.cons (.hd (.tl .id)) (.hd .id)) streamF) (.tl (.tl .id)))

/-- Several streams: argument (trie, lists of keys). -/
def streamsF : Fm := lett (foldF streamsStep (.cons (.hd .id) (.quote .nil)) (.tl .id))
  (foldF .id (.quote .nil) (.tl .id))

section stream

variable {ub : ℕ} {ct : List Bool → List Bool} {t : Tree}

theorem streamStep_does (hct : ∀ k, tget k t = ofBits (ct k)) (hlen : ∀ k, (ct k).length ≤ ub)
    (k : List Bool) (acc : List Bool) :
    Does θ streamStep (.cons (ofBits k) (.cons t (ofBits acc)))
      ((if ct k ≠ [] then [((1 : A), ct k ++ acc)] else []).map (Prod.map id fun acc => .cons t (ofBits acc)))
      (ub * 62 + k.length * 60 + 300) := by
  have h1 : Gives θ (getF (.hd .id) (.hd (.tl .id))) (.cons (ofBits k) (.cons t (ofBits acc))) (ofBits (ct k))
      (k.length * 30 + 40) := by
    have := getF_gives (θ := θ) (x := .cons (ofBits k) (.cons t (ofBits acc)))
      (pf := .hd .id) (tf := .hd (.tl .id)) (p := ofBits k) (t := t) (Gives.id _).hd (Gives.id _).tl.hd
    rw [path_ofBits, hct, len_ofBits] at this
    exact this.mono (by omega)
  by_cases hk : ct k = []
  · have h0 : Gives θ (getF (.hd .id) (.hd (.tl .id))) (.cons (ofBits k) (.cons t (ofBits acc))) .nil
        (k.length * 30 + 40) := by
      rw [hk] at h1
      exact h1
    refine ((Does.ite_false h0 (Does.fail _)).replace ?_).mono (by omega)
    simp [hk]
  · have h2 := appB_gives h1 (Gives.id (θ := θ) (.cons (ofBits k) (.cons t (ofBits acc)))).tl.tl
    have h3 : ofBits (ct k) ≠ .nil := by
      cases h : ct k with
      | nil => exact absurd h hk
      | cons b w => simp [ofBits]
    have h5 := hlen k
    refine ((Does.ite_true h1 h3 (Gives.cons (Gives.id _).tl.hd h2)).replace ?_).mono (by omega)
    simp [hk]

theorem foldL_stream (es : List (List Bool)) (acc : List Bool) :
    foldL (A := A) (fun k acc => if ct k ≠ [] then [((1 : A), ct k ++ acc)] else []) es acc =
      if ∀ k ∈ es, ct k ≠ [] then [((1 : A), es.reverse.flatMap ct ++ acc)] else [] := by
  induction es generalizing acc with
  | nil => simp [foldL]
  | cons e es ih =>
    rw [foldL]
    by_cases he : ct e ≠ []
    · rw [if_pos he, bindL_single, ih]
      by_cases hes : ∀ k ∈ es, ct k ≠ []
      · rw [if_pos hes, if_pos (by
          intro k hk
          rcases List.mem_cons.1 hk with rfl | hk
          · exact he
          · exact hes k hk)]
        simp
      · rw [if_neg hes, if_neg fun h => hes fun k hk => h k (List.mem_cons_of_mem _ hk)]
    · rw [if_neg he, if_neg fun h => he (h e List.mem_cons_self)]
      rfl

theorem streamF_does (hct : ∀ k, tget k t = ofBits (ct k)) (hlen : ∀ k, (ct k).length ≤ ub)
    (es : List (List Bool)) :
    Does θ streamF (.cons t (listT (es.map ofBits)))
      ((if ∀ k ∈ es, ct k ≠ [] then [((1 : A), es.reverse.flatMap ct)] else []).map (Prod.map id ofBits))
      ((es.map fun k => ub * 62 + k.length * 60 + 330).sum + 60) := by
  have h0 : Gives θ (.cons (.hd .id) (.quote .nil)) (.cons t (listT (es.map ofBits))) (.cons t (ofBits [])) 8 :=
    (Gives.cons (Gives.id _).hd (Gives.quote _ _)).mono (by omega)
  have h1 := foldT (θ := θ) (A := A) (encE := ofBits) (xs := es)
    (enc := fun acc : List Bool => .cons t (ofBits acc)) (s₀ := [])
    (f := fun k acc => if ct k ≠ [] then [((1 : A), ct k ++ acc)] else []) (Inv := fun _ _ => True)
    (d := fun k => ub * 62 + k.length * 60 + 300) (step := streamStep) (l := .tl .id) h0 (Gives.id _).tl
    (fun k _ acc _ _ => ⟨streamStep_does hct hlen k acc, fun _ _ => trivial⟩) trivial
  have h2 := Does.lettE (G := .tl .id) (f := fun acc => [((1 : A), acc)]) (enc' := ofBits) (d := 2) h1
    (fun b _ => by exact (Gives.id _).tl)
  rw [foldL_stream] at h2
  have e : (es.map fun k => ub * 62 + k.length * 60 + 300 + 30) = es.map fun k => ub * 62 + k.length * 60 + 330 :=
    List.map_congr_left fun k _ => by omega
  rw [e] at h2
  refine (h2.replace ?_).mono (by omega)
  split_ifs <;> simp [bindL]

theorem streamsStep_does (hct : ∀ k, tget k t = ofBits (ct k)) (hlen : ∀ k, (ct k).length ≤ ub)
    (es : List (List Bool)) (acc : List (List Bool)) :
    Does θ streamsStep (.cons (listT (es.map ofBits)) (.cons t (listT (acc.map ofBits))))
      ((if ∀ k ∈ es, ct k ≠ [] then [((1 : A), es.reverse.flatMap ct :: acc)] else []).map
        (Prod.map id fun acc => .cons t (listT (acc.map ofBits))))
      ((es.map fun k => ub * 62 + k.length * 60 + 330).sum + 150) := by
  have e1 : Gives θ (.cons (.hd (.tl .id)) (.hd .id)) (.cons (listT (es.map ofBits)) (.cons t (listT (acc.map ofBits))))
      (.cons t (listT (es.map ofBits))) 20 := (Gives.cons (Gives.id _).tl.hd (Gives.id _).hd).mono (by omega)
  have e2 := Does.of_gives e1 (streamF_does (θ := θ) hct hlen es)
  have e3 := Does.cons (Gives.id (θ := θ) (.cons (listT (es.map ofBits)) (.cons t (listT (acc.map ofBits))))).tl.hd
    (Does.cons e2 (Gives.id _).tl.tl)
  refine (e3.replace ?_).mono (by omega)
  split_ifs <;> simp [listT]

theorem foldL_streams (slots : List (List (List Bool))) (acc : List (List Bool)) :
    foldL (A := A) (fun es acc => if ∀ k ∈ es, ct k ≠ [] then [((1 : A), es.reverse.flatMap ct :: acc)]
      else []) slots acc = if ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ [] then
        [((1 : A), (slots.map fun es => es.reverse.flatMap ct).reverse ++ acc)] else [] := by
  induction slots generalizing acc with
  | nil => simp [foldL]
  | cons es slots ih =>
    rw [foldL]
    by_cases he : ∀ k ∈ es, ct k ≠ []
    · rw [if_pos he, bindL_single, ih]
      by_cases hes : ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ []
      · rw [if_pos hes, if_pos (by
          intro es' h'
          rcases List.mem_cons.1 h' with rfl | h'
          · exact he
          · exact hes es' h')]
        simp
      · rw [if_neg hes, if_neg fun h => hes fun es' h' => h es' (List.mem_cons_of_mem _ h')]
    · rw [if_neg he, if_neg fun h => he (h es List.mem_cons_self)]
      rfl

theorem streamsF_does (hct : ∀ k, tget k t = ofBits (ct k)) (hlen : ∀ k, (ct k).length ≤ ub)
    (slots : List (List (List Bool))) :
    Does θ streamsF (.cons t (keysT slots))
      ((if ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ [] then [((1 : A), slots.map fun es => es.reverse.flatMap ct)]
        else []).map (Prod.map id fun l : List (List Bool) => listT (l.map ofBits)))
      ((slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum + 100) := by
  have h0 : Gives θ (.cons (.hd .id) (.quote .nil)) (.cons t (keysT slots))
      (.cons t (listT (([] : List (List Bool)).map ofBits))) 8 :=
    (Gives.cons (Gives.id _).hd (Gives.quote _ _)).mono (by omega)
  have h1 := foldT (θ := θ) (A := A) (encE := fun es : List (List Bool) => listT (es.map ofBits)) (xs := slots)
    (enc := fun acc : List (List Bool) => .cons t (listT (acc.map ofBits))) (s₀ := [])
    (f := fun es acc => if ∀ k ∈ es, ct k ≠ [] then [((1 : A), es.reverse.flatMap ct :: acc)] else [])
    (Inv := fun ys acc => ys.length + acc.length = slots.length)
    (d := fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 150) (step := streamsStep)
    (l := .tl .id) h0 (Gives.id _).tl
    (fun es ys acc _ hinv => ⟨streamsStep_does hct hlen es acc, fun q hq => by
      split_ifs at hq
      · rw [List.mem_singleton] at hq
        subst hq
        simp only [List.length_cons] at hinv ⊢
        omega
      · simp at hq⟩) (by simp)
  rw [foldL_streams, List.append_nil] at h1
  have h2 := Does.lettE (G := foldF .id (.quote .nil) (.tl .id)) (f := fun acc => [((1 : A), acc.reverse)])
    (enc' := fun l : List (List Bool) => listT (l.map ofBits)) (d := slots.length * 31 + 30) h1 (fun b hb => by
      have hl : b.2.length = slots.length := by
        split_ifs at hb
        · rw [List.mem_singleton] at hb
          subst hb
          simp
        · simp at hb
      have := rev_gives (θ := θ) (x := .cons t (listT (b.2.map ofBits))) (ys := [])
        (xs := b.2.map ofBits) (s := .quote .nil) (l := .tl .id) (Gives.quote _ _) (Gives.id _).tl
      rw [List.append_nil, ← List.map_reverse, List.length_map, hl] at this
      exact this.mono (by omega))
  refine (h2.replace ?_).mono ?_
  · split_ifs <;> simp [bindL]
  · have : (slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 150 + 30).sum + slots.length * 60 =
        (slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum := by
      clear h1 h2 h0
      induction slots with
      | nil => rfl
      | cons es slots ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
    omega

end stream

end Nc.Grp
