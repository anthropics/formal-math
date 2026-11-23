/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Acc.CompK
import Nc.Acc.Trie
import Nc.Acc.LowDeg

/-!
# The program that guesses a parse tree

The argument of the loop is (the loop, (budget, (stack of gates, tree of pairs of letters))).
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- Concatenation of lists of bits. -/
theorem appBits_gives {a b : Fm} {x : Tree} {ca cb : ℕ} {v w : List Bool} (ha : Gives θ a x (ofBits v) ca)
    (hb : Gives θ b x (ofBits w) cb) : Gives θ (appF a b) x (ofBits (v ++ w)) (ca + cb + v.length * 62 + 41) := by
  rw [← listT_ofBits] at ha hb ⊢
  have := appF_gives ha hb
  rw [← List.map_append, List.length_map] at this
  exact this

/-- Guess a word. -/
def gwd : ℕ → Fm
  | 0 => .quote .nil
  | M + 1 => .cons (.ite .guess (.quote one) (.quote .nil)) (gwd M)

theorem gwd_does (M : ℕ) (x : Tree) : Does θ (gwd M) x ((wd M).map fun w => (1, ofBits w)) (6 * M + 1) := by
  induction M with
  | zero => exact (Gives.quote .nil x).mono (by norm_num)
  | succ M ih =>
    have h := ((Gives.quote (θ := θ) one x).either (Gives.quote .nil x)).cons ih
    have e : (([(1, one)] ++ [(1, Tree.nil)] : List (A × Tree)).flatMap fun q =>
        ((wd M).map fun w => ((1 : A), ofBits w)).map fun r => (q.1 * r.1, Tree.cons q.2 r.2)) =
        (wd (M + 1)).map fun w => (1, ofBits w) := by
      simp [wd, Function.comp_def, ofBits, bit]
    rw [e] at h
    exact h.mono (by omega)

/-- A step of the walk. The argument is (tree, path so far, reversed). -/
def stepW : Fm := .ite .guess (.cons (.tl (.hd .id)) (.cons (.quote one) (.tl .id)))
  (.cons (.hd (.hd .id)) (.cons (.quote .nil) (.tl .id)))

/-- Guess a path in a tree. -/
def walkF : ℕ → Fm
  | 0 => .id
  | m + 1 => lett stepW (walkF m)

theorem walkF_does (m : ℕ) (T : Tree) (acc : List Bool) : Does θ (walkF m) (.cons T (ofBits acc))
    ((wd m).map fun p => (1, .cons (look p T) (ofBits (p.reverse ++ acc)))) (12 * m + 1) := by
  induction m generalizing T acc with
  | zero => exact (Gives.id _).mono (by norm_num)
  | succ m ih =>
    have h0 := (Gives.cons (Gives.id (θ := θ) (.cons T (ofBits acc))).hd.tl
      (Gives.cons (Gives.quote one _) (Gives.id _).tl)).either
      (Gives.cons (Gives.id (θ := θ) (.cons T (ofBits acc))).hd.hd (Gives.cons (Gives.quote .nil _) (Gives.id _).tl))
    have h := h0.lett (G := walkF m) (R := fun o => (wd m).map fun p => (1, .cons (look p o.hd)
      (ofBits (p.reverse ++ o.tl.path)))) (d := 12 * m + 1) (by
        intro q hq
        simp only [hd_cons, tl_cons, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · have := ih T.tl (true :: acc)
          have e : (Tree.cons one (ofBits acc)).path = true :: acc := by
            have : ofBits (true :: acc) = Tree.cons one (ofBits acc) := rfl
            rw [← this, path_ofBits]
          simp only [hd_cons, tl_cons, e]
          exact this
        · have := ih T.hd (false :: acc)
          have e : (Tree.cons Tree.nil (ofBits acc)).path = false :: acc := by
            have : ofBits (false :: acc) = Tree.cons .nil (ofBits acc) := rfl
            rw [← this, path_ofBits]
          simp only [hd_cons, tl_cons, e]
          exact this)
    have e1 : (Tree.cons one (ofBits acc)).path = true :: acc := by
      have : ofBits (true :: acc) = Tree.cons one (ofBits acc) := rfl
      rw [← this, path_ofBits]
    have e2 : (Tree.cons Tree.nil (ofBits acc)).path = false :: acc := by
      have : ofBits (false :: acc) = Tree.cons .nil (ofBits acc) := rfl
      rw [← this, path_ofBits]
    simp only [bindW, hd_cons, tl_cons, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_map, Function.comp_def, one_mul, e1, e2] at h
    have e : ((wd (m + 1)).map fun p => ((1 : A), Tree.cons (look p T) (ofBits (p.reverse ++ acc)))) =
        ((wd m).map fun p => ((1 : A), Tree.cons (look p T.tl) (ofBits (p.reverse ++ true :: acc)))) ++
        (wd m).map fun p => ((1 : A), Tree.cons (look p T.hd) (ofBits (p.reverse ++ false :: acc))) := by
      simp [wd, Function.comp_def, look]
    rw [e]
    exact h.mono (by omega)

/-- The code of a letter. -/
def lc (t : Tree) : List Bool := if t = .nil then [false, false] else t.path

/-- The gate on top of the stack; the argument is (argument of the loop, anything). -/
def topF : Fm := .hd (.hd (.tl (.tl (.hd .id))))

/-- The name of the weight of an input. -/
def nameL : Fm := .cons (.quote .nil) (.cons (.quote one) (appF topF (appF (.tl (.tl .id))
  (appF (.ite (.hd (.tl .id)) (.hd (.tl .id)) (.quote (ofBits [false, false]))) (.quote (ofBits [false]))))))

/-- The name of the weight of a product gate. -/
def nameK : Fm := .cons (.quote .nil) (.cons (.quote .nil) (appF topF (appF (.hd (.tl .id))
  (appF (.tl (.tl .id)) (.quote (ofBits [false]))))))

/-- An input is read. -/
def leafB : Fm := .cons (.mul nameL) (.run (.hd (.hd .id)) (.cons (.hd (.hd .id)) (.cons (.hd (.tl (.hd .id)))
  (.cons (.tl (.hd (.tl (.tl (.hd .id))))) (.tl (.tl (.tl (.hd .id))))))))

/-- A product gate. -/
def intB : Fm := .cons (.mul nameK) (.run (.hd (.hd .id)) (.cons (.hd (.hd .id)) (.cons (.tl (.hd (.tl (.hd .id))))
  (.cons (.cons (.hd (.tl .id)) (.cons (.tl (.tl .id)) (.tl (.hd (.tl (.tl (.hd .id)))))))
    (.tl (.tl (.tl (.hd .id))))))))

/-- Guess an input. -/
def leafF (m : ℕ) : Fm := lett (.cons .id (lett (.cons (.tl (.tl (.tl .id))) (.quote .nil)) (walkF m))) leafB

/-- Guess a product gate. -/
def intF (M : ℕ) : Fm := .ite (.hd (.tl .id)) (lett (.cons .id (.cons (gwd M) (gwd M))) intB) .fail

/-- The loop. -/
def loopF (M m : ℕ) : Fm := .ite (.hd (.tl (.tl .id))) (.ite .guess (leafF m) (intF M)) (.quote .nil)

theorem nameL_gives {self T t : Tree} {b : Tree} {g acc : List Bool} {ws : List (List Bool)}
    (ht : t = .nil ∨ ∃ c : List Bool, c.length = 2 ∧ t = ofBits c) :
    Gives θ nameL (.cons (.cons self (.cons b (.cons (listT ((g :: ws).map ofBits)) T))) (.cons t (ofBits acc)))
      (ofBits ([false, true] ++ g ++ acc ++ lc t ++ [false])) (62 * (g.length + acc.length) + 500) := by
  set y := Tree.cons (.cons self (.cons b (.cons (listT ((g :: ws).map ofBits)) T))) (.cons t (ofBits acc)) with hy
  have hg : Gives θ topF y (ofBits g) 6 := (Gives.id y).hd.tl.tl.hd.hd
  have hacc : Gives θ (.tl (.tl .id)) y (ofBits acc) 3 := (Gives.id y).tl.tl
  have hc : Gives θ (.ite (.hd (.tl .id)) (.hd (.tl .id)) (.quote (ofBits [false, false]))) y (ofBits (lc t)) 8 := by
    have h1 : Gives θ (.hd (.tl .id)) y t 3 := (Gives.id y).tl.hd
    rcases ht with rfl | ⟨c, hc2, rfl⟩
    · exact (h1.ite_false (Gives.quote _ _)).mono (by norm_num)
    · have hne : ofBits c ≠ .nil := by
        cases c with
        | nil => simp at hc2
        | cons a c => simp [ofBits]
      have e : lc (ofBits c) = c := by rw [lc, if_neg hne, path_ofBits]
      rw [e]
      exact (h1.ite_true hne h1).mono (by norm_num)
  have hlc : (lc t).length ≤ 2 := by
    rcases ht with rfl | ⟨c, hc2, rfl⟩
    · simp [lc]
    · unfold lc
      split_ifs
      · simp
      · rw [path_ofBits, hc2]
  have h := Gives.cons (Gives.quote (θ := θ) .nil y) (Gives.cons (Gives.quote one y) (appBits_gives hg (appBits_gives hacc
    (appBits_gives hc (Gives.quote (ofBits [false]) y)))))
  have e : ofBits ([false, true] ++ g ++ acc ++ lc t ++ [false]) =
      Tree.cons .nil (.cons one (ofBits (g ++ (acc ++ (lc t ++ [false]))))) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  rw [e]
  exact h.mono (by omega)

theorem nameK_gives {self T : Tree} {b : Tree} {g l r : List Bool} {ws : List (List Bool)} :
    Gives θ nameK (.cons (.cons self (.cons b (.cons (listT ((g :: ws).map ofBits)) T))) (.cons (ofBits l) (ofBits r)))
      (ofBits ([false, false] ++ g ++ l ++ r ++ [false])) (62 * (g.length + l.length + r.length) + 500) := by
  set y := Tree.cons (.cons self (.cons b (.cons (listT ((g :: ws).map ofBits)) T))) (.cons (ofBits l) (ofBits r)) with hy
  have hg : Gives θ topF y (ofBits g) 6 := (Gives.id y).hd.tl.tl.hd.hd
  have hl : Gives θ (.hd (.tl .id)) y (ofBits l) 3 := (Gives.id y).tl.hd
  have hr : Gives θ (.tl (.tl .id)) y (ofBits r) 3 := (Gives.id y).tl.tl
  have h := Gives.cons (Gives.quote (θ := θ) .nil y) (Gives.cons (Gives.quote .nil y) (appBits_gives hg (appBits_gives hl
    (appBits_gives hr (Gives.quote (ofBits [false]) y)))))
  have e : ofBits ([false, false] ++ g ++ l ++ r ++ [false]) =
      Tree.cons .nil (.cons .nil (ofBits (g ++ (l ++ (r ++ [false]))))) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  rw [e]
  exact h.mono (by omega)

open Nc.Acc in
/-- **The loop computes the sum over the parse trees.** -/
theorem loopF_kv {M m : ℕ} {T : Tree} {κ : List Bool → R} {S : Set (List Bool)} {E : ℕ → PowerSeries R} {a : ℕ → R}
    {k : ℕ → ℕ → ℕ → R}
    (hE : ∀ g, E g = PowerSeries.C (a g) + PowerSeries.X * ∑ l ∈ Finset.range (2 ^ M), ∑ r ∈ Finset.range (2 ^ M),
      PowerSeries.C (k g l r) * (E l * E r))
    (hk : ∀ g l r : List Bool, g.length = M → l.length = M → r.length = M →
      κ ([false, false] ++ g ++ l ++ r ++ [false]) = k (KT.val g) (KT.val l) (KT.val r) ∧
      [false, false] ++ g ++ l ++ r ++ [false] ∈ S)
    (ha : ∀ g : List Bool, g.length = M →
      ((wd m).map fun p => κ ([false, true] ++ g ++ p.reverse ++ lc (look p T) ++ [false])).sum = a (KT.val g))
    (hS : ∀ g p c : List Bool, g.length = M → p.length = m → c.length = 2 → [false, true] ++ g ++ p ++ c ++ [false] ∈ S)
    (hT : ∀ p : List Bool, p.length = m → look p T = .nil ∨ ∃ c : List Bool, c.length = 2 ∧ look p T = ofBits c)
    (n b : ℕ) (ws : List (List Bool)) (hn : 2 * b + ws.length ≤ n) (hws : ∀ w ∈ ws, w.length = M) :
    KV θ κ S (loopF M m) (.cons (loopF M m).code (.cons (num b) (.cons (listT (ws.map ofBits)) T)))
      (W E b (ws.map KT.val)) ((n + 1) * (400 * (M + m) + 2000)) := by
  induction n generalizing b ws with
  | zero =>
    have hws0 : ws = [] := List.length_eq_zero_iff.1 (by omega)
    subst hws0
    refine (KV.ite_false (Gives.id _).tl.tl.hd (KV.of_gives (Gives.quote .nil _))).mono ?_ |>.congr (W_nil E b).symm
    omega
  | succ n ih =>
    cases ws with
    | nil =>
      refine (KV.ite_false (Gives.id _).tl.tl.hd (KV.of_gives (Gives.quote .nil _))).mono ?_ |>.congr (W_nil E b).symm
      nlinarith
    | cons g ws =>
      have hg : g.length = M := hws g List.mem_cons_self
      have hws' : ∀ w ∈ ws, w.length = M := fun w hw => hws w (List.mem_cons_of_mem _ hw)
      set x := Tree.cons (loopF M m).code (.cons (num b) (.cons (listT ((g :: ws).map ofBits)) T)) with hx
      rw [List.length_cons] at hn
      have hlc : ∀ p : List Bool, p.length = m → (lc (look p T)).length = 2 := by
        intro p hp
        rcases hT p hp with h | ⟨c, hc, h⟩
        · rw [h]
          rfl
        · rw [h, lc]
          split_ifs with h2
          · rfl
          · rw [path_ofBits, hc]
      -- an input
      have h1 : KV θ κ S (leafF m) x (a (KT.val g) * W E b (ws.map KT.val))
          ((n + 1) * (400 * (M + m) + 2000) + 100 * (M + m) + 800) := by
        have hq := Does.cons (Gives.id (θ := θ) x) (Does.of_gives (Gives.cons (Gives.id (θ := θ) x).tl.tl.tl
          (Gives.quote (ofBits []) x)) (walkF_does m T []))
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, Function.comp_def, one_mul] at hq
        have h := KV.lett (κ := κ) (S := S) (G := leafB) (ω := fun o => κ ([false, true] ++ g ++ o.tl.tl.path ++ lc o.tl.hd
          ++ [false]) * W E b (ws.map KT.val)) hq (d := (n + 1) * (400 * (M + m) + 2000) + 62 * (M + m) + 600) (by
            intro q hq
            rw [List.mem_map] at hq
            obtain ⟨p, hp, rfl⟩ := hq
            have hpm := length_of_mem_wd hp
            simp only [tl_cons, hd_cons, path_ofBits]
            have m1 := KV.mul (κ := κ) (S := S) (nameL_gives (θ := θ) (self := (loopF M m).code) (b := num b) (T := T)
              (g := g) (ws := ws) (acc := p.reverse) (hT p hpm)) (by
                rw [path_ofBits]
                exact hS g p.reverse _ hg (by simpa using hpm) (hlc p hpm))
            rw [path_ofBits] at m1
            have r1 := KV.run (κ := κ) (S := S) (p := (loopF M m).code)
              (Gives.id (θ := θ) (.cons x (.cons (look p T) (ofBits p.reverse)))).hd.hd
              (Gives.cons (Gives.id _).hd.hd (Gives.cons (Gives.id _).hd.tl.hd (Gives.cons (Gives.id _).hd.tl.tl.hd.tl
                (Gives.id _).hd.tl.tl.tl))) (by
                rw [Fm.ofTree_code]
                exact ih b ws (by omega) hws')
            refine (KV.cons m1 r1).mono ?_
            simp only [List.length_reverse]
            omega)
        refine (h.mono (by omega)).congr ?_
        rw [List.map_map]
        simp only [Function.comp_def, map_one, one_mul, tl_cons, hd_cons, path_ofBits]
        rw [List.sum_map_mul_right, ha g hg]
      -- a product gate
      have h2 : KV θ κ S (intF M) x (Wi E (2 ^ M) (k (KT.val g)) (ws.map KT.val) b) ((n + 1) * (400 * (M + m) + 2000) + 300 * (M + m) + 900) := by
        cases b with
        | zero =>
          refine (KV.ite_false (Gives.id _).tl.hd (KV.fail x)).mono ?_
          omega
        | succ b =>
          have hq := Does.cons (Gives.id (θ := θ) x) (Does.cons (gwd_does (θ := θ) M x) (gwd_does M x))
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, Function.comp_def, one_mul,
            List.flatMap_map, List.map_flatMap] at hq
          have h := KV.lett (κ := κ) (S := S) (G := intB) (ω := fun o => κ ([false, false] ++ g ++ o.tl.hd.path ++ o.tl.tl.path
            ++ [false]) * W E b (KT.val o.tl.hd.path :: KT.val o.tl.tl.path :: ws.map KT.val)) hq
            (d := (n + 1) * (400 * (M + m) + 2000) + 62 * (3 * M) + 600) (by
              intro q hq
              rw [List.mem_flatMap] at hq
              obtain ⟨l, hl, hq⟩ := hq
              rw [List.mem_map] at hq
              obtain ⟨r, hr, rfl⟩ := hq
              have hlm := length_of_mem_wd hl
              have hrm := length_of_mem_wd hr
              simp only [tl_cons, hd_cons, path_ofBits]
              have m1 := KV.mul (κ := κ) (S := S) (nameK_gives (θ := θ) (self := (loopF M m).code) (b := num (b + 1)) (T := T)
                (g := g) (ws := ws) (l := l) (r := r)) (by
                  rw [path_ofBits]
                  exact (hk g l r hg hlm hrm).2)
              rw [path_ofBits] at m1
              have r1 := KV.run (κ := κ) (S := S) (p := (loopF M m).code)
                (Gives.id (θ := θ) (.cons x (.cons (ofBits l) (ofBits r)))).hd.hd
                (Gives.cons (Gives.id _).hd.hd (Gives.cons (Gives.id _).hd.tl.hd.tl (Gives.cons
                  (Gives.cons (Gives.id _).tl.hd (Gives.cons (Gives.id _).tl.tl (Gives.id _).hd.tl.tl.hd.tl))
                  (Gives.id _).hd.tl.tl.tl))) (by
                  rw [Fm.ofTree_code]
                  exact ih b (l :: r :: ws) (by simp only [List.length_cons]; omega) (by
                    intro w hw
                    simp only [List.mem_cons] at hw
                    rcases hw with rfl | rfl | hw
                    · exact hlm
                    · exact hrm
                    · exact hws' w hw))
              refine (KV.cons m1 r1).mono ?_
              omega)
          refine ((KV.ite_true (H := .fail) (Gives.id _).tl.hd (by rw [hx]; simp [num]) h).mono ?_).congr ?_
          · omega
          · rw [sum_flatMap_map, Wi]
            simp only [List.map_map, Function.comp_def, map_one, one_mul, tl_cons, hd_cons, path_ofBits]
            rw [← sum_wd M fun l => ∑ r ∈ Finset.range (2 ^ M), k (KT.val g) l r * W E b (l :: r :: ws.map KT.val)]
            congr 1
            refine List.map_congr_left fun l hl => ?_
            rw [← sum_wd M fun r => k (KT.val g) (KT.val l) r * W E b (KT.val l :: r :: ws.map KT.val)]
            congr 1
            refine List.map_congr_left fun r hr => ?_
            rw [(hk g l r hg (length_of_mem_wd hl) (length_of_mem_wd hr)).1]
      have h3 := KV.ite_true (H := .quote .nil) (Gives.id (θ := θ) x).tl.tl.hd (by rw [hx]; simp [listT]) (KV.either h1 h2)
      refine (h3.mono ?_).congr ?_
      · have e : (n + 1 + 1) * (400 * (M + m) + 2000) = (n + 1) * (400 * (M + m) + 2000) + (400 * (M + m) + 2000) := by ring
        rw [e]
        omega
      · rw [List.map_cons, W_cons (hE (KT.val g))]

end NS1
