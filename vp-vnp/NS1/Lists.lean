/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Comp

/-!
# Lists, equality, tries
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- A list of trees as a tree. -/
def listT : List Tree → Tree
  | [] => .nil
  | x :: xs => .cons x (listT xs)

@[simp] theorem toList_listT (xs : List Tree) : (listT xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listT, toList, ih]

theorem listT_toList (x : Tree) : listT x.toList = x := by
  induction x with
  | nil => rfl
  | cons a b _ ih => simp [listT, toList, ih]

theorem listT_ofBits (w : List Bool) : listT (w.map bit) = ofBits w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [listT, ofBits, ih]

/-- Apply the program that is the value of a formula to the values of another one. -/
theorem Does.runW {F G : Fm} {x p : Tree} {Q : List (A × Tree)} {R : Tree → List (A × Tree)} {c d e : ℕ}
    (hF : Gives θ F x p c) (hG : Does θ G x Q d) (h : ∀ q ∈ Q, Does θ (Fm.ofTree p) q.2 (R q.2) e) :
    Does θ (.run F G) x (bindW Q R) (c + d + e + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have ho : ∀ r ∈ l, r.out = p := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  have hG' : ∀ s ∈ l', Does θ (Fm.ofTree p) s.out (R s.out) e := by
    intro s hs
    obtain ⟨-, -, q, hq, h'⟩ := f2 s hs
    rw [← h']
    exact h q hq
  refine ⟨_, Ev.run' e1 f1 fun r hr s hs => by rw [ho r hr]; exact (hG' s hs).hl, ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
    rw [ho r hr] at ht
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, q, hq, b3⟩ := f2 s hs
    obtain ⟨c1, c2, q', hq', c3⟩ := (hG' s hs).evl.1 t ht
    rw [← b3] at hq'
    refine ⟨by simp [Run.seq, Run.tick, a1, b1, c1], ?_, (q.1 * q'.1, q'.2), mem_bindW_of hq hq', c3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map, wsum_bindW]
    have h1 : ∀ r ∈ l, ((l'.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out).map fun u => u.th * φ u.out).sum = r.th * wsum Q fun o => wsum (R o) φ := by
      intro r hr
      rw [sum_flatMap_map, ← f3 fun o => wsum (R o) φ, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s hs => ?_
      rw [ho r hr, List.map_map, ← (hG' s hs).evl.2 φ, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick]
      ring
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum Q fun o => wsum (R o) φ
    rw [this]
    simp [wsum]

section Fold

/-- Fold over a list with a state. The argument is (this program, (state, list)); `step` is applied to
(element, state). -/
def foldB (step : Fm) : Fm := .ite (.tl (.tl .id))
  (.run (.hd .id) (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
    (.tl (.tl (.tl .id)))))) (.hd (.tl .id))

/-- Fold: `s` gives the state at the beginning, `l` the list. -/
def foldF (step s l : Fm) : Fm := app (foldB step).code (.cons (.quote (foldB step).code) (.cons s l))

/-- The weighted list of a fold. -/
def foldW (f : Tree → Tree → List (A × Tree)) : List Tree → Tree → List (A × Tree)
  | [], σ => [(1, σ)]
  | x :: xs, σ => bindW (f x σ) (foldW f xs)

theorem foldB_does {step : Fm} {f : Tree → Tree → List (A × Tree)} {Inv : List Tree → Tree → Prop} {d : Tree → ℕ}
    {xs : List Tree} (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ → Does θ step (.cons x σ) (f x σ) (d x) ∧
      ∀ q ∈ f x σ, Inv ys q.2) {σ : Tree} (hσ : Inv xs σ) :
    Does θ (foldB step) (.cons (foldB step).code (.cons σ (listT xs))) (foldW f xs σ)
      ((xs.map fun x => d x + 30).sum + 10) := by
  induction xs generalizing σ with
  | nil => exact (Does.ite_false (Gives.id _).tl.tl (Gives.id _).tl.hd).mono (by simp)
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h x xs σ List.mem_cons_self hσ
    have e1 : Does θ (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
        (.cons (foldB step).code (.cons σ (listT (x :: xs)))) (f x σ) (8 + d x + 2) :=
      Does.of_gives (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.hd) h1
    have e2 := Does.cons (Gives.id (θ := θ) (.cons (foldB step).code (.cons σ (listT (x :: xs))))).hd
      (Does.cons e1 (Gives.id (.cons (foldB step).code (.cons σ (listT (x :: xs))))).tl.tl.tl)
    have e3 := Does.runW (R := fun o => foldW f xs o.tl.hd) (e := (xs.map fun x => d x + 30).sum + 10)
      (Gives.id (θ := θ) (.cons (foldB step).code (.cons σ (listT (x :: xs))))).hd e2 (by
      intro q hq
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map, List.mem_flatMap,
        List.map_cons, List.map_nil, List.mem_singleton] at hq
      obtain ⟨q1, ⟨q2, hq2, rfl⟩, rfl⟩ := hq
      show Does θ (Fm.ofTree (foldB step).code) (.cons (foldB step).code (.cons q2.2 (listT xs))) _ _
      rw [Fm.ofTree_code]
      exact ih (fun y ys σ hy => h y ys σ (List.mem_cons_of_mem _ hy)) (h2 q2 hq2))
    refine ((Does.ite_true (Gives.id _).tl.tl (by simp [listT]) e3).congr ?_ fun φ => ?_).mono ?_
    · intro p hp
      obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map, List.mem_flatMap,
        List.map_cons, List.map_nil, List.mem_singleton] at hq
      obtain ⟨q1, ⟨q2, hq2, rfl⟩, rfl⟩ := hq
      exact ⟨_, mem_bindW_of hq2 hr, h3.symm⟩
    · rw [foldW, wsum_bindW, wsum_bindW]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
      simp only [wsum, List.map_map, one_mul, mul_one, flatMap_single, Function.comp_def, hd_cons, tl_cons]
    · simp only [List.map_cons, List.sum_cons]
      omega

theorem foldF_does {step s l : Fm} {x σ : Tree} {cs cl : ℕ} {f : Tree → Tree → List (A × Tree)}
    {Inv : List Tree → Tree → Prop} {d : Tree → ℕ} {xs : List Tree} (hs : Gives θ s x σ cs)
    (hl : Gives θ l x (listT xs) cl) (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ →
      Does θ step (.cons x σ) (f x σ) (d x) ∧ ∀ q ∈ f x σ, Inv ys q.2) (hσ : Inv xs σ) :
    Does θ (foldF step s l) x (foldW f xs σ) (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have h1 := Gives.cons (Gives.quote (θ := θ) (foldB step).code x) (Gives.cons hs hl)
  have h2 := Does.app (p := (foldB step).code) (R := fun _ => foldW f xs σ) h1 (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [Fm.ofTree_code]
    exact foldB_does h hσ)
  refine (h2.congr ?_ fun φ => ?_).mono (by omega)
  · intro p hp
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
    exact ⟨r, hr, h3.symm⟩
  · rw [wsum_bindW]
    simp [wsum]

theorem foldW_det (g : Tree → Tree → Tree) (xs : List Tree) (σ : Tree) :
    foldW (A := A) (fun x σ => [(1, g x σ)]) xs σ = [(1, xs.foldl (fun σ x => g x σ) σ)] := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih => simp [foldW, bindW, ih]

/-- A deterministic fold. -/
theorem foldF_gives {step s l : Fm} {x σ : Tree} {cs cl : ℕ} {g : Tree → Tree → Tree}
    {Inv : List Tree → Tree → Prop} {d : Tree → ℕ} {xs : List Tree} (hs : Gives θ s x σ cs)
    (hl : Gives θ l x (listT xs) cl) (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ →
      Gives θ step (.cons x σ) (g x σ) (d x) ∧ Inv ys (g x σ)) (hσ : Inv xs σ) :
    Gives θ (foldF step s l) x (xs.foldl (fun σ x => g x σ) σ) (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have := foldF_does (f := fun x σ => [(1, g x σ)]) hs hl (fun x ys σ hx hσ => by
    obtain ⟨h1, h2⟩ := h x ys σ hx hσ
    refine ⟨h1, fun q hq => ?_⟩
    rw [List.mem_singleton] at hq
    subst hq
    exact h2) hσ
  rwa [foldW_det] at this

/-- Reverse a list onto another one. -/
theorem foldl_rev (xs : List Tree) (ys : List Tree) :
    xs.foldl (fun σ x => Tree.cons x σ) (listT ys) = listT (xs.reverse ++ ys) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, show Tree.cons x (listT ys) = listT (x :: ys) from rfl, ih]
    simp

theorem rev_gives {s l : Fm} {x : Tree} {cs cl : ℕ} {xs ys : List Tree} (hs : Gives θ s x (listT ys) cs)
    (hl : Gives θ l x (listT xs) cl) :
    Gives θ (foldF .id s l) x (listT (xs.reverse ++ ys)) (cs + cl + xs.length * 31 + 20) := by
  have := foldF_gives (step := .id) (g := fun x σ => .cons x σ) (Inv := fun _ _ => True) (d := fun _ => 1) hs hl
    (fun x _ σ _ _ => ⟨Gives.id _, trivial⟩) trivial
  rw [foldl_rev] at this
  simpa using this

/-- Concatenation. -/
def appF (a b : Fm) : Fm := foldF .id b (foldF .id (.quote .nil) a)

theorem appF_gives {a b : Fm} {x : Tree} {ca cb : ℕ} {xs ys : List Tree} (ha : Gives θ a x (listT xs) ca)
    (hb : Gives θ b x (listT ys) cb) :
    Gives θ (appF a b) x (listT (xs ++ ys)) (ca + cb + xs.length * 62 + 41) := by
  have h1 := rev_gives (Gives.quote (θ := θ) (listT []) x) ha
  rw [List.append_nil] at h1
  have h2 := rev_gives hb h1
  rw [List.reverse_reverse, List.length_reverse] at h2
  exact h2.mono (by omega)

end Fold

section Map

/-- Apply `step` to (parameter, element) for all elements of a list. The argument is (this program, (parameter,
list)). -/
def mapB (step : Fm) : Fm := .ite (.tl (.tl .id))
  (.cons (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl .id)))) step)
    (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.tl .id)) (.tl (.tl (.tl .id))))))) (.quote .nil)

/-- Map: `e` gives the parameter, `l` the list. -/
def mapF (step e l : Fm) : Fm := app (mapB step).code (.cons (.quote (mapB step).code) (.cons e l))

theorem mapB_gives {step : Fm} {e : Tree} {g : Tree → Tree} {d : Tree → ℕ} {xs : List Tree}
    (h : ∀ x ∈ xs, Gives θ step (.cons e x) (g x) (d x)) :
    Gives θ (mapB step) (.cons (mapB step).code (.cons e (listT xs))) (listT (xs.map g))
      ((xs.map fun x => d x + 40).sum + 10) := by
  induction xs with
  | nil => exact ((Gives.id _).tl.tl.ite_false (Gives.quote _ _)).mono (by simp)
  | cons x xs ih =>
    have e1 : Gives θ (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl .id)))) step)
        (.cons (mapB step).code (.cons e (listT (x :: xs)))) (g x) (8 + d x + 2) :=
      Gives.lett (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.hd) (h x List.mem_cons_self)
    have ih' : Gives θ (Fm.ofTree (mapB step).code) (.cons (mapB step).code (.cons e (listT xs))) (listT (xs.map g))
        ((xs.map fun x => d x + 40).sum + 10) := by
      rw [Fm.ofTree_code]
      exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    have e2 := Gives.run (Gives.id (θ := θ) (.cons (mapB step).code (.cons e (listT (x :: xs))))).hd
      (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.tl)) ih'
    refine (Gives.ite_true (Gives.id _).tl.tl (by simp [listT]) (Gives.cons e1 e2)).mono ?_
    simp only [List.map_cons, List.sum_cons]
    omega

theorem mapF_gives {step ef l : Fm} {x e : Tree} {ce cl : ℕ} {g : Tree → Tree} {d : Tree → ℕ} {xs : List Tree}
    (he : Gives θ ef x e ce) (hl : Gives θ l x (listT xs) cl) (h : ∀ x ∈ xs, Gives θ step (.cons e x) (g x) (d x)) :
    Gives θ (mapF step ef l) x (listT (xs.map g)) (ce + cl + (xs.map fun x => d x + 40).sum + 20) := by
  refine (Gives.app (p := (mapB step).code) (Gives.cons (Gives.quote _ _) (Gives.cons he hl)) (by
    rw [Fm.ofTree_code]
    exact mapB_gives h)).mono (by omega)

end Map

section Eq

/-- Equality of trees: 1 if equal, else empty. The argument is (this program, (a, b)). -/
def eqB : Fm := .ite (.hd (.tl .id))
  (.ite (.tl (.tl .id))
    (.ite (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.hd (.tl .id))) (.hd (.tl (.tl .id))))))
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl (.tl .id))))))
      (.quote .nil))
    (.quote .nil))
  (.ite (.tl (.tl .id)) (.quote .nil) (.quote one))

/-- Equality of two values. -/
def eqF (a b : Fm) : Fm := app eqB.code (.cons (.quote eqB.code) (.cons a b))

theorem eqB_gives (a b : Tree) : Gives θ eqB (.cons eqB.code (.cons a b)) (bit (decide (a = b))) (60 * a.size) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil =>
      refine ((Gives.id _).tl.hd.ite_false ((Gives.id _).tl.tl.ite_false (Gives.quote one _))).mono ?_
      simp [size]
    | cons b1 b2 =>
      refine ((Gives.id _).tl.hd.ite_false ((Gives.id _).tl.tl.ite_true (by simp) (Gives.quote .nil _))).mono ?_
      simp [size]
  | cons a1 a2 ih1 ih2 =>
    cases b with
    | nil =>
      refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_false (Gives.quote .nil _))).mono ?_
      simp only [size]
      omega
    | cons b1 b2 =>
      have h1 : Gives θ (Fm.ofTree eqB.code) (.cons eqB.code (.cons a1 b1)) (bit (decide (a1 = b1))) (60 * a1.size) := by
        rw [Fm.ofTree_code]; exact ih1 b1
      have h2 : Gives θ (Fm.ofTree eqB.code) (.cons eqB.code (.cons a2 b2)) (bit (decide (a2 = b2))) (60 * a2.size) := by
        rw [Fm.ofTree_code]; exact ih2 b2
      have r1 := Gives.run (Gives.id (θ := θ) (.cons eqB.code (.cons (.cons a1 a2) (.cons b1 b2)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.hd (Gives.id _).tl.tl.hd)) h1
      have r2 := Gives.run (Gives.id (θ := θ) (.cons eqB.code (.cons (.cons a1 a2) (.cons b1 b2)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.id _).tl.tl.tl)) h2
      by_cases hab : a1 = b1
      · have hb : bit (decide (a1 = b1)) ≠ .nil := by simp [hab, bit, one]
        have e : decide (Tree.cons a1 a2 = Tree.cons b1 b2) = decide (a2 = b2) := by simp [hab]
        rw [e]
        refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_true (by simp)
          (Gives.ite_true r1 hb r2))).mono ?_
        simp only [size]
        omega
      · have hb : bit (decide (a1 = b1)) = .nil := by simp [hab, bit]
        rw [hb] at r1
        have e : bit (decide (Tree.cons a1 a2 = Tree.cons b1 b2)) = .nil := by simp [hab, bit]
        rw [e]
        refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_true (by simp)
          (Gives.ite_false r1 (Gives.quote .nil _)))).mono ?_
        simp only [size]
        omega

theorem eqF_gives {a b : Fm} {x u v : Tree} {ca cb : ℕ} (ha : Gives θ a x u ca) (hb : Gives θ b x v cb) :
    Gives θ (eqF a b) x (bit (decide (u = v))) (ca + cb + 60 * u.size + 10) := by
  refine (Gives.app (p := eqB.code) (Gives.cons (Gives.quote _ _) (Gives.cons ha hb)) (by
    rw [Fm.ofTree_code]
    exact eqB_gives u v)).mono (by omega)

end Eq

section Choice

/-- Choose an element of a list. The argument is (this program, list). -/
def pickB : Fm := .ite (.tl .id)
  (.ite .guess (.hd (.tl .id)) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) .fail

/-- Choose an element of a list. -/
def pickF (l : Fm) : Fm := app pickB.code (.cons (.quote pickB.code) l)

theorem pickB_does (xs : List Tree) :
    Does θ pickB (.cons pickB.code (listT xs)) (xs.map fun x => (1, x)) (20 * xs.length + 10) := by
  induction xs with
  | nil => exact (Does.ite_false (Gives.id _).tl (Does.fail _)).mono (by simp)
  | cons x xs ih =>
    have ih' : Does θ (Fm.ofTree pickB.code) (.cons pickB.code (listT xs)) (xs.map fun x => (1, x)) (20 * xs.length + 10) := by
      rw [Fm.ofTree_code]; exact ih
    have r := Does.run (Gives.id (θ := θ) (.cons pickB.code (listT (x :: xs)))).hd
      (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl) ih'
    refine (Does.ite_true (Gives.id _).tl (by simp [listT]) (Does.either (Gives.id _).tl.hd r)).mono ?_
    simp only [List.length_cons]
    omega

theorem pickF_does {l : Fm} {x : Tree} {cl : ℕ} {xs : List Tree} (hl : Gives θ l x (listT xs) cl) :
    Does θ (pickF l) x (xs.map fun x => (1, x)) (cl + 20 * xs.length + 20) := by
  have h1 := Gives.cons (Gives.quote (θ := θ) pickB.code x) hl
  have h2 := Does.app (p := pickB.code) (R := fun _ => xs.map fun x => ((1 : A), x)) h1 (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [Fm.ofTree_code]
    exact pickB_does xs)
  refine (h2.congr ?_ fun φ => ?_).mono (by omega)
  · intro p hp
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
    exact ⟨r, hr, h3.symm⟩
  · rw [wsum_bindW]
    simp [wsum]

end Choice

section Tries

/-- Tries: (value, (left, right)); the empty tree is the empty trie. -/
def tget : List Bool → Tree → Tree
  | [], t => t.hd
  | true :: p, t => tget p t.tl.tl
  | false :: p, t => tget p t.tl.hd

/-- Write a value. -/
def tset : List Bool → Tree → Tree → Tree
  | [], v, t => .cons v t.tl
  | true :: p, v, t => .cons t.hd (.cons t.tl.hd (tset p v t.tl.tl))
  | false :: p, v, t => .cons t.hd (.cons (tset p v t.tl.hd) t.tl.tl)

theorem tget_nil (p : List Bool) : tget p .nil = .nil := by
  induction p with
  | nil => rfl
  | cons b p ih => cases b <;> exact ih

theorem tget_tset (p p' : List Bool) (v t : Tree) : tget p (tset p' v t) = if p = p' then v else tget p t := by
  induction p' generalizing p t with
  | nil =>
    cases p with
    | nil => rfl
    | cons b p => cases b <;> simp [tset, tget]
  | cons b' p' ih =>
    cases p with
    | nil => cases b' <;> simp [tset, tget]
    | cons b p =>
      cases b <;> cases b' <;> simp [tset, tget, ih]

/-- Read a value. The argument is (this program, (path, trie)). -/
def getB : Fm := .ite (.hd (.tl .id))
  (.ite (.hd (.hd (.tl .id)))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl (.tl (.tl .id)))))))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.hd (.tl (.tl (.tl .id))))))))
  (.hd (.tl (.tl .id)))

/-- Read a value: `p` gives the path, `t` the trie. -/
def getF (p t : Fm) : Fm := app getB.code (.cons (.quote getB.code) (.cons p t))

theorem getB_gives (p : Tree) (t : Tree) :
    Gives θ getB (.cons getB.code (.cons p t)) (tget p.path t) (30 * p.len + 10) := by
  induction p generalizing t with
  | nil => exact ((Gives.id _).tl.hd.ite_false (Gives.id _).tl.tl.hd).mono (by simp [len])
  | cons a p _ ih =>
    by_cases ha : a = .nil
    · subst ha
      have h1 : Gives θ (Fm.ofTree getB.code) (.cons getB.code (.cons p t.tl.hd)) (tget p.path t.tl.hd)
          (30 * p.len + 10) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons getB.code (.cons (.cons .nil p) t))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.id _).tl.tl.tl.hd)) h1
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_false (Gives.id _).tl.hd.hd r)).mono ?_
      simp only [len]
      omega
    · have h1 : Gives θ (Fm.ofTree getB.code) (.cons getB.code (.cons p t.tl.tl)) (tget p.path t.tl.tl)
          (30 * p.len + 10) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons getB.code (.cons (.cons a p) t))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.id _).tl.tl.tl.tl)) h1
      have e : tget (Tree.cons a p).path t = tget p.path t.tl.tl := by simp [path, ha, tget]
      rw [e]
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_true (Gives.id _).tl.hd.hd (by simpa using ha) r)).mono ?_
      simp only [len]
      omega

theorem getF_gives {pf tf : Fm} {x p t : Tree} {cp ct : ℕ} (hp : Gives θ pf x p cp) (ht : Gives θ tf x t ct) :
    Gives θ (getF pf tf) x (tget p.path t) (cp + ct + 30 * p.len + 20) := by
  refine (Gives.app (p := getB.code) (Gives.cons (Gives.quote _ _) (Gives.cons hp ht)) (by
    rw [Fm.ofTree_code]
    exact getB_gives p t)).mono (by omega)

/-- Write a value. The argument is (this program, (path, (value, trie))). -/
def setB : Fm := .ite (.hd (.tl .id))
  (.ite (.hd (.hd (.tl .id)))
    (.cons (.hd (.tl (.tl (.tl .id)))) (.cons (.hd (.tl (.tl (.tl (.tl .id)))))
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.cons (.hd (.tl (.tl .id)))
        (.tl (.tl (.tl (.tl (.tl .id)))))))))))
    (.cons (.hd (.tl (.tl (.tl .id)))) (.cons
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.cons (.hd (.tl (.tl .id)))
        (.hd (.tl (.tl (.tl (.tl .id)))))))))
      (.tl (.tl (.tl (.tl (.tl .id))))))))
  (.cons (.hd (.tl (.tl .id))) (.tl (.tl (.tl (.tl .id)))))

/-- Write a value: `p` gives the path, `v` the value, `t` the trie. -/
def setF (p v t : Fm) : Fm := app setB.code (.cons (.quote setB.code) (.cons p (.cons v t)))

theorem setB_gives (p v t : Tree) :
    Gives θ setB (.cons setB.code (.cons p (.cons v t))) (tset p.path v t) (60 * p.len + 20) := by
  induction p generalizing t with
  | nil =>
    exact ((Gives.id _).tl.hd.ite_false (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.tl.tl.tl)).mono (by simp [len])
  | cons a p _ ih =>
    by_cases ha : a = .nil
    · subst ha
      have h1 : Gives θ (Fm.ofTree setB.code) (.cons setB.code (.cons p (.cons v t.tl.hd))) (tset p.path v t.tl.hd)
          (60 * p.len + 20) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons setB.code (.cons (.cons .nil p) (.cons v t)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.cons (Gives.id _).tl.tl.hd
          (Gives.id _).tl.tl.tl.tl.hd))) h1
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_false (Gives.id _).tl.hd.hd
        (Gives.cons (Gives.id _).tl.tl.tl.hd (Gives.cons r (Gives.id _).tl.tl.tl.tl.tl)))).mono ?_
      simp only [len]
      omega
    · have h1 : Gives θ (Fm.ofTree setB.code) (.cons setB.code (.cons p (.cons v t.tl.tl))) (tset p.path v t.tl.tl)
          (60 * p.len + 20) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons setB.code (.cons (.cons a p) (.cons v t)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.cons (Gives.id _).tl.tl.hd
          (Gives.id _).tl.tl.tl.tl.tl))) h1
      have e : tset (Tree.cons a p).path v t = .cons t.hd (.cons t.tl.hd (tset p.path v t.tl.tl)) := by
        simp [path, ha, tset]
      rw [e]
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_true (Gives.id _).tl.hd.hd (by simpa using ha)
        (Gives.cons (Gives.id _).tl.tl.tl.hd (Gives.cons (Gives.id _).tl.tl.tl.tl.hd r)))).mono ?_
      simp only [len]
      omega

theorem setF_gives {pf vf tf : Fm} {x p v t : Tree} {cp cv ct : ℕ} (hp : Gives θ pf x p cp) (hv : Gives θ vf x v cv)
    (ht : Gives θ tf x t ct) : Gives θ (setF pf vf tf) x (tset p.path v t) (cp + cv + ct + 60 * p.len + 30) := by
  refine (Gives.app (p := setB.code) (Gives.cons (Gives.quote _ _) (Gives.cons hp (Gives.cons hv ht))) (by
    rw [Fm.ofTree_code]
    exact setB_gives p v t)).mono (by omega)

end Tries

section Weights

/-- Formulas for elements of `A`. -/
inductive WE where
  /-- 0 -/
  | zero
  /-- 1 -/
  | one
  /-- a named constant -/
  | nm (p : List Bool)
  /-- sum -/
  | add (a b : WE)
  /-- product -/
  | mul (a b : WE)

/-- The value. -/
def WE.val (θ : List Bool → A) : WE → A
  | zero => 0
  | one => 1
  | nm p => θ p
  | add a b => a.val θ + b.val θ
  | mul a b => a.val θ * b.val θ

/-- The formula of the machine. -/
def WE.fm : WE → Fm
  | zero => .fail
  | one => .quote .nil
  | nm p => .theta (.quote (ofBits p))
  | add a b => .ite .guess a.fm b.fm
  | mul a b => lett a.fm (lett b.fm (.quote .nil))

/-- The cost. -/
def WE.cost : WE → ℕ
  | zero => 1
  | one => 1
  | nm _ => 2
  | add a b => max a.cost b.cost + 2
  | mul a b => a.cost + b.cost + 10

/-- Multiply the weight by an element of `A`. -/
theorem WE.does (e : WE) (x : Tree) : Does θ e.fm x [(e.val θ, .nil)] e.cost := by
  induction e generalizing x with
  | zero =>
    refine ((Does.fail x).congr (by simp) fun φ => ?_).mono (Nat.zero_le _)
    simp [WE.val]
  | one => exact Gives.quote .nil x
  | nm p =>
    have := Does.theta (Gives.quote (θ := θ) (ofBits p) x)
    rwa [path_ofBits] at this
  | add a b iha ihb =>
    refine (Does.either (iha x) (ihb x)).congr ?_ fun φ => ?_
    · intro q hq
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl
    · simp [WE.val, add_mul]
  | mul a b iha ihb =>
    have h1 := Does.lett (R := fun _ => [(b.val θ, .nil)]) (G := lett b.fm (.quote .nil)) (iha x)
      (d := b.cost + 1 + 2) (by
        intro q hq
        have := Does.lett (R := fun _ => [((1 : A), Tree.nil)]) (G := .quote .nil) (ihb q.2) (d := 1)
          fun p _ => Gives.quote .nil p.2
        simpa [bindW] using this)
    refine (h1.congr ?_ fun φ => ?_).mono ?_
    · intro q hq
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [bindW, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
        List.mem_singleton] at hq
      subst hq
      rfl
    · simp [bindW, WE.val]
    · simp only [WE.cost]
      omega

/-- Every element of the subring generated by the constants has a formula, if −1 is a constant. -/
theorem WE.exists_of_adjoin {p₀ : List Bool} (h : θ p₀ = -1) {a : A} (ha : a ∈ Subring.closure (Set.range θ)) :
    ∃ e : WE, e.val θ = a := by
  induction ha using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨.nm p, rfl⟩
  | zero => exact ⟨.zero, rfl⟩
  | one => exact ⟨.one, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨f, rfl⟩ := hy
    exact ⟨.add e f, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨f, rfl⟩ := hy
    exact ⟨.mul e f, rfl⟩
  | neg x _ hx =>
    obtain ⟨e, rfl⟩ := hx
    exact ⟨.mul (.nm p₀) e, by simp [WE.val, h]⟩

end Weights

end NS1
