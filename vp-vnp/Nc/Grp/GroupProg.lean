/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Pack

/-!
# The program GROUP
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

section unary

/-- Unary from binary (most significant bit first). -/
def unF (b : Fm) : Fm := foldF (.ite (.hd .id) (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (appF (.tl .id) (.tl .id)))
  (.quote .nil) b

theorem le_foldl_bval (w : List Bool) (a : ℕ) : a ≤ w.foldl (fun a b => 2 * a + b.toNat) a := by
  induction w generalizing a with
  | nil => exact le_rfl
  | cons b w ih => exact le_trans (by omega) (ih (2 * a + b.toNat))

theorem unStep_gives (b : Bool) (a v : ℕ) (ha : a ≤ v) :
    Gives θ (.ite (.hd .id) (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (appF (.tl .id) (.tl .id)))
      (.cons (bit b) (num a)) (num (2 * a + b.toNat)) (v * 62 + 90) := by
  have e1 : Gives θ (.tl .id) (.cons (bit b) (num a)) (ofBits (List.replicate a false)) 2 := by
    rw [← num_eq_ofBits]
    exact (Gives.id _).tl
  have e2 := appB_gives e1 e1
  rw [← List.replicate_add, ← num_eq_ofBits, List.length_replicate, ← two_mul] at e2
  cases b with
  | false => exact (Gives.ite_false (Gives.id _).hd e2).mono (by omega)
  | true =>
    have e3 : Gives θ (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (.cons (bit true) (num a)) (num (2 * a + 1))
        (v * 62 + 80) := (Gives.cons (Gives.quote .nil _) e2).mono (by omega)
    exact (Gives.ite_true (Gives.id _).hd (by simp [bit, one]) e3).mono (by omega)

theorem unF_gives {b : Fm} {x : Tree} {w : List Bool} {c : ℕ} (h : Gives θ b x (ofBits w) c) :
    Gives θ (unF b) x (num (bval w)) (c + w.length * (bval w * 62 + 130) + 30) := by
  have hl : Gives θ b x (listT (w.map bit)) c := by
    rw [listT_ofBits]
    exact h
  have h1 := foldTG (θ := θ) (encE := bit) (xs := w) (enc := num) (s₀ := 0) (g := fun b a => 2 * a + b.toNat)
    (Inv := fun ys a => ys.foldl (fun a b => 2 * a + b.toNat) a = bval w) (d := fun _ => bval w * 62 + 90)
    (step := .ite (.hd .id) (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (appF (.tl .id) (.tl .id)))
    (s := .quote .nil) (Gives.quote _ _) hl (fun b ys a _ hinv => ⟨unStep_gives b a _ (by
      rw [← hinv]
      exact le_trans (by omega) (le_foldl_bval ys (2 * a + b.toNat))), hinv⟩) rfl
  refine h1.mono ?_
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  ring_nf
  omega

end unary

section group

variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : G.Law A, L.Ro))

/-- The separator. -/
def sepOf : List Bool := List.ofFn (cb none)

variable (θ) in
/-- What an instruction does with a trie. -/
noncomputable def insSem (T ub : ℕ) : Ins → Tree → List (A × Tree)
  | .block q q' B, t => if h : q < Fintype.card Q ∧ q' < Fintype.card Q then
      bindL (simSem θ mu cb T ⟨q, h.1⟩ ⟨q', h.2⟩) fun o => packSem A (sepOf cb) ub B o t else []
  | .input part B, t => packSem A (sepOf cb) ub B (inOuts (S := S) part) t
  | .both k k', t => if tget k t = tget k' t then [(1, t)] else []
  | .one k w, t => if tget k t = ofBits w then [(1, t)] else []
  | .role j tt slots keys, t => match kinds[j]? with
    | some z => roleSem θ z.1 z.2 ub (fun k => (tget k t).path) tt slots keys t
    | none => []

/-- Conditions on an instruction. -/
def InsOk (S Q : Type) [Fintype S] [DecidableEq S] [Fintype Q] (c : ℕ) (kinds : List (Σ L : G.Law A, L.Ro)) : Ins → Prop
  | .block q q' _ => q < Fintype.card Q ∧ q' < Fintype.card Q
  | .input part _ => ∀ a ∈ part, a.length ≤ c
  | .both _ _ => True
  | .one _ _ => True
  | .role j _ slots _ => ∃ z, kinds[j]? = some z ∧ slots.length = (slList z.1 z.2).length

/-- Costs of the body of an instruction. -/
def bodyCost (ub : ℕ) (B : Body) : ℕ := flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1

/-- Costs of an instruction. -/
def insCost (T ub : ℕ) : Ins → ℕ
  | .block _ _ B => T + bodyCost ub B
  | .input part B => part.length + bodyCost ub B
  | .both k k' => k.length + k'.length + ub + 1
  | .one k w => k.length + w.length + ub + 1
  | .role _ tt slots keys => tt * (ub + 1) + putCost ub slots + putCost ub keys + 1

/-- All contents are lists of at most `ub` bits. -/
def TOk (ub : ℕ) (t : Tree) : Prop := ∀ k, ∃ w : List Bool, tget k t = ofBits w ∧ w.length ≤ ub

theorem TOk.path {ub : ℕ} {t : Tree} (h : TOk ub t) (k : List Bool) : tget k t = ofBits (tget k t).path ∧
    (tget k t).path.length ≤ ub := by
  obtain ⟨w, h1, h2⟩ := h k
  rw [h1, path_ofBits]
  exact ⟨rfl, h2⟩

theorem tOk_nil (ub : ℕ) : TOk ub .nil := fun k => ⟨[], by rw [tget_nil]; rfl, Nat.zero_le _⟩

theorem TOk.tset {ub : ℕ} {t : Tree} (h : TOk ub t) (k w : List Bool) (hw : w.length ≤ ub) :
    TOk ub (tset k (ofBits w) t) := by
  intro k'
  rw [tget_tset]
  split_ifs
  · exact ⟨w, rfl, hw⟩
  · exact h k'

theorem TOk.putL {ub : ℕ} {keys : List (List Bool)} {r : List Bool} {t : Tree} (h : TOk ub t) :
    ∀ t' ∈ putL ub keys r t, TOk ub t' := by
  induction keys generalizing r t with
  | nil =>
    intro t' ht'
    rw [Grp.putL] at ht'
    split_ifs at ht'
    · rw [List.mem_singleton] at ht'
      exact ht' ▸ h
    · simp at ht'
  | cons k ks ih =>
    intro t' ht'
    rw [Grp.putL] at ht'
    split_ifs at ht'
    · simp at ht'
    · exact ih (h.tset k _ (length_padTake _ _).le) t' ht'

theorem TOk.putsL {ub : ℕ} {kss : List (List (List Bool))} {strs : List (List Bool)} {t : Tree} (h : TOk ub t) :
    ∀ t' ∈ putsL ub kss strs t, TOk ub t' := by
  induction kss generalizing strs t with
  | nil =>
    intro t' ht'
    rw [Grp.putsL, List.mem_singleton] at ht'
    exact ht' ▸ h
  | cons ks kss ih =>
    intro t' ht'
    rw [Grp.putsL, List.mem_flatMap] at ht'
    obtain ⟨t1, h1, h2⟩ := ht'
    exact ih (h.putL t1 h1) t' h2

theorem mem_encT {l : List Tree} {q : A × Tree} (h : q ∈ encT (A := A) l) : q.2 ∈ l := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact ht

theorem TOk.pack {sep : List Bool} {ub : ℕ} {B : Body} {o : Outs S} {t : Tree} (h : TOk ub t) :
    ∀ q ∈ packSem A sep ub B o t, TOk ub q.2 := by
  intro q hq
  obtain ⟨a, -, r, hr, e1⟩ := mem_bindL hq
  obtain ⟨b, hb, r', hr', e2⟩ := mem_bindL hr
  obtain ⟨d, -, r'', hr'', e3⟩ := mem_bindL hr'
  rw [e1, e2, e3]
  exact (h.putsL _ (mem_encT hb)).putsL _ (mem_encT hr'')

theorem TOk.insSem {T ub : ℕ} {i : Ins} {t : Tree} (h : TOk ub t) :
    ∀ q ∈ insSem θ mu cb kinds T ub i t, TOk ub q.2 := by
  intro q hq
  cases i with
  | block q₁ q₂ B =>
    rw [Grp.insSem] at hq
    split_ifs at hq
    · obtain ⟨a, -, r, hr, e1⟩ := mem_bindL hq
      rw [e1]
      exact h.pack r hr
    · simp at hq
  | input part B => exact h.pack q hq
  | both k k' =>
    rw [Grp.insSem] at hq
    split_ifs at hq
    · rw [List.mem_singleton] at hq
      exact hq ▸ h
    · simp at hq
  | one k w =>
    rw [Grp.insSem] at hq
    split_ifs at hq
    · rw [List.mem_singleton] at hq
      exact hq ▸ h
    · simp at hq
  | role j tt slots keys =>
    rw [Grp.insSem] at hq
    split at hq
    · unfold roleSem at hq
      split_ifs at hq
      · obtain ⟨a, -, r, hr, e1⟩ := mem_bindL hq
        rw [e1]
        exact h.putsL _ (mem_encT hr)
      · simp at hq
    · simp at hq

/-- The state of GROUP. -/
def encG (T ub : ℕ) (t : Tree) : Tree := .cons (num T) (.cons (num ub) t)

/-- The programs of all roles. -/
theorem ex_kinds : ∃ (Fs : List Fm) (κ : ℕ), ∀ (j : ℕ) (z : Σ L : G.Law A, L.Ro), kinds[j]? = some z →
    ∃ F, Fs[j]? = some F ∧ ∀ (ub tt : ℕ) (slots keys : List (List (List Bool))) (t : Tree), TOk ub t →
      slots.length = (slList z.1 z.2).length →
      Does θ F (.cons (num ub) (.cons t (.cons (num tt) (.cons (keysT slots) (keysT keys)))))
        (roleSem θ z.1 z.2 ub (fun k => (tget k t).path) tt slots keys t)
        (κ * (tt * (ub + 1) + putCost ub slots + putCost ub keys + 1)) := by
  induction kinds with
  | nil => exact ⟨[], 0, fun j z h => by simp at h⟩
  | cons z₀ kinds ih =>
    obtain ⟨Fs, κ, h⟩ := ih
    obtain ⟨F, κ', h'⟩ := ex_role (θ := θ) z₀.1 z₀.2
    refine ⟨F :: Fs, max κ (2 * κ'), fun j z hj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      refine ⟨F, rfl, fun ub tt slots keys t ht hs => ?_⟩
      refine (h' ub (fun k => (tget k t).path) tt slots keys t (fun k => (ht.path k).1) (fun k => (ht.path k).2) hs).mono ?_
      have h1 : (slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum ≤ 2 * putCost ub slots := by
        unfold putCost
        rw [← List.sum_map_mul_left]
        refine List.sum_le_sum fun es _ => ?_
        have : (es.map fun k => ub * 62 + k.length * 60 + 330).sum ≤ (es.map fun k => ub * 90 + k.length * 60 + 330).sum :=
          List.sum_le_sum fun k _ => by omega
        omega
      change κ' * (_ + _ + putCost ub keys + 1) ≤ _
      refine le_trans ?_ (Nat.mul_le_mul_right _ (le_max_right κ (2 * κ')))
      rw [mul_comm 2 κ', mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      obtain ⟨F', h1, h2⟩ := h j z hj
      exact ⟨F', by simpa using h1, fun ub tt slots keys t ht hs => (h2 ub tt slots keys t ht hs).mono
        (Nat.mul_le_mul_right _ (le_max_left _ _))⟩

/-- **One instruction.** -/
theorem ex_ins (hc : (sepOf cb).length ≤ c) : ∃ F κ, ∀ (T ub : ℕ) (i : Ins) (t : Tree), InsOk S Q c kinds i → TOk ub t →
    Does θ F (.cons i.tree (encG T ub t)) ((insSem (S := S) θ mu cb kinds T ub i t).map (Prod.map id (encG T ub)))
      (κ * insCost T ub i) := by
  obtain ⟨Fs, κs, hFs⟩ := ex_sim (θ := θ) mu cb
  obtain ⟨κl, hκl⟩ := exists_simSem_length (θ := θ) mu cb
  obtain ⟨Fp, κp, hFp⟩ := ex_pack (A := A) (θ := θ) (S := S) (sepOf cb) c hc
  obtain ⟨Fi, κi, hFi⟩ := ex_inOuts (θ := θ) (S := S)
  obtain ⟨Fk, κk, hFk⟩ := ex_kinds (θ := θ) kinds
  -- the formulas
  set fBlock : Fm := lett (.cons .id (lett (.cons (.hd (.tl .id)) (.hd (.tl (.hd .id)))) Fs))
    (lett (.cons (.tl .id) (.cons (.hd (.tl (.tl (.hd .id)))) (.cons (.tl (.tl (.tl (.hd .id))))
      (.tl (.tl (.hd (.hd .id))))))) Fp) with hBlock
  set fInput : Fm := lett (.cons (Fi (.hd (.tl (.hd .id)))) (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id)))
      (.tl (.tl (.hd .id)))))) Fp with hInput
  set fBoth : Fm := .ite (eqF (getF (.hd (.tl (.hd .id))) (.tl (.tl (.tl .id)))) (getF (.tl (.tl (.hd .id)))
      (.tl (.tl (.tl .id))))) (.tl (.tl (.tl .id))) .fail with hBoth
  set fOne : Fm := .ite (eqF (getF (.hd (.tl (.hd .id))) (.tl (.tl (.tl .id)))) (.tl (.tl (.hd .id))))
      (.tl (.tl (.tl .id))) .fail with hOne
  set fs : List Fm := fBlock :: fInput :: fBoth :: fOne :: Fk.map fun G =>
    lett (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id))) (.tl (.hd .id)))) G with hfs
  set sw : ℕ := (kinds.length + 5) * (kinds.length + 10) with hsw
  refine ⟨.cons (.hd (.tl .id)) (.cons (.hd (.tl (.tl .id))) (switchF (.hd (.hd .id)) fs)),
    κs + κp * (κl + 2) + κi * 10 + κk + sw + 2000, fun T ub i t hi ht => ?_⟩
  set x : Tree := .cons i.tree (encG T ub t) with hx
  have gT : Gives θ (.hd (.tl .id)) x (num T) 3 := (Gives.id _).tl.hd
  have gU : Gives θ (.hd (.tl (.tl .id))) x (num ub) 4 := (Gives.id _).tl.tl.hd
  have gt : Gives θ (.tl (.tl (.tl .id))) x t 4 := (Gives.id _).tl.tl.tl
  have gpos : 1 ≤ insCost T ub i := by
    cases i <;> simp only [insCost, bodyCost] <;> omega
  -- it is enough to make the trie
  suffices h : Does θ (switchF (.hd (.hd .id)) fs) x (insSem (S := S) θ mu cb kinds T ub i t)
      ((κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * insCost T ub i) by
    refine ((Does.cons gT (Does.cons gU h)).replace ?_).mono ?_
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, one_mul]
      rfl
    · have : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 2000) * insCost T ub i =
        (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * insCost T ub i + 100 * insCost T ub i := by ring
      omega
  cases i with
  | block q q' B =>
    obtain ⟨hq, hq'⟩ := hi
    have g0 : Gives θ (.hd (.hd .id)) x (num 0) 3 := (Gives.id _).hd.hd
    have e1 : Gives θ (.cons (.hd (.tl .id)) (.hd (.tl (.hd .id)))) x (.cons (num T) (.cons (num q) (num q'))) 8 :=
      (Gives.cons gT (Gives.id _).hd.tl.hd).mono (by omega)
    have e2 := Does.of_gives e1 (hFs T ⟨q, hq⟩ ⟨q', hq'⟩)
    have e3 := Does.letkT (G := lett (.cons (.tl .id) (.cons (.hd (.tl (.tl (.hd .id)))) (.cons (.tl (.tl (.tl (.hd .id))))
        (.tl (.tl (.hd (.hd .id))))))) Fp) (f := fun o => packSem A (sepOf cb) ub B o t)
      (d := 30 + κp * (κl * T + flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1) + 2) e2 (by
        intro b hb
        obtain ⟨h1, h2⟩ := hκl T ⟨q, hq⟩ ⟨q', hq'⟩ b hb
        have e4 : Gives θ (.cons (.tl .id) (.cons (.hd (.tl (.tl (.hd .id)))) (.cons (.tl (.tl (.tl (.hd .id))))
            (.tl (.tl (.hd (.hd .id))))))) (.cons x (encO b.2)) (.cons (encO b.2) (.cons (num ub) (.cons t B.tree))) 30 :=
          (Gives.cons (Gives.id _).tl (Gives.cons (Gives.id _).hd.tl.tl.hd (Gives.cons (Gives.id _).hd.tl.tl.tl
            (Gives.id _).hd.hd.tl.tl))).mono (by omega)
        exact Does.of_gives e4 (hFp ub B b.2 t (κl * T) h1 h2))
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fBlock) rfl e3
    refine (e5.replace ?_).mono ?_
    · rw [insSem, dif_pos ⟨hq, hq'⟩]
    · simp only [insCost, bodyCost]
      set N := flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1 with hN
      have h1 : κp * (κl * T + flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1) ≤
          κp * ((κl + 2) * (T + N)) := by
        refine Nat.mul_le_mul_left _ ?_
        have : (κl + 2) * (T + N) = κl * T + κl * N + 2 * T + 2 * N := by ring
        rw [this]
        omega
      have h2 : κs * (T + 1) ≤ κs * (T + N) := Nat.mul_le_mul_left _ (by omega)
      have h3 : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * (T + N) = κs * (T + N) + κp * ((κl + 2) * (T + N)) +
        κi * 10 * (T + N) + κk * (T + N) + sw * (T + N) + 1900 * (T + N) := by ring
      have h4 : 1 ≤ T + N := by omega
      omega
  | input part B =>
    have g0 : Gives θ (.hd (.hd .id)) x (num 1) 3 := (Gives.id _).hd.hd
    have e1 := hFi (.hd (.tl (.hd .id))) x part 4 (Gives.id _).hd.tl.hd
    have e2 := Gives.cons e1 (Gives.cons gU (Gives.cons gt (Gives.id (θ := θ) x).hd.tl.tl))
    have e3 := hFp ub B (inOuts (S := S) part) t part.length (fun j => by
        unfold inOuts
        split_ifs
        · exact le_rfl
        · simp) (fun j a ha => by
        unfold inOuts at ha
        split_ifs at ha
        · exact hi a ha
        · simp at ha)
    have e4 := Does.of_gives e2 e3
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fInput) rfl e4
    refine e5.mono ?_
    simp only [insCost, bodyCost]
    set N := flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1 with hN
    have h1 : κp * (part.length + flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1) ≤
        κp * ((κl + 2) * (part.length + N)) := by
      refine Nat.mul_le_mul_left _ ?_
      have : (κl + 2) * (part.length + N) = κl * (part.length + N) + 2 * part.length + 2 * N := by ring
      rw [this]
      omega
    have h3 : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * (part.length + N) = κs * (part.length + N) +
      κp * ((κl + 2) * (part.length + N)) + κi * 10 * (part.length + N) + κk * (part.length + N) +
      sw * (part.length + N) + 1900 * (part.length + N) := by ring
    have h4 : 1 ≤ part.length + N := by omega
    have h5 : κi * (4 + 1) ≤ κi * 10 * (part.length + N) := by nlinarith
    omega
  | both k k' =>
    have g0 : Gives θ (.hd (.hd .id)) x (num 2) 3 := (Gives.id _).hd.hd
    have e1 := getF_gives (θ := θ) (x := x) (pf := .hd (.tl (.hd .id))) (p := ofBits k) (Gives.id _).hd.tl.hd gt
    have e2 := getF_gives (θ := θ) (x := x) (pf := .tl (.tl (.hd .id))) (p := ofBits k') (Gives.id _).hd.tl.tl gt
    have e3 := eqF_gives e1 e2
    rw [path_ofBits, path_ofBits, len_ofBits, len_ofBits] at e3
    have h1 : (tget k t).size ≤ 4 * ub + 1 := by
      obtain ⟨a1, a2⟩ := ht.path k
      rw [a1]
      exact (size_ofBits _).trans (by omega)
    have h2 : Does θ fBoth x (insSem (S := S) θ mu cb kinds T ub (.both k k') t) (300 * insCost T ub (.both k k')) := by
      simp only [insSem, insCost]
      by_cases h : tget k t = tget k' t
      · rw [if_pos h]
        have e4 : bit (decide (tget k t = tget k' t)) ≠ .nil := by simp [h, bit, one]
        exact (Does.ite_true e3 e4 gt).mono (by omega)
      · rw [if_neg h]
        have e4 : bit (decide (tget k t = tget k' t)) = .nil := by simp [h, bit]
        rw [e4] at e3
        exact (Does.ite_false e3 (Does.fail _)).mono (by omega)
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fBoth) rfl h2
    refine e5.mono ?_
    have h3 : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * insCost T ub (.both k k') =
      κs * insCost T ub (.both k k') + κp * (κl + 2) * insCost T ub (.both k k') + κi * 10 * insCost T ub (.both k k') +
      κk * insCost T ub (.both k k') + sw * insCost T ub (.both k k') + 1900 * insCost T ub (.both k k') := by ring
    omega
  | one k w =>
    have g0 : Gives θ (.hd (.hd .id)) x (num 3) 3 := (Gives.id _).hd.hd
    have e1 := getF_gives (θ := θ) (x := x) (pf := .hd (.tl (.hd .id))) (p := ofBits k) (Gives.id _).hd.tl.hd gt
    have e3 := eqF_gives e1 (Gives.id (θ := θ) x).hd.tl.tl
    rw [path_ofBits, len_ofBits] at e3
    have h1 : (tget k t).size ≤ 4 * ub + 1 := by
      obtain ⟨a1, a2⟩ := ht.path k
      rw [a1]
      exact (size_ofBits _).trans (by omega)
    have h2 : Does θ fOne x (insSem (S := S) θ mu cb kinds T ub (.one k w) t) (300 * insCost T ub (.one k w)) := by
      simp only [insSem, insCost]
      by_cases h : tget k t = ofBits w
      · rw [if_pos h]
        have e4 : bit (decide (tget k t = x.hd.tl.tl)) ≠ .nil := by
          have : tget k t = x.hd.tl.tl := h
          simp [this, bit, one]
        exact (Does.ite_true e3 e4 gt).mono (by omega)
      · rw [if_neg h]
        have e4 : bit (decide (tget k t = x.hd.tl.tl)) = .nil := by
          have : ¬ tget k t = x.hd.tl.tl := h
          simp [this, bit]
        rw [e4] at e3
        exact (Does.ite_false e3 (Does.fail _)).mono (by omega)
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fOne) rfl h2
    refine e5.mono ?_
    have h3 : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * insCost T ub (.one k w) =
      κs * insCost T ub (.one k w) + κp * (κl + 2) * insCost T ub (.one k w) + κi * 10 * insCost T ub (.one k w) +
      κk * insCost T ub (.one k w) + sw * insCost T ub (.one k w) + 1900 * insCost T ub (.one k w) := by ring
    omega
  | role j tt slots keys =>
    obtain ⟨z, hz, hsl⟩ := hi
    obtain ⟨G, hG, hG'⟩ := hFk j z hz
    have hj : j < kinds.length := by
      by_contra h
      rw [List.getElem?_eq_none (not_lt.1 h)] at hz
      simp at hz
    have g0 : Gives θ (.hd (.hd .id)) x (num (4 + j)) 3 := (Gives.id _).hd.hd
    have e1 := Gives.cons gU (Gives.cons gt (Gives.id (θ := θ) x).hd.tl)
    have e2 := Does.of_gives e1 (hG' ub tt slots keys t ht hsl)
    have hf : fs[4 + j]? = some (lett (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id))) (.tl (.hd .id)))) G) := by
      rw [hfs, add_comm]
      simp [hG]
    have e5 := switchF_does (θ := θ) g0 (fs := fs) hf e2
    refine (e5.replace ?_).mono ?_
    · rw [insSem, hz]
    · simp only [insCost]
      set N := tt * (ub + 1) + putCost ub slots + putCost ub keys + 1 with hN
      have h1 : (4 + j + 1) * (3 + (4 + j) + 1) ≤ sw * N := by
        have h2 : (4 + j + 1) * (3 + (4 + j) + 1) ≤ sw := Nat.mul_le_mul (by omega) (by omega)
        have h3 : 1 ≤ N := by omega
        nlinarith
      have h3 : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * N = κs * N + κp * (κl + 2) * N + κi * 10 * N + κk * N +
        sw * N + 1900 * N := by ring
      have h4 : 1 ≤ N := by omega
      omega

variable (θ) in
/-- What a script does with a trie. -/
noncomputable def scriptSem (T ub : ℕ) (l : List Ins) (t : Tree) : List (A × Tree) :=
  foldL (insSem (S := S) θ mu cb kinds T ub) l t

/-- **The program GROUP.** -/
theorem ex_group (hc : (sepOf cb).length ≤ c) : ∃ F κ, ∀ (bT bub : List Bool) (l : List Ins),
    (∀ i ∈ l, InsOk S Q c kinds i) →
    Does θ F (scriptT bT bub l) ((scriptSem (S := S) θ mu cb kinds (bval bT) (bval bub) l .nil).map
      (Prod.map id (encG (bval bT) (bval bub))))
      (κ * ((bT.length + 1) * (bval bT + 1) + (bub.length + 1) * (bval bub + 1) +
        (l.map (insCost (bval bT) (bval bub))).sum + l.length)) := by
  obtain ⟨F, κ, hF⟩ := ex_ins (θ := θ) mu cb kinds hc
  refine ⟨foldF F (.cons (unF (.hd (.hd .id))) (.cons (unF (.tl (.hd .id))) (.quote .nil))) (.tl .id), κ + 300,
    fun bT bub l hl => ?_⟩
  have g1 : Gives θ (.hd (.hd .id)) (scriptT bT bub l) (ofBits bT) 3 := (Gives.id _).hd.hd
  have g2 : Gives θ (.tl (.hd .id)) (scriptT bT bub l) (ofBits bub) 3 := (Gives.id _).hd.tl
  have h0 := Gives.cons (unF_gives g1) (Gives.cons (unF_gives g2) (Gives.quote .nil (scriptT bT bub l)))
  have h1 := foldT (θ := θ) (A := A) (encE := Ins.tree) (xs := l) (enc := encG (bval bT) (bval bub)) (s₀ := .nil)
    (f := insSem (S := S) θ mu cb kinds (bval bT) (bval bub)) (Inv := fun _ t => TOk (bval bub) t)
    (d := fun i => κ * insCost (bval bT) (bval bub) i) (step := F) (l := .tl .id) (x := scriptT bT bub l) h0
    (Gives.id _).tl (fun i _ t hi ht => ⟨hF _ _ i t (hl i hi) ht, fun q hq => ht.insSem mu cb kinds q hq⟩) (tOk_nil _)
  refine h1.mono ?_
  have h2 : ∀ l : List Ins, (l.map fun i => κ * insCost (bval bT) (bval bub) i + 30).sum =
      κ * (l.map (insCost (bval bT) (bval bub))).sum + 30 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      ring
  rw [h2]
  set P := (bT.length + 1) * (bval bT + 1) with hP
  set R := (bub.length + 1) * (bval bub + 1) with hR
  set Sm := (l.map (insCost (bval bT) (bval bub))).sum
  have p1 : bT.length * (bval bT * 62 + 130) ≤ 130 * P := by rw [hP]; nlinarith
  have p2 : bub.length * (bval bub * 62 + 130) ≤ 130 * R := by rw [hR]; nlinarith
  have p3 : 1 ≤ P := Nat.succ_le_of_lt (by positivity)
  have p4 : (κ + 300) * (P + R + Sm + l.length) = κ * (P + R + l.length) + κ * Sm + 300 * (P + R + Sm + l.length) := by ring
  omega

end group

end Nc.Grp
