/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Eval

/-!
# The interpreter is right
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem Run.seq_assoc (r s t : Run A) : (r.seq s).seq t = r.seq (s.seq t) := by
  simp [Run.seq, add_assoc, mul_assoc, List.append_assoc]

theorem Fm.ofTree_cases (f : Tree) :
    (f.hd.len = 0 ∧ ofTree f = quote f.tl) ∨ (f.hd.len = 1 ∧ ofTree f = id) ∨
    (f.hd.len = 2 ∧ ofTree f = hd (ofTree f.tl)) ∨ (f.hd.len = 3 ∧ ofTree f = tl (ofTree f.tl)) ∨
    (f.hd.len = 4 ∧ ofTree f = cons (ofTree f.tl.hd) (ofTree f.tl.tl)) ∨
    (f.hd.len = 5 ∧ ofTree f = ite (ofTree f.tl.hd) (ofTree f.tl.tl.hd) (ofTree f.tl.tl.tl)) ∨
    (f.hd.len = 6 ∧ ofTree f = run (ofTree f.tl.hd) (ofTree f.tl.tl)) ∨
    (f.hd.len = 7 ∧ ofTree f = guess) ∨ ((f.hd.len = 8 ∨ 11 ≤ f.hd.len) ∧ ofTree f = fail) ∨
    (f.hd.len = 9 ∧ ofTree f = theta (ofTree f.tl)) ∨ (f.hd.len = 10 ∧ ofTree f = mul (ofTree f.tl)) := by
  cases f with
  | nil => left; exact ⟨rfl, by rw [ofTree]; rfl⟩
  | cons o a =>
    rw [ofTree]
    simp only [hd_cons, tl_cons]
    rcases hn : o.len with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp

/-- What the interpreter does in one run: `q` is a run of the formula and the budgets that are left. -/
structure RelJ (M j : ℕ) (r : Run A) (q : Run A × Bt) : Prop where
  th : r.th = q.1.th
  bill : r.bill = []
  out : r.out = .cons q.1.out q.2.enc
  cost : r.cost + j ≤ M * q.1.cost

/-- The bound for the overhead. -/
def MM (H : ℕ) : ℕ := 1000 + 100 * H

theorem IF_case {f x : Tree} {t : Bt} {c : Fm} (hc : caseL[f.hd.len]? = some c) {M : ℕ}
    {Q : List (Run A × Bt)} (h : ∃ l, Ev θ c (env f x t) l ∧ List.Forall₂ (RelJ M 300) l Q) :
    ∃ l', Ev θ IF (env f x t) l' ∧ List.Forall₂ (RelJ M 0) l' Q := by
  obtain ⟨l, hl, hQ⟩ := h
  obtain ⟨k', hk', h'⟩ := selF_ev (cs := caseL) (b := fO .id) (Dt.fO (Dt.id (θ := θ) (env f x t))) (l := l)
    (fun c' hc' => by
      rw [hc] at hc'
      obtain rfl := Option.some.inj hc'
      exact hl)
    (fun hlen => by
      rw [List.getElem?_eq_none hlen] at hc
      simp at hc)
  refine ⟨_, h', ?_⟩
  rw [List.forall₂_map_left_iff]
  have hk : k' ≤ 300 := hk'.trans (by simp [caseL])
  refine hQ.imp fun r q hr => ⟨hr.th, hr.bill, hr.out, ?_⟩
  have := hr.cost
  simp only [Run.delay]
  omega

/-- A call for a single value: `let r = IF(args)`. -/
theorem call0 {f x : Tree} {t : Bt} {M : ℕ} {l : List (Run A)}
    (h : ∃ l', Ev θ IF (env f.tl x t) l' ∧ List.Forall₂ (RelJ M 0) l' (simS t l)) {body : Fm}
    {Q2 : Run A × Bt → List (Run A × Bt)}
    (hb : ∀ q ∈ simS t l, ∃ l2, Ev θ body (.cons q.1.out q.2.enc) l2 ∧ List.Forall₂ (fun s p => s.bill = [] ∧
      q.1.th * s.th = p.1.th ∧ s.out = .cons p.1.out p.2.enc ∧ M * q.1.cost + s.cost + 400 ≤ M * p.1.cost) l2 (Q2 q)) :
    ∃ l', Ev θ (lett (rec' .id (fA .id) (fX .id) (fS .id)) body) (env f x t) l' ∧
      List.Forall₂ (RelJ M 300) l' ((simS t l).flatMap Q2) := by
  obtain ⟨l1, h1, h1'⟩ := h
  have e := rec_ev (Dt.id (env f x t)) (Dt.fA (Dt.id _)) (Dt.fX (Dt.id _)) (Dt.fS (Dt.id _)) h1
  refine lett_rel e (Q := simS t l) (R := fun s q => s.th = q.1.th ∧ s.bill = [] ∧ s.out = .cons q.1.out q.2.enc ∧
    s.cost ≤ M * q.1.cost + 30) ?_ ?_
  · rw [List.forall₂_map_left_iff]
    refine h1'.imp fun r q hr => ⟨hr.th, hr.bill, hr.out, ?_⟩
    have := hr.cost
    simp only [Run.delay]
    omega
  · rintro s - q hq ⟨e1, e2, e3, e4⟩
    obtain ⟨l2, h2, h2'⟩ := hb q hq
    rw [← e3] at h2
    refine ⟨l2, h2, h2'.imp fun u p hu => ?_⟩
    obtain ⟨f1, f2, f3, f4⟩ := hu
    refine ⟨?_, ?_, f3, ?_⟩
    · simp only [e1, f2]
    · simp only [e2, f1, List.append_nil]
    · simp only
      omega

theorem call1_rel {f x : Tree} {t : Bt} {M : ℕ} {l : List (Run A)}
    (h : ∃ l', Ev θ IF (env f.tl.hd x t) l' ∧ List.Forall₂ (RelJ M 0) l' (simS t l)) :
    ∃ l', Ev θ call1 (env f x t) l' ∧ List.Forall₂ (fun s q => s.th = q.1.th ∧ s.bill = [] ∧
      s.out = .cons (env f x t) (.cons q.1.out q.2.enc) ∧ s.cost ≤ M * q.1.cost + 30) l' (simS t l) := by
  obtain ⟨l1, h1, h1'⟩ := h
  have e := Ev.cons (Dt.id (θ := θ) (env f x t))
    (rec_ev (Dt.id (env f x t)) (.hd (Dt.fA (Dt.id _))) (Dt.fX (Dt.id _)) (Dt.fS (Dt.id _)) h1)
  refine ⟨_, e, ?_⟩
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff, List.forall₂_map_left_iff]
  refine h1'.imp fun r q hr => ⟨?_, ?_, ?_, ?_⟩
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.th]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.bill]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.out]
  · have := hr.cost
    simp only [Run.seq, Run.tick, Run.det, Run.delay]
    omega

theorem call2_rel {f x o : Tree} {t t1 : Bt} {M : ℕ} {l : List (Run A)}
    (h : ∃ l', Ev θ IF (env f.tl.tl x t1) l' ∧ List.Forall₂ (RelJ M 0) l' (simS t1 l)) :
    ∃ l', Ev θ call2 (.cons (env f x t) (.cons o t1.enc)) l' ∧ List.Forall₂ (fun s q => s.th = q.1.th ∧ s.bill = [] ∧
      s.out = .cons (.cons (env f x t) (.cons o t1.enc)) (.cons q.1.out q.2.enc) ∧ s.cost ≤ M * q.1.cost + 30) l'
      (simS t1 l) := by
  obtain ⟨l1, h1, h1'⟩ := h
  have hb : Dt θ (.hd .id) (.cons (env f x t) (.cons o t1.enc)) (env f x t) 2 := .hd (.id _)
  have e := Ev.cons (Dt.id (θ := θ) (.cons (env f x t) (.cons o t1.enc)))
    (rec_ev hb (.tl (Dt.fA hb)) (Dt.fX hb) (t := t1) (.tl (.tl (Dt.id _))) h1)
  refine ⟨_, e, ?_⟩
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff, List.forall₂_map_left_iff]
  refine h1'.imp fun r q hr => ⟨?_, ?_, ?_, ?_⟩
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.th]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.bill]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.out]
  · have := hr.cost
    simp only [Run.seq, Run.tick, Run.det, Run.delay]
    omega

theorem flatMap_single {α β : Type*} (l : List α) (g : α → β) : (l.flatMap fun a => [g a]) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- **The interpreter is right.** -/
theorem interp {H : ℕ} {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) :
    ∀ f, Fm.ofTree f = F → ∀ t : Bt, t.ht ≤ H →
      ∃ l', Ev θ IF (env f x t) l' ∧ List.Forall₂ (RelJ (MM H) 0) l' (simS t l) := by
  have hM : 1000 ≤ MM H := by unfold MM; omega
  induction h with
  | quote c x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := .cons (fA .id) (fS .id)) (by rw [h1]; rfl) ⟨_, Dt.cons (Dt.fA (Dt.id _)) (Dt.fS (Dt.id _)), ?_⟩
    simp only [simS, Run.det, List.filterMap_cons, Bt.decAll, Option.map_some, List.filterMap_nil]
    refine .cons ⟨rfl, rfl, rfl, ?_⟩ .nil
    simp only
    omega
  | id x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := .cons (fX .id) (fS .id)) (by rw [h1]; rfl) ⟨_, Dt.cons (Dt.fX (Dt.id _)) (Dt.fS (Dt.id _)), ?_⟩
    simp only [simS, Run.det, List.filterMap_cons, Bt.decAll, Option.map_some, List.filterMap_nil]
    refine .cons ⟨rfl, rfl, rfl, ?_⟩ .nil
    simp only
    omega
  | @hd a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    rw [simS_map (G := fun r => r.tick r.out.hd) (fun _ => rfl), ← flatMap_single]
    refine call0 (ih f.tl rfl t ht) fun q hq => ⟨_, Dt.cons (.hd (.hd (.id _))) (.tl (.id _)), ?_⟩
    refine .cons ⟨rfl, mul_one _, rfl, ?_⟩ .nil
    simp only [Run.tick, Run.det]
    nlinarith
  | @tl a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    rw [simS_map (G := fun r => r.tick r.out.tl) (fun _ => rfl), ← flatMap_single]
    refine call0 (ih f.tl rfl t ht) fun q hq => ⟨_, Dt.cons (.tl (.hd (.id _))) (.tl (.id _)), ?_⟩
    refine .cons ⟨rfl, mul_one _, rfl, ?_⟩ .nil
    simp only [Run.tick, Run.det]
    nlinarith
  | @cons a b x la lb ha hb iha ihb =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    obtain ⟨l1, e1, r1⟩ := call1_rel (iha f.tl.hd rfl t ht)
    rw [simS_flatMap (G := fun r s => (r.seq s).tick (.cons r.out s.out)) (fun _ _ => rfl)]
    refine lett_rel e1 r1 fun s _ q hq hs => ?_
    obtain ⟨s1, s2, s3, s4⟩ := hs
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    obtain ⟨l2, e2, r2⟩ := call2_rel (f := f) (o := q.1.out) (t := t) (ihb f.tl.tl rfl q.2 hqt)
    rw [← s3] at e2
    rw [← flatMap_single]
    refine lett_rel e2 r2 fun u _ p hp hu => ?_
    obtain ⟨u1, u2, u3, u4⟩ := hu
    rw [u3]
    refine ⟨_, Dt.cons (.cons (.hd (.tl (.hd (.id _)))) (.hd (.tl (.id _)))) (.tl (.tl (.id _))), .cons ⟨?_, ?_, rfl, ?_⟩ .nil⟩
    · simp [Run.det, Run.seq, Run.tick, s1, u1]
    · simp [Run.det, s2, u2]
    · simp only [Run.det, Run.seq, Run.tick]
      nlinarith
  | @ite a b c x la L ha hb hc iha ihb ihc =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    obtain ⟨l1, e1, r1⟩ := call1_rel (iha f.tl.hd rfl t ht)
    rw [simS_flatMap (G := fun r s => (r.seq s).tick s.out) (fun _ _ => rfl)]
    refine lett_rel e1 r1 fun s _ q hq hs => ?_
    obtain ⟨s1, s2, s3, s4⟩ := hs
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    have hy : Dt θ (.hd .id) s.out (env f x t) 2 := by rw [s3]; exact .hd (.id _)
    have hv : Dt θ (.hd (.tl .id)) s.out q.1.out 3 := by rw [s3]; exact .hd (.tl (.id _))
    have ht' : Dt θ (.tl (.tl .id)) s.out q.2.enc 3 := by rw [s3]; exact .tl (.tl (.id _))
    by_cases hq0 : q.1.out = .nil
    · obtain ⟨l2, e2, r2⟩ := ihc q.1 (mem_simS hq).1 hq0 f.tl.tl.tl rfl q.2 hqt
      refine ⟨_, Ev.ite_false (hq0 ▸ hv) (rec_ev hy (.tl (.tl (Dt.fA hy))) (Dt.fX hy) ht' e2), ?_⟩
      rw [List.forall₂_map_left_iff, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine r2.imp fun u p hu => ⟨?_, ?_, ?_, ?_⟩
      · simp [Run.delay, Run.seq, Run.tick, s1, hu.th]
      · simp [Run.delay, s2, hu.bill]
      · simp [Run.delay, Run.tick, hu.out]
      · have := hu.cost
        simp only [Run.delay, Run.seq, Run.tick]
        nlinarith
    · obtain ⟨l2, e2, r2⟩ := ihb q.1 (mem_simS hq).1 hq0 f.tl.tl.hd rfl q.2 hqt
      refine ⟨_, Ev.ite_true hv hq0 (rec_ev hy (.hd (.tl (Dt.fA hy))) (Dt.fX hy) ht' e2), ?_⟩
      rw [List.forall₂_map_left_iff, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine r2.imp fun u p hu => ⟨?_, ?_, ?_, ?_⟩
      · simp [Run.delay, Run.seq, Run.tick, s1, hu.th]
      · simp [Run.delay, s2, hu.bill]
      · simp [Run.delay, Run.tick, hu.out]
      · have := hu.cost
        simp only [Run.delay, Run.seq, Run.tick]
        nlinarith
  | @run a b x la lb L ha hb hL iha ihb ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    obtain ⟨l1, e1, r1⟩ := call1_rel (iha f.tl.hd rfl t ht)
    have hlist : (la.flatMap fun r => lb.flatMap fun s => (L r s).map fun t => ((r.seq s).seq t).tick t.out) =
        la.flatMap fun r => (lb.flatMap fun s => (L r s).map fun t => s.seq t).map fun u => (r.seq u).tick u.out := by
      refine List.flatMap_congr fun r _ => ?_
      rw [List.map_flatMap]
      refine List.flatMap_congr fun s _ => ?_
      rw [List.map_map]
      refine List.map_congr_left fun u _ => ?_
      simp only [Function.comp_apply, Run.seq_assoc]
      rfl
    rw [hlist, simS_flatMap (G := fun r s => (r.seq s).tick s.out) (fun _ _ => rfl)]
    refine lett_rel e1 r1 fun s _ q hq hs => ?_
    obtain ⟨s1, s2, s3, s4⟩ := hs
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    obtain ⟨l2, e2, r2⟩ := call2_rel (f := f) (o := q.1.out) (t := t) (ihb f.tl.tl rfl q.2 hqt)
    rw [← s3] at e2
    rw [simS_flatMap (G := fun r s => r.seq s) (fun _ _ => rfl), List.map_flatMap]
    refine lett_rel e2 r2 fun u _ p hp hu => ?_
    obtain ⟨u1, u2, u3, u4⟩ := hu
    have hpt : p.2.ht ≤ H := (Bt.ht_decAll (mem_simS hp).2).trans_le hqt
    obtain ⟨l3, e3, r3⟩ := ih q.1 (mem_simS hq).1 p.1 (mem_simS hp).1 q.1.out rfl p.2 hpt
    have hy : Dt θ (.hd (.hd .id)) u.out (env f x t) 3 := by rw [u3]; exact .hd (.hd (.id _))
    have hf' : Dt θ (.hd (.tl (.hd .id))) u.out q.1.out 4 := by rw [u3]; exact .hd (.tl (.hd (.id _)))
    have hx : Dt θ (.hd (.tl .id)) u.out p.1.out 3 := by rw [u3]; exact .hd (.tl (.id _))
    have ht' : Dt θ (.tl (.tl .id)) u.out p.2.enc 3 := by rw [u3]; exact .tl (.tl (.id _))
    refine ⟨_, rec_ev hy hf' hx ht' e3, ?_⟩
    rw [List.forall₂_map_left_iff, List.map_map, List.forall₂_map_right_iff]
    refine r3.imp fun v w hv => ⟨?_, ?_, ?_, ?_⟩
    · simp [Run.delay, Run.seq, Run.tick, s1, u1, hv.th]
    · simp [Run.delay, s2, u2, hv.bill]
    · simp [Run.delay, Run.seq, Run.tick, hv.out]
    · have := hv.cost
      simp only [Run.delay, Run.seq, Run.tick, Function.comp_apply]
      nlinarith
  | guess x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := .cons .guess (fS .id)) (by rw [h1]; rfl) ⟨_, Ev.cons (.guess _) (Dt.fS (Dt.id _)), ?_⟩
    simp only [simS, Run.det, List.filterMap_cons, Bt.decAll, Option.map_some, List.filterMap_nil]
    refine .cons ⟨?_, rfl, rfl, ?_⟩ (.cons ⟨?_, rfl, rfl, ?_⟩ .nil)
    · simp [Run.seq, Run.tick]
    · simp only [Run.seq, Run.tick]; omega
    · simp [Run.seq, Run.tick]
    · simp only [Run.seq, Run.tick]; omega
  | fail x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    obtain ⟨k', hk', h'⟩ := selF_ev (cs := caseL) (b := fO .id) (Dt.fO (Dt.id (θ := θ) (env f x t))) (l := [])
      (fun c' hc' => by
        rcases h1 with h1 | h1
        · rw [h1] at hc'
          obtain rfl := Option.some.inj hc'
          exact .fail _
        · rw [List.getElem?_eq_none (by simpa [caseL] using h1)] at hc'
          simp at hc')
      (fun _ => rfl)
    exact ⟨_, h', by simp [simS]⟩
  | @theta a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    rw [simS_map (G := fun r => ⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩) (fun _ => rfl), ← flatMap_single]
    refine call0 (ih f.tl rfl t ht) fun q hq => ⟨_, Ev.cons (Ev.theta (Dt.hd (.id _))) (Dt.tl (.id _)), ?_⟩
    refine .cons ⟨rfl, ?_, rfl, ?_⟩ .nil
    · simp [Run.seq, Run.tick, Run.det]
    · simp only [Run.seq, Run.tick, Run.det]
      nlinarith
  | @mul a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    have hlist : simS t (l.map fun r => (⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩ : Run A)) =
        (simS t l).flatMap fun q => ((Bt.dec q.1.out.path q.2).map fun t' =>
          ((⟨q.1.cost + 1, q.1.th, q.1.bill ++ [q.1.out.path], .nil⟩ : Run A), t')).toList := by
      clear ih h
      induction l with
      | nil => rfl
      | cons r l ih =>
        simp only [simS, List.map_cons, List.filterMap_cons, Bt.decAll_append] at ih ⊢
        cases hd : Bt.decAll r.bill t with
        | none =>
          simp only [Option.bind_none, Option.map_none]
          exact ih
        | some t1 =>
          simp only [Option.bind_some, Bt.decAll, Option.map_some, List.flatMap_cons]
          cases hd2 : Bt.dec r.out.path t1 with
          | none =>
            simp only [Option.bind_none, Option.map_none, Option.toList_none, List.nil_append]
            exact ih
          | some t2 =>
            simp only [Option.bind_some, Option.map_some, Option.toList_some, List.singleton_append]
            rw [ih]
    rw [hlist]
    refine call0 (ih f.tl rfl t ht) fun q hq => ?_
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    cases hd : Bt.dec q.1.out.path q.2 with
    | none =>
      refine ⟨_, Ev.cons_nil_right (Dt.quote _ _) (Ev.run_nil (.quote _ _) (.cons (.quote _ _) (.id _)) ?_), .nil⟩
      rw [Fm.ofTree_code]
      exact DC_none hd
    | some t2 =>
      obtain ⟨k, hk, hdc⟩ := DC_some (θ := θ) hd
      refine ⟨_, Dt.cons (.quote _ _) (.run (.quote _ _) (.cons (.quote _ _) (.id _)) (i := k) ?_), .cons ⟨rfl, ?_, rfl, ?_⟩ .nil⟩
      · rw [Fm.ofTree_code]
        exact hdc
      · simp [Run.det]
      · simp only [Run.det]
        have : 60 * q.2.ht + 420 ≤ MM H := by unfold MM; omega
        nlinarith

end NS1
