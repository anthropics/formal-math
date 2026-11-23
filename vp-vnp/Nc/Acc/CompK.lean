/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Util

/-!
# Values of formulas with named constants

`KV θ κ S F x w c`: all runs of the formula `F` at `x` stop; the accepting ones have cost at most `c` and use names of
constants in `S`; with the constants `κ` the sum of their weights is `w`.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- The value of a formula. -/
def KV (θ : List Bool → A) (κ : List Bool → R) (S : Set (List Bool)) (F : Fm) (x : Tree) (w : R) (c : ℕ) : Prop :=
  ∃ l, Ev θ F x l ∧ (∀ r ∈ l, r.cost ≤ c ∧ ∀ p ∈ r.bill, p ∈ S) ∧ val κ l = w

theorem wt_mul (κ : List Bool → R) {r s u : Run A} (h1 : u.th = r.th * s.th) (h2 : u.bill = r.bill ++ s.bill) :
    wt κ u = wt κ r * wt κ s := by
  rw [wt, wt, wt, h1, h2, map_mul, List.map_append, List.prod_append]
  ring

namespace KV

variable {κ : List Bool → R} {S : Set (List Bool)} {F G H : Fm} {x : Tree} {w w' : R} {c d : ℕ}

theorem mono (h : KV θ κ S F x w c) (hc : c ≤ d) : KV θ κ S F x w d := by
  obtain ⟨l, h1, h2, h3⟩ := h
  exact ⟨l, h1, fun r hr => ⟨(h2 r hr).1.trans hc, (h2 r hr).2⟩, h3⟩

theorem congr (h : KV θ κ S F x w c) (hw : w = w') : KV θ κ S F x w' c := hw ▸ h

theorem hl (h : KV θ κ S F x w c) : Hl θ F x := by
  obtain ⟨l, h1, -⟩ := h
  exact h1.hl

theorem evl (h : KV θ κ S F x w c) : (∀ r ∈ NS1.evl θ F x, r.cost ≤ c ∧ ∀ p ∈ r.bill, p ∈ S) ∧
    val κ (NS1.evl θ F x) = w := by
  obtain ⟨l, h1, h2, h3⟩ := h
  rw [h1.evl]
  exact ⟨h2, h3⟩

theorem of_does {Q : List (A × Tree)} (h : Does θ F x Q c) :
    KV θ κ S F x (algebraMap A R (Q.map Prod.fst).sum) c := by
  obtain ⟨l, h1, h2, h3⟩ := h
  refine ⟨l, h1, fun r hr => ⟨(h2 r hr).2.1, ?_⟩, ?_⟩
  · rw [(h2 r hr).1]
    simp
  · rw [val_plain fun r hr => (h2 r hr).1, pval]
    have := h3 fun _ => 1
    simp only [mul_one, wsum] at this
    rw [this]

theorem of_gives {o : Tree} (h : Gives θ F x o c) : KV θ κ S F x 1 c := (of_does h).congr (by simp)

theorem fail (x : Tree) : KV θ κ S .fail x 0 0 := ⟨[], .fail x, by simp, by simp [val]⟩

theorem mul {o : Tree} (h : Gives θ F x o c) (ho : o.path ∈ S) : KV θ κ S (.mul F) x (κ o.path) (c + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := h
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.mul e1, ?_, ?_⟩
  · intro u hu
    rw [List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    refine ⟨by simpa using a2, fun p hp => ?_⟩
    rw [a1, List.nil_append, List.mem_singleton] at hp
    rw [hp, hout r hr]
    exact ho
  · have h1 : (l.map fun r : Run A => (⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩ : Run A)).map (wt κ) =
        l.map fun r => algebraMap A R r.th * κ o.path := by
      rw [List.map_map]
      refine List.map_congr_left fun r hr => ?_
      simp [wt, (e2 r hr).1, hout r hr]
    rw [val, h1, List.sum_map_mul_right]
    have h2 := e3 fun _ => 1
    simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h2
    have h3 : (l.map fun r => algebraMap A R r.th).sum = 1 := by
      have h4 := congrArg (algebraMap A R) h2
      rw [map_list_sum, List.map_map, map_one] at h4
      exact h4
    rw [h3, one_mul]

theorem cons (hF : KV θ κ S F x w c) (hG : KV θ κ S G x w' d) : KV θ κ S (.cons F G) x (w * w') (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  refine ⟨_, Ev.cons e1 f1, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    refine ⟨?_, fun p hp => ?_⟩
    · have h1 := (e2 r hr).1
      have h2 := (f2 s hs).1
      simp only [Run.tick, Run.seq]
      omega
    · simp only [Run.tick, Run.seq, List.mem_append] at hp
      exact hp.elim ((e2 r hr).2 p) ((f2 s hs).2 p)
  · rw [val, sum_flatMap_map]
    have h1 : ∀ r : Run A, ((l'.map fun s => (r.seq s).tick (.cons r.out s.out)).map (wt κ)).sum = wt κ r * w' := by
      intro r
      rw [← f3, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun s _ => wt_mul κ rfl rfl
    simp only [h1]
    rw [List.sum_map_mul_right, ← e3]
    rfl

theorem ite_true {o : Tree} (hF : Gives θ F x o c) (ho : o ≠ .nil) (hG : KV θ κ S G x w d) :
    KV θ κ S (.ite F G H) x w (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r _ _ => f1) (fun r hr h => absurd ((hout r hr).symm.trans h) ho), ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2⟩ := f2 s hs
    refine ⟨?_, fun p hp => ?_⟩
    · simp only [Run.seq, Run.tick]
      omega
    · simp only [Run.tick, Run.seq, a1, List.nil_append] at hp
      exact b2 p hp
  · rw [val, sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map (wt κ)).sum = algebraMap A R r.th * w := by
      intro r hr
      rw [← f3, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s _ => ?_
      rw [Function.comp_apply, wt_mul κ (r := r) (s := s) rfl rfl, wt, (e2 r hr).1]
      simp
    rw [List.map_congr_left h1, List.sum_map_mul_right]
    have h2 := e3 fun _ => 1
    simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h2
    have h4 := congrArg (algebraMap A R) h2
    rw [map_list_sum, List.map_map, map_one] at h4
    have h3 : (l.map fun r => algebraMap A R r.th).sum = 1 := h4
    rw [h3, one_mul]

theorem ite_false (hF : Gives θ F x .nil c) (hH : KV θ κ S H x w d) : KV θ κ S (.ite F G H) x w (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hH
  have hout : ∀ r ∈ l, r.out = .nil := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r hr h => absurd (hout r hr) h) (fun r _ _ => f1), ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2⟩ := f2 s hs
    refine ⟨?_, fun p hp => ?_⟩
    · simp only [Run.seq, Run.tick]
      omega
    · simp only [Run.tick, Run.seq, a1, List.nil_append] at hp
      exact b2 p hp
  · rw [val, sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map (wt κ)).sum = algebraMap A R r.th * w := by
      intro r hr
      rw [← f3, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s _ => ?_
      rw [Function.comp_apply, wt_mul κ (r := r) (s := s) rfl rfl, wt, (e2 r hr).1]
      simp
    rw [List.map_congr_left h1, List.sum_map_mul_right]
    have h2 := e3 fun _ => 1
    simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h2
    have h4 := congrArg (algebraMap A R) h2
    rw [map_list_sum, List.map_map, map_one] at h4
    have h3 : (l.map fun r => algebraMap A R r.th).sum = 1 := h4
    rw [h3, one_mul]

theorem either (hG : KV θ κ S G x w c) (hH : KV θ κ S H x w' d) :
    KV θ κ S (.ite .guess G H) x (w + w') (max c d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hG
  obtain ⟨l', f1, f2, f3⟩ := hH
  refine ⟨_, Ev.ite (L := fun r => if r.out = .nil then l' else l) (Ev.guess x) (fun r _ h => by rw [if_neg h]; exact e1)
    (fun r _ h => by rw [if_pos h]; exact f1), ?_, ?_⟩
  · intro u hu
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_map, Run.det, Tree.one,
      if_true, reduceCtorEq, if_false] at hu
    rcases hu with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · obtain ⟨a1, a2⟩ := f2 s hs
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [Run.seq, Run.tick]
        omega
      · simp only [Run.seq, Run.tick, List.nil_append] at hp
        exact a2 p hp
    · obtain ⟨a1, a2⟩ := e2 s hs
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [Run.seq, Run.tick]
        omega
      · simp only [Run.seq, Run.tick, List.nil_append] at hp
        exact a2 p hp
  · rw [← e3, ← f3, val, val, val, add_comm]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.sum_append, List.map_map,
      Run.det, Tree.one, if_true, reduceCtorEq, if_false]
    congr 1
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick]
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick]

/-- A plain computation, then a value. -/
theorem app {p : Tree} {Q : List (A × Tree)} {ω : Tree → R} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, KV θ κ S (Fm.ofTree p) q.2 (ω q.2) d) :
    KV θ κ S (NS1.app p F) x (Q.map fun q => algebraMap A R q.1 * ω q.2).sum (c + d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  have hG' : ∀ s ∈ l, KV θ κ S (Fm.ofTree p) s.out (ω s.out) d := by
    intro s hs
    obtain ⟨-, -, q, hq, h⟩ := e2 s hs
    rw [← h]
    exact hG q hq
  refine ⟨_, Ev.app e1 fun s hs => (hG' s hs).hl, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, h1, h2, h3, -⟩ := mem_app hu
    obtain ⟨a1, a2, -⟩ := e2 s hs
    obtain ⟨b1, b2⟩ := (hG' s hs).evl.1 t ht
    refine ⟨by omega, fun p hp => ?_⟩
    rw [h2, a1, List.nil_append] at hp
    exact b2 p hp
  · rw [val, sum_flatMap_map]
    have h1 : ∀ s ∈ l, (((NS1.evl θ (Fm.ofTree p) s.out).map fun t => ((Run.det 1 p).seq s).seq t |>.tick t.out).map
        (wt κ)).sum = algebraMap A R s.th * ω s.out := by
      intro s hs
      rw [← (hG' s hs).evl.2, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick, Run.det, (e2 s hs).1, mul_assoc]
    rw [List.map_congr_left h1]
    -- functions with values in `R`
    have h2 : ∀ (L : List (Run A)) (P : List (A × Tree)),
        (∀ φ : Tree → A, (L.map fun r => r.th * φ r.out).sum = wsum P φ) →
        (L.map fun s => algebraMap A R s.th * ω s.out).sum = (P.map fun q => algebraMap A R q.1 * ω q.2).sum := by
      intro L P hLP
      classical
      let D : Finset Tree := (L.map Run.out).toFinset ∪ (P.map Prod.snd).toFinset
      have k1 : (L.map fun s => algebraMap A R s.th * ω s.out).sum =
          ∑ o ∈ D, algebraMap A R (L.map fun r => r.th * if r.out = o then 1 else 0).sum * ω o := by
        have : ∀ s ∈ L, algebraMap A R s.th * ω s.out =
            ∑ o ∈ D, algebraMap A R (s.th * if s.out = o then 1 else 0) * ω o := by
          intro s hs
          rw [Finset.sum_eq_single s.out]
          · simp
          · intro o _ ho
            rw [if_neg (Ne.symm ho), mul_zero, map_zero, zero_mul]
          · intro h
            exact absurd (Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map_of_mem hs))) h
        rw [List.map_congr_left this]
        clear this
        have : ∀ L : List (Run A), (L.map fun s => ∑ o ∈ D, algebraMap A R (s.th * if s.out = o then 1 else 0) * ω o).sum =
            ∑ o ∈ D, algebraMap A R (L.map fun r => r.th * if r.out = o then 1 else 0).sum * ω o := by
          intro L
          induction L with
          | nil => simp
          | cons s L ih =>
            rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun o _ => ?_
            rw [List.map_cons, List.sum_cons, map_add, add_mul]
        exact this L
      have k2 : (P.map fun q => algebraMap A R q.1 * ω q.2).sum =
          ∑ o ∈ D, algebraMap A R (P.map fun q => q.1 * if q.2 = o then 1 else 0).sum * ω o := by
        have : ∀ q ∈ P, algebraMap A R q.1 * ω q.2 =
            ∑ o ∈ D, algebraMap A R (q.1 * if q.2 = o then 1 else 0) * ω o := by
          intro q hq
          rw [Finset.sum_eq_single q.2]
          · simp
          · intro o _ ho
            rw [if_neg (Ne.symm ho), mul_zero, map_zero, zero_mul]
          · intro h
            exact absurd (Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map_of_mem hq))) h
        rw [List.map_congr_left this]
        clear this
        have : ∀ P : List (A × Tree), (P.map fun q => ∑ o ∈ D, algebraMap A R (q.1 * if q.2 = o then 1 else 0) * ω o).sum =
            ∑ o ∈ D, algebraMap A R (P.map fun q => q.1 * if q.2 = o then 1 else 0).sum * ω o := by
          intro P
          induction P with
          | nil => simp
          | cons s P ih =>
            rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun o _ => ?_
            rw [List.map_cons, List.sum_cons, map_add, add_mul]
        exact this P
      rw [k1, k2]
      refine Finset.sum_congr rfl fun o _ => ?_
      have := hLP fun t => if t = o then 1 else 0
      rw [this]
      rfl
    exact h2 l Q e3

theorem lett {Q : List (A × Tree)} {ω : Tree → R} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, KV θ κ S G q.2 (ω q.2) d) :
    KV θ κ S (NS1.lett F G) x (Q.map fun q => algebraMap A R q.1 * ω q.2).sum (c + d + 2) :=
  app (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)

theorem app_gives {p o : Tree} (hF : Gives θ F x o c) (hG : KV θ κ S (Fm.ofTree p) o w d) :
    KV θ κ S (NS1.app p F) x w (c + d + 2) :=
  (app (Q := [(1, o)]) (ω := fun _ => w) hF (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hG)).congr (by simp)

/-- Apply a program that is the value of a formula. -/
theorem run {p y : Tree} {e : ℕ} (hF : Gives θ F x p c) (hG : Gives θ G x y d)
    (h : KV θ κ S (Fm.ofTree p) y w e) : KV θ κ S (.run F G) x w (c + d + e + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have ho : ∀ r ∈ l, r.out = p := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  have ho' : ∀ r ∈ l', r.out = y := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := f2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  have one : ∀ {L : List (Run A)} {o : Tree}, (∀ φ : Tree → A, (L.map fun r => r.th * φ r.out).sum = wsum [(1, o)] φ) →
      (L.map fun r => algebraMap A R r.th).sum = 1 := by
    intro L o hL
    have h2 := hL fun _ => 1
    simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h2
    have h4 := congrArg (algebraMap A R) h2
    rw [map_list_sum, List.map_map, map_one] at h4
    exact h4
  refine ⟨_, Ev.run' e1 f1 fun r hr s hs => by rw [ho r hr, ho' s hs]; exact h.hl, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
    rw [ho r hr, ho' s hs] at ht
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, -⟩ := f2 s hs
    obtain ⟨c1, c2⟩ := h.evl.1 t ht
    refine ⟨?_, fun p hp => ?_⟩
    · simp only [Run.seq, Run.tick]
      omega
    · simp only [Run.seq, Run.tick, a1, b1, List.nil_append] at hp
      exact c2 p hp
  · rw [val, sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out).map (wt κ)).sum = algebraMap A R r.th * w := by
      intro r hr
      rw [sum_flatMap_map]
      have h2 : ∀ s ∈ l', (((NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
          ((r.seq s).seq t).tick t.out).map (wt κ)).sum = algebraMap A R s.th * (algebraMap A R r.th * w) := by
        intro s hs
        rw [ho r hr, ho' s hs, List.map_map, ← h.evl.2, val, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun t _ => ?_
        simp only [Function.comp_apply, wt, Run.seq, Run.tick, (e2 r hr).1, (f2 s hs).1, List.nil_append, map_mul]
        ring
      rw [List.map_congr_left h2, List.sum_map_mul_right, one f3, one_mul]
    rw [List.map_congr_left h1, List.sum_map_mul_right, one e3, one_mul]

end KV

end NS1
