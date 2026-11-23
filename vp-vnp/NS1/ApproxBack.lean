/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.ApproxExtract
import Nc.Acc.Main

/-!
# An approximate accelerator gives an exact one

The program that reads the coefficient of ε^0 out of an approximate accelerator, its constants and its size.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree LaurentPolynomial

variable {A : Type} [CommRing A] {θ : List Bool → A} {E : Type} [CommRing E] [Algebra A E]

/-- Runs that give values with weights, then a formula at the values. -/
theorem KV.app_rel {R : Type} [CommRing R] [Algebra A R] {κ : List Bool → R} {S : Set (List Bool)} {β : Type*}
    {F e : Fm} {x : Tree} {le : List (Run A)} {Q : List β} {c : β → R} {o : β → Tree} {w : β → R} {ce d : ℕ}
    (he : Ev θ e x le)
    (rel : List.Forall₂ (fun r q => wt κ r = c q ∧ r.out = o q ∧ (∀ p ∈ r.bill, p ∈ S) ∧ r.cost ≤ ce) le Q)
    (hF : ∀ q ∈ Q, KV θ κ S F (o q) (w q) d) :
    KV θ κ S (NS1.app F.code e) x (Q.map fun q => c q * w q).sum (ce + d + 2) := by
  have eU := Ev.app (p := F.code) he fun s hs => by
    obtain ⟨q, hq, -, h, -⟩ := forall₂_exists rel hs
    rw [Fm.ofTree_code, h]
    exact (hF q hq).hl
  refine ⟨_, eU, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, h1, h2, -, -⟩ := mem_app hu
    obtain ⟨q, hq, -, h4, h5, h6⟩ := forall₂_exists rel hs
    rw [Fm.ofTree_code, h4] at ht
    obtain ⟨c1, c2⟩ := (hF q hq).evl.1 t ht
    refine ⟨by omega, fun p hp => ?_⟩
    rw [h2, List.mem_append] at hp
    exact hp.elim (h5 p) (c2 p)
  · rw [val_eq_sumF, sumF_app, sum_rel (c := c) (o := o) (rel.imp fun r q hr => ⟨hr.1, hr.2.1⟩)]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    rw [Fm.ofTree_code, ← val_eq_sumF, (hF q hq).evl.2]

/-- Accept only with the counter at 0; then run the plain instance. The argument is (argument, (budgets, counter)). -/
def finF (P : Tree) : Fm := .cons (.run (.quote AZ.code) (.cons (.quote AZ.code) (.cons (.quote .nil) (.tl (.tl .id)))))
  (app UF.code (.cons (.quote WF.code) (.cons (.quote P) (.cons (.hd .id) (.hd (.tl .id))))))

theorem finF_kv {κ : List Bool → E} {S : Set (List Bool)} {P z : Tree} {t : Bt} {o : List Bool} {l : List (Run A)}
    {T H : ℕ} (hP : Ev θ (Fm.ofTree P) z l) (hT : ∀ r ∈ l, r.cost ≤ T) (ht : t.ht ≤ H) :
    KV θ κ S (finF P) (.cons z (.cons t.enc (ofBits o)))
      ((if KT.val o = 0 then 1 else 0) * algebraMap A E (l.map fun r => if ok t r.bill = true then r.th else 0).sum)
      (40 * (o.length + 1) + MM H * T + 40 * t.nds + 90) := by
  obtain ⟨pl, pe, -⟩ := zq_plain hP hT ht (τ := MM H * T + 40 * t.nds + 40) le_rfl
  obtain ⟨k, hk, u, hu⟩ := AZ_ev (θ := θ) (.leaf o)
  obtain ⟨x, hx⟩ : ∃ x, x = Tree.cons z (.cons t.enc (ofBits o)) := ⟨_, rfl⟩
  rw [← hx]
  have hu' : Ev θ (Fm.ofTree AZ.code) (.cons AZ.code (.cons .nil (ofBits o)))
      (if (Bt.leaf o).zero then [.det k u] else []) := by
    rw [Fm.ofTree_code]
    exact hu
  have eA := Ev.run_det (Dt.quote (θ := θ) AZ.code x) (Dt.cons (Dt.quote AZ.code x) (Dt.cons (Dt.quote .nil x)
    (Dt.tl (Dt.tl (Dt.id x))))) (by rw [hx]; simpa using hu')
  have k1 : KV θ κ S (.run (.quote AZ.code) (.cons (.quote AZ.code) (.cons (.quote .nil) (.tl (.tl .id))))) x
      (if KT.val o = 0 then 1 else 0) (40 * (o.length + 1) + 20) := by
    refine ⟨_, eA, ?_, ?_⟩
    · intro r hr
      simp only [Bt.nds] at hk
      by_cases hz : (Bt.leaf o).zero
      · simp only [hz, if_true, List.map_cons, List.map_nil, List.mem_singleton] at hr
        subst hr
        refine ⟨?_, by simp [Run.delay, Run.det]⟩
        simp only [Run.delay, Run.det]
        omega
      · simp [hz] at hr
    · have e : (Bt.leaf o).zero = true ↔ KT.val o = 0 := by rw [Bt.zero]; exact all_not_iff o
      by_cases hz : KT.val o = 0
      · simp [e.2 hz, hz, val, wt, Run.delay, Run.det]
      · simp [Bool.eq_false_iff.2 (fun h => hz (e.1 h)), hz, val]
  have k2 : KV θ κ S UF (zq P z t) (algebraMap A E (l.map fun r => if ok t r.bill = true then r.th else 0).sum)
      (MM H * T + 40 * t.nds + 45) := by
    refine ⟨_, UF_ev pl.1.ev, ?_, ?_⟩
    · intro r hr
      rw [List.mem_map] at hr
      obtain ⟨s, hs, rfl⟩ := hr
      obtain ⟨b1, b2⟩ := pl.2 s hs
      refine ⟨?_, by simp [Run.delay, b1]⟩
      simp only [Run.delay]
      omega
    · rw [← pe, pv, val_plain]
      · simp [pval, Function.comp_def, Run.delay]
      · intro r hr
        rw [List.mem_map] at hr
        obtain ⟨s, hs, rfl⟩ := hr
        exact (pl.2 s hs).1
  have g : Gives θ (.cons (.quote WF.code) (.cons (.quote P) (.cons (.hd .id) (.hd (.tl .id))))) x (zq P z t) 12 := by
    subst hx
    exact (Gives.cons (Gives.quote _ _) (Gives.cons (Gives.quote _ _)
      (Gives.cons (Gives.id _).hd (Gives.id _).tl.hd))).mono (by norm_num)
  exact (KV.cons k1 (KV.app_gives (p := UF.code) g (by rw [Fm.ofTree_code]; exact k2))).mono (by omega)

theorem nds_coefK (J m : ℕ) (K : KT E[T;T⁻¹]) : (coefK J m K).nds ≤ K.nds * 2 ^ (J + m + 1) := by
  induction K with
  | none => simpa [coefK, KT.nds] using Nat.one_le_two_pow
  | leaf c =>
    have := KT.nds_full (J + m) fun w => termCoef (c ^ KT.val (w.take J)) (KT.val (w.drop J))
    simp only [coefK, KT.nds]
    omega
  | node l r ihl ihr =>
    simp only [coefK, KT.nds]
    have := Nat.one_le_two_pow (n := J + m + 1)
    have : (l.nds + r.nds + 1) * 2 ^ (J + m + 1) = l.nds * 2 ^ (J + m + 1) + r.nds * 2 ^ (J + m + 1) + 2 ^ (J + m + 1) := by
      ring
    omega

theorem ht_coefK (J m : ℕ) (K : KT E[T;T⁻¹]) : (coefK J m K).ht ≤ K.ht + J + m := by
  induction K with
  | none => simp [coefK, KT.ht]
  | leaf c => simp [coefK, KT.ht, KT.ht_full]
  | node l r ihl ihr =>
    simp only [coefK, KT.ht]
    omega

/-- The program of the extraction: guess with `g`, then check the counter and run the plain instance. -/
def extF (P : Tree) (g : Fm) : Fm := app (finF P).code (.cons .id g)

/-- **The value of the extraction.** -/
theorem extF_kv {κ : List Bool → E} {S : Set (List Bool)} {P z : Tree} {g : Fm} {cg T H n W : ℕ}
    {lg l : List (Run A)} {Q : List (Bt × E × List Bool)} (hg : Ev θ g z lg) (rg : List.Forall₂ (RelX κ S cg) lg Q)
    (hP : Ev θ (Fm.ofTree P) z l) (hT : ∀ r ∈ l, r.cost ≤ T)
    (hQ : ∀ q ∈ Q, q.1.ht ≤ H ∧ q.1.nds ≤ n ∧ q.2.2.length = W) :
    KV θ κ S (extF P g) z (Q.map fun q => q.2.1 * ((if KT.val q.2.2 = 0 then 1 else 0) *
      algebraMap A E (l.map fun r => if ok q.1 r.bill = true then r.th else 0).sum)).sum
      (cg + 40 * (W + 1) + MM H * T + 40 * n + 110) := by
  have ec := Ev.cons (Dt.id (θ := θ) z) hg
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at ec
  refine (KV.app_rel (F := finF P) (Q := Q) (c := fun q => q.2.1)
    (o := fun q => .cons z (.cons q.1.enc (ofBits q.2.2))) ec (ce := cg + 2)
    ?_ (d := 40 * (W + 1) + MM H * T + 40 * n + 90) fun q hq => ?_).mono (by omega)
  · rw [List.forall₂_map_left_iff]
    refine rg.imp fun r q hr => ⟨?_, ?_, ?_, ?_⟩
    · rw [wt_tick, wt_seq, wt_det, one_mul, wt, hr.th, hr.bill, map_one, one_mul]
    · simp [Run.tick, Run.det, hr.out]
    · simpa [Run.seq, Run.tick, Run.det] using hr.names
    · have := hr.cost
      simp only [Run.seq, Run.tick, Run.det]
      omega
  · obtain ⟨q1, q2, q3⟩ := hQ q hq
    refine (finF_kv hP hT q1).mono ?_
    rw [q3]
    omega

/-- The sizes of the fixed programs of the extraction. -/
def xcst : ℕ := combF.code.size + 2 * AZ.code.size + UF.code.size + WF.code.size + 1000

theorem xcst_def : xcst = combF.code.size + 2 * AZ.code.size + UF.code.size + WF.code.size + 1000 := rfl

theorem size_chT {n C : ℕ} {f : List Bool → Fm} (h : ∀ w : List Bool, w.length = n → (f w).code.size ≤ C) :
    (chT n f).code.size + 31 ≤ 2 ^ n * (C + 31) := by
  induction n generalizing f with
  | zero => simpa [chT] using h [] rfl
  | succ n ih =>
    have h1 := ih (f := fun w => f (true :: w)) fun w hw => h _ (by simp [hw])
    have h2 := ih (f := fun w => f (false :: w)) fun w hw => h _ (by simp [hw])
    rw [chT, size_ite, size_guess, pow_succ]
    have : 2 ^ n * 2 * (C + 31) = 2 ^ n * (C + 31) + 2 ^ n * (C + 31) := by ring
    omega

theorem size_xF (J m W : ℕ) (K : KT E[T;T⁻¹]) (pre : List Bool) :
    (xF J m W K pre).code.size ≤ K.nds * (2 ^ (J + m) * (4 * (pre.length + K.ht) + 8 * (J + m + W) + xcst + 31)) := by
  induction K generalizing pre with
  | none =>
    have h2 := size_ofBits (List.replicate W false)
    rw [List.length_replicate] at h2
    rw [KT.nds, one_mul]
    refine le_trans ?_ (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
    rw [xcst_def]
    simp only [xF, size_quote, Bt.enc, Tree.size, KT.ht]
    omega
  | leaf c =>
    have h := size_chT (n := J + m) (C := 4 * (pre.length + KT.ht (KT.leaf c)) + 8 * (J + m + W) + xcst)
      (f := fun w => .ite (.mul (.quote (ofBits (pre ++ (w ++ [false]))))) .fail
      (.quote (.cons (Bt.leaf (w.take J)).enc (ofBits (expBits W (termExp (c ^ KT.val (w.take J)) (KT.val (w.drop J))))))))
      fun w hw => by
        have h1 := size_ofBits (pre ++ (w ++ [false]))
        have h2 := size_ofBits (w.take J)
        have h3 := size_ofBits (expBits W (termExp (c ^ KT.val (w.take J)) (KT.val (w.drop J))))
        rw [length_expBits] at h3
        have h4 : (w.take J).length ≤ J := List.length_take_le _ _
        simp only [List.length_append, List.length_singleton, hw] at h1
        rw [xcst_def, size_ite, size_mul, size_quote, size_quote]
        simp only [Fm.code, Bt.enc, Tree.size, size_num, KT.ht]
        omega
    rw [KT.nds, one_mul]
    exact (Nat.le_add_right _ 31).trans h
  | node l r ihl ihr =>
    have h1 := ihl (pre ++ [false])
    have h2 := ihr (pre ++ [true])
    simp only [List.length_append, List.length_singleton] at h1 h2
    obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ (J + m) * (4 * (pre.length + KT.ht (KT.node l r)) + 8 * (J + m + W) + xcst + 31) :=
      ⟨_, rfl⟩
    have e1 := h1.trans (Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ (by simp only [KT.ht]; omega)).trans_eq hP.symm :
      2 ^ (J + m) * (4 * (pre.length + 1 + l.ht) + 8 * (J + m + W) + xcst + 31) ≤ P))
    have e2 := h2.trans (Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ (by simp only [KT.ht]; omega)).trans_eq hP.symm :
      2 ^ (J + m) * (4 * (pre.length + 1 + r.ht) + 8 * (J + m + W) + xcst + 31) ≤ P))
    have e3 : combF.code.size + 28 ≤ P := by
      rw [hP]
      refine le_trans ?_ (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
      rw [xcst_def]
      omega
    rw [← hP, KT.nds, xF, size_lett, size_cons]
    have : (l.nds + r.nds + 1) * P = l.nds * P + r.nds * P + P := by ring
    omega

set_option maxHeartbeats 1000000 in
theorem size_extF (P : Tree) (g : Fm) : (extF P g).code.size ≤ P.size + g.code.size + xcst := by
  rw [xcst_def, extF, finF]
  simp only [size_quote, size_cons, size_hd, size_tl, size_id, size_run, size_app, Tree.size]
  omega

end NS1
