/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Group
import Nc.Cut.Facts

/-!
# What an accepting run of GROUP tells

The numbers of units of the base parties and the outcomes of the moves are bounded if GROUP has an accepting run.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A B' : Type} [CommRing A] [CommRing B'] {θ : List Bool → A} {α β ε : Type}

theorem snd_bindL (l : List (A × α)) (f : α → List (A × β)) :
    (bindL l f).map Prod.snd = (l.map Prod.snd).flatMap fun a => (f a).map Prod.snd := by
  simp only [bindL, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

theorem snd_foldL {f : ε → β → List (A × β)} {f' : ε → β → List (B' × β)}
    (h : ∀ x s, (f x s).map Prod.snd = (f' x s).map Prod.snd) (xs : List ε) (s : β) :
    (foldL f xs s).map Prod.snd = (foldL f' xs s).map Prod.snd := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [foldL, foldL, snd_bindL, snd_bindL, h]
    exact List.flatMap_congr fun a _ => ih a

theorem snd_segsL (sep : List Bool) (items : List Item) (accs : List (List Bool)) :
    (segsL A sep items accs).map Prod.snd = (segsL B' sep items accs).map Prod.snd := by
  refine snd_foldL (fun it s => ?_) items accs
  simp [segOne]

variable {S : Type} [Fintype S] [DecidableEq S]

theorem snd_packSem (sep : List Bool) (ub : ℕ) (B : Body) (o : Outs S) (t : Tree) :
    (packSem A sep ub B o t).map Prod.snd = (packSem B' sep ub B o t).map Prod.snd := by
  simp only [packSem, snd_bindL, snd_segsL (A := A) (B' := B'), encT, List.map_map, Function.comp_def]

/-- All weights are 1. -/
def Ones (l : List (A × α)) : Prop := ∀ p ∈ l, p.1 = 1

theorem Ones.bindL {l : List (A × α)} {f : α → List (A × β)} (hl : Ones l) (hf : ∀ a, Ones (f a)) : Ones (bindL l f) := by
  intro p hp
  unfold Grp.bindL at hp
  obtain ⟨a, ha, hp⟩ := List.mem_flatMap.1 hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
  simp only [hl a ha, hf _ r hr, mul_one]

theorem ones_map (l : List α) (g : α → β) : Ones (l.map fun t => ((1 : A), g t)) := by
  intro p hp
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hp
  rfl

theorem Ones.foldL {f : ε → β → List (A × β)} (hf : ∀ x s, Ones (f x s)) (xs : List ε) (s : β) : Ones (foldL f xs s) := by
  induction xs generalizing s with
  | nil =>
    intro p hp
    rw [Grp.foldL, List.mem_singleton] at hp
    rw [hp]
  | cons x xs ih => exact Ones.bindL (hf x s) ih

theorem ones_packSem (sep : List Bool) (ub : ℕ) (B : Body) (o : Outs S) (t : Tree) : Ones (packSem A sep ub B o t) := by
  have hs : ∀ items accs, Ones (segsL A sep items accs) := fun items accs =>
    Ones.foldL (fun it s => ones_map _ _) items accs
  refine (hs _ _).bindL fun sR => (ones_map _ _).bindL fun t1 => (hs _ _).bindL fun sC => ones_map _ _

theorem sumL_ones {l : List (ℤ × α)} (h : Ones l) : sumL l (fun _ => 1) = l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [sumL_cons, ih fun q hq => h q (List.mem_cons_of_mem _ hq), h p List.mem_cons_self, List.length_cons]
    push_cast
    ring

theorem foldL_ne_nil {f : ε → β → List (A × β)} {xs : List ε} {s : β} (h : foldL f xs s ≠ []) :
    ∀ x ∈ xs, ∃ s', f x s' ≠ [] := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    intro y hy
    rw [foldL] at h
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨a, ha, r, hr, -⟩ := mem_bindL hp
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨s, List.ne_nil_of_mem ha⟩
    · exact ih (List.ne_nil_of_mem hr) y hy

variable {Γ Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T cap : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {dkey : Fin (K + K) × Fin U0 → List Bool} {tg : M.R → ℕ}

/-- What is simulated are the letters of a run. -/
theorem mem_runL_sim (k : ℕ) (s : TSt (Fintype.card Q) 0 (nT S + nT S) (List Bool)) :
    ∀ r ∈ runL θ (simTab θ mu cb) k s, ∃ w : List (Letter S Unit Γ), w.length = k ∧
      r.2.2.2 = fun j => w.reverse.flatMap (fun z => pushOf cb z j) ++ s.2.2 j := by
  induction k generalizing s with
  | zero =>
    intro r hr
    rw [runL, List.replicate_zero, foldL, List.mem_singleton] at hr
    subst hr
    exact ⟨[], rfl, rfl⟩
  | succ k ih =>
    intro r hr
    rw [runL, List.replicate_succ, foldL] at hr
    obtain ⟨a, ha, r', hr', e⟩ := mem_bindL hr
    obtain ⟨op, hop, rfl⟩ := List.mem_map.1 ha
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hop
    obtain ⟨w, hw, e'⟩ := ih _ r' hr'
    refine ⟨z.1 :: w, by rw [List.length_cons, hw], ?_⟩
    rw [e, e']
    funext j
    simp [Opt.app]

theorem mem_simSem {T : ℕ} {a b : Fin (Fintype.card Q)} {r : A × Outs S} (h : r ∈ simSem θ mu cb T a b) :
    ∃ w : List (Letter S Unit Γ), w.length = T ∧ r.2 = outsOf cb w := by
  obtain ⟨s, hs, z, hz, e⟩ := mem_bindL h
  obtain ⟨w, hw, e'⟩ := mem_runL_sim T _ s hs
  refine ⟨w, hw, ?_⟩
  split_ifs at hz
  · rw [List.mem_singleton] at hz
    rw [e, hz]
    simp only
    rw [e']
    funext j
    simp [outsOf]
  · simp at hz

/-- From a result of a base party. -/
theorem exists_of_pack (hub : 0 < ub) {p : Fin (K + K)}
    (hρ : ∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) {wl rl : Option S → List Γ}
    (hwl : ∀ s, (wl s).length ≤ T) (hrl : ∀ s, (rl s).length ≤ T) {out : Outs S}
    (h1 : ∀ i, out (Fin.castAdd (nT S) i) = ((wl ((tapes S).get i)).map (code cb)).reverse)
    (h2 : ∀ i, out (Fin.natAdd (nT S) i) = ((rl ((tapes S).get i)).map (code cb)).reverse) {t : Tree}
    (h : packSem A (sepOf cb) ub (bodyOf ρ n key dkey p) out t ≠ []) :
    ∃ R C : Option S → Fin (K + K) → List Γ, (∀ s, cat (R s) = wl s) ∧ (∀ s, cat (C s) = rl s) ∧
      (∀ b, ucount ub (strOf cb fun s => R s b) = n p b) ∧ ∀ b, ucount ub (strOf cb fun s => C s b) = n b p := by
  have hK : 0 < K + K := Nat.lt_of_le_of_lt (Nat.zero_le _) p.2
  have h3 : packSem ℤ (sepOf cb) ub (bodyOf ρ n key dkey p) out t ≠ [] := by
    intro h0
    have := snd_packSem (A := A) (B' := ℤ) (sepOf cb) ub (bodyOf ρ n key dkey p) out t
    rw [h0, List.map_nil, List.map_eq_nil_iff] at this
    exact h this
  have h4 := sumL_ones (ones_packSem (A := ℤ) (sepOf cb) ub (bodyOf ρ n key dkey p) out t)
  rw [sumL_pack hub hK hρ hwl hrl h1 h2] at h4
  have h5 : ((packSem ℤ (sepOf cb) ub (bodyOf ρ n key dkey p) out t).length : ℤ) ≠ 0 := by
    have := List.length_pos_iff.2 h3
    omega
  rw [← h4] at h5
  obtain ⟨R, -, hR⟩ := Finset.exists_ne_zero_of_sum_ne_zero h5
  obtain ⟨C, -, hC⟩ := Finset.exists_ne_zero_of_sum_ne_zero hR
  split_ifs at hC with hc
  · exact ⟨R.words, C.words, hc.1, hc.2.1, hc.2.2.2.1, hc.2.2.2.2⟩
  · exact absurd rfl hC

theorem sum_wr_le (w : List (Letter S Unit Γ)) : ∑ s, (wr w s).length ≤ w.length := by
  have h1 : ∑ z, (emit w z).length ≤ w.length := by
    unfold emit
    rw [sum_length_proj]
    exact List.reduceOption_length_le w
  refine le_trans ?_ h1
  rw [Fintype.sum_option]
  simp only [wr, List.length_nil, zero_add]
  rw [← Finset.sum_image (f := fun z : Ch S Unit => (emit w z).length) (s := univ) (g := fun s : S => .tp s false)]
  · exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · intro s _ s' _ e
    simpa using e

theorem sum_rdr_le (w : List (Letter S Unit Γ)) : ∑ s, (rdr w s).length ≤ w.length := by
  have h1 : ∑ z, (emit w z).length ≤ w.length := by
    unfold emit
    rw [sum_length_proj]
    exact List.reduceOption_length_le w
  refine le_trans ?_ h1
  let f : Option S → Ch S Unit := fun s => s.elim (.inp ()) fun s => .tp s true
  have hf : ∑ s, (rdr w s).length = ∑ s, (emit w (f s)).length := by
    refine Finset.sum_congr rfl fun s _ => ?_
    cases s <;> simp [f, rdr]
  have inj : Function.Injective f := by
    intro s s' e
    cases s <;> cases s' <;> simp [f] at e ⊢
    exact e
  rw [hf, ← Finset.sum_image (f := fun z : Ch S Unit => (emit w z).length) (s := univ) (g := f)
    fun s _ s' _ e => inj e]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **(i)** The numbers of units of the base parties of the group. -/
theorem count_of_accept (hub : 0 < ub) (hx : ∀ κ, (x κ).length ≤ T)
    (hρ : ∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) {b : G.Uid (K + K) U0 M.N U1 → UW ub} {t : Tree}
    (h : scriptSem (S := S) θ mu cb kinds T ub
      (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b) t ≠ []) {p : Fin (K + K)}
    (hp : grp (Fin.castAdd A' p) = g) :
    ∑ b, ((n p b : ℕ) + n b p) ≤ 2 * ((T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K)) := by
  have hmem : Fin.addCases (motive := fun _ => Ins)
      (fun κ => .block (qn Q (q κ.castSucc)) (qn Q (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
      (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p ∈
      script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, mem_baseList.2 hp, List.mem_cons_self⟩))
  obtain ⟨t', ht'⟩ := foldL_ne_nil h _ hmem
  have key1 : ∃ R C : Option S → Fin (K + K) → List Γ, ∑ s, (cat (R s)).length ≤ T ∧ ∑ s, (cat (C s)).length ≤ T ∧
      (∀ b, ucount ub (strOf cb fun s => R s b) = n p b) ∧ ∀ b, ucount ub (strOf cb fun s => C s b) = n b p := by
    revert ht'
    refine Fin.addCases (motive := fun p => insSem θ mu cb kinds T ub (Fin.addCases (motive := fun _ => Ins)
      (fun κ => .block (qn Q (q κ.castSucc)) (qn Q (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
      (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p) t' ≠ [] →
      ∃ R C : Option S → Fin (K + K) → List Γ, ∑ s, (cat (R s)).length ≤ T ∧ ∑ s, (cat (C s)).length ≤ T ∧
      (∀ b, ucount ub (strOf cb fun s => R s b) = n p b) ∧ ∀ b, ucount ub (strOf cb fun s => C s b) = n b p) ?_ ?_ p
    · intro κ ht'
      rw [Fin.addCases_left, insSem, dif_pos ⟨(qn Q _).2, (qn Q _).2⟩] at ht'
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ ht'
      obtain ⟨a, ha, r', hr', -⟩ := mem_bindL hr
      obtain ⟨w, hw, ew⟩ := mem_simSem ha
      rw [ew] at hr'
      obtain ⟨R, C, h1, h2, h3, h4⟩ := exists_of_pack (A := A) (T := T) hub (fun s => hρ s _) (wl := wr w) (rl := rdr w)
        (fun s => hw ▸ length_wr w s) (fun s => hw ▸ length_rdr w s) (outsOf_left cb w) (outsOf_right cb w)
        (List.ne_nil_of_mem hr')
      refine ⟨R, C, ?_, ?_, h3, h4⟩
      · simp only [h1]
        exact hw ▸ sum_wr_le w
      · simp only [h2]
        exact hw ▸ sum_rdr_le w
    · intro κ ht'
      rw [Fin.addCases_right, insSem] at ht'
      obtain ⟨R, C, h1, h2, h3, h4⟩ := exists_of_pack (A := A) (T := T) hub (fun s => hρ s _)
        (wl := fun s => if s = none then x κ else []) (rl := fun _ => [])
        (fun s => by split_ifs; exacts [hx κ, Nat.zero_le _]) (fun s => Nat.zero_le _)
        (fun i => inOuts_left cb (x κ) i) (fun i => inOuts_right cb (x κ) i) ht'
      refine ⟨R, C, ?_, ?_, h3, h4⟩
      · simp only [h1]
        rw [Fintype.sum_option]
        simpa using hx κ
      · simp only [h2]
        simp
  obtain ⟨R, C, h1, h2, h3, h4⟩ := key1
  have e1 : ∑ b, (n p b : ℕ) ≤ (T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K) := by
    rw [Finset.sum_congr rfl fun b _ => (h3 b).symm]
    exact sum_ucount_le h1
  have e2 : ∑ b, (n b p : ℕ) ≤ (T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K) := by
    rw [Finset.sum_congr rfl fun b _ => (h4 b).symm]
    exact sum_ucount_le h2
  rw [Finset.sum_add_distrib]
  omega

/-- The output lists of the transducer of a role. -/
theorem mem_runL_roleTab (L : G.Law A) (p : L.Ro) (B : ℕ) (s : TSt 1 (slList L p).length (cnList L p).length Bool) :
    ∀ r ∈ runL θ (roleTab θ L p) B s, ∃ f : Fin B → Bk L p,
      ∀ j, r.2.2.2 j = (chS L p f ((cnList L p).get j)).reverse ++ s.2.2 j := by
  induction B generalizing s with
  | zero =>
    intro r hr
    rw [runL, List.replicate_zero, foldL, List.mem_singleton] at hr
    subst hr
    exact ⟨Fin.elim0, fun j => by simp [chS, G.chString]⟩
  | succ B ih =>
    intro r hr
    rw [runL, List.replicate_succ, foldL] at hr
    obtain ⟨a, ha, r', hr', e⟩ := mem_bindL hr
    obtain ⟨op, hop, rfl⟩ := List.mem_map.1 ha
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hop
    obtain ⟨f, hf⟩ := ih _ r' hr'
    refine ⟨Fin.cons z f, fun j => ?_⟩
    rw [e, hf, chS_cons]
    simp [Opt.app]

theorem putsL_ne_nil {kss : List (List (List Bool))} {strs : List (List Bool)} {t : Tree} (h : putsL ub kss strs t ≠ [])
    {P : List (List (List Bool) × List Bool)} (hub : 0 < ub) (h1 : kss = P.map Prod.fst)
    (h2 : strs = P.map fun p => p.2 ++ [true]) : ∀ p ∈ P, ucount ub p.2 = p.1.length := by
  rw [h1, h2, putsL_eq hub] at h
  by_contra hc
  rw [if_neg hc] at h
  exact h rfl

/-- **(ii)** The outcomes of the moves at the roles of the group. -/
theorem outcome_of_accept (hub : 0 < ub) (hkind : ∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩)
    {b : G.Uid (K + K) U0 M.N U1 → UW ub} {t : Tree}
    (h : scriptSem (S := S) θ mu cb kinds T ub
      (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b) t ≠ []) {r : M.R} (hr : grp (M.rp r) = g) :
    ∃ ι : Fin (P.num n o r.1 * ub) → (M.kind r.1).I, ∀ ν : (M.kind r.1).CnAt r.2,
      (o ⟨r.1, ν.1⟩ : ℕ) = (∑ k, ((M.kind r.1).lam + (M.kind r.1).len (ι k) ν.1)) / ub := by
  have hmem : roleIns P n o key tg r ∈ script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨r, mem_roleList.2 hr, rfl⟩))
  obtain ⟨t', ht'⟩ := foldL_ne_nil h _ hmem
  rw [roleIns, insSem, hkind] at ht'
  simp only [roleSem] at ht'
  split_ifs at ht' with hs
  swap
  · exact absurd rfl ht'
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ ht'
  obtain ⟨a, ha, z', hz', -⟩ := mem_bindL hz
  obtain ⟨f, hf⟩ := mem_runL_roleTab (M.kind r.1) r.2 _ _ a ha
  have hne : putsL ub ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k))
      (List.ofFn fun j => (a.2.2.2 j).reverse ++ [true]) t' ≠ [] :=
    List.ne_nil_of_mem (mem_encT hz')
  have hkeys : ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k)) =
      (PN o key r f).map Prod.fst := by
    rw [PN, List.map_map]
    rfl
  have hstr : (List.ofFn fun j => (a.2.2.2 j).reverse ++ [true]) = (PN o key r f).map fun z => z.2 ++ [true] := by
    rw [PN, List.map_map]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp [hf]
  have hcnt := putsL_ne_nil hne hub hkeys hstr
  refine ⟨fun k => (f k).1, fun ν => ?_⟩
  have h1 := hcnt (kNew o key r ν, chS (M.kind r.1) r.2 f ν) (List.mem_map.2 ⟨ν, mem_cnList ν, rfl⟩)
  simp only at h1
  rw [length_kNew, ucount, Nat.add_right_cancel_iff] at h1
  rw [← h1]
  congr 1
  rw [chS, G.length_chString]

end Nc.Grp
