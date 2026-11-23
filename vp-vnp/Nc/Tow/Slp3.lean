/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Slp2

/-!
# The program of the tower plan: choices from loads, the loop over time
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b D J r m Uu AA U0 U1 : ℕ} {T : Tower h b D J r}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T}
variable {Inp ι : Type} {Dd Y p c : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}

theorem ind_eq {X X' : Type} {P : X → Prop} {Q : X' → Prop} {x : X} {y : X'} (hi : P x ↔ Q y) :
    ind P x = ind Q y := by
  by_cases hp : P x
  · rw [ind_true hp, ind_true (hi.1 hp)]
  · rw [ind_false hp, ind_false fun hq => hp (hi.2 hq)]

section Loads

variable {L : Inp → Tg T m AA → ℕ} (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hb : 0 < b)
  (hL : ∀ x τ, L x τ ≤ Wb R ch FL U0 U1)
include hA hB hb hL

theorem sqs_le (x : Inp) (j : Fin (J + 1)) (i : Fin h) : sqs (L x) j i ≤ 2 * Y ^ 3 := by
  unfold sqs
  calc _ ≤ ∑ _e : T.Ed j, Y ^ 2 := by
        refine Finset.sum_le_sum fun e _ => ?_
        split_ifs
        · exact Nat.pow_le_pow_left ((hL x _).trans hB.w) 2
        · exact Nat.zero_le _
    _ = Fintype.card (T.Ed j) * Y ^ 2 := by simp
    _ ≤ Y * Y ^ 2 := Nat.mul_le_mul_right _ (hB.ed j)
    _ = Y ^ 3 := by ring
    _ ≤ 2 * Y ^ 3 := by omega

theorem cy_sqs (hm : ∀ τ, (fun x => L x τ) ∈ H) (j : Fin (J + 1)) (i : Fin h) :
    CY Dd H Y 3 fun x => sqs (L x) j i := by
  have hY := hA.pos
  have e : ∀ x, sqs (L x) j i = ∑ e ∈ univ.filter (fun e : T.Ed j => T.ty e = i), L x (.edge j e) ^ 2 := by
    intro x
    rw [Finset.sum_filter]
    rfl
  refine CY.congr ?_ fun x => (e x).symm
  refine CY.sum hA _ ((card_filter_le _ _).trans (hB.ed j)) (fun e _ => ?_) fun x => ?_
  · refine CY.op1 hA (fun s => s ^ 2) (CY.base (hm _) hY) fun x => hA.lt_of_le3 ?_
    calc L x (.edge j e) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left ((hL x _).trans hB.w) 2
      _ ≤ Y ^ 3 := Nat.pow_le_pow_right hY (by omega)
      _ ≤ 2 * Y ^ 3 := by omega
  · rw [← e x]
    exact hA.lt_of_le3 (sqs_le hA hB hb hL x j i)

omit hb hL in
theorem py_isMin (hq : ∀ j i, (fun x => sqs (L x) j i) ∈ H) (j : Fin (J + 1)) (i : Fin h) :
    PY Dd H Y 7 fun x => IsMin (L x) j i := by
  have hY := hA.pos
  have h1 : ∀ i, PY Dd H Y 3 fun x => ∀ i', sqs (L x) j i ≤ sqs (L x) j i' := fun i =>
    PY.forall_univ hA (by simpa using hB.h) fun i' =>
      PY.rel hA (fun s t => s ≤ t) (CY.base (hq j i) hY) (CY.base (hq j i') hY)
  have h2 : PY Dd H Y 6 fun x => ∀ i' ∈ univ.filter (fun i' => i' < i), ¬ ∀ i'', sqs (L x) j i' ≤ sqs (L x) j i'' :=
    PY.forall_mem hA _ ((card_filter_le _ _).trans (by simpa using hB.h)) fun i' _ => PY.not hA (h1 i')
  refine (PY.and hA ((h1 i).mono hY (by omega)) h2).congr fun x => ?_
  unfold IsMin
  simp

omit hb hL in
theorem py_fits {s : Inp → ℕ} {a : ℕ} (hm : ∀ τ, (fun x => L x τ) ∈ H) (l : LMv T FL) (hs : CY Dd H Y a s) :
    PY Dd H Y (a + 3) fun x => Fits FL (L x) l (s x) := by
  classical
  have hY := hA.pos
  have h1 : PY Dd H Y (a + 1 + 2) fun x => ∀ q ∈ univ.filter (fun q : Sym2 T.Fl => ¬ q.IsDiag),
      L x (.seg l.1 l.2.1 l.2.2.1 q) ≤ slo FL l.2.2.2 q * s x :=
    PY.forall_mem hA _ ((card_filter_le _ _).trans hB.fl) fun q _ =>
      PY.rel hA (fun u t => u ≤ slo FL l.2.2.2 q * t) ((CY.base (hm _) hY).mono hY (Nat.zero_le a)) hs
  refine h1.congr fun x => ?_
  unfold Fits
  simp

theorem cy_tmin (hm : ∀ τ, (fun x => L x τ) ∈ H) (l : LMv T FL) : CY Dd H Y 8 fun x => tmin FL (L x) l := by
  have hY := hA.pos
  have h1 : ∀ s ∈ range Y, PY Dd H Y 6 fun x => ¬ ∃ d, Fits FL (L x) (withD FL l d) s := by
    intro s hs
    refine PY.not hA (PY.exists_univ hA hB.di fun d => ?_)
    exact py_fits hA hB hm (withD FL l d) (CY.const s (hA.lt_of_le (mem_range.1 hs).le))
  have hlt : ∀ x, tmin FL (L x) l < Y := fun x =>
    lt_of_lt_of_le (tmin_lt hb (fun τ => hL x τ) l) hB.tt
  have e : ∀ x, tmin FL (L x) l = ∑ s ∈ range Y, ind (fun x => ¬ ∃ d, Fits FL (L x) (withD FL l d) s) x := by
    intro x
    rw [tmin_sum (hlt x)]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact ind_eq Iff.rfl
  refine CY.congr ?_ fun x => (e x).symm
  refine CY.sum hA _ (by simp) (fun s hs => (h1 s hs).toCY) fun x => ?_
  rw [← e x]
  exact hA.lt_of_le (hlt x).le

omit hb hL in
theorem py_pick (hm : ∀ τ, (fun x => L x τ) ∈ H) (ht : ∀ l : LMv T FL, (fun x => tmin FL (L x) l) ∈ H) (l : LMv T FL) :
    PY Dd H Y 7 fun x => Pick FL (L x) l := by
  have hY := hA.pos
  have h1 : ∀ d, PY Dd H Y 3 fun x => Fits FL (L x) (withD FL l d) (tmin FL (L x) l) := fun d =>
    py_fits hA hB hm (withD FL l d) (CY.base (ht l) hY)
  have h0 : PY Dd H Y 3 fun x => Fits FL (L x) l (tmin FL (L x) l) := py_fits hA hB hm l (CY.base (ht l) hY)
  have h2 : PY Dd H Y 6 fun x => ∀ d ∈ univ.filter
      (fun d => Fintype.equivFin FL.Di d < Fintype.equivFin FL.Di l.2.2.2),
      ¬ Fits FL (L x) (withD FL l d) (tmin FL (L x) l) :=
    PY.forall_mem hA _ ((card_filter_le _ _).trans hB.di) fun d _ => PY.not hA (h1 d)
  refine (PY.and hA (h0.mono hY (by omega)) h2).congr fun x => ?_
  unfold Pick
  simp

omit hb hL in
theorem py_actR (hi : ∀ j i, ind (fun x => IsMin (L x) j i) ∈ H) (y : RM T m AA) :
    PY Dd H Y 0 fun x => ActR (L x) y := by
  have hY := hA.pos
  rcases y with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · exact PY.const hA True
  · exact PY.base (hi _ _) hY
  · by_cases hs : s = 0
    · refine (PY.base (hi j.castSucc (T.ty e)) hY).congr fun x => ?_
      exact ⟨fun h _ => h, fun h => h hs⟩
    · refine (PY.const hA True).congr fun x => ?_
      exact ⟨fun _ h => absurd h hs, fun _ => trivial⟩
  · exact PY.const hA True

theorem cy_numF (hm : ∀ τ, (fun x => L x τ) ∈ H) (hi : ∀ j i, ind (fun x => IsMin (L x) j i) ∈ H)
    (ht : ∀ l : LMv T FL, (fun x => tmin FL (L x) l) ∈ H) (hp : ∀ l : LMv T FL, ind (fun x => Pick FL (L x) l) ∈ H)
    (mv : Mv T R ch FL) : CY Dd H Y 2 fun x => numF R ch FL (L x) mv := by
  classical
  have hY := hA.pos
  rcases mv with y | l
  · refine (CY.ite hA (py_actR hA hB hi y.1) (CY.base (hm (inpR T y.1)) hY) (CY.const 0 hA.zero_lt)
      (fun x => hA.lt_of_le ((hL x _).trans hB.w)) fun _ => hA.zero_lt).congr fun x => ?_
    unfold numF
    by_cases ha : ActR (L x) y.1
    · rw [if_pos ha]
      exact (if_pos ha).symm
    · rw [if_neg ha]
      exact (if_neg ha).symm
  · refine (CY.ite hA (PY.base (hp l) hY) (CY.base (ht l) hY) (CY.const 0 hA.zero_lt)
      (fun x => hA.lt_of_le (lt_of_lt_of_le (tmin_lt hb (fun τ => hL x τ) l) hB.tt).le) fun _ => hA.zero_lt).congr
      fun x => ?_
    unfold numF
    by_cases ha : Pick FL (L x) l
    · rw [if_pos ha]
      exact (if_pos ha).symm
    · rw [if_neg ha]
      exact (if_neg ha).symm

/-- What is computed from loads. -/
structure Chosen (L : Inp → Tg T m AA → ℕ) (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T)
    (H : Set (Inp → ℕ)) : Prop where
  isMin : ∀ j i, ind (fun x => IsMin (L x) j i) ∈ H
  tmin : ∀ l : LMv T FL, (fun x => tmin FL (L x) l) ∈ H
  pick : ∀ l : LMv T FL, ind (fun x => Pick FL (L x) l) ∈ H
  numF : ∀ mv : Mv T R ch FL, (fun x => numF R ch FL (L x) mv) ∈ H

omit hA hB hb hL in
theorem Chosen.weaken {L : Inp → Tg T m AA → ℕ} {H H' : Set (Inp → ℕ)} (hc : Chosen L R ch FL H) (hH : H ⊆ H') :
    Chosen L R ch FL H' :=
  ⟨fun j i => hH (hc.isMin j i), fun l => hH (hc.tmin l), fun l => hH (hc.pick l), fun mv => hH (hc.numF mv)⟩

theorem pick_stage (hS : SY inp Y p c H) (hm : ∀ τ, (fun x => L x τ) ∈ H) :
    ∃ H', SY inp Y p (c + 5) H' ∧ H ⊆ H' ∧ Chosen L R ch FL H' := by
  have hjh : Fintype.card (Fin (J + 1) × Fin h) ≤ Y ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, pow_two]
    exact Nat.mul_le_mul hB.j hB.h
  have hl : Fintype.card (LMv T FL) ≤ Y ^ 1 := by
    rw [pow_one]
    exact (Fintype.card_le_of_injective (fun l : LMv T FL => (Sum.inr l : Mv T R ch FL)) Sum.inr_injective).trans hB.mv
  obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := Fin (J + 1) × Fin h) (fun q x => sqs (L x) q.1 q.2) (a := 3) (e := 2)
    hjh (fun q => cy_sqs hA hB hb hL hm q.1 q.2) (by omega)
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (κ := Fin (J + 1) × Fin h) (fun q => ind fun x => IsMin (L x) q.1 q.2)
    (a := 7) (e := 2) hjh (fun q => py_isMin hA hB (fun j i => f1 (j, i)) q.1 q.2) (by omega)
  have m2 : ∀ τ, (fun x => L x τ) ∈ H2 := fun τ => u2 (u1 (hm τ))
  obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (κ := LMv T FL) (fun l x => tmin FL (L x) l) (a := 8) (e := 1) hl
    (fun l => cy_tmin hA hB hb hL m2 l) (by omega)
  have m3 : ∀ τ, (fun x => L x τ) ∈ H3 := fun τ => u3 (m2 τ)
  obtain ⟨H4, s4, u4, f4⟩ := s3.add hA (κ := LMv T FL) (fun l => ind fun x => Pick FL (L x) l) (a := 7) (e := 1) hl
    (fun l => py_pick hA hB m3 f3 l) (by omega)
  have m4 : ∀ τ, (fun x => L x τ) ∈ H4 := fun τ => u4 (m3 τ)
  obtain ⟨H5, s5, u5, f5⟩ := s4.add hA (κ := Mv T R ch FL) (fun mv x => numF R ch FL (L x) mv) (a := 2) (e := 1)
    (by simpa using hB.mv) (fun mv => cy_numF hA hB hb hL m4 (fun j i => u4 (u3 (f2 (j, i)))) (fun l => u4 (f3 l)) f4 mv)
    (by omega)
  exact ⟨H5, s5, u1.trans (u2.trans (u3.trans (u4.trans u5))), fun j i => u5 (u4 (u3 (f2 (j, i)))),
    fun l => u5 (u4 (f3 l)), fun l => u5 (f4 l), f5⟩

end Loads

variable {nx : Inp → Fin AA → Fin AA → ℕ} {ox : Inp → NM R FL (ch := ch) → ℕ} {lhat : ℕ}
variable (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hR : Rng nx ox U0 U1) (hb : 0 < b)
include hA hB hR hb

/-- The loop over time. -/
theorem num_stage (hS : SY inp Y p c H) (hs : Stat nx ox lhat H) (t : ℕ) :
    ∃ H', SY inp Y p (c + 1 + 8 * t) H' ∧ H ⊆ H' ∧
      ∀ mv : Mv T R ch FL, (fun x => numS R ch FL lhat (nx x) (ox x) t mv) ∈ H' := by
  have hY := hA.pos
  induction t with
  | zero =>
    obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := Mv T R ch FL) (fun mv x => numS R ch FL lhat (nx x) (ox x) 0 mv)
      (a := 0) (e := 1) (by simpa using hB.mv) (fun mv => CY.const 0 hA.zero_lt) (by omega)
    exact ⟨H1, s1, u1, f1⟩
  | succ t ih =>
    obtain ⟨H0, s0, u0, f0⟩ := ih
    obtain ⟨H1, s1, u1, f1, g1⟩ := ld_stage hA hB hR s0 (hs.weaken u0) f0
    obtain ⟨H2, s2, u2, f2⟩ := pick_stage hA hB hb
      (fun x τ => ld_le (hR.n x) (hR.o x) _ τ) s1 g1
    obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (κ := Mv T R ch FL)
      (fun mv x => numS R ch FL lhat (nx x) (ox x) (t + 1) mv) (a := 0) (e := 1) (by simpa using hB.mv)
      (fun mv => by
        by_cases ht : timeM R ch FL mv = t
        · refine (CY.base (f2.numF mv) hY).congr fun x => ?_
          rw [numS, if_pos ht]
        · refine (CY.base (u2 (u1 (f0 mv))) hY).congr fun x => ?_
          rw [numS, if_neg ht]) (by omega)
    exact ⟨H3, s3.le hA (by omega), u0.trans (u1.trans (u2.trans u3)), f3⟩

/-- What is known after the loop. -/
structure After (nx : Inp → Fin AA → Fin AA → ℕ) (ox : Inp → NM R FL (ch := ch) → ℕ) (lhat : ℕ)
    (H : Set (Inp → ℕ)) : Prop extends Stat nx ox lhat H,
    Chosen (fun x => load R ch FL lhat (nx x) (ox x)) R ch FL H where
  num : ∀ mv : Mv T R ch FL, (fun x => num R ch FL lhat (nx x) (ox x) mv) ∈ H
  alv : ∀ ν : NM R FL (ch := ch), (fun x => alv R ch FL lhat (nx x) (ox x) ν) ∈ H
  load : ∀ τ : Tg T m AA, (fun x => load R ch FL lhat (nx x) (ox x) τ) ∈ H

omit hA hB hR hb in
theorem After.weaken {H H' : Set (Inp → ℕ)} (ha : After nx ox lhat H) (hH : H ⊆ H') : After nx ox lhat H' where
  toStat := ha.toStat.weaken hH
  toChosen := ha.toChosen.weaken hH
  num mv := hH (ha.num mv)
  alv ν := hH (ha.alv ν)
  load τ := hH (ha.load τ)

theorem after_stage (hS : SY inp Y p c H) (hbs : Base nx ox H) :
    ∃ H', SY inp Y p (c + 11 + 8 * Y) H' ∧ H ⊆ H' ∧ After nx ox lhat H' := by
  obtain ⟨H1, s1, u1, f1⟩ := stat_stage hA hB hR hS hbs (lhat := lhat)
  obtain ⟨H2, s2, u2, f2⟩ := num_stage hA hB hR hb s1 f1 (tend J m)
  obtain ⟨H3, s3, u3, f3, g3⟩ := ld_stage hA hB hR s2 (f1.weaken u2)
    (Nf := fun x => num R ch FL lhat (nx x) (ox x)) f2
  obtain ⟨H4, s4, u4, f4⟩ := pick_stage (L := fun x => load R ch FL lhat (nx x) (ox x)) hA hB hb
    (fun x τ => ld_le (hR.n x) (hR.o x) _ τ) s3 g3
  refine ⟨H4, s4.le hA ?_, u1.trans (u2.trans (u3.trans u4)), (f1.weaken (u2.trans (u3.trans u4))), f4,
    fun mv => u4 (u3 (f2 mv)), fun ν => u4 (f3 ν), fun τ => u4 (g3 τ)⟩
  have := hB.t
  omega

end Nc.Tow
