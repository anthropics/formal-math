/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Slp1

/-!
# The program of the tower plan: one step of time
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b D J r m Uu AA U0 U1 : ℕ} {T : Tower h b D J r}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T}
variable {Inp ι : Type} {Dd Y p c : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}
variable (nx : Inp → Fin AA → Fin AA → ℕ) (ox : Inp → NM R FL (ch := ch) → ℕ) (lhat : ℕ)

/-- What is available at the beginning. -/
structure Base (H : Set (Inp → ℕ)) : Prop where
  n : ∀ a c, (fun x => nx x a c) ∈ H
  o : ∀ ν, (fun x => ox x ν) ∈ H

theorem Base.weaken {nx : Inp → Fin AA → Fin AA → ℕ} {ox : Inp → NM R FL (ch := ch) → ℕ} {H H' : Set (Inp → ℕ)}
    (hb : Base nx ox H) (hH : H ⊆ H') : Base nx ox H' :=
  ⟨fun a c => hH (hb.n a c), fun ν => hH (hb.o ν)⟩

/-- What doesn't depend on time. -/
structure Stat (H : Set (Inp → ℕ)) : Prop extends Base nx ox H where
  valid : ind (fun x => Valid lhat (nx x)) ∈ H
  bt : ∀ τ : Tg T m AA, (fun x => bt R ch lhat (nx x) τ) ∈ H
  q : ∀ l : LMv T FL, (fun x => ∑ ν : (FL.L l.2.2.2).Cn, ox x ⟨Sum.inr l, ν⟩ ^ 2) ∈ H

theorem Stat.weaken {nx : Inp → Fin AA → Fin AA → ℕ} {ox : Inp → NM R FL (ch := ch) → ℕ} {lhat : ℕ}
    {H H' : Set (Inp → ℕ)} (hb : Stat nx ox lhat H) (hH : H ⊆ H') : Stat nx ox lhat H' :=
  ⟨hb.toBase.weaken hH, hH hb.valid, fun τ => hH (hb.bt τ), fun l => hH (hb.q l)⟩

/-- The values are in range. -/
structure Rng (U0 U1 : ℕ) : Prop where
  n : ∀ x a c, nx x a c ≤ U0
  o : ∀ x ν, ox x ν ≤ U1

variable {nx ox lhat} (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hR : Rng nx ox U0 U1)
include hA hB hR

theorem card_cn (l : LMv T FL) : Fintype.card (FL.L l.2.2.2).Cn ≤ Y := by
  refine (Fintype.card_le_of_injective
    (fun ν : (FL.L l.2.2.2).Cn => (⟨Sum.inr l, ν⟩ : NM R FL (ch := ch))) ?_).trans hB.nm
  intro ν ν' he
  have := eq_of_heq (Sigma.mk.inj he).2
  exact this

theorem py_valid (hb : Base nx ox H) : PY Dd H Y 6 fun x => Valid lhat (nx x) := by
  have hY := hA.pos
  unfold Valid
  refine PY.forall_univ hA (by simpa using hB.aa1) fun a => PY.rel1 hA (fun s => s ≤ lhat) ?_
  refine CY.sum hA univ (by simpa using hB.aa1) (fun c _ => ?_) fun x => hA.lt_of_le3 ?_
  · by_cases hca : c = a
    · simp only [if_pos hca]
      exact (CY.const 0 hA.zero_lt).mono hY (Nat.zero_le 1)
    · simp only [if_neg hca]
      refine CY.op hA (fun s t => s + t) (CY.base (hb.n a c) hY) (CY.base (hb.n c a) hY) fun x => hA.lt_of_le3 ?_
      have h1 := hR.n x a c
      have h2 := hR.n x c a
      have h3 := hB.u0 a
      have h4 : Y ≤ Y ^ 3 := Nat.le_self_pow (by omega) Y
      change nx x a c + nx x c a ≤ _
      omega
  · have h3 := hB.u0 a
    calc _ ≤ ∑ _c : Fin AA, 2 * Y := by
          refine Finset.sum_le_sum fun c _ => ?_
          have h1 := hR.n x a c
          have h2 := hR.n x c a
          split_ifs <;> omega
      _ = AA * (2 * Y) := by simp
      _ ≤ Y * (2 * Y) := Nat.mul_le_mul_right _ hB.aa1
      _ = 2 * Y ^ 2 := by ring
      _ ≤ 2 * Y ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY (by omega))

theorem cy_bt (hb : Base nx ox H) (hv : ind (fun x => Valid lhat (nx x)) ∈ H) (τ : Tg T m AA) :
    CY Dd H Y 7 fun x => bt R ch lhat (nx x) τ := by
  classical
  have hY := hA.pos
  have hb0 : ∀ x, ∑ a, ∑ c, ((range (nx x a c)).filter fun k => tgB T R ch a c k = τ).card ≤ Y := by
    intro x
    refine le_trans ?_ hB.w
    unfold Wb
    refine le_trans ?_ (Nat.le_add_right _ _)
    calc _ ≤ ∑ _a : Fin AA, ∑ _c : Fin AA, U0 := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => ?_
          refine (card_filter_le _ _).trans ?_
          rw [card_range]
          exact hR.n x a c
      _ = AA * AA * U0 := by simp; ring
  have h1 : CY Dd H Y 5 fun x => ∑ a, ∑ c, ((range (nx x a c)).filter fun k => tgB T R ch a c k = τ).card := by
    refine CY.sum hA univ (by simpa using hB.aa1) (fun a _ => ?_) fun x => hA.lt_of_le (hb0 x)
    refine CY.sum hA univ (by simpa using hB.aa1) (fun c _ => ?_) fun x => hA.lt_of_le ?_
    · refine CY.op1 hA (fun s => ((range s).filter fun k => tgB T R ch a c k = τ).card)
        (CY.base (hb.n a c) hY) fun x => hA.lt_of_le ?_
      refine (card_filter_le _ _).trans ?_
      rw [card_range]
      exact (hR.n x a c).trans (hB.u0 a)
    · refine le_trans ?_ (hb0 x)
      exact Finset.single_le_sum (f := fun a => ∑ c, ((range (nx x a c)).filter fun k => tgB T R ch a c k = τ).card)
        (fun _ _ => Nat.zero_le _) (mem_univ a)
  refine (CY.ite hA ((PY.base hv hY).mono hY (Nat.zero_le 5)) h1
    ((CY.const 0 hA.zero_lt).mono hY (Nat.zero_le 5)) (fun x => hA.lt_of_le (hb0 x)) fun _ => hA.zero_lt).congr
    fun x => ?_
  rfl

theorem cy_q (hb : Base nx ox H) (l : LMv T FL) :
    CY Dd H Y 3 fun x => ∑ ν : (FL.L l.2.2.2).Cn, ox x ⟨Sum.inr l, ν⟩ ^ 2 := by
  have hY := hA.pos
  have h1 : ∀ x (ν : (FL.L l.2.2.2).Cn), ox x ⟨Sum.inr l, ν⟩ ^ 2 ≤ Y ^ 2 := fun x ν =>
    Nat.pow_le_pow_left ((hR.o x _).trans (hB.u1 (⟨Sum.inr l, ν⟩ : NM R FL (ch := ch)))) 2
  refine CY.sum hA univ (card_cn hA hB hR l) (fun ν _ => ?_) fun x => hA.lt_of_le3 ?_
  · refine CY.op1 hA (fun s => s ^ 2) (CY.base (hb.o _) hY) fun x => hA.lt_of_le3 ((h1 x ν).trans ?_)
    have : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY (by omega)
    omega
  · calc _ ≤ ∑ _ν : (FL.L l.2.2.2).Cn, Y ^ 2 := Finset.sum_le_sum fun ν _ => h1 x ν
      _ = Fintype.card (FL.L l.2.2.2).Cn * Y ^ 2 := by simp
      _ ≤ Y * Y ^ 2 := Nat.mul_le_mul_right _ (card_cn hA hB hR l)
      _ = Y ^ 3 := by ring
      _ ≤ 2 * Y ^ 3 := by omega

/-- The static part. -/
theorem stat_stage (hS : SY inp Y p c H) (hb : Base nx ox H) :
    ∃ H', SY inp Y p (c + 3) H' ∧ H ⊆ H' ∧ Stat nx ox lhat H' := by
  have hY := hA.pos
  obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := Unit) (fun _ => ind fun x => Valid lhat (nx x)) (a := 6) (e := 0)
    (by simp) (fun _ => py_valid hA hB hR hb) (by omega)
  have hb1 := hb.weaken u1
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (κ := Tg T m AA) (fun τ x => bt R ch lhat (nx x) τ) (a := 7) (e := 1)
    (by simpa using hB.tg) (fun τ => cy_bt hA hB hR hb1 (f1 ()) τ) (by omega)
  have hl : Fintype.card (LMv T FL) ≤ Y := by
    refine (Fintype.card_le_of_injective (fun l : LMv T FL => (Sum.inr l : Mv T R ch FL)) Sum.inr_injective).trans hB.mv
  obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (κ := LMv T FL)
    (fun l x => ∑ ν : (FL.L l.2.2.2).Cn, ox x ⟨Sum.inr l, ν⟩ ^ 2) (a := 3) (e := 1)
    (by simpa using hl) (fun l => cy_q hA hB hR (hb1.weaken u2) l) (by omega)
  exact ⟨H3, s3, u1.trans (u2.trans u3), (hb1.weaken u2).weaken u3, u3 (u2 (f1 ())), fun τ => u3 (f2 τ), f3⟩

/-- Alive units from numbers of units. -/
theorem cy_alvN (hs : Stat nx ox lhat H) {Nf : Inp → Mv T R ch FL → ℕ} (hN : ∀ mv, (fun x => Nf x mv) ∈ H)
    (ν : NM R FL (ch := ch)) : CY Dd H Y 3 fun x => alvN R ch FL (ox x) ν (Nf x ν.1) := by
  have hY := hA.pos
  have hlt : ∀ x, alvN R ch FL (ox x) ν (Nf x ν.1) ≤ Y := fun x =>
    ((alvN_le _ _).trans (hR.o x ν)).trans (hB.u1 ν)
  rcases ν with ⟨y | l, ν⟩
  · refine CY.mono hY (a := 1) ((CY.op hA (fun s t => if s = t then t else 0) (CY.base (hs.o _) hY)
      (CY.base (hN (.inl y)) hY) fun x => hA.lt_of_le (hlt x)).congr fun x => ?_) (by omega)
    exact (alvN_inl y ν _).symm
  · have hg : PY Dd H Y 1 fun x => GoodL R ch FL (ox x) l (Nf x (.inr l)) :=
      PY.rel hA (fun q t => r * b * q ≤ FL.G₁ * t ^ 2) (CY.base (hs.q l) hY) (CY.base (hN (.inr l)) hY)
    have ho : ∀ x, ox x ⟨.inr l, ν⟩ ≤ Y := fun x => (hR.o x _).trans (hB.u1 ⟨.inr l, ν⟩)
    have hm : CY Dd H Y 1 fun x => min (ox x ⟨.inr l, ν⟩) (Nf x (.inr l)) :=
      CY.op hA (fun s t => min s t) (CY.base (hs.o _) hY) (CY.base (hN (.inr l)) hY)
        fun x => hA.lt_of_le ((min_le_left _ _).trans (ho x))
    refine (CY.ite hA hg ((CY.base (hs.o ⟨.inr l, ν⟩) hY).mono hY (Nat.zero_le 1)) hm
      (fun x => hA.lt_of_le (ho x)) fun x => hA.lt_of_le ((min_le_left _ _).trans (ho x))).congr fun x => ?_
    exact (alvN_inr l ν _).symm

/-- Loads from alive units. -/
theorem cy_ld (hs : Stat nx ox lhat H) {Nf : Inp → Mv T R ch FL → ℕ}
    (ha : ∀ ν : NM R FL (ch := ch), (fun x => alvN R ch FL (ox x) ν (Nf x ν.1)) ∈ H) (τ : Tg T m AA) :
    CY Dd H Y 3 fun x => ld R ch FL lhat (nx x) (ox x) (Nf x) τ := by
  have hY := hA.pos
  have hle : ∀ x, ld R ch FL lhat (nx x) (ox x) (Nf x) τ ≤ Y := fun x =>
    (ld_le (hR.n x) (hR.o x) _ _).trans hB.w
  have e : ∀ x, ld R ch FL lhat (nx x) (ox x) (Nf x) τ = bt R ch lhat (nx x) τ +
      ∑ ν ∈ univ.filter (fun ν : NM R FL (ch := ch) => tgM R ch FL ν.1 ν.2 = τ),
        alvN R ch FL (ox x) ν (Nf x ν.1) := by
    intro x
    rw [Finset.sum_filter]
    rfl
  have h1 : CY Dd H Y 2 fun x => ∑ ν ∈ univ.filter (fun ν : NM R FL (ch := ch) => tgM R ch FL ν.1 ν.2 = τ),
        alvN R ch FL (ox x) ν (Nf x ν.1) := by
    refine CY.sum hA _ ((card_filter_le _ _).trans hB.nm) (fun ν _ => CY.base (ha ν) hY) fun x => hA.lt_of_le ?_
    have := hle x
    rw [e] at this
    omega
  refine (CY.op hA (fun s t => s + t) ((CY.base (hs.bt τ) hY).mono hY (Nat.zero_le 2)) h1 fun x => ?_).congr
    fun x => (e x).symm
  have := hle x
  rw [e] at this
  exact hA.lt_of_le this

/-- Alive units and loads. -/
theorem ld_stage (hS : SY inp Y p c H) (hs : Stat nx ox lhat H) {Nf : Inp → Mv T R ch FL → ℕ}
    (hN : ∀ mv, (fun x => Nf x mv) ∈ H) : ∃ H', SY inp Y p (c + 2) H' ∧ H ⊆ H' ∧
      (∀ ν : NM R FL (ch := ch), (fun x => alvN R ch FL (ox x) ν (Nf x ν.1)) ∈ H') ∧
      ∀ τ, (fun x => ld R ch FL lhat (nx x) (ox x) (Nf x) τ) ∈ H' := by
  obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := NM R FL (ch := ch))
    (fun ν x => alvN R ch FL (ox x) ν (Nf x ν.1)) (a := 3) (e := 1) (by simpa using hB.nm)
    (fun ν => cy_alvN hA hB hR hs hN ν) (by omega)
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (κ := Tg T m AA)
    (fun τ x => ld R ch FL lhat (nx x) (ox x) (Nf x) τ) (a := 3) (e := 1) (by simpa using hB.tg)
    (fun τ => cy_ld hA hB hR (hs.weaken u1) f1 τ) (by omega)
  exact ⟨H2, s2, u1.trans u2, fun ν => u2 (f1 ν), f2⟩

end Nc.Tow
