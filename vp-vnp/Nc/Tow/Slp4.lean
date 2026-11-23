/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Slp3

/-!
# The program of the tower plan: units
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}

section Mem

variable {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}

theorem rkU_sum (u : Un R FL Pl U0 U1) : rkU R FL Pl lhat n o u =
    ∑ v ∈ univ.filter (fun v : Un R FL Pl U0 U1 => tgU R FL Pl v = tgU R FL Pl u ∧ ix R FL Pl v < ix R FL Pl u),
      ind (fun _ : Unit => AlU R FL Pl lhat n o v) () := by
  classical
  have h1 : ∀ v, ind (fun _ : Unit => AlU R FL Pl lhat n o v) () = if AlU R FL Pl lhat n o v then 1 else 0 := by
    intro v
    by_cases hv : AlU R FL Pl lhat n o v
    · rw [if_pos hv, ind_true (P := fun _ : Unit => AlU R FL Pl lhat n o v) hv]
    · rw [if_neg hv, ind_false (P := fun _ : Unit => AlU R FL Pl lhat n o v) hv]
  rw [Finset.sum_congr rfl fun v _ => h1 v, ← Finset.card_filter, Finset.filter_filter]
  unfold rkU rk
  congr 1
  ext v
  simp only [mem_filter, mem_Al, mem_univ, true_and]
  tauto

theorem mem_cons_inl (y : {x : RM T m AA // okR T R ch x}) (s : (kindM R ch FL (.inl y)).Sl) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inl y, s⟩ ↔
      ActR (load R ch FL lhat (nn n) (oo R FL Pl o)) y.1 ∧ AlU R FL Pl lhat n o u ∧ tgU R FL Pl u = inpR T y.1 := by
  classical
  simp only [consM]
  by_cases ha : ActR (load R ch FL lhat (nn n) (oo R FL Pl o)) y.1
  · rw [if_pos ha, mem_filter, mem_Al]
    exact ⟨fun hu => ⟨ha, hu⟩, fun hu => hu.2⟩
  · rw [if_neg ha]
    exact ⟨fun hu => absurd hu (notMem_empty _), fun hu => absurd hu.1 ha⟩

theorem mem_cons_inr (l : LMv T FL) (e : (FL.L l.2.2.2).Sl) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inr l, e⟩ ↔
      Pick FL (load R ch FL lhat (nn n) (oo R FL Pl o)) l ∧ AlU R FL Pl lhat n o u ∧
        tgU R FL Pl u = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) ∧
        su FL l.2.2.2 e * num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) ≤ rkU R FL Pl lhat n o u ∧
        rkU R FL Pl lhat n o u < (su FL l.2.2.2 e + 1) * num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) := by
  classical
  simp only [consM]
  by_cases ha : Pick FL (load R ch FL lhat (nn n) (oo R FL Pl o)) l
  · rw [if_pos ha, mem_filter, mem_Al]
    exact ⟨fun hu => ⟨ha, hu⟩, fun hu => hu.2⟩
  · rw [if_neg ha]
    exact ⟨fun hu => absurd hu (notMem_empty _), fun hu => absurd hu.1 ha⟩

/-- The unit is made at some time. -/
def SeenU (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1) : Un R FL Pl U0 U1 → Prop
  | .init a c k => k.1 < (n a c).1
  | .new ν k => k.1 ≤ (o ν).1

theorem mem_cur (u : Un R FL Pl U0 U1) :
    u ∈ (plan R FL Pl lhat U0 U1).cur n o (Fintype.card (Mv T R ch FL)) ↔
      SeenU n o u ∧ ¬ ∃ z : ZM R FL (ch := ch), u ∈ consM R FL Pl lhat n o z := by
  classical
  unfold Plan.cur
  rw [mem_sdiff]
  refine and_congr ?_ (not_congr ?_)
  · unfold Plan.seenAt
    rw [mem_union, mem_biUnion]
    rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
    · simp [seen0, newUnits, SeenU]
    · constructor
      · rintro (h1 | ⟨x', -, h2⟩)
        · simp [seen0] at h1
        · simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq] at h2
          exact h2.2
      · intro h1
        refine Or.inr ⟨ν.1, mem_filter.2 ⟨mem_univ _, ν.1.2⟩, ?_⟩
        simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq]
        exact h1
  · unfold Plan.used
    rw [mem_biUnion]
    constructor
    · rintro ⟨z, -, hz⟩
      exact ⟨eZ R FL Pl z, hz⟩
    · rintro ⟨z, hz⟩
      refine ⟨(eZ R FL Pl).symm z, mem_filter.2 ⟨mem_univ _, ((eZ R FL Pl).symm z).1.2⟩, ?_⟩
      change u ∈ consM R FL Pl lhat n o (eZ R FL Pl ((eZ R FL Pl).symm z))
      rw [Equiv.apply_symm_apply]
      exact hz

end Mem

variable {Inp ι : Type} {Dd Y p c TM : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}
variable {nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)} {oI : Inp → (sys R FL Pl).N → Fin U1}

/-- More bounds. -/
structure Bnd2 (R : Routes T m Uu) (FL : FlagLaws F T) (Pl : Place T ch A') (U0 U1 Y TM : ℕ) : Prop where
  zm : Fintype.card (ZM R FL (ch := ch)) ≤ Y
  un : Fintype.card (Un R FL Pl U0 U1) ≤ Y
  tm : TM ≤ Y

/-- The numbers of initial units. -/
def nX (nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)) (x : Inp) : Fin AA → Fin AA → ℕ := nn (nI x)

/-- The outcomes. -/
noncomputable def oX (oI : Inp → (sys R FL Pl).N → Fin U1) (x : Inp) : NM R FL (ch := ch) → ℕ := oo R FL Pl (oI x)

theorem rng : Rng (nX nI) (oX oI : Inp → NM R FL (ch := ch) → ℕ) U0 U1 where
  n x a c := Nat.le_of_lt_succ (nI x a c).2
  o x _ := (oI x _).2.le

/-- What is known about units. -/
structure Units (nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)) (oI : Inp → (sys R FL Pl).N → Fin U1) (lhat TM : ℕ)
    (H : Set (Inp → ℕ)) : Prop where
  cons : ∀ z u, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) ∈ H
  num : ∀ mv : Mv T R ch FL, (fun x => num R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)) mv) ∈ H
  lt : ∀ (mv : Mv T R ch FL) (τ : Fin TM), ind (fun x => τ.1 < Tow.num R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)) mv) ∈ H
  pad : ∀ (z : ZM R FL (ch := ch)) (τ : Fin TM), ind (fun x => (consM R FL Pl lhat (nI x) (oI x) z).card ≤ τ.1 ∧
    τ.1 < Tow.num R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)) z.1) ∈ H
  cur : ∀ u, ind (fun x => u ∈ (plan R FL Pl lhat U0 U1).cur (nI x) (oI x) (Fintype.card (Mv T R ch FL))) ∈ H
  good : ∀ mv : Mv T R ch FL, ind (fun x => GoodMv R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)) mv) ∈ H
  good' : ind (fun x => ∀ mv : Mv T R ch FL, GoodMv R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)) mv) ∈ H
  valid : ind (fun x => Valid lhat (nn (nI x))) ∈ H

theorem Units.weaken {H H' : Set (Inp → ℕ)} (hu : Units nI oI lhat TM H) (hH : H ⊆ H') : Units nI oI lhat TM H' :=
  ⟨fun z u => hH (hu.cons z u), fun mv => hH (hu.num mv), fun mv τ => hH (hu.lt mv τ), fun z τ => hH (hu.pad z τ),
    fun u => hH (hu.cur u), fun mv => hH (hu.good mv), hH hu.good', hH hu.valid⟩

variable (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hB2 : Bnd2 R FL Pl U0 U1 Y TM)
include hA hB hB2

theorem py_al (ha : After (nX nI) (oX oI) lhat H) (u : Un R FL Pl U0 U1) :
    PY Dd H Y 2 fun x => AlU R FL Pl lhat (nI x) (oI x) u := by
  have hY := hA.pos
  rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
  · exact PY.and hA ((PY.base ha.valid hY).mono hY (Nat.zero_le 1))
      (PY.rel1 hA (fun s => k.1 < s) (CY.base (ha.n a c) hY))
  · exact (PY.rel1 hA (fun s => k.1 < s) (CY.base (ha.alv (eN R FL Pl ν)) hY)).mono hY (by omega)

theorem cy_rk (hal : ∀ u, ind (fun x => AlU R FL Pl lhat (nI x) (oI x) u) ∈ H) (u : Un R FL Pl U0 U1) :
    CY Dd H Y 2 fun x => rkU R FL Pl lhat (nI x) (oI x) u := by
  have hY := hA.pos
  have e : ∀ x, rkU R FL Pl lhat (nI x) (oI x) u =
      ∑ v ∈ univ.filter (fun v : Un R FL Pl U0 U1 => tgU R FL Pl v = tgU R FL Pl u ∧ ix R FL Pl v < ix R FL Pl u),
        ind (fun x => AlU R FL Pl lhat (nI x) (oI x) v) x := by
    intro x
    rw [rkU_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : AlU R FL Pl lhat (nI x) (oI x) v
    · rw [ind_true (P := fun x => AlU R FL Pl lhat (nI x) (oI x) v) hv,
        ind_true (P := fun _ : Unit => AlU R FL Pl lhat (nI x) (oI x) v) hv]
    · rw [ind_false (P := fun x => AlU R FL Pl lhat (nI x) (oI x) v) hv,
        ind_false (P := fun _ : Unit => AlU R FL Pl lhat (nI x) (oI x) v) hv]
  refine CY.congr ?_ fun x => (e x).symm
  refine CY.sum hA _ ((card_filter_le _ _).trans hB2.un) (fun v _ => CY.base (hal v) hY) fun x => hA.lt_of_le ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun v _ => ind_le _ _).trans ?_
  rw [smul_eq_mul, mul_one]
  exact (card_filter_le _ _).trans hB2.un

theorem py_cons (ha : After (nX nI) (oX oI) lhat H)
    (hal : ∀ u, ind (fun x => AlU R FL Pl lhat (nI x) (oI x) u) ∈ H)
    (hrk : ∀ u, (fun x => rkU R FL Pl lhat (nI x) (oI x) u) ∈ H) (z : ZM R FL (ch := ch)) (u : Un R FL Pl U0 U1) :
    PY Dd H Y 5 fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z := by
  have hY := hA.pos
  rcases z with ⟨y | l, e⟩
  · have h1 : PY Dd H Y 0 fun x => ActR (load R ch FL lhat (nX nI x) (oX oI x)) y.1 := py_actR hA hB ha.isMin y.1
    have h2 := PY.and hA (h1.mono hY (Nat.zero_le 1)) (PY.and hA (PY.base (hal u) hY)
      (PY.const hA (tgU R FL Pl u = inpR T y.1)))
    exact (h2.congr fun x => (mem_cons_inl y e u).symm).mono hY (by omega)
  · have h1 : PY Dd H Y 0 fun x => Pick FL (load R ch FL lhat (nX nI x) (oX oI x)) l := PY.base (ha.pick l) hY
    have h3 : PY Dd H Y 1 fun x => su FL l.2.2.2 e * Tow.num R ch FL lhat (nX nI x) (oX oI x) (.inr l) ≤
        rkU R FL Pl lhat (nI x) (oI x) u :=
      PY.rel hA (fun s t => su FL l.2.2.2 e * s ≤ t) (CY.base (ha.num (.inr l)) hY) (CY.base (hrk u) hY)
    have h4 : PY Dd H Y 1 fun x => rkU R FL Pl lhat (nI x) (oI x) u <
        (su FL l.2.2.2 e + 1) * Tow.num R ch FL lhat (nX nI x) (oX oI x) (.inr l) :=
      PY.rel hA (fun s t => t < (su FL l.2.2.2 e + 1) * s) (CY.base (ha.num (.inr l)) hY) (CY.base (hrk u) hY)
    have h5 := PY.and hA (h1.mono hY (Nat.zero_le 4)) (PY.and hA ((PY.base (hal u) hY).mono hY (Nat.zero_le 3))
      (PY.and hA ((PY.const hA (tgU R FL Pl u = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e))).mono hY (Nat.zero_le 2))
        (PY.and hA h3 h4)))
    exact h5.congr fun x => (mem_cons_inr l e u).symm

theorem py_cur (ha : After (nX nI) (oX oI) lhat H)
    (hco : ∀ z u, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) ∈ H) (u : Un R FL Pl U0 U1) :
    PY Dd H Y 4 fun x => u ∈ (plan R FL Pl lhat U0 U1).cur (nI x) (oI x) (Fintype.card (Mv T R ch FL)) := by
  have hY := hA.pos
  have h1 : PY Dd H Y 1 fun x => SeenU (nI x) (oI x) u := by
    rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
    · exact PY.rel1 hA (fun s => k.1 < s) (CY.base (ha.n a c) hY)
    · refine (PY.rel1 hA (fun s => k.1 ≤ s) (CY.base (ha.o (eN R FL Pl ν)) hY)).congr fun x => ?_
      have : oX oI x (eN R FL Pl ν) = (oI x ν).1 := by
        unfold oX oo
        rw [Equiv.symm_apply_apply]
      rw [this]
      exact Iff.rfl
  have h2 : PY Dd H Y 2 fun x => ∃ z, u ∈ consM R FL Pl lhat (nI x) (oI x) z :=
    PY.exists_univ hA hB2.zm fun z => PY.base (hco z u) hY
  exact (PY.and hA (h1.mono hY (by omega)) (PY.not hA h2)).congr fun x => (mem_cur u).symm

theorem py_good (ha : After (nX nI) (oX oI) lhat H) (mv : Mv T R ch FL) :
    PY Dd H Y 4 fun x => GoodMv R ch FL lhat (nX nI x) (oX oI x) mv := by
  have hY := hA.pos
  rcases mv with y | l
  · have hc : Fintype.card (kindM R ch FL (.inl y)).Cn ≤ Y := by
      refine (Fintype.card_le_of_injective
        (fun ν : (kindM R ch FL (.inl y)).Cn => (⟨Sum.inl y, ν⟩ : NM R FL (ch := ch))) ?_).trans hB.nm
      intro ν ν' he
      exact eq_of_heq (Sigma.mk.inj he).2
    have h1 : PY Dd H Y 3 fun x => ∀ ν : (kindM R ch FL (.inl y)).Cn, oX oI x ⟨.inl y, ν⟩ =
        Tow.num R ch FL lhat (nX nI x) (oX oI x) (.inl y) :=
      PY.forall_univ hA hc fun ν => PY.rel hA (fun s t => s = t) (CY.base (ha.o _) hY) (CY.base (ha.num _) hY)
    exact h1.mono hY (by omega)
  · have hc : Fintype.card (kindM R ch FL (.inr l)).Cn ≤ Y := card_cn hA hB (rng (nI := nI) (oI := oI)) l
    have h1 : PY Dd H Y 1 fun x => GoodL R ch FL (oX oI x) l (Tow.num R ch FL lhat (nX nI x) (oX oI x) (.inr l)) :=
      PY.rel hA (fun q t => r * b * q ≤ FL.G₁ * t ^ 2) (CY.base (ha.q l) hY) (CY.base (ha.num (.inr l)) hY)
    have h2 : PY Dd H Y 3 fun x => ∀ ν : (kindM R ch FL (.inr l)).Cn,
        Tow.num R ch FL lhat (nX nI x) (oX oI x) (.inr l) ≤ oX oI x ⟨.inr l, ν⟩ :=
      PY.forall_univ hA hc fun ν => PY.rel hA (fun s t => s ≤ t) (CY.base (ha.num _) hY) (CY.base (ha.o _) hY)
    exact PY.and hA (h1.mono hY (by omega)) h2

theorem units_stage (hS : SY inp Y p c H) (ha : After (nX nI) (oX oI) lhat H) :
    ∃ H', SY inp Y p (c + 9) H' ∧ H ⊆ H' ∧ Units nI oI lhat TM H' := by
  have hY := hA.pos
  have hun : Fintype.card (Un R FL Pl U0 U1) ≤ Y ^ 1 := by simpa using hB2.un
  have hzt : Fintype.card (ZM R FL (ch := ch) × Fin TM) ≤ Y ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, pow_two]
    exact Nat.mul_le_mul hB2.zm hB2.tm
  have hmt : Fintype.card (Mv T R ch FL × Fin TM) ≤ Y ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, pow_two]
    exact Nat.mul_le_mul hB.mv hB2.tm
  have hzu : Fintype.card (ZM R FL (ch := ch) × Un R FL Pl U0 U1) ≤ Y ^ 2 := by
    rw [Fintype.card_prod, pow_two]
    exact Nat.mul_le_mul hB2.zm hB2.un
  obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := Un R FL Pl U0 U1)
    (fun u => ind fun x => AlU R FL Pl lhat (nI x) (oI x) u) (a := 2) (e := 1) hun
    (fun u => py_al hA hB hB2 ha u) (by omega)
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (κ := Un R FL Pl U0 U1)
    (fun u x => rkU R FL Pl lhat (nI x) (oI x) u) (a := 2) (e := 1) hun
    (fun u => cy_rk hA hB hB2 f1 u) (by omega)
  have a2 := ha.weaken (u1.trans u2)
  obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (κ := ZM R FL (ch := ch) × Un R FL Pl U0 U1)
    (fun q => ind fun x => q.2 ∈ consM R FL Pl lhat (nI x) (oI x) q.1) (a := 5) (e := 2) hzu
    (fun q => py_cons hA hB hB2 a2 (fun u => u2 (f1 u)) f2 q.1 q.2) (by omega)
  have a3 := a2.weaken u3
  have c3 : ∀ z u, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) ∈ H3 := fun z u => f3 (z, u)
  obtain ⟨H4, s4, u4, f4⟩ := s3.add hA (κ := ZM R FL (ch := ch))
    (fun z x => (consM R FL Pl lhat (nI x) (oI x) z).card) (a := 2) (e := 1) (by simpa using hB2.zm)
    (fun z => by
      classical
      have e : ∀ x, (consM R FL Pl lhat (nI x) (oI x) z).card =
          ∑ u ∈ univ, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) x := by
        intro x
        have h1 : ∀ u, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) x =
            if u ∈ consM R FL Pl lhat (nI x) (oI x) z then 1 else 0 := by
          intro u
          by_cases hu : u ∈ consM R FL Pl lhat (nI x) (oI x) z
          · rw [if_pos hu, ind_true (P := fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) hu]
          · rw [if_neg hu, ind_false (P := fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) hu]
        rw [Finset.sum_congr rfl fun u _ => h1 u, ← Finset.card_filter]
        congr 1
        ext u
        simp
      refine CY.congr ?_ fun x => (e x).symm
      refine CY.sum hA univ hB2.un (fun u _ => CY.base (c3 z u) hY) fun x => hA.lt_of_le ?_
      refine (Finset.sum_le_card_nsmul _ _ 1 fun v _ => ind_le _ _).trans ?_
      rw [smul_eq_mul, mul_one]
      exact hB2.un) (by omega)
  have a4 := a3.weaken u4
  obtain ⟨H5, s5, u5, f5⟩ := s4.add hA (κ := Mv T R ch FL × Fin TM)
    (fun q => ind fun x => q.2.1 < Tow.num R ch FL lhat (nX nI x) (oX oI x) q.1) (a := 1) (e := 2) hmt
    (fun q => PY.rel1 hA (fun s => q.2.1 < s) (CY.base (a4.num q.1) hY)) (by omega)
  obtain ⟨H6, s6, u6, f6⟩ := s5.add hA (κ := ZM R FL (ch := ch) × Fin TM)
    (fun q => ind fun x => (consM R FL Pl lhat (nI x) (oI x) q.1).card ≤ q.2.1 ∧
      q.2.1 < Tow.num R ch FL lhat (nX nI x) (oX oI x) q.1.1) (a := 2) (e := 2) hzt
    (fun q => PY.and hA (PY.rel1 hA (fun s => s ≤ q.2.1) (CY.base (u5 (f4 q.1)) hY))
      (PY.rel1 hA (fun s => q.2.1 < s) (CY.base (u5 (a4.num q.1.1)) hY))) (by omega)
  have c6 : ∀ z u, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) ∈ H6 := fun z u => u6 (u5 (u4 (c3 z u)))
  have a6 := a4.weaken (u5.trans u6)
  obtain ⟨H7, s7, u7, f7⟩ := s6.add hA (κ := Un R FL Pl U0 U1)
    (fun u => ind fun x => u ∈ (plan R FL Pl lhat U0 U1).cur (nI x) (oI x) (Fintype.card (Mv T R ch FL)))
    (a := 4) (e := 1) hun (fun u => py_cur hA hB hB2 a6 c6 u) (by omega)
  have a7 := a6.weaken u7
  obtain ⟨H8, s8, u8, f8⟩ := s7.add hA (κ := Mv T R ch FL)
    (fun mv => ind fun x => GoodMv R ch FL lhat (nX nI x) (oX oI x) mv) (a := 4) (e := 1) (by simpa using hB.mv)
    (fun mv => py_good hA hB hB2 a7 mv) (by omega)
  obtain ⟨H9, s9, u9, f9⟩ := s8.add hA (κ := Unit)
    (fun _ => ind fun x => ∀ mv, GoodMv R ch FL lhat (nX nI x) (oX oI x) mv) (a := 2) (e := 0) (by simp)
    (fun _ => PY.forall_univ hA hB.mv fun mv => PY.base (f8 mv) hY) (by omega)
  have v79 := u8.trans u9
  refine ⟨H9, s9, ?_, ⟨fun z u => v79 (u7 (c6 z u)), fun mv => v79 (a7.num mv), fun mv τ => v79 (u7 (u6 (f5 (mv, τ)))),
    fun z τ => v79 (u7 (f6 (z, τ))), fun u => v79 (f7 u), fun mv => u9 (f8 mv), f9 (), v79 a7.valid⟩⟩
  exact u1.trans (u2.trans (u3.trans (u4.trans (u5.trans (u6.trans (u7.trans v79))))))

end Nc.Tow
