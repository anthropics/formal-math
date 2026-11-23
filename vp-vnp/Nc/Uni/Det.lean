/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.Rules

/-!
# The universal machine is deterministic but for the guesses and the input
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The rule for a mode and the kind of the record that is loaded. -/
def nextR (supp : Finset (List Bool)) : Md (Nm supp) → Kd → Option (Ru supp)
  | .S0, .N => some (.inl .s0)
  | .S1, .N => some (.inl .s1)
  | .PR, .PA => some (.inl .pa)
  | .PR, .PB => some (.inl .pb)
  | .PR, .PE => some (.inl .pe)
  | .S2, .C => some (.inl (.s2 true))
  | .S2, .N => some (.inl (.s2 false))
  | .E, .N => some (.inl .en)
  | .E, .C => some (.inl .ec)
  | .D j, .C => if h : j.1 < 10 then some (.inl (.dc ⟨j.1, h⟩)) else none
  | .D 0, .N => some (.inl .d0)
  | .D 1, .N => some (.inl .d1)
  | .D 2, .N => some (.inl .d2)
  | .D 3, .N => some (.inl .d3)
  | .D 4, .N => some (.inl .d4)
  | .D 5, .N => some (.inl .d5)
  | .D 6, .N => some (.inl .d6)
  | .D 9, .N => some (.inl .d9)
  | .K4, .C => some (.inl (.k4 true))
  | .K4, .N => some (.inl (.k4 false))
  | .K5, .C => some (.inl (.k5 true))
  | .K5, .N => some (.inl (.k5 false))
  | .K6, .C => some (.inl (.k6 true))
  | .K6, .N => some (.inl (.k6 false))
  | .R, .HD => some (.inl .rhd)
  | .R, .TL => some (.inl .rtl)
  | .R, .CO1 => some (.inl .rco1)
  | .R, .CO2 => some (.inl .rco2)
  | .R, .IT => some (.inl .rit)
  | .R, .RU1 => some (.inl .rru1)
  | .R, .RU2 => some (.inl .rru2)
  | .R, .HT => some (.inl .rht)
  | .R, .TH => if h : [] ∈ pre supp then some (.inr (.inl ⟨(), h⟩)) else none
  | .H, .C => some (.inl (.h true))
  | .H, .N => some (.inl (.h false))
  | .T, .C => some (.inl (.t true))
  | .T, .N => some (.inl (.t false))
  | .I, .C => some (.inl .ic)
  | .I, .N => some (.inl .inn)
  | .I1, .C => some (.inl (.i1 true))
  | .I1, .N => some (.inl (.i1 false))
  | .I2, .C => some (.inl (.i2 true))
  | .I2, .N => some (.inl (.i2 false))
  | .TH p, .N => some (.inr (.inr (.inl p)))
  | .TH p, .C => some (.inr (.inr (.inr (.inl p))))
  | .TB p, .C => if h : p.1 ++ [true] ∈ pre supp then some (.inr (.inr (.inr (.inr ⟨(p, ⟨_, h⟩, true), rfl⟩)))) else none
  | .TB p, .N => if h : p.1 ++ [false] ∈ pre supp then some (.inr (.inr (.inr (.inr ⟨(p, ⟨_, h⟩, false), rfl⟩)))) else none
  | _, _ => none

/-- The rules that are chosen by the input or by a guess. -/
def Sp (r : Ru supp) : Prop := r = .inl .pr0 ∨ r = .inl .pr1 ∨ ∃ b, r = .inl (.d7 b)

theorem nextR_of (r : Ru supp) (hr : ¬ Sp r) : nextR supp (rule θ supp r).src (rule θ supp r).lk = some r := by
  rcases r with r | u | p | p | x
  · cases r with
    | pr0 => exact absurd (Or.inl rfl) hr
    | pr1 => exact absurd (Or.inr (Or.inl rfl)) hr
    | d7 b => exact absurd (Or.inr (Or.inr ⟨b, rfl⟩)) hr
    | s2 b => cases b <;> rfl
    | k4 b => cases b <;> rfl
    | k5 b => cases b <;> rfl
    | k6 b => cases b <;> rfl
    | h b => cases b <;> rfl
    | t b => cases b <;> rfl
    | i1 b => cases b <;> rfl
    | i2 b => cases b <;> rfl
    | dc j =>
      have : (j.castSucc : Fin 11).1 < 10 := j.2
      exact dif_pos this
    | _ => rfl
  · exact dif_pos u.2
  · rfl
  · rfl
  · obtain ⟨⟨p, p', b⟩, hx⟩ := x
    obtain ⟨p', hp'⟩ := p'
    simp only at hx
    subst hx
    cases b
    · exact dif_pos hp'
    · exact dif_pos hp'

theorem rd_of (r : Ru supp) (hr : ¬ Sp r) : (rule θ supp r).rd = none := by
  rcases r with r | u | p | p | x
  · cases r with
    | pr0 => exact absurd (Or.inl rfl) hr
    | pr1 => exact absurd (Or.inr (Or.inl rfl)) hr
    | d7 b => exact absurd (Or.inr (Or.inr ⟨b, rfl⟩)) hr
    | _ => rfl
  all_goals rfl

theorem src_ne (r : Ru supp) : (rule θ supp r).src ≠ .Z := by
  rcases r with r | u | p | p | x
  · cases r with
    | d7 b => cases b <;> simp [rule, ruleA, rl]
    | _ => simp [rule, ruleA, rl]
  all_goals simp [rule, rl]

/-- States of the universal machine. -/
abbrev St (supp : Finset (List Bool)) := Mach.State (M := Md (Nm supp)) (K := Kd)

/-- A heap that can be used. -/
structure OKs (σ : St supp) : Prop where
  nil : ((.N, ![0, 0, 0, 0]) : Rec Kd) ∈ σ.heap
  le : ∀ c ∈ σ.heap, c.2 0 ≤ σ.n
  fn : ∀ c ∈ σ.heap, ∀ c' ∈ σ.heap, c.2 0 = c'.2 0 → c = c'
  r0 : σ.regs 0 = 0

/-- The values of the variables. -/
def envOf (σ : St supp) (p q s : ℕ) : Fin 9 → ℕ :=
  ![σ.regs 0, σ.regs 1, σ.regs 2, σ.regs 3, σ.regs 4, p, q, s, σ.n + 1]

/-- The state after a step. -/
noncomputable def nx (θ : List Bool → A) (σ : St supp) (r : Ru supp) (p q s : ℕ) : St supp :=
  Mach.nxt (P := UM θ supp) σ (r, envOf σ p q s)

theorem dr_zero (r : Ru supp) : (rule θ supp r).dr 0 = 0 := by
  rcases r with r | u | p | p | x
  · cases r with
    | d7 b => cases b <;> rfl
    | _ => rfl
  all_goals rfl

theorem OKs.nx {σ : St supp} (hσ : OKs σ) (r : Ru supp) (p q s : ℕ) : OKs (nx θ σ r p q s) := by
  have ha : (Mach.al (P := UM θ supp) (r, envOf σ p q s)).2 0 = σ.n + 1 := rfl
  constructor
  · exact List.mem_append_left _ hσ.nil
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact (hσ.le c hc).trans (Nat.le_succ _)
    · rw [List.mem_singleton] at hc
      subst hc
      exact ha.le
  · intro c hc c' hc' e
    rcases List.mem_append.1 hc with hc | hc <;> rcases List.mem_append.1 hc' with hc' | hc'
    · exact hσ.fn c hc c' hc' e
    · rw [List.mem_singleton] at hc'
      subst hc'
      have := hσ.le c hc
      omega
    · rw [List.mem_singleton] at hc
      subst hc
      have := hσ.le c' hc'
      omega
    · rw [List.mem_singleton] at hc hc'
      rw [hc, hc']
  · change envOf σ p q s ((rule θ supp r).dr 0) = 0
    rw [dr_zero]
    exact hσ.r0

theorem heap_nx (σ : St supp) (r : Ru supp) (p q s : ℕ) : σ.heap ⊆ (nx θ σ r p q s).heap :=
  fun _ hc => List.mem_append_left _ hc

/-- The record that is allocated is in the heap. -/
theorem new_nx (σ : St supp) (r : Ru supp) (p q s : ℕ) :
    ((rule θ supp r).ak, ![σ.n + 1, envOf σ p q s ((rule θ supp r).af 0), envOf σ p q s ((rule θ supp r).af 1),
      envOf σ p q s ((rule θ supp r).af 2)]) ∈ (nx θ σ r p q s).heap :=
  List.mem_append_right _ (List.mem_singleton_self _)

theorem inp_nx (σ : St supp) (r : Ru supp) (p q s : ℕ) :
    (nx θ σ r p q s).inp = σ.inp.drop (rule θ supp r).rd.toList.length := rfl

/-- The possible steps. -/
theorem fire_iff {σ : St supp} (hσ : OKs σ) {κ : Kd} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (laM σ.mode), p, q, s]) ∈ σ.heap) (st : (UM θ supp).Step) :
    Mach.Fire σ st ↔ (rule θ supp st.1).src = σ.mode ∧ (rule θ supp st.1).lk = κ ∧
      (rule θ supp st.1).rd.toList <+: σ.inp ∧ st.2 = envOf σ p q s := by
  have hla : ∀ r, (UM θ supp).la r = laM (rule θ supp r).src := fun r => la_eq θ supp r
  constructor
  · intro hf
    have hs : (rule θ supp st.1).src = σ.mode := hf.src
    have h0 : (Mach.ld st).2 0 = σ.regs (laM σ.mode) := by
      have : (Mach.ld st).2 0 = st.2 (rv ((UM θ supp).la st.1)) := rfl
      rw [this, hf.regs, hla, hs]
    have h1 := hσ.fn _ hf.load _ hrec h0
    have h2 := congrArg Prod.fst h1
    have h3 := fun i => congrFun (congrArg Prod.snd h1) i
    refine ⟨hs, h2, hf.read, ?_⟩
    funext i
    refine Mach.env_cases (fun i => st.2 i = envOf σ p q s i) (fun j => ?_) (h3 1) (h3 2) (h3 3) hf.fresh i
    rw [hf.regs]
    fin_cases j <;> rfl
  · rintro ⟨hs, hk, hr, he⟩
    have hregs : ∀ j, st.2 (rv j) = σ.regs j := by
      intro j
      rw [he]
      fin_cases j <;> rfl
    refine ⟨hs, hregs, by rw [he]; rfl, ?_, hr⟩
    have : Mach.ld st = (κ, ![σ.regs (laM σ.mode), p, q, s]) := by
      refine Prod.ext hk ?_
      have h0 : st.2 (rv ((UM θ supp).la st.1)) = σ.regs (laM σ.mode) := by rw [hregs, hla, hs]
      change ![st.2 (rv ((UM θ supp).la st.1)), st.2 5, st.2 6, st.2 7] = _
      rw [h0, he]
      rfl
    rw [this]
    exact hrec

/-- A step that is forced. -/
theorem sumTo_rule {σ : St supp} (hσ : OKs σ) {κ : Kd} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (laM σ.mode), p, q, s]) ∈ σ.heap) (r : Ru supp) (hr : nextR supp σ.mode κ = some r)
    (hm : σ.mode ≠ .P) (hd : ¬ (σ.mode = .D 7 ∧ κ = .N)) (hs : (rule θ supp r).src = σ.mode) (hk : (rule θ supp r).lk = κ)
    {S : A} {B : ℤ} (h : Mach.SumTo (UM θ supp) (nx θ σ r p q s) S B) :
    Mach.SumTo (UM θ supp) σ ((rule θ supp r).wt * S) (B + 1) := by
  have hz : σ.mode ≠ (UM θ supp).mh := by
    rw [← hs]
    exact src_ne r
  have hsp : ∀ r' : Ru supp, (rule θ supp r').src = σ.mode → (rule θ supp r').lk = κ → ¬ Sp r' := by
    rintro r' h1 h2 (rfl | rfl | ⟨b, rfl⟩)
    · exact hm h1.symm
    · exact hm h1.symm
    · cases b
      · exact hd ⟨h1.symm, h2.symm⟩
      · exact hd ⟨h1.symm, h2.symm⟩
  refine Mach.SumTo.one hz (r, envOf σ p q s) (fun st' => ?_) h
  rw [fire_iff hσ hrec]
  constructor
  · rintro ⟨h1, h2, -, h4⟩
    have h5 := nextR_of (θ := θ) st'.1 (hsp _ h1 h2)
    rw [h1, h2, hr] at h5
    exact Prod.ext (Option.some_injective _ h5).symm h4
  · rintro rfl
    refine ⟨hs, hk, ?_, rfl⟩
    rw [rd_of r (hsp r hs hk)]
    exact List.nil_prefix

/-- No rule applies. -/
theorem sumTo_stuck {σ : St supp} (hσ : OKs σ) {κ : Kd} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (laM σ.mode), p, q, s]) ∈ σ.heap) (hr : nextR supp σ.mode κ = none)
    (hm : σ.mode ≠ .P) (hd : ¬ (σ.mode = .D 7 ∧ κ = .N)) (hz : σ.mode ≠ .Z) (B : ℤ) :
    Mach.SumTo (UM θ supp) σ 0 B := by
  refine Mach.SumTo.none hz (fun st hf => ?_) B
  rw [fire_iff hσ hrec] at hf
  obtain ⟨h1, h2, -, -⟩ := hf
  have hsp : ¬ Sp st.1 := by
    rintro (h | h | ⟨b, h⟩)
    · rw [h] at h1; exact hm h1.symm
    · rw [h] at h1; exact hm h1.symm
    · rw [h] at h1 h2
      cases b
      · exact hd ⟨h1.symm, h2.symm⟩
      · exact hd ⟨h1.symm, h2.symm⟩
  have h5 := nextR_of (θ := θ) st.1 hsp
  rw [h1, h2, hr] at h5
  exact absurd h5 (by simp)

end Nc.Uni
