/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.Defs

/-!
# Contraction, and the power of a law
-/

set_option linter.unusedSectionVars false

namespace Nc.G

open Finset

section Contract

variable {F : Type} [CommRing F] {Ro Cn ι : Type} [Fintype Ro] [DecidableEq Ro] [Fintype Cn] [DecidableEq Cn]
  [Fintype ι] {S : ι → Cn → Type} [∀ i ν, Fintype (S i ν)] {Z : Type} [Fintype Z] (c d : Cn → Ro)
  (code : (ν : Cn) → (i : ι) → S i ν → Z)

open Classical in
/-- The table of a role with code words on its channels. -/
noncomputable def codeTab (p : Ro) (G : (i : ι) → ((ν : {ν // c ν = p ∨ d ν = p}) → S i ν) → F) (z : Cn → Z) : F :=
  ∑ i, ∑ g : (ν : {ν // c ν = p ∨ d ν = p}) → S i ν, if ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (g ν) = z ν then G i g else 0

/-- Only the code words on the channels of the role matter. -/
theorem codeTab_congr {p : Ro} {G : (i : ι) → ((ν : {ν // c ν = p ∨ d ν = p}) → S i ν) → F} {z z' : Cn → Z}
    (h : ∀ ν, c ν = p ∨ d ν = p → z ν = z' ν) : codeTab c d code p G z = codeTab c d code p G z' := by
  classical
  unfold codeTab
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => ?_
  have : (∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (g ν) = z ν) ↔
      ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (g ν) = z' ν :=
    forall_congr' fun ν => by rw [h ν.1 ν.2]
  by_cases h1 : ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (g ν) = z ν
  · rw [if_pos h1, if_pos (this.1 h1)]
  · rw [if_neg h1, if_neg fun h2 => h1 (this.2 h2)]

variable {c d code}

open Classical in
/-- **Contraction.** Tables with code words, summed over the code words on all channels, give the sum of the products
of the tables. -/
theorem contract [Nonempty Ro]
    (hcode : ∀ ν, Function.Injective fun q : Σ i, S i ν => code ν q.1 q.2)
    (conn : ∀ f : Ro → ι, (∀ ν, f (c ν) = f (d ν)) → ∀ p p', f p = f p')
    (G : (p : Ro) → (i : ι) → ((ν : {ν // c ν = p ∨ d ν = p}) → S i ν) → F) :
    (∑ z : Cn → Z, ∏ p, codeTab c d code p (G p) z) = ∑ i, ∑ g : ∀ ν, S i ν, ∏ p, G p i fun ν => g ν := by
  have p0 : Ro := Classical.arbitrary Ro
  have hL : ∀ z : Cn → Z, (∏ p, codeTab c d code p (G p) z) =
      ∑ f : (p : Ro) → Σ i, (ν : {ν // c ν = p ∨ d ν = p}) → S i ν,
        if ∀ p, ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν (f p).1 ((f p).2 ν) = z ν then ∏ p, G p (f p).1 (f p).2 else 0 := by
    intro z
    have e1 : ∀ p, codeTab c d code p (G p) z = ∑ q : Σ i, (ν : {ν // c ν = p ∨ d ν = p}) → S i ν,
        if ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν q.1 (q.2 ν) = z ν then G p q.1 q.2 else 0 := by
      intro p
      rw [codeTab, Fintype.sum_sigma]
    simp only [e1]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_imp_iff]
  simp only [hL]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_sigma (fun q : Σ i, ∀ ν, S i ν => ∏ p, G p q.1 fun ν => q.2 ν)]
  symm
  refine Finset.sum_bij_ne_zero (fun q _ _ => (fun ν => code ν q.1 (q.2 ν), fun p => ⟨q.1, fun ν => q.2 ν⟩)) ?_ ?_ ?_ ?_
  · exact fun _ _ _ => Finset.mem_univ _
  · rintro ⟨i, g⟩ - - ⟨i', g'⟩ - - heq
    have h2 := congrArg Prod.snd heq
    have hi : i = i' := congrArg Sigma.fst (congrFun h2 p0)
    subst hi
    congr 1
    funext ν
    have h4 := congrFun h2 (c ν)
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h4
    exact congrFun h4 ⟨ν, Or.inl rfl⟩
  · rintro ⟨z, f⟩ - hne
    have hcond : ∀ p, ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν (f p).1 ((f p).2 ν) = z ν := by
      by_contra hc
      rw [if_neg hc] at hne
      exact hne rfl
    rw [if_pos hcond] at hne
    have hpair : ∀ ν, (⟨(f (c ν)).1, (f (c ν)).2 ⟨ν, Or.inl rfl⟩⟩ : Σ i, S i ν) =
        ⟨(f (d ν)).1, (f (d ν)).2 ⟨ν, Or.inr rfl⟩⟩ := by
      intro ν
      apply hcode ν
      simp only
      rw [hcond (c ν) ⟨ν, Or.inl rfl⟩, hcond (d ν) ⟨ν, Or.inr rfl⟩]
    have hall : ∀ p, (f p).1 = (f p0).1 := fun p =>
      conn (fun p => (f p).1) (fun ν => by
        have := congrArg Sigma.fst (hpair ν)
        exact this) p p0
    obtain ⟨i, hi⟩ : ∃ i, i = (f p0).1 := ⟨_, rfl⟩
    have hex : ∀ p, ∃ gp : (ν : {ν // c ν = p ∨ d ν = p}) → S i ν, f p = ⟨i, gp⟩ := by
      intro p
      have h := (hall p).trans hi.symm
      generalize f p = q at h ⊢
      obtain ⟨i', g'⟩ := q
      have h : i' = i := h
      subst h
      exact ⟨g', rfl⟩
    choose gp hgp using hex
    have hcond' : ∀ p, ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (gp p ν) = z ν := by
      intro p
      have := hcond p
      rw [hgp p] at this
      exact this
    let g : ∀ ν, S i ν := fun ν => gp (c ν) ⟨ν, Or.inl rfl⟩
    have hg : ∀ p, (fun ν : {ν // c ν = p ∨ d ν = p} => g ν) = gp p := by
      intro p
      funext ν
      obtain ⟨ν, hν⟩ := ν
      rcases hν with rfl | rfl
      · rfl
      · have := hpair ν
        rw [hgp (c ν), hgp (d ν)] at this
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
        exact this
    have hprod : (∏ p, G p i fun ν => g ν) = ∏ p, G p (f p).1 (f p).2 := by
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [hgp p, hg p]
    refine ⟨⟨i, g⟩, Finset.mem_univ _, ?_, ?_⟩
    · rw [hprod]
      exact hne
    · ext1
      · funext ν
        exact hcond' (c ν) ⟨ν, Or.inl rfl⟩
      · funext p
        show (⟨i, fun ν => g ν⟩ : Σ i, (ν : {ν // c ν = p ∨ d ν = p}) → S i ν) = f p
        rw [hgp p, hg p]
  · rintro ⟨i, g⟩ - -
    simp only
    rw [if_pos]
    exact fun p ν => trivial

end Contract

section Pow

variable {F : Type} [CommRing F] (L : Law F)

/-- **The power of a law**: `B` blocks. -/
theorem Law.pow (B : ℕ) (X : L.Ro → Fin B → L.Sl → Bool) :
    (if ∀ e k, X (L.a e) k e = X (L.b e) k e then (1 : F) else 0) =
      ∑ i : Fin B → L.I, ∑ g : (ν : L.Cn) → (k : Fin B) → Fin (L.len (i k) ν) → Bool,
        ∏ p, ∏ k, L.tab p (i k) (fun e => X p k e) fun ν => g ν k := by
  have h1 : (if ∀ e k, X (L.a e) k e = X (L.b e) k e then (1 : F) else 0) =
      ∏ k, if ∀ e, X (L.a e) k e = X (L.b e) k e then (1 : F) else 0 := by
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_imp_iff, Finset.prod_const_one]
    exact if_congr forall_comm rfl rfl
  rw [h1]
  have h2 : ∀ k, (if ∀ e, X (L.a e) k e = X (L.b e) k e then (1 : F) else 0) =
      ∑ i, ∑ g : (ν : L.Cn) → Fin (L.len i ν) → Bool, ∏ p, L.tab p i (fun e => X p k e) fun ν => g ν := fun k =>
    L.law fun p => X p k
  rw [Finset.prod_congr rfl fun k _ => h2 k]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fintype.sum_equiv (Equiv.piComm fun (k : Fin B) (ν : L.Cn) => Fin (L.len (i k) ν) → Bool) _ _ fun g => ?_
  rw [Finset.prod_comm]
  rfl

theorem Law.conn_pow (B : ℕ) (f : L.Ro → Fin B → L.I) (h : ∀ ν, f (L.c ν) = f (L.d ν)) : ∀ p p', f p = f p' := by
  intro p p'
  funext k
  exact L.conn (fun p => f p k) (fun ν => congrFun (h ν) k) p p'

end Pow

end Nc.G
