/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Slp3
import Nc.Tow.Tree

/-!
# The program of the tower plan: the tree
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b D J r m Uu AA U0 U1 : ℕ} {T : Tower h b D J r}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T}
variable {Inp ι : Type} {Dd Y p c : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}
variable (hh : 0 < h) {L : Inp → Tg T m AA → ℕ}

section Bounds

variable (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hL : ∀ x τ, L x τ ≤ Wb R ch FL U0 U1)
include hA hB hL

theorem lev_le (x : Inp) (j : ℕ) (e : T.Ed j) : lev (L x) j e ≤ Y := by
  unfold lev
  split_ifs
  · exact (hL x _).trans hB.w
  · exact Nat.zero_le _

theorem fb_leS (x : Inp) {j : ℕ} (hj : j ≤ J) (c : T.X j) : fb (lev (L x)) j c ≤ Y ^ 2 := by
  unfold fb Tower.bet
  calc _ ≤ ∑ _e : T.Ed j, Y := by
        refine Finset.sum_le_sum fun e _ => ?_
        split_ifs
        · exact lev_le hA hB hL x j e
        · exact Nat.zero_le _
    _ = Fintype.card (T.Ed j) * Y := by simp
    _ ≤ Y * Y := Nat.mul_le_mul_right _ (hB.ed ⟨j, Nat.lt_succ_of_le hj⟩)
    _ = Y ^ 2 := by ring

end Bounds

/-- Parents, as bits. -/
def HostOk (hh : 0 < h) (L : Inp → Tg T m AA → ℕ) (H : Set (Inp → ℕ)) : Prop :=
  ∀ (j : ℕ) (_ : j < J) (c : T.X j) (c' : T.X (j + 1)), ind (fun x => hostj hh (lev (L x)) c = c') ∈ H

variable (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hL : ∀ x τ, L x τ ≤ Wb R ch FL U0 U1)
include hA hB hL

omit hL in
theorem host_stage (hS : SY inp Y p c H) (hi : ∀ j i, ind (fun x => IsMin (L x) j i) ∈ H) :
    ∃ H', SY inp Y p (c + 1) H' ∧ H ⊆ H' ∧ HostOk hh L H' := by
  classical
  have hY := hA.pos
  have hc : Fintype.card (Σ j : Fin J, T.X j × T.X (j + 1)) ≤ Y ^ 2 := by
    rw [pow_two]
    refine le_trans (Fintype.card_le_of_injective (β := Nd T × Nd T)
      (fun q => (nd T q.1 q.1.2.le q.2.1, nd T (q.1 + 1) q.1.2 q.2.2)) ?_) (by
      rw [Fintype.card_prod]; exact Nat.mul_le_mul hB.nd hB.nd)
    rintro ⟨j, x, y⟩ ⟨j', x', y'⟩ he
    obtain ⟨h1, h2⟩ := Prod.mk.inj he
    have hj : j = j' := by
      by_contra hne
      exact nd_ne (fun hv => hne (Fin.ext hv)) h1
    subst hj
    have e1 := nd_inj.1 h1
    have e2 := nd_inj.1 h2
    simp only at e1 e2
    rw [e1, e2]
  obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := Σ j : Fin J, T.X j × T.X (j + 1))
    (fun q => ind fun x => hostj hh (lev (L x)) q.2.1 = q.2.2) (a := 2) (e := 2) hc (fun q => by
      have h1 : PY Dd H Y 2 fun x => ∃ i ∈ univ.filter
          (fun i => T.host i (T.vx i q.2.1) = q.2.2), IsMin (L x) q.1.castSucc i :=
        PY.exists_mem hA _ ((card_filter_le _ _).trans (by simpa using hB.h)) fun i _ => PY.base (hi _ _) hY
      refine h1.congr fun x => ?_
      unfold hostj
      constructor
      · rintro ⟨i, hi, hm⟩
        rw [isMin_iff hh] at hm
        subst hm
        exact (mem_filter.1 hi).2
      · intro he
        exact ⟨imin hh (lev (L x)) q.1, mem_filter.2 ⟨mem_univ _, he⟩, (isMin_iff hh (L x) q.1.castSucc _).2 rfl⟩)
    (by omega)
  exact ⟨H1, s1, u1, fun j hj c c' => f1 ⟨⟨j, hj⟩, c, c'⟩⟩

omit hh in
/-- The loads at the chambers. -/
theorem fb_stage (hS : SY inp Y p c H) (hm : ∀ τ, (fun x => L x τ) ∈ H) :
    ∃ H', SY inp Y p (c + 1) H' ∧ H ⊆ H' ∧ ∀ (j : ℕ) (_ : j ≤ J) (x' : T.X j),
      (fun x => fb (lev (L x)) j x') ∈ H' := by
  classical
  have hY := hA.pos
  have hX : Fintype.card (Σ j : Fin (J + 1), T.X j) ≤ Y ^ 1 := by
    rw [pow_one]
    refine le_trans (Fintype.card_le_of_injective (β := Nd T) some (Option.some_injective _)) hB.nd
  obtain ⟨H2, s2, u2, f2⟩ := hS.add hA (κ := Σ j : Fin (J + 1), T.X j) (fun q x => fb (lev (L x)) q.1 q.2)
    (a := 2) (e := 1) hX (fun q => by
      have e : ∀ x, fb (lev (L x)) q.1 q.2 =
          ∑ e ∈ univ.filter (fun e : T.Ed q.1 => T.e0 e = q.2 ∨ T.e1 e = q.2), L x (.edge q.1 e) := by
        intro x
        unfold fb Tower.bet lev
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [dif_pos q.1.2]
      refine CY.congr ?_ fun x => (e x).symm
      refine CY.sum hA _ ((card_filter_le _ _).trans (hB.ed q.1)) (fun e _ => CY.base (hm _) hY) fun x => ?_
      rw [← e]
      refine hA.lt_of_le3 ((fb_leS hA hB hL x (Nat.le_of_lt_succ q.1.2) q.2).trans ?_)
      have : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY (by omega)
      omega) (by omega)
  exact ⟨H2, s2, u2, fun j hj x' => f2 ⟨⟨j, Nat.lt_succ_of_le hj⟩, x'⟩⟩

end Nc.Tow
