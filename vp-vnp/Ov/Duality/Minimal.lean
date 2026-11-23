/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Ov.Core.Equi
import Ov.Duality.PreSpec
import Ov.Duality.Abstract

/-!
# Tensors up to equivalence

Tensors that are restrictions of one another are identified; their classes form a commutative monoid with a covering
relation (`Ov.Duality.Abstract`). The proofs of Proposition prop:gauge and Theorem thm:duality (`Paper/Gauges.lean`) and of
Proposition prop:extend (`Paper/Extension.lean`) work there.
-/

namespace Ov

open Finset Duality

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

namespace Duality

/-- Tensors up to equivalence. -/
def tenSetoid (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] : Setoid (Ten K I) where
  r := Ten.Equi
  iseqv := ⟨Ten.Equi.refl, Ten.Equi.symm, Ten.Equi.trans⟩

/-- The classes of tensors over I under equivalence. -/
def Cls (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] : Type 1 :=
  Quotient (tenSetoid K I)

/-- The class of a tensor. -/
def cls (t : Ten K I) : Cls K I := Quotient.mk (tenSetoid K I) t

theorem cls_eq {s t : Ten K I} : cls s = cls t ↔ Ten.Equi s t :=
  ⟨fun h => Quotient.exact (s := tenSetoid K I) h, fun h => Quotient.sound (s := tenSetoid K I) h⟩

/-- A tensor of a given class. -/
noncomputable def rep (m : Cls K I) : Ten K I := Quotient.out (s := tenSetoid K I) m

@[simp] theorem cls_rep (m : Cls K I) : cls (rep m) = m := Quotient.out_eq _

theorem rep_cls (t : Ten K I) : Ten.Equi (rep (cls t)) t := cls_eq.1 (cls_rep _)

/-- The classes form a commutative monoid under the product. -/
noncomputable instance : CommMonoid (Cls K I) where
  one := cls 1
  mul x y := cls (rep x * rep y)
  mul_assoc x y z := by
    refine cls_eq.2 ?_
    exact (((rep_cls _).mul (Ten.Equi.refl _)).trans (Ten.Equi.mul_assoc _ _ _)).trans
      ((Ten.Equi.refl _).mul (rep_cls _).symm)
  one_mul x := by
    conv_rhs => rw [← cls_rep x]
    exact cls_eq.2 (((rep_cls _).mul (Ten.Equi.refl _)).trans (Ten.Equi.one_mul _))
  mul_one x := by
    conv_rhs => rw [← cls_rep x]
    exact cls_eq.2 (((Ten.Equi.refl _).mul (rep_cls _)).trans (Ten.Equi.mul_one _))
  mul_comm x y := cls_eq.2 (Ten.Equi.mul_comm _ _)

theorem cls_one : cls (1 : Ten K I) = 1 := rfl

theorem cls_mul (s t : Ten K I) : cls (s * t) = cls s * cls t :=
  cls_eq.2 ((rep_cls s).symm.mul (rep_cls t).symm)

theorem cls_kpow (t : Ten K I) (n : ℕ) : cls (Ten.kpow t n) = cls t ^ n := by
  induction n with
  | zero => rw [pow_zero, ← cls_one]; exact cls_eq.2 (Ten.Equi.kpow_zero t)
  | succ n ih => rw [pow_succ', ← ih, ← cls_mul]; exact cls_eq.2 (Ten.Equi.kpow_succ t n)

/-- The covering relation on classes: sums of restrictions. -/
noncomputable def tenCover (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] :
    Cover (Cls K I) where
  cov t b := Ten.SumRestr (rep t) (fun k => rep (b k))
  refl t := (Ten.Restr.refl _).sumRestr
  bind h h' := h.bind h'
  mul {κ _ t b} s h := by
    have h1 : Ten.SumRestr (rep t * rep s) (fun k => rep (b k) * rep s) := by
      have h2 := (h.mul (Ten.Restr.refl (rep s)).sumRestr).reindex (Equiv.prodPUnit κ).symm
      exact h2
    exact ((rep_cls _).1.trans_sum h1).mono fun k => (rep_cls _).2

theorem tenCover_cov {κ : Type} [Fintype κ] {t : Ten K I} {b : κ → Ten K I} :
    (tenCover K I).cov (cls t) (fun k => cls (b k)) ↔ Ten.SumRestr t b :=
  ⟨fun h => ((rep_cls t).2.trans_sum h).mono fun k => (rep_cls (b k)).1,
    fun h => ((rep_cls t).1.trans_sum h).mono fun k => (rep_cls (b k)).2⟩

/-- Equivalent tensors have the same value. -/
theorem _root_.Ov.PreSpec.congr (P : PreSpec K I) {s t : Ten K I} (h : Ten.Equi s t) :
    P.p s = P.p t := le_antisymm (P.mono h.1) (P.mono h.2)

/-- A gauge as a function on classes. -/
noncomputable def onCls (P : PreSpec K I) (m : Cls K I) : ℝ := P.p (rep m)

@[simp] theorem onCls_cls (P : PreSpec K I) (t : Ten K I) : onCls P (cls t) = P.p t :=
  P.congr (rep_cls t)

theorem isPre_onCls (P : PreSpec K I) : IsPre (tenCover K I) (onCls P) where
  nonneg _ := P.nonneg _
  one := by rw [← cls_one, onCls_cls, P.one]
  mul_le s t := by
    rw [← cls_rep s, ← cls_rep t, ← cls_mul, onCls_cls, onCls_cls, onCls_cls]
    exact P.mul_le _ _
  le_sum t b h := P.le_sum _ _ h

/-- The gauge given by a function on classes. -/
def ofCls {q : Cls K I → ℝ} (h : IsPre (tenCover K I) q) : PreSpec K I where
  p t := q (cls t)
  nonneg _ := h.nonneg _
  one := h.one
  mul_le s t := by rw [cls_mul]; exact h.mul_le _ _
  le_sum s b hb := h.le_sum _ _ (tenCover_cov.2 hb)

theorem keeps_onCls {P : PreSpec K I} {x y : Ten K I} {c : ℝ} (h : ∀ t, P.p (t * x) ≤ c * P.p (t * y)) :
    Duality.Keeps (onCls P) (cls x) (cls y) c := by
  intro m
  rw [← cls_rep m, ← cls_mul, ← cls_mul, onCls_cls, onCls_cls]
  exact h _

end Duality

end Ov
