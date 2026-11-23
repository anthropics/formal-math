/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Ov.Core.Basic

/-!
# Equivalence of tensors

The paper identifies tensors that are restrictions of one another (in the subsection "Tensors"). Here they are called equivalent, `Equi`, and this file has the laws of products,
powers, products of families and `push` (giving legs to parties) up to equivalence.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Every tensor is equivalent to itself. -/
theorem Equi.refl (t : Ten K I) : Equi t t := ⟨Restr.refl t, Restr.refl t⟩

/-- Equivalence is symmetric. -/
theorem Equi.symm {s t : Ten K I} (h : Equi s t) : Equi t s := ⟨h.2, h.1⟩

/-- Equivalence is transitive. -/
theorem Equi.trans {s t u : Ten K I} (h : Equi s t) (h' : Equi t u) : Equi s u :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- Products of equivalent tensors are equivalent. -/
theorem Equi.mul {s t s' t' : Ten K I} (h : Equi s s') (h' : Equi t t') :
    Equi (s * t) (s' * t') := ⟨h.1.mul h'.1, h.2.mul h'.2⟩

/-- Giving the legs of equivalent tensors to parties. -/
theorem Equi.push (π : J → I) {s t : Ten K J} (h : Equi s t) :
    Equi (push π s) (push π t) := ⟨h.1.push π, h.2.push π⟩

/-- Tensors whose index sets correspond to one another, leg by leg, with equal entries are
equivalent. -/
theorem Equi.of_equiv {s t : Ten K I} (e : ∀ p, s.ι p ≃ t.ι p)
    (h : ∀ x, s.val x = t.val (fun p => e p (x p))) : Equi s t :=
  ⟨Restr.of_map' (fun p => e p) h, Restr.of_map' (fun p => (e p).symm) fun y => by
    rw [h]; simp⟩

/-! ### Products -/

/-- The product is commutative. -/
theorem Equi.mul_comm (s t : Ten K I) : Equi (s * t) (t * s) :=
  Equi.of_equiv (fun _ => Equiv.prodComm _ _) fun _ => _root_.mul_comm _ _

/-- The product is associative. -/
theorem Equi.mul_assoc (s t u : Ten K I) : Equi (s * t * u) (s * (t * u)) :=
  Equi.of_equiv (fun _ => Equiv.prodAssoc _ _ _) fun _ => _root_.mul_assoc _ _ _

/-- 1 is neutral. -/
theorem Equi.one_mul (t : Ten K I) : Equi (1 * t) t :=
  Equi.of_equiv (fun p => Equiv.punitProd (t.ι p)) fun _ => _root_.one_mul _

/-- 1 is neutral. -/
theorem Equi.mul_one (t : Ten K I) : Equi (t * 1) t :=
  Equi.of_equiv (fun p => Equiv.prodPUnit (t.ι p)) fun _ => _root_.mul_one _

section Prod

variable {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- Renaming the factors of a product. -/
theorem Equi.prod_reindex (b : κ → Ten K I) (e : κ' ≃ κ) :
    Equi (Ten.prod b) (Ten.prod fun k => b (e k)) :=
  Equi.symm <| Equi.of_equiv (fun p => Equiv.piCongrLeft (fun k => (b k).ι p) e) fun x => by
    rw [prod_val, prod_val]
    refine Fintype.prod_equiv e _ _ fun k => ?_
    congr 1
    funext p
    exact (Equiv.piCongrLeft_apply_apply (fun k => (b k).ι p) e (x p) k).symm

/-- The product of the empty family. -/
theorem Equi.prod_empty [IsEmpty κ] (b : κ → Ten K I) : Equi (Ten.prod b) 1 :=
  Equi.of_equiv (fun p => show (∀ k, (b k).ι p) ≃ Unit from Equiv.equivPUnit _)
    fun x => by rw [prod_val]; simp

/-- The product of a family with one member. -/
theorem Equi.prod_unique [Unique κ] (b : κ → Ten K I) : Equi (Ten.prod b) (b default) :=
  Equi.of_equiv (fun p => show (∀ k, (b k).ι p) ≃ (b default).ι p from Equiv.piUnique _)
    fun x => by rw [prod_val]; simp; rfl

/-- The product over a disjoint union. -/
theorem Equi.prod_sum (b : κ ⊕ κ' → Ten K I) :
    Equi (Ten.prod b) (Ten.prod (fun k => b (Sum.inl k)) * Ten.prod (fun k => b (Sum.inr k))) :=
  Equi.of_equiv (fun p => Equiv.sumPiEquivProdPi fun k => (b k).ι p)
    fun x => by rw [prod_val, Fintype.prod_sum_type]; rfl

end Prod

/-- The product of a family indexed by 0, …, n is its first member times the product of the others. -/
theorem Equi.prod_fin_succ {n : ℕ} (b : Fin (n + 1) → Ten K I) :
    Equi (Ten.prod b) (b 0 * Ten.prod fun k : Fin n => b k.succ) :=
  Equi.of_equiv (fun p => (Fin.consEquiv fun k => (b k).ι p).symm)
    fun x => by rw [prod_val, Fin.prod_univ_succ]; rfl

/-- The product of a family of two tensors. -/
theorem Equi.prod_fin_two (b : Fin 2 → Ten K I) : Equi (Ten.prod b) (b 0 * b 1) :=
  (Equi.prod_fin_succ b).trans ((Equi.refl _).mul (Equi.prod_unique _))

/-! ### Powers -/

/-- The power with exponent 0. -/
theorem Equi.kpow_zero (t : Ten K I) : Equi (Ten.kpow t 0) 1 :=
  Equi.prod_empty (fun _ : Fin 0 => t)

/-- The power with exponent k + 1. -/
theorem Equi.kpow_succ (t : Ten K I) (k : ℕ) : Equi (Ten.kpow t (k + 1)) (t * Ten.kpow t k) :=
  Equi.prod_fin_succ (fun _ : Fin (k + 1) => t)

/-! ### Giving legs to parties -/

section Push

variable {L : Type} [Fintype L] [DecidableEq L]

/-- Giving each leg to the party of its own name changes nothing, up to equivalence. -/
theorem Equi.push_id (t : Ten K I) : Equi (Ten.push id t) t :=
  Equi.of_equiv
    (fun q => ⟨fun y => y ⟨q, rfl⟩, fun a j => (show q = j.1 from j.2.symm) ▸ a, fun y => by
        funext j; obtain ⟨j, hj⟩ := j; cases hj; rfl, fun a => rfl⟩)
    fun x => rfl

/-- Giving legs away twice. -/
theorem Equi.push_push (π : J → I) (ρ : L → J) (t : Ten K L) :
    Equi (Ten.push π (Ten.push ρ t)) (Ten.push (π ∘ ρ) t) :=
  Equi.of_equiv
    (fun q => ⟨fun y i => y ⟨ρ i.1, i.2⟩ ⟨i.1, rfl⟩, fun z j i => z ⟨i.1, by
        rw [Function.comp, i.2]; exact j.2⟩, fun y => by
        funext j i
        obtain ⟨j, hj⟩ := j
        obtain ⟨i, hi⟩ := i
        cases hj
        cases hi
        rfl, fun _ => rfl⟩)
    fun _ => rfl

/-- Giving legs away, for a product. -/
theorem Equi.push_mul (π : J → I) (s t : Ten K J) :
    Equi (Ten.push π (s * t)) (Ten.push π s * Ten.push π t) :=
  Equi.of_equiv
    (fun _ => ⟨fun y => (fun j => (y j).1, fun j => (y j).2), fun z j => (z.1 j, z.2 j),
      fun _ => rfl, fun _ => rfl⟩)
    fun _ => rfl

/-- Giving legs away, for 1. -/
theorem Equi.push_one (π : J → I) : Equi (Ten.push π (1 : Ten K J)) 1 :=
  Equi.of_equiv
    (fun q => show (({j : J // π j = q}) → Unit) ≃ Unit from Equiv.equivPUnit _) fun _ => rfl

/-- Giving legs away, for the product of a family. -/
theorem Equi.push_prod {κ : Type} [Fintype κ] [DecidableEq κ] (π : J → I) (b : κ → Ten K J) :
    Equi (Ten.push π (Ten.prod b)) (Ten.prod fun k => Ten.push π (b k)) :=
  Equi.of_equiv (fun _ => Equiv.piComm _) fun _ => rfl

/-- Giving legs away, for a power. -/
theorem Equi.push_kpow (π : J → I) (t : Ten K J) (k : ℕ) :
    Equi (Ten.push π (Ten.kpow t k)) (Ten.kpow (Ten.push π t) k) :=
  Equi.push_prod π (fun _ : Fin k => t)

end Push

end Ten

end Ov
