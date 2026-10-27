/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Field.Defs
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Log

/-! # Lists and finite sets

No arithmetic in the finite field of the proof of Lemma 13 is done here; only lists and finite sets.
`wordsL s` lists every word of s bits once; each Γ_u (`gamW`) is listed as an increasing list of
numbers below m; `famD m a` may filter first and map afterwards (`famD_eq`); and
`isFamily_list`: if a list L without repetitions enumerates, through an injective D, the index set Ω
of sets Γ with (a), (b), (c) of Lemma 13 (Family of checks), and G u lists the set Γ (D u),
then the places of the list `L.map G` index a family with (a), (b), (c). -/

public section

namespace VariableBound.Fld

open Groundwork Finset

/-! ### The words -/

/-- The members of `wordsL s` are the words of s bits. -/
theorem mem_wordsL {s : ℕ} {w : List Bool} : w ∈ wordsL s ↔ w.length = s := by
  simp only [wordsL, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨y, _, rfl⟩; simp
  · rintro rfl; exact ⟨ofWord w, ofWord_lt w, toWord_ofWord w⟩

/-- No word occurs twice in `wordsL s`. -/
theorem nodup_wordsL (s : ℕ) : (wordsL s).Nodup :=
  List.Nodup.map_on (fun x hx y hy h => toWord_injOn s (by simpa using hx) (by simpa using hy) h) List.nodup_range

/-- The members of the four-fold product are the quadruples of words of s bits. -/
theorem mem_quad {s : ℕ} {u : List Bool × List Bool × List Bool × List Bool} :
    u ∈ wordsL s ×ˢ wordsL s ×ˢ wordsL s ×ˢ wordsL s ↔ u.1.length = s ∧ u.2.1.length = s ∧ u.2.2.1.length = s ∧ u.2.2.2.length = s := by
  obtain ⟨u1, u2, u3, u4⟩ := u
  simp only [List.mem_product, mem_wordsL]

/-- No quadruple occurs twice in the four-fold product. -/
theorem nodup_quad (s : ℕ) : (wordsL s ×ˢ wordsL s ×ˢ wordsL s ×ˢ wordsL s).Nodup :=
  (nodup_wordsL s).product ((nodup_wordsL s).product ((nodup_wordsL s).product (nodup_wordsL s)))

/-! ### The members of the family -/

/-- Γ_u is listed in increasing order. -/
theorem gamW_sorted (m a : ℕ) (g : List Bool) (u : List Bool × List Bool × List Bool × List Bool) : (gamW m a g u).Pairwise (· < ·) :=
  List.Pairwise.sublist List.filter_sublist List.pairwise_lt_range

/-- Γ_u is listed without repetitions. -/
theorem gamW_nodup (m a : ℕ) (g : List Bool) (u : List Bool × List Bool × List Bool × List Bool) : (gamW m a g u).Nodup :=
  List.Nodup.sublist List.filter_sublist List.nodup_range

/-- The numbers in the list of Γ_u are below m. -/
theorem gamW_lt (m a : ℕ) (g : List Bool) (u : List Bool × List Bool × List Bool × List Bool) : ∀ E ∈ gamW m a g u, E < m :=
  fun _ hE => List.mem_range.1 (List.mem_of_mem_filter hE)

/-- A list of numbers below m without repetitions has as many members as the set it lists. -/
theorem card_setD {m : ℕ} {l : List ℕ} (h1 : l.Nodup) (h2 : ∀ E ∈ l, E < m) : #(setD m l) = l.length := by
  rw [← List.toFinset_card_of_nodup h1]
  refine Finset.card_bij (fun E _ => E.val) (fun E hE => ?_) (fun _ _ _ _ h => Fin.ext h) fun E hE => ?_
  · simpa [setD] using hE
  · have hE' : E ∈ l := by simpa using hE
    exact ⟨⟨E, h2 E hE'⟩, by simpa [setD] using hE', rfl⟩

/-- The list of the family: first leave out the u with 2^a·|Γ_u| > 16m, then list the sets. -/
theorem famD_eq (m a : ℕ) : famD m a =
    ((wordsL (sD m) ×ˢ wordsL (sD m) ×ˢ wordsL (sD m) ×ˢ wordsL (sD m)).filter fun u =>
      decide (2 ^ a * (gamW m a (modW (sD m)) u).length ≤ 16 * m)).map (gamW m a (modW (sD m))) := by
  rw [famD, List.filter_map]; rfl

/-! ### From an index set to the places of a list -/

/-- (a), (b), (c) of Lemma 13 (Family of checks) pass along an injective map φ of index sets with Ω =
φ(Ω'). -/
theorem isFamily_comap {E ι ι' : Type} [Fintype E] [DecidableEq E] {v : ℕ} {Ω : Finset ι} {Γ : ι → Finset E} (h : AppVariables.IsFamily v Ω Γ)
    (φ : ι' ↪ ι) (Ω' : Finset ι') (hΩ : Ω = Ω'.map φ) : AppVariables.IsFamily v Ω' fun i => Γ (φ i) := by
  subst hΩ
  refine ⟨fun u hu => h.a _ (Finset.mem_map_of_mem φ hu), fun e => ?_, fun V hV => ?_⟩
  · have := h.b e
    rwa [Finset.filter_map, Finset.card_map, Finset.card_map] at this
  · have := h.c V hV
    rwa [Finset.filter_map, Finset.card_map, Finset.card_map] at this

/-- Let the list L have no repetitions, let D be injective on its members with image Ω, and let G u
list the set Γ (D u) for every member u of L. If the sets Γ_w, w ∈ Ω, have (a), (b), (c) of
Lemma 13 (Family of checks) for v, then the list `L.map G` has |Ω| members, and they, indexed by
their places, have (a), (b), (c) for v. -/
theorem isFamily_list {m v : ℕ} {ι U : Type} (Ω : Finset ι) (Γ : ι → Finset (Fin m)) (L : List U) (D : U → ι) (G : U → List ℕ)
    (hL : L.Nodup) (hD : ∀ u ∈ L, ∀ u' ∈ L, D u = D u' → u = u') (hΩ : ∀ w, w ∈ Ω ↔ ∃ u ∈ L, D u = w)
    (hG : ∀ u ∈ L, setD m (G u) = Γ (D u)) (h : AppVariables.IsFamily v Ω Γ) :
    #Ω = (L.map G).length ∧ AppVariables.IsFamily v (univ : Finset (Fin (L.map G).length)) fun i => setD m ((L.map G).get i) := by
  have hlen : (L.map G).length = L.length := List.length_map G
  let φ : Fin (L.map G).length ↪ ι := ⟨fun i => D (L.get (i.cast hlen)), fun i j hij => by
    have := hD _ (List.get_mem L _) _ (List.get_mem L _) hij
    have := (List.Nodup.get_inj_iff hL).1 this
    exact Fin.cast_injective hlen this⟩
  have hmap : Ω = (univ : Finset (Fin (L.map G).length)).map φ := by
    ext w
    rw [hΩ, Finset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem hu
      exact ⟨i.cast hlen.symm, Finset.mem_univ _, rfl⟩
    · rintro ⟨i, _, rfl⟩
      exact ⟨_, List.get_mem L _, rfl⟩
  refine ⟨by rw [hmap, Finset.card_map, Finset.card_univ, Fintype.card_fin], ?_⟩
  have key := isFamily_comap h φ univ hmap
  have e : (fun i : Fin (L.map G).length => setD m ((L.map G).get i)) = fun i => Γ (φ i) := by
    funext i
    have : (L.map G).get i = G (L.get (i.cast hlen)) := by simp
    rw [this, hG _ (List.get_mem L _)]
    rfl
  rw [e]
  exact key

/-! ### The number of bits -/

/-- 16m ≤ 2^s. -/
theorem sD_le (m : ℕ) : 16 * m ≤ 2 ^ sD m := Nat.le_pow_clog (by norm_num) _

/-- 2^s < 32m, for m ≥ 1. -/
theorem sD_lt {m : ℕ} (hm : 1 ≤ m) : 2 ^ sD m < 32 * m := by
  have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := 16 * m) (by omega)
  have h2 : 0 < Nat.clog 2 (16 * m) := Nat.clog_pos (by norm_num) (by omega)
  have h3 : 2 ^ sD m = 2 * 2 ^ (Nat.clog 2 (16 * m)).pred := by
    rw [sD, ← pow_succ', Nat.pred_eq_sub_one]; congr 1; omega
  omega

/-- s ≥ 1, for m ≥ 1. -/
theorem one_le_sD {m : ℕ} (hm : 1 ≤ m) : 1 ≤ sD m := Nat.clog_pos (by norm_num) (by omega)

end VariableBound.Fld
