/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.RunDefs
public import ClauseBound.ParityChecks.Approx

/-! # The truncated potential is num / den

A state of the choice of the checks is (Ls, cur, e): the complete checks, the part of the current
check chosen so far, the number e of clauses already decided for it. With j the number of
complete checks, k = r − 1 − j and p = 1/nb, the four terms of the truncated potential of that state
are
5^k·numP/(2·8^k·nb^i₀) (`Num.tUpar_eq`), numI/(8mr) (`Num.Uinc_eq`), numR/(8r(nb+1)^m)
(`Num.Urow_eq`) and numC/(8m(nb+1)^r) (`Num.Ucol_eq`),
and over the common denominator `den` their sum has the numerator `num` (`num_div_den`). The sums
over the checks 0, …, r − 1 are split into the complete checks, the current check and the
later, empty checks. The auxiliary statements are in the namespace `ClauseBound.ParityChecks.Num`. -/

public section

namespace ClauseBound.ParityChecks

open Finset _root_.ParityChecks

variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))

/-- A list of clauses without repetition, all below e. -/
@[expose] def ChkOK (e : ℕ) (L : Chk) : Prop := L.Nodup ∧ ∀ x ∈ L, x < e

namespace Num

/-! ### Lists and sums -/

/-- The sum of a list of values at 0, …, n − 1. -/
theorem list_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- A sum over the first entries of a list of checks. -/
theorem sum_getD {M : Type} [AddCommMonoid M] (g : Chk → M) (Ls t : List Chk) :
    ∑ i ∈ range Ls.length, g ((Ls ++ t).getD i []) = (Ls.map g).sum := by
  induction Ls with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    congr 1

/-- A sum over 0, …, r − 1, split at j. -/
theorem sum_split {M : Type} [AddCommMonoid M] (f : ℕ → M) {j r : ℕ} (hj : j < r) :
    ∑ i ∈ range r, f i = ∑ i ∈ range j, f i + f j + ∑ i ∈ range (r - 1 - j), f (j + 1 + i) := by
  have h : r = (j + 1) + (r - 1 - j) := by omega
  conv_lhs => rw [h]
  rw [Finset.sum_range_add, Finset.sum_range_succ]

/-- The current check. -/
theorem getD_mid (Ls : List Chk) (cur : Chk) : (Ls ++ [cur]).getD Ls.length [] = cur := by
  simp [List.getD_eq_getElem?_getD]

/-- The later checks are empty. -/
theorem getD_late (Ls : List Chk) (cur : Chk) (i : ℕ) : (Ls ++ [cur]).getD (Ls.length + 1 + i) [] = [] := by
  apply List.getD_eq_default
  simp only [List.length_append, List.length_singleton]
  omega

/-- The number of lists that contain x, as a sum. -/
theorem countP_eq_sum (x : ℕ) (Ls : List Chk) :
    (Ls.countP fun L => decide (x ∈ L)) = (Ls.map fun L => if x ∈ L then 1 else 0).sum := by
  induction Ls with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
    by_cases h : x ∈ a <;> simp [h, add_comm]

/-- The set of a list without repetition has as many elements as the list. -/
theorem card_filter_mem {m : ℕ} {L : Chk} (hn : L.Nodup) (hl : ∀ x ∈ L, x < m) : #(univ.filter fun x : Fin m => x.val ∈ L) = L.length := by
  rw [← List.toFinset_card_of_nodup hn, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext a
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, List.mem_toFinset]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro ha; exact ⟨⟨a, hl a ha⟩, ha, rfl⟩

/-- m − e clauses are not yet decided. -/
theorem card_Dset (m e : ℕ) : #(Dset m e) = m - e := by
  unfold Dset
  rw [← Nat.card_Ico, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext a
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.isLt⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨a, h2⟩, h1, rfl⟩

/-- 2^a/(1 + p)^c over the denominator (nb + 1)^n, for c ≤ n. -/
theorem frac (nb a c n : ℕ) (hnb : 1 ≤ nb) (hc : c ≤ n) :
    (2 : ℚ) ^ a / (1 + pr nb) ^ c = ((2 ^ a * nb ^ c * (nb + 1) ^ (n - c) : ℕ) : ℚ) / ((nb : ℚ) + 1) ^ n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
  have h0 : (nb : ℚ) ≠ 0 := by exact_mod_cast (by omega : nb ≠ 0)
  have h1 : (nb : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (1 : ℚ) + 1 / nb = (nb + 1) / nb := by field_simp
  rw [Nat.add_sub_cancel_left, pow_add]
  unfold pr
  push_cast
  rw [h2, div_pow]
  field_simp

end Num

/-! ### The state -/

/-- A check as a set has as many elements as its list. -/
theorem card_lam {Ls : List Chk} (hL : ∀ L ∈ Ls, ChkOK q.m L) (j : ℕ) : #(lam q.m Ls j) = (Ls.getD j []).length := by
  unfold lam
  rcases Nat.lt_or_ge j Ls.length with h | h
  · have hmem : Ls.getD j [] ∈ Ls := by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
    exact Num.card_filter_mem (hL _ hmem).1 (hL _ hmem).2
  · rw [List.getD_eq_default _ _ h]; simp

/-- The state (Ls, cur, e) is a state in the sense of `IsState`. -/
theorem isState {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hc : ChkOK e cur) :
    IsState q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) := by
  refine ⟨hj, fun j' hj' => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j' = Ls.length + 1 + i := ⟨j' - (Ls.length + 1), by omega⟩
    unfold lam
    rw [Num.getD_late]
    simp
  · rw [Finset.disjoint_left]
    intro x hx hx'
    unfold lam at hx
    rw [Num.getD_mid] at hx
    have h1 := hc.2 _ (Finset.mem_filter.1 hx).2
    have h2 := (Finset.mem_filter.1 hx').2
    omega

/-- The common denominator is positive. -/
theorem den_pos (hnb : 1 ≤ q.nb) (hm : 1 ≤ q.m) (hr : 1 ≤ q.r) (j : ℕ) : 0 < q.den j := by
  unfold Par.den
  positivity

namespace Num

variable {q}

/-! ### The four terms -/

/-- All checks of the state are lists without repetition of clauses below m. -/
theorem all_ok {Ls : List Chk} {cur : Chk} {e : ℕ} (hL : ∀ L ∈ Ls, ChkOK q.m L) (hc : ChkOK e cur) (he : e ≤ q.m) :
    ∀ L ∈ Ls ++ [cur], ChkOK q.m L := by
  intro L hLm
  rcases List.mem_append.1 hLm with h | h
  · exact hL L h
  · rw [List.mem_singleton.1 h]
    exact ⟨hc.1, fun x hx => lt_of_lt_of_le (hc.2 x hx) he⟩

/-- For an earlier check all clauses are decided. -/
theorem undRow_early {m e j i : ℕ} (h : i < j) : undRow j (Dset m e) i = 0 := by
  unfold undRow; rw [if_pos h]

/-- For the current check m − e clauses are not yet decided. -/
theorem undRow_mid (m e j : ℕ) : undRow j (Dset m e) j = m - e := by
  unfold undRow; rw [if_neg (lt_irrefl j), if_pos rfl, card_Dset]

/-- For a later check no clause is decided. -/
theorem undRow_late (m e j i : ℕ) : undRow j (Dset m e) (j + 1 + i) = m := by
  unfold undRow; rw [if_neg (by omega), if_neg (by omega), Fintype.card_fin]

/-- The number of pairs (check, clause in it). -/
theorem sum_card {Ls : List Chk} {cur : Chk} (hall : ∀ L ∈ Ls ++ [cur], ChkOK q.m L) (hj : Ls.length < q.r) :
    ∑ j' ∈ range q.r, #(lam q.m (Ls ++ [cur]) j') = (Ls.map List.length).sum + cur.length := by
  simp_rw [card_lam q hall]
  rw [sum_split _ hj, sum_getD List.length Ls [cur], getD_mid]
  simp only [getD_late, List.length_nil, sum_const_zero, add_zero]

/-- The number of undecided pairs. -/
theorem sum_undRow (m e : ℕ) {j r : ℕ} (hj : j < r) : ∑ j' ∈ range r, undRow j (Dset m e) j' = (m - e) + (r - 1 - j) * m := by
  rw [sum_split _ hj, Finset.sum_eq_zero fun i hi => undRow_early (mem_range.1 hi), undRow_mid]
  simp [undRow_late]

/-- Υ_inc = numI/(8mr). -/
theorem Uinc_eq (hnb : 1 ≤ q.nb) (hm : 1 ≤ q.m) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r)
    (hall : ∀ L ∈ Ls ++ [cur], ChkOK q.m L) :
    Uinc q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) = (q.numI Ls cur e : ℚ) / (8 * q.m * q.r) := by
  have h0 : (q.nb : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.nb ≠ 0)
  have h1 : (q.m : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.m ≠ 0)
  have h2 : (q.r : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.r ≠ 0)
  unfold Uinc Par.numI Par.k
  rw [sum_card hall hj, sum_undRow _ _ hj, Fintype.card_fin]
  generalize (Ls.map List.length).sum + cur.length = I
  generalize q.m - e + (q.r - 1 - Ls.length) * q.m = Und
  unfold pr
  push_cast
  field_simp

/-- The numerators of the terms of Υ_row add up to numR. -/
theorem sum_row {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hall : ∀ L ∈ Ls ++ [cur], ChkOK q.m L) (he : e ≤ q.m) :
    ∑ j' ∈ range q.r, 2 ^ #(lam q.m (Ls ++ [cur]) j') * q.nb ^ (q.m - undRow Ls.length (Dset q.m e) j') *
      (q.nb + 1) ^ (q.m - (q.m - undRow Ls.length (Dset q.m e) j')) = q.numR Ls cur e := by
  simp_rw [card_lam q hall]
  rw [sum_split _ hj, undRow_mid, getD_mid, Nat.sub_sub_self he]
  have h1 : ∑ i ∈ range Ls.length, 2 ^ ((Ls ++ [cur]).getD i []).length * q.nb ^ (q.m - undRow Ls.length (Dset q.m e) i) *
      (q.nb + 1) ^ (q.m - (q.m - undRow Ls.length (Dset q.m e) i)) = (Ls.map fun L => 2 ^ L.length * q.nb ^ q.m).sum := by
    rw [← sum_getD (fun L => 2 ^ L.length * q.nb ^ q.m) Ls [cur]]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [undRow_early (mem_range.1 hi)]
    simp
  rw [h1]
  simp only [undRow_late, getD_late, List.length_nil, pow_zero, Nat.sub_self, Nat.sub_zero, one_mul, sum_const, card_range, smul_eq_mul]
  rfl

/-- Υ_row = numR/(8r(nb+1)^m). -/
theorem Urow_eq (hnb : 1 ≤ q.nb) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r)
    (hall : ∀ L ∈ Ls ++ [cur], ChkOK q.m L) (he : e ≤ q.m) :
    Urow q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) = (q.numR Ls cur e : ℚ) / (8 * q.r * ((q.nb : ℚ) + 1) ^ q.m) := by
  have h2 : (q.r : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.r ≠ 0)
  have h3 : ((q.nb : ℚ) + 1) ^ q.m ≠ 0 := by positivity
  unfold Urow
  rw [Fintype.card_fin, Finset.sum_congr rfl fun j' _ => frac q.nb _ _ q.m hnb (Nat.sub_le _ _), ← Finset.sum_div, ← Nat.cast_sum,
    sum_row hj hall he]
  field_simp

/-- The number of checks that contain the clause x. -/
theorem card_col {Ls : List Chk} (cur : Chk) (hj : Ls.length < q.r) (x : Fin q.m) :
    #{j' ∈ range q.r | x ∈ lam q.m (Ls ++ [cur]) j'} = Par.colOf Ls cur x.val := by
  rw [Finset.card_filter, sum_split _ hj]
  simp only [lam, mem_filter, mem_univ, true_and]
  rw [sum_getD (fun L => if x.val ∈ L then 1 else 0) Ls [cur], getD_mid]
  simp only [getD_late, List.not_mem_nil, if_false, sum_const_zero, add_zero, Par.colOf, countP_eq_sum]

/-- The number of checks for which the clause x is decided. -/
theorem sub_undCol {e j : ℕ} (hj : j < q.r) (x : Fin q.m) : q.r - undCol q.r j (Dset q.m e) x = j + if x.val < e then 1 else 0 := by
  unfold undCol Dset
  simp only [mem_filter, mem_univ, true_and]
  by_cases h : e ≤ x.val
  · rw [if_pos h, if_neg (by omega)]; omega
  · rw [if_neg h, if_pos (by omega)]; omega

/-- The numerators of the terms of Υ_col add up to numC. -/
theorem sum_col {Ls : List Chk} (cur : Chk) (e : ℕ) (hj : Ls.length < q.r) :
    ∑ x : Fin q.m, 2 ^ #{j' ∈ range q.r | x ∈ lam q.m (Ls ++ [cur]) j'} * q.nb ^ (q.r - undCol q.r Ls.length (Dset q.m e) x) *
      (q.nb + 1) ^ (q.r - (q.r - undCol q.r Ls.length (Dset q.m e) x)) = q.numC Ls cur e := by
  simp_rw [card_col cur hj, sub_undCol hj]
  unfold Par.numC
  rw [list_sum_range, ← Fin.sum_univ_eq_sum_range]

/-- Υ_col = numC/(8m(nb+1)^r). -/
theorem Ucol_eq (hnb : 1 ≤ q.nb) (hm : 1 ≤ q.m) {Ls : List Chk} (cur : Chk) (e : ℕ) (hj : Ls.length < q.r) :
    Ucol q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) = (q.numC Ls cur e : ℚ) / (8 * q.m * ((q.nb : ℚ) + 1) ^ q.r) := by
  have h1 : (q.m : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.m ≠ 0)
  have h3 : ((q.nb : ℚ) + 1) ^ q.r ≠ 0 := by positivity
  unfold Ucol
  rw [Fintype.card_fin, Finset.sum_congr rfl fun x _ => frac q.nb _ _ q.r hnb (Nat.sub_le _ _), ← Finset.sum_div, ← Nat.cast_sum,
    sum_col cur e hj]
  field_simp

/-- numP = nb^i₀·(A + Σ_{i ≤ i₀} (−2p)^i·B_i). -/
theorem numP_cast (hnb : 1 ≤ q.nb) (A : ℤ) (B : ℕ → ℤ) :
    (q.numP A B : ℚ) = (q.nb : ℚ) ^ q.i₀ * ((A : ℚ) + ∑ i ∈ range (q.i₀ + 1), (-2 * pr q.nb) ^ i * (B i : ℚ)) := by
  have h0 : (q.nb : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.nb ≠ 0)
  unfold Par.numP
  rw [list_sum_range]
  push_cast
  rw [mul_add, Finset.mul_sum, mul_comm (A : ℚ)]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (mem_range.1 hi))
  rw [hd, Nat.add_sub_cancel_left, pow_add]
  unfold pr
  rw [mul_pow, one_div, inv_pow]
  field_simp

/-- The truncated Υ_par = (5/8)^k·½·numP/nb^i₀. -/
theorem tUpar_eq (hnb : 1 ≤ q.nb) (j : ℕ) (Λ : ℕ → Finset (Fin q.m)) (D : Finset (Fin q.m)) :
    tUpar V q.nb q.r q.i₀ j Λ D =
      (5 / 8) ^ q.k j * (1 / 2) * ((q.numP (Aint V q.nb j Λ) (fun i => Bint V q.nb i j Λ D) : ℚ) / (q.nb : ℚ) ^ q.i₀) := by
  have h0 : (q.nb : ℚ) ^ q.i₀ ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q.nb ≠ 0))
  rw [Approx.compute, numP_cast hnb, mul_div_cancel_left₀ _ h0]
  rfl

end Num

/-- The truncated potential is num / den. -/
theorem num_div_den (hnb : 1 ≤ q.nb) (hm : 1 ≤ q.m) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hL : ∀ L ∈ Ls, ChkOK q.m L)
    (hc : ChkOK e cur) (he : e ≤ q.m) :
    (q.num (Aint V q.nb Ls.length (lam q.m (Ls ++ [cur]))) (fun i => Bint V q.nb i Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)) Ls cur e : ℚ) / q.den Ls.length
      = tUpar V q.nb q.r q.i₀ Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) + Uinc q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)
        + Urow q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) + Ucol q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) := by
  have hall := Num.all_ok hL hc he
  have h0 : (q.nb : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.nb ≠ 0)
  have h1 : (q.m : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.m ≠ 0)
  have h2 : (q.r : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.r ≠ 0)
  have h3 : (q.nb : ℚ) + 1 ≠ 0 := by positivity
  rw [Num.tUpar_eq V hnb, Num.Uinc_eq hnb hm hj hall, Num.Urow_eq hnb hj hall he, Num.Ucol_eq hnb hm cur e hj]
  unfold Par.num Par.den
  generalize q.numP _ _ = nP
  generalize q.numI Ls cur e = nI
  generalize q.numR Ls cur e = nR
  generalize q.numC Ls cur e = nC
  generalize q.k Ls.length = k
  push_cast
  rw [div_pow, pow_add]
  field_simp
  ring

end ClauseBound.ParityChecks
