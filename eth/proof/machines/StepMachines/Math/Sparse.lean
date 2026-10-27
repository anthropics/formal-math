/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.GridDefs
public import StepMachines.Math.CodeMore

/-! Names for sparse strings of Bell states, used for the label sets `rowLabels` and `colLabels`.
Here a Bell state is a pair of bits (the type `Bell`), one of four.
A string of n Bell states of which at most c differ from a fixed state s₀ is named by a word of
`capW n c` = n + `tb c` bits, where `tb c` is the number of bits of 3^c:
n bits that mark the positions where the string differs from s₀, then one number below 3^(number of
marks), whose digits
in base 3, lowest first, say which of the three other states stands at the marked positions, in
their order. Rows: s₀ is
the singlet, `(true, true)`, and c = n − i; columns: s₀ is Φ⁺, `(false, false)`, and c = i. -/

@[expose] public section

namespace Groundwork

open Finset
open Groundwork.Prog (tb capW)

/-- The strings of n Bell states with at most c states other than s₀. -/
def sparseLab (s₀ : Bell) (n c : ℕ) : Finset (Fin n → Bell) := univ.filter fun β => #{k | β k ≠ s₀} ≤ c

/-- The three states other than s₀, numbered 0, 1, 2. -/
def oth (s₀ : Bell) (d : ℕ) : Bell :=
  if d = 0 then (s₀.1, !s₀.2) else if d = 1 then (!s₀.1, s₀.2) else (!s₀.1, !s₀.2)

/-- The state at position k of the string named by the word w. -/
def symAt (s₀ : Bell) (n : ℕ) (w : List Bool) (k : ℕ) : Bell :=
  if w.getD k false = true then oth s₀ (ofWord (w.drop n) / 3 ^ (w.take k).count true % 3) else s₀

/-- Is the word w (of n + tb c bits) a name? At most c marks, and the number is below 3^(number of
marks). -/
def validW (n c : ℕ) (w : List Bool) : Bool :=
  decide ((w.take n).count true ≤ c) && decide (ofWord (w.drop n) / 3 ^ (w.take n).count true = 0)

/-! ### The three other states -/

/-- `oth s₀ d` is never s₀. -/
theorem oth_ne (s₀ : Bell) (d : ℕ) : oth s₀ d ≠ s₀ := by
  rcases s₀ with ⟨a, b⟩
  unfold oth
  split_ifs <;> cases a <;> cases b <;> simp

/-- The three numbers 0, 1, 2 name different states. -/
theorem oth_inj : ∀ (s₀ : Bell), ∀ d < 3, ∀ d' < 3, oth s₀ d = oth s₀ d' → d = d' := by
  decide

/-- Every state other than s₀ has a number. -/
theorem exists_oth : ∀ (s₀ b : Bell), b ≠ s₀ → ∃ d < 3, oth s₀ d = b := by
  decide

/-! ### The decoder as a recursion on the list of marks -/

/-- The string named by the marks m and the number Y, read off from left to right: a marked position
takes the lowest
digit of Y in base 3 and removes it. -/
def decL (s₀ : Bell) : List Bool → ℕ → List Bell
  | [], _ => []
  | true :: m, Y => oth s₀ (Y % 3) :: decL s₀ m (Y / 3)
  | false :: m, Y => s₀ :: decL s₀ m Y

theorem length_decL (s₀ : Bell) (m : List Bool) (Y : ℕ) : (decL s₀ m Y).length = m.length := by
  induction m generalizing Y with
  | nil => rfl
  | cons b m ih => cases b <;> simp [decL, ih]

/-- Position k of the recursion is what `symAt` computes directly. -/
theorem getD_decL (s₀ : Bell) (m : List Bool) (Y k : ℕ) : (decL s₀ m Y).getD k s₀ =
    if m.getD k false = true then oth s₀ (Y / 3 ^ (m.take k).count true % 3) else s₀ := by
  induction m generalizing Y k with
  | nil => simp [decL]
  | cons b m ih =>
    cases b with
    | false =>
      cases k with
      | zero => simp [decL]
      | succ k =>
        simp only [decL, List.getD_cons_succ, List.take_succ_cons]
        rw [ih]
        simp
    | true =>
      cases k with
      | zero => simp [decL]
      | succ k =>
        simp only [decL, List.getD_cons_succ, List.take_succ_cons]
        rw [ih]
        simp [pow_succ', Nat.div_div_eq_div_mul]

theorem symAt_eq (s₀ : Bell) {n k : ℕ} (w : List Bool) (hk : k < n) :
    symAt s₀ n w k = (decL s₀ (w.take n) (ofWord (w.drop n))).getD k s₀ := by
  have h1 : (w.take n).getD k false = w.getD k false := by
    simp [List.getD_eq_getElem?_getD, hk]
  rw [getD_decL, h1, List.take_take, min_eq_left hk.le, symAt]

/-- The number of marks among the first n positions. -/
theorem card_getD_range (w : List Bool) (n : ℕ) :
    #{j ∈ range n | w.getD j false = true} = (w.take n).count true := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    cases w with
    | nil => simp
    | cons b w =>
      have h := ih w
      rw [card_filter] at h ⊢
      rw [sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, h, List.take_succ_cons, List.count_cons]
      cases b <;> simp

/-- The string differs from s₀ exactly at the marked positions. -/
theorem card_decL (s₀ : Bell) (m : List Bool) (Y n : ℕ) :
    #{k : Fin n | (decL s₀ m Y).getD k s₀ ≠ s₀} = (m.take n).count true := by
  have h : ∀ j : ℕ, (decL s₀ m Y).getD j s₀ ≠ s₀ ↔ m.getD j false = true := by
    intro j
    rw [getD_decL]
    split_ifs with hj
    · exact ⟨fun _ => hj, fun _ => oth_ne _ _⟩
    · exact ⟨fun h => absurd rfl h, fun h => absurd h hj⟩
  simp only [h]
  rw [← card_getD_range, card_filter, card_filter,
    Fin.sum_univ_eq_sum_range (fun j => if m.getD j false = true then 1 else 0)]

/-- Different names give different strings. -/
theorem decL_inj (s₀ : Bell) (m m' : List Bool) (Y Y' : ℕ) (hY : Y < 3 ^ m.count true)
    (hY' : Y' < 3 ^ m'.count true) (h : decL s₀ m Y = decL s₀ m' Y') : m = m' ∧ Y = Y' := by
  induction m generalizing m' Y Y' with
  | nil =>
    cases m' with
    | nil =>
      simp only [List.count_nil, pow_zero] at hY hY'
      exact ⟨rfl, by omega⟩
    | cons b' m' => cases b' <;> simp [decL] at h
  | cons b m ih =>
    cases m' with
    | nil => cases b <;> simp [decL] at h
    | cons b' m' =>
      cases b <;> cases b'
      · simp only [decL, List.cons.injEq, true_and] at h
        obtain ⟨h1, h2⟩ := ih m' Y Y' (by simpa using hY) (by simpa using hY') h
        exact ⟨by rw [h1], h2⟩
      · simp only [decL, List.cons.injEq] at h
        exact absurd h.1.symm (oth_ne _ _)
      · simp only [decL, List.cons.injEq] at h
        exact absurd h.1 (oth_ne _ _)
      · simp only [decL, List.cons.injEq] at h
        simp only [List.count_cons_self, pow_succ] at hY hY'
        obtain ⟨h1, h2⟩ := ih m' (Y / 3) (Y' / 3) (by omega) (by omega) h.2
        have h3 := oth_inj s₀ _ (Nat.mod_lt Y (by norm_num)) _ (Nat.mod_lt Y' (by norm_num)) h.1
        exact ⟨by rw [h1], by omega⟩

/-- Every string has a name. -/
theorem exists_decL (s₀ : Bell) (L : List Bell) :
    ∃ (m : List Bool) (Y : ℕ), m.length = L.length ∧ Y < 3 ^ m.count true ∧ decL s₀ m Y = L := by
  induction L with
  | nil => exact ⟨[], 0, rfl, by simp, rfl⟩
  | cons b L ih =>
    obtain ⟨m, Y, hm, hY, hd⟩ := ih
    by_cases hb : b = s₀
    · exact ⟨false :: m, Y, by simp [hm], by simpa using hY, by simp [decL, hd, hb]⟩
    · obtain ⟨d, hd3, hdb⟩ := exists_oth s₀ b hb
      refine ⟨true :: m, d + 3 * Y, by simp [hm], ?_, ?_⟩
      · simp only [List.count_cons_self, pow_succ]
        omega
      · have h1 : (d + 3 * Y) % 3 = d := by omega
        have h2 : (d + 3 * Y) / 3 = Y := by omega
        simp [decL, h1, h2, hd, hdb]

/-- What it means to be a valid word. -/
theorem mem_validWords {n c : ℕ} {w : List Bool} :
    w ∈ ((words (capW n c)).filter fun w => validW n c w = true) ↔
      w.length = n + tb c ∧ (w.take n).count true ≤ c ∧ ofWord (w.drop n) < 3 ^ (w.take n).count true := by
  simp [validW, capW, Nat.div_eq_zero_iff]

/-- The valid words name the strings with at most c states other than s₀, one each. -/
theorem sparse_bijOn (s₀ : Bell) (n c : ℕ) :
    Set.BijOn (fun (w : List Bool) (k : Fin n) => symAt s₀ n w k)
      ((words (capW n c)).filter fun w => validW n c w = true : Finset (List Bool)) (sparseLab s₀ n c) := by
  refine ⟨fun w hw => ?_, fun w hw w' hw' h => ?_, fun β hβ => ?_⟩
  · obtain ⟨-, hc, -⟩ := mem_validWords.1 (mem_coe.1 hw)
    refine mem_coe.2 (mem_filter.2 ⟨mem_univ _, ?_⟩)
    have h1 : #{k : Fin n | symAt s₀ n w k ≠ s₀} = ((w.take n).take n).count true := by
      rw [← card_decL s₀ (w.take n) (ofWord (w.drop n)) n]
      exact congrArg card (filter_congr fun k _ => by rw [symAt_eq s₀ w k.2])
    rw [h1, List.take_take, min_self]
    exact hc
  · obtain ⟨hl, -, hY⟩ := mem_validWords.1 (mem_coe.1 hw)
    obtain ⟨hl', -, hY'⟩ := mem_validWords.1 (mem_coe.1 hw')
    have hd : decL s₀ (w.take n) (ofWord (w.drop n)) = decL s₀ (w'.take n) (ofWord (w'.drop n)) := by
      refine List.ext_getElem (by simp [length_decL, hl, hl']) fun j h₁ h₂ => ?_
      have hj : j < n := by
        rw [length_decL, List.length_take] at h₁
        omega
      rw [← List.getD_eq_getElem _ s₀ h₁, ← List.getD_eq_getElem _ s₀ h₂, ← symAt_eq s₀ w hj, ← symAt_eq s₀ w' hj]
      exact congrFun h ⟨j, hj⟩
    obtain ⟨h1, h2⟩ := decL_inj s₀ _ _ _ _ hY hY' hd
    have h3 : w.drop n = w'.drop n := by
      rw [← toWord_ofWord (w.drop n), ← toWord_ofWord (w'.drop n), h2, List.length_drop, List.length_drop, hl, hl']
    rw [← List.take_append_drop n w, ← List.take_append_drop n w', h1, h3]
  · obtain ⟨m, Y, hm, hY, hd⟩ := exists_decL s₀ (List.ofFn β)
    rw [List.length_ofFn] at hm
    have hβk : ∀ k : Fin n, (decL s₀ m Y).getD k s₀ = β k := by
      intro k
      rw [hd, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have hpop : m.count true ≤ c := by
      have h1 := card_decL s₀ m Y n
      rw [← hm, List.take_length, hm] at h1
      rw [← h1]
      simp only [hβk]
      exact (mem_filter.1 (mem_coe.1 hβ)).2
    have hY2 : Y < 2 ^ tb c :=
      hY.trans_le ((Nat.pow_le_pow_right (by norm_num) hpop).trans (Nat.lt_size_self _).le)
    have htake : (m ++ toWord (tb c) Y).take n = m := by rw [← hm, List.take_left]
    have hdrop : (m ++ toWord (tb c) Y).drop n = toWord (tb c) Y := by rw [← hm, List.drop_left]
    refine ⟨m ++ toWord (tb c) Y, mem_coe.2 (mem_validWords.2 ⟨by simp [hm], ?_, ?_⟩), ?_⟩
    · rw [htake]
      exact hpop
    · rw [htake, hdrop, ofWord_toWord hY2]
      exact hY
    · funext k
      change symAt s₀ n _ k = β k
      rw [symAt_eq s₀ _ k.2, htake, hdrop, ofWord_toWord hY2, hβk]

/-- The code of the strings with at most c states other than s₀: the valid words, decoded by
`symAt`. -/
def Code.sparse (s₀ : Bell) (n c : ℕ) : Code (sparseLab s₀ n c) (capW n c) where
  D := (words (capW n c)).filter fun w => validW n c w = true
  dec w := fun k => symAt s₀ n w k
  len _ h := mem_words.1 (mem_filter.1 h).1
  bij := sparse_bijOn s₀ n c

/-- Every position holds s₀ or another state. -/
theorem card_eq_add_card_ne {n : ℕ} (s₀ : Bell) (β : Fin n → Bell) : #{k | β k = s₀} + #{k | β k ≠ s₀} = n := by
  rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]

/-- At least i singlets: at most n − i states other than the singlet. -/
theorem rowLabels_eq {n i : ℕ} (h : i ≤ n) : rowLabels n i = sparseLab (true, true) n (n - i) := by
  ext β
  have key : ∀ a b : ℕ, a + b = n → (i ≤ a ↔ b ≤ n - i) := by omega
  simp only [rowLabels, sparseLab, mem_filter, mem_univ, true_and]
  apply key
  unfold singlets
  convert card_eq_add_card_ne (true, true) β

/-- At most i states other than Φ⁺: the label set for columns. -/
theorem colLabels_eq (n i : ℕ) : colLabels n i = sparseLab (false, false) n i := rfl

/-- A name has at most 4n bits. -/
theorem capW_le {n c : ℕ} (hn : 1 ≤ n) (hc : c ≤ n) : capW n c ≤ 4 * n := by
  have := Prog.tb_le c
  unfold capW
  omega

end Groundwork
