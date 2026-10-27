/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FreeCode.Defs
import FreeCode.Code
import Mathlib.Tactic

/-! # Definition 6 with the code that does not depend on k: a reader

No sentence of the paper stands behind this file: the paper fixes no code. `readFree` reads 1ⁿ0 and
then goes once through the remaining bits, one step (`stepR`) per bit, keeping this state:
two bits that say where it is (between clauses; in a clause, before a mark; inside the bits of a
literal; past the end of the formula), the bits of the literal that is being read, the literals of
the clause that is being read, and the clauses read so far; all three lists last member first, and a
literal as its word of bits.
At the end the lists are turned round and every word of bits is read as a literal.
`readFree_enc_append`: on the code of φ followed by ANY bits the reader returns (n in unary, φ with
numbers as variables). `reads_readFree` is the case of no further bits. That the reader is
polynomial time is proved in proof/consequences/FreeCode/ReaderCert.lean. -/

@[expose] public section

namespace FreeCode

open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

/-- The state of the reader: two bits for the place (00 between clauses, 01 in a clause before a
mark, 10 inside a literal, 11 past the end), the bits of the literal being read, the literals of the
clause being read, the clauses read; each list last member first. -/
abbrev RState : Type := Bool × Bool × List Bool × List (List Bool) × List (List (List Bool))

/-- One bit e is read; w is the number of bits of a literal. -/
def stepR (w : ℕ) (s : RState) (e : Bool) : RState :=
  bif s.1 then
    (bif s.2.1 then s
     else bif decide (s.2.2.1.length + 1 = w) then (false, true, [], (e :: s.2.2.1) :: s.2.2.2.1, s.2.2.2.2)
       else (true, false, e :: s.2.2.1, s.2.2.2.1, s.2.2.2.2))
  else
    (bif s.2.1 then (bif e then (true, false, [], s.2.2.2.1, s.2.2.2.2) else (false, false, [], [], s.2.2.2.1 :: s.2.2.2.2))
     else (bif e then (false, true, [], [], s.2.2.2.2) else (true, true, [], [], s.2.2.2.2)))

/-- The state after all bits that follow 1ⁿ0 have been read. -/
def scanR (x : List Bool) : RState := (x.dropWhile id).tail.foldl (stepR (width (x.takeWhile id).length)) (false, false, [], [], [])

/-- The reader: n in unary, and the clauses read, every word of bits as a literal. -/
def readFree (x : List Bool) : List Unit × Fml :=
  (List.replicate (x.takeWhile id).length (), (scanR x).2.2.2.2.reverse.map fun cl => cl.reverse.map fun cur => (slotDec (ofWord cur.reverse)).getD (0, false))

end FreeCode

public section

namespace FreeCode

open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

/-- The ones in front of the first zero. -/
theorem takeWhile_header (n : ℕ) (l : List Bool) : (List.replicate n true ++ false :: l).takeWhile id = List.replicate n true := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

/-- What stands from the first zero on. -/
theorem dropWhile_header (n : ℕ) (l : List Bool) : (List.replicate n true ++ false :: l).dropWhile id = false :: l := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

/-- Inside a literal: when the bits still to come fill the literal up to w bits, the reader ends in
the clause, with the word of the literal (last bit first) put on the clause. -/
theorem foldl_bits (w : ℕ) (cl : List (List Bool)) (acc : List (List (List Bool))) : ∀ (bs cur : List Bool), bs ≠ [] → cur.length + bs.length = w →
    bs.foldl (stepR w) (true, false, cur, cl, acc) = (false, true, [], (bs.reverse ++ cur) :: cl, acc)
  | [], _, h, _ => absurd rfl h
  | [e], cur, _, hw => by
    have : cur.length + 1 = w := by simpa using hw
    simp [stepR, this]
  | e :: e' :: bs, cur, _, hw => by
    have hne : ¬ cur.length + 1 = w := by simp only [List.length_cons] at hw; omega
    have hs : stepR w (true, false, cur, cl, acc) e = (true, false, e :: cur, cl, acc) := by simp [stepR, hne]
    rw [List.foldl_cons, hs, foldl_bits w cl acc (e' :: bs) (e :: cur) (by simp) (by simp only [List.length_cons] at hw ⊢; omega)]
    simp

/-- In a clause: the mark 1 and the w bits of a literal put the word of the literal (last bit first)
on the clause. -/
theorem foldl_lit (w : ℕ) (cl : List (List Bool)) (acc : List (List (List Bool))) (bs : List Bool) (hw : bs.length = w) (h0 : bs ≠ []) :
    (true :: bs).foldl (stepR w) (false, true, [], cl, acc) = (false, true, [], bs.reverse :: cl, acc) := by
  have hs : stepR w (false, true, [], cl, acc) true = (true, false, [], cl, acc) := by simp [stepR]
  rw [List.foldl_cons, hs, foldl_bits w cl acc bs [] h0 (by simpa using hw)]
  simp

/-- In a clause: the literals of C, each behind its mark, are put on the clause. -/
theorem foldl_lits {n : ℕ} (acc : List (List (List Bool))) : ∀ (C : List (Lit n)) (cl : List (List Bool)),
    (C.flatMap fun l => true :: SatFree.encLit l).foldl (stepR (Nat.log2 (2 * n) + 1)) (false, true, [], cl, acc) =
      (false, true, [], (C.map fun l => (SatFree.encLit l).reverse).reverse ++ cl, acc)
  | [], _ => rfl
  | l :: C, cl => by
    have h0 : SatFree.encLit l ≠ [] := fun h => by
      have := length_encLit l
      rw [h] at this
      simp at this
    rw [List.flatMap_cons, List.foldl_append, foldl_lit _ cl acc _ (length_encLit l) h0, foldl_lits acc C]
    simp

/-- Between clauses: the code of a clause puts the clause on the list of clauses. -/
theorem foldl_clause {n : ℕ} (acc : List (List (List Bool))) (C : List (Lit n)) :
    (SatFree.encClause C).foldl (stepR (Nat.log2 (2 * n) + 1)) (false, false, [], [], acc) =
      (false, false, [], [], (C.map fun l => (SatFree.encLit l).reverse).reverse :: acc) := by
  have hs : stepR (Nat.log2 (2 * n) + 1) (false, false, [], [], acc) true = (false, true, [], [], acc) := by simp [stepR]
  rw [SatFree.encClause, List.foldl_cons, hs, List.foldl_append, foldl_lits acc C []]
  simp [stepR]

/-- Between clauses: the codes of the clauses of φ put them on the list of clauses. -/
theorem foldl_clauses {n : ℕ} : ∀ (φ : CNF n) (acc : List (List (List Bool))),
    (φ.flatMap SatFree.encClause).foldl (stepR (Nat.log2 (2 * n) + 1)) (false, false, [], [], acc) =
      (false, false, [], [], (φ.map fun C => (C.map fun l => (SatFree.encLit l).reverse).reverse).reverse ++ acc)
  | [], _ => rfl
  | C :: φ, acc => by
    rw [List.flatMap_cons, List.foldl_append, foldl_clause, foldl_clauses φ]
    simp

/-- Past the end of the formula nothing changes. -/
theorem foldl_done (w : ℕ) (s : List Bool × List (List Bool) × List (List (List Bool))) : ∀ u : List Bool, u.foldl (stepR w) (true, true, s) = (true, true, s)
  | [] => rfl
  | e :: u => by
    have hs : stepR w (true, true, s) e = (true, true, s) := by simp [stepR]
    rw [List.foldl_cons, hs, foldl_done w s u]

/-- The state of the reader after the code of φ followed by any bits u. -/
theorem scanR_enc_append {n : ℕ} (φ : CNF n) (u : List Bool) :
    scanR (SatFree.enc φ ++ u) = (true, true, [], [], (φ.map fun C => (C.map fun l => (SatFree.encLit l).reverse).reverse).reverse) := by
  have e : SatFree.enc φ ++ u = List.replicate n true ++ false :: (φ.flatMap SatFree.encClause ++ false :: u) := by
    simp [SatFree.enc]
  have hs : ∀ acc, stepR (Nat.log2 (2 * n) + 1) (false, false, [], [], acc) false = (true, true, [], [], acc) := fun acc => by simp [stepR]
  rw [scanR, e, takeWhile_header, dropWhile_header, List.length_replicate, width_eq, List.tail_cons, List.foldl_append, foldl_clauses, List.foldl_cons, hs,
    foldl_done, List.append_nil]

/-- **The reader on a code followed by any bits**: it returns n in unary and φ with numbers as
variables. -/
theorem readFree_enc_append {n : ℕ} (φ : CNF n) (u : List Bool) : readFree (SatFree.enc φ ++ u) = (List.replicate n (), toN φ) := by
  have e : SatFree.enc φ ++ u = List.replicate n true ++ false :: (φ.flatMap SatFree.encClause ++ false :: u) := by
    simp [SatFree.enc]
  have h1 : ((SatFree.enc φ ++ u).takeWhile id).length = n := by rw [e, takeWhile_header, List.length_replicate]
  rw [readFree, scanR_enc_append, h1]
  simp only [List.reverse_reverse, List.map_map, toN]
  congr 1
  refine List.map_congr_left fun C _ => ?_
  simp only [Function.comp_apply, List.reverse_reverse, List.map_map]
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, List.reverse_reverse, slotDec_encLit, Option.getD_some]

/-- `readFree` reads the code. -/
theorem reads_readFree : Reads readFree := fun n φ => by
  have := readFree_enc_append φ []
  rwa [List.append_nil] at this

end FreeCode
