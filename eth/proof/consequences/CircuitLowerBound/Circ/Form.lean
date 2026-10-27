/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.InterfacesPolyT
import ToTuring.Lib.Int
import ToTuring.Lib.List3
import ToTuring.Lib.List2
import ToTuring.Lib.Unary
import ToTuring.Lib.Nat2
import ToTuring.Lib.Nat1b
import Mathlib.Tactic

/-! # The formula «some clause is violated by the assignment that the circuit C computes»

Let G be the circuit that computes clause number j of the formula of a table from the bits of j. The
check circuit consists of G, three copies of C that read the three variables of the clause off the
output
wires of G, three gates that compare the outputs of the copies with the three signs, and two gates
for the conjunction. It outputs 1 on j if and only if clause number j is violated by the assignment
i ↦ C(i). The formula has one variable for every wire of the check circuit, four clauses for every
gate, and one clause that says that the last wire is 1.

The proofs work with assignments a : ℕ → Bool of values to the wires and with the equations of the
gates (`GE`). `seg`: if the equations of a relocated copy of a circuit hold, the wires of the copy
carry the values of
the wires of the circuit. `stForm_of` proves the interface statement `StForm` from `StClauseCirc`.
The auxiliary statements are in the namespace `CircuitLowerBound.Form`. -/

public section

namespace CircuitLowerBound

open ENP Groundwork

namespace Form

/-! ### The wires of a circuit -/

theorem wires_cons (w : List Bool) (G : Gate) (C : Circuit) :
    wires w (G :: C) = wires (w ++ [G.op (w.getD G.in₁ false) (w.getD G.in₂ false)]) C := rfl

/-- There is one more wire for every gate. -/
theorem length_wires (C : Circuit) (w : List Bool) : (wires w C).length = w.length + C.length := by
  induction C generalizing w with
  | nil => rfl
  | cons G C ih =>
    rw [wires_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

/-- The wires that are there at the start keep their values. -/
theorem getD_wires_of_lt (C : Circuit) (w : List Bool) {i : ℕ} (h : i < w.length) : (wires w C).getD i false = w.getD i false := by
  induction C generalizing w with
  | nil => rfl
  | cons G C ih =>
    rw [wires_cons, ih _ (by rw [List.length_append]; omega), List.getD_append _ _ _ _ h]

/-- A statement on all gates of a list, with their numbers, for two lists one after the other. -/
theorem forall_append (Q : ℕ → GateD → Prop) (N : ℕ) (A B : List GateD) :
    (∀ t (h : t < (A ++ B).length), Q (N + t) (A ++ B)[t]) ↔
      (∀ t (h : t < A.length), Q (N + t) A[t]) ∧ ∀ t (h : t < B.length), Q (N + A.length + t) B[t] := by
  constructor
  · intro H
    refine ⟨fun t h => ?_, fun t h => ?_⟩
    · have := H t (by rw [List.length_append]; omega)
      rwa [List.getElem_append_left h] at this
    · have := H (A.length + t) (by rw [List.length_append]; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using this
  · rintro ⟨H1, H2⟩ t h
    rcases Nat.lt_or_ge t A.length with h1 | h1
    · rw [List.getElem_append_left h1]
      exact H1 t h1
    · rw [List.getElem_append_right h1]
      have := H2 (t - A.length) (by rw [List.length_append] at h; omega)
      rwa [show N + A.length + (t - A.length) = N + t by omega] at this

theorem wf_append (n : ℕ) (A B : List GateD) : WF n (A ++ B) ↔ WF n A ∧ WF (n + A.length) B :=
  forall_append (fun i g => g.2.1 < i ∧ g.2.2 < i) n A B

theorem wf_tail {n : ℕ} {g : GateD} {C : List GateD} (h : WF n (g :: C)) : WF (n + 1) C :=
  ((wf_append n [g] C).1 h).2

/-- The wire of a gate carries the value of the gate on the wires that it reads. -/
theorem getD_wires_gate (C : List GateD) (w : List Bool) (hC : WF w.length C) (t : ℕ) (h : t < C.length) :
    (wires w (toC C)).getD (w.length + t) false
      = C[t].toGate.op ((wires w (toC C)).getD C[t].2.1 false) ((wires w (toC C)).getD C[t].2.2 false) := by
  induction C generalizing w t with
  | nil => simp at h
  | cons g C ih =>
    have e : wires w (toC (g :: C)) = wires (w ++ [g.toGate.op (w.getD g.2.1 false) (w.getD g.2.2 false)]) (toC C) := rfl
    have hl : (w ++ [g.toGate.op (w.getD g.2.1 false) (w.getD g.2.2 false)]).length = w.length + 1 := by
      rw [List.length_append, List.length_singleton]
    rw [e]
    cases t with
    | zero =>
      have h0 := hC 0 h
      simp only [List.getElem_cons_zero, Nat.add_zero] at h0 ⊢
      rw [getD_wires_of_lt _ _ (by rw [hl]; omega), getD_wires_of_lt _ _ (by rw [hl]; omega), getD_wires_of_lt _ _ (by rw [hl]; omega),
        List.getD_append_right _ _ _ _ le_rfl, List.getD_append _ _ _ _ h0.1, List.getD_append _ _ _ _ h0.2, Nat.sub_self]
      rfl
    | succ t =>
      have h' : t < C.length := by simpa using h
      have := ih _ (by rw [hl]; exact wf_tail hC) t h'
      rw [hl] at this
      simp only [List.getElem_cons_succ]
      rw [show w.length + (t + 1) = w.length + 1 + t by omega]
      exact this

/-- The output of a circuit is the value of its last wire. -/
theorem eval_eq (C : Circuit) (x : List Bool) : eval C x = (wires x C).getD (x.length + C.length - 1) false := by
  rw [eval, ← length_wires, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-! ### Assignments of values to wires, and the equations of the gates -/

/-- The gates of K, whose wires are N, N + 1, …, have the right values under a. -/
def GE (a : ℕ → Bool) (N : ℕ) (K : List GateD) : Prop := ∀ t (h : t < K.length), a (N + t) = K[t].toGate.op (a K[t].2.1) (a K[t].2.2)

theorem ge_append (a : ℕ → Bool) (N : ℕ) (A B : List GateD) : GE a N (A ++ B) ↔ GE a N A ∧ GE a (N + A.length) B :=
  forall_append (fun i g => a i = g.toGate.op (a g.2.1) (a g.2.2)) N A B

/-- The values of the wires on an input satisfy the equations of the gates. -/
theorem exists_ge (n : ℕ) (K : List GateD) (hK : WF n K) (x : List Bool) (hx : x.length = n) :
    ∃ a : ℕ → Bool, GE a n K ∧ (List.range n).map a = x := by
  subst hx
  refine ⟨fun i => (wires x (toC K)).getD i false, fun t h => getD_wires_gate K x hK t h, ?_⟩
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, getD_wires_of_lt _ _ h2, List.getD_eq_getElem _ _ h2]

/-- A copy of the circuit C on L inputs, with the wire k of C moved to the wire ρ k, where the gates
go to N, N + 1, …: if the equations of the gates of the copy hold under a, then the wire ρ k carries
the value of
the wire k of C on the input that the wires ρ 0, …, ρ (L − 1) carry. -/
theorem seg (a : ℕ → Bool) (L N : ℕ) (ρ : ℕ → ℕ) (C : List GateD) (hC : WF L C) (hρ : ∀ t, ρ (L + t) = N + t)
    (hE : ∀ t (h : t < C.length), a (N + t) = C[t].toGate.op (a (ρ C[t].2.1)) (a (ρ C[t].2.2))) (k : ℕ) (hk : k < L + C.length) :
    a (ρ k) = (wires ((List.range L).map fun i => a (ρ i)) (toC C)).getD k false := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hx : ((List.range L).map fun i => a (ρ i)).length = L := by simp
    rcases Nat.lt_or_ge k L with h | h
    · rw [getD_wires_of_lt _ _ (by rw [hx]; exact h), List.getD_eq_getElem _ _ (by rw [hx]; exact h), List.getElem_map, List.getElem_range]
    · obtain ⟨t, rfl⟩ : ∃ t, k = L + t := ⟨k - L, by omega⟩
      have ht : t < C.length := by omega
      have hw := hC t ht
      have h1 := getD_wires_gate C ((List.range L).map fun i => a (ρ i)) (by rw [hx]; exact hC) t ht
      rw [hx] at h1
      rw [h1, hρ, hE t ht, ih _ (by omega) (by omega), ih _ (by omega) (by omega)]

/-! ### One variable for every wire -/

/-- The four clauses of a gate whose wire is i. -/
def gateCl (i : ℕ) (g : GateD) : Cnf :=
  [[(g.2.1, true), (g.2.2, true), (i, g.1.1)], [(g.2.1, true), (g.2.2, false), (i, g.1.2.1)],
   [(g.2.1, false), (g.2.2, true), (i, g.1.2.2.1)], [(g.2.1, false), (g.2.2, false), (i, g.1.2.2.2)]]

/-- A clause of three literals is satisfied if one of the three is. -/
theorem ex3 (a : ℕ → Bool) (l1 l2 l3 : ℕ × Bool) : (∃ l ∈ [l1, l2, l3], a l.1 = l.2) ↔ a l1.1 = l1.2 ∨ a l2.1 = l2.2 ∨ a l3.1 = l3.2 := by
  constructor
  · rintro ⟨l, hl, h⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> tauto
  · rintro (h | h | h)
    exacts [⟨l1, by simp, h⟩, ⟨l2, by simp, h⟩, ⟨l3, by simp, h⟩]

theorem sat_gateCl (a : ℕ → Bool) (i : ℕ) (g : GateD) :
    (∀ D ∈ gateCl i g, ∃ l ∈ D, a l.1 = l.2) ↔ a i = g.toGate.op (a g.2.1) (a g.2.2) := by
  obtain ⟨⟨v00, v01, v10, v11⟩, i1, i2⟩ := g
  simp only [gateCl, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, ex3, GateD.toGate]
  cases a i1 <;> cases a i2 <;> simp

/-- A gate for the places where there is none. -/
def dG : GateD := ((false, false, false, false), 0, 0)

/-- The clauses of all gates of a circuit on n inputs. -/
def tseitin (n : ℕ) (K : List GateD) : Cnf := (List.range K.length).flatMap fun t => gateCl (n + t) (K.getD t dG)

theorem sat_tseitin (a : ℕ → Bool) (n : ℕ) (K : List GateD) : (∀ D ∈ tseitin n K, ∃ l ∈ D, a l.1 = l.2) ↔ GE a n K := by
  unfold tseitin GE
  constructor
  · intro H t h
    rw [← sat_gateCl]
    intro D hD
    exact H D (List.mem_flatMap.2 ⟨t, List.mem_range.2 h, by rwa [List.getD_eq_getElem _ _ h]⟩)
  · intro H D hD
    obtain ⟨t, ht, hD⟩ := List.mem_flatMap.1 hD
    have h := List.mem_range.1 ht
    rw [List.getD_eq_getElem _ _ h] at hD
    exact (sat_gateCl a _ _).2 (H t h) D hD

/-- The clauses have three literals, and their variables are wires. -/
theorem shape_tseitin (n : ℕ) (K : List GateD) (hK : WF n K) : ∀ D ∈ tseitin n K, D.length ≤ 3 ∧ ∀ l ∈ D, l.1 < n + K.length := by
  intro D hD
  obtain ⟨t, ht, hD⟩ := List.mem_flatMap.1 hD
  have h := List.mem_range.1 ht
  rw [List.getD_eq_getElem _ _ h] at hD
  have hw := hK t h
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl | rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl | rfl <;> simp only <;> omega

/-! ### The check circuit -/

/-- Where the wire k of a circuit on L inputs goes in a copy: an input to the wire that the list o
names at the place off + k, the gate number t to the wire N + t. -/
def rho (L N : ℕ) (o : List ℕ) (off k : ℕ) : ℕ := if k < L then o.getD (off + k) 0 else N + (k - L)

/-- The copy. -/
def reloc (L N : ℕ) (o : List ℕ) (off : ℕ) (C : List GateD) : List GateD := C.map fun g => (g.1, rho L N o off g.2.1, rho L N o off g.2.2)

def xorT : Bool × Bool × Bool × Bool := (false, true, true, false)

def andT : Bool × Bool × Bool × Bool := (false, false, false, true)

/-- The last five gates: the outputs of the three copies, which have c gates each and begin at the
wire N, are compared with the three signs; then the conjunction. -/
def fin (L N c : ℕ) (o : List ℕ) : List GateD :=
  [(xorT, rho L N o 0 (L + c - 1), o.getD (0 + L) 0),
   (xorT, rho L (N + c) o (L + 1) (L + c - 1), o.getD (L + 1 + L) 0),
   (xorT, rho L (N + c + c) o (L + 1 + (L + 1)) (L + c - 1), o.getD (L + 1 + (L + 1) + L) 0),
   (andT, N + c + c + c, N + c + c + c + 1), (andT, N + c + c + c + 3, N + c + c + c + 2)]

/-- The check circuit; N is the number of the wires of G, inputs included. -/
def check (L N : ℕ) (G : List GateD) (o : List ℕ) (C : List GateD) : List GateD :=
  G ++ (reloc L N o 0 C ++ (reloc L (N + C.length) o (L + 1) C ++ (reloc L (N + C.length + C.length) o (L + 1 + (L + 1)) C ++ fin L N C.length o)))

theorem length_reloc (L N : ℕ) (o : List ℕ) (off : ℕ) (C : List GateD) : (reloc L N o off C).length = C.length := List.length_map _

theorem length_check (L N : ℕ) (G : List GateD) (o : List ℕ) (C : List GateD) :
    (check L N G o C).length = G.length + C.length + C.length + C.length + 5 := by
  simp only [check, List.length_append, length_reloc, fin, List.length_cons, List.length_nil]
  omega

theorem rho_lt {L N : ℕ} {o : List ℕ} (ho : ∀ i, o.getD i 0 < N) (off : ℕ) {k t : ℕ} (hk : k < L + t) : rho L N o off k < N + t := by
  unfold rho
  split_ifs
  · exact (ho _).trans_le (Nat.le_add_right _ _)
  · omega

theorem wf_reloc {L N : ℕ} {o : List ℕ} (ho : ∀ i, o.getD i 0 < N) (off : ℕ) {C : List GateD} (hC : WF L C) : WF N (reloc L N o off C) := by
  intro t h
  have ht : t < C.length := by rwa [length_reloc] at h
  have hw := hC t ht
  simp only [reloc, List.getElem_map]
  exact ⟨rho_lt ho off hw.1, rho_lt ho off hw.2⟩

/-- In the check circuit every gate reads inputs and earlier gates only. -/
theorem wf_check {n L : ℕ} {G : List GateD} {o : List ℕ} {C : List GateD} (hL : 1 ≤ L) (hG : WF n G) (hC : WF L C)
    (ho : ∀ i, o.getD i 0 < n + G.length) : WF n (check L (n + G.length) G o C) := by
  have ho1 : ∀ i, o.getD i 0 < n + G.length + C.length := fun i => (ho i).trans_le (Nat.le_add_right _ _)
  have ho2 : ∀ i, o.getD i 0 < n + G.length + C.length + C.length := fun i => (ho1 i).trans_le (Nat.le_add_right _ _)
  rw [check, wf_append, wf_append, wf_append, wf_append]
  simp only [length_reloc]
  refine ⟨hG, wf_reloc ho _ hC, wf_reloc ho1 _ hC, wf_reloc ho2 _ hC, fun t h => ?_⟩
  have r0 := rho_lt ho 0 (show L + C.length - 1 < L + C.length by omega)
  have r1 := rho_lt ho1 (L + 1) (show L + C.length - 1 < L + C.length by omega)
  have r2 := rho_lt ho2 (L + 1 + (L + 1)) (show L + C.length - 1 < L + C.length by omega)
  have s0 := ho (0 + L)
  have s1 := ho (L + 1 + L)
  have s2 := ho (L + 1 + (L + 1) + L)
  have h5 : t < 5 := by simpa [fin] using h
  interval_cases t <;> simp only [fin, List.getElem_cons_zero, List.getElem_cons_succ] <;> constructor <;> omega

/-- The output wire of a copy carries the output of the circuit on the input that the wires named by
o carry. -/
theorem copy_out (a : ℕ → Bool) {L N : ℕ} (o : List ℕ) (off : ℕ) {C : List GateD} (hL : 1 ≤ L) (hC : WF L C) (hE : GE a N (reloc L N o off C)) :
    a (rho L N o off (L + C.length - 1)) = eval (toC C) ((List.range L).map fun k => a (o.getD (off + k) 0)) := by
  have h1 := seg a L N (rho L N o off) C hC (fun t => by simp [rho]) (fun t h => by
    have := hE t (by rwa [length_reloc])
    simp only [reloc, List.getElem_map] at this
    exact this) (L + C.length - 1) (by omega)
  have e : ((List.range L).map fun i => a (rho L N o off i)) = (List.range L).map fun k => a (o.getD (off + k) 0) :=
    List.map_congr_left fun i hi => by rw [rho, if_pos (List.mem_range.1 hi)]
  rw [e] at h1
  rw [h1, eval_eq, List.length_map, List.length_range, toC, List.length_map]

theorem xor_op (i j : ℕ) (x y : Bool) : (GateD.toGate (xorT, i, j)).op x y = (x != y) := by
  cases x <;> cases y <;> rfl

theorem and_op (i j : ℕ) (x y : Bool) : (GateD.toGate (andT, i, j)).op x y = (x && y) := by
  cases x <;> cases y <;> rfl

/-- What the last wire of the check circuit says, if the equations of all gates hold: each of the
three copies of C, on the input that the output wires of G carry, differs from the sign wire. -/
theorem check_out (a : ℕ → Bool) {n L : ℕ} {G : List GateD} {o : List ℕ} {C : List GateD} (hL : 1 ≤ L) (hG : WF n G) (hC : WF L C)
    (ho : ∀ i, o.getD i 0 < n + G.length) (hE : GE a n (check L (n + G.length) G o C)) :
    a (n + G.length + C.length + C.length + C.length + 4) = true ↔
      ∀ off ∈ [0, L + 1, L + 1 + (L + 1)],
        eval (toC C) ((List.range L).map fun k => (wires ((List.range n).map a) (toC G)).getD (o.getD (off + k) 0) false) ≠
          (wires ((List.range n).map a) (toC G)).getD (o.getD (off + L) 0) false := by
  rw [check, ge_append, ge_append, ge_append, ge_append] at hE
  simp only [length_reloc] at hE
  obtain ⟨hg, h0, h1, h2, hf⟩ := hE
  have hW : ∀ k, k < n + G.length → a k = (wires ((List.range n).map a) (toC G)).getD k false :=
    fun k hk => seg a n n id G hG (fun _ => rfl) hg k hk
  have hin : ∀ off, ((List.range L).map fun k => a (o.getD (off + k) 0))
      = (List.range L).map fun k => (wires ((List.range n).map a) (toC G)).getD (o.getD (off + k) 0) false :=
    fun off => List.map_congr_left fun k _ => hW _ (ho _)
  have c0 := copy_out a o 0 hL hC h0
  have c1 := copy_out a o (L + 1) hL hC h1
  have c2 := copy_out a o (L + 1 + (L + 1)) hL hC h2
  rw [hin] at c0 c1 c2
  have e0 := hf 0 (by simp [fin])
  have e1 := hf 1 (by simp [fin])
  have e2 := hf 2 (by simp [fin])
  have e3 := hf 3 (by simp [fin])
  have e4 := hf 4 (by simp [fin])
  simp only [fin, List.getElem_cons_zero, List.getElem_cons_succ, xor_op, and_op] at e0 e1 e2 e3 e4
  rw [c0, hW _ (ho _)] at e0
  rw [c1, hW _ (ho _)] at e1
  rw [c2, hW _ (ho _)] at e2
  rw [Nat.add_zero] at e0
  rw [e4, e3, e0, e1, e2]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Bool.and_eq_true, bne_iff_ne, ne_eq, and_assoc]

/-- The formula is satisfiable if and only if some assignment satisfies the equations of all gates
and gives the wire «out» the value 1. -/
theorem sat_psi (n : ℕ) (K : List GateD) (out : ℕ) : Sat (tseitin n K ++ [[(out, true)]]).dedup ↔ ∃ a : ℕ → Bool, GE a n K ∧ a out = true := by
  constructor
  · rintro ⟨a, h⟩
    refine ⟨a, (sat_tseitin a n K).1 fun D hD => h D (List.mem_dedup.2 (List.mem_append_left _ hD)), ?_⟩
    obtain ⟨l, hl, h'⟩ := h [(out, true)] (List.mem_dedup.2 (List.mem_append_right _ (by simp)))
    rw [List.mem_singleton] at hl
    subst hl
    exact h'
  · rintro ⟨a, h1, h2⟩
    refine ⟨a, fun D hD => ?_⟩
    rcases List.mem_append.1 (List.mem_dedup.1 hD) with h | h
    · exact (sat_tseitin a n K).2 h1 D h
    · rw [List.mem_singleton] at h
      subst h
      exact ⟨(out, true), by simp, h2⟩

/-- A part of a list, entry by entry. -/
theorem take_drop_eq (o : List ℕ) (off L : ℕ) (h : off + L ≤ o.length) : (o.drop off).take L = (List.range L).map fun k => o.getD (off + k) 0 := by
  refine List.ext_getElem (by simp; omega) fun k h1 h2 => ?_
  have hk : k < L := by simpa using h2
  rw [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ (by omega)]

/-- Not all clauses of the formula of a table are satisfied: some clause is violated. -/
theorem not_all_iff (e : MCode) (L P : ℕ) (f : ℕ → Bool) :
    (¬∀ D ∈ tabF e L P, ∃ l ∈ D, f l.1 = l.2) ↔ ∃ j < 2 ^ nb e L, ∀ l ∈ clauseAt e L P j, f l.1 ≠ l.2 := by
  constructor
  · intro h
    by_contra hc
    refine h fun D hD => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hD
    by_contra h2
    exact hc ⟨j, List.mem_range.1 hj, fun l hl he => h2 ⟨l, hl, he⟩⟩
  · rintro ⟨j, hj, hv⟩ H
    obtain ⟨l, hl, he⟩ := H _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
    exact hv l hl he

/-! ### The formula and its properties -/

/-- The properties of the formula, for a circuit G with output wires o that computes the clauses of
the formula of the table e. -/
theorem form_spec {e : MCode} {L P : ℕ} (hFit : Fits e L P) {G : List GateD} {o : List ℕ} {C : List GateD} (hG : WF (nb e L) G)
    (ho : o.length = 3 * (L + 1)) (hoN : ∀ w ∈ o, w < nb e L + G.length)
    (hval : ∀ j < 2 ^ nb e L, ∀ i < 3,
      (ofWord (((o.drop (i * (L + 1))).take L).map fun w => (wires (toWord (nb e L) j) (toC G)).getD w false),
        (wires (toWord (nb e L) j) (toC G)).getD (o.getD (i * (L + 1) + L) 0) false) = (clauseAt e L P j).getD i (0, false))
    (hC : WF L C) :
    Shaped3 (nb e L + (check L (nb e L + G.length) G o C).length)
        (tseitin (nb e L) (check L (nb e L + G.length) G o C) ++ [[(nb e L + (check L (nb e L + G.length) G o C).length - 1, true)]]).dedup ∧
      (Sat (tseitin (nb e L) (check L (nb e L + G.length) G o C) ++ [[(nb e L + (check L (nb e L + G.length) G o C).length - 1, true)]]).dedup ↔
        ¬∀ D ∈ tabF e L P, ∃ l ∈ D, eval (toC C) (toWord L l.1) = l.2) := by
  obtain ⟨hf1, hf2⟩ := hFit
  have hL : 1 ≤ L := by omega
  have hn : 1 ≤ nb e L := by
    have : bt e L ≠ 0 := fun h0 => by
      rw [h0, pow_zero] at hf2
      omega
    unfold nb
    omega
  have ho' : ∀ i, o.getD i 0 < nb e L + G.length := by
    intro i
    rcases Nat.lt_or_ge i o.length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact hoN _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]
      omega
  have hK := wf_check hL hG hC ho'
  have hout : nb e L + (check L (nb e L + G.length) G o C).length - 1 = nb e L + G.length + C.length + C.length + C.length + 4 := by
    rw [length_check]
    omega
  -- the three literals of clause number j, read off the output wires of G
  have lit : ∀ j < 2 ^ nb e L, ∀ i < 3,
      ((List.range L).map fun k => (wires (toWord (nb e L) j) (toC G)).getD (o.getD (i * (L + 1) + k) 0) false)
          = toWord L ((clauseAt e L P j).getD i (0, false)).1 ∧
        (wires (toWord (nb e L) j) (toC G)).getD (o.getD (i * (L + 1) + L) 0) false = ((clauseAt e L P j).getD i (0, false)).2 := by
    intro j hj i hi
    have h := hval j hj i hi
    rw [take_drop_eq o (i * (L + 1)) L (by rw [ho]; interval_cases i <;> omega), List.map_map] at h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    simp only at h1 h2
    have h3 := toWord_ofWord ((List.range L).map ((fun w => (wires (toWord (nb e L) j) (toC G)).getD w false) ∘ fun k => o.getD (i * (L + 1) + k) 0))
    rw [List.length_map, List.length_range, h1] at h3
    exact ⟨h3.symm, h2⟩
  -- what the last wire says
  have viol : ∀ (a : ℕ → Bool) (j : ℕ), j < 2 ^ nb e L → GE a (nb e L) (check L (nb e L + G.length) G o C) → (List.range (nb e L)).map a = toWord (nb e L) j →
      (a (nb e L + G.length + C.length + C.length + C.length + 4) = true ↔ ∀ l ∈ clauseAt e L P j, eval (toC C) (toWord L l.1) ≠ l.2) := by
    intro a j hj hE hx
    rw [check_out a hL hG hC ho' hE, hx]
    have l0 := lit j hj 0 (by norm_num)
    have l1 := lit j hj 1 (by norm_num)
    have l2 := lit j hj 2 (by norm_num)
    simp only [Nat.zero_mul, Nat.one_mul, Nat.two_mul] at l0 l1 l2
    have hc : clauseAt e L P j = [(clauseAt e L P j).getD 0 (0, false), (clauseAt e L P j).getD 1 (0, false), (clauseAt e L P j).getD 2 (0, false)] := rfl
    rw [hc]
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    rw [l0.1, l0.2, l1.1, l1.2, l2.1, l2.2]
  refine ⟨⟨fun D hD => ?_, List.nodup_dedup _⟩, ?_⟩
  · rcases List.mem_append.1 (List.mem_dedup.1 hD) with h | h
    · exact shape_tseitin _ _ hK D h
    · rw [List.mem_singleton] at h
      subst h
      refine ⟨by simp, fun l hl => ?_⟩
      rw [List.mem_singleton] at hl
      subst hl
      simp only
      omega
  · rw [sat_psi, not_all_iff e L P fun i => eval (toC C) (toWord L i), hout]
    constructor
    · rintro ⟨a, hE, ha⟩
      have hx : ((List.range (nb e L)).map a).length = nb e L := by simp
      have hj : ofWord ((List.range (nb e L)).map a) < 2 ^ nb e L := by
        have := ofWord_lt ((List.range (nb e L)).map a)
        rwa [hx] at this
      have hw : (List.range (nb e L)).map a = toWord (nb e L) (ofWord ((List.range (nb e L)).map a)) := by
        have := toWord_ofWord ((List.range (nb e L)).map a)
        rw [hx] at this
        exact this.symm
      exact ⟨_, hj, (viol a _ hj hE hw).1 ha⟩
    · rintro ⟨j, hj, hv⟩
      obtain ⟨a, hE, hx⟩ := exists_ge (nb e L) _ hK (toWord (nb e L) j) (length_toWord _ _)
      exact ⟨a, hE, (viol a j hj hE hx).2 hv⟩

/-- The number of the input bits of the check circuit, cut off so that it can be written in unary. -/
def nF (e : MCode) (L : ℕ) : ℕ := min (nb e L) (rb e + L)

theorem nF_eq {e : MCode} {L P : ℕ} (h : Fits e L P) : nF e L = nb e L := by
  obtain ⟨h1, -⟩ := h
  have h2 : 2 * ((L - kb e - lam e - 2) / 2) ≤ L - kb e - lam e - 2 := Nat.mul_div_le _ 2
  unfold nF nb bq bt
  exact min_eq_left (by omega)

section Program

variable (B : MCode × List Unit × ℕ → List GateD × List ℕ)

/-- The check circuit, from the table, L in unary, the parameter P and the circuit C. -/
def cK (q : (MCode × List Unit × ℕ) × List GateD) : List GateD :=
  check q.1.2.1.length (nF q.1.1 q.1.2.1.length + (B q.1).1.length) (B q.1).1 (B q.1).2 q.2

/-- The number of variables, in unary, and the formula. -/
def F (q : (MCode × List Unit × ℕ) × List GateD) : List Unit × Cnf :=
  (List.replicate (nF q.1.1 q.1.2.1.length + (cK B q).length) (),
    (tseitin (nF q.1.1 q.1.2.1.length) (cK B q) ++ [[(nF q.1.1 q.1.2.1.length + (cK B q).length - 1, true)]]).dedup)

end Program

/-! ### Polynomial time -/

section Cert

variable {α : Type} [Enc α]

@[fun_prop] theorem rho_polyT {L N off k : α → ℕ} {o : α → List ℕ} (hL : PolyT L) (hN : PolyT N) (ho : PolyT o) (hoff : PolyT off) (hk : PolyT k) :
    PolyT fun x => rho (L x) (N x) (o x) (off x) (k x) := by
  unfold rho
  fun_prop

theorem reloc_polyT {L N off : α → ℕ} {o : α → List ℕ} {C : α → List GateD} (hL : PolyT L) (hN : PolyT N) (ho : PolyT o) (hoff : PolyT off)
    (hC : PolyT C) : PolyT fun x => reloc (L x) (N x) (o x) (off x) (C x) := by
  unfold reloc
  fun_prop

theorem fin_polyT {L N c : α → ℕ} {o : α → List ℕ} (hL : PolyT L) (hN : PolyT N) (hc : PolyT c) (ho : PolyT o) :
    PolyT fun x => fin (L x) (N x) (c x) (o x) := by
  unfold fin
  have g0 : PolyT fun x => ((xorT, rho (L x) (N x) (o x) 0 (L x + c x - 1), (o x).getD (0 + L x) 0) : GateD) := by fun_prop
  have g1 : PolyT fun x => ((xorT, rho (L x) (N x + c x) (o x) (L x + 1) (L x + c x - 1), (o x).getD (L x + 1 + L x) 0) : GateD) := by fun_prop
  have g2 : PolyT fun x => ((xorT, rho (L x) (N x + c x + c x) (o x) (L x + 1 + (L x + 1)) (L x + c x - 1),
      (o x).getD (L x + 1 + (L x + 1) + L x) 0) : GateD) := by fun_prop
  have g3 : PolyT fun x => ((andT, N x + c x + c x + c x, N x + c x + c x + c x + 1) : GateD) := by fun_prop
  have g4 : PolyT fun x => ((andT, N x + c x + c x + c x + 3, N x + c x + c x + c x + 2) : GateD) := by fun_prop
  exact g0.cons' (g1.cons' (g2.cons' (g3.cons' (g4.cons' (PolyT.const [])))))

theorem check_polyT {L N : α → ℕ} {G C : α → List GateD} {o : α → List ℕ} (hL : PolyT L) (hN : PolyT N) (hG : PolyT G) (ho : PolyT o)
    (hC : PolyT C) : PolyT fun x => check (L x) (N x) (G x) (o x) (C x) := by
  unfold check
  exact hG.append ((reloc_polyT hL hN ho (by fun_prop) hC).append ((reloc_polyT hL (by fun_prop) ho (by fun_prop) hC).append
    ((reloc_polyT hL (by fun_prop) ho (by fun_prop) hC).append (fin_polyT hL hN (by fun_prop) ho))))

theorem tseitin_polyT {n : α → ℕ} {K : α → List GateD} (hn : PolyT n) (hK : PolyT K) : PolyT fun x => tseitin (n x) (K x) := by
  unfold tseitin
  exact PolyT.flatMap (by unfold gateCl dG; fun_prop) (PolyT.range (Unary.of_length hK))

theorem nF_polyT {e : α → MCode} {L : α → ℕ} (he : PolyT e) (hL : PolyT L) : PolyT fun x => nF (e x) (L x) := by
  unfold nF nb bq bt rb kb lam tab
  fun_prop

theorem nF_unary {e : α → MCode} {u : α → List Unit} (he : PolyT e) (hu : PolyT u) : Unary fun x => nF (e x) (u x).length := by
  refine Unary.of_le (g := fun x => (tab (e x)).length + (u x).length)
    (Unary.add (Unary.of_length (by unfold tab; fun_prop)) (Unary.of_length hu)) (nF_polyT he (by fun_prop)) fun x => ?_
  have h1 : Nat.size (tab (e x)).length ≤ (tab (e x)).length := Nat.size_le.2 Nat.lt_two_pow_self
  have h2 : nF (e x) (u x).length ≤ rb (e x) + (u x).length := min_le_right _ _
  unfold rb at h2
  omega

theorem F_polyT (B : MCode × List Unit × ℕ → List GateD × List ℕ) (hB : PolyT B) : PolyT (F B) := by
  have hn : PolyT fun q : (MCode × List Unit × ℕ) × List GateD => nF q.1.1 q.1.2.1.length := nF_polyT (by fun_prop) (by fun_prop)
  have hK : PolyT (cK B) := by
    unfold cK
    exact check_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hU : Unary fun q : (MCode × List Unit × ℕ) × List GateD => nF q.1.1 q.1.2.1.length + (cK B q).length :=
    Unary.add (nF_unary (by fun_prop) (by fun_prop)) (Unary.of_length hK)
  unfold F
  exact PolyT.prodMk hU (PolyT.dedup (PolyT.append (tseitin_polyT hn hK) (by fun_prop)))

end Cert

end Form

open Form

/-- The formula that says «some clause of the formula of the table e is violated by the assignment
that the circuit C computes», from the circuit that computes a clause from its number. -/
theorem stForm_of (h : StClauseCirc) : StForm := by
  obtain ⟨a₀, g, B, hB, hspec⟩ := h
  refine ⟨a₀ + 1, fun e => g e + rb e + 5, F B, F_polyT B hB, fun e L P C hFit hC => ?_⟩
  obtain ⟨hG, hlen, ho, hoN, hval⟩ := hspec e L P hFit
  have hs := form_spec hFit hG ho hoN hval hC
  have hn := nF_eq hFit
  have hle : nb e L ≤ rb e + L := hn ▸ min_le_right _ _
  simp only [F, cK, List.length_replicate, hn]
  refine ⟨hs.1, ?_, hs.2⟩
  rw [length_check, Nat.add_mul, Nat.one_mul]
  omega

end CircuitLowerBound
