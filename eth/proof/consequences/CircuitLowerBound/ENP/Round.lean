/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.InterfacesPolyT
public import PaddedDescent.Pad
import ToTuring.Poly.Decode
import ToTuring.Poly.Sat
import ToTuring.Lib.List3
import ToTuring.Lib.Nat2
import ToTuring.Lib.Unary
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): one round of the prefix search for the language L0

The language `L0` is decided by a prefix search with queries to SAT. In the restart form of E^NP an
ordinary machine is started on x and the answers so far (`ENP.roundInput`). This file has the
function `roundF` that such a
machine computes, as a function of its input word and a pad. With m = |x| and i the number that x
writes: as long as there are at most i answers, it returns the query «is `Phi m`, together with the
values found so far and 0 for the next
variable, satisfiable?»; after that it returns the result, the negation of answer number i.
The file proves: the input word is read correctly (`mL_roundInput`, `xW_roundInput`,
`aW_roundInput`); the code of formulas is one-to-one, so that a query asks what it is meant to ask
(`sat_encCnf`); with a pad of 2^(2m+4) units
nothing is cut off (`roundF_roundInput`); and `roundF` is polynomial-time in its input and the pad
(`roundF_polyT`). The functions G and fb are those of the interface statements `StCertTabF` and
`StFlip`. -/

@[expose] public section

namespace CircuitLowerBound

open ENP Groundwork

/-! ### The function -/

/-- The numbers 0, …, m − 1, where m is the number of pairs 1b at the start of the word. -/
def mL (w : List Bool) : List ℕ := (List.range w.length).takeWhile fun i => w.getD (2 * i) false

/-- m in unary. -/
def mU (w : List Bool) : List Unit := (mL w).map fun _ => ()

/-- The word x. -/
def xW (w : List Bool) : List Bool := (mL w).map fun i => w.getD (2 * i + 1) false

/-- The answers so far. -/
def aW (w : List Bool) : List Bool := w.drop (2 * (mL w).length + 1)

/-- The logarithm of the length of the pad. -/
def eW (w : List Bool) : ℕ := 2 * (mL w).length + 4

/-- `Phi m`, for m in unary, written under a pad. -/
def PhiF (G : (MCode × List Unit × ℕ) × List Unit → Cnf) (fb : List Unit → Bool) (u pad : List Unit) : Cnf :=
  bif decide (pos u.length < top (nu u.length)) then
    (bif decide (Fits (codeOf (nu u.length)) u.length (next u.length)) then G ((codeOf (nu u.length), u, next u.length), pad) else [])
  else bif decide (pos u.length = top (nu u.length)) then (bif fb u then [[]] else []) else []

/-- The code of a formula, with the variables cut off at the length of the pad. -/
def encF (pad : List Unit) (φ : Cnf) : List Bool :=
  φ.flatMap (fun C => C.flatMap (fun l => true :: ((pad.take l.1).map (fun _ => true) ++ [false, l.2])) ++ [false, true]) ++ [false, false]

/-- One round: the next query, or the result. -/
def roundF (G : (MCode × List Unit × ℕ) × List Unit → Cnf) (fb : List Unit → Bool) (p : List Bool × List Unit) : List Bool :=
  bif decide ((aW p.1).length ≤ ofWord (xW p.1)) then
    true :: encF p.2 (PhiF G fb (mU p.1) p.2 ++ units ((aW p.1).map (fun b => !b) ++ [false]))
  else [false, !(aW p.1).getD (ofWord (xW p.1)) false]

namespace Round

/-! ### Reading the input word -/

theorem roundInput_cons (b : Bool) (x ans : List Bool) : roundInput (b :: x) ans = true :: b :: roundInput x ans := by
  simp [roundInput]

theorem length_roundInput (x ans : List Bool) : (roundInput x ans).length = 2 * x.length + 1 + ans.length := by
  induction x with
  | nil => simp [roundInput]; omega
  | cons b x ih => rw [roundInput_cons]; simp only [List.length_cons, ih]; omega

theorem getD_even (x ans : List Bool) (i : ℕ) (hi : i < x.length) : (roundInput x ans).getD (2 * i) false = true := by
  induction x generalizing i with
  | nil => simp at hi
  | cons b x ih =>
    rw [roundInput_cons]
    cases i with
    | zero => rfl
    | succ i =>
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ]
      exact ih i (by simpa using hi)

theorem getD_odd (x ans : List Bool) (i : ℕ) (hi : i < x.length) : (roundInput x ans).getD (2 * i + 1) false = x.getD i false := by
  induction x generalizing i with
  | nil => simp at hi
  | cons b x ih =>
    rw [roundInput_cons]
    cases i with
    | zero => rfl
    | succ i =>
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
      exact ih i (by simpa using hi)

theorem getD_end (x ans : List Bool) : (roundInput x ans).getD (2 * x.length) false = false := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    rw [roundInput_cons, List.length_cons, show 2 * (x.length + 1) = 2 * x.length + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ]
    exact ih

theorem drop_roundInput (x ans : List Bool) : (roundInput x ans).drop (2 * x.length + 1) = ans := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    rw [roundInput_cons, List.length_cons, show 2 * (x.length + 1) + 1 = 2 * x.length + 1 + 1 + 1 by ring, List.drop_succ_cons, List.drop_succ_cons]
    exact ih

/-- The first numbers that pass a test, if the test holds below m, fails at m, and m is in the
range. -/
theorem takeWhile_range {p : ℕ → Bool} {m n : ℕ} (h1 : ∀ i < m, p i = true) (h2 : p m = false) (hmn : m < n) :
    (List.range n).takeWhile p = List.range m := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
  rw [List.range_add, List.takeWhile_append_of_pos (fun a ha => h1 a (List.mem_range.1 ha)), List.range_succ_eq_map, List.map_cons,
    List.takeWhile_cons_of_neg (by simp [h2]), List.append_nil]

theorem mL_roundInput (x ans : List Bool) : mL (roundInput x ans) = List.range x.length :=
  takeWhile_range (fun i hi => getD_even x ans i hi) (getD_end x ans) (by rw [length_roundInput]; omega)

theorem mU_roundInput (x ans : List Bool) : mU (roundInput x ans) = List.replicate x.length () := by
  rw [mU, mL_roundInput, List.map_const', List.length_range]

theorem xW_roundInput (x ans : List Bool) : xW (roundInput x ans) = x := by
  rw [xW, mL_roundInput]
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, getD_odd x ans i h2, List.getD_eq_getElem _ _ h2]

theorem aW_roundInput (x ans : List Bool) : aW (roundInput x ans) = ans := by
  rw [aW, mL_roundInput, List.length_range, drop_roundInput]

theorem eW_roundInput (x ans : List Bool) : eW (roundInput x ans) = 2 * x.length + 4 := by
  rw [eW, mL_roundInput, List.length_range]

/-! ### The code of formulas is one-to-one -/

theorem replicate_inj {v v' : ℕ} {Y Y' : List Bool} (h : List.replicate v true ++ false :: Y = List.replicate v' true ++ false :: Y') : v = v' ∧ Y = Y' := by
  induction v generalizing v' with
  | zero =>
    cases v' with
    | zero => simpa using h
    | succ v' => simp [List.replicate_succ] at h
  | succ v ih =>
    cases v' with
    | zero => simp [List.replicate_succ] at h
    | succ v' =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨a, b⟩ := ih h
      exact ⟨by rw [a], b⟩

theorem clause_inj {C C' : List (ℕ × Bool)} {r r' : List Bool} (h : C.flatMap encLit ++ false :: r = C'.flatMap encLit ++ false :: r') : C = C' ∧ r = r' := by
  induction C generalizing C' with
  | nil =>
    cases C' with
    | nil => simpa using h
    | cons l' C' => simp [encLit] at h
  | cons l C ih =>
    cases C' with
    | nil => simp [encLit] at h
    | cons l' C' =>
      simp only [List.flatMap_cons, encLit, List.cons_append, List.append_assoc, List.cons.injEq, true_and, List.nil_append] at h
      obtain ⟨a, b⟩ := replicate_inj h
      simp only [List.cons.injEq] at b
      obtain ⟨c, d⟩ := ih b.2
      exact ⟨by rw [c, Prod.ext a b.1], d⟩

theorem encCnf_cons (C : List (ℕ × Bool)) (φ : Cnf) : encCnf (C :: φ) = C.flatMap encLit ++ false :: true :: encCnf φ := by
  simp [encCnf]

theorem encCnf_injective {φ φ' : Cnf} (h : encCnf φ = encCnf φ') : φ = φ' := by
  induction φ generalizing φ' with
  | nil =>
    cases φ' with
    | nil => rfl
    | cons C' φ' =>
      rw [encCnf_cons] at h
      have h' : ([] : List (ℕ × Bool)).flatMap encLit ++ false :: [false] = C'.flatMap encLit ++ false :: true :: encCnf φ' := h
      simpa using (clause_inj h').2
  | cons C φ ih =>
    cases φ' with
    | nil =>
      rw [encCnf_cons] at h
      have h' : C.flatMap encLit ++ false :: true :: encCnf φ = ([] : List (ℕ × Bool)).flatMap encLit ++ false :: [false] := h
      simpa using (clause_inj h').2
    | cons C' φ' =>
      rw [encCnf_cons, encCnf_cons] at h
      obtain ⟨a, b⟩ := clause_inj h
      rw [a, ih (List.cons.inj b).2]

/-- The code of a formula is in SAT if and only if the formula is satisfiable. -/
theorem sat_encCnf (φ : Cnf) : SAT (encCnf φ) ↔ Sat φ :=
  ⟨fun ⟨_, h, hs⟩ => encCnf_injective h ▸ hs, fun h => ⟨φ, rfl, h⟩⟩

/-- Under a pad that is at least as long as every variable is large, the code is not cut off. -/
theorem encF_eq {pad : List Unit} {φ : Cnf} (h : ∀ C ∈ φ, ∀ l ∈ C, l.1 ≤ pad.length) : encF pad φ = encCnf φ := by
  unfold encF encCnf
  congr 1
  refine List.flatMap_congr fun C hC => ?_
  congr 1
  refine List.flatMap_congr fun l hl => ?_
  rw [encLit, List.map_const', List.length_take, Nat.min_eq_left (h C hC l hl)]

/-! ### Sizes -/

theorem length_rest_le (x : List Bool) : (rest x).length ≤ x.length := by
  rw [rest, List.length_tail]
  exact (Nat.sub_le _ _).trans (List.dropWhile_sublist _).length_le

theorem length_bits_le (a : ℕ) : (Nat.bits a).length ≤ a := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.2 Nat.lt_two_pow_self

/-- The table number a has at most a clauses. -/
theorem length_tab_codeOf_le (a : ℕ) : (tab (codeOf a)).length ≤ a := by
  have h1 : (tab (codeOf a)).length ≤ (rest (rest (Nat.bits a))).length := by
    simp only [tab, codeOf, codeOfWord, List.length_map, List.length_range]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  exact h1.trans ((length_rest_le _).trans ((length_rest_le _).trans (length_bits_le a)))

theorem nu_le (m : ℕ) : nu m ≤ m := by
  rw [nu]
  exact (List.takeWhile_sublist _).length_le.trans (length_bits_le m)

/-- The number of a clause of the formula of the table of m, for variables of m bits, has at most 2m
bits. -/
theorem nb_le {m P : ℕ} (h : Fits (codeOf (nu m)) m P) : nb (codeOf (nu m)) m ≤ 2 * m := by
  have h1 : rb (codeOf (nu m)) ≤ m := by
    rw [rb]
    exact (Nat.size_le.2 Nat.lt_two_pow_self).trans ((length_tab_codeOf_le _).trans (nu_le m))
  have h2 := h.1
  unfold nb bq bt
  omega

/-- The variables of `Phi m` have m bits. -/
theorem var_Phi_lt (hV : StVars) (m : ℕ) : ∀ C ∈ Phi m, ∀ l ∈ C, l.1 < 2 ^ m := by
  intro C hC l hl
  unfold Phi at hC
  split_ifs at hC with h1 h2 h3 h4
  · exact hV _ _ _ h2 C hC l hl
  · simp at hC
  · rw [List.mem_singleton.1 hC] at hl
    simp at hl
  · simp at hC
  · simp at hC

/-- The variables of `units w` are below the length of w. -/
theorem var_units_lt (w : List Bool) : ∀ C ∈ units w, ∀ l ∈ C, l.1 < w.length := by
  intro C hC l hl
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hC
  rw [List.mem_singleton.1 hl]
  exact List.mem_range.1 hi

/-! ### Nothing is cut off -/

variable {G : (MCode × List Unit × ℕ) × List Unit → Cnf} {fb : List Unit → Bool}

/-- With a pad of at least 2^(2m) units, `PhiF` writes `Phi m`. -/
theorem PhiF_eq (hG : ∀ (e : MCode) (L P : ℕ) (pad : List Unit), Fits e L P → 2 ^ nb e L ≤ pad.length → G ((e, List.replicate L (), P), pad) = tabF e L P)
    (hfb : ∀ m : ℕ, pos m = top (nu m) →
      (fb (List.replicate m ()) = true ↔ Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m))))
    (m : ℕ) {pad : List Unit} (hp : 2 ^ (2 * m) ≤ pad.length) : PhiF G fb (List.replicate m ()) pad = Phi m := by
  unfold PhiF Phi
  simp only [List.length_replicate]
  by_cases h1 : pos m < top (nu m)
  · rw [decide_eq_true h1, cond_true, if_pos h1]
    by_cases h2 : Fits (codeOf (nu m)) m (next m)
    · rw [decide_eq_true h2, cond_true, if_pos h2, hG _ _ _ _ h2 ((Nat.pow_le_pow_right (by norm_num) (nb_le h2)).trans hp)]
    · rw [decide_eq_false h2, cond_false, if_neg h2]
  · rw [decide_eq_false h1, cond_false, if_neg h1]
    by_cases h2 : pos m = top (nu m)
    · rw [decide_eq_true h2, cond_true, if_pos h2]
      by_cases h3 : Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m))
      · rw [(hfb m h2).2 h3, cond_true, if_pos h3]
      · have h4 : fb (List.replicate m ()) = false := by
          rw [← Bool.not_eq_true]
          exact fun h => h3 ((hfb m h2).1 h)
        rw [h4, cond_false, if_neg h3]
    · rw [decide_eq_false h2, cond_false, if_neg h2]

/-- What a round returns on x and at most 2^m answers, with a pad of at least 2^(2m+4) units, m = |x|. -/
theorem roundF_roundInput (hG : ∀ (e : MCode) (L P : ℕ) (pad : List Unit), Fits e L P → 2 ^ nb e L ≤ pad.length → G ((e, List.replicate L (), P), pad) = tabF e L P)
    (hfb : ∀ m : ℕ, pos m = top (nu m) →
      (fb (List.replicate m ()) = true ↔ Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m))))
    (hV : StVars) (x ans : List Bool) (ha : ans.length ≤ 2 ^ x.length) {pad : List Unit} (hp : 2 ^ (2 * x.length + 4) ≤ pad.length) :
    roundF G fb (roundInput x ans, pad) =
      bif decide (ans.length ≤ ofWord x) then true :: encCnf (Phi x.length ++ units (ans.map (fun b => !b) ++ [false]))
      else [false, !ans.getD (ofWord x) false] := by
  have h1 : 2 ^ (2 * x.length) ≤ pad.length := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hp
  have h2 : 2 ^ x.length + 1 ≤ pad.length := by
    have a1 : 2 ^ (x.length + 1) ≤ 2 ^ (2 * x.length + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a2 : 2 ^ (x.length + 1) = 2 ^ x.length * 2 := pow_succ 2 _
    have a3 : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
    omega
  simp only [roundF, aW_roundInput, xW_roundInput, mU_roundInput]
  rw [PhiF_eq hG hfb x.length h1, encF_eq]
  intro C hC l hl
  rcases List.mem_append.1 hC with hC | hC
  · have := var_Phi_lt hV x.length C hC l hl
    omega
  · have := var_units_lt _ C hC l hl
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at this
    omega

/-! ### Polynomial time -/

section Cert

variable {α : Type} [Enc α]

theorem mL_polyT : PolyT mL := by
  have hr : PolyT fun w : List Bool => List.range w.length := PolyT.range (Unary.of_length PolyT.id')
  unfold mL; fun_prop

theorem mU_polyT : PolyT mU := by
  have := mL_polyT
  unfold mU; fun_prop

theorem xW_polyT : PolyT xW := by
  have := mL_polyT
  unfold xW; fun_prop

theorem aW_polyT : PolyT aW := by
  have := mL_polyT
  unfold aW; fun_prop

theorem eW_polyT : PolyT eW := by
  have := mL_polyT
  unfold eW; fun_prop

theorem units_polyT {f : α → List Bool} (hf : PolyT f) : PolyT fun x => units (f x) := by
  have hr : PolyT fun x => List.range (f x).length := PolyT.range (Unary.of_length hf)
  unfold units; fun_prop

theorem encF_polyT {pad : α → List Unit} {φ : α → Cnf} (hp : PolyT pad) (hφ : PolyT φ) : PolyT fun x => encF (pad x) (φ x) := by
  unfold encF; fun_prop

theorem PhiF_polyT (h1 : StCertSched) (hG : PolyT G) (hfb : PolyT fb) {u pad : α → List Unit} (hu : PolyT u) (hp : PolyT pad) :
    PolyT fun x => PhiF G fb (u x) (pad x) := by
  obtain ⟨s1, s2, -, s4, s5, s6⟩ := h1
  have c1 : PolyT fun x => codeOf (nu (u x).length) :=
    PolyT.comp (f := fun v : List Unit => codeOf (nu v.length)) (g := u) s1 hu
  have c2 : PolyT fun x => next (u x).length := PolyT.comp (f := fun v : List Unit => next v.length) (g := u) s2 hu
  have c4 : PolyT fun x => decide (pos (u x).length < top (nu (u x).length)) :=
    PolyT.comp (f := fun v : List Unit => decide (pos v.length < top (nu v.length))) (g := u) s4 hu
  have c5 : PolyT fun x => decide (pos (u x).length = top (nu (u x).length)) :=
    PolyT.comp (f := fun v : List Unit => decide (pos v.length = top (nu v.length))) (g := u) s5 hu
  have c6 : PolyT fun x => decide (Fits (codeOf (nu (u x).length)) (u x).length (next (u x).length)) :=
    PolyT.comp (f := fun p : MCode × List Unit × ℕ => decide (Fits p.1 p.2.1.length p.2.2))
      (g := fun x => (codeOf (nu (u x).length), u x, next (u x).length)) s6 (PolyT.prodMk c1 (PolyT.prodMk hu c2))
  have c7 : PolyT fun x => G ((codeOf (nu (u x).length), u x, next (u x).length), pad x) :=
    PolyT.comp (f := G) (g := fun x => ((codeOf (nu (u x).length), u x, next (u x).length), pad x)) hG
      (PolyT.prodMk (PolyT.prodMk c1 (PolyT.prodMk hu c2)) hp)
  have c8 : PolyT fun x => fb (u x) := PolyT.comp (f := fb) (g := u) hfb hu
  unfold PhiF
  exact PolyT.cond' c4 (PolyT.cond' c6 c7 (PolyT.const [])) (PolyT.cond' c5 (PolyT.cond' c8 (PolyT.const [[]]) (PolyT.const [])) (PolyT.const []))

/-- One round is polynomial-time in the input word and the pad. -/
theorem roundF_polyT (h1 : StCertSched) (hG : PolyT G) (hfb : PolyT fb) : PolyT (roundF G fb) := by
  have a1 : PolyT fun p : List Bool × List Unit => aW p.1 := PolyT.comp aW_polyT PolyT.id'.fst
  have a2 : PolyT fun p : List Bool × List Unit => xW p.1 := PolyT.comp xW_polyT PolyT.id'.fst
  have a3 : PolyT fun p : List Bool × List Unit => mU p.1 := PolyT.comp mU_polyT PolyT.id'.fst
  have a4 : PolyT fun p : List Bool × List Unit => p.2 := PolyT.id'.snd
  have a5 := PhiF_polyT h1 hG hfb a3 a4
  have a6 := units_polyT (f := fun p : List Bool × List Unit => (aW p.1).map (fun b => !b) ++ [false]) (by fun_prop)
  have a7 := encF_polyT (φ := fun p : List Bool × List Unit => PhiF G fb (mU p.1) p.2 ++ units ((aW p.1).map (fun b => !b) ++ [false])) a4 (by fun_prop)
  unfold roundF; fun_prop

end Cert

end Round

end CircuitLowerBound
