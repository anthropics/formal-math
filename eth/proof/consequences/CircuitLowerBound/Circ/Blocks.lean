/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.InterfacesPolyT
import Mathlib.Tactic

/-! # Circuits as lists of gates: wires, blocks, chains, numbers in binary

General facts for circuits that are written block by block, with the numbers of the wires in closed
form; they serve the circuit lower bound for E^NP (Section 7 of the paper: E^NP does not have
circuits of linear size).

* `Obeys v n C`: in the values v of the wires, the gates of the list C, whose wires are n, n + 1, …,
  have their values. `WFa n C`: these gates read wires before their own. Both split along `++` and
  along
  `(List.range w).flatMap f` with pieces of equal length. The values of the wires of a circuit on an
  input obey the circuit (`obeys_wires`).
* Chains of gates that compute the AND or the OR of many wires (`chain_all`, `chain_any`).
* `num b w`: the number with the binary digits b 0, …, b (w − 1), lowest first; the chains of half
  adders and of full adders (`half_adder`, `full_adder`). -/

@[expose] public section

namespace CircuitLowerBound.Blocks

open ENP Groundwork

/-! ### Gates -/

/-- The values of a function of two bits at 00, 01, 10, 11. -/
abbrev B4 : Type := Bool × Bool × Bool × Bool

def opZero : B4 := (false, false, false, false)
def opOne : B4 := (true, true, true, true)
def opAnd : B4 := (false, false, false, true)
def opOr : B4 := (false, true, true, true)
def opXor : B4 := (false, true, true, false)
/-- The first input. -/
def opFst : B4 := (false, false, true, true)
/-- The first input and not the second. -/
def opAndN : B4 := (false, false, true, false)

/-- The value of a gate in the values v of the wires. -/
def gval (v : ℕ → Bool) (g : GateD) : Bool := g.toGate.op (v g.2.1) (v g.2.2)

theorem gval_zero (v : ℕ → Bool) (i j : ℕ) : gval v (opZero, i, j) = false := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opZero, hi, hj]

theorem gval_one (v : ℕ → Bool) (i j : ℕ) : gval v (opOne, i, j) = true := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opOne, hi, hj]

theorem gval_and (v : ℕ → Bool) (i j : ℕ) : gval v (opAnd, i, j) = (v i && v j) := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opAnd, hi, hj]

theorem gval_or (v : ℕ → Bool) (i j : ℕ) : gval v (opOr, i, j) = (v i || v j) := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opOr, hi, hj]

theorem gval_xor (v : ℕ → Bool) (i j : ℕ) : gval v (opXor, i, j) = (v i ^^ v j) := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opXor, hi, hj]

theorem gval_fst (v : ℕ → Bool) (i j : ℕ) : gval v (opFst, i, j) = v i := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opFst, hi, hj]

theorem gval_andN (v : ℕ → Bool) (i j : ℕ) : gval v (opAndN, i, j) = (v i && !v j) := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opAndN, hi, hj]

/-! ### Lists of gates -/

/-- In the values v, the gates of the list, whose wires are n, n + 1, …, have their values. -/
def Obeys (v : ℕ → Bool) : ℕ → List GateD → Prop
  | _, [] => True
  | n, g :: C => v n = gval v g ∧ Obeys v (n + 1) C

/-- The gates of the list, whose wires are n, n + 1, …, read wires before their own. -/
def WFa : ℕ → List GateD → Prop
  | _, [] => True
  | n, g :: C => (g.2.1 < n ∧ g.2.2 < n) ∧ WFa (n + 1) C

theorem obeys_append (v : ℕ → Bool) (n : ℕ) (C D : List GateD) : Obeys v n (C ++ D) ↔ Obeys v n C ∧ Obeys v (n + C.length) D := by
  induction C generalizing n with
  | nil => simp [Obeys]
  | cons g C ih =>
    simp only [List.cons_append, Obeys, ih, List.length_cons, and_assoc]
    rw [show n + 1 + C.length = n + (C.length + 1) by omega]

theorem wfa_append (n : ℕ) (C D : List GateD) : WFa n (C ++ D) ↔ WFa n C ∧ WFa (n + C.length) D := by
  induction C generalizing n with
  | nil => simp [WFa]
  | cons g C ih =>
    simp only [List.cons_append, WFa, ih, List.length_cons, and_assoc]
    rw [show n + 1 + C.length = n + (C.length + 1) by omega]

theorem length_flatMap_const {α : Type} {k : ℕ} (f : ℕ → List α) (hf : ∀ i, (f i).length = k) (w : ℕ) :
    ((List.range w).flatMap f).length = k * w := by
  induction w with
  | zero => simp
  | succ w ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [hf]; ring

theorem obeys_flatMap (v : ℕ → Bool) (n : ℕ) {k : ℕ} (f : ℕ → List GateD) (hf : ∀ i, (f i).length = k) (w : ℕ) :
    Obeys v n ((List.range w).flatMap f) ↔ ∀ i < w, Obeys v (n + k * i) (f i) := by
  induction w with
  | zero => simp [Obeys]
  | succ w ih =>
    rw [List.range_succ, List.flatMap_append, obeys_append, ih, length_flatMap_const f hf]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h w (by omega)⟩

theorem wfa_flatMap (n : ℕ) {k : ℕ} (f : ℕ → List GateD) (hf : ∀ i, (f i).length = k) (w : ℕ) :
    WFa n ((List.range w).flatMap f) ↔ ∀ i < w, WFa (n + k * i) (f i) := by
  induction w with
  | zero => simp [WFa]
  | succ w ih =>
    rw [List.range_succ, List.flatMap_append, wfa_append, ih, length_flatMap_const f hf]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h w (by omega)⟩

theorem map_eq_flatMap {α : Type} (g : ℕ → α) (w : ℕ) : (List.range w).map g = (List.range w).flatMap fun i => [g i] := by
  induction w with
  | zero => rfl
  | succ w ih => rw [List.range_succ, List.map_append, List.flatMap_append, ih]; rfl

theorem obeys_map (v : ℕ → Bool) (n : ℕ) (g : ℕ → GateD) (w : ℕ) : Obeys v n ((List.range w).map g) ↔ ∀ i < w, v (n + i) = gval v (g i) := by
  rw [map_eq_flatMap, obeys_flatMap v n (k := 1) _ (fun _ => rfl)]
  simp [Obeys]

theorem wfa_map (n : ℕ) (g : ℕ → GateD) (w : ℕ) : WFa n ((List.range w).map g) ↔ ∀ i < w, (g i).2.1 < n + i ∧ (g i).2.2 < n + i := by
  rw [map_eq_flatMap, wfa_flatMap n (k := 1) _ (fun _ => rfl)]
  simp [WFa]

theorem wf_of_wfa {n : ℕ} {C : List GateD} (h : WFa n C) : WF n C := by
  induction C generalizing n with
  | nil => intro t ht; simp at ht
  | cons g C ih =>
    intro t ht
    cases t with
    | zero => simpa using h.1
    | succ t =>
      have := ih h.2 t (by simpa using ht)
      simp only [List.getElem_cons_succ]
      omega

/-! ### The wires of a circuit -/

theorem wires_cons (x : List Bool) (G : Gate) (C : Circuit) : wires x (G :: C) = wires (x ++ [G.op (x.getD G.in₁ false) (x.getD G.in₂ false)]) C := rfl

theorem prefix_wires (x : List Bool) (C : Circuit) : x <+: wires x C := by
  induction C generalizing x with
  | nil => exact List.prefix_rfl
  | cons G C ih => rw [wires_cons]; exact (List.prefix_append _ _).trans (ih _)

theorem getD_of_prefix {l₁ l₂ : List Bool} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) : l₂.getD i false = l₁.getD i false := by
  obtain ⟨r, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

/-- The input wires carry the input. -/
theorem wires_input (x : List Bool) (C : Circuit) {i : ℕ} (hi : i < x.length) : (wires x C).getD i false = x.getD i false :=
  getD_of_prefix (prefix_wires x C) hi

/-- The values of the wires of a circuit on an input obey the circuit. -/
theorem obeys_wires (x : List Bool) (C : List GateD) (h : WFa x.length C) : Obeys (fun i => (wires x (toC C)).getD i false) x.length C := by
  induction C generalizing x with
  | nil => trivial
  | cons g C ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have e : wires x (toC (g :: C)) = wires (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]) (toC C) := rfl
    have hl : (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]).length = x.length + 1 := by simp
    have hp := prefix_wires (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]) (toC C)
    have ih' := ih (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]) (by rw [hl]; exact h3)
    rw [hl] at ih'
    refine ⟨?_, by rw [e]; exact ih'⟩
    simp only [gval]
    rw [e, getD_of_prefix hp (by omega), getD_of_prefix hp (by omega), getD_of_prefix hp (by omega), List.getD_append _ _ _ _ h1,
      List.getD_append _ _ _ _ h2, List.getD_append_right _ _ _ _ le_rfl]
    simp

/-! ### Chains -/

/-- The wire before place i of a chain that begins at the wire `off` and starts from the wire
`init`. At i = (length of the chain) it is the last wire of the chain. -/
def prevW (off init i : ℕ) : ℕ := if i = 0 then init else off + i - 1

theorem prevW_succ (off init i : ℕ) : prevW off init (i + 1) = off + i := by simp [prevW]

theorem prevW_lt {off init i : ℕ} (h : init < off) : prevW off init i < off + i := by
  unfold prevW; split_ifs <;> omega

/-- A chain of gates «the wire before, and p i». -/
theorem chain_all (v : ℕ → Bool) (off init len : ℕ) (p : ℕ → Bool) (h : ∀ i < len, v (off + i) = (v (prevW off init i) && p i)) :
    ∀ m ≤ len, v (prevW off init m) = (v init && decide (∀ i < m, p i = true)) := by
  intro m
  induction m with
  | zero => intro _; simp [prevW]
  | succ m ih =>
    intro hm
    rw [prevW_succ, h m hm, ih (by omega), Bool.and_assoc]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h m (by omega)⟩

/-- A chain of gates «the wire before, or p i». -/
theorem chain_any (v : ℕ → Bool) (off init len : ℕ) (p : ℕ → Bool) (h : ∀ i < len, v (off + i) = (v (prevW off init i) || p i)) :
    ∀ m ≤ len, v (prevW off init m) = (v init || decide (∃ i < m, p i = true)) := by
  intro m
  induction m with
  | zero => intro _; simp [prevW]
  | succ m ih =>
    intro hm
    rw [prevW_succ, h m hm, ih (by omega), Bool.or_assoc]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨i, hi, h1⟩ | h2)
      · exact ⟨i, by omega, h1⟩
      · exact ⟨m, by omega, h2⟩
    · rintro ⟨i, hi, h1⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact .inl ⟨i, h, h1⟩
      · exact .inr h1

/-! ### Numbers in binary -/

/-- The number with the binary digits b 0, …, b (w − 1), lowest first. -/
def num (b : ℕ → Bool) (w : ℕ) : ℕ := ofWord ((List.range w).map b)

theorem ofWord_append (l₁ l₂ : List Bool) : ofWord (l₁ ++ l₂) = ofWord l₁ + 2 ^ l₁.length * ofWord l₂ := by
  induction l₁ with
  | nil => simp [ofWord]
  | cons b l ih => simp only [List.cons_append, ofWord, ih, List.length_cons, pow_succ]; ring

theorem num_zero (b : ℕ → Bool) : num b 0 = 0 := rfl

theorem num_succ (b : ℕ → Bool) (w : ℕ) : num b (w + 1) = num b w + 2 ^ w * (b w).toNat := by
  rw [num, List.range_succ, List.map_append, ofWord_append]
  simp [num, ofWord]

theorem num_lt (b : ℕ → Bool) (w : ℕ) : num b w < 2 ^ w := by
  have := ofWord_lt ((List.range w).map b)
  simpa [num] using this

theorem num_congr {b c : ℕ → Bool} {w : ℕ} (h : ∀ i < w, b i = c i) : num b w = num c w := by
  unfold num
  exact congrArg ofWord (List.map_congr_left fun i hi => h i (List.mem_range.1 hi))

theorem num_testBit (x w : ℕ) : num x.testBit w = x % 2 ^ w := by
  induction w with
  | zero => simp [num_zero, Nat.mod_one]
  | succ w ih =>
    rw [num_succ, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ w) with h | h <;> simp [h]

theorem num_false (w : ℕ) : num (fun _ => false) w = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => rw [num_succ, ih]; simp

theorem getD_toWord {n j k : ℕ} (hk : k < n) : (toWord n j).getD k false = j.testBit k := by
  induction n generalizing j k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      simp only [toWord, List.getD_cons_zero, Nat.testBit_zero]
    | succ k =>
      simp only [toWord, List.getD_cons_succ]
      rw [ih (by omega), Nat.testBit_succ]

/-- A chain of half adders: s i = a i ⊕ c i, c (i+1) = a i ∧ c i. -/
theorem half_adder (a s c : ℕ → Bool) (w : ℕ) (hs : ∀ i < w, s i = (a i ^^ c i)) (hc : ∀ i < w, c (i + 1) = (a i && c i)) :
    ∀ m ≤ w, num s m + 2 ^ m * (c m).toNat = num a m + (c 0).toNat := by
  intro m
  induction m with
  | zero => intro _; simp [num_zero]
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    rw [num_succ, num_succ, hs m hm, hc m hm, pow_succ]
    generalize 2 ^ m = p at h1 ⊢
    generalize c m = cm at h1 ⊢
    cases a m <;> cases cm <;> simp at h1 ⊢ <;> omega

/-- A chain of full adders: s i = a i ⊕ d i ⊕ c i, c (i+1) = (a i ∧ d i) ∨ ((a i ⊕ d i) ∧ c i). -/
theorem full_adder (a d s c : ℕ → Bool) (w : ℕ) (hs : ∀ i < w, s i = ((a i ^^ d i) ^^ c i))
    (hc : ∀ i < w, c (i + 1) = ((a i && d i) || ((a i ^^ d i) && c i))) :
    ∀ m ≤ w, num s m + 2 ^ m * (c m).toNat = num a m + num d m + (c 0).toNat := by
  intro m
  induction m with
  | zero => intro _; simp [num_zero]
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    rw [num_succ, num_succ, num_succ, hs m hm, hc m hm, pow_succ]
    generalize 2 ^ m = p at h1 ⊢
    generalize c m = cm at h1 ⊢
    cases a m <;> cases d m <;> cases cm <;> simp at h1 ⊢ <;> omega

end CircuitLowerBound.Blocks
