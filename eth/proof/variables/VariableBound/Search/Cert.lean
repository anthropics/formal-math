/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Search.Correct
public import PaddedDescent.F.FuelCert

/-! # Step 2 of Appendix D as a program: the certificate

Proves `VariableBound.StCertSearchD`: the search for the checks is polynomial-time (`PolyT`) in the
pad, jointly in everything it reads, if the function that returns X(𝓛) is; the numbers m, n̄, β, r̄,
t̄ are given in unary.

* `loadSum` and `upsNum`: all exponents are numbers given in unary or lengths of lists, so the
  integers have polynomially many bits, as Step 2 of Appendix D says of Υ.
* `argminD`: a fold whose state is empty or a pair (candidate, its key), so its length is bounded.
* `searchD`: a fold whose state the pad cuts off after every round (`PaddedDescent.F.foldl_cap`). -/

public section

namespace VariableBound.Search

open Groundwork PaddedDescent.F

variable {α : Type} [Enc α]

/-- Σ_E 2^load(E) is polynomial-time, for m in unary. -/
@[fun_prop] theorem loadSum_polyT {m : α → ℕ} {L : α → List (List ℕ)} (hm : Unary m) (hL : PolyT L) : PolyT fun x => loadSum (m x) (L x) := by
  unfold loadSum
  fun_prop

/-- `upsNum` with the powers taken in the natural numbers. -/
theorem upsNum_eq (m nb β rb tb : ℕ) (x : ℤ) (L : List (List ℕ)) :
    upsNum m nb β rb tb x L = ((4 ^ L.length * 2 ^ tb * (15 * nb) ^ (rb - L.length) : ℕ) : ℤ) * x +
      ((3 ^ L.length * 2 ^ (β - 1) * (15 * nb + 16) ^ (rb - L.length) * loadSum m L : ℕ) : ℤ) := by
  unfold upsNum
  push_cast
  rfl

/-- The numerator of Υ is polynomial-time, for m, n̄, β, r̄, t̄ in unary. -/
@[fun_prop] theorem upsNum_polyT {m nb β rb tb : α → ℕ} {v : α → ℤ} {L : α → List (List ℕ)} (hm : Unary m) (hnb : Unary nb) (hβ : Unary β) (hrb : Unary rb)
    (htb : Unary tb) (hv : PolyT v) (hL : PolyT L) : PolyT fun x => upsNum (m x) (nb x) (β x) (rb x) (tb x) (v x) (L x) := by
  have := hnb.poly
  simp only [upsNum_eq]
  fun_prop

omit [Enc α] in
/-- A step of `argminD` returns the new pair or the old state. -/
theorem stepD_cases (key : List ℕ → ℤ) (best : Option (List ℕ × ℤ)) (l : List ℕ) : stepD key best l = some (l, key l) ∨ stepD key best l = best := by
  cases best with
  | none => exact Or.inl rfl
  | some b =>
    simp only [stepD, Option.elim_some]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl

omit [Enc α] in
/-- The state of `argminD` is empty or a pair (l, key l) for a member l of the list. -/
theorem fold_stepD_mem (key : List ℕ → ℤ) (S : List (List ℕ)) : ∀ (r : List (List ℕ)) (c : Option (List ℕ × ℤ)), (∀ l ∈ r, l ∈ S) →
    (c = none ∨ ∃ l ∈ S, c = some (l, key l)) → (r.foldl (stepD key) c = none ∨ ∃ l ∈ S, r.foldl (stepD key) c = some (l, key l)) := by
  intro r
  induction r with
  | nil => intro c _ h; exact h
  | cons a t ih =>
    intro c hr hc
    rw [List.foldl_cons]
    refine ih _ (fun l hl => hr l (List.mem_cons_of_mem _ hl)) ?_
    rcases stepD_cases key c a with h | h
    · exact Or.inr ⟨a, hr a List.mem_cons_self, h⟩
    · rw [h]; exact hc

/-- The first member with the smallest key is polynomial-time, if the key and the list are. -/
theorem argminD_polyT {key : α → List ℕ → ℤ} {fam : α → List (List ℕ)} (hk : PolyT fun p : α × List ℕ => key p.1 p.2) (hf : PolyT fam) :
    PolyT fun x => argminD (key x) (fam x) := by
  have hpair : PolyT fun p : α × List ℕ => (p.2, key p.1 p.2) := by fun_prop
  obtain ⟨b, hb, hbl⟩ := PolyT.len_bound_mem (f := fun x l => (l, key x l)) hpair hf
  have hstep : PolyT fun p : α × Option (List ℕ × ℤ) × List ℕ => stepD (key p.1) p.2.1 p.2.2 := by
    have h1 : PolyT fun p : α × Option (List ℕ × ℤ) × List ℕ => key p.1 p.2.2 :=
      PolyT.comp (g := fun p : α × Option (List ℕ × ℤ) × List ℕ => (p.1, p.2.2)) hk (by fun_prop)
    have h2 : PolyT fun q : (α × Option (List ℕ × ℤ) × List ℕ) × List ℕ × ℤ => key q.1.1 q.1.2.2 :=
      PolyT.comp (g := fun q : (α × Option (List ℕ × ℤ) × List ℕ) × List ℕ × ℤ => (q.1.1, q.1.2.2)) hk (by fun_prop)
    unfold stepD
    fun_prop
  have hfold : PolyT fun x => (fam x).foldl (stepD (key x)) none := by
    refine PolyT.foldl (g := fun x best l => stepD (key x) best l) hf (PolyT.const none) hstep ⟨fun n => b n + 4, hb.add (PB.const 4), fun x k => ?_⟩
    rcases fold_stepD_mem (key x) (fam x) ((fam x).take k) none (fun l hl => List.mem_of_mem_take hl) (Or.inl rfl) with h | ⟨l, hl, h⟩
    · rw [h, len_none]; show 2 ≤ b (len x) + 4; omega
    · rw [h, len_some]; show _ ≤ b (len x) + 4; have := hbl x l hl; omega
  simp only [argminD_eq]
  fun_prop

/-- One round is polynomial-time, if the function that returns X(𝓛) and the list of the candidates
are; m, n̄, β, r̄, t̄ in unary. -/
theorem roundD_polyT {evX : α → List (List ℕ) → ℤ} {fam : α → List (List ℕ)} {m nb β rb tb : α → ℕ} {L : α → List (List ℕ)}
    (he : PolyT fun p : α × List (List ℕ) => evX p.1 p.2) (hf : PolyT fam) (hm : Unary m) (hnb : Unary nb) (hβ : Unary β) (hrb : Unary rb) (htb : Unary tb)
    (hL : PolyT L) : PolyT fun x => roundD (evX x) (fam x) (m x) (nb x) (β x) (rb x) (tb x) (L x) := by
  have h1 : PolyT fun x => evX x (L x) := PolyT.comp (g := fun x => (x, L x)) he (by fun_prop)
  have h2 : PolyT fun p : α × List ℕ => evX p.1 (L p.1 ++ [p.2]) := PolyT.comp (g := fun p : α × List ℕ => (p.1, L p.1 ++ [p.2])) he (by fun_prop)
  have h3 : PolyT fun p : α × List ℕ => upsNum (m p.1) (nb p.1) (β p.1) (rb p.1) (tb p.1) (evX p.1 (L p.1 ++ [p.2])) (L p.1 ++ [p.2]) :=
    upsNum_polyT (hm.comp PolyT.id'.fst) (hnb.comp PolyT.id'.fst) (hβ.comp PolyT.id'.fst) (hrb.comp PolyT.id'.fst) (htb.comp PolyT.id'.fst) h2 (by fun_prop)
  have h4 := argminD_polyT (key := fun x l => upsNum (m x) (nb x) (β x) (rb x) (tb x) (evX x (L x ++ [l])) (L x ++ [l])) h3 hf
  unfold roundD
  fun_prop

end VariableBound.Search

namespace VariableBound

open Groundwork PaddedDescent.F

/-- Step 2, the algorithm as a program: the search is polynomial-time in the pad, jointly in
everything it reads, if the function that returns X(𝓛) is; m, n̄, β, r̄, t̄ are given in unary. -/
theorem stCertSearchD : StCertSearchD := by
  intro α _ pad evX fam m nb β rb tb hp he hf hm hnb hβ hrb htb
  have h1 : PolyT fun p : α × List (List ℕ) × ℕ => roundD (evX p.1) (fam p.1) (m p.1) (nb p.1) (β p.1) (rb p.1) (tb p.1) p.2.1 :=
    Search.roundD_polyT (evX := fun p : α × List (List ℕ) × ℕ => evX p.1)
      (PolyT.comp (g := fun q : (α × List (List ℕ) × ℕ) × List (List ℕ) => (q.1.1, q.2)) he (by fun_prop)) (PolyT.comp hf PolyT.id'.fst)
      (hm.comp PolyT.id'.fst) (hnb.comp PolyT.id'.fst) (hβ.comp PolyT.id'.fst) (hrb.comp PolyT.id'.fst) (htb.comp PolyT.id'.fst) PolyT.id'.snd.fst
  unfold searchD
  exact foldl_cap (pad := pad) (l := fun x => List.range (rb x)) (a := fun _ => ([] : List (List ℕ)))
    (g := fun x L _ => roundD (evX x) (fam x) (m x) (nb x) (β x) (rb x) (tb x) L) [] hp (PolyT.range hrb) (PolyT.const []) h1

end VariableBound
