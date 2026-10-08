/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# The tables of the coefficients of Schönhage's identity

Section 2.2 defines, for each of the ten terms λ of Schönhage's identity, two linear forms φ_λ and
ψ_λ in seven variables each; step (2) of the recursion applies them.  coef(phi) writes the
coefficient φ_λ(s) of the variable number s < 7 in the form of the term number λ < 10 to the cell
phi + 7 λ + s, and ψ_λ(t) to the cell phi + 70 + 7 λ + t.  The body is a straight line of 140
stores, made from the two tables `Spec.phiTable` and `Spec.psiTable`.  `storeSigns_spec` treats
such a line of stores by induction on the list, and `coef_entry`, the specification that the callers
of the procedure assume, applies it to the two tables.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-- A coefficient as an expression: 1, 0, or 0 - 1. -/
def signExpr (x : ℤ) : Expr := if x = 1 then k 1 else if x = 0 then k 0 else k 0 -' k 1

/-- The only local variable of coef: its argument phi. -/
abbrev Coef.Dest : ℕ := 0

open Coef in
/-- Stores the numbers of the list l, each of them 1, 0 or -1, into the cells from phi + i on. -/
def storeSigns : ℕ → List ℤ → Stmt
  | _, [] => .skip
  | i, x :: l => .store (v Dest +' k i) (signExpr x) ;; storeSigns (i + 1) l

/-- coef(phi). -/
def coefBody : Stmt := storeSigns 0 (Spec.phiFlat ++ Spec.psiFlat)

/-- A coefficient's expression stays within the limits and gives the coefficient. -/
private theorem signExpr_gives (h1 : (1 : ℤ) ≤ lim.word) {x : ℤ} (hx : x = 1 ∨ x = 0 ∨ x = -1)
    (σ : State) : (signExpr x).Gives lim σ x := by
  rcases hx with rfl | rfl | rfl <;> simp [signExpr] <;> omega

/-- A coefficient's expression costs at most 3 steps. -/
private theorem signExpr_cost (x : ℤ) : (signExpr x).cost ≤ 3 := by
  unfold signExpr
  split_ifs <;> simp

/-- **storeSigns** writes the list to the cells from base + i on, changes nothing else, and takes
at most 7 steps for each number. -/
theorem storeSigns_spec (std : Std lim) {base : ℕ} (l : List ℤ) (i : ℕ) (μ : ℕ → ℤ)
    (hl : ∀ x ∈ l, x = 1 ∨ x = 0 ∨ x = -1) (hsp : base + i + l.length ≤ lim.space) :
    Ends lim P d (storeSigns i l) ⟨frame [base], μ⟩ (7 * l.length) fun σ' =>
      Seg σ'.mem (base + i) l ∧ SameOutside μ σ'.mem (base + i) l.length := by
  light_facts std
  induction l generalizing i μ with
  | nil => exact Ends.skip ⟨Seg.nil, .refl⟩
  | cons x l ih =>
    rw [List.length_cons] at hsp ⊢
    have hcost := signExpr_cost x
    -- mem[phi + i] := x, in at most 7 steps, and then the rest of the list
    refine Ends.storeToThen (base + i) x
      ((ih (i + 1) _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (by omega)).mono
        (by simp; omega) ?_)
      (he := ⟨by light_side, signExpr_gives (by omega) (hl x List.mem_cons_self) _, by omega⟩)
      (hT := by simp; omega)
    rintro σ' ⟨hrest, same⟩
    refine ⟨seg_cons.2 ⟨?_, by rwa [Nat.add_assoc]⟩, fun b hb => ?_⟩
    · rw [same (base + i) (Or.inl (by omega)), Function.update_self]
    · rw [same b (by omega), Function.update_of_ne (by omega)]

/-- All coefficients are 1, 0 or -1. -/
private theorem coef_signs :
    ∀ x ∈ Spec.phiFlat ++ Spec.psiFlat, x = 1 ∨ x = 0 ∨ x = -1 := by
  simp [Spec.phiFlat, Spec.psiFlat, Spec.phiTable, Spec.psiTable]

/-- **coef** writes the two tables and changes nothing else, in 7 · 140 steps: the specification
that its callers assume. -/
theorem coef_entry (std : Std lim) (hP : P[pCoef]? = some coefBody) {c : ℕ} (hc : 980 ≤ c) :
    CoefSpec lim P c := by
  intro phi μ hsp d _
  have hlen : (Spec.phiFlat ++ Spec.psiFlat).length = 140 := by simp
  have hphi := Spec.length_phiFlat
  refine ⟨coefBody, hP, (storeSigns_spec std _ 0 μ coef_signs (by omega)).mono (by omega) ?_⟩
  rintro σ' ⟨hcells, same⟩
  rw [Nat.add_zero] at hcells same
  obtain ⟨hphiCells, hpsiCells⟩ := seg_append.1 hcells
  exact ⟨hphiCells, hphi ▸ hpsiCells, hlen ▸ same⟩

end Light.Sec2
