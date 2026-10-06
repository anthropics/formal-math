/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.NeedPolynomial
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Program
public import ThreeSumApsp.Programs.Sec3.Theorem17.TimeBound.Total

/-!
# Theorem 17 for programs of the light language, with the two choices of parameters of Section 3.3

Theorem 17 reduces Exact Triangle to at most `4ng` instances of Lop-AE-SparseTri(n, D). As
a claim about programs: from every solver of Lop-AE-SparseTri there is a solver of Exact Triangle
whose time obeys the bound of the theorem, here with Strassen's algorithm for the matrix product
(`Claim.Theorem_17` with `strassen`).  The program is the host `et17`.

The host takes the procedures that compute `D` from `n` and `g` from `D` as parameters.  Here they
are the routines for the two choices of the proof of Theorem 19: "Let D be the largest power of four
with D ≤ n^{1/18} [...] and let g := ⌈D^{1/36}⌉", and "Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉".
The program is the solver's program, followed by the parameter routines (`paramProcs`), followed by
the procedures of the host.

1. The four routines are parameter procedures in the sense of the host (`paramProc_d5`,
   `paramProc_g5`, `paramProc_d26`, `paramProc_g26`).
2. The parameters and the numbers that the routines form are polynomially bounded
   (`polyBounded_paramD₅Nat`, `polyBounded_paramG₅Nat`, `polyBounded_wD5`, `polyBounded_wG5`,
   and the same for the second choice).  So the need of the host (word size, cells, depth of calls)
   is polynomially bounded if that of the solver is (`hostNeed_poly`).  With `et17_solves` this
   makes the host turn solvers into solvers (`host_of_paramProcs`).
3. The routines take `O(n)`, respectively `O(D)`, steps (`steps_tD5`, `steps_tG5`, `steps_tD26`,
   `steps_tG26`).  So the time of the host obeys the bound of the theorem (`obeysBound17_hostTime`).
   Together: `claim_theorem_17₅` and `claim_theorem_17₂₆`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The parameter routines -/

/-- The six parameter routines, placed behind a program of length `o`, at the numbers `o`, …,
`o + 5`.  The arguments are the numbers of the routines that a routine calls. -/
private def paramProcs (o : ℕ) : Program :=
  [powLtBody, rootCeilBody o, d26Body (o + 1), d5Body (o + 2), g5Body (o + 1), g26Body (o + 1)]

/-- A bound on the numbers that `d26Body` forms. -/
private def wD26 (n : ℕ) : ℕ := (n + 1) * (paramD₂₆Nat n + 1) + 19

/-- A bound on the numbers that `d5Body` forms. -/
private def wD5 (n : ℕ) : ℕ := wD26 n + 4 * (paramD₂₆Nat n + 1)

/-- A bound on the numbers that `g5Body` forms. -/
private def wG5 (D : ℕ) : ℕ := D * paramG₅Nat D + 37

/-- A bound on the numbers that `g26Body` forms.  It looks for the least `g` with `g^2000 ≥ D^63`,
since `0.0315 = 63/2000`. -/
private def wG26 (D : ℕ) : ℕ := D ^ 63 * paramG₂₆Nat D + 2001

/-- The routine number `i` stands at the place `Q.length + i` of the whole program. -/
private theorem paramProcs_get (Q R : Program) {i : ℕ} {body : Stmt}
    (h : (paramProcs Q.length)[i]? = some body) :
    (Q ++ paramProcs Q.length ++ R)[Q.length + i]? = some body := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R

/-- `d26Body` computes `⌊n^{1/18}⌋`. -/
private theorem paramProc_d26 (Q R : Program) :
    ParamProc (Q ++ paramProcs Q.length ++ R) (Q.length + 2) paramD₂₆Nat tD26 wD26 := by
  intro lim d x μ _ _ hw hd
  exact ⟨_, paramProcs_get Q R (i := 2) rfl, d26_spec (paramProcs_get Q R (i := 1) rfl)
    (paramProcs_get Q R (i := 0) rfl) hw (by omega)⟩

/-- `d5Body` computes the largest power of four that is at most `n^{1/18}`. -/
private theorem paramProc_d5 (Q R : Program) :
    ParamProc (Q ++ paramProcs Q.length ++ R) (Q.length + 3) paramD₅Nat tD5 wD5 := by
  intro lim d x μ _ _ hw hd
  have hroot : ((wD26 x : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by unfold wD5; exact_mod_cast (by omega)) hw
  have hpower : ((4 * (paramD₂₆Nat x + 1) : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by unfold wD5; exact_mod_cast (by omega)) hw
  exact ⟨_, paramProcs_get Q R (i := 3) rfl, d5_spec (paramProcs_get Q R (i := 2) rfl)
    (paramProcs_get Q R (i := 1) rfl) (paramProcs_get Q R (i := 0) rfl) hroot hpower (by omega)⟩

/-- `g5Body` computes `⌈D^{1/36}⌉`. -/
private theorem paramProc_g5 (Q R : Program) :
    ParamProc (Q ++ paramProcs Q.length ++ R) (Q.length + 4) paramG₅Nat tG5 wG5 := by
  intro lim d x μ hx _ hw hd
  exact ⟨_, paramProcs_get Q R (i := 4) rfl, g5_spec (paramProcs_get Q R (i := 1) rfl)
    (paramProcs_get Q R (i := 0) rfl) hx hw (by omega)⟩

/-- `g26Body` computes `⌈D^{0.0315}⌉`. -/
private theorem paramProc_g26 (Q R : Program) :
    ParamProc (Q ++ paramProcs Q.length ++ R) (Q.length + 5) paramG₂₆Nat tG26 wG26 := by
  intro lim d x μ hx _ hw hd
  exact ⟨_, paramProcs_get Q R (i := 5) rfl, g26_spec (paramProcs_get Q R (i := 1) rfl)
    (paramProcs_get Q R (i := 0) rfl) hx hw (by omega)⟩

/-! ## The parameters and the words are polynomially bounded -/

/-- `⌊n^{1/18}⌋ ≤ n`. -/
private theorem polyBounded_paramD₂₆Nat : PolyBounded fun n _ => paramD₂₆Nat n :=
  PolyBounded.fst.of_le fun n _ => paramD₂₆Nat_le n

/-- The largest power of four that is at most `n^{1/18}` is at most `⌊n^{1/18}⌋`; the `+ 1` serves
`n = 0`. -/
private theorem polyBounded_paramD₅Nat : PolyBounded fun n _ => paramD₅Nat n :=
  (by growth_poly [polyBounded_paramD₂₆Nat] :
    PolyBounded fun n _ => paramD₂₆Nat n + 1).of_le fun n _ => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [paramD₅Nat]
    · exact (paramD₅Nat_le_paramD₂₆Nat hn).trans (Nat.le_succ _)

/-- `⌈D^{1/36}⌉ ≤ D`; the `+ 1` serves `D = 0`. -/
private theorem polyBounded_paramG₅Nat {D : ℕ → ℕ} (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => paramG₅Nat (D n) :=
  (by growth_poly [hD] : PolyBounded fun n _ => D n + 1).of_le fun n _ => by
    rcases Nat.eq_zero_or_pos (D n) with h0 | hpos
    · simp [h0, paramG₅Nat, rootCeil]
    · exact (paramG₅Nat_le hpos).trans (Nat.le_succ _)

/-- `⌈D^{0.0315}⌉ ≤ D`; the `+ 1` serves `D = 0`. -/
private theorem polyBounded_paramG₂₆Nat {D : ℕ → ℕ} (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => paramG₂₆Nat (D n) :=
  (by growth_poly [hD] : PolyBounded fun n _ => D n + 1).of_le fun n _ => by
    rcases Nat.eq_zero_or_pos (D n) with h0 | hpos
    · simp [h0, paramG₂₆Nat, rootCeil]
    · exact (paramG₂₆Nat_le hpos).trans (Nat.le_succ _)

/-- The numbers of `d26Body`. -/
private theorem polyBounded_wD26 : PolyBounded fun n _ => wD26 n := by
  unfold wD26
  growth_poly [polyBounded_paramD₂₆Nat]

/-- The numbers of `d5Body`. -/
private theorem polyBounded_wD5 : PolyBounded fun n _ => wD5 n := by
  unfold wD5
  growth_poly [polyBounded_wD26, polyBounded_paramD₂₆Nat]

/-- The numbers of `g5Body`. -/
private theorem polyBounded_wG5 : PolyBounded fun n _ => wG5 (paramD₅Nat n) := by
  unfold wG5
  growth_poly [polyBounded_paramD₅Nat, polyBounded_paramG₅Nat polyBounded_paramD₅Nat]

/-- The numbers of `g26Body`. -/
private theorem polyBounded_wG26 : PolyBounded fun n _ => wG26 (paramD₂₆Nat n) := by
  unfold wG26
  growth_poly [polyBounded_paramD₂₆Nat, polyBounded_paramG₂₆Nat polyBounded_paramD₂₆Nat]

/-! ## The time of the parameter routines -/

/-- `⌊n^{1/18}⌋ ≤ n`. -/
private theorem steps_paramD₂₆Nat : StepsMon (fun θ => paramD₂₆Nat θ.n) 1 0 0 :=
  steps_n.of_le fun θ _ => paramD₂₆Nat_le θ.n

/-- `d26Body` takes a constant number of steps for each number up to `⌊n^{1/18}⌋ + 1`. -/
private theorem steps_tD26 : StepsMon (fun θ => tD26 θ.n) 1 0 0 := by
  unfold tD26
  growth [steps_paramD₂₆Nat]

/-- `d5Body` calls `d26Body` and then multiplies by four `⌊log₄ ⌊n^{1/18}⌋⌋` times. -/
private theorem steps_tD5 : StepsMon (fun θ => tD5 θ.n) 1 0 0 := by
  unfold tD5
  growth [steps_tD26, steps_paramD₂₆Nat, Scale.SoftO.log]

/-- `g5Body` takes a constant number of steps for each number up to `⌈D^{1/36}⌉ ≤ D`. -/
private theorem steps_tG5 : StepsMon (fun θ => tG5 θ.D) 0 2 0 := by
  have hg : StepsMon (fun θ => paramG₅Nat θ.D) 0 2 0 :=
    steps_D.of_le fun _ hθ => paramG₅Nat_le hθ.one_le_D_nat
  unfold tG5
  growth [hg]

/-- `g26Body` takes a constant number of steps for each number up to `⌈D^{0.0315}⌉ ≤ D`. -/
private theorem steps_tG26 : StepsMon (fun θ => tG26 θ.D) 0 2 0 := by
  have hg : StepsMon (fun θ => paramG₂₆Nat θ.D) 0 2 0 :=
    steps_D.of_le fun _ hθ => paramG₂₆Nat_le hθ.one_le_D_nat
  unfold tG26
  growth [hg]

/-! ## The host with parameter routines -/

/-- The host over two of the parameter routines, at the places `i` and `j` of `paramProcs`, turns a
solver of Lop-AE-SparseTri into a solver of Exact Triangle and keeps the need polynomial. -/
private theorem host_of_paramProcs {Dfun Gfun tD tG wD wG : ℕ → ℕ} {i j : ℕ}
    (hD : ∀ Q R, ParamProc (Q ++ paramProcs Q.length ++ R) (Q.length + i) Dfun tD wD)
    (hG : ∀ Q R, ParamProc (Q ++ paramProcs Q.length ++ R) (Q.length + j) Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n)
    (hpoly : ∀ r, PolyNeedN r → PolyNeed (hostNeed Dfun Gfun wD wG r)) :
    ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves etTask (Q ++ R) p' (hostTime Dfun Gfun tD tG Tn)
        (hostNeed Dfun Gfun wD wG r) ∧ PolyNeed (hostNeed Dfun Gfun wD wG r) := by
  intro Q pS Tn r hr hs
  have h := et17_solves (P₀ := Q ++ paramProcs Q.length) (hs.append _) (hD Q) (hG Q) hpos
  rw [List.append_assoc] at h
  exact ⟨_, _, h, hpoly r hr⟩

/-- **Theorem 17** for programs of the light language, with D "the largest power of four with D ≤
n^{1/18}" and "g := ⌈D^{1/36}⌉". -/
theorem claim_theorem_17₅ : Claim.Theorem_17 lightModel strassen paramD₅ paramG₅ :=
  claim17_of_host strassen paramD₅ paramG₅ _ _
    (host_of_paramProcs paramProc_d5 paramProc_g5 (fun n _ => one_le_paramD₅Nat n) fun _ =>
      hostNeed_poly polyBounded_paramD₅Nat (polyBounded_paramG₅Nat polyBounded_paramD₅Nat)
        polyBounded_wD5 polyBounded_wG5)
    (obeysBound17_hostTime paramD₅ paramG₅ paramD₅Nat_eq (fun n _ => paramG₅Nat_eq n)
      steps_tD5.withinBuild steps_tG5.withinBuild)

/-- **Theorem 17** for programs of the light language, with "D := ⌊n^{1/18}⌋ and g :=
⌈D^{0.0315}⌉". -/
theorem claim_theorem_17₂₆ : Claim.Theorem_17 lightModel strassen paramD₂₆ paramG₂₆ :=
  claim17_of_host strassen paramD₂₆ paramG₂₆ _ _
    (host_of_paramProcs paramProc_d26 paramProc_g26 (fun _ hn => one_le_paramD₂₆Nat hn) fun _ =>
      hostNeed_poly polyBounded_paramD₂₆Nat (polyBounded_paramG₂₆Nat polyBounded_paramD₂₆Nat)
        polyBounded_wD26 polyBounded_wG26)
    (obeysBound17_hostTime paramD₂₆ paramG₂₆ paramD₂₆Nat_eq (fun _ hn => paramG₂₆Nat_eq hn)
      steps_tD26.withinBuild steps_tG26.withinBuild)

end Light.Sec3
