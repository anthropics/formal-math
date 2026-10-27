/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.ProgDefs
public import ClauseBound.ParityChecks.CertLib
public import PaddedDescent.F.CertMark

/-! # Certificates for the parameters of the count through parity checks

All numbers that the program of proof/rates/ClauseBound/ParityChecks/ProgDefs.lean computes from the
number n of variables, the bound Δ on the occurrences of a variable and the number m of clauses are
given in unary when n, Δ
and m are: the five parameters of the choice of the checks (`parQ_QU`), the cap for the marks, the
code parameters, the bounds for the rows and columns of the incidences, and the bounds for the
shared bits and the size of the networks of marks (`UbOL_unary`, `PbOL_unary`). The lemmas on
numbers made from the five parameters are stated for any function q of the context whose five
components are given in unary. -/

public section

namespace ClauseBound.ParityChecks.CertPar

open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib

variable {α : Type} [Enc α]

/-! ### The five parameters -/

/-- ⌈log₂(2Δ)⌉ is given in unary. -/
theorem LD_unary {Δ : α → ℕ} (hΔ : PolyT Δ) : Unary fun x => LD (Δ x) := clog_unary ((PolyT.const 2).mul hΔ)

/-- nb is given in unary if n is. -/
theorem nbOf_unary {n Δ : α → ℕ} (hn : Unary n) (hΔ : PolyT Δ) : Unary fun x => nbOf (n x) (Δ x) := unary_div hn (LD_unary hΔ).poly

/-- β₀ is given in unary if nb is. -/
theorem beta0_unary {m nb : α → ℕ} (hm : PolyT m) (hnb : Unary nb) : Unary fun x => beta0 (m x) (nb x) :=
  clog_unary (choose_polyT hm (hnb.add (Unary.const 1)))

/-- r is given in unary if n and β₀ are. -/
theorem rOf_unary {n b : α → ℕ} (hn : Unary n) (hb : Unary b) : Unary fun x => rOf (n x) (b x) :=
  unary_div (((Unary.const 59).mul ((hn.add hb).add (Unary.const 3))).add (Unary.const 39)) (PolyT.const 40)

/-- i₀ is given in unary if n is. -/
theorem i0Of_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => i0Of (n x) :=
  unary_div (unary_sub (((Unary.const 20).mul hn).add (log_unary hn)) (PolyT.const 1)) (log_polyT hn.poly)

/-- β₁ is given in unary if i₀ is. -/
theorem beta1_unary {m i : α → ℕ} (hm : PolyT m) (hi : Unary i) : Unary fun x => beta1 (m x) (i x) :=
  sup_range_unary_min (n := fun x => i x + 1) (f := fun x j => Nat.clog 2 ((m x).choose j)) (hi.add (Unary.const 1))
    (clog_unary (choose_polyT (PolyT.comp hm PolyT.id'.fst) (unary_min_right PolyT.id'.snd ((hi.add (Unary.const 1)).comp PolyT.id'.fst))))

/-- The first parameter is m. -/
theorem parQ_m (n Δ m : ℕ) : (parQ n Δ m).m = m := by unfold parQ; split_ifs <;> rfl
/-- The second parameter is nb. -/
theorem parQ_nb (n Δ m : ℕ) : (parQ n Δ m).nb = nbOf n Δ := by unfold parQ; split_ifs <;> rfl
/-- The number of checks is 0 if m ≤ nb. -/
theorem parQ_r (n Δ m : ℕ) : (parQ n Δ m).r = if m ≤ nbOf n Δ then 0 else rOf n (beta0 m (nbOf n Δ)) := by unfold parQ; split_ifs <;> rfl
/-- The fourth parameter is i₀. -/
theorem parQ_i₀ (n Δ m : ℕ) : (parQ n Δ m).i₀ = i0Of n := by unfold parQ; split_ifs <;> rfl
/-- The fifth parameter is n + β₀ + β₁ + 2. -/
theorem parQ_β (n Δ m : ℕ) : (parQ n Δ m).β = n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2 := by unfold parQ; split_ifs <;> rfl

/-- The five parameters are given in unary if n, Δ and m are. -/
theorem parQ_QU {n Δ m : α → ℕ} (hn : Unary n) (hΔ : Unary Δ) (hm : Unary m) : QU fun x => parQ (n x) (Δ x) (m x) := by
  have hnb := nbOf_unary hn hΔ.poly
  have hb0 := beta0_unary hm.poly hnb
  have hi0 := i0Of_unary hn
  exact
    { m := unary_congr hm fun x => (parQ_m _ _ _).symm
      nb := unary_congr hnb fun x => (parQ_nb _ _ _).symm
      r := unary_congr (ClauseBound.Alg.CertGridG.unary_ite (PolyT.decide_le hm.poly hnb.poly) (Unary.const 0) (rOf_unary hn hb0)) fun x => (parQ_r _ _ _).symm
      i₀ := unary_congr hi0 fun x => (parQ_i₀ _ _ _).symm
      β := unary_congr (((hn.add hb0).add (beta1_unary hm.poly hi0)).add (Unary.const 2)) fun x => (parQ_β _ _ _).symm }

/-! ### Numbers made from the parameters -/

section
variable {q : α → Par} (hq : QU q)
include hq

/-- The cap for the marks is given in unary. -/
theorem capM_unary : Unary fun x => capM (q x) := (unary_sub hq.β (PolyT.const 1)).add hq.r

end

/-- The bound for the number of checks that contain a clause is given in unary. -/
theorem colMax_unary {n Δ : α → ℕ} (hn : PolyT n) (hΔ : PolyT Δ) : Unary fun x => colMax (n x) (Δ x) :=
  ((clog_unary (((PolyT.const 16).mul hΔ).mul hn)).add ((Unary.const 18).mul (LD_unary hΔ))).add (Unary.const 2)

/-- The bound for the number of clauses of a check is given in unary. -/
theorem rowMax_unary {n Δ : α → ℕ} (hn : PolyT n) (hΔ : Unary Δ) : Unary fun x => rowMax (n x) (Δ x) :=
  ((clog_unary ((PolyT.const 96).mul hn)).add (((Unary.const 3).mul hΔ).mul (LD_unary hΔ.poly))).add (Unary.const 2)

/-- The bound for the number of clauses in which a variable occurs is given in unary. -/
theorem occOL_unary {n Δ : α → ℕ} (hn : PolyT n) (hΔ : Unary Δ) : Unary fun x => occOL (n x) (Δ x) :=
  ClauseBound.Alg.CertGridG.unary_max (hΔ.mul ((Unary.const 2).add (colMax_unary hn hΔ.poly))) (rowMax_unary hn hΔ)

/-- The length of the blocks of the code is given in unary. -/
theorem blkOL_unary {Δ : α → ℕ} (hΔ : Unary Δ) : Unary fun x => blkOL (Δ x) :=
  (((Unary.const 2).mul hΔ).add (((Unary.const 16).mul hΔ).mul (LD_unary hΔ.poly))).add (Unary.const 1)

/-- The number of bits of a position in a block is given in unary. -/
theorem bitOL_unary {Δ : α → ℕ} (hΔ : Unary Δ) : Unary fun x => bitOL (Δ x) := clog_unary (blkOL_unary hΔ).poly

/-- The parameters of the network of marks are polynomial-time. -/
theorem parM_polyT {q : α → Par} (hq : QU q) {n Δ : α → ℕ} (hn : Unary n) (hΔ : Unary Δ) : PolyT fun x => parM (n x) (Δ x) (q x) :=
  PolyT.prodMk (hn.add hq.r) (PolyT.prodMk (capM_unary hq) (PolyT.prodMk (bitOL_unary hΔ) (blkOL_unary hΔ)))

/-- The bound for the shared bits of a network of marks is given in unary if its arguments are. -/
theorem Ub_unary (k : ℕ) {g n w β R : α → ℕ} (hg : Unary g) (hn : Unary n) (hw : Unary w) (hβ : Unary β) (hR : Unary R) :
    Unary fun x => Ub k (g x) (n x) (w x) (β x) (R x) :=
  ((Unary.const 2).mul hR).mul (((((Unary.const (k - 1)).mul hw).mul ((Unary.const 1).add hβ)).add ((Unary.const (k - 1)).mul (hn.add (Unary.const 1)))).add
    (unary_pow_const hg 2))

/-- The bound for the size of a network of marks is given in unary if its arguments are. -/
theorem Pb_unary {g n β Δ : α → ℕ} (hg : Unary g) (hn : Unary n) (hβ : Unary β) (hΔ : Unary Δ) : Unary fun x => Pb (g x) (n x) (β x) (Δ x) :=
  ((((Unary.const 2).mul ((Unary.const 2).add hβ)).mul (Mark.Cert.qv_unary hg hn))).mul (hΔ.add (Unary.const 4))

/-- 3K⁸ is given in unary if K is. -/
theorem g_unary {K : α → ℕ} (hK : Unary K) : Unary fun x => 3 * K x ^ 8 := (Unary.const 3).mul (unary_pow_const hK 8)

/-- The bound for the shared bits of the networks is given in unary. -/
theorem UbOL_unary (k : ℕ) {K n Δ : α → ℕ} (hK : Unary K) (hn : Unary n) (hΔ : Unary Δ) : Unary fun x => UbOL k (K x) (n x) (Δ x) :=
  Ub_unary (k + 1) (g_unary hK) ((Unary.const 7).mul hn) ((Unary.const 11).mul hn) (bitOL_unary hΔ) (Unary.const 3)

/-- The bound for the size of the networks is given in unary. -/
theorem PbOL_unary {K n Δ : α → ℕ} (hK : Unary K) (hn : Unary n) (hΔ : Unary Δ) : Unary fun x => PbOL (K x) (n x) (Δ x) :=
  Pb_unary (g_unary hK) ((Unary.const 7).mul hn) (bitOL_unary hΔ) (occOL_unary hn.poly hΔ)

end ClauseBound.ParityChecks.CertPar
