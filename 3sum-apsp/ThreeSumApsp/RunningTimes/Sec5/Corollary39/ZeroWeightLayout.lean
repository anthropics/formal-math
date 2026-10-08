/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.TopProcedure
public import ThreeSumApsp.Programs.Sec5.Corollary39.ZeroWeight.Host

/-!
# Zero-Weight k-Clique: from a solver of the task to a program for the layout of the end statement

Zero-Weight k-Clique (Corollary 39).  `realized_zeroKClique`: if the task `kcTask k` is
solved in time T, then `EndStatement.ZeroWeightKClique k` is solved on the word RAM within a
constant times T.

The input is n in cell 0 and then, for each ordered pair of parts (p, q), an n × n block of numbers;
the weight between vertex u of part p and vertex v of part q stands in cell
1 + ((p k + q) n + u) n + v (`getD_kList`).  Only the blocks with p < q count.  The solver is told
the graph of these blocks (`upperGraph`), whose cliques have the weights that the end statement sums
(`cliqueWeight_upperGraph`, `hasZeroClique_upperGraph`), and it reads no other block
(`kcPre_input`).  The free pointer is 1 + k² n².
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec ThreeSumApsp.KClique Light.Sec3

section Input

variable {k n : ℕ}

/-! ## The list of the weights -/

/-- The weights, as the input has them. -/
def kList (w : Fin k → Fin k → Fin n → Fin n → ℤ) : List ℤ :=
  (List.ofFn fun i => (List.ofFn fun j => EndStatement.rowByRow (w i j)).flatten).flatten

/-- The list of the weights, block after block. -/
theorem kList_eq (w : Fin k → Fin k → Fin n → Fin n → ℤ) :
    kList w =
      (List.finRange k).flatMap fun p => (List.finRange k).flatMap fun q => rowMajor (w p q) := by
  simp only [kList, rowByRow_eq, List.ofFn_eq_map, List.flatMap_def]

/-- There are `k² n²` weights. -/
theorem length_kList (w : Fin k → Fin k → Fin n → Fin n → ℤ) :
    (kList w).length = k * k * n * n := by
  rw [kList_eq, List.length_flatMap_finRange _ fun p =>
    List.length_flatMap_finRange _ fun q => length_rowMajor (w p q)]
  ring

/-- At size 0 there are no weights. -/
theorem kList_zero (w : Fin k → Fin k → Fin 0 → Fin 0 → ℤ) : kList w = [] :=
  List.eq_nil_of_length_eq_zero ((length_kList w).trans (Nat.mul_zero _))

/-- The entry at the place of a weight is the weight. -/
theorem getD_kList (w : Fin k → Fin k → Fin n → Fin n → ℤ) (p q : Fin k) (u v : Fin n) :
    (kList w).getD (widx k n p u q v) 0 = w p q u v := by
  have hblock : ∀ p q : Fin k, (rowMajor (w p q)).length = n * n := fun p q => length_rowMajor _
  have hblocks : ∀ p : Fin k,
      ((List.finRange k).flatMap fun q => rowMajor (w p q)).length = k * (n * n) :=
    fun p => List.length_flatMap_finRange _ (hblock p)
  have huv : (u : ℕ) * n + v < n * n := Nat.mul_add_lt_mul u.2 v.2
  have hq : (q : ℕ) * (n * n) + ((u : ℕ) * n + v) < k * (n * n) := Nat.mul_add_lt_mul q.2 huv
  have hidx : widx k n p u q v =
      (p : ℕ) * (k * (n * n)) + ((q : ℕ) * (n * n) + ((u : ℕ) * n + v)) := by
    unfold widx
    ring
  rw [kList_eq, hidx, List.getD_flatMap_finRange _ hblocks p hq,
    List.getD_flatMap_finRange _ (hblock p) q huv, getD_rowMajor]

/-- Every weight is one of the numbers of the input. -/
theorem mem_kList (w : Fin k → Fin k → Fin n → Fin n → ℤ) (p q : Fin k) (u v : Fin n) :
    w p q u v ∈ kList w := by
  rw [kList_eq]
  exact List.mem_flatMap.2 ⟨p, List.mem_finRange p,
    List.mem_flatMap.2 ⟨q, List.mem_finRange q, mem_rowMajor_self (w p q) u v⟩⟩

/-! ## The graph of the upper blocks -/

/-- The complete `k`-partite graph whose weights between the parts `p < q` are the block
`(p, q)`. -/
def upperGraph (w : Fin k → Fin k → Fin n → Fin n → ℤ) : KPartiteGraph k n where
  w p u q v := if p < q then w p q u v else if q < p then w q p v u else 0
  symm p u q v := by
    rcases lt_trichotomy p q with h | rfl | h
    · simp only [if_pos h, if_neg (not_lt_of_gt h)]
    · simp only [lt_irrefl, if_false]
    · simp only [if_pos h, if_neg (not_lt_of_gt h)]

/-- A clique of the graph has the weight that the upper blocks give it. -/
theorem cliqueWeight_upperGraph (w : Fin k → Fin k → Fin n → Fin n → ℤ) (c : Fin k → Fin n) :
    (upperGraph w).cliqueWeight c = cliqueWeight w c :=
  Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ hq => if_pos (Finset.mem_filter.1 hq).2

/-- Some clique of the graph has weight 0 exactly if the question of the end statement has the
answer yes. -/
theorem hasZeroClique_upperGraph (w : Fin k → Fin k → Fin n → Fin n → ℤ) :
    (upperGraph w).HasZeroClique ↔ (EndStatement.ZeroWeightKClique k).yes w := by
  refine exists_congr fun c => ?_
  rw [cliqueWeight_upperGraph, List.sum_ofFn, cliqueWeight]
  simp only [List.sum_ofFn]
  rw [Finset.sum_comm]
  exact Eq.congr_left (Finset.sum_congr rfl fun p _ => Finset.sum_filter _ _)

/-- What a solver of a weighted `k`-Clique problem asks of the memory holds for the input, with the
weights from cell 1 on. -/
theorem kcPre_input (w : Fin k → Fin k → Fin n → Fin n → ℤ) {U : ℕ}
    (hw : ∀ a ∈ kList w, a.natAbs ≤ U) (hn : 1 ≤ n) (hU : 1 ≤ U) {fr : ℕ}
    (hfr : 1 + k * k * n * n ≤ fr) :
    KcInst.Pre (k := k) ⟨n, U, 1, upperGraph w⟩ (memOf ((n : ℤ) :: kList w)) fr where
  n_pos := hn
  U_pos := hU
  weights p q u v hpq := by
    have hcell : memOf ((n : ℤ) :: kList w) (1 + widx k n p u q v) =
        (kList w).getD (widx k n p u q v) 0 := by
      unfold memOf
      rw [Nat.add_comm 1]
      rfl
    exact hcell.trans ((getD_kList w p q u v).trans (if_pos hpq).symm)
  le p q u v hpq := by
    rw [show (upperGraph w).w p u q v = w p q u v from if_pos hpq, Int.abs_eq_natAbs]
    exact_mod_cast hw _ (mem_kList w p q u v)
  below := hfr

end Input

/-! ## The connection -/

/-- The arguments of the solver: n, U, the address 1 of the weights, and the free pointer
1 + k² n². -/
def cliqueArgs (kk : ℕ) : List Expr := [v 1, v 2, k 1, k 1 +' k (kk * kk) *' v 3]

/-- The arguments stay within the limits. -/
theorem safe_cliqueArgs (kk n : ℕ) {lim : Limits} {σ : State} (hnn : σ.loc 3 = ((n * n : ℕ) : ℤ))
    (hw : (((kk * kk + 1) * (n * n + 1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ e ∈ cliqueArgs kk, e.Safe lim σ := by
  rw [show (kk * kk + 1) * (n * n + 1) = kk * kk * (n * n) + kk * kk + n * n + 1 by ring] at hw
  push_cast at hw hnn
  have : (0 : ℤ) ≤ (kk : ℤ) * kk * ((n : ℤ) * n) := by positivity
  have : (0 : ℤ) ≤ (kk : ℤ) * kk := by positivity
  have : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  simp [cliqueArgs, hnn, abs_le]
  omega

/-- What connects Zero-Weight k-Clique in the layout of the end statement with the task. -/
noncomputable def wrapClique (kk : ℕ) (hk : 1 ≤ kk) :
    Wrap (EndStatement.ZeroWeightKClique kk) (kcTask kk) true where
  cst := kk * kk + 1
  cst_pos := by omega
  args := cliqueArgs kk
  inst x := ⟨x.n, x.U, 1, upperGraph x.x⟩
  fr x := 1 + kk * kk * x.n * x.n
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by
    rw [show (kk * kk + 1) * (x.n * x.n + 1) = kk * kk * x.n * x.n + kk * kk + x.n * x.n + 1 by
      ring]
    omega
  vals x σ hn hU hnn := by
    simp only [cliqueArgs, List.map_cons, List.map_nil, Expr.val, Op.eval, hn, hU, hnn, kcTask]
    simp
    ring
  safe x lim σ _ _ hnn hw := safe_cliqueArgs kk x.n hnn hw
  zero x hn _ :=
    ⟨⟨fun h => absurd h (by simp), fun ⟨c, _⟩ => absurd (c ⟨0, hk⟩).isLt (by omega)⟩, trivial⟩
  pre x hn hU := kcPre_input x.x x.bounded hn hU le_rfl
  post x r μ' _ h := by
    obtain ⟨rfl, -⟩ := h
    exact ⟨(verdictOf_flag _).trans (hasZeroClique_upperGraph x.x), trivial⟩

/-- **Zero-Weight k-Clique**: if the task is solved in time T, then the problem is solved on the
word RAM within a constant times T. -/
theorem realized_zeroKClique (kk : ℕ) (hk : 1 ≤ kk) (T : ℕ → ℝ → ℝ)
    (h : SolvedIn (kcTask kk) T) : Realized (EndStatement.ZeroWeightKClique kk) T :=
  (wrapClique kk hk).realized h

end Light.Sec5
