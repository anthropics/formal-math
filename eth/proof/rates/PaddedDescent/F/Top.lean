/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
import PaddedDescent.F.NSat
import ToTuring.EncLemmas
import SparsifyWidthK.Step
import SparsifyWidthK.SetAlg
import SparsifyWidthK.Thresholds
import SparsifyWidthK.Refine
import SparsifyWidthK.ProgMain

/-! # The top of the function A: the walk of the sparsification tree, and the correctness of A

`walk : StWalk`: if the pad is long enough, `walkF k` says whether some leaf of the sparsification
tree at width k passes the test.
`treeK`: what is needed to know about the sparsification tree of a formula with clauses of 1 to k
literals.
`walk_sat`: for every width k ≥ 1, every n with sOf n ≥ s0K k and every pad of length at least
2^(8·(n / 2^(sOf n) + 1)), the walk whose test is «`countM k` is positive» says whether a
formula on n variables with clauses of 1 to k literals, at most inLen k n of them, is satisfiable.
`correct : StCountM → StLeaf → StSched → StA → StAW → StCorrect (C0K 3) (s0K 3)`: the function `A`,
given the code of an instance φ of 3-SAT on n variables with
sOf n ≥ s0K 3 and the pad of length 2^(C0K 3·(n / 2^(sOf n) + 1)), returns the bit «φ is
satisfiable». The five hypotheses are the statements
of other files: the count for one sparse formula, the form of a leaf, the schedule, and the two
parts of the arithmetic («the pad is long enough»). -/

namespace PaddedDescent.F.Top

open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)

/-- A fold that applies f and then a cut-off cp in every round equals the iterate of f, if the
cut-off leaves all iterates alone. -/
theorem foldl_capped_eq_iterate {γ ι : Type} (cp f : γ → γ) (P : γ → Prop) (hcp : ∀ x, P x → cp x = x) (l : List ι) (a : γ)
    (h : ∀ i ≤ l.length, P (f^[i] a)) : l.foldl (fun st _ => cp (f st)) (cp a) = f^[l.length] a := by
  rw [hcp a (h 0 (Nat.zero_le _))]
  induction l generalizing a with
  | nil => rfl
  | cons e l ih =>
    rw [List.foldl_cons, hcp (f a) (h 1 (by simp)), List.length_cons, Function.iterate_succ_apply]
    exact ih (f a) fun i hi => by
      rw [← Function.iterate_succ_apply]
      exact h (i + 1) (by simpa using hi)

/-- If the pad has at least 2·(number of leaves) − 1 units and every state of the walk fits under
it, `walkF` says whether some leaf passes the test. -/
public theorem walk : StWalk := by
  intro k pad τ test r d hd hlen hst
  unfold walkF
  rw [foldl_capped_eq_iterate (cap pad ([], false)) (roundB (stepK (theta τ) k) test) (fun x => len x ≤ pad.length)
    (fun x hx => cap_eq hx) pad ([r], false) (fun i _ => hst i),
    Sparsify.roundB_iterate_of_le (stepK (theta τ) k) test d r hd pad.length (by omega)]

/-! ### The length of the word of a state of the walk -/

/-- A bound on the length of the word of a list of at most k members, each with a word of length at
most s. -/
public theorem len_list_le {α : Type} [Enc α] {l : List α} {k s : ℕ} (hl : l.length ≤ k) (hs : ∀ x ∈ l, len x ≤ s) :
    len l ≤ k * (s + 2) + 2 := by
  have : ∀ l : List α, (∀ x ∈ l, len x ≤ s) → (l.map fun a => len a + 2).sum ≤ l.length * (s + 2) := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      intro hs
      have h1 := hs x (by simp)
      have h2 := ih fun y hy => hs y (by simp [hy])
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  rw [len_list]
  exact Nat.add_le_add_right ((this l hs).trans (Nat.mul_le_mul_right _ hl)) 2

/-- A bound on the length of the word of a literal with variable below n. -/
theorem len_lit_le {l : ℕ × Bool} {n : ℕ} (h : l.1 < n) : len l ≤ 3 * n + 3 := by
  have : l.1.size ≤ l.1 := Nat.size_le.2 Nat.lt_two_pow_self
  obtain ⟨a, b⟩ := l
  rw [len_pair, len_nat, len_bool]
  simp only at this h
  omega

/-- A bound on the length of the word of a formula of at most m clauses of at most k literals with
variables below n. -/
public theorem len_fml_le {x : Fml} {k m n : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    len x ≤ m * (k * (3 * n + 5) + 10) + 2 := by
  refine len_list_le hm (s := k * (3 * n + 5) + 8) fun C hC => ?_
  have h := len_list_le (hx C hC).1 fun l hl => len_lit_le ((hx C hC).2 l hl)
  have e : 3 * n + 3 + 2 = 3 * n + 5 := rfl
  rw [e] at h
  omega

/-! ### The tree of an instance -/

/-- The sparsification lemma of the imported modules `SparsifyWidthK.Step` to
`SparsifyWidthK.ProgMain`, for the program `stepK`. -/
theorem prog : WidthK.StProg :=
  WidthK.stProg WidthK.stNodeRoot WidthK.stNodeStep WidthK.stNodeBound WidthK.stLeafCard WidthK.stLightEq WidthK.stHeavyEq
    WidthK.stSatIff WidthK.stThr WidthK.stBetaSum WidthK.Refine.stRefines

/-- The sparsification tree of a formula ψ of at most m clauses of 1 to k literals on variables
below n: every node that `leaves` returns at depth bsum τ k · n is a leaf (`stepK` gives `none` on
it); their number; the word of
every state of the walk is short; and if the test is right on every formula of at most (leafC τ k + 2)·n
clauses of 1 to k literals in which every variable occurs at most
leafC τ k + 2 times, then some leaf passes the test iff ψ is satisfiable. -/
public theorem treeK (hLf : StLeaf) {k τ n m : ℕ} (hτ : 1 ≤ τ) (ψ : Fml) (hψl : ψ.length ≤ m)
    (hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (test : PFml → Bool)
    (htest : ∀ x : Fml, x.length ≤ (leafC τ k + 2) * n → WfL k n [x] → (∀ v, (occ x v).length ≤ leafC τ k + 2) →
      (test x = true ↔ Fml.Sat x)) :
    (∀ x ∈ leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ), stepK (theta τ) k x = none) ∧
    (leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ)).length ≤ ∑ j ∈ range (k * n / τ + 1), (bsum τ k * n).choose j ∧
    (∀ i, len ((roundB (stepK (theta τ) k) test)^[i] ([rootP ψ], false)) ≤ stackLen k τ n m) ∧
    ((leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ)).any test = true ↔ Fml.Sat ψ) := by
  obtain ⟨t1, t2, t3, t4⟩ := prog τ k n hτ ψ hψne
  obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ) := ⟨_, rfl⟩
  rw [← hL] at t1 t2 t3 ⊢
  have hleaf : ∀ x ∈ L, (test x = true ↔ Fml.Sat x) := fun x hx => by
    obtain ⟨l1, l2⟩ := hLf k τ n ψ hτ hψne x (hL ▸ hx)
    refine htest x ((t2 x hx).2.1.trans (Nat.mul_le_mul_right n (by omega))) ?_ fun v => (l2 v).trans (by omega)
    intro y hy C hC
    rw [List.mem_singleton.1 hy] at hC
    exact ⟨l1 C hC, (t2 x hx).2.2 C hC⟩
  refine ⟨fun x hx => (t2 x hx).1, t1, fun i => ?_, ?_⟩
  · obtain ⟨s1, s2⟩ := t4 i
    have e := Sparsify.roundB_iterate (stepK (theta τ) k) test i [rootP ψ] []
    rw [List.any_nil] at e
    rw [e, len_pair, len_bool, stackLen]
    have hf : ∀ x ∈ ((round (stepK (theta τ) k))^[i] ([rootP ψ], [])).1, len x ≤ 2 ^ k * m * (k * (3 * n + 5) + 10) + 2 := fun x hx =>
      len_fml_le ((s2 x hx).1.trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hψl)) (s2 x hx).2
    have h := len_list_le s1 hf
    have e4 : 2 ^ k * m * (k * (3 * n + 5) + 10) + 2 + 2 = 2 ^ k * m * (k * (3 * n + 5) + 10) + 4 := rfl
    rw [e4] at h
    omega
  · simp only [List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hx'⟩
      obtain ⟨a, ha⟩ := (hleaf x hx).1 hx'
      exact ⟨a, (t3 fun l => a l.1 = l.2).2 ⟨x, hx, ha⟩⟩
    · rintro ⟨a, ha⟩
      obtain ⟨x, hx, h⟩ := (t3 fun l => a l.1 = l.2).1 ha
      exact ⟨x, hx, (hleaf x hx).2 ⟨a, h⟩⟩

/-- The threshold is positive. -/
theorem one_le_tauOf (s : ℕ) : 1 ≤ tauOf s := Nat.one_le_two_pow

/-- The four parameters of the evaluations, as numbers. -/
theorem length_markPar (n s : ℕ) : (markPar n s).1.length = n ∧ (markPar n s).2.1.length = n + 2 ∧ (markPar n s).2.2.1.length = betaOf s ∧
    (markPar n s).2.2.2.length = 2 ^ betaOf s := by
  simp only [markPar, List.length_replicate, capOf, and_self]

/-- The walk whose test is «the count is positive» decides satisfiability: width k ≥ 1, n variables
with sOf n ≥ s0K k, at most inLen k n clauses of 1 to k literals, and a pad of
length at least 2^(8·(n / 2^(sOf n) + 1)). -/
public theorem walk_sat (hCount : StCountM) (hLf : StLeaf) (hSched : StSched) (hA : StA) (hAW : StAW) {k n : ℕ} (hk : 1 ≤ k) (hs : s0K k ≤ sOf n)
    (pad : U) (hF : 2 ^ (8 * (n / 2 ^ sOf n + 1)) ≤ pad.length) (ψ : Fml) (hψl : ψ.length ≤ inLen k n)
    (hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    walkF k pad (tauOf (sOf n))
      (fun x => decide (0 < countM k pad ((schedF pad (depthOf (sOf n))).1, (schedF pad (depthOf (sOf n))).2.1) (markPar n (sOf n)) (layersOf (sOf n)) x))
      (rootP ψ) = true ↔ Fml.Sat ψ := by
  obtain ⟨w1, w2, w3, w4⟩ := hAW k n pad.length hk hs hF
  obtain ⟨a1, a2⟩ := hA k n pad.length (leafC (tauOf (sOf n)) k + 2) (by omega) hF w1 w2
  rw [hSched pad _ a2]
  obtain ⟨p1, p2, p3, p4⟩ := length_markPar n (sOf n)
  obtain ⟨b1, b2, b3, b4⟩ := treeK hLf (one_le_tauOf (sOf n)) ψ hψl hψne
    (fun x => decide (0 < countM k pad (schedL (depthOf (sOf n)), List.replicate (Kseq (depthOf (sOf n))) ()) (markPar n (sOf n))
      (layersOf (sOf n)) x))
    (fun x hx hW ho => by
      rw [decide_eq_true_eq, hCount k pad _ (markPar n (sOf n)) _ _ _ x (by rw [p1, p3, p4]; exact a1) (by rw [p1, p2]) (by rw [p1]; exact hW) ho hx,
        p1]
      exact Mark.NSat.cast_nSat_pos_iff fun C hC => (hW x (by simp) C hC).2.2)
  rw [walk k pad _ _ _ _ b1 (by omega) fun i => (b3 i).trans w4]
  exact b4

/-- The bound for the length of a code at width 3. -/
theorem inLen_three (n : ℕ) : inLen 3 n = 25 * (n + 2) ^ 4 := by
  unfold inLen; norm_num

/-- The function `A` is correct on every instance with sOf n ≥ s0K 3, given the pad of length 2^(C0K
3·(n / 2^(sOf n) + 1)). -/
public theorem correct (hCount : StCountM) (hLf : StLeaf) (hSched : StSched) (hA : StA) (hAW : StAW) : StCorrect (C0K 3) (s0K 3) := by
  intro n φ h3 hs
  obtain ⟨C₀, hC₀, hC8⟩ : ∃ C₀, C₀ = C0K 3 ∧ 8 ≤ C₀ := ⟨_, rfl, Nat.le_mul_of_pos_right 8 (Nat.two_pow_pos _)⟩
  rw [← hC₀]
  obtain ⟨pad, hpad⟩ : ∃ pad : U, pad = List.replicate (2 ^ (C₀ * (n / 2 ^ sOf n + 1))) () := ⟨_, rfl⟩
  rw [← hpad]
  have hF : 2 ^ (8 * (n / 2 ^ sOf n + 1)) ≤ pad.length := by
    rw [hpad, List.length_replicate]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hC8)
  have hdec : Decode.dec (Sat3.enc φ) = (n, Decode.toN φ) := Decode.dec_enc h3.1
  have hnilψ : hasNil (Decode.toN φ) = true ↔ [] ∈ φ := by
    rw [← Decode.nil_mem_toN]
    simp [hasNil, List.any_eq_true]
  simp only [A, decF, hdec]
  by_cases hnil : [] ∈ φ
  · rw [hnilψ.2 hnil]
    simp only [cond_true, Bool.false_eq_true, false_iff]
    rintro ⟨a, ha⟩
    obtain ⟨l, hl, -⟩ := ha [] hnil
    simp at hl
  · have hn' : hasNil (Decode.toN φ) = false := by
      rw [← Bool.not_eq_true]; exact fun h => hnil (hnilψ.1 h)
    have hm : (Decode.toN φ).length ≤ inLen 3 n := by
      have h := Decode.length_enc φ
      have h' := Decode.length_enc_succ_le h3
      have hB : 0 < 3 * (Nat.log2 (2 * n) + 1) := by omega
      have := Nat.le_mul_of_pos_right φ.length hB
      rw [Decode.length_toN, inLen_three]
      omega
    have hψne : ∀ C ∈ Decode.toN φ, C ≠ [] ∧ C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n := by
      intro D hD
      obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN hD
      refine ⟨?_, hl ▸ h3.1 C hC, h⟩
      rintro rfl
      exact hnil ((Decode.nil_mem_toN φ).1 hD)
    rw [hn', cond_false, walk_sat hCount hLf hSched hA hAW (by norm_num) hs pad hF _ hm hψne]
    exact Decode.satN_toN φ

end PaddedDescent.F.Top
