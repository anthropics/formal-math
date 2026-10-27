/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Mach.Walk
import SparsificationLemma.Side
import UniformInK.Tree.Tree
import UniformInK.Spars.Main
import UniformInK.Top.Leaves
import UniformInK.Top.Budget
import ClauseBound.Alg.Decode
import ClauseBound.Alg.End
import PaddedDescent.F.Top
import all CountKSatRate.Leaf
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! # The function of (input, pad) writes the outputs

`BL_eq`: on the input 1^s 0 1^k 0 code(φ), with k ≥ 1, s ≥ `s0U k` and φ a k-CNF without an empty
clause, and with the pad of 2^(eL …) units, `BL` is the code of the list of outputs for τ =
2^(4s+17).
The steps:
* `len_node_le`, `len_state_le`: a node that is ever on the stack has a word of length at most
  `nodeLen k n m`, m the number of clauses of φ (`UniformInK.StTreeU` bounds these nodes), and the
  stack and the list of results together never hold more nodes than the tree has leaves
  (`total_le_leaves`, proof/sparsification/SparsificationLemma/Mach/Walk.lean). So if L bounds the
  number of leaves, the word of a state has length at most L·(nodeLen k n m + 2) + 6.
* `map_walkL`: under a pad of this length the walk returns the leaves of the tree whose side list
  starts with the clauses xᵢ ∨ ¬xᵢ; their outputs are those of the tree that starts with the empty
  side list (`StOutputsSame`).
* `pad_enough`: 2^(eL …) units suffice for L = 2^(⌊n/2^s⌋+1), which bounds the number of leaves by
  `UniformInK.StLeavesU`, because k, n and m are at most the length of the input.
* `codeP_eq`: the variables of the outputs are below n, so the cut-off in the code does nothing. -/

public section

namespace SparsificationLemma.Mach

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg SparsificationLemma.Geo

/-! ### The length of the word of a state -/

/-- The word of a node with the bounds of `UniformInK.StTreeU` has length at most `nodeLen k n m`. -/
theorem len_node_le {k n m : ℕ} {x : CNode} (a1 : x.1.length ≤ m * 2 ^ k) (a2 : x.2.length ≤ 2 * n) (a3 : ∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n)
    (a4 : ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) : len x ≤ nodeLen k n m := by
  have b1 := Top.len_fml_le (m := 2 ^ k * m) (x := x.1) (by rw [Nat.mul_comm]; exact a1) a3
  have b2 := Top.len_fml_le (m := 2 * n) (x := x.2) a2 a4
  obtain ⟨s, X⟩ := x
  rw [len_pair]
  simp only at b1 b2
  unfold nodeLen
  omega

/-- The word of a state with at most L nodes, each with a word of length at most b, has length at
most L·(b + 2) + 6. -/
theorem len_state_le {st : List CNode × List CNode} {L b : ℕ} (h : st.1.length + st.2.length ≤ L) (h1 : ∀ x ∈ st.1, len x ≤ b) (h2 : ∀ x ∈ st.2, len x ≤ b) :
    len st ≤ L * (b + 2) + 6 := by
  have a1 := Top.len_list_le (le_refl st.1.length) h1
  have a2 := Top.len_list_le (le_refl st.2.length) h2
  have a3 : (st.1.length + st.2.length) * (b + 2) ≤ L * (b + 2) := Nat.mul_le_mul_right _ h
  rw [Nat.add_mul] at a3
  obtain ⟨a, c⟩ := st
  rw [len_pair]
  simp only at a1 a2 a3
  omega

/-! ### The walk returns the outputs -/

/-- For k ≥ 1, τ ≥ k², τ ≥ 8k and a k-CNF ψ on n variables: if L is at least Σ_{j ≤ kn/τ} C(bsumU τ
k · n, j), which bounds the number of leaves, and the pad has at least 2L − 1 units and at least
L·(nodeLen k n m + 2) + 6 units, m the number of clauses of ψ, then the walk returns nodes whose
outputs are `outTau k n τ ψ`, and every variable of the outputs is below n. -/
theorem map_walkL {k τ n L : ℕ} {ψ : PFml} {pad : U} (hk : 1 ≤ k) (h2 : k ^ 2 ≤ τ) (h8 : 8 * k ≤ τ) (hψ : IsKCNF k n ψ)
    (hL : ∑ j ∈ Finset.range (k * n / τ + 1), (bsumU τ k * n).choose j ≤ L) (hp1 : 2 * L ≤ pad.length + 1) (hp2 : L * (nodeLen k n ψ.length + 2) + 6 ≤ pad.length) :
    (walkL k pad τ (rootC (List.replicate n (), ψ))).map out = outTau k n τ ψ ∧ ∀ Φ ∈ outTau k n τ ψ, ∀ C ∈ Φ, ∀ l ∈ C, l.1 < n := by
  obtain ⟨t1, t2, -, t4⟩ := stTreeU stIfaceU k τ n hk h2 h8 ψ hψ
  have hO : (leaves (stepC (thetaU τ) k) (bsumU τ k * n) (rootC (List.replicate n (), ψ))).map out = outTau k n τ ψ := stOutputsSame (thetaU τ) k (bsumU τ k * n) n ψ
  obtain ⟨r, hr⟩ : ∃ r, r = rootC (List.replicate n (), ψ) := ⟨_, rfl⟩
  rw [← hr] at t1 t2 t4 hO ⊢
  have hd : ∀ x ∈ leaves (stepC (thetaU τ) k) (bsumU τ k * n) r, stepC (thetaU τ) k x = none := fun x hx => (t2 x hx).1
  have hnode : ∀ i, ∀ x ∈ ((round (stepC (thetaU τ) k))^[i] ([r], [])).1, len x ≤ nodeLen k n ψ.length := fun i x hx =>
    let ⟨a1, a2, a3, a4⟩ := (t4 i).2 x hx
    len_node_le a1 a2 a3 a4
  have hst : ∀ i, len ((round (stepC (thetaU τ) k))^[i] ([r], [])) ≤ pad.length := fun i =>
    (len_state_le ((total_le_leaves _ _ r hd i).trans (t1.trans hL)) (hnode i) (out_of_stack _ (fun x => len x ≤ nodeLen k n ψ.length) r hnode i)).trans hp2
  refine ⟨?_, ?_⟩
  · rw [walkL_eq k pad τ r _ hd (by have := t1.trans hL; omega) hst, hO]
  · rw [← hO]
    intro Φ hΦ C hC
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hΦ
    obtain ⟨-, -, b3, -, b5⟩ := t2 x hx
    rcases List.mem_append.1 (List.mem_dedup.1 hC) with hC | hC
    · exact (b5 C (Leaf.mem_sideU.1 hC).1).2
    · exact (b3 C hC).2.2

/-! ### The code -/

/-- The cut-off does nothing to a number that is at most the length of the pad. -/
theorem codeNatP_eq {pad : U} {v : ℕ} (h : v ≤ pad.length) : codeNatP pad v = codeNat v := by
  have e : (pad.take v).map (fun _ => true) = List.replicate v true := List.eq_replicate_iff.2 ⟨by simp [h], by simp⟩
  rw [codeNatP, codeNat, e]

/-- The cut-off does nothing to a list of formulas whose variables are at most the length of the
pad. -/
theorem codeP_eq {pad : U} {L : List PFml} (h : ∀ Φ ∈ L, ∀ C ∈ Φ, ∀ l ∈ C, l.1 ≤ pad.length) : codeP pad L = code L := by
  unfold codeP code
  congr 1
  refine List.flatMap_congr fun Φ hΦ => ?_
  unfold codeFmlP codeFml
  congr 2
  refine List.flatMap_congr fun C hC => ?_
  unfold codeClP codeCl
  congr 2
  refine List.flatMap_congr fun l hl => ?_
  rw [codeLitP, codeLit, codeNatP_eq (h Φ hΦ C hC l hl)]

/-! ### Reading the input -/

/-- From 1^s 0 1^k 0 code(φ) the function reads s, k, n and φ. -/
theorem dec_encIn (s k n : ℕ) (φ : Sat3.CNF n) (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) :
    sL (encIn s k φ) = s ∧ kL (encIn s k φ) = k ∧ dL (encIn s k φ) = (List.replicate n (), Decode.toN φ) := by
  obtain ⟨h1, h2⟩ := ClauseBound.Alg.Decode.stDecM k n φ hk hφ
  refine ⟨?_, ?_, ?_⟩
  · rw [sL, encIn, ClauseBound.Alg.Decode.kOf_ones, List.length_replicate]
  · rw [kL, encIn, ClauseBound.Alg.Decode.restOf_ones, h1, List.length_replicate]
  · rw [dL, encIn, ClauseBound.Alg.Decode.restOf_ones, h2]

/-- The input has s + k + n + 3 + m·k·(⌊log₂ 2n⌋ + 1) symbols, m the number of clauses of φ. -/
theorem length_encIn (s k : ℕ) {n : ℕ} (φ : Sat3.CNF n) : (encIn s k φ).length = s + k + n + 3 + φ.length * (k * (Nat.log2 (2 * n) + 1)) := by
  rw [encIn, List.length_append, List.length_cons, List.length_replicate, End.length_enc]
  omega

/-- The exponent of the pad on the input 1^s 0 1^k 0 code(φ). -/
theorem eL_encIn (s k n : ℕ) (φ : Sat3.CNF n) (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) :
    eL (encIn s k φ) = n / 2 ^ s + k + 3 * Nat.size (encIn s k φ).length + 9 := by
  obtain ⟨d1, d2, d3⟩ := dec_encIn s k n φ hk hφ
  rw [eL, d1, d2, d3, List.length_replicate]

/-- A k-CNF without an empty clause, read with natural numbers as variables, is a k-CNF on n
variables. -/
theorem isKCNF_toN {k n : ℕ} {φ : Sat3.CNF n} (hφ : ∀ C ∈ φ, C.length ≤ k) (hnil : [] ∉ φ) : IsKCNF k n (Decode.toN φ) := by
  intro D hD
  obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN hD
  refine ⟨?_, hl ▸ hφ C hC, h⟩
  rintro rfl
  exact hnil ((Decode.nil_mem_toN φ).1 hD)

/-! ### The pad is long enough -/

/-- 2^(a + k + 3·size N + 9) units suffice for 2^(a+1) nodes, if k, n and m are at most N. -/
theorem pad_enough (a : ℕ) {k n m N : ℕ} (hk : k ≤ N) (hn : n ≤ N) (hm : m ≤ N) :
    2 ^ (a + 1) * (nodeLen k n m + 2) + 6 ≤ 2 ^ (a + k + 3 * Nat.size N + 9) := by
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 2 ^ Nat.size N := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 2 ^ k := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ a := ⟨_, rfl⟩
  have hNZ : N < Z := hZ ▸ Nat.lt_size_self N
  have hK1 : 1 ≤ K := hK ▸ Nat.one_le_two_pow
  have hA1 : 1 ≤ A := hA ▸ Nat.one_le_two_pow
  have hZ1 : 1 ≤ Z := by omega
  have e0 : 2 ^ (a + k + 3 * Nat.size N + 9) = A * K * Z ^ 3 * 512 := by
    rw [pow_add, pow_add, pow_add, Nat.mul_comm 3, pow_mul, ← hZ, ← hK, ← hA]
    norm_num
  have e1 : 2 ^ (a + 1) = 2 * A := by rw [pow_succ, ← hA, Nat.mul_comm]
  have b1 : Z ≤ Z ^ 3 := Nat.le_self_pow (by norm_num) Z
  have b2 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have b3 : 1 ≤ Z ^ 3 := Nat.one_le_pow _ _ hZ1
  have c1 : m * (k * (3 * n + 5) + 10) ≤ Z * (Z * (3 * Z + 5) + 10) := by gcongr <;> omega
  have c2 : 2 * n * (2 * (3 * n + 5) + 10) ≤ 2 * Z * (2 * (3 * Z + 5) + 10) := by gcongr <;> omega
  have e2 : Z * (Z * (3 * Z + 5) + 10) = 3 * Z ^ 3 + 5 * Z ^ 2 + 10 * Z := by ring
  have e3 : 2 * Z * (2 * (3 * Z + 5) + 10) = 12 * Z ^ 2 + 40 * Z := by ring
  have c3 : K * (m * (k * (3 * n + 5) + 10)) ≤ K * (18 * Z ^ 3) := Nat.mul_le_mul_left _ (by omega)
  have c4 : 60 * Z ^ 3 ≤ K * (60 * Z ^ 3) := Nat.le_mul_of_pos_left _ hK1
  have c5 : nodeLen k n m + 2 ≤ K * (78 * Z ^ 3) := by
    have e4 : K * (78 * Z ^ 3) = K * (18 * Z ^ 3) + K * (60 * Z ^ 3) := by ring
    rw [nodeLen, ← hK, Nat.mul_assoc K, e4]
    omega
  have c6 : 1 ≤ A * K * Z ^ 3 := Nat.mul_pos (Nat.mul_pos hA1 hK1) b3
  calc 2 ^ (a + 1) * (nodeLen k n m + 2) + 6 ≤ 2 * A * (K * (78 * Z ^ 3)) + 6 := by rw [e1]; gcongr
    _ = 156 * (A * K * Z ^ 3) + 6 := by ring
    _ ≤ A * K * Z ^ 3 * 512 := by omega
    _ = _ := e0.symm

/-! ### The function writes the outputs -/

/-- On 1^s 0 1^k 0 code(φ), for k ≥ 1, s ≥ `s0U k` and φ a k-CNF without an empty clause, and with
the pad of 2^(eL …) units, `BL` is the code of the list of outputs for τ = 2^(4s+17). -/
theorem BL_eq (k n s : ℕ) (φ : Sat3.CNF n) (hk : 1 ≤ k) (hs : s0U k ≤ s) (hφ : SatK.IsKCNF k φ) (hnil : [] ∉ φ) :
    BL (encIn s k φ, PaddedDescent.pad (eL (encIn s k φ))) = code (outTau k n (tauOf s) (Decode.toN φ)) := by
  obtain ⟨d1, d2, d3⟩ := dec_encIn s k n φ hk hφ.1
  have he := eL_encIn s k n φ hk hφ.1
  have hN := length_encIn s k φ
  obtain ⟨N, hNdef⟩ : ∃ N, N = (encIn s k φ).length := ⟨_, rfl⟩
  rw [← hNdef] at he hN
  have hm : φ.length ≤ φ.length * (k * (Nat.log2 (2 * n) + 1)) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hk (Nat.succ_pos _))
  obtain ⟨hτ1, hτ2⟩ := (stParU k s hk).2 hs
  obtain ⟨e, hedef⟩ : ∃ e, e = eL (encIn s k φ) := ⟨_, rfl⟩
  rw [← hedef] at he ⊢
  have hlen : (PaddedDescent.pad e).length = 2 ^ e := List.length_replicate
  have hp2 := pad_enough (n / 2 ^ s) (k := k) (n := n) (m := (Decode.toN φ).length) (N := N) (by omega) (by omega) (by rw [Decode.length_toN]; omega)
  rw [← he, ← hlen] at hp2
  have hp1 : 2 * 2 ^ (n / 2 ^ s + 1) ≤ (PaddedDescent.pad e).length + 1 := by
    have : 2 ^ (n / 2 ^ s + 1) * 2 ≤ 2 ^ (n / 2 ^ s + 1) * (nodeLen k n (Decode.toN φ).length + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨w1, w2⟩ := map_walkL hk hτ1 hτ2 (isKCNF_toN hφ.1 hnil) (stLeavesU k n s hk hs) hp1 hp2
  have hke : k ≤ e ∧ Nat.size N ≤ e := by
    generalize n / 2 ^ s = a at he
    omega
  have hmin : min k (Nat.log 2 (PaddedDescent.pad e).length) = k := by
    rw [hlen, Nat.log_pow (by norm_num)]
    exact min_eq_left hke.1
  have hn : n ≤ (PaddedDescent.pad e).length := by
    have h1 : N < 2 ^ Nat.size N := Nat.lt_size_self N
    have h2 : 2 ^ Nat.size N ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hke.2
    omega
  simp only [BL, d1, d2, d3, hmin]
  rw [w1, codeP_eq fun Φ hΦ C hC l hl => ((w2 Φ hΦ C hC l hl).le).trans hn]

end SparsificationLemma.Mach
