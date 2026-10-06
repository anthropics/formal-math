/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma7_8

/-!
# Sections 2.4.1 and 2.4.2: the encodings, the recursion `Pruned`, and Lemma 10

The encoding of an array is computed by `Full` with the other array left out (`computeEncoding_phi`,
`computeEncoding_psi`).  `Pruned(S)` is `Full` without that phase, and each call computes only the
outputs in the set `S` that is passed to it.  Lemma 10 (`lemma_10`) has three claims.

* Values.  One induction gives a closed form (`Pruned_eq_restrictTo_sum`): at a string of `S`,
  `Pruned` returns the sum, over the leaves contributing to the string, of the product of the two
  numbers looked up at the leaf.  With the encodings of `a` and `b` this sum is `Mult(a, b)` by
  definition (`Lemma10.values`), which is what `Full` returns by Lemma 7
  (`Pruned_eq_restrictTo_Full`).  The paper compares `Pruned` with `Full` level by level instead.
* Leaves visited.  A vertex below the root is called exactly if it contributes to a string of `U`
  (`Pruned.called_iff_root_or`, `Pruned.called_iff`; the step of the induction is
  `Pruned.called_succ`).  For leaves this is `Lemma10.leaves_visited`.  The set passed to a vertex
  consists of the suffixes of these strings (`Pruned.mem_passed_iff`; no later proof uses this).
* Total size.  A set of strings is no larger than its set of leaves, because a string is determined
  by its private leaf (`card_le_card_Leaves`), and the leaves of `Leaves(S)` that begin with
  `λ` are the leaves of `Leaves(S_λ)` with `λ` put in front (`card_Leaves_succ`).  So the
  sets passed at one depth have total size at most `|Leaves(U)|` (`Pruned.sum_card_passed_le`), and
  there are `L + 1` depths (`Lemma10.total_size`).

Which calls `Pruned` makes depends only on the set passed to it, so the second and the third claim
are proved for any two arrays in place of the two encodings.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Section 2.4.1: the encodings -/

/-- Section 2.4.1, the procedure that computes the encoding of `a`: "we run Full with b left out and
without step (4): […] the left number at the leaf τ is Φ_τ(a), and the leaf stores it." What is left
of `Full` is step (2) for `a`, the recursive calls of step (3), and at depth `L` the number that has
been reached. "The encoding of b […] is computed in the same way", so the procedure is written once,
for the coefficients `c` of any family of linear forms: `c = φ` for `a`, and `c = ψ` for `b`. -/
def computeEncoding {α : Type} [Fintype α] (c : Term → α → ℤ) :
    (L : ℕ) → ((Fin L → α) → ℤ) → Leaf L → ℤ
  | 0, a, _ => a Fin.elim0
  | L + 1, a, τ => computeEncoding c L (fun u' => ∑ s, c (τ 0) s * sliceAt a s u') (Fin.tail τ)

/-- At the leaf `τ` the procedure of Section 2.4.1 stores `∑_u a[u] ∏_ℓ c_{τ_ℓ}(u_ℓ)`. -/
theorem computeEncoding_eq_encodeWith {α : Type} [Fintype α] (c : Term → α → ℤ) {L : ℕ}
    (a : (Fin L → α) → ℤ) (τ : Leaf L) : computeEncoding c L a τ = encodeWith c τ a := by
  induction L with
  | zero => rw [computeEncoding, encodeWith_zero]
  | succ n ih => rw [computeEncoding, ih, ← encodeWith_cons, Fin.cons_self_tail]

/-- The procedure of Section 2.4.1 computes the encoding of `a`. -/
theorem computeEncoding_phi {L : ℕ} (a : LeftStr L → ℤ) : computeEncoding phi L a = encodingL a :=
  funext (computeEncoding_eq_encodeWith phi a)

/-- The procedure of Section 2.4.1 computes the encoding of `b`. -/
theorem computeEncoding_psi {L : ℕ} (b : RightStr L → ℤ) : computeEncoding psi L b = encodingR b :=
  funext (computeEncoding_eq_encodeWith psi b)

/-! ### Section 2.4.2: the sets `S_λ` of step (2) -/

/-- Membership in a slice of a set of output strings. -/
@[simp]
theorem mem_sliceSet {n : ℕ} (S : Finset (OutStr (n + 1))) (z : OutVar) (w' : OutStr n) :
    w' ∈ sliceSet S z ↔ (Fin.cons z w' : OutStr (n + 1)) ∈ S := by
  simp [sliceSet]

/-- Section 2.4.2, step (2): "i.e., S_{P_ij} := S_{z_ij} ∪ S_{z₀}". -/
theorem childSet_P {n : ℕ} (S : Finset (OutStr (n + 1))) (i j : Fin 3) :
    childSet S (.P i j) = sliceSet S (.z i j) ∪ sliceSet S .z0 := by
  have hz : (univ.filter fun z => (Term.P i j).Contributes z) = {.z i j, .z0} := by
    decide +revert
  rw [childSet, hz, biUnion_insert, singleton_biUnion]

/-- Section 2.4.2, step (2): "and S_{P₀} := S_{z₀}". -/
theorem childSet_P0 {n : ℕ} (S : Finset (OutStr (n + 1))) :
    childSet S .P0 = sliceSet S .z0 := by
  have hz : (univ.filter fun z => Term.P0.Contributes z) = {.z0} := by decide
  rw [childSet, hz, singleton_biUnion]

/-- Section 2.4.2, step (4): "These restrictions make sense, since S_{z_ij} ⊆ S_{P_ij} and S_{z₀} ⊆
S_λ for every λ, by step (2)": `S_z ⊆ S_λ` whenever `λ` contributes to `z`. -/
theorem sliceSet_subset_childSet {n : ℕ} (S : Finset (OutStr (n + 1))) {lam : Term} {z : OutVar}
    (h : lam.Contributes z) : sliceSet S z ⊆ childSet S lam :=
  subset_biUnion_of_mem (fun z => sliceSet S z) (mem_filter.mpr ⟨mem_univ z, h⟩)

/-- In the proof of Lemma 10: "S_λ consists of the last L-k-1 variables of each string in S
such that λ contributes to the first variable of that string." -/
theorem mem_childSet {n : ℕ} {S : Finset (OutStr (n + 1))} {lam : Term} {w' : OutStr n} :
    w' ∈ childSet S lam ↔ ∃ w ∈ S, lam.Contributes (w 0) ∧ Fin.tail w = w' := by
  simp only [childSet, mem_biUnion, mem_filter, mem_univ, true_and, mem_sliceSet]
  constructor
  · rintro ⟨z, hz, hw⟩
    exact ⟨_, hw, by simpa using hz, by simp⟩
  · rintro ⟨w, hw, hz, rfl⟩
    exact ⟨w 0, hz, by rwa [Fin.cons_self_tail]⟩

/-! ### Lemma 10, first claim: the values -/

/-- At a string of `S`, an array restricted to `S` has its own entry. -/
theorem restrictTo_of_mem {n : ℕ} {S : Finset (OutStr n)} {w : OutStr n} (h : w ∈ S)
    (c : OutStr n → ℤ) : restrictTo S c w = c w :=
  if_pos h

/-- An array restricted to the empty set is the zero array. -/
@[simp]
theorem restrictTo_empty {n : ℕ} (c : OutStr n → ℤ) : restrictTo ∅ c = 0 :=
  rfl

/-- The array `C_λ` of step (3) of `Pruned`; it is the zero array if `S_λ = ∅`. -/
def Pruned.childResult {n : ℕ} (encA encB : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1)))
    (lam : Term) : OutStr n → ℤ :=
  if (childSet S lam).Nonempty then
    Pruned n (sliceAt encA lam) (sliceAt encB lam) (childSet S lam)
  else 0

/-- Steps (2) to (4) of `Pruned`, written out. -/
theorem Pruned_succ {n : ℕ} (encA encB : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1))) :
    Pruned (n + 1) encA encB S = restrictTo S fun w =>
      match w 0 with
      | .z i j => Pruned.childResult encA encB S (.P i j) (Fin.tail w)
      | .z0 => ∑ lam, Pruned.childResult encA encB S lam (Fin.tail w) := by
  simp only [Pruned, Pruned.run, Pruned.childResult, apply_ite Prod.fst]
  rfl

/-- Step (4) of `Pruned` at one string: the entry at `w ∈ S` is the sum of the `C_λ`, at the rest of
`w`, over the terms `λ` that contribute to the first variable of `w`. -/
theorem Pruned_succ_apply {n : ℕ} (encA encB : Leaf (n + 1) → ℤ)
    (S : Finset (OutStr (n + 1))) (w : OutStr (n + 1)) :
    Pruned (n + 1) encA encB S w = if w ∈ S then
      ∑ lam : Term with lam.Contributes (w 0), Pruned.childResult encA encB S lam (Fin.tail w)
    else 0 := by
  rw [Pruned_succ, restrictTo, Term.sum_contributes]
  rfl

/-- What `Pruned` returns, for arbitrary arrays in place of the two encodings: at each string of
`S`, the sum, over the leaves contributing to it, of the product of the two numbers looked up at the
leaf in step (1). -/
theorem Pruned_eq_restrictTo_sum {n : ℕ} (encA encB : Leaf n → ℤ) (S : Finset (OutStr n)) :
    Pruned n encA encB S
      = restrictTo S fun w => ∑ τ : Leaf n with Leaf.Contributes τ w, encA τ * encB τ := by
  induction n with
  | zero =>
    -- The only leaf is the empty string, and it contributes to the empty output string.
    have hleaf (w : OutStr 0) :
        (univ.filter fun τ : Leaf 0 => Leaf.Contributes τ w) = {Fin.elim0} :=
      eq_singleton_iff_unique_mem.mpr
        ⟨mem_filter.mpr ⟨mem_univ _, fun ℓ => ℓ.elim0⟩, fun _ _ => Subsingleton.elim _ _⟩
    simp only [Pruned, Pruned.run, hleaf, sum_singleton]
  | succ n ih =>
    -- The induction hypothesis describes each `C_λ`, also when `S_λ = ∅`.
    have hC (lam : Term) : Pruned.childResult encA encB S lam
        = restrictTo (childSet S lam) fun w' =>
          ∑ τ' : Leaf n with Leaf.Contributes τ' w',
            encA (Fin.cons lam τ') * encB (Fin.cons lam τ') := by
      unfold Pruned.childResult
      split_ifs with hne
      · exact ih _ _ _
      · rw [not_nonempty_iff_eq_empty.mp hne, restrictTo_empty]
    -- Step (4) reads `C_λ` only at strings of `S_λ`, and a leaf is its first term and the rest.
    funext w
    rw [Pruned_succ_apply, restrictTo, Leaf.sum_contributes_succ]
    split_ifs with hw
    · refine sum_congr rfl fun lam hlam => ?_
      have hmem : Fin.tail w ∈ childSet S lam :=
        mem_childSet.mpr ⟨w, hw, (mem_filter.mp hlam).2, rfl⟩
      rw [hC, restrictTo_of_mem hmem]
    · rfl

/-- **Lemma 10**, first claim.  "Let a and b be input arrays, and let U be a set of output
strings of length L. Called at the root, Pruned(U) returns Mult(a, b) restricted to U." -/
theorem Lemma10.values {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (U : Finset (OutStr L)) :
    Pruned L (encodingL a) (encodingR b) U = restrictTo U (Mult a b) :=
  -- By definition, `Mult` is the sum over the contributing leaves of the products of the encoded
  -- numbers.
  Pruned_eq_restrictTo_sum _ _ U

/-- Section 2.4.2, the specification of `Pruned`: it "returns the array returned by the vertex
τ₁⋯τ_k of Full, restricted to the strings in S".  Here `a` and `b` are the input arrays of that
vertex: by `Phi_cons` and `Psi_cons`, applied once for each level, the parts of the two encodings
below a vertex are the encodings of its input arrays. -/
theorem Pruned_eq_restrictTo_Full {n : ℕ} (a : LeftStr n → ℤ) (b : RightStr n → ℤ)
    (S : Finset (OutStr n)) :
    Pruned n (encodingL a) (encodingR b) S = restrictTo S (Full n a b) := by
  rw [Lemma10.values, Lemma7.returns_Mult]

/-! ### Lemma 10, second claim: the calls that are made and the sets passed to them -/

/-- Section 2.3.2: "a vertex τ₁ ⋯ τ_k contributes to an output string w if τ_ℓ contributes to w_ℓ at
every level ℓ ≤ k."  Only `k ≤ L` occurs; the hypothesis `h` is there so that `w_ℓ` makes sense. -/
def Vertex.Contributes {k L : ℕ} (τ : Vertex k) (w : OutStr L) : Prop :=
  ∀ (ℓ : Fin k) (h : (ℓ : ℕ) < L), (τ ℓ).Contributes (w ⟨ℓ, h⟩)

/-- Section 2.3.2: for a vertex at depth `L`, that is, a leaf, "contributes to" means that `τ_ℓ`
contributes to `w_ℓ` at every level. -/
theorem Vertex.contributes_iff_leaf {L : ℕ} (τ : Leaf L) (w : OutStr L) :
    Vertex.Contributes τ w ↔ Leaf.Contributes τ w :=
  ⟨fun h ℓ => h ℓ ℓ.2, fun h ℓ _ => h ℓ⟩

/-- The vertex `λ τ₁⋯τ_k` contributes to `w` if and only if `λ` contributes to the first variable of
`w` and `τ₁⋯τ_k` contributes to the rest of `w`. -/
theorem Vertex.contributes_cons {k L : ℕ} {lam : Term} {τ : Vertex k} {w : OutStr (L + 1)} :
    Vertex.Contributes (Fin.cons lam τ : Vertex (k + 1)) w
      ↔ lam.Contributes (w 0) ∧ Vertex.Contributes τ (Fin.tail w) := by
  constructor
  · intro h
    exact ⟨h 0 (Nat.succ_pos L), fun ℓ hℓ => h ℓ.succ (Nat.succ_lt_succ hℓ)⟩
  · rintro ⟨h0, h1⟩ ℓ h
    induction ℓ using Fin.cases with
    | zero => exact h0
    | succ i => exact h1 i (Nat.lt_of_succ_lt_succ h)

/-- The calls made by the child `λ` of `Pruned(S)`: none if `S_λ = ∅`. -/
def Pruned.childCalls {n : ℕ} (encA encB : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1)))
    (lam : Term) : Multiset PrunedCall :=
  if (childSet S lam).Nonempty then
    Pruned.calls n (sliceAt encA lam) (sliceAt encB lam) (childSet S lam)
  else 0

/-- The calls made by `Pruned(S)`: the call itself, and the calls made by the children `λ` with
`S_λ ≠ ∅`. -/
theorem Pruned.calls_succ {n : ℕ} (encA encB : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1))) :
    Pruned.calls (n + 1) encA encB S = ⟨⟨0, Fin.elim0⟩, ⟨n + 1, S⟩⟩ ::ₘ
      univ.val.bind fun lam => (Pruned.childCalls encA encB S lam).map (.under lam) := by
  simp only [Pruned.calls, Pruned.run, Pruned.childCalls, apply_ite Prod.snd]

/-- The calls of `Pruned(S)`, one level unfolded (steps (2) and (3)): the call itself, and for each
term `λ` with `S_λ ≠ ∅` the calls of `Pruned_λ(S_λ)`. -/
theorem Pruned.mem_calls_succ {n : ℕ} {encA encB : Leaf (n + 1) → ℤ}
    {S : Finset (OutStr (n + 1))} {c : PrunedCall} :
    c ∈ Pruned.calls (n + 1) encA encB S ↔
      c = ⟨⟨0, Fin.elim0⟩, ⟨n + 1, S⟩⟩
        ∨ ∃ lam : Term, (childSet S lam).Nonempty
            ∧ ∃ c' ∈ Pruned.calls n (sliceAt encA lam) (sliceAt encB lam) (childSet S lam),
                c = c'.under lam := by
  rw [Pruned.calls_succ, Multiset.mem_cons, Multiset.mem_bind]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨lam, -, h⟩
    obtain ⟨c', hc', rfl⟩ := Multiset.mem_map.mp h
    unfold Pruned.childCalls at hc'
    split_ifs at hc' with hne
    · exact ⟨lam, hne, c', hc', rfl⟩
    · simp at hc'
  · rintro ⟨lam, hne, c', hc', rfl⟩
    refine ⟨lam, mem_univ lam, Multiset.mem_map.mpr ⟨c', ?_, rfl⟩⟩
    rwa [Pruned.childCalls, if_pos hne]

/-- A call below the child `λ` is at the vertex `τ` of depth `k + 1` exactly if `λ` is the first
term of `τ` and, seen from the child, the call is at the rest of `τ`. -/
private theorem PrunedCall.vertex_under_eq_iff {lam : Term} {c : PrunedCall} {k : ℕ}
    {τ : Vertex (k + 1)} :
    (c.under lam).vertex = ⟨k + 1, τ⟩ ↔ lam = τ 0 ∧ c.vertex = ⟨k, Fin.tail τ⟩ := by
  obtain ⟨⟨k', τ'⟩, T⟩ := c
  constructor
  · intro h
    simp only [PrunedCall.under, Sigma.mk.injEq, Nat.add_right_cancel_iff] at h
    obtain ⟨rfl, h⟩ := h
    obtain rfl := eq_of_heq h
    simp
  · rintro ⟨rfl, h⟩
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain rfl := eq_of_heq h
    simp [PrunedCall.under]

/-- `Pruned(U)`, called at the root, calls the vertex `τ`.  For a leaf this is `Pruned.Visits`. -/
def Pruned.Called {L k : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) (τ : Vertex k) :
    Prop :=
  ∃ c ∈ Pruned.calls L encA encB U, c.vertex = ⟨k, τ⟩

/-- The root is called. -/
theorem Pruned.called_root {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L))
    (τ : Vertex 0) : Pruned.Called encA encB U τ := by
  obtain rfl : τ = Fin.elim0 := Subsingleton.elim _ _
  cases L with
  | zero => exact ⟨_, Multiset.mem_singleton_self _, rfl⟩
  | succ n => exact ⟨_, Pruned.mem_calls_succ.mpr (.inl rfl), rfl⟩

/-- Step (3): a vertex `λ τ'` below the root is called exactly if `S_λ ≠ ∅` and the child `λ` calls
`τ'`. -/
theorem Pruned.called_succ {n k : ℕ} (encA encB : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1)))
    (τ : Vertex (k + 1)) :
    Pruned.Called encA encB S τ ↔ (childSet S (τ 0)).Nonempty ∧
      Pruned.Called (sliceAt encA (τ 0)) (sliceAt encB (τ 0)) (childSet S (τ 0)) (Fin.tail τ) := by
  constructor
  · rintro ⟨c, hc, hcτ⟩
    rcases Pruned.mem_calls_succ.mp hc with rfl | ⟨lam, hne, c', hc', rfl⟩
    · exact absurd (congrArg Sigma.fst hcτ) (by simp)
    · obtain ⟨rfl, hc'τ⟩ := PrunedCall.vertex_under_eq_iff.mp hcτ
      exact ⟨hne, c', hc', hc'τ⟩
  · rintro ⟨hne, c', hc', hc'τ⟩
    exact ⟨c'.under (τ 0), Pruned.mem_calls_succ.mpr (.inr ⟨τ 0, hne, c', hc', rfl⟩),
      PrunedCall.vertex_under_eq_iff.mpr ⟨rfl, hc'τ⟩⟩

/-- The vertex `λ τ'` contributes to a string of `S` exactly if `τ'` contributes to a string of
`S_λ`. -/
private theorem exists_contributes_childSet {n k : ℕ} (S : Finset (OutStr (n + 1)))
    (τ : Vertex (k + 1)) :
    (∃ w' ∈ childSet S (τ 0), Vertex.Contributes (Fin.tail τ) w')
      ↔ ∃ w ∈ S, Vertex.Contributes τ w := by
  have hcons (w : OutStr (n + 1)) : Vertex.Contributes τ w
      ↔ (τ 0).Contributes (w 0) ∧ Vertex.Contributes (Fin.tail τ) (Fin.tail w) := by
    rw [← Vertex.contributes_cons, Fin.cons_self_tail]
  constructor
  · rintro ⟨w', hw', hτ'⟩
    obtain ⟨w, hw, hz, rfl⟩ := mem_childSet.mp hw'
    exact ⟨w, hw, (hcons w).mpr ⟨hz, hτ'⟩⟩
  · rintro ⟨w, hw, hτ⟩
    exact ⟨_, mem_childSet.mpr ⟨w, hw, ((hcons w).mp hτ).1, rfl⟩, ((hcons w).mp hτ).2⟩

/-- A vertex at depth `k ≤ L` is called by `Pruned(U)` if and only if it is the root or it
contributes to some string of `U` (proof of Lemma 10).  The induction follows the
recursion: the vertex `λ τ'` is called by `Pruned(U)` exactly if `τ'` is called by `Pruned(U_λ)`. -/
theorem Pruned.called_iff_root_or {L k : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L))
    (hkL : k ≤ L) (τ : Vertex k) :
    Pruned.Called encA encB U τ ↔ k = 0 ∨ ∃ w ∈ U, Vertex.Contributes τ w := by
  induction L generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact iff_of_true (Pruned.called_root encA encB U τ) (.inl rfl)
  | succ n ih =>
    cases k with
    | zero => exact iff_of_true (Pruned.called_root encA encB U τ) (.inl rfl)
    | succ k =>
      have ihτ := ih (sliceAt encA (τ 0)) (sliceAt encB (τ 0)) (childSet U (τ 0))
        (Nat.le_of_succ_le_succ hkL) (Fin.tail τ)
      rw [Pruned.called_succ, ← exists_contributes_childSet]
      constructor
      · rintro ⟨⟨w', hw'⟩, hcalled⟩
        rcases ihτ.mp hcalled with rfl | hτ'
        · -- The child `λ` itself, as a vertex at depth 0, contributes to every string of `U_λ`.
          exact .inr ⟨w', hw', fun ℓ => ℓ.elim0⟩
        · exact .inr hτ'
      · rintro (hk | ⟨w', hw', hτ'⟩)
        · exact absurd hk (Nat.succ_ne_zero k)
        · exact ⟨⟨w', hw'⟩, ihτ.mpr (.inr ⟨w', hw', hτ'⟩)⟩

/-- In the proof of Lemma 10: "the vertex is called if and only if this set is nonempty",
that is, if and only if the vertex contributes to some string of `U`.

NOTE.  As printed this fails for the root when `U = ∅` (the root is always called).  The hypothesis
`hk` excludes only that case.  `hkL` says that `τ` is a vertex of the recursion tree, whose depth is
at most `L` (Section 2.3.1); the type `Vertex k` exists for every `k`. -/
theorem Pruned.called_iff {L k : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L))
    (hk : 1 ≤ k ∨ U.Nonempty) (hkL : k ≤ L) (τ : Vertex k) :
    Pruned.Called encA encB U τ ↔ ∃ w ∈ U, Vertex.Contributes τ w := by
  rw [Pruned.called_iff_root_or _ _ U hkL τ]
  constructor
  · rintro (rfl | h)
    · obtain ⟨w, hw⟩ := hk.resolve_left (by omega)
      exact ⟨w, hw, fun ℓ => ℓ.elim0⟩
    · exact h
  · exact Or.inr

/-- A call at depth `k` is passed strings of length `L - k`. -/
theorem Pruned.depth_add_length {L : ℕ} {encA encB : Leaf L → ℤ} {U : Finset (OutStr L)}
    {c : PrunedCall} (hc : c ∈ Pruned.calls L encA encB U) : c.vertex.1 + c.passed.1 = L := by
  induction L generalizing c with
  | zero =>
    obtain rfl := Multiset.mem_singleton.mp hc
    rfl
  | succ n ih =>
    rcases Pruned.mem_calls_succ.mp hc with rfl | ⟨lam, -, c', hc', rfl⟩
    · exact Nat.zero_add _
    · have hlen := ih hc'
      change c'.vertex.1 + 1 + c'.passed.1 = n + 1
      omega

/-- `w'` is the suffix of `w` that is left when the first `k` variables are removed. -/
def IsSuffixFrom {n L : ℕ} (k : ℕ) (w' : OutStr n) (w : OutStr L) : Prop :=
  ∀ (i : Fin n) (hi : k + (i : ℕ) < L), w' i = w ⟨k + i, hi⟩

/-- Removing no variable leaves the string as it is. -/
private theorem isSuffixFrom_zero {n : ℕ} (w' w : OutStr n) : IsSuffixFrom 0 w' w ↔ w' = w := by
  have hidx (i : Fin n) (hi : 0 + (i : ℕ) < n) : (⟨0 + i, hi⟩ : Fin n) = i :=
    Fin.ext (Nat.zero_add _)
  constructor
  · intro h
    funext i
    rw [h i (by simp), hidx]
  · rintro rfl i hi
    rw [hidx]

/-- Removing `k + 1` variables is removing the first variable and then `k` more. -/
private theorem isSuffixFrom_succ {n L k : ℕ} {w' : OutStr n} {w : OutStr (L + 1)} :
    IsSuffixFrom (k + 1) w' w ↔ IsSuffixFrom k w' (Fin.tail w) := by
  have hidx (i : Fin n) (h₁ : k + 1 + (i : ℕ) < L + 1) (h₂ : k + (i : ℕ) < L) :
      w ⟨k + 1 + i, h₁⟩ = Fin.tail w ⟨k + i, h₂⟩ :=
    congrArg w (Fin.ext (by simp only [Fin.val_succ]; omega))
  exact ⟨fun h i hi => (h i (by omega)).trans (hidx i _ hi),
    fun h i hi => (h i (by omega)).trans (hidx i hi _).symm⟩

/-- The set passed to the root is `U`, and the root contributes to every string. -/
private theorem mem_iff_root {L : ℕ} (U : Finset (OutStr L)) (w' : OutStr L) :
    w' ∈ U ↔ ∃ w ∈ U, Vertex.Contributes (Fin.elim0 : Vertex 0) w ∧ IsSuffixFrom 0 w' w := by
  simp only [isSuffixFrom_zero]
  exact ⟨fun h => ⟨w', h, fun ℓ => ℓ.elim0, rfl⟩, fun ⟨_, hw, _, h⟩ => h ▸ hw⟩

/-- Proof of Lemma 10 (announced in Section 2.4.2): "the set passed to the vertex τ₁⋯τ_k
consists of the suffixes w_{k+1}⋯w_L of the strings w of U to which the vertex contributes".  For a
call `c`, `c.vertex.1` is the depth `k`, `c.vertex.2` the vertex, `c.passed.1` the length `L - k` of
the strings passed, and `c.passed.2` the set passed. -/
theorem Pruned.mem_passed_iff {L : ℕ} {encA encB : Leaf L → ℤ} {U : Finset (OutStr L)}
    {c : PrunedCall} (hc : c ∈ Pruned.calls L encA encB U) (w' : OutStr c.passed.1) :
    w' ∈ c.passed.2 ↔
      ∃ w ∈ U, Vertex.Contributes c.vertex.2 w ∧ IsSuffixFrom c.vertex.1 w' w := by
  induction L generalizing c with
  | zero =>
    obtain rfl := Multiset.mem_singleton.mp hc
    exact mem_iff_root U w'
  | succ n ih =>
    rcases Pruned.mem_calls_succ.mp hc with rfl | ⟨lam, -, c', hc', rfl⟩
    · exact mem_iff_root U w'
    · -- A vertex below the child `λ`: the induction hypothesis for `S_λ`, whose strings are the
      -- rests of the strings of `U` to whose first variable `λ` contributes.
      refine (ih hc' w').trans ⟨?_, ?_⟩
      · rintro ⟨_, hw₁, hτ, hsuffix⟩
        obtain ⟨w, hw, hz, rfl⟩ := mem_childSet.mp hw₁
        exact ⟨w, hw, Vertex.contributes_cons.mpr ⟨hz, hτ⟩, isSuffixFrom_succ.mpr hsuffix⟩
      · rintro ⟨w, hw, hτ, hsuffix⟩
        obtain ⟨hz, hτ'⟩ := Vertex.contributes_cons.mp hτ
        exact ⟨Fin.tail w, mem_childSet.mpr ⟨w, hw, hz, rfl⟩, hτ', isSuffixFrom_succ.mp hsuffix⟩

/-- **Lemma 10**, second claim.  "The leaves it visits are exactly those of Leaves(U)".  The
hypothesis `0 < L ∨ U.Nonempty` is explained at `lemma_10`. -/
theorem Lemma10.leaves_visited {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L))
    (h : 0 < L ∨ U.Nonempty) (τ : Leaf L) : Pruned.Visits encA encB U τ ↔ τ ∈ Leaves U :=
  -- A leaf is a vertex at depth `L`.
  (Pruned.called_iff encA encB U h le_rfl τ).trans
    (by simp only [mem_Leaves, Vertex.contributes_iff_leaf])

/-! ### Lemma 10, third claim: the total size of the sets passed -/

/-- The leaf `λ τ'` is in `Leaves(S)` if and only if `τ'` is in `Leaves(S_λ)`. -/
theorem mem_Leaves_succ {n : ℕ} {S : Finset (OutStr (n + 1))} {τ : Leaf (n + 1)} :
    τ ∈ Leaves S ↔ Fin.tail τ ∈ Leaves (childSet S (τ 0)) := by
  rw [mem_Leaves, mem_Leaves]
  constructor
  · rintro ⟨w, hw, hcon⟩
    obtain ⟨h0, h1⟩ := Leaf.contributes_succ.mp hcon
    exact ⟨Fin.tail w, mem_childSet.mpr ⟨w, hw, h0, rfl⟩, h1⟩
  · rintro ⟨w', hw', h1⟩
    obtain ⟨w, hw, h0, rfl⟩ := mem_childSet.mp hw'
    exact ⟨w, hw, Leaf.contributes_succ.mpr ⟨h0, h1⟩⟩

/-- `Leaves(S)` is the disjoint union, over the terms `λ`, of the leaves `λ τ'` with `τ'` in
`Leaves(S_λ)`. -/
theorem card_Leaves_succ {n : ℕ} (S : Finset (OutStr (n + 1))) :
    (Leaves S).card = ∑ lam, (Leaves (childSet S lam)).card := by
  rw [card_eq_sum_card_fiberwise (f := fun τ : Leaf (n + 1) => τ 0) (t := univ)
    (fun _ _ => mem_coe.mpr (mem_univ _))]
  refine sum_congr rfl fun lam _ => ?_
  rw [← card_image_of_injective (Leaves (childSet S lam))
    (Fin.cons_right_injective (α := fun _ : Fin (n + 1) => Term) lam)]
  congr 1
  ext τ
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hτ, rfl⟩
    exact ⟨Fin.tail τ, mem_Leaves_succ.mp hτ, Fin.cons_self_tail τ⟩
  · rintro ⟨τ', hτ', rfl⟩
    refine ⟨mem_Leaves_succ.mpr ?_, Fin.cons_zero _ _⟩
    simpa using hτ'

/-- Different output strings have different private leaves. -/
theorem privateLeaf_injective {L : ℕ} : Function.Injective (privateLeaf (L := L)) :=
  have hterm : Function.Injective OutVar.privateTerm := by decide
  fun _ _ h => funext fun ℓ => hterm (congrFun h ℓ)

/-- The map of the proof of Lemma 10, at the root: an output string goes to the leaf that
picks `P_ij` where the string has `z_ij` and `P₀` where it has `z₀`.  The leaf contributes to the
string and determines it, so a set of output strings is no larger than its set of leaves. -/
theorem card_le_card_Leaves {n : ℕ} (S : Finset (OutStr n)) : S.card ≤ (Leaves S).card := by
  refine card_le_card_of_injOn privateLeaf (fun w hw => ?_) privateLeaf_injective.injOn
  exact mem_coe.mpr (mem_Leaves.mpr
    ⟨w, hw, fun _ => (Term.contributes_iff _ _).mpr (.inr rfl)⟩)

/-- The total size of the sets passed to the calls at depth `k` in a list of calls. -/
private def sizeAt (s : Multiset PrunedCall) (k : ℕ) : ℕ :=
  ((s.filter fun c => c.vertex.1 = k).map fun c => c.passed.2.card).sum

/-- The size at depth `k` of a list of calls with one more call. -/
private theorem sizeAt_cons (c : PrunedCall) (s : Multiset PrunedCall) (k : ℕ) :
    sizeAt (c ::ₘ s) k
      = (if c.vertex.1 = k then c.passed.2.card else 0) + sizeAt s k := by
  unfold sizeAt
  rw [Multiset.filter_cons]
  split_ifs <;> simp

/-- The size at depth `k` of the lists of calls of the ten children together. -/
private theorem sizeAt_bind (f : Term → Multiset PrunedCall) (k : ℕ) :
    sizeAt (univ.val.bind f) k = ∑ lam, sizeAt (f lam) k := by
  unfold sizeAt
  rw [Multiset.filter_bind, Multiset.map_bind, Multiset.sum_bind]
  rfl

/-- Seen from one level higher, the calls at depth `k` are at depth `k + 1`. -/
private theorem sizeAt_under_succ (lam : Term) (s : Multiset PrunedCall) (k : ℕ) :
    sizeAt (s.map (PrunedCall.under lam)) (k + 1) = sizeAt s k := by
  unfold sizeAt
  rw [Multiset.filter_map, Multiset.map_map]
  rw [Multiset.filter_congr (q := fun c => c.vertex.1 = k) (by simp [PrunedCall.under])]
  rfl

/-- Seen from one level higher, no call is at depth `0`. -/
private theorem sizeAt_under_zero (lam : Term) (s : Multiset PrunedCall) :
    sizeAt (s.map (PrunedCall.under lam)) 0 = 0 := by
  unfold sizeAt
  rw [Multiset.filter_map, Multiset.filter_eq_nil.mpr (by simp [PrunedCall.under])]
  rfl

/-- The total size of the sets passed is the sum, over the depths, of the sizes at each depth. -/
private theorem sum_sizeAt (s : Multiset PrunedCall) (N : ℕ) (h : ∀ c ∈ s, c.vertex.1 < N) :
    (s.map fun c => c.passed.2.card).sum = ∑ k ∈ range N, sizeAt s k := by
  induction s using Multiset.induction_on with
  | empty => simp [sizeAt]
  | cons c s ih =>
    simp only [sizeAt_cons, Multiset.map_cons, Multiset.sum_cons, sum_add_distrib]
    rw [ih fun c' hc' => h c' (Multiset.mem_cons_of_mem hc'), sum_ite_eq,
      if_pos (mem_range.mpr (h c (Multiset.mem_cons_self c s)))]

/-- End of the proof of Lemma 10: "the sets passed to the vertices at each of the L+1
depths have total size at most |Leaves(U)|." -/
theorem Pruned.sum_card_passed_le {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) (k : ℕ) :
    (((Pruned.calls L encA encB U).filter fun c => c.vertex.1 = k).map fun c => c.passed.2.card).sum
      ≤ (Leaves U).card := by
  -- The paper's injection (vertex, suffix) ↦ leaf, organised as an induction on `L`: the strings
  -- passed to the root inject into `Leaves(U)`, and the calls at depth `k + 1` are the calls at
  -- depth `k` of the children `λ`, whose leaves, with `λ` put in front, are pairwise disjoint parts
  -- of `Leaves(U)`.
  change sizeAt (Pruned.calls L encA encB U) k ≤ _
  induction L generalizing k with
  | zero =>
    have hcalls : Pruned.calls 0 encA encB U = ⟨⟨0, Fin.elim0⟩, ⟨0, U⟩⟩ ::ₘ 0 := rfl
    rw [hcalls, sizeAt_cons]
    split_ifs
    · simpa [sizeAt] using card_le_card_Leaves U
    · simp [sizeAt]
  | succ n ih =>
    rw [Pruned.calls_succ, sizeAt_cons, sizeAt_bind]
    cases k with
    | zero =>
      simp only [sizeAt_under_zero, sum_const_zero, if_true, add_zero]
      exact card_le_card_Leaves U
    | succ k =>
      simp only [sizeAt_under_succ]
      rw [if_neg (by simp), zero_add, card_Leaves_succ]
      refine sum_le_sum fun lam _ => ?_
      unfold Pruned.childCalls
      split_ifs
      · exact ih _ _ _ _
      · simp [sizeAt]

/-- **Lemma 10**, third claim.  "the sets passed to the calls it makes have total size at
most (L+1) |Leaves(U)|." -/
theorem Lemma10.total_size {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) :
    Pruned.totalSize encA encB U ≤ (L + 1) * (Leaves U).card := by
  have hdepth : ∀ c ∈ Pruned.calls L encA encB U, c.vertex.1 < L + 1 :=
    fun c hc => by have := Pruned.depth_add_length hc; omega
  rw [Pruned.totalSize, sum_sizeAt _ (L + 1) hdepth]
  calc ∑ k ∈ range (L + 1), sizeAt (Pruned.calls L encA encB U) k
      ≤ ∑ _k ∈ range (L + 1), (Leaves U).card :=
        sum_le_sum fun k _ => Pruned.sum_card_passed_le _ _ U k
    _ = (L + 1) * (Leaves U).card := by simp

/-- **Lemma 10**, its three claims together.  "Let a and b be input arrays, and let U be a
set of output strings of length L. Called at the root, Pruned(U) returns Mult(a, b) restricted to U.
The leaves it visits are exactly those of Leaves(U), and the sets passed to the calls it makes have
total size at most (L+1) |Leaves(U)|."

NOTE.  The hypothesis `0 < L ∨ U.Nonempty` of the second claim is not in the paper.  It excludes
only the case `L = 0`, `U = ∅`, in which the root is itself a leaf, so that the call at the root
visits it, while `Leaves(∅)` is empty.  In the paper `L ≥ m ≥ 1`, and `Pruned` is run only on
nonempty sets (Section 2.4.4). -/
theorem lemma_10 {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (U : Finset (OutStr L)) :
    Pruned L (encodingL a) (encodingR b) U = restrictTo U (Mult a b)
      ∧ (0 < L ∨ U.Nonempty →
          ∀ τ : Leaf L, Pruned.Visits (encodingL a) (encodingR b) U τ ↔ τ ∈ Leaves U)
      ∧ Pruned.totalSize (encodingL a) (encodingR b) U ≤ (L + 1) * (Leaves U).card :=
  ⟨Lemma10.values a b U, Lemma10.leaves_visited _ _ U, Lemma10.total_size _ _ U⟩

end ThreeSumApsp
