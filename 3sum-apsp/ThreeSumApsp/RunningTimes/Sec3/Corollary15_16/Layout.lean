/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.TopProcedure
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Sec3.MatrixLanguage

/-!
# The thin matrix product and the lopsided triangle problems in the layout of the word RAM

A solver of the thin matrix product, of #Lop-AE-SparseTri or of Lop-AE-SparseTri gets its sizes, the
bound on the entries and its addresses as arguments.  The three problems on the word RAM have one
layout: the cells 0, 1, 2 hold N, D and the number w of wanted positions, then come X, Y, the rows
and the columns of the wanted positions, then the output.

One more procedure, `thinTop`, is appended to the program of the solver: it reads N, D, w, forms the
bound N^e by e multiplications (the instances have the bound U = N^κ on their entries, for a fixed
exponent κ; e = κ for the matrix product, e = 0 for matrices of zeros and ones), computes the
addresses, calls the solver, and returns 1.

* `pre_toThinU`: the input is an instance of the task;
* `thinTop_ends`: the run of the outermost call;
* `small_limN`, `input_le_limN`: the limits are polynomial in N and D, and the input fits;
* `realizedN`: from a solver to the word RAM; `realized_thinProduct` and `realized_lop` (with
  `realized_lopCount` and `realized_lopDetect`) are its uses.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.WordRam

/-! ## The outermost procedure -/

/-- The outermost procedure.  Local 1 is N, 2 is the bound N^e, 3 is D, 4 is w; 5 to 9 are the
addresses of Y, of the rows, of the columns, of the output, and the free pointer. -/
def thinTop (e p : ℕ) : Stmt :=
  .set 1 (M (k 0)) ;;
  .set 2 (k 1) ;;
  powStmt e ;;
  .set 3 (M (k 1)) ;;
  .set 4 (M (k 2)) ;;
  .set 5 (k 3 +' v 1 *' v 3) ;;
  .set 6 (v 5 +' v 3 *' v 1) ;;
  .set 7 (v 6 +' v 4) ;;
  .set 8 (v 7 +' v 4) ;;
  .set 9 (v 8 +' v 4) ;;
  .call p [v 1, v 3, v 4, v 2, k 3, v 5, v 6, v 7, v 8, v 9] 0 ;;
  .set 0 (k 1)

/-- A problem in the layout of the thin matrix product. -/
def thinProb (A : ThinInstance → Bool → (ℕ → ℤ) → Prop) : Problem where
  Inst := ThinInstance
  params x := [x.N, x.D]
  input x := x.input []
  IsAnswer := A

/-- A task with the calling convention of the thin matrix product. -/
def thinTaskOf (pars : ThinInst → List ℕ) (Pre : ThinInst → (ℕ → ℤ) → ℕ → Prop)
    (Post : ThinInst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop) : TaskN where
  Inst := ThinInst
  pars := pars
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre := Pre
  Post := Post

/-- The instance of the task, with the bound U that is handed to the solver. -/
def toThinU (x : ThinInstance) (U : ℕ) : ThinInst where
  N := x.N
  D := x.D
  w := x.W.length
  U := U
  x := 3
  y := 3 + x.N * x.D
  wi := 3 + x.N * x.D + x.D * x.N
  wj := 3 + x.N * x.D + x.D * x.N + x.W.length
  out := 3 + x.N * x.D + x.D * x.N + x.W.length + x.W.length
  X := rowMajor x.X
  Y := rowMajor x.Y
  WI := x.W.map fun q => q.1.val
  WJ := x.W.map fun q => q.2.val

/-- The free pointer: the first cell after the output. -/
def outputEnd (x : ThinInstance) : ℕ :=
  3 + x.N * x.D + x.D * x.N + x.W.length + x.W.length + x.W.length

/-- The input: three numbers, the two matrices, and the rows and the columns of the wanted
positions. -/
theorem length_input (x : ThinInstance) :
    (x.input []).length = 3 + x.N * x.D + x.D * x.N + x.W.length + x.W.length := by
  have h1 : (rowMajor x.X).length = x.N * x.D := length_rowMajor _
  have h2 : (rowMajor x.Y).length = x.D * x.N := length_rowMajor _
  simp [ThinInstance.input, h1, h2]
  omega

/-- A part of a list lies in the memory that holds the list. -/
theorem seg_memOf_of_eq {L pre l post : List ℤ} {a : ℕ} (h : L = pre ++ l ++ post)
    (ha : pre.length = a) : Seg (memOf L) a l := by
  subst h ha
  exact seg_memOf _ _ _

/-- The matrix X in the input. -/
theorem seg_input_X (x : ThinInstance) : Seg (memOf (x.input [])) 3 (rowMajor x.X) :=
  seg_memOf_of_eq (pre := [(x.N : ℤ), x.D, x.W.length])
    (post := rowMajor x.Y ++ (x.W.map (fun q => (q.1.val : ℤ)) ++ x.W.map fun q => (q.2.val : ℤ)))
    (by simp [ThinInstance.input]) rfl

/-- The matrix Y in the input. -/
theorem seg_input_Y (x : ThinInstance) :
    Seg (memOf (x.input [])) (3 + x.N * x.D) (rowMajor x.Y) :=
  seg_memOf_of_eq (pre := [(x.N : ℤ), x.D, x.W.length] ++ rowMajor x.X)
    (post := x.W.map (fun q => (q.1.val : ℤ)) ++ x.W.map fun q => (q.2.val : ℤ))
    (by simp [ThinInstance.input]) (by have := length_rowMajor x.X; simp; omega)

/-- The rows of the wanted positions in the input. -/
theorem seg_input_rows (x : ThinInstance) :
    Seg (memOf (x.input [])) (3 + x.N * x.D + x.D * x.N) (x.W.map fun q => (q.1.val : ℤ)) :=
  seg_memOf_of_eq (pre := [(x.N : ℤ), x.D, x.W.length] ++ rowMajor x.X ++ rowMajor x.Y)
    (post := x.W.map fun q => (q.2.val : ℤ))
    (by simp [ThinInstance.input])
    (by have := length_rowMajor x.X; have := length_rowMajor x.Y; simp; omega)

/-- The columns of the wanted positions in the input. -/
theorem seg_input_cols (x : ThinInstance) :
    Seg (memOf (x.input [])) (3 + x.N * x.D + x.D * x.N + x.W.length)
      (x.W.map fun q => (q.2.val : ℤ)) :=
  seg_memOf_of_eq (pre := [(x.N : ℤ), x.D, x.W.length] ++ rowMajor x.X ++ rowMajor x.Y ++
      x.W.map fun q => (q.1.val : ℤ)) (post := [])
    (by simp [ThinInstance.input])
    (by have := length_rowMajor x.X; have := length_rowMajor x.Y; simp; omega)

/-- The instance lies in the memory that holds the input. -/
theorem pre_toThinU (x : ThinInstance) (hN : 1 ≤ x.N) (hD : 1 ≤ x.D) {U : ℕ} (hU : 1 ≤ U)
    (hX : ∀ i j, |x.X i j| ≤ (U : ℤ)) (hY : ∀ i j, |x.Y i j| ≤ (U : ℤ)) :
    (toThinU x U).Pre (memOf (x.input [])) (outputEnd x) := by
  exact
    { N_pos := hN
      D_pos := hD
      U_pos := hU
      lenX := length_rowMajor _
      lenY := length_rowMajor _
      lenWI := by simp [toThinU]
      lenWJ := by simp [toThinU]
      segX := seg_input_X x
      segY := seg_input_Y x
      segWI := by
        change Seg _ _ ((x.W.map fun q => q.1.val).map fun i : ℕ => (i : ℤ))
        rw [List.map_map]
        exact seg_input_rows x
      segWJ := by
        change Seg _ _ ((x.W.map fun q => q.2.val).map fun i : ℕ => (i : ℤ))
        rw [List.map_map]
        exact seg_input_cols x
      leX := fun v hv => by
        obtain ⟨i, j, rfl⟩ := mem_rowMajor hv
        exact hX i j
      leY := fun v hv => by
        obtain ⟨i, j, rfl⟩ := mem_rowMajor hv
        exact hY i j
      ltWI := fun i hi => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 hi
        exact q.1.isLt
      ltWJ := fun i hi => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 hi
        exact q.2.isLt
      nodup := by
        change ((x.W.map fun q => q.1.val).zip (x.W.map fun q => q.2.val)).Nodup
        rw [List.zip_map']
        refine x.nodup.map fun a b h => ?_
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
      belowX := by simp only [toThinU, outputEnd]; omega
      belowY := by simp only [toThinU, outputEnd]; omega
      belowWI := by simp only [toThinU, outputEnd]; omega
      belowWJ := by simp only [toThinU, outputEnd]; omega
      belowOut := by simp only [toThinU, outputEnd]; omega
      apartX := Or.inr (by simp only [toThinU]; omega)
      apartY := Or.inr (by simp only [toThinU]; omega)
      apartWI := Or.inr (by simp only [toThinU]; omega)
      apartWJ := Or.inr (by simp only [toThinU]; omega) }

/-- The entries that the task asks for are the entries of the product. -/
theorem thinEntry_eq (x : ThinInstance) (I J : Fin x.N) :
    thinEntry x.N x.D (rowMajor x.X) (rowMajor x.Y) I J = (x.X * x.Y) I J := by
  rw [thinEntry, List.sum_map_range, Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [getD_rowMajor x.X I k, getD_rowMajor x.Y k J]

/-- The limits of the run on an instance, if the solver needs nd. -/
def runLimits (nd : Need) (x : ThinInstance) (e : ℕ) : Limits :=
  ⟨(nd.word + (outputEnd x + nd.cells) + x.N ^ e + x.N + x.D + 8 : ℕ), outputEnd x + nd.cells,
      nd.depth + 2⟩

/-- The first three cells of the input hold N, D and the number of wanted positions. -/
theorem memOf_input_N (x : ThinInstance) : memOf (x.input []) 0 = x.N := by
  simp [memOf, ThinInstance.input]

@[inherit_doc memOf_input_N]
theorem memOf_input_D (x : ThinInstance) : memOf (x.input []) 1 = x.D := by
  simp [memOf, ThinInstance.input]

@[inherit_doc memOf_input_N]
theorem memOf_input_w (x : ThinInstance) : memOf (x.input []) 2 = x.W.length := by
  simp [memOf, ThinInstance.input]

/-- The bound N^e is formed in local 2. -/
theorem pow_frame {lim : Limits} {P : Program} {d n : ℕ} (hn : 1 ≤ n) (e : ℕ) (μ : ℕ → ℤ)
    (hw : ((n ^ e : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d (powStmt e) ⟨frame [0, n, (1 : ℕ)], μ⟩ (4 * e) fun σ' =>
      σ' = ⟨frame [0, n, (n ^ e : ℕ)], μ⟩ := by
  simpa using pow_spec hn 0 μ e hw

/-- The run of the outermost call. -/
theorem thinTop_ends {pars : ThinInst → List ℕ} {Pre : ThinInst → (ℕ → ℤ) → ℕ → Prop}
    {Post : ThinInst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop} {P : Program} {p : ℕ}
    {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    (hsol : SolvesN (thinTaskOf pars Pre Post) P p Tn need) (e : ℕ) (x : ThinInstance)
    (hN : 1 ≤ x.N) (hpre : Pre (toThinU x (x.N ^ e)) (memOf (x.input [])) (outputEnd x)) :
    Ends (runLimits (need (pars (toThinU x (x.N ^ e)))) x e) (P ++ [thinTop e p]) 0
      (mainStmt P.length) ⟨frame [0, 0, 0], memOf (x.input [])⟩
      (Tn (pars (toThinU x (x.N ^ e))) + (4 * e + 60))
      fun σ' => ∃ r, Post (toThinU x (x.N ^ e)) (memOf (x.input [])) (outputEnd x) r σ'.mem := by
  generalize hnd : need (pars (toThinU x (x.N ^ e))) = nd
  generalize hT₀ : Tn (pars (toThinU x (x.N ^ e))) = T₀
  generalize hlim : runLimits nd x e = lim
  have hword : lim.word =
      ((nd.word + (outputEnd x + nd.cells) + x.N ^ e + x.N + x.D + 8 : ℕ) : ℤ) := by
    rw [← hlim]; rfl
  have hspace : lim.space = outputEnd x + nd.cells := by rw [← hlim]; rfl
  have hdepth : lim.depth = nd.depth + 2 := by rw [← hlim]; rfl
  have hfree : outputEnd x = 3 + x.N * x.D + x.D * x.N + x.W.length + x.W.length + x.W.length := rfl
  have hw : (lim.space : ℤ) ≤ lim.word := by rw [hword, hspace]; exact_mod_cast (by omega)
  have h8 : (8 : ℤ) ≤ lim.word := by rw [hword]; exact_mod_cast (by omega)
  have hUw : ((x.N ^ e : ℕ) : ℤ) ≤ lim.word := by rw [hword]; exact_mod_cast (by omega)
  have hok : nd.Ok lim (outputEnd x) (1 + 1) :=
    ⟨by rw [hword]; exact_mod_cast (by omega), by omega, hw, by omega⟩
  have hm : Meets lim (P ++ [thinTop e p]) p (1 + 1)
      [x.N, x.D, x.W.length, (x.N ^ e : ℕ), (3 : ℕ), (3 + x.N * x.D : ℕ),
        (3 + x.N * x.D + x.D * x.N : ℕ), (3 + x.N * x.D + x.D * x.N + x.W.length : ℕ),
        (3 + x.N * x.D + x.D * x.N + x.W.length + x.W.length : ℕ), (outputEnd x : ℕ)]
      (memOf (x.input [])) T₀ (Post (toThinU x (x.N ^ e)) (memOf (x.input [])) (outputEnd x)) :=
    hT₀ ▸ hsol.meets [thinTop e p] (toThinU x (x.N ^ e)) hpre (hnd ▸ hok)
  unfold mainStmt
  refine Ends.call (body := thinTop e p) (T₀ + 4 * e + 49) (by simp) (by simp) (by omega) ?_
    (by simp; omega)
  change Ends lim _ 1 (thinTop e p) ⟨frame [0, 0], memOf (x.input [])⟩ _ _
  -- N := mem[0]; U := 1
  light_set (x.N : ℕ) using memOf_input_N
  light_set (1 : ℕ)
  -- U := N^e
  refine Ends.next (4 * e) ((pow_frame hN e _ hUw).mono le_rfl ?_)
  rintro _ rfl
  -- D := mem[1]; w := mem[2]
  light_set (x.D : ℕ) using memOf_input_D
  light_set (x.W.length : ℕ) using memOf_input_w
  -- the addresses of Y, of the rows, of the columns, of the output, and the free pointer
  light_set (3 + x.N * x.D : ℕ)
  light_set (3 + x.N * x.D + x.D * x.N : ℕ)
  light_set (3 + x.N * x.D + x.D * x.N + x.W.length : ℕ)
  light_set (3 + x.N * x.D + x.D * x.N + x.W.length + x.W.length : ℕ)
  light_set (outputEnd x : ℕ)
  -- the solver; the result is 1
  refine Ends.callToThen hm fun r μ' hpost => ?_
  light_set (1 : ℕ)
  exact ⟨r, hpost⟩

/-! ## The limits are polynomial in N and D -/

/-- There are at most N² wanted positions. -/
theorem length_W_le (x : ThinInstance) : x.W.length ≤ x.N * x.N := by
  have := x.nodup.length_le_card
  simpa using this

theorem polyBound_two (s k N D : ℕ) : polyBound s k [N, D] = 2 ^ s * ((N + 1) * (D + 1)) ^ k := by
  simp [polyBound]

/-- A bound in N, D, the number of wanted positions and N^e is a bound in N and D. -/
theorem polyBound_four (s k κ e : ℕ) (he : e ≤ κ) (x : ThinInstance) (hN : 1 ≤ x.N) :
    polyBound s k [x.N, x.D, x.W.length, x.N ^ e] ≤ polyBound s ((κ + 4) * k) [x.N, x.D] := by
  have hw := length_W_le x
  rw [polyBound_two, pow_mul]
  simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ k)
  have hX : x.N + 1 ≤ (x.N + 1) * (x.D + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hX1 : 1 ≤ (x.N + 1) * (x.D + 1) := by omega
  have h1 : x.W.length + 1 ≤ ((x.N + 1) * (x.D + 1)) ^ 2 := by
    calc x.W.length + 1 ≤ (x.N + 1) ^ 2 := by
          have : (x.N + 1) ^ 2 = x.N * x.N + 2 * x.N + 1 := by ring
          omega
      _ ≤ _ := Nat.pow_le_pow_left hX 2
  have h2 : x.N ^ e + 1 ≤ ((x.N + 1) * (x.D + 1)) ^ (κ + 1) := by
    have a1 : x.N ^ e ≤ (x.N + 1) ^ κ :=
      (Nat.pow_le_pow_left (by omega) e).trans (Nat.pow_le_pow_right (by omega) he)
    have a2 : 1 ≤ (x.N + 1) ^ κ := Nat.one_le_pow _ _ (by omega)
    have a3 : 2 * (x.N + 1) ^ κ ≤ (x.N + 1) * (x.N + 1) ^ κ := Nat.mul_le_mul_right _ (by omega)
    calc x.N ^ e + 1 ≤ (x.N + 1) ^ (κ + 1) := by rw [pow_succ']; omega
      _ ≤ _ := Nat.pow_le_pow_left hX _
  calc (x.N + 1) * ((x.D + 1) * ((x.W.length + 1) * (x.N ^ e + 1)))
      = ((x.N + 1) * (x.D + 1)) * ((x.W.length + 1) * (x.N ^ e + 1)) := by ring
    _ ≤ ((x.N + 1) * (x.D + 1)) *
        (((x.N + 1) * (x.D + 1)) ^ 2 * ((x.N + 1) * (x.D + 1)) ^ (κ + 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
    _ = ((x.N + 1) * (x.D + 1)) ^ (κ + 4) := by ring

/-- The same without the bound on the entries. -/
theorem polyBound_three (s k κ : ℕ) (x : ThinInstance) (hN : 1 ≤ x.N) :
    polyBound s k [x.N, x.D, x.W.length] ≤ polyBound s ((κ + 4) * k) [x.N, x.D] := by
  refine le_trans ?_ (polyBound_four s k κ 0 (Nat.zero_le _) x hN)
  simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ k)
  refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
  exact Nat.le_mul_of_pos_right _ (by omega)

/-- The limits are polynomial in N and D. -/
theorem small_limN {nd : Need} {s k' κ e : ℕ} {x : ThinInstance} (he : e ≤ κ)
    (h1 : nd.word ≤ polyBound s k' [x.N, x.D])
    (h2 : nd.cells ≤ polyBound s k' [x.N, x.D]) (h3 : nd.depth ≤ polyBound s k' [x.N, x.D]) :
    Small (s + 5) (k' + κ + 2) [x.N, x.D] (runLimits nd x e) := by
  -- With X = (N + 1)(D + 1) and Z = 2^s X^(k' + κ + 2), each summand of the limits is at most a
  -- small multiple of Z, and the multiples add up to at most 32.
  have hw := length_W_le x
  rw [polyBound_two] at h1 h2 h3
  have hgoal : polyBound (s + 5) (k' + κ + 2) [x.N, x.D] =
      32 * (2 ^ s * ((x.N + 1) * (x.D + 1)) ^ (k' + κ + 2)) := by
    rw [polyBound_two, pow_add 2 s 5]
    ring
  -- The quantities that occur, in terms of X.
  have hXN : x.N + 1 ≤ (x.N + 1) * (x.D + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hXD : x.D + 1 ≤ (x.N + 1) * (x.D + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hND : x.N * x.D ≤ (x.N + 1) * (x.D + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hDN : x.D * x.N = x.N * x.D := Nat.mul_comm _ _
  have hNN : x.N * x.N ≤ ((x.N + 1) * (x.D + 1)) ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hNe : x.N ^ e ≤ ((x.N + 1) * (x.D + 1)) ^ κ :=
    (Nat.pow_le_pow_left (by omega) e).trans (Nat.pow_le_pow_right (by omega) he)
  generalize (x.N + 1) * (x.D + 1) = X at *
  have hX : 1 ≤ X := by omega
  -- The powers of X that occur are at most X^(k' + κ + 2), which is at most Z.
  have e1 : X ^ k' ≤ X ^ (k' + κ + 2) := Nat.pow_le_pow_right hX (by omega)
  have e2 : X ^ 2 ≤ X ^ (k' + κ + 2) := Nat.pow_le_pow_right hX (by omega)
  have e3 : X ^ κ ≤ X ^ (k' + κ + 2) := Nat.pow_le_pow_right hX (by omega)
  have e4 : X ≤ X ^ (k' + κ + 2) := by
    calc X = X ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hX (by omega)
  have e5 : 2 ^ s * X ^ k' ≤ 2 ^ s * X ^ (k' + κ + 2) := Nat.mul_le_mul_left _ e1
  have e6 : X ^ (k' + κ + 2) ≤ 2 ^ s * X ^ (k' + κ + 2) := Nat.le_mul_of_pos_left _ (by positivity)
  generalize 2 ^ s * X ^ (k' + κ + 2) = Z at *
  generalize X ^ (k' + κ + 2) = Y at *
  have hfree : outputEnd x = 3 + x.N * x.D + x.D * x.N + x.W.length + x.W.length + x.W.length := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> try rw [hgoal]
  · simp only [runLimits]
    positivity
  · simp only [runLimits]
    exact_mod_cast
        (by omega : nd.word + (outputEnd x + nd.cells) + x.N ^ e + x.N + x.D + 8 ≤ 32 * Z)
  · simp only [runLimits]
    omega
  · simp only [runLimits]
    omega

/-- Every number of the input fits in a word. -/
theorem input_le_limN (nd : Need) (x : ThinInstance) (e : ℕ)
    (hX : ∀ i j, |x.X i j| ≤ ((x.N ^ e : ℕ) : ℤ)) (hY : ∀ i j, |x.Y i j| ≤ ((x.N ^ e : ℕ) : ℤ)) :
    ∀ v ∈ x.input [], |v| ≤ (runLimits nd x e).word := by
  have hfree : outputEnd x = 3 + x.N * x.D + x.D * x.N + x.W.length + x.W.length + x.W.length := rfl
  have hp0 : (0 : ℤ) ≤ (x.N : ℤ) ^ e := by positivity
  intro v hv
  refine le_trans (b := ((outputEnd x + x.N ^ e + x.N + x.D : ℕ) : ℤ)) ?_ (by
    simp only [runLimits]
    exact_mod_cast (by omega))
  simp only [ThinInstance.input, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hv
  push_cast
  rcases hv with ((((rfl | rfl | rfl) | hv) | hv) | ⟨q, -, rfl⟩) | ⟨q, -, rfl⟩
  · rw [abs_of_nonneg (by positivity)]; omega
  · rw [abs_of_nonneg (by positivity)]; omega
  · rw [abs_of_nonneg (by positivity)]; omega
  · obtain ⟨i, j, rfl⟩ := mem_rowMajor hv
    have := hX i j
    push_cast at this
    omega
  · obtain ⟨i, j, rfl⟩ := mem_rowMajor hv
    have := hY i j
    push_cast at this
    omega
  · rw [abs_of_nonneg (by positivity)]
    have := q.1.isLt
    omega
  · rw [abs_of_nonneg (by positivity)]
    have := q.2.isLt
    omega

/-! ## From a solver to the word RAM -/

/-- **If a task with the calling convention of the thin matrix product is solved, the problem is
solved on the word RAM** within a constant times the time of the solver.  The bound that is handed
to the solver is N^(e κ). -/
theorem realizedN {A : ThinInstance → Bool → (ℕ → ℤ) → Prop} {pars : ThinInst → List ℕ}
    {Pre : ThinInst → (ℕ → ℤ) → ℕ → Prop}
    {Post : ThinInst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop} {dom : ThinInstance → Prop}
    {T : ThinInstance → ℝ} (e : ℕ → ℕ) (he : ∀ κ, e κ ≤ κ) {P : Program} {p : ℕ}
    {Tn : List ℕ → ℕ} {need : List ℕ → Need} (hpoly : PolyNeedN need)
    (hsol : SolvesN (thinTaskOf pars Pre Post) P p Tn need)
    (hpre : ∀ κ x, dom x → 1 ≤ x.N → x.U = x.N ^ κ →
      Pre (toThinU x (x.N ^ e κ)) (memOf (x.input [])) (outputEnd x))
    (hpost : ∀ κ x r μ', dom x → 1 ≤ x.N → x.U = x.N ^ κ →
      Post (toThinU x (x.N ^ e κ)) (memOf (x.input [])) (outputEnd x) r μ' →
      A x true fun i => μ' ((x.input []).length + i))
    (hpars : ∀ κ x s k, 1 ≤ x.N →
      polyBound s k (pars (toThinU x (x.N ^ e κ))) ≤ polyBound s ((κ + 4) * k) [x.N, x.D])
    (hle : ∀ κ x, dom x → 1 ≤ x.N → x.U = x.N ^ κ →
      (∀ i j, |x.X i j| ≤ ((x.N ^ e κ : ℕ) : ℤ)) ∧ ∀ i j, |x.Y i j| ≤ ((x.N ^ e κ : ℕ) : ℤ))
    (hT : ∀ κ x, dom x → 1 ≤ x.N → x.U = x.N ^ κ → (Tn (pars (toThinU x (x.N ^ e κ))) : ℝ) ≤ T x) :
    RealizedWithin (thinProb A) (fun x => x.N) (fun x => x.U) dom T := by
  obtain ⟨s, k, hpoly⟩ := hpoly
  intro κ
  -- The program with the outermost call solves the problem within T x + (4 e + 60) steps of the
  -- language, under polynomial limits; `solves_of_programSolves` carries this to the word RAM.
  have htop : ProgramSolves (thinProb A) (P ++ [thinTop (e κ) p]) P.length false (s + 5)
      ((κ + 4) * k + κ + 2) (fun x => dom x ∧ 1 ≤ x.N ∧ x.U = x.N ^ κ)
      (fun x => T x + ((4 * e κ + 60 : ℕ) : ℝ)) := by
    rintro x ⟨hd, hn, hU⟩
    obtain ⟨σ', c, hex, hc, r, hq⟩ := thinTop_ends hsol (e κ) x hn (hpre κ x hd hn hU)
    obtain ⟨b1, b2, b3⟩ := hpoly (pars (toThinU x (x.N ^ e κ)))
    have hb := hpars κ x s k hn
    refine ⟨_, σ', c, hex, ?_, ?_, small_limN (he κ) (b1.trans hb) (b2.trans hb) (b3.trans hb),
      hpost κ x r _ hd hn hU hq⟩
    · have : (c : ℝ) ≤ (Tn (pars (toThinU x (x.N ^ e κ))) : ℝ) + ((4 * e κ + 60 : ℕ) : ℝ) := by
        exact_mod_cast hc
      linarith [hT κ x hd hn hU]
    · exact input_le_limN _ x _ (hle κ x hd hn hU).1 (hle κ x hd hn hU).2
  refine ⟨_, _, (timeConst (P ++ [thinTop (e κ) p]) false : ℝ) * (((4 * e κ + 60 : ℕ) : ℝ) + 1),
    by positivity,
    (solves_of_programSolves htop (r := 2) fun x => by simp [thinProb]).mono le_rfl
      (fun _ hx => hx) ?_⟩
  rintro x ⟨hd, hn, hU⟩
  have h0 : (0 : ℝ) ≤ T x := le_trans (by positivity) (hT κ x hd hn hU)
  have hK : (0 : ℝ) ≤ (timeConst (P ++ [thinTop (e κ) p]) false : ℝ) := by positivity
  have hE : (0 : ℝ) ≤ ((4 * e κ + 60 : ℕ) : ℝ) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hK hE) h0]

/-! ## The three problems -/

/-- The answers that the tasks ask for are the wanted entries of the product. -/
theorem out_eq (x : ThinInstance) {U : ℕ} {μ' : ℕ → ℤ} {f : ℤ → ℤ}
    (h : Seg μ' (toThinU x U).out ((thinOut x.N x.D (rowMajor x.X) (rowMajor x.Y)
      (x.W.map fun q => q.1.val) (x.W.map fun q => q.2.val)).map f))
    (i : ℕ) (hi : i < x.W.length) :
    μ' ((x.input []).length + i) = f ((x.X * x.Y) x.W[i].1 x.W[i].2) := by
  have h1 := h i (by simp [thinOut]; exact hi)
  have h2 : (toThinU x U).out = (x.input []).length := (length_input x).symm
  rw [h2] at h1
  rw [h1]
  simp only [thinOut, List.getElem_map, List.getElem_zip]
  rw [thinEntry_eq]

/-- **The thin matrix product**: if the task is solved in time T, the wanted entries are computed on
the word RAM within a constant times T. -/
theorem realized_thinProduct (T : ℕ → ℕ → ℕ → ℝ → ℝ) (h : ThinSolvedIn T) :
    RealizedWithin (thinProduct []) (fun x => x.N) (fun x => x.U) (fun x => 1 ≤ x.D)
      (fun x => T x.N x.D x.W.length x.U) := by
  obtain ⟨P, p, Tn, need, hpoly, hsol, hT⟩ := h
  refine realizedN (A := (thinProduct []).IsAnswer) (pars := thinTask.pars) (Pre := thinTask.Pre)
    (Post := thinTask.Post) id
    (fun _ => le_rfl) hpoly hsol ?_ ?_ ?_ ?_ ?_
  · intro κ x hD hN hU
    exact pre_toThinU x hN hD (Nat.one_le_pow _ _ hN) (fun i j => hU ▸ x.boundX i j)
      (fun i j => hU ▸ x.boundY i j)
  · rintro κ x r μ' hD hN hU ⟨hseg, -⟩
    refine ⟨rfl, fun i hi => ?_⟩
    have := out_eq x (U := x.N ^ κ) (μ' := μ') (f := id) (by rw [List.map_id]; exact hseg) i hi
    exact this
  · intro κ x s k hN
    exact polyBound_four s k κ κ le_rfl x hN
  · intro κ x hD hN hU
    exact ⟨fun i j => hU ▸ x.boundX i j, fun i j => hU ▸ x.boundY i j⟩
  · intro κ x hD hN hU
    have := hT x.N x.D x.W.length x.W.length (x.N ^ κ) x.U hN hD (Nat.one_le_pow _ _ hN) le_rfl
      (by rw [hU])
    exact this

/-- The entries of matrices of zeros and ones are at most 1 = N^0. -/
theorem zeroOne_le {x : ThinInstance} (h : x.ZeroOne) :
    (∀ i j, |x.X i j| ≤ ((x.N ^ 0 : ℕ) : ℤ)) ∧ ∀ i j, |x.Y i j| ≤ ((x.N ^ 0 : ℕ) : ℤ) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rcases h.1 i j with e | e <;> simp [e]
  · rcases h.2 i j with e | e <;> simp [e]

/-- The instance of the two lopsided triangle tasks lies in the memory that holds the input. -/
theorem pre_lop {x : ThinInstance} (h : x.ZeroOne) (hD : 1 ≤ x.D) (hN : 1 ≤ x.N) :
    (toThinU x (x.N ^ 0)).Pre (memOf (x.input [])) (outputEnd x) ∧ (toThinU x (x.N ^ 0)).ZeroOne ∧
      (toThinU x (x.N ^ 0)).U = 1 := by
  refine ⟨pre_toThinU x hN hD (by simp) (zeroOne_le h).1 (zeroOne_le h).2,
    ⟨fun v hv => ?_, fun v hv => ?_⟩, by simp [toThinU]⟩
  · obtain ⟨i, j, rfl⟩ := mem_rowMajor hv
    exact h.1 i j
  · obtain ⟨i, j, rfl⟩ := mem_rowMajor hv
    exact h.2 i j

/-- **The two lopsided triangle problems**: what differs between them is how the answers are read
off the memory (hpost). -/
theorem realized_lop {A : ThinInstance → Bool → (ℕ → ℤ) → Prop}
    {Post : ThinInst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop} (T : ℕ → ℕ → ℕ → ℝ)
    (h : LopSolvedIn (thinTaskOf lopCountTask.pars lopCountTask.Pre Post) T)
    (hpost : ∀ (x : ThinInstance) r μ', x.ZeroOne →
      Post (toThinU x (x.N ^ 0)) (memOf (x.input [])) (outputEnd x) r μ' →
      A x true fun i => μ' ((x.input []).length + i)) :
    RealizedWithin (thinProb A) (fun x => x.N) (fun x => x.U) (fun x => x.ZeroOne ∧ 1 ≤ x.D)
      (fun x => T x.N x.D x.W.length) := by
  obtain ⟨P, p, Tn, need, hpoly, hsol, hT⟩ := h
  refine realizedN (fun _ => 0) (fun _ => Nat.zero_le _) hpoly hsol ?_ ?_ ?_ ?_ ?_
  · rintro κ x ⟨hZ, hD⟩ hN -
    exact pre_lop hZ hD hN
  · rintro κ x r μ' ⟨hZ, -⟩ - - hp
    exact hpost x r μ' hZ hp
  · intro κ x s k hN
    exact polyBound_three s k κ x hN
  · rintro κ x ⟨hZ, -⟩ - -
    exact zeroOne_le hZ
  · rintro κ x ⟨-, hD⟩ hN -
    exact hT x.N x.D x.W.length x.W.length hN hD le_rfl

/-- **#Lop-AE-SparseTri**: if the task is solved in time T, the problem is solved on the word RAM
within a constant times T. -/
theorem realized_lopCount (T : ℕ → ℕ → ℕ → ℝ) (h : LopSolvedIn lopCountTask T) :
    RealizedWithin lopCount (fun x => x.N) (fun x => x.U) (fun x => x.ZeroOne ∧ 1 ≤ x.D)
      (fun x => T x.N x.D x.W.length) := by
  refine realized_lop (A := lopCount.IsAnswer) (Post := lopCountTask.Post) T h ?_
  rintro x r μ' hZ ⟨hseg, -⟩
  refine ⟨rfl, fun i hi => ?_⟩
  have := out_eq x (U := x.N ^ 0) (μ' := μ') (f := id) (by rw [List.map_id]; exact hseg) i hi
  exact this.trans (Footnote8.zero_one x.X x.Y x.W.toFinset hZ.1 hZ.2 _ _)

/-- **Lop-AE-SparseTri**: if the task is solved in time T, the problem is solved on the word RAM
within a constant times T. -/
theorem realized_lopDetect (T : ℕ → ℕ → ℕ → ℝ) (h : LopSolvedIn lopDetectTask T) :
    RealizedWithin lopDetect (fun x => x.N) (fun x => x.U) (fun x => x.ZeroOne ∧ 1 ≤ x.D)
      (fun x => T x.N x.D x.W.length) := by
  refine realized_lop (A := lopDetect.IsAnswer) (Post := lopDetectTask.Post) T h ?_
  rintro x r μ' hZ ⟨hseg, -⟩
  refine ⟨rfl, fun i hi => ?_⟩
  have := out_eq x (U := x.N ^ 0) (μ' := μ') (f := fun v => if v = 0 then 0 else 1) hseg i hi
  simp only
  rw [this, Footnote8.zero_one x.X x.Y x.W.toFinset hZ.1 hZ.2]
  have hiff := LopInstance.numTriangles_ne_zero_iff x.lop x.W[i].1 x.W[i].2
  constructor
  · intro hin
    rw [if_neg]
    exact_mod_cast hiff.2 hin
  · intro hnot
    rw [if_pos]
    have : ¬ x.lop.numTriangles x.W[i].1 x.W[i].2 ≠ 0 := fun hne => hnot (hiff.1 hne)
    exact_mod_cast not_not.1 this

end Light.Sec3
