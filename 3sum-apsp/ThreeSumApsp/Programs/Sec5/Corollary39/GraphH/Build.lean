/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary39.Tasks

/-!
# Corollary 39 in the light language: what the hosts for k-Clique share

Proof of Corollary 39: "We enumerate the n^t ways of fixing one vertex in each of the first t parts,
and for each of them we build H".  The hosts for weight zero and for minimum and maximum weight do
this in the same way.  `hostSetup_spec` computes N = n^⌊k/3⌋, n^t and the places (`matH`);
`buildH_spec` writes the three matrices of H for one choice of the fixed vertices, by three calls of
`fillH_spec`, and they are an instance of a triangle problem with the graph H (`HoldsH.pre`,
`HoldsH.graphAt_eq`, collected in `Built`); `nextChoice_spec` goes to the next choice.

The paper's bound n^ν on the weights is a free parameter U, and its bound (k choose 2) n^ν on the
weights of H is lenH k * U, where lenH k is the number of pairs of parts.

The local variables that both hosts use are in the namespace `KC`; `hostPairs` lists them with their
values before a round, and `HostLocals` says what the pieces of text of this file read.
-/

@[expose] public section

open ThreeSumApsp.Spec

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.KClique KC

/-! ## Small pieces -/

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The power n^j, as an expression. -/
def powE : ℕ → Expr
  | 0 => k 1
  | j + 1 => powE j *' v Size

/-- The cost of the expression. -/
@[simp] theorem powE_cost (j : ℕ) : (powE j).cost = 2 * j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [powE, ih]; omega

/-- The expression is safe if the powers up to n^j fit in a word, and its value is n^j. -/
theorem powE_safe_val {σ : State} {n : ℕ} (hsize : σ.loc Size = n) (j : ℕ)
    (h : ∀ i ≤ j, ((n ^ i : ℕ) : ℤ) ≤ lim.word) :
    (powE j).Safe lim σ ∧ (powE j).val σ = ((n ^ j : ℕ) : ℤ) := by
  induction j with
  | zero => exact ⟨by simpa [powE] using h 0 le_rfl, by simp [powE]⟩
  | succ j ih =>
    obtain ⟨hs, hv⟩ := ih fun i hi => h i (by omega)
    have hv' : (powE (j + 1)).val σ = ((n ^ (j + 1) : ℕ) : ℤ) := by
      simp only [powE, Expr.val, Op.eval, hv, hsize]
      push_cast
      ring
    refine ⟨⟨hs, trivial, ?_⟩, hv'⟩
    have := h (j + 1) le_rfl
    have hv'' : Op.mul.eval ((powE j).val σ) ((v Size).val σ) = ((n ^ (j + 1) : ℕ) : ℤ) := hv'
    rw [hv'', abs_of_nonneg (by positivity)]
    exact this

/-- Write 0 to the cells base + j, …, base + j + len - 1 (base is local vb). -/
def zeroStmt (vb : ℕ) : ℕ → ℕ → Stmt
  | _, 0 => .skip
  | j, len + 1 => .store (v vb +' k j) (k 0) ;; zeroStmt vb (j + 1) len

/-- `zeroStmt` assigns no local variable. -/
@[simp] theorem zeroStmt_assigns (vb : ℕ) : ∀ j len : ℕ, (zeroStmt vb j len).assigns = []
  | _, 0 => rfl
  | j, len + 1 => by simp [zeroStmt, zeroStmt_assigns vb (j + 1) len]

/-- **zeroStmt** writes 0 to len cells and changes nothing else; 5 steps for each cell. -/
theorem zeroStmt_spec {vb base : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) (len : ℕ) :
    ∀ (j : ℕ) (μ : ℕ → ℤ) (loc : ℕ → ℤ), loc vb = base → base + j + len ≤ lim.space →
      Ends lim P d (zeroStmt vb j len) ⟨loc, μ⟩ (5 * len) fun σ' =>
        σ'.loc = loc ∧ (∀ i < len, σ'.mem (base + j + i) = 0) ∧
          SameOutside μ σ'.mem (base + j) len := by
  induction len with
  | zero =>
    intro j μ loc _ _
    exact Ends.skip ⟨rfl, fun i hi => absurd hi (by omega), SameOutside.refl⟩
  | succ len ih =>
    intro j μ loc eb hB
    unfold zeroStmt
    -- mem[base + j] := 0
    refine Ends.storeThen ?_ (by light_norm [eb, abs_le, Limits.Addr]; omega)
    light_norm [eb, toNat_natCast_add_natCast]
    light_piece (ih (j + 1) _ loc eb (by omega)) with σ' ⟨hl, hz, hf⟩
    refine ⟨hl, fun i hi => ?_, fun b hb => ?_⟩
    · cases i with
      | zero =>
        rw [Nat.add_zero, hf _ (Or.inl (by omega))]
        simp
      | succ i =>
        rw [show base + j + (i + 1) = base + (j + 1) + i by omega]
        exact hz i (by omega)
    · rw [hf b (by omega), Function.update_of_ne (by omega)]

/-! ## The text -/

/-- The number of pairs of parts; the weights of H are at most lenH k times as large as those of the
graph. -/
def lenH (k : ℕ) : ℕ := (pairsH k 0).length + (pairsH k 1).length + (pairsH k 2).length

/-- Build H for the current choice of the fixed vertices: its three weight matrices. -/
def buildH (kk : ℕ) : Stmt :=
  fillMat kk (width kk) (numFixed kk) (numFixed kk + width kk) MatAB (pairsN kk 0) ;;
  fillMat kk (width kk) (numFixed kk + width kk) (numFixed kk + 2 * width kk) MatBC (pairsN kk 1) ;;
  fillMat kk (width kk) (numFixed kk) (numFixed kk + 2 * width kk) MatAC (pairsN kk 2)

/-- What a host does first.  `Choice` holds the free pointer.  The host computes N and n^t, then the
places of the three matrices of H behind the k cells of the chosen vertices and the first cell
behind them, and makes the first choice. -/
def hostSetup (kk : ℕ) : Stmt :=
  .set Side (powE (width kk)) ;;
  .set Rounds (powE (numFixed kk)) ;;
  .set MatAB (v Choice +' k kk) ;;
  .set MatBC (v MatAB +' v Side *' v Side) ;;
  .set MatAC (v MatBC +' v Side *' v Side) ;;
  .set Behind (v MatAC +' v Side *' v Side) ;;
  zeroStmt Choice 0 kk ;;
  .set Round (k 0)

/-- Go to the next choice of the fixed vertices. -/
def nextChoice (kk : ℕ) : Stmt :=
  incStmt Choice Size 0 (numFixed kk) ;;
  .set Round (v Round +' k 1)

/-- `buildH` assigns only `Row`, `Col`, `Place` and `Entry`. -/
@[simp] theorem buildH_assigns (kk : ℕ) {xs : List ℕ} (h : [Row, Col, Place, Entry] ⊆ xs) :
    (buildH kk).assigns ⊆ xs := by
  simp [buildH, h]

/-- `nextChoice` assigns only `Round`. -/
@[simp] theorem nextChoice_assigns (kk : ℕ) : (nextChoice kk).assigns = [Round] := by
  simp [nextChoice]

/-- The time of fillMat for the matrix number i. -/
def fillT (kk N : ℕ) (i : Fin 3) : ℕ := matTime N (width kk) (pairsH kk i).length

/-! ## The layout of the memory, and the locals that hold it -/

/-- The places behind the k cells of the chosen vertices at fr: `matH k n fr i` is the address of
matrix number i of H, for i = 0, 1, 2, and `matH k n fr 3` is the first cell behind the matrices. -/
def matH (k n fr i : ℕ) : ℕ := fr + k + i * (n ^ width k * n ^ width k)

/-- The four places, written out. -/
theorem matH_places (k n fr : ℕ) : matH k n fr 0 = fr + k ∧
    matH k n fr 1 = fr + k + n ^ width k * n ^ width k ∧
    matH k n fr 2 = fr + k + 2 * (n ^ width k * n ^ width k) ∧
    matH k n fr 3 = fr + k + 3 * (n ^ width k * n ^ width k) := by
  unfold matH
  omega

/-- Each of the three matrices lies behind the chosen vertices and before `matH k n fr 3`. -/
theorem matH_bounds (k n fr : ℕ) (i : Fin 3) : fr + k ≤ matH k n fr i ∧
    matH k n fr i + n ^ width k * n ^ width k ≤ matH k n fr 3 := by
  have := Nat.mul_le_mul_right (n ^ width k * n ^ width k) (Nat.le_of_lt_succ i.2)
  unfold matH
  omega

/-- What both hosts hold in the locals `Size` to `Behind` during their loops. -/
structure HostLocals (loc : ℕ → ℤ) (k n U g fr : ℕ) : Prop where
  size : loc Size = n
  bound : loc Bound = U
  weights : loc Weights = g
  side : loc Side = (n ^ width k : ℕ)
  rounds : loc Rounds = (n ^ numFixed k : ℕ)
  choice : loc Choice = fr
  matAB : loc MatAB = matH k n fr 0
  matBC : loc MatBC = matH k n fr 1
  matAC : loc MatAC = matH k n fr 2
  behind : loc Behind = matH k n fr 3

/-- `HostLocals` survives a piece of text that assigns only `Row`, `Col`, `Place` and `Entry`. -/
theorem HostLocals.of_keep {loc loc' : ℕ → ℤ} {k n U g fr : ℕ} (h : HostLocals loc k n U g fr)
    (hkeep : ∀ y ∉ [Row, Col, Place, Entry], loc' y = loc y) : HostLocals loc' k n U g fr where
  size := (hkeep _ (by decide)).trans h.size
  bound := (hkeep _ (by decide)).trans h.bound
  weights := (hkeep _ (by decide)).trans h.weights
  side := (hkeep _ (by decide)).trans h.side
  rounds := (hkeep _ (by decide)).trans h.rounds
  choice := (hkeep _ (by decide)).trans h.choice
  matAB := (hkeep _ (by decide)).trans h.matAB
  matBC := (hkeep _ (by decide)).trans h.matBC
  matAC := (hkeep _ (by decide)).trans h.matAC
  behind := (hkeep _ (by decide)).trans h.behind

/-! ## The three matrices of H in the memory -/

/-- Two instances with the same three matrices are equal. -/
theorem tri_ext {N : ℕ} {T T' : TriangleInstance ℤ N} (h1 : T.wAB = T'.wAB) (h2 : T.wBC = T'.wBC)
    (h3 : T.wAC = T'.wAC) : T = T' := by
  cases T
  cases T'
  simp_all

/-- The weights in the memory are bounded by U. -/
theorem KcInst.Pre.abs_le {k : ℕ} {x : KcInst k} {μ₀ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ₀ fr)
    (p q u v : ℕ) (hp : p < k) (hq : q < k) (hlt : p < q) (hu : u < x.n) (hv : v < x.n) :
    |μ₀ (x.g + widx k x.n p u q v)| ≤ (x.U : ℤ) := by
  have hlt' : (⟨p, hp⟩ : Fin k) < ⟨q, hq⟩ := hlt
  have := hpre.weights ⟨p, hp⟩ ⟨q, hq⟩ ⟨u, hu⟩ ⟨v, hv⟩ hlt'
  simp only at this
  rw [this]
  exact hpre.le _ _ _ _ hlt'

/-- The context of sumPairs from the precondition of the task. -/
theorem fillCtx_of_pre {k : ℕ} {x : KcInst k} {μ₀ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ₀ fr)
    (hw : (lim.space : ℤ) ≤ lim.word) (hB : fr + k ≤ lim.space) : FillCtx lim μ₀ k x.n x.g fr x.U :=
  ⟨hw, by have := hpre.below; omega, hB, hpre.abs_le⟩

/-- Each of the three lists of pairs is a part of all pairs. -/
theorem length_pairsN_le (k : ℕ) (i : Fin 3) : (pairsN k i).length ≤ lenH k := by
  rw [length_pairsN]
  unfold lenH
  fin_cases i <;> simp <;> omega

/-- There is at least one pair of parts. -/
theorem lenH_pos {k : ℕ} (hk : 3 ≤ k) : 1 ≤ lenH k := by
  have hw : 1 ≤ width k := by unfold width; omega
  have : 1 ≤ (pairsH k 0).length := by
    unfold pairsH
    simp only [List.length_append, List.length_flatMap, List.length_map, List.length_finRange,
      List.map_const', List.sum_replicate, smul_eq_mul]
    have : 1 ≤ width k * width k := Nat.mul_pos hw hw
    omega
  unfold lenH
  omega

/-- What building H needs of the limits. -/
structure BuildOk (lim : Limits) (k n U fr : ℕ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  cells : matH k n fr 3 ≤ lim.space
  word : ((lenH k * U + n + 1 : ℕ) : ℤ) ≤ lim.word

/-- The instance of a triangle problem that buildH leaves in the memory: H, with its three matrices
behind the k cells at fr. -/
def triInstOf (k n U fr : ℕ) (μ : ℕ → ℤ) : TriInst :=
  ⟨n ^ width k, lenH k * U, matH k n fr 0, matH k n fr 1, matH k n fr 2,
    readSeg μ (matH k n fr 0) (n ^ width k * n ^ width k),
    readSeg μ (matH k n fr 1) (n ^ width k * n ^ width k),
    readSeg μ (matH k n fr 2) (n ^ width k * n ^ width k)⟩

/-- The graph whose three weight matrices stand in the memory μ behind the k cells at fr. -/
abbrev graphAt (k n U fr : ℕ) (μ : ℕ → ℤ) : TriangleInstance ℤ (n ^ width k) :=
  triOf (n ^ width k) (triInstOf k n U fr μ).AB (triInstOf k n U fr μ).BC (triInstOf k n U fr μ).AC

/-- The graph H of the choice number F of the fixed vertices. -/
abbrev KcInst.H {k : ℕ} (x : KcInst k) (F : Fin (x.n ^ numFixed k)) :
    TriangleInstance ℤ (x.n ^ width k) :=
  graphH x.G (finFunctionFinEquiv.symm F)

/-- The three matrices of H for the choice number F of the fixed vertices stand in the memory μ,
behind the k cells at fr.  μ₀ is a memory that holds the weights. -/
structure HoldsH {k : ℕ} (x : KcInst k) (μ₀ μ : ℕ → ℤ) (fr F : ℕ) : Prop where
  ab : ∀ a < x.n ^ width k, ∀ b < x.n ^ width k, μ (matH k x.n fr 0 + a * x.n ^ width k + b)
    = memSum μ₀ x.g k x.n (vtx k x.n F a b 0) (pairsN k 0)
  bc : ∀ b < x.n ^ width k, ∀ c < x.n ^ width k, μ (matH k x.n fr 1 + b * x.n ^ width k + c)
    = memSum μ₀ x.g k x.n (vtx k x.n F 0 b c) (pairsN k 1)
  ac : ∀ a < x.n ^ width k, ∀ c < x.n ^ width k, μ (matH k x.n fr 2 + a * x.n ^ width k + c)
    = memSum μ₀ x.g k x.n (vtx k x.n F a 0 c) (pairsN k 2)

/-- The three matrices in the memory are the graph H. -/
theorem HoldsH.graphAt_eq {k : ℕ} {x : KcInst k} {μ₀ μ : ℕ → ℤ} {fr F : ℕ} (h : HoldsH x μ₀ μ fr F)
    (hn : 0 < x.n) (hG : WeightsAt μ₀ x.g x.G) (hF : F < x.n ^ numFixed k) :
    graphAt k x.n x.U fr μ = x.H ⟨F, hF⟩ := by
  have hentry (base : ℕ) (a b : Fin (x.n ^ width k)) :
      (readSeg μ base (x.n ^ width k * x.n ^ width k)).getD (a * x.n ^ width k + b) 0 =
        μ (base + a * x.n ^ width k + b) := by
    rw [getD_readSeg (Nat.mul_add_lt_mul a.2 b.2), Nat.add_assoc]
  refine tri_ext (funext₂ fun a b => ?_) (funext₂ fun b c => ?_) (funext₂ fun a c => ?_)
  · exact ((hentry _ a b).trans (h.ab a a.2 b b.2)).trans ((memSum_eq_pairSum hG hn _ _ _ _ _).trans
      (graphH_entries hn x.G ⟨F, hF⟩ a b a).1.symm)
  · exact ((hentry _ b c).trans (h.bc b b.2 c c.2)).trans ((memSum_eq_pairSum hG hn _ _ _ _ _).trans
      (graphH_entries hn x.G ⟨F, hF⟩ b b c).2.1.symm)
  · exact ((hentry _ a c).trans (h.ac a a.2 c c.2)).trans ((memSum_eq_pairSum hG hn _ _ _ _ _).trans
      (graphH_entries hn x.G ⟨F, hF⟩ a a c).2.2.symm)

/-- The entries of a matrix of H are at most lenH k times as large as the weights of the graph. -/
theorem absLe_matrixH {k : ℕ} {x : KcInst k} {μ₀ μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ₀ fr) (base : ℕ)
    (i : Fin 3) (vf : ℕ → ℕ → ℕ → ℕ) (hvf : ∀ a b p, vf a b p < x.n)
    (hval : ∀ a < x.n ^ width k, ∀ b < x.n ^ width k,
      μ (base + a * x.n ^ width k + b) = memSum μ₀ x.g k x.n (vf a b) (pairsN k i)) :
    AbsLe (readSeg μ base (x.n ^ width k * x.n ^ width k)) ((lenH k * x.U : ℕ) : ℤ) := by
  intro e he
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he
  rw [getElem_readSeg]
  obtain ⟨a, ha, b, hb, rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul (by simpa using hj)
  rw [← Nat.add_assoc, hval a ha b hb]
  refine (memSum_abs_le (fun p _ => hvf a b p) hpre.abs_le _ (pairsN_valid k i)).trans ?_
  exact_mod_cast Nat.mul_le_mul_right x.U (length_pairsN_le k i)

/-- The three matrices are an instance for a solver of a triangle problem. -/
theorem HoldsH.pre {k : ℕ} {x : KcInst k} {μ₀ μ : ℕ → ℤ} {fr F : ℕ} (h : HoldsH x μ₀ μ fr F)
    (hk : 3 ≤ k) (hpre : x.Pre μ₀ fr) :
    (triInstOf k x.n x.U fr μ).Pre μ (matH k x.n fr 3) where
  n_pos := Nat.pow_pos hpre.n_pos
  U_pos := Nat.mul_pos (lenH_pos hk) hpre.U_pos
  lenAB := length_readSeg
  lenBC := length_readSeg
  lenAC := length_readSeg
  segAB := seg_readSeg
  segBC := seg_readSeg
  segAC := seg_readSeg
  leAB := absLe_matrixH hpre _ 0 (fun a b => vtx k x.n F a b 0)
    (fun _ _ _ => vtx_lt hpre.n_pos _ _ _ _ _ _) h.ab
  leBC := absLe_matrixH hpre _ 1 (fun b c => vtx k x.n F 0 b c)
    (fun _ _ _ => vtx_lt hpre.n_pos _ _ _ _ _ _) h.bc
  leAC := absLe_matrixH hpre _ 2 (fun a c => vtx k x.n F a 0 c)
    (fun _ _ _ => vtx_lt hpre.n_pos _ _ _ _ _ _) h.ac
  belowAB := (matH_bounds k x.n fr 0).2
  belowBC := (matH_bounds k x.n fr 1).2
  belowAC := (matH_bounds k x.n fr 2).2

/-- **One matrix of H.**  With the row odometer at ro and the column odometer at co, fillMat writes
the sums over the list number i of pairs to the place dst of matrix number i, which local dl holds.
-/
theorem fillH_spec {k : ℕ} (x : KcInst k) {μ₀ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ₀ fr)
    (hb : BuildOk lim k x.n x.U fr) (F : ℕ) (i : Fin 3) {ro co dl dst : ℕ} {vf : ℕ → ℕ → ℕ → ℕ}
    (hro : ro + width k ≤ co) (hco : co + width k ≤ k)
    (hvf : ∀ r c, ∀ p < k, choiceAt (vtx k x.n F 0 0 0) x.n (width k) ro co r c p = vf r c p)
    (hvf0 : ∀ p, vf 0 0 p = vtx k x.n F 0 0 0 p) {loc μ : ℕ → ℤ}
    (hloc : HostLocals loc k x.n x.U x.g fr) (hdl : loc dl = dst) (hK : Kept μ₀ μ fr)
    (hvt : ChoiceIs μ fr k (vtx k x.n F 0 0 0)) (hdst : dst = matH k x.n fr i := by rfl) :
    Ends lim P d (fillMat k (width k) ro co dl (pairsN k i)) ⟨loc, μ⟩ (fillT k (x.n ^ width k) i)
      fun σ' =>
      Kept μ₀ σ'.mem fr ∧ ChoiceIs σ'.mem fr k (vtx k x.n F 0 0 0) ∧
      (∀ r < x.n ^ width k, ∀ c < x.n ^ width k,
        σ'.mem (dst + r * x.n ^ width k + c) = memSum μ₀ x.g k x.n (vf r c) (pairsN k i)) ∧
      SameOutside2 μ σ'.mem dst (x.n ^ width k * x.n ^ width k) fr k := by
  obtain ⟨hw, hcells, hword⟩ := hb
  obtain ⟨hdst, hdstB⟩ : fr + k ≤ dst ∧ dst + x.n ^ width k * x.n ^ width k ≤ matH k x.n fr 3 :=
    hdst ▸ matH_bounds k x.n fr i
  have hn : 0 < x.n := hpre.n_pos
  have hbelow := hpre.below
  have hlen := Nat.mul_le_mul_right x.U (length_pairsN_le k i)
  have hstart : ∀ p < k,
      choiceAt (vtx k x.n F 0 0 0) x.n (width k) ro co 0 0 p = vtx k x.n F 0 0 0 p :=
    fun p hp => (hvf 0 0 p hp).trans (hvf0 p)
  -- The weights are in μ as in μ₀.
  have hweights : Kept μ₀ μ (x.g + k * k * x.n * x.n) := SameOn.mono hK fun a ha => by omega
  have X : MatCtx lim μ
      { kk := k, n := x.n, g := x.g, vt := fr, U := x.U, gw := width k, ro := ro, co := co
        N := x.n ^ width k, dst := dst, vf0 := vtx k x.n F 0 0 0, L := pairsN k i } :=
    { fill := (fillCtx_of_pre hpre hw (by omega)).of_kept hweights
      n_pos := hn
      n_le := show (x.n : ℤ) ≤ lim.word from le_trans (by exact_mod_cast (by omega)) hword
      side := rfl
      row := by change ro + width k ≤ k; omega
      col := hco
      apart := Or.inl hro
      start_lt := fun p _ => vtx_lt hn _ _ _ _ _ _
      pairs := pairsN_valid k i
      sum_le := show (((pairsN k i).length * x.U : ℕ) : ℤ) ≤ lim.word from
        le_trans (by exact_mod_cast (by omega)) hword
      dst_le := hdstB.trans hcells
      weights_dst := by change x.g + k * k * x.n * x.n ≤ dst; omega
      weights_vt := by change x.g + k * k * x.n * x.n ≤ fr; omega
      dst_vt := Or.inl hdst }
  refine (fillMat_spec X
    { size := hloc.size, weights := hloc.weights, side := hloc.side, choice := hloc.choice } hdl
    (hvt.congr fun p hp => (hstart p hp).symm)).mono
    (by rw [fillT, length_pairsN]) ?_
  rintro ⟨loc', μ'⟩ hfilled
  have hrest : SameOutside2 μ μ' dst (x.n ^ width k * x.n ^ width k) fr k := hfilled.rest
  exact ⟨fun a ha => (hrest a ⟨by omega, by omega⟩).trans (hK a ha),
    hfilled.choice.congr hstart,
    fun r hr c hc => (hfilled.written r hr c hc).trans ((memSum_congr hweights
      (choiceAt_lt hn (fun p _ => vtx_lt hn _ _ _ _ _ _) _ _ _ _ _) (pairsN_valid k i)).trans
      (memSum_congr_vf (hvf r c) (pairsN_valid k i))), hrest⟩

/-- **What buildH achieves** for the choice number F of the fixed vertices.  The cells below fr and
the chosen vertices are as before, and the three matrices behind them are an instance of a triangle
problem with the graph H. -/
structure Built {k : ℕ} (x : KcInst k) (μ₀ : ℕ → ℤ) (fr : ℕ) {F : ℕ} (hF : F < x.n ^ numFixed k)
    (μ : ℕ → ℤ) : Prop where
  kept : Kept μ₀ μ fr
  choice : ChoiceIs μ fr k (vtx k x.n F 0 0 0)
  pre : (triInstOf k x.n x.U fr μ).Pre μ (matH k x.n fr 3)
  graph : graphAt k x.n x.U fr μ = x.H ⟨F, hF⟩

/-- **buildH** writes the graph H of the choice number F of the fixed vertices. -/
theorem buildH_spec {k : ℕ} (hk : 3 ≤ k) (x : KcInst k) {μ₀ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ₀ fr)
    (hb : BuildOk lim k x.n x.U fr) {F : ℕ} (hF : F < x.n ^ numFixed k) {loc μ : ℕ → ℤ}
    (hloc : HostLocals loc k x.n x.U x.g fr) (hK : Kept μ₀ μ fr)
    (hvt : ChoiceIs μ fr k (vtx k x.n F 0 0 0)) :
    Ends lim P d (buildH k) ⟨loc, μ⟩
      (fillT k (x.n ^ width k) 0 + fillT k (x.n ^ width k) 1 + fillT k (x.n ^ width k) 2) fun σ' =>
      Built x μ₀ fr hF σ'.mem := by
  have h3w := three_width_add k
  obtain ⟨hAt0, hAt1, hAt2, -⟩ := matH_places k x.n fr
  unfold buildH
  -- the matrix between the groups 0 and 1
  light_piece ((fillH_spec x hpre hb F 0 (by omega) (by omega) (choiceAt_AB k x.n F)
    (fun _ => rfl) hloc hloc.matAB hK hvt).keepingBut [Row, Col, Place, Entry])
    with ⟨loc₁, μ₁⟩ ⟨⟨hK₁, hvt₁, hAB, -⟩, hkeep₁⟩
  have hloc₁ := hloc.of_keep hkeep₁
  -- the matrix between the groups 1 and 2
  light_piece ((fillH_spec x hpre hb F 1 (by omega) (by omega) (choiceAt_BC k x.n F)
    (fun _ => rfl) hloc₁ hloc₁.matBC hK₁ hvt₁).keepingBut [Row, Col, Place, Entry])
    with ⟨loc₂, μ₂⟩ ⟨⟨hK₂, hvt₂, hBC, hf₂⟩, hkeep₂⟩
  have hloc₂ := hloc₁.of_keep hkeep₂
  -- the matrix between the groups 0 and 2
  light_piece (fillH_spec x hpre hb F 2 (by omega) (by omega) (choiceAt_AC k x.n F) (fun _ => rfl)
    hloc₂ hloc₂.matAC hK₂ hvt₂) with ⟨loc₃, μ₃⟩ ⟨hK₃, hvt₃, hAC, hf₃⟩
  -- a later matrix leaves the earlier ones alone
  have H : HoldsH x μ₀ μ₃ fr F :=
    { ab := fun a ha b hb => by
        have := Nat.mul_add_lt_mul ha hb
        exact ((hf₃ _ ⟨by omega, by omega⟩).trans (hf₂ _ ⟨by omega, by omega⟩)).trans
          (hAB a ha b hb)
      bc := fun b hb c hc => by
        have := Nat.mul_add_lt_mul hb hc
        exact (hf₃ _ ⟨by omega, by omega⟩).trans (hBC b hb c hc)
      ac := hAC }
  exact ⟨hK₃, hvt₃, H.pre hk hpre, H.graphAt_eq hpre.n_pos hpre.weights hF⟩

/-! ## The set-up and the next choice -/

/-- **hostSetup** computes the sizes and the places, and chooses vertex 0 in every part. -/
theorem hostSetup_spec {k n fr : ℕ} {loc μ : ℕ → ℤ} (hsize : loc Size = n)
    (hchoice : loc Choice = fr) (hn : 0 < n) (hw : (lim.space : ℤ) ≤ lim.word)
    (hcells : matH k n fr 3 ≤ lim.space) (hword : ((n ^ numFixed k + k : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d (hostSetup k) ⟨loc, μ⟩ (2 * width k + 2 * numFixed k + 5 * k + 28) fun σ' =>
      σ'.loc = updateLocals loc [(Side, (n ^ width k : ℕ)), (Rounds, (n ^ numFixed k : ℕ)),
        (MatAB, matH k n fr 0), (MatBC, matH k n fr 1), (MatAC, matH k n fr 2),
        (Behind, matH k n fr 3), (Round, 0)] ∧
      ChoiceIs σ'.mem fr k (vtx k n 0 0 0 0) ∧ SameOutside μ σ'.mem fr k := by
  obtain ⟨hAt0, hAt1, hAt2, hAt3⟩ := matH_places k n fr
  have hNN : n ^ width k ≤ n ^ width k * n ^ width k := Nat.le_mul_of_pos_left _ (by positivity)
  have hpw : ∀ i ≤ width k, ((n ^ i : ℕ) : ℤ) ≤ lim.word := fun i hi => by
    have : n ^ i ≤ n ^ width k := Nat.pow_le_pow_right hn hi
    exact le_trans (by exact_mod_cast (by omega)) hw
  have hpt : ∀ i ≤ numFixed k, ((n ^ i : ℕ) : ℤ) ≤ lim.word := fun i hi => by
    have : n ^ i ≤ n ^ numFixed k := Nat.pow_le_pow_right hn hi
    exact le_trans (by exact_mod_cast (by omega)) hword
  unfold hostSetup
  -- Side := N = n^⌊k/3⌋; Rounds := n^t
  refine Ends.setValThen (n ^ width k : ℕ) ?_ (powE_safe_val hsize (width k) hpw)
    (by rw [powE_cost]; omega)
  refine Ends.setValThen (n ^ numFixed k : ℕ) ?_
    (powE_safe_val (by simpa using hsize) (numFixed k) hpt) (by simp only [powE_cost]; omega)
  simp only [powE_cost]
  generalize n ^ width k = N at *
  -- MatAB, MatBC, MatAC, Behind := the places of the three matrices and the cell behind them
  refine Ends.setValThen (matH k n fr 0 : ℕ) ?_ (by light_side [hchoice])
  refine Ends.setValThen (matH k n fr 1 : ℕ) ?_ (by light_side)
  refine Ends.setValThen (matH k n fr 2 : ℕ) ?_ (by light_side)
  refine Ends.setValThen (matH k n fr 3 : ℕ) ?_ (by light_side)
  -- vertex 0 in every part; Round := 0
  light_piece (zeroStmt_spec (base := fr) hw k 0 μ _ (by simp [hchoice]) (by omega))
    with ⟨_, μ'⟩ ⟨rfl, hzero, hout⟩
  exact Ends.setVal 0 ⟨rfl, fun p hp => by simpa [vtx] using hzero p hp, by simpa using hout⟩
    (by simp; omega)

/-- **nextChoice** turns the choice number F of the fixed vertices into the choice number F + 1. -/
theorem nextChoice_spec {k n fr F : ℕ} {loc μ : ℕ → ℤ} (hsize : loc Size = n)
    (hchoice : loc Choice = fr) (hround : loc Round = F) (hn : 0 < n)
    (hlim : OdometerOk lim n fr k) (hF : ((F + 1 : ℕ) : ℤ) ≤ lim.word)
    (hvt : ChoiceIs μ fr k (vtx k n F 0 0 0)) :
    Ends lim P d (nextChoice k) ⟨loc, μ⟩ (14 * numFixed k + 9) fun σ' =>
      σ'.loc = Function.update loc Round ((F + 1 : ℕ) : ℤ) ∧
      ChoiceIs σ'.mem fr k (vtx k n (F + 1) 0 0 0) ∧ SameOutside μ σ'.mem fr (numFixed k) := by
  have h3w := three_width_add k
  unfold nextChoice
  refine Ends.next _
    ((inc_spec (vf := fun _ => 0) (c := F) hlim hn (by omega) hsize hchoice
      (hvt.congr fun p hp => (withDigits_fixed k n F p hp).symm)).mono le_rfl ?_)
  rintro ⟨loc', μ'⟩ ⟨hl, hvt', hout⟩
  obtain rfl : loc = loc' := hl.symm
  exact Ends.setVal _ ⟨rfl, hvt'.congr (withDigits_fixed k n (F + 1)), by simpa using hout⟩
    (by light_side [hround])

/-- The locals that both hosts use in the same way, with their values before the round for the
choice number F of the fixed vertices. -/
@[simp] abbrev hostPairs (k n U g fr F : ℕ) : List (ℕ × ℤ) :=
  [(Size, n), (Bound, U), (Weights, g), (Side, (n ^ width k : ℕ)), (Rounds, (n ^ numFixed k : ℕ)),
    (Choice, fr), (MatAB, matH k n fr 0), (MatBC, matH k n fr 1), (MatAC, matH k n fr 2),
    (Behind, matH k n fr 3), (Round, F)]

end Light.Sec5
