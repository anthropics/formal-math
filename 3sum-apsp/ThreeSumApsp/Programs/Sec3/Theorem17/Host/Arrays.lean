/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need
public import ThreeSumApsp.Spec.Sec3.Theorem17.ClassStarts

/-!
# The host of Theorem 17: the arrays and the loop

The third part of the host procedure `et17` (Exact Triangle by Theorem 17) fills the table of
doubles and the three lists of residues (`resid_then`), sorts the pairs into classes and cuts the
classes into chunks (`classes_then`), and calls the loop over the instances.

`et17Tables_spec` is the specification of the whole part: within `hostRunTime` steps, local 0 holds
the bit `found m` of the loop over the instances, and the cells below the free pointer are
unchanged.  Three lemmas connect the calls to the loop: `ready_of` (a run of et17 provides what this
part needs), `hostMem_of` (the arrays that the loop reads are in the memory) and `hostLay_of` (they
lie where the loop expects them).
-/

@[expose] public section

open ThreeSumApsp.Spec

namespace Light.Sec3

open ThreeSumApsp

namespace Et17

/-- A call that puts its result into the local Small. -/
theorem setLocal_res (x : TriInst) (X : HostData) (fr : ℕ) (g s nch res r : ℤ) :
    setLocal (locals x X fr g s nch res) Small r = locals x X fr g s nch r := rfl

/-- What the third part needs, for the data X of the loop: the limits, the prime, and the three
matrices below the free pointer. -/
structure Ready (lim : Limits) (d : ℕ) (x : TriInst) (X : HostData) (μ : ℕ → ℤ) (fr : ℕ) :
    Prop where
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + 2 ≤ lim.depth
  prime : 1 ≤ X.p
  word : ((X.p * 2 ^ (bitLen x.U + 1) : ℕ) : ℤ) ≤ lim.word
  top : aFr X x.U fr < lim.space
  segAB : Seg μ x.ab X.AB
  segBC : Seg μ x.bc X.BC
  segAC : Seg μ x.ac X.AC
  lenAB : X.AB.length = X.n * X.n
  lenBC : X.BC.length = X.n * X.n
  lenAC : X.AC.length = X.n * X.n
  leAB : AbsLe X.AB x.U
  leBC : AbsLe X.BC x.U
  leAC : AbsLe X.AC x.U
  belowAB : x.ab + X.n * X.n ≤ fr
  belowBC : x.bc + X.n * X.n ≤ fr
  belowAC : x.ac + X.n * X.n ≤ fr

variable {lim : Limits} {P : Program} {d : ℕ} {x : TriInst} {X : HostData} {μ : ℕ → ℤ} {fr : ℕ}

/-- The places of the lists of residues: they stand one after the other behind the table of doubles,
and end where the array of the classes begins, below the free pointer of the solver. -/
private theorem resid_places (X : HostData) (U fr : ℕ) :
    aRab X U fr = fr + (bitLen U + 1) ∧ aRbc X U fr = aRab X U fr + X.n * X.n ∧
      aRac X U fr = aRbc X U fr + X.n * X.n ∧ aCls X U fr = aRac X U fr + X.n * X.n ∧
      aCls X U fr ≤ aFr X U fr := by
  have := host_places X U fr
  omega

/-- The places of the arrays of the classes and the chunks: they stand one after the other behind
the lists of residues, and end at aX, the first matrix of the instance that is handed to the solver,
below the free pointer of the solver. -/
private theorem class_places (X : HostData) (U fr : ℕ) :
    aRbc X U fr = aRab X U fr + X.n * X.n ∧ aRac X U fr = aRbc X U fr + X.n * X.n ∧
      aCls X U fr = aRac X U fr + X.n * X.n ∧ aCur X U fr = aCls X U fr + (X.p + 1) ∧
      aQi X U fr = aCur X U fr + X.p ∧ aQj X U fr = aQi X U fr + X.n * X.n ∧
      aCr X U fr = aQj X U fr + X.n * X.n ∧ aCl X U fr = aCr X U fr + (X.n * X.n + X.p) ∧
      aCw X U fr = aCl X U fr + (X.n * X.n + X.p) ∧ aX X U fr = aCw X U fr + (X.n * X.n + X.p) ∧
      aX X U fr ≤ aFr X U fr := by
  have := host_places X U fr
  omega

/-- The memory after the first four calls: the three lists of residues; only cells between the free
pointer and the array of the classes have changed. -/
structure ResidMem (x : TriInst) (X : HostData) (fr : ℕ) (μ μ' : ℕ → ℤ) : Prop where
  rab : SegN μ' (aRab X x.U fr) X.RAB
  rbc : SegN μ' (aRbc X x.U fr) X.RBC
  rac : SegN μ' (aRac X x.U fr) X.RAC
  same : SameOn (fun c => c < fr ∨ aCls X x.U fr ≤ c) μ μ'

/-- The memory after the next two calls: the pairs, class after class, and the table of the chunks;
only cells between the array of the classes and aX, the first matrix of the instance that is handed
to the solver, have changed. -/
structure ClassMem (x : TriInst) (X : HostData) (fr : ℕ) (μ μ' : ℕ → ℤ) : Prop where
  qi : SegN μ' (aQi X x.U fr) X.QI
  qj : SegN μ' (aQj X x.U fr) X.QJ
  cr : SegN μ' (aCr X x.U fr) (X.CT.map fun c => c.residue)
  cl : SegN μ' (aCl X x.U fr) (X.CT.map fun c => c.start)
  cw : SegN μ' (aCw X x.U fr) (X.CT.map fun c => c.len)
  same : SameOn (fun c => c < aCls X x.U fr ∨ aX X x.U fr ≤ c) μ μ'

/-- What residues needs, for a matrix below the free pointer and a destination between the table of
doubles and the end of the arrays. -/
theorem Ready.residuesPre (h : Ready lim d x X μ fr) {μ' : ℕ → ℤ} {src dst : ℕ} {l : List ℤ}
    (hdbl : Seg μ' fr (dblList X.p (bitLen x.U))) (hsrc : Seg μ' src l)
    (hlen : l.length = X.n * X.n) (hle : AbsLe l x.U) (hbelow : src + X.n * X.n ≤ fr)
    (hlow : fr + (bitLen x.U + 1) ≤ dst := by omega)
    (hhigh : dst + X.n * X.n < lim.space := by omega) :
    ResiduesPre lim μ' src dst (X.n * X.n) fr X.p (bitLen x.U) x.U l :=
  { hw := h.space
    prime := h.prime
    segDbl := hdbl
    segSrc := hsrc
    length := hlen
    le := hle
    lt := Nat.lt_size_self _
    spaceDbl := by omega
    spaceSrc := by omega
    spaceDst := by omega
    count := by omega
    apartSrc := by omega
    apartDbl := by omega
    word := h.word }

/-- **The table of doubles and the three lists of residues**, followed by the rest t of the text. -/
theorem resid_then {pDbl pResid pResidues : ℕ} (hDbl : P[pDbl]? = some dblTableBody)
    (hResid : P[pResid]? = some residBody) (hResidues : P[pResidues]? = some (residuesBody pResid))
    (hr : Ready lim d x X μ fr) {g s : ℤ} {t : Stmt} {T : ℕ} {Q : State → Prop}
    (h : ∀ res μ', ResidMem x X fr μ μ' → Ends lim P d t ⟨frame (locals x X fr g s 0 res), μ'⟩
      (T - (tDblTable (bitLen x.U) + 3 * tResidues (X.n * X.n) (bitLen x.U) + 26)) Q)
    (hT : tDblTable (bitLen x.U) + 3 * tResidues (X.n * X.n) (bitLen x.U) + 26 ≤ T) :
    Ends lim P d
      (.call pDbl [v Free, v ThePrime, v Bits] Small ;;
        .call pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] Small ;;
        .call pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] Small ;;
        .call pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] Small ;; t)
      ⟨frame (locals x X fr g s 0 0), μ⟩ T Q := by
  have hdepth := hr.depth
  have htop := hr.top
  have hplaces := resid_places X x.U fr
  have lenAB := hr.lenAB
  have lenBC := hr.lenBC
  have lenAC := hr.lenAC
  have hAB := hr.belowAB
  have hBC := hr.belowBC
  have hAC := hr.belowAC
  have hword : ((X.p * 2 ^ bitLen x.U : ℕ) : ℤ) ≤ lim.word := le_trans (by
    exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)))
    hr.word
  have lenDbl : (dblList X.p (bitLen x.U)).length = bitLen x.U + 1 := by simp [dblList]
  have lenRAB : X.RAB.length = X.n * X.n := (length_residList _ _).trans hr.lenAB
  have lenRBC : X.RBC.length = X.n * X.n := (length_residList _ _).trans hr.lenBC
  -- Small := pDbl(Free, ThePrime, Bits)
  light_call (dblTable_meets (dst := fr) (p := X.p) (len := bitLen x.U) hDbl hr.space
    (by omega) hword) with r₁ μ₁ ⟨hdbl, same₁⟩
  rw [setLocal_res]
  -- Small := pResidues(AdrAB, ResAB, SizeSq, Free, Bits)
  light_call (residues_meets hResidues hResid (by omega) (hr.residuesPre
    (dst := aRab X x.U fr) hdbl hr.segAB.keep hr.lenAB hr.leAB hr.belowAB)) with r₂ μ₂ ⟨hrab, same₂⟩
  rw [setLocal_res]
  -- Small := pResidues(AdrBC, ResBC, SizeSq, Free, Bits)
  light_call (residues_meets hResidues hResid (by omega) (hr.residuesPre
    (dst := aRbc X x.U fr) hdbl.keep hr.segBC.keep hr.lenBC hr.leBC hr.belowBC))
    with r₃ μ₃ ⟨hrbc, same₃⟩
  rw [setLocal_res]
  -- Small := pResidues(AdrAC, ResAC, SizeSq, Free, Bits)
  light_call (residues_meets hResidues hResid (by omega) (hr.residuesPre
    (dst := aRac X x.U fr) hdbl.keep hr.segAC.keep hr.lenAC hr.leAC hr.belowAC))
    with r₄ μ₄ ⟨hrac, same₄⟩
  rw [setLocal_res]
  exact (h r₄ μ₄ ⟨hrab.keep, hrbc.keep, hrac, by light_keep⟩).mono (by simp; omega) fun _ hQ => hQ

/-- There are at most n² + p chunks. -/
theorem Ready.chunkCount_le (hr : Ready lim d x X μ fr) (hcap : 1 ≤ X.cap) :
    X.chunkCount ≤ X.n * X.n + X.p :=
  length_chunkTab_le_add hcap fun i hi => lt_of_mem_residList hr.prime (by
    rw [List.getD_eq_getElem _ _ (by rw [HostData.RAB, length_residList, hr.lenAB]; exact hi)]
    exact List.getElem_mem _)

/-- **The classes and the chunks**, followed by the rest t of the text. -/
theorem classes_then {pClasses pChunks : ℕ} (hClasses : P[pClasses]? = some classesBody)
    (hChunks : P[pChunks]? = some chunksBody) (hr : Ready lim d x X μ fr) (hcap : 1 ≤ X.cap)
    {μ₁ : ℕ → ℤ} (hrab : SegN μ₁ (aRab X x.U fr) X.RAB) {g s res : ℤ} {t : Stmt} {T : ℕ}
    {Q : State → Prop}
    (h : ∀ res' μ', ClassMem x X fr μ₁ μ' → Ends lim P d t
      ⟨frame (locals x X fr g s X.chunkCount res'), μ'⟩
      (T - (tClasses X.n X.p + tChunks X.p X.chunkCount + 17)) Q)
    (hT : tClasses X.n X.p + tChunks X.p X.chunkCount + 17 ≤ T) :
    Ends lim P d
      (.call pClasses [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols] Small ;;
        .call pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW] NumChunks ;; t)
      ⟨frame (locals x X fr g s 0 res), μ₁⟩ T Q := by
  have hchunks : X.chunkCount = (chunkTabOf X.p X.cap (classStarts X.n X.p X.RAB)).length := rfl
  rw [hchunks] at h hT
  have hdepth := hr.depth
  have hp := hr.prime
  have htop := hr.top
  have hplaces := class_places X x.U fr
  have lenRAB : X.RAB.length = X.n * X.n := (length_residList _ _).trans hr.lenAB
  have ltRAB : ∀ r ∈ X.RAB, r < X.p := fun r hmem => lt_of_mem_residList (by omega) hmem
  have hroom : (chunkTabOf X.p X.cap (classStarts X.n X.p X.RAB)).length ≤ X.n * X.n + X.p :=
    hr.chunkCount_le hcap
  -- Small := pClasses(ResAB, Size, ThePrime, Cls, Cur, Rows, Cols)
  refine Ends.callToThen (classes_meets hClasses hr.space
    { rab := aRab X x.U fr, n := X.n, p := X.p, cls := aCls X x.U fr, cur := aCur X x.U fr,
      qi := aQi X x.U fr, qj := aQj X x.U fr, RAB := X.RAB } μ₁
    { seg := hrab, len := lenRAB, lt := ltRAB }) ?_ (by simp)
  rintro r₁ μ₂ ⟨hcls, hqi, hqj, same₂⟩
  dsimp only at hcls hqi hqj same₂
  rw [setLocal_res]
  -- NumChunks := pChunks(Cls, ThePrime, Cap, TabR, TabL, TabW)
  refine Ends.callToThen (chunks_meets hChunks hr.space
    { cls := aCls X x.U fr, p := X.p, cap := X.cap, cr := aCr X x.U fr, cl := aCl X x.U fr,
      cw := aCw X x.U fr, R := X.n * X.n + X.p, B := X.n * X.n, C := classStarts X.n X.p X.RAB } μ₂
    { seg := hcls, len := length_classStarts X.n X.p X.RAB,
      le := fun y hy => le_of_mem_classStarts hy, room := hroom }) ?_ (by simp)
    (hT := by simp only [ChunksArgs.table]; light_time)
  rintro _ μ₃ ⟨rfl, hcr, hcl, hcw, same₃⟩
  simp only [ChunksArgs.table, ChunksArgs.Same] at hcr hcl hcw same₃ ⊢
  have hsorted : (sortedIdx X.n X.p X.RAB).length ≤ X.n * X.n := by
    rw [length_sortedIdx_eq]
    exact classStart_le_sq X.n X.RAB X.p
  have keep : ∀ {a : ℕ} {l : List ℕ}, SegN μ₂ a l → a + l.length ≤ aCr X x.U fr → SegN μ₃ a l := by
    intro a l hs hle
    refine Seg.congr hs fun i hi => same₃ _ ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_⟩ <;>
      (simp only [List.length_map] at hi; omega)
  refine (h r₁ μ₃ ⟨keep hqi (by simp only [HostData.QI, queryRows, List.length_map]; omega),
    keep hqj (by simp only [HostData.QJ, queryCols, List.length_map]; omega), hcr, hcl, hcw,
    fun c hc => ?_⟩).mono (by simp; omega) fun _ hQ => hQ
  exact (same₃ c ⟨by omega, by omega, by omega⟩).trans (same₂ c (by simp only [Outside]; omega))

/-- Where the arrays lie, for the addresses of et17. -/
theorem hostLay_of (hr : Ready lim d x X μ fr) (hchunks : X.chunkCount ≤ X.n * X.n + X.p) :
    HostLay X (hostAddr x X fr) := by
  light_facts hr
  have hplaces := host_places X x.U fr
  have hcomm : X.D * X.n = X.n * X.D := Nat.mul_comm _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun t ht => ?_⟩
  case refine_13 =>
    have := X.w_le_cap ht
    simp only [hostAddr]
    omega
  all_goals
    simp only [hostAddr]
    omega

/-- The arrays that the loop over the instances reads are in the memory. -/
theorem hostMem_of (hr : Ready lim d x X μ fr) {μ₁ μ₂ : ℕ → ℤ}
    (hresid : ResidMem x X fr μ μ₁) (hclass : ClassMem x X fr μ₁ μ₂) :
    HostMem X (hostAddr x X fr) μ₂ := by
  light_facts hr hresid hclass
  have hplaces := resid_places X x.U fr
  have lenRAC : X.RAC.length = X.n * X.n := (length_residList _ _).trans hr.lenAC
  have lenRBC : X.RBC.length = X.n * X.n := (length_residList _ _).trans hr.lenBC
  exact
    { segAB := hr.segAB.keep
      segBC := hr.segBC.keep
      segAC := hr.segAC.keep
      segRAC := hresid.rac.keep
      segRBC := hresid.rbc.keep
      segQI := hclass.qi
      segQJ := hclass.qj
      segCR := hclass.cr
      segCL := hclass.cl
      segCW := hclass.cw }

/-- What the third part needs holds for the data of a run of et17. -/
theorem ready_of {need : List ℕ → Need} {D g a b : ℕ} (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ready lim d x (hostData x D g) μ fr := by
  have hD16 := hbig.sixteen_le
  have hcells := hok.cells
  have hdepth := hok.depth
  have htop := aFr_le (x := x) (g := g) hD16 fr
  have hp := two_le_hostData_p x g hD16
  have hps := Nat.mul_le_mul_right (2 ^ (bitLen x.U + 1)) (hostData_p_le x g hD16)
  simp only [hostNeedAt] at hcells hdepth
  exact
    { space := hok.space
      depth := by omega
      prime := by omega
      word := le_word_of_le_hostWord hok
      top := by omega
      segAB := hpre.segAB
      segBC := hpre.segBC
      segAC := hpre.segAC
      lenAB := hpre.lenAB
      lenBC := hpre.lenBC
      lenAC := hpre.lenAC
      leAB := hpre.leAB
      leBC := hpre.leBC
      leAC := hpre.leAC
      belowAB := hpre.belowAB
      belowBC := hpre.belowBC
      belowAC := hpre.belowAC }

end Et17

open Et17 in
/-- **The third part of et17**: the result of the loop over the instances; only cells from the free
pointer on change. -/
theorem et17Tables_spec {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    {lim : Limits} {d : ℕ} (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Tables ν) ⟨frame (et17LocB x fr D g), μ⟩
      (hostRunTime Tn (hostData x D g) x.U)
      fun σ' => σ'.loc 0 = bit ((hostData x D g).found (hostData x D g).m) ∧ Kept μ σ'.mem fr := by
  have hr := ready_of hpre hbig hok
  have hlim := hostLim_of_ok hbig hok
  have hv := hostData_valid hpre hbig
  unfold et17LocB
  generalize hostData x D g = X at hr hlim hv ⊢
  have hdepth := hr.depth
  have hfr : fr ≤ aX X x.U fr := by
    have := host_places X x.U fr
    omega
  unfold et17Tables hostRunTime
  -- the table of doubles and the residues; the classes and the chunks
  refine resid_then C.hDbl C.hResid C.hResidues hr (fun r₁ μ₁ hresid => ?_) (by omega)
  refine classes_then C.hClasses C.hChunks hr hv.cap_pos hresid.rab
    (fun r₂ μ₂ hclass => ?_) (by omega)
  -- NumInst := NumPieces * NumChunks
  have hcount := hlim.count
  have hm : (X.m : ℤ) = (X.h : ℤ) * X.chunkCount := by
    rw [HostData.m]
    push_cast
    rfl
  have hpos : (0 : ℤ) ≤ (X.h : ℤ) * X.chunkCount := by positivity
  light_set (X.m : ℕ) using hm
  -- the result is pLoop(…)
  light_call (Meets.of_body (Q := fun r μ' => r = bit (X.found X.m) ∧
      Kept μ₂ μ' (hostAddr x X fr).x) C.hLoop
    (hostLoop_spec C.loop ⟨hv, hr.leAB, hr.leBC, hr.leAC⟩ (hostMem_of hr hresid hclass)
      (hostLay_of hr (hr.chunkCount_le hv.cap_pos)) hlim)) using hostLoopArgs, hostAddr
    with r μ₃ ⟨rfl, hkept⟩
  refine ⟨rfl, fun c hc => ?_⟩
  have hcls : fr ≤ aCls X x.U fr := by
    have := host_places X x.U fr
    omega
  exact (hkept c (lt_of_lt_of_le hc hfr)).trans ((hclass.same c (Or.inl (by omega))).trans
    (hresid.same c (Or.inl hc)))

end Light.Sec3
