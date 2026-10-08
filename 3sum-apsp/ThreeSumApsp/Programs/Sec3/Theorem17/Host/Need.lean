/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.InstanceCount
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Text

/-!
# The host of Theorem 17: the limits

The host procedure `et17` (Exact Triangle by Theorem 17) states what it needs of the limits of a
run: word size, memory, depth of calls (`hostNeedAt`).  This file shows that this need covers what
the procedures that it calls ask for.

* The arrays of the host lie one behind the other and fit into the cells that `hostLayout` counts
  (`aFr_le`).
* Every number that is at most `hostWord` fits in a word (`le_word_of_le_hostWord`).
* So the preconditions of the choice of the prime and of the loop over the instances hold
  (`choosePre_of_ok`, `hostLim_of_ok`).  For the solver this uses that an instance has at most
  `⌊n²/√D⌋` query pairs (`HostData.w_le_cap`, `need_le_supNeed`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The case that n is not small -/

/-- The host falls back on the brute force exactly if the hypotheses of Theorem 17 fail. -/
theorem not_smallCase_iff {n D g : ℕ} : ¬ SmallCase n D g ↔ BigCase n D g := by
  unfold SmallCase
  exact ⟨fun h => ⟨by omega, by omega, by omega, by omega⟩,
    fun ⟨_, _, _, _⟩ => by omega⟩

/-- The chosen prime is at most √D. -/
theorem hostData_p_le (x : TriInst) {D : ℕ} (g : ℕ) (hD : 16 ≤ D) :
    (hostData x D g).p ≤ Nat.sqrt D :=
  chosenPrime_le_sqrt x.AB x.BC x.AC hD

/-- The chosen prime is at least 2. -/
theorem two_le_hostData_p (x : TriInst) {D : ℕ} (g : ℕ) (hD : 16 ≤ D) : 2 ≤ (hostData x D g).p :=
  two_le_chosenPrime x.AB x.BC x.AC hD

/-- There are at most `4ng` instances. -/
theorem hostData_m_le {x : TriInst} {D g : ℕ} (h : BigCase x.n D g) :
    (hostData x D g).m ≤ 4 * x.n * g :=
  HostData.m_le h (chosenPrime_mem x.AB x.BC x.AC h.sixteen_le)

/-- The data of a run are valid. -/
theorem hostData_valid {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) : (hostData x D g).Valid :=
  HostData.valid_of_params h (chosenPrime_mem x.AB x.BC x.AC h.sixteen_le) hpre.lenAB hpre.lenBC
    hpre.lenAC

/-! ## The addresses -/

/-- The free pointer of the solver, written out. -/
private theorem aFr_eq (X : HostData) (U fr : ℕ) :
    aFr X U fr = fr + (bitLen U + 1) + 3 * (X.n * X.n) + (X.p + 1) + X.p + 2 * (X.n * X.n)
      + 3 * (X.n * X.n + X.p) + 2 * (X.n * X.D) + X.cap := by
  simp only [aFr, aOut, aY, aX, aCw, aCl, aCr, aQj, aQi, aCur, aCls, aRac, aRbc, aRab]
  omega

/-- The arrays of et17 fit into the cells that hostLayout counts. -/
theorem aFr_le {x : TriInst} {D g : ℕ} (hD : 16 ≤ D) (fr : ℕ) :
    aFr (hostData x D g) x.U fr ≤ fr + hostLayout x.n x.U D := by
  have hp := hostData_p_le x g hD
  rw [aFr_eq]
  unfold hostLayout
  change fr + (bitLen x.U + 1) + 3 * (x.n * x.n) + ((hostData x D g).p + 1) + (hostData x D g).p
    + 2 * (x.n * x.n) + 3 * (x.n * x.n + (hostData x D g).p) + 2 * (x.n * D) + queryCapNat x.n D ≤ _
  omega

/-! ## The words -/

/-- The numbers of the host fit in a word. -/
private theorem hostWord_le {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {n U fr D g : ℕ}
    (hok : (hostNeedAt a b need n U D g).Ok lim fr d) :
    ((hostWord a b n U D g : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast Nat.le_add_right _ _) hok.word

/-- A number that is at most hostWord fits in a word. -/
theorem le_word_of_le_hostWord {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {n U fr D g : ℕ}
    (hok : (hostNeedAt a b need n U D g).Ok lim fr d) {z : ℕ}
    (hz : z ≤ hostWord a b n U D g := by unfold hostWord; omega) : ((z : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast hz) (hostWord_le hok)

/-- What choosePrime needs. -/
theorem choosePre_of_ok {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {x : TriInst} {μ : ℕ → ℤ}
    {fr D g : ℕ} (hpre : x.Pre μ fr) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    ChoosePrimePre lim (d + 1) μ x D fr := by
  have hcells : fr + (chooseCells x.n x.U D + hostLayout x.n x.U D
      + (supNeed need x.n D (queryCapNat x.n D)).cells + 2) ≤ lim.space := hok.cells
  have hdepth : d + (2 * Nat.clog 2 x.n + 8 + (supNeed need x.n D (queryCapNat x.n D)).depth)
      ≤ lim.depth := hok.depth
  exact
    { space_le := hok.space
      inst := hpre
      cells := by omega
      wordD := le_word_of_le_hostWord hok
      wordU := le_word_of_le_hostWord hok
      wordN := le_word_of_le_hostWord hok
      wordDbl := le_word_of_le_hostWord hok
      wordStr := le_word_of_le_hostWord hok
      wordSum := le_word_of_le_hostWord hok
      depth := by omega }

/-- The need of the solver on an instance with at most cap query pairs is at most supNeed. -/
private theorem need_le_supNeed (need : List ℕ → Need) (n D : ℕ) {cap w : ℕ} (hw : w ≤ cap) :
    (need [n, D, w]).word ≤ (supNeed need n D cap).word ∧
      (need [n, D, w]).cells ≤ (supNeed need n D cap).cells ∧
      (need [n, D, w]).depth ≤ (supNeed need n D cap).depth := by
  have hm : w ∈ Finset.range (cap + 1) := Finset.mem_range.2 (by omega)
  exact ⟨Finset.le_sup (f := fun v => (need [n, D, v]).word) hm,
    Finset.le_sup (f := fun v => (need [n, D, v]).cells) hm,
    Finset.le_sup (f := fun v => (need [n, D, v]).depth) hm⟩

/-- What hostLoop asks of the limits. -/
theorem hostLim_of_ok {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {x : TriInst}
    {fr D g : ℕ} (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    HostLim lim (d + 1) (hostData x D g) x.U (hostAddr x (hostData x D g) fr) need := by
  have hD : 16 ≤ D := hbig.sixteen_le
  have hcells : fr + (chooseCells x.n x.U D + hostLayout x.n x.U D
      + (supNeed need x.n D (queryCapNat x.n D)).cells + 2) ≤ lim.space := hok.cells
  have hdepth : d + (2 * Nat.clog 2 x.n + 8 + (supNeed need x.n D (queryCapNat x.n D)).depth)
      ≤ lim.depth := hok.depth
  have hword : ((hostWord a b x.n x.U D g + (supNeed need x.n D (queryCapNat x.n D)).word : ℕ) : ℤ)
      ≤ lim.word := hok.word
  have hfr := aFr_le (x := x) (g := g) hD fr
  have hp := hostData_p_le x g hD
  have hm := hostData_m_le hbig
  have hlay : 2 * Nat.sqrt D ≤ hostLayout x.n x.U D := by unfold hostLayout; omega
  exact
    { space := hok.space
      fr := by change aFr (hostData x D g) x.U fr < lim.space; omega
      prime := by omega
      count := le_word_of_le_hostWord hok (hm.trans (by unfold hostWord; omega))
      step := le_word_of_le_hostWord hok (by
        change x.n + pieceSizeNat D g ≤ _
        unfold hostWord
        omega)
      weights := le_word_of_le_hostWord hok
      depth := by omega
      solver := fun t ht => by
        have hwc : (hostData x D g).w t ≤ queryCapNat x.n D := (hostData x D g).w_le_cap ht
        obtain ⟨hsword, hscells, hsdepth⟩ := need_le_supNeed need x.n D hwc
        change (need [x.n, D, (hostData x D g).w t]).Ok lim (aFr (hostData x D g) x.U fr)
          (d + 1 + 1)
        exact ⟨le_trans (Nat.cast_le.2 (hsword.trans (Nat.le_add_left _ _))) hword, by omega,
          hok.space, by omega⟩ }

end Light.Sec3
