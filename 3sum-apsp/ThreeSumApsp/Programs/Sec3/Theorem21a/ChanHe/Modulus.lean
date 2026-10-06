/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeMemory

/-!
# The reduction from 3SUM to Convolution-3SUM: the modulus of a node

For Theorem 21(a).  The modulus of a node of the recursion tree of
[CH20, Theorem 5.1] is the product of two primes up to m: p₁ is the least prime q such that the
three sets have few colliding pairs modulo q (`firstP`), and p₂ the least prime q such that few of
these pairs still collide modulo p₁ q (`secondP`).

* search(mult, s₁, l₁, s₂, l₂, s₃, l₃, b₁, b₂, b₃, np, pr, cnt, fr) runs through the primes q in
  ascending order and returns the first one for which each of the three sets has at most bᵢ / np
  colliding pairs modulo mult · q (`Good`), and 1 if there is none (`search_spec`).  It always runs
  through all candidates.  A round (`searchRound_ends`) makes three tests (`check_ends`,
  `searchChecks_ends`) and records the candidate; that the first good element of the sorted list is
  the least good element of the set is `pick_filter`.
* modulus calls search twice, as in the definitions of the two primes, with three calls of coll in
  between, and returns the product; if there is no prime at all it returns 1 (`modulus_spec`).
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset

variable {lim : Limits} {P : Program}

namespace FirstGood

/-! ## The least good element of a set is the first good element of its sorted list -/

/-- The first good element of a list, and 0 if there is none. -/
def hit (good : ℕ → Prop) [DecidablePred good] (l : List ℕ) : ℕ :=
  (l.find? fun q => decide (good q)).getD 0

variable {good : ℕ → Prop} [DecidablePred good]

/-- One more candidate: it counts if it is good and no earlier one was. -/
theorem hit_snoc {l : List ℕ} (hl : ∀ x ∈ l, x ≠ 0) (q : ℕ) :
    hit good (l ++ [q]) = if hit good l = 0 then (if good q then q else 0) else hit good l := by
  unfold hit
  rw [List.find?_append]
  cases h : l.find? fun q => decide (good q) with
  | none =>
    by_cases hq : good q <;> simp [hq]
  | some x =>
    have hx : x ≠ 0 := hl x (List.mem_of_find?_eq_some h)
    simp [hx]

/-- The first good element among the first t + 1 elements of a list. -/
theorem hit_take_succ {l : List ℕ} (hl : ∀ x ∈ l, x ≠ 0) {t : ℕ} (ht : t < l.length) :
    hit good (l.take (t + 1)) = if hit good (l.take t) = 0 then (if good l[t] then l[t] else 0)
      else hit good (l.take t) := by
  rw [List.take_succ_eq_append_getElem ht, hit_snoc fun x hx => hl x (List.mem_of_mem_take hx)]

/-- The least good element of a set of positive numbers, from its sorted list. -/
theorem pick_filter (Q : Finset ℕ) (h0 : ∀ q ∈ Q, q ≠ 0) :
    pick {q ∈ Q | good q}
      = if hit good (Q.sort (· ≤ ·)) = 0 then 1 else hit good (Q.sort (· ≤ ·)) := by
  unfold hit
  cases h : (Q.sort (· ≤ ·)).find? (fun q => decide (good q)) with
  | none =>
    have hempty : ({q ∈ Q | good q} : Finset ℕ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro q hq
      simpa using List.find?_eq_none.1 h q ((Finset.mem_sort _).2 hq)
    simp [pick, hempty]
  | some x =>
    obtain ⟨hx, as, bs, hl, has⟩ := List.find?_eq_some_iff_append.1 h
    have hxQ : x ∈ Q := (Finset.mem_sort (· ≤ ·)).1 (by rw [hl]; simp)
    have hgood : good x := by simpa using hx
    have hmem : x ∈ ({q ∈ Q | good q} : Finset ℕ) := by simp [hxQ, hgood]
    have hne : ({q ∈ Q | good q} : Finset ℕ).Nonempty := ⟨x, hmem⟩
    have hsorted := Finset.pairwise_sort Q (· ≤ ·)
    rw [hl, List.pairwise_append] at hsorted
    have hmin : ({q ∈ Q | good q} : Finset ℕ).min' hne = x := by
      apply le_antisymm (Finset.min'_le _ _ hmem)
      apply Finset.le_min'
      intro y hy
      obtain ⟨hyQ, hyg⟩ := Finset.mem_filter.1 hy
      have hyl : y ∈ as ++ x :: bs := by
        rw [← hl]
        exact (Finset.mem_sort _).2 hyQ
      rcases List.mem_append.1 hyl with hbefore | hfrom
      · exact absurd hyg (by simpa using has y hbefore)
      · rcases List.mem_cons.1 hfrom with rfl | hafter
        · exact le_rfl
        · exact (List.pairwise_cons.1 hsorted.2.1).1 y hafter
    simp [pick, hne, hmin, h0 x hxQ]

/-- The least element of a set of primes up to m, or 1, lies between 1 and m. -/
theorem pick_bounds {m : ℕ} (hm : 1 ≤ m) {T : Finset ℕ} (hT : T ⊆ Nat.primesLE m) :
    1 ≤ pick T ∧ pick T ≤ m := by
  unfold pick
  split_ifs with h
  · have := Nat.mem_primesLE.1 (hT (Finset.min'_mem T h))
    exact ⟨this.2.one_le, this.1⟩
  · exact ⟨le_rfl, hm⟩

end FirstGood

open FirstGood

/-! ## One test of a candidate -/

namespace Search

/-- The local variables of search: the arguments mult, s₁, l₁, s₂, l₂, s₃, l₃, b₁, b₂, b₃, np, pr,
cnt, fr; the number of the candidate; the first good candidate found so far (0 if none); the modulus
mult · q; a number of colliding pairs; and whether the candidate has passed all tests so far.  Local
0 also takes the result. -/
abbrev Mult : ℕ := 0
@[inherit_doc Mult] abbrev Result : ℕ := 0
@[inherit_doc Mult] abbrev Set1 : ℕ := 1
@[inherit_doc Mult] abbrev Len1 : ℕ := 2
@[inherit_doc Mult] abbrev Set2 : ℕ := 3
@[inherit_doc Mult] abbrev Len2 : ℕ := 4
@[inherit_doc Mult] abbrev Set3 : ℕ := 5
@[inherit_doc Mult] abbrev Len3 : ℕ := 6
@[inherit_doc Mult] abbrev Bound1 : ℕ := 7
@[inherit_doc Mult] abbrev Bound2 : ℕ := 8
@[inherit_doc Mult] abbrev Bound3 : ℕ := 9
@[inherit_doc Mult] abbrev NumPrimes : ℕ := 10
@[inherit_doc Mult] abbrev Primes : ℕ := 11
@[inherit_doc Mult] abbrev Count : ℕ := 12
@[inherit_doc Mult] abbrev Free : ℕ := 13
@[inherit_doc Mult] abbrev Idx : ℕ := 14
@[inherit_doc Mult] abbrev Found : ℕ := 15
@[inherit_doc Mult] abbrev Modulus : ℕ := 16
@[inherit_doc Mult] abbrev Pairs : ℕ := 17
@[inherit_doc Mult] abbrev Passed : ℕ := 18

end Search

open Search in
/-- One test: pairs := coll(len, s, modulus, cnt, fr); if b < pairs * np then passed := 0.  The set
has its length in local xl and its address in local xs, and the bound b is in local xb. -/
def checkStmt (pColl xl xs xb : ℕ) : Stmt :=
  .call pColl [v xl, v xs, v Modulus, v Count, v Free] Pairs ;;
  .ite (v xb <' v Pairs *' v NumPrimes) (.set Passed (k 0)) .skip

/-- **One test** leaves the number of colliding pairs in the local Pairs, and puts 0 in the local
Passed if it is too large.  The locals are arbitrary, since the test is made for each of
the three sets; hloc says what the test reads, and for a state that is written as a list it holds by
definition.  The bound must not stand in Pairs, which the call overwrites (hxb). -/
theorem check_ends {pColl : ℕ} (hColl : CollSpec lim P pColl)
    {d fr V Mo s len cnt cap np b xl xs xb : ℕ} {S : Finset ℤ} {loc μ : ℕ → ℤ}
    (hB : BucketMem μ fr V Mo s len cnt cap S) (hok : (collNeed len V Mo).Ok lim fr (d + 1))
    (hprod : (len : ℤ) ^ 2 * np ≤ lim.word) (hxb : xb ≠ Search.Pairs := by decide)
    (hloc : loc xl = len ∧ loc xs = s ∧ loc xb = b ∧ loc Search.Modulus = Mo ∧
      loc Search.Count = cnt ∧ loc Search.Free = fr ∧ loc Search.NumPrimes = np := by
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) :
    Ends lim P d (checkStmt pColl xl xs xb) ⟨loc, μ⟩ (15 + tColl len V) fun σ' =>
      ∃ μ', Kept μ μ' fr ∧ σ' = ⟨updateLocals loc [(Search.Pairs, (coll S Mo : ℤ)),
        (Search.Passed, if coll S Mo * np ≤ b then loc Search.Passed else 0)], μ'⟩ := by
  obtain ⟨el, es, eb, emod, ecnt, efr, enp⟩ := hloc
  have hdepth := hok.depth
  have hcoll : (coll S Mo : ℤ) * np ≤ lim.word := by
    have hsq : coll S Mo ≤ len ^ 2 := hB.set.card ▸ coll_le_sq S Mo
    exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsq) (by positivity)) hprod
  have hnonneg : (0 : ℤ) ≤ (coll S Mo : ℤ) * np := by positivity
  simp only [checkStmt, Search.Modulus, Search.Count, Search.Free, Search.Pairs, Search.NumPrimes,
    Search.Passed]
  -- pairs := coll(len, s, modulus, cnt, fr)
  refine Ends.callThen (hColl (d + 1) fr V Mo s len cnt cap S μ hB hok) ?_
    (by simp [el, es, emod, ecnt, efr])
  rintro _ μ' ⟨rfl, kept⟩
  -- if b < pairs * np
  refine Ends.iteLast (fun hlarge => ?_) (fun hsmall => ?_) (by simp [enp]; omega)
  · -- passed := 0
    have hlarge' : ¬ coll S Mo * np ≤ b := fun h => by
      have hlt : (b : ℤ) < (coll S Mo : ℤ) * np := by simpa [hxb, eb, enp] using hlarge
      have hle : ((coll S Mo * np : ℕ) : ℤ) ≤ b := by exact_mod_cast h
      push_cast at hle
      omega
    exact Ends.setLast ⟨μ', kept, by simp [if_neg hlarge']⟩ (by simp; omega)
  · have hsmall' : coll S Mo * np ≤ b := by
      have hnlt : ¬ (b : ℤ) < (coll S Mo : ℤ) * np := by simpa [hxb, eb, enp] using hsmall
      exact_mod_cast not_lt.1 hnlt
    refine Ends.skip ⟨μ', kept, ?_⟩
    rw [if_pos hsmall', updateLocals, updateLocals, updateLocals,
      show loc Search.Passed = Function.update loc Search.Pairs
        (coll S Mo : ℤ) Search.Passed by simp,
      Function.update_eq_self]

/-! ## The search -/

open Search in
/-- The three tests of a candidate. -/
def searchChecks (pColl : ℕ) : Stmt :=
  checkStmt pColl Len1 Set1 Bound1 ;;
  checkStmt pColl Len2 Set2 Bound2 ;;
  checkStmt pColl Len3 Set3 Bound3

open Search in
/-- The candidate is recorded: if passed = 1 and found = 0 then found := mem[pr + t]. -/
def searchRecord : Stmt :=
  .ite (v Passed =' k 1) (.ite (v Found =' k 0) (.set Found (M (v Primes +' v Idx))) .skip) .skip

open Search in
/-- A round of search, for candidate number t: modulus := mult * mem[pr + t]; passed := 1; the three
tests; the candidate is recorded. -/
def searchRound (pColl : ℕ) : Stmt :=
  .set Modulus (v Mult *' M (v Primes +' v Idx)) ;;
  .set Passed (k 1) ;;
  searchChecks pColl ;;
  searchRecord

open Search in
/-- search(mult, s₁, l₁, s₂, l₂, s₃, l₃, b₁, b₂, b₃, np, pr, cnt, fr): found := 0; a round for each
t < np; return found, or 1 if found = 0. -/
def searchBody (pColl : ℕ) : Stmt :=
  .set Found (k 0) ;;
  .for Idx (v NumPrimes) (searchRound pColl) ;;
  .ite (v Found =' k 0) (.set Result (k 1)) (.set Result (v Found))

section search

variable {d pColl : ℕ} {x : SearchArgs} {μ : ℕ → ℤ}

/-- There are at most m² + 1 primes up to m.  (This is the shape y ≤ M + 1 that `mul_le_word` asks
for, with M = m².) -/
theorem Env.Ok.np_le {e : Env} (h : e.Ok μ) : e.np ≤ e.m * e.m + 1 := by
  have hcard := h.primes.1 ▸ Nat.card_primesLE_le e.m
  have hsq := Nat.le_mul_self e.m
  omega

/-- What is allowed for search covers what coll needs one level of calls further down. -/
theorem collNeed_ok_of_search {fr n V m l Mo : ℕ} (hok : (searchNeed n V m).Ok lim fr d)
    (hl : l ≤ n) (hMo : Mo ≤ m * m) : (collNeed l V Mo).Ok lim fr (d + 1) :=
  hok.mono (wordNeed_mono hl hMo) (by simp only [collNeed, searchNeed]; omega)
    (by simp only [collNeed, searchNeed]; omega)

/-- The time of the three tests of a candidate. -/
def tChecks (x : SearchArgs) : ℕ :=
  45 + (tColl x.X₁.len x.V + tColl x.X₂.len x.V + tColl x.X₃.len x.V)

/-- **The three tests** leave 1 in the local Passed if the candidate is good, and 0 if not. -/
theorem searchChecks_ends (hColl : CollSpec lim P pColl) (hN : NodeMem μ x.toNodeArgs)
    (hok : (searchNeed x.n x.V x.m).Ok lim x.fr d) {q t found : ℕ} {c : ℤ}
    (hM1 : 1 ≤ x.mult * q) (hM : x.mult * q ≤ x.m * x.m) :
    Ends lim P d (searchChecks pColl)
      ⟨frame (x.vals ++ [(t : ℤ), found, (x.mult * q : ℕ), c, 1]), μ⟩ (tChecks x) fun σ' =>
      ∃ (c' : ℤ) (μ' : ℕ → ℤ), Kept μ μ' x.fr ∧ σ' = ⟨frame (x.vals ++
        [(t : ℤ), found, (x.mult * q : ℕ), c', if x.Good q then 1 else 0]), μ'⟩ := by
  have hprod : ∀ l ≤ x.n, (l : ℤ) ^ 2 * x.np ≤ lim.word := fun l hl => by
    simpa using mul_le_word (x := l ^ 2) (z := 1) hok.word (Nat.pow_le_pow_left (by omega) 2)
      hN.envOk.np_le (by omega)
  unfold tChecks
  -- the first set
  light_piece (check_ends hColl (hN.set₁.bucket hN.envOk hM1 hM)
    (collNeed_ok_of_search hok hN.set₁.le hM) (hprod _ hN.set₁.le)) with _ ⟨μ₁, kept₁, rfl⟩
  have hN₁ := hN.kept kept₁
  -- the second set
  light_piece (check_ends hColl (hN₁.set₂.bucket hN₁.envOk hM1 hM)
    (collNeed_ok_of_search hok hN.set₂.le hM) (hprod _ hN.set₂.le)) with _ ⟨μ₂, kept₂, rfl⟩
  have hN₂ := hN₁.kept kept₂
  -- the third set
  light_piece (check_ends hColl (hN₂.set₃.bucket hN₂.envOk hM1 hM)
    (collNeed_ok_of_search hok hN.set₃.le hM) (hprod _ hN.set₃.le)) with _ ⟨μ₃, kept₃, rfl⟩
  refine ⟨coll x.X₃.set (x.mult * q), μ₃, kept₁.trans (kept₂.trans kept₃), ?_⟩
  by_cases h₁ : coll x.X₁.set (x.mult * q) * x.np ≤ x.b₁ <;>
    by_cases h₂ : coll x.X₂.set (x.mult * q) * x.np ≤ x.b₂ <;>
    by_cases h₃ : coll x.X₃.set (x.mult * q) * x.np ≤ x.b₃ <;>
    simp [update_frame_setLocal, SearchArgs.Good, h₁, h₂, h₃]

/-- The candidates of search: the primes up to m, in ascending order. -/
abbrev SearchArgs.candidates (x : SearchArgs) : List ℕ := (Nat.primesLE x.m).sort (· ≤ ·)

/-- The state before candidate number t is tested: the local Found holds the first good candidate
among the first t (0 if there is none), the locals Modulus, Pairs and Passed hold anything, and no
cell below the free pointer has changed. -/
def SearchInv (μ : ℕ → ℤ) (x : SearchArgs) (t : ℕ) (σ : State) : Prop :=
  ∃ (y z w : ℤ) (μ' : ℕ → ℤ), Kept μ μ' x.fr ∧
    σ = ⟨frame (x.vals ++ [(t : ℤ), (hit x.Good (x.candidates.take t) : ℕ), y, z, w]), μ'⟩

/-- **The candidate is recorded** if it is good and no earlier one was. -/
theorem searchRecord_ends {g : Prop} [Decidable g] {t found q : ℕ} {y c : ℤ}
    (hread : μ (x.pr + t) = (q : ℕ)) (hpr : x.pr + t < lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hone : (1 : ℤ) ≤ lim.word) :
    Ends lim P d searchRecord
      ⟨frame (x.vals ++ [(t : ℤ), found, y, c, if g then 1 else 0]), μ⟩ 13 fun σ' =>
      σ' = ⟨frame (x.vals ++ [(t : ℤ),
        ((if found = 0 then (if g then q else 0) else found : ℕ) : ℤ), y, c,
        if g then 1 else 0]), μ⟩ := by
  by_cases hg : g
  · simp only [if_pos hg]
    -- if passed = 1
    refine Ends.iteLast (fun _ => ?_) (fun h => absurd h (by simp))
    -- if found = 0 then found := mem[pr + t]
    refine Ends.iteLast (fun hfirst => ?_) (fun hlater => ?_)
    · have hzero : found = 0 := by simpa using hfirst
      exact Ends.setTo (q : ℤ) (by simp [hzero]) (by light_side [hread])
    · have hpos : ¬ found = 0 := by simpa using hlater
      exact Ends.skip (by simp [hpos])
  · simp only [if_neg hg]
    refine Ends.iteLast (fun h => absurd h (by simp)) (fun _ => Ends.skip ?_)
    by_cases hzero : found = 0 <;> simp [hzero]

/-- **A round of search** tests candidate number t and records it if it is the first good one.  The
conclusion has the form that `Ends.for` asks of a round: the counter is unchanged, and the invariant
holds once it is increased. -/
theorem searchRound_ends (hColl : CollSpec lim P pColl) (hN : NodeMem μ x.toNodeArgs)
    (hmult_pos : 1 ≤ x.mult) (hmult_le : x.mult ≤ x.m)
    (hok : (searchNeed x.n x.V x.m).Ok lim x.fr d) {t : ℕ} (ht : t < x.np) {σ : State}
    (hσ : SearchInv μ x t σ) :
    Ends lim P d (searchRound pColl) σ (tChecks x + 22) fun σ' =>
      σ'.loc Search.Idx = t ∧ SearchInv μ x (t + 1)
        { σ' with loc := Function.update σ'.loc Search.Idx ((t : ℤ) + 1) } := by
  obtain ⟨y, z, w, μ', kept, rfl⟩ := hσ
  have hN' := hN.kept kept
  unfold SearchInv
  generalize hps : x.candidates = ps at *
  have htl : t < ps.length := by rw [← hps, Finset.length_sort, ← hN.envOk.primes.1]; exact ht
  have hprime : ∀ q ∈ ps, q.Prime ∧ q ≤ x.m := fun q hq => by
    rw [← hps, Finset.mem_sort, Nat.mem_primesLE] at hq
    exact ⟨hq.2, hq.1⟩
  obtain ⟨hqp, hqm⟩ := hprime ps[t] (List.getElem_mem htl)
  have hread : μ' (x.pr + t) = (ps[t] : ℕ) := SegN.getElem (hps ▸ hN'.envOk.primes.2) htl
  have hsucc := hit_take_succ (good := x.Good) (fun q hq => (hprime q hq).1.ne_zero) htl
  have hMo : x.mult * ps[t] ≤ x.m * x.m := Nat.mul_le_mul hmult_le hqm
  have hMw : (x.mult : ℤ) * ps[t] ≤ lim.word := by
    exact_mod_cast le_word_of_le (y := x.mult * ps[t]) hok.word (by omega)
  have hMpos : (1 : ℤ) ≤ (x.mult : ℤ) * ps[t] := by
    exact_mod_cast Nat.mul_pos hmult_pos hqp.one_le
  have hw := hok.space
  have hcells := hok.cells
  have hpr := hN.envOk.belowPr
  -- modulus := mult * mem[pr + t]
  light_set (x.mult * ps[t] : ℕ) using hread
  -- passed := 1
  light_set 1
  -- the three tests
  light_piece (searchChecks_ends hColl hN' hok (Nat.mul_pos hmult_pos hqp.one_le) hMo)
    with _ ⟨c, μ'', kept', rfl⟩
  -- the candidate is recorded
  light_piece (searchRecord_ends ((kept' _ (by omega)).trans hread) (by omega) hw (by omega))
    with _ rfl
  exact ⟨by simp, _, c, _, μ'', kept.trans kept', by rw [update_frame_setLocal, hsucc]; rfl⟩

/-- **search** meets its specification. -/
theorem search_spec {p : ℕ} (hP : P[p]? = some (searchBody pColl)) (hColl : CollSpec lim P pColl) :
    SearchSpec lim P p := by
  intro x μ hN hmult_pos hmult_le d hok
  refine .of_body hP ?_
  have hone : ((1 : ℕ) : ℤ) ≤ lim.word := le_word_of_le hok.word (by omega)
  have hnp : (x.np : ℤ) ≤ lim.word := le_word_of_le hok.word hN.envOk.np_le
  -- found := 0
  refine Ends.setToThen 0 ?_ (hT := by simp [tSearch])
  -- for t < np
  refine Ends.next _ (Ends.for (SearchInv μ x) x.np (tChecks x + 22) ?start ?round ?done ?bound
    (hT := le_rfl)) (by simp [tSearch, tChecks]; ring_nf; omega)
  case start =>
    exact ⟨0, 0, 0, μ, .refl, by rw [update_frame_setLocal, ← frame_append_zeros _ 3]; rfl⟩
  case round => exact fun t σ ht _ hσ => searchRound_ends hColl hN hmult_pos hmult_le hok ht hσ
  case done =>
    rintro _ - ⟨y, z, w, μ', kept, rfl⟩
    have hpick := pick_filter (good := x.Good) (Nat.primesLE x.m)
      fun q hq => (Nat.prime_of_mem_primesLE hq).ne_zero
    rw [List.take_of_length_le (by rw [Finset.length_sort, hN.envOk.primes.1])]
    generalize hit x.Good x.candidates = found at *
    -- return found, or 1 if found = 0
    refine Ends.iteLast (fun hnone => ?_) (fun hsome => ?_)
      (hT := by simp [tSearch, tChecks]; ring_nf; omega)
    · have hzero : found = 0 := by simpa using hnone
      exact Ends.setTo 1 ⟨by simp [hpick, hzero], kept⟩
        (hT := by simp [tSearch, tChecks]; ring_nf; omega)
    · have hpos : ¬ found = 0 := by simpa using hsome
      exact Ends.setTo found ⟨by simp [hpick, hpos], kept⟩
        (hT := by simp [tSearch, tChecks]; ring_nf; omega)
  case bound =>
    rintro t _ - - ⟨y, z, w, μ', -, rfl⟩
    simp

end search

/-! ## The modulus -/

namespace Modulus

/-- The local variables of modulus: the arguments s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr; the
two primes; and the numbers of colliding pairs of the three sets modulo the first prime.  Local 0
also takes the result. -/
abbrev Set1 : ℕ := 0
@[inherit_doc Set1] abbrev Result : ℕ := 0
@[inherit_doc Set1] abbrev Len1 : ℕ := 1
@[inherit_doc Set1] abbrev Set2 : ℕ := 2
@[inherit_doc Set1] abbrev Len2 : ℕ := 3
@[inherit_doc Set1] abbrev Set3 : ℕ := 4
@[inherit_doc Set1] abbrev Len3 : ℕ := 5
@[inherit_doc Set1] abbrev Digits : ℕ := 6
@[inherit_doc Set1] abbrev NumPrimes : ℕ := 7
@[inherit_doc Set1] abbrev Primes : ℕ := 8
@[inherit_doc Set1] abbrev Count : ℕ := 9
@[inherit_doc Set1] abbrev Free : ℕ := 10
@[inherit_doc Set1] abbrev Prime1 : ℕ := 11
@[inherit_doc Set1] abbrev Prime2 : ℕ := 12
@[inherit_doc Set1] abbrev Pairs1 : ℕ := 13
@[inherit_doc Set1] abbrev Pairs2 : ℕ := 14
@[inherit_doc Set1] abbrev Pairs3 : ℕ := 15

end Modulus

open Modulus in
/-- The numbers of colliding pairs of the three sets modulo the first prime. -/
def modulusColls (pColl : ℕ) : Stmt :=
  .call pColl [v Len1, v Set1, v Prime1, v Count, v Free] Pairs1 ;;
  .call pColl [v Len2, v Set2, v Prime1, v Count, v Free] Pairs2 ;;
  .call pColl [v Len3, v Set3, v Prime1, v Count, v Free] Pairs3

open Modulus in
/-- The two searches of modulus, with the three calls of coll between them, and the product. -/
def modulusMain (pSearch pColl : ℕ) : Stmt :=
  .call pSearch
    [k 1, v Set1, v Len1, v Set2, v Len2, v Set3, v Len3,
      k 3 *' v Digits *' v Len1 *' v Len1,
      k 3 *' v Digits *' v Len2 *' v Len2,
      k 3 *' v Digits *' v Len3 *' v Len3,
      v NumPrimes, v Primes, v Count, v Free] Prime1 ;;
  modulusColls pColl ;;
  .call pSearch
    [v Prime1, v Set1, v Len1, v Set2, v Len2, v Set3, v Len3,
      k 3 *' v Digits *' v Pairs1,
      k 3 *' v Digits *' v Pairs2,
      k 3 *' v Digits *' v Pairs3,
      v NumPrimes, v Primes, v Count, v Free] Prime2 ;;
  .set Result (v Prime1 *' v Prime2)

open Modulus in
/-- modulus(s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr) returns 1 if there is no prime, and the
product of the two primes otherwise. -/
def modulusBody (pSearch pColl : ℕ) : Stmt :=
  .ite (v NumPrimes =' k 0) (.set Result (k 1)) (modulusMain pSearch pColl)

section modulus

variable {d Λ pSearch pColl : ℕ} {a : NodeArgs} {μ : ℕ → ℤ}

/-- The arguments of the first search: the moduli are the primes, and the bounds are 3 Λ lᵢ². -/
@[simp] def NodeArgs.firstSearch (a : NodeArgs) (Λ : ℕ) : SearchArgs :=
  { toNodeArgs := a, mult := 1, b₁ := 3 * Λ * a.X₁.len * a.X₁.len,
    b₂ := 3 * Λ * a.X₂.len * a.X₂.len, b₃ := 3 * Λ * a.X₃.len * a.X₃.len }

/-- The arguments of the second search: the moduli are the multiples of p₁ by the primes, and the
bounds are 3 Λ times the numbers of colliding pairs modulo p₁. -/
@[simp] def NodeArgs.secondSearch (a : NodeArgs) (Λ p₁ : ℕ) : SearchArgs :=
  { toNodeArgs := a, mult := p₁, b₁ := 3 * Λ * coll a.X₁.set p₁, b₂ := 3 * Λ * coll a.X₂.set p₁,
    b₃ := 3 * Λ * coll a.X₃.set p₁ }

/-- The first search returns the first prime of the node. -/
theorem search_meets_firstP (hSearch : SearchSpec lim P pSearch) (hN : NodeMem μ a) (hm : 1 ≤ a.m)
    (hok : (searchNeed a.n a.V a.m).Ok lim a.fr d) :
    Meets lim P pSearch d (a.firstSearch Λ).vals μ (tSearch a.np a.X₁.len a.X₂.len a.X₃.len a.V)
      fun r μ' => r = (firstP (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set : ℤ) ∧
        Kept μ μ' a.fr := by
  refine (hSearch (a.firstSearch Λ) μ hN le_rfl hm d hok).mono le_rfl ?_
  rintro _ μ' ⟨rfl, kept⟩
  refine ⟨?_, kept⟩
  unfold firstP SearchArgs.Good
  simp only [NodeArgs.firstSearch, one_mul, ← hN.envOk.primes.1, hN.set₁.set.card, hN.set₂.set.card,
    hN.set₃.set.card, sq, mul_assoc]

/-- The second search returns the second prime of the node. -/
theorem search_meets_secondP (hSearch : SearchSpec lim P pSearch) (hN : NodeMem μ a) {p₁ : ℕ}
    (hp₁_pos : 1 ≤ p₁) (hp₁_le : p₁ ≤ a.m) (hok : (searchNeed a.n a.V a.m).Ok lim a.fr d) :
    Meets lim P pSearch d (a.secondSearch Λ p₁).vals μ
      (tSearch a.np a.X₁.len a.X₂.len a.X₃.len a.V)
      fun r μ' => r = (secondP (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set p₁ : ℤ) ∧
        Kept μ μ' a.fr := by
  refine (hSearch (a.secondSearch Λ p₁) μ hN hp₁_pos hp₁_le d hok).mono le_rfl ?_
  rintro _ μ' ⟨rfl, kept⟩
  refine ⟨?_, kept⟩
  unfold secondP SearchArgs.Good
  simp only [NodeArgs.secondSearch, ← hN.envOk.primes.1]
  rfl

section words

variable {n V m : ℕ}

/-- The bounds that are handed to search fit in a word: 3 Λ x for x up to (n + 1)². -/
theorem three_lam_mul_le (hword : ((wordNeed n V (m * m) : ℕ) : ℤ) ≤ lim.word) (hΛ : Λ ≤ V + 2)
    {x : ℕ} (hx : x ≤ (n + 1) ^ 2) : 0 ≤ 3 * (Λ : ℤ) * x ∧ 3 * (Λ : ℤ) * x ≤ lim.word := by
  have h := mul_le_word (y := 1) (z := 3 * Λ) hword hx (by omega) (by omega)
  push_cast at h
  exact ⟨by positivity, by linarith⟩

/-- The same for a length and its square. -/
theorem three_lam_sq_le (hword : ((wordNeed n V (m * m) : ℕ) : ℤ) ≤ lim.word) (hΛ : Λ ≤ V + 2)
    {l : ℕ} (hl : l ≤ n) : (0 ≤ 3 * (Λ : ℤ) * l ∧ 3 * (Λ : ℤ) * l ≤ lim.word) ∧
      0 ≤ 3 * (Λ : ℤ) * l * l ∧ 3 * (Λ : ℤ) * l * l ≤ lim.word := by
  have hsq : l * l ≤ (n + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h := three_lam_mul_le hword hΛ hsq
  push_cast at h
  rw [← mul_assoc] at h
  exact ⟨three_lam_mul_le hword hΛ ((Nat.le_mul_self l).trans hsq), h⟩

/-- The same for a number of colliding pairs. -/
theorem three_lam_coll_le (hword : ((wordNeed n V (m * m) : ℕ) : ℤ) ≤ lim.word) (hΛ : Λ ≤ V + 2)
    {s l M : ℕ} {S : Finset ℤ} (hS : SetAt μ s l S) (hl : l ≤ n) :
    0 ≤ 3 * (Λ : ℤ) * coll S M ∧ 3 * (Λ : ℤ) * coll S M ≤ lim.word :=
  three_lam_mul_le hword hΛ ((coll_le_sq S M).trans (hS.card ▸ Nat.pow_le_pow_left (by omega) 2))

end words

/-- coll, called for a set of a node. -/
theorem Slot.Ok.coll_meets {e : Env} {X : Slot} {M : ℕ} (h : X.Ok μ e) (he : e.Ok μ)
    (hColl : CollSpec lim P pColl) (hM : 1 ≤ M) (hMm : M ≤ e.m * e.m)
    (hok : (collNeed X.len e.V M).Ok lim e.fr d) :
    Meets lim P pColl d [X.len, X.addr, M, e.cnt, e.fr] μ (tColl X.len e.V) fun r μ' =>
      r = (coll X.set M : ℤ) ∧ Kept μ μ' e.fr :=
  hColl d _ _ _ _ _ _ _ _ μ (h.bucket he hM hMm) hok

/-- **The three calls of coll** between the two searches leave the numbers of colliding pairs modulo
p₁ in Pairs1, Pairs2, Pairs3 and change no cell below the free pointer. -/
theorem modulusColls_ends (hColl : CollSpec lim P pColl) (hN : NodeMem μ a)
    (hok : (modulusNeed a.n a.V a.m).Ok lim a.fr d) {p₁ : ℕ} (hp₁_pos : 1 ≤ p₁)
    (hp₁_le_sq : p₁ ≤ a.m * a.m) :
    Ends lim P d (modulusColls pColl) ⟨frame (a.modulusVals Λ ++ [(p₁ : ℤ)]), μ⟩
      (21 + (tColl a.X₁.len a.V + tColl a.X₂.len a.V + tColl a.X₃.len a.V)) fun σ' =>
      ∃ μ', Kept μ μ' a.fr ∧ σ' = ⟨frame (a.modulusVals Λ ++
        [(p₁ : ℤ), 0, coll a.X₁.set p₁, coll a.X₂.set p₁, coll a.X₃.set p₁]), μ'⟩ := by
  have hdepth := hok.depth
  simp only [modulusNeed] at hdepth
  have hokC : ∀ {l : ℕ}, l ≤ a.n → (collNeed l a.V p₁).Ok lim a.fr (d + 1) := fun hl =>
    hok.mono (wordNeed_mono hl hp₁_le_sq) (by simp only [collNeed, modulusNeed]; omega)
      (by simp only [collNeed, modulusNeed]; omega)
  -- c₁ := coll(l₁, s₁, p₁, cnt, fr)
  light_call (hN.set₁.coll_meets hN.envOk hColl hp₁_pos hp₁_le_sq (hokC hN.set₁.le))
    with _ μ₁ ⟨rfl, kept₁⟩
  have hN₁ := hN.kept kept₁
  -- c₂ := coll(l₂, s₂, p₁, cnt, fr)
  light_call (hN₁.set₂.coll_meets hN₁.envOk hColl hp₁_pos hp₁_le_sq (hokC hN.set₂.le))
    with _ μ₂ ⟨rfl, kept₂⟩
  have hN₂ := hN₁.kept kept₂
  -- c₃ := coll(l₃, s₃, p₁, cnt, fr)
  light_call (hN₂.set₃.coll_meets hN₂.envOk hColl hp₁_pos hp₁_le_sq (hokC hN.set₃.le))
    with _ μ₃ ⟨rfl, kept₃⟩
  exact ⟨μ₃, kept₁.trans (kept₂.trans kept₃), rfl⟩

/-- **The main part of modulus** returns the product of the two primes of the node. -/
theorem modulusMain_ends (hSearch : SearchSpec lim P pSearch) (hColl : CollSpec lim P pColl)
    (hN : NodeMem μ a) (hΛ : Λ ≤ a.V + 2) (hok : (modulusNeed a.n a.V a.m).Ok lim a.fr d)
    (hm : 1 ≤ a.m) :
    Ends lim P d (modulusMain pSearch pColl) ⟨frame (a.modulusVals Λ), μ⟩
      (tModulus a.np a.X₁.len a.X₂.len a.X₃.len a.V - 73) fun σ' =>
      σ'.loc Modulus.Result = (modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set : ℤ) ∧
        Kept μ σ'.mem a.fr := by
  have hdepth := hok.depth
  simp only [modulusNeed] at hdepth
  have hokS : (searchNeed a.n a.V a.m).Ok lim a.fr (d + 1) :=
    hok.mono le_rfl le_rfl (by simp only [searchNeed, modulusNeed]; omega)
  obtain ⟨p₁, hfirst⟩ : ∃ p₁, p₁ = firstP (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set :=
    ⟨_, rfl⟩
  obtain ⟨p₂, hsecond⟩ :
      ∃ p₂, p₂ = secondP (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set p₁ := ⟨_, rfl⟩
  obtain ⟨hp₁_pos, hp₁_le⟩ : 1 ≤ p₁ ∧ p₁ ≤ a.m := by
    rw [hfirst, firstP]
    exact pick_bounds hm (Finset.filter_subset _ _)
  obtain ⟨-, hp₂_le⟩ : 1 ≤ p₂ ∧ p₂ ≤ a.m := by
    rw [hsecond, secondP]
    exact pick_bounds hm (Finset.filter_subset _ _)
  -- The words that are formed: 3, 3 Λ, 3 Λ lᵢ, 3 Λ lᵢ², 3 Λ cᵢ and p₁ p₂.
  have hthree := three_lam_mul_le (Λ := 1) hok.word (by omega) (x := 1)
    (Nat.one_le_pow _ _ (by omega))
  have hlam := three_lam_mul_le hok.word hΛ (x := 1) (Nat.one_le_pow _ _ (by omega))
  have hlen₁ := three_lam_sq_le hok.word hΛ hN.set₁.le
  have hlen₂ := three_lam_sq_le hok.word hΛ hN.set₂.le
  have hlen₃ := three_lam_sq_le hok.word hΛ hN.set₃.le
  have hcoll₁ := three_lam_coll_le (M := p₁) hok.word hΛ hN.set₁.set hN.set₁.le
  have hcoll₂ := three_lam_coll_le (M := p₁) hok.word hΛ hN.set₂.set hN.set₂.le
  have hcoll₃ := three_lam_coll_le (M := p₁) hok.word hΛ hN.set₃.set hN.set₃.le
  have hprod : 0 ≤ (p₁ : ℤ) * p₂ ∧ (p₁ : ℤ) * p₂ ≤ lim.word := ⟨by positivity, by
    exact_mod_cast le_word_of_le (y := p₁ * p₂) hok.word
      ((Nat.mul_le_mul hp₁_le hp₂_le).trans (by omega))⟩
  simp only [tModulus]
  -- p₁ := search(1, s₁, l₁, s₂, l₂, s₃, l₃, 3 Λ l₁², 3 Λ l₂², 3 Λ l₃², np, pr, cnt, fr)
  light_call (search_meets_firstP (Λ := Λ) hSearch hN hm hokS) with _ μ₁ ⟨rfl, kept₁⟩
  rw [← hfirst]
  -- the numbers cᵢ of colliding pairs modulo p₁
  light_piece (modulusColls_ends hColl (hN.kept kept₁) hok hp₁_pos
    (hp₁_le.trans (Nat.le_mul_self a.m))) with _ ⟨μ₂, kept₂, rfl⟩
  -- p₂ := search(p₁, s₁, l₁, s₂, l₂, s₃, l₃, 3 Λ c₁, 3 Λ c₂, 3 Λ c₃, np, pr, cnt, fr)
  light_call (search_meets_secondP (Λ := Λ) hSearch ((hN.kept kept₁).kept kept₂)
    hp₁_pos hp₁_le hokS) with _ μ₃ ⟨rfl, kept₃⟩
  rw [← hsecond]
  -- return p₁ * p₂
  light_set ((p₁ : ℤ) * p₂)
  refine ⟨?_, kept₁.trans (kept₂.trans kept₃)⟩
  simp [modulus, ← hfirst, ← hsecond]

/-- **modulus** meets its specification. -/
theorem modulus_spec {p : ℕ} (hP : P[p]? = some (modulusBody pSearch pColl))
    (hSearch : SearchSpec lim P pSearch) (hColl : CollSpec lim P pColl) : ModulusSpec lim P p := by
  intro a Λ μ hN hΛ d hok
  refine .of_body hP ?_
  have hone : ((1 : ℕ) : ℤ) ≤ lim.word := le_word_of_le hok.word (by omega)
  have hcard := hN.envOk.primes.1
  -- if np = 0
  refine Ends.iteLast (fun hnone => ?_) (fun hsome => ?_) (hT := by simp [tModulus])
  · -- return 1
    have hempty : Nat.primesLE a.m = ∅ := Finset.card_eq_zero.1 (by
      have hnp : a.np = 0 := by simpa using hnone
      omega)
    exact Ends.setTo 1 ⟨by simp [modulus, firstP, secondP, pick, hempty], .refl⟩
      (hT := by simp [tModulus])
  · have hm : 1 ≤ a.m := by
      have hpos : 0 < #(Nat.primesLE a.m) := by
        have hnp : ¬ a.np = 0 := by simpa using hsome
        omega
      obtain ⟨q, hq⟩ := Finset.card_pos.1 hpos
      exact (Nat.prime_of_mem_primesLE hq).one_le.trans (Nat.le_of_mem_primesLE hq)
    exact (modulusMain_ends hSearch hColl hN hΛ hok hm).mono (by simp [tModulus]) fun _ h => h

/-- The modulus, in a program that holds modulus and search, from the specification of coll. -/
theorem modulusSpec_of {p : ℕ} (hP : P[p]? = some (modulusBody pSearch pColl))
    (hPs : P[pSearch]? = some (searchBody pColl)) (hColl : CollSpec lim P pColl) :
    ModulusSpec lim P p :=
  modulus_spec hP (search_spec hPs hColl) hColl

end modulus

end Light.Sec3.ChanHe
