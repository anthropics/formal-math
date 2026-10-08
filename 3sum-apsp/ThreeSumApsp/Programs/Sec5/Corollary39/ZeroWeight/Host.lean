/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec5.Corollary39.GraphH.Build
public import ThreeSumApsp.Sec5.Corollary39

/-!
# Corollary 39, weight zero, in the light language: the host

Proof of Corollary 39: "We enumerate the n^t ways of fixing one vertex in each of the first t parts,
and for each of them we build H", and ask an arbitrary solver of Exact Triangle whether H has a
triangle of weight zero.  The number k of parts is fixed before the program is written.

kc(n, U, g, fr): the weights stand at g; the result is 1 if some k-clique has total weight zero, and
0 if not (`kcTask`).  `kcRound_spec` is one round: build H (`buildH_spec`), ask the solver, note the
answer and go to the next choice (`noteAnswer_spec`); `kc_spec` is the loop over the n^t choices,
with the invariant `KcInv`; `isHost_kc` puts it in the form of a host, with the time `kcTime` and
the need `kcNeed`.

Only weight zero is treated here; minimum and maximum weight have a host of their own.  The running
time n^{k - ε⌊k/3⌋} is derived from `kcTime` where the host is put together with the solver of
Theorem 19.

The names of the local variables that both hosts for k-Clique use are in the namespace `KC`, those
of this host in `ZeroKc`; `kcLocals` lists the locals of this host with their values before a round.
-/

@[expose] public section

open ThreeSumApsp ThreeSumApsp.Spec

namespace Light.Sec5

open ThreeSumApsp.KClique KC

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace ZeroKc

/-- The result of the host: a procedure returns what local 0 holds at its end. -/
abbrev Result : ℕ := 0
/-- The free pointer. -/
abbrev Free : ℕ := 3
/-- 1 if a triangle of weight zero has been found, 0 if not. -/
abbrev Found : ℕ := 17

end ZeroKc

open ZeroKc

/-- The result becomes 1 if the answer of the solver is 1; then the next choice. -/
def noteAnswer (kk : ℕ) : Stmt :=
  .ite (v Answer =' k 1) (.set Found (k 1)) .skip ;;
  nextChoice kk

/-- One choice of the fixed vertices: build H, ask the solver (procedure pe), note the answer, go to
the next choice. -/
def kcRound (kk pe : ℕ) : Stmt :=
  buildH kk ;;
  .call pe [v Side, k (lenH kk) *' v Bound, v MatAB, v MatBC, v MatAC, v Behind] Answer ;;
  noteAnswer kk

/-- kc(n, U, g, fr). -/
def kcBody (kk pe : ℕ) : Stmt :=
  .set Choice (v Free) ;;
  hostSetup kk ;;
  .set Found (k 0) ;;
  .while (v Round <' v Rounds) (kcRound kk pe) ;;
  .set Result (v Found)

/-- The time of one round. -/
def roundT (kk : ℕ) (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  fillT kk (n ^ width kk) 0 + fillT kk (n ^ width kk) 1 + fillT kk (n ^ width kk) 2 +
    T (n ^ width kk) (lenH kk * U) + 14 * numFixed kk + 25

/-- The time of the host. -/
def kcTime (kk : ℕ) (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  n ^ numFixed kk * (roundT kk T n U + 4) + 2 * width kk + 2 * numFixed kk + 5 * kk + 38

/-- What the host needs.  Words: what the solver needs, the largest weight of H, and the sizes.
Cells: the k chosen vertices, the three matrices, and what the solver needs.  Depth of calls: one
more than the solver. -/
def kcNeed (kk : ℕ) (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := (r (n ^ width kk) (lenH kk * U)).word + lenH kk * U + lenH kk + n ^ numFixed kk
    + n + kk + 1
  cells := kk + 3 * (n ^ width kk * n ^ width kk) + (r (n ^ width kk) (lenH kk * U)).cells
  depth := (r (n ^ width kk) (lenH kk * U)).depth + 1

/-! ## The host is correct -/

section host

variable {k : ℕ} {P₀ R : Program} {pe : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}

/-- The graph H of the choice number F has a triangle of weight zero. -/
def ZeroAt {k : ℕ} (x : KcInst k) (F : ℕ) : Prop :=
  ∃ h : F < x.n ^ numFixed k, (x.H ⟨F, h⟩).HasZeroTriangle

/-- Some k-clique has weight zero exactly if for some choice of the fixed vertices the graph H has a
triangle of weight zero. -/
theorem hasZeroClique_iff {k : ℕ} (x : KcInst k) :
    x.G.HasZeroClique ↔ ∃ F < x.n ^ numFixed k, ZeroAt x F := by
  rw [Corollary39.hasZeroClique_iff]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨finFunctionFinEquiv f, (finFunctionFinEquiv f).2, (finFunctionFinEquiv f).2, ?_⟩
    rw [Fin.eta, KcInst.H, Equiv.symm_apply_apply]
    exact hf
  · rintro ⟨F, -, h, hz⟩
    exact ⟨_, hz⟩

/-- The locals of the host before the round for the choice number F of the fixed vertices.  `found`
is the result so far. -/
@[simp] abbrev kcLocals {k : ℕ} (x : KcInst k) (fr F : ℕ) (found : ℤ) : List ℤ :=
  setLocals [] (hostPairs k x.n x.U x.g fr F ++ [(Free, (fr : ℤ)), (Found, found)])

/-- The locals of the host whose values do not matter between two rounds. -/
abbrev kcScratch : List ℕ := [Row, Col, Place, Entry, Answer]

/-- The state before the round for the choice number F of the fixed vertices: the locals of the
host, with a result that tells whether an earlier choice had a triangle of weight zero; the input;
and the chosen vertices. -/
structure KcInv {k : ℕ} (x : KcInst k) (μ₀ : ℕ → ℤ) (fr F : ℕ) (σ : State) : Prop where
  locals : LocalsBut kcScratch (kcLocals x fr F (flag (∃ F' < F, ZeroAt x F'))) σ.loc
  kept : Kept μ₀ σ.mem fr
  choice : ChoiceIs σ.mem fr k (vtx k x.n F 0 0 0)

/-- The result after one more choice, if this choice has no triangle of weight zero. -/
theorem flag_exists_lt_succ_of_not {p : ℕ → Prop} {F : ℕ} (h : ¬ p F) :
    flag (∃ F' < F + 1, p F') = flag (∃ F' < F, p F') :=
  flag_congr ⟨fun ⟨F', hlt, hp⟩ => ⟨F', by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | rfl
    · exact hlt
    · exact absurd hp h, hp⟩, fun ⟨F', hlt, hp⟩ => ⟨F', by omega, hp⟩⟩

/-- **The answer is noted**, and the next choice is made. -/
theorem noteAnswer_spec {x : KcInst k} {μ₀ : ℕ → ℤ} {fr F : ℕ} (hn : 0 < x.n)
    (hlim : OdometerOk lim x.n fr k) (hF : ((F + 1 : ℕ) : ℤ) ≤ lim.word) {loc μ : ℕ → ℤ}
    (hσ : KcInv x μ₀ fr F ⟨loc, μ⟩)
    (hanswer : loc Answer = flag (ZeroAt x F)) :
    Ends lim P d (noteAnswer k) ⟨loc, μ⟩ (14 * numFixed k + 15) (KcInv x μ₀ fr (F + 1)) := by
  -- nextChoice k, with the new result in Found
  have hnext {loc' : ℕ → ℤ}
      (hloc' : LocalsBut kcScratch (kcLocals x fr F (flag (∃ F' < F + 1, ZeroAt x F'))) loc') :
      Ends lim P d (nextChoice k) ⟨loc', μ⟩ (14 * numFixed k + 9) (KcInv x μ₀ fr (F + 1)) := by
    refine (nextChoice_spec (n := x.n) (fr := fr) (F := F) (hloc' Size (by decide))
      (hloc' Choice (by decide)) (hloc' Round (by decide)) hn hlim hF hσ.choice).mono le_rfl ?_
    rintro ⟨_, μ'⟩ ⟨rfl, hchoice, hout⟩
    exact ⟨hloc'.update Round _, fun a ha => (hout a (Or.inl ha)).trans (hσ.kept a ha), hchoice⟩
  refine Ends.asFrame hσ.locals ?_
  unfold noteAnswer
  -- if Answer = 1 then Found := 1
  refine Ends.iteThen (fun hc => ?_) fun hc => ?_
  · have hZ : ∃ F' < F + 1, ZeroAt x F' :=
      ⟨F, by omega, flag_eq_one_iff.1 (by simpa [hanswer] using hc)⟩
    rw [flag_of hZ] at hnext
    exact Ends.setToThen 1 ((hnext (LocalsBut.of_eq (by simp))).mono (by light_time) fun _ h => h)
  · have hZ : ¬ ZeroAt x F := fun h => hc (by simp [hanswer, flag_of h])
    rw [flag_exists_lt_succ_of_not hZ] at hnext
    exact Ends.next 0 (Ends.skip ((hnext (LocalsBut.of_eq (by simp))).mono (by light_time)
      fun _ h => h))

/-- **One round of the host**: H is built for the choice number F, the solver is asked, the result
becomes 1 if the answer is yes, and the next choice is made. -/
theorem kcRound_spec (hsol : Solves etTask P₀ pe T r) (hk : 3 ≤ k) {x : KcInst k} {μ₀ : ℕ → ℤ}
    {fr : ℕ} (hpre : x.Pre μ₀ fr) (hok : (kcNeed k r x.n x.U).Ok lim fr d) {F : ℕ}
    (hF : F < x.n ^ numFixed k) {σ : State} (hσ : KcInv x μ₀ fr F σ) :
    Ends lim (P₀ ++ R) d (kcRound k pe) σ (roundT k T x.n x.U) (KcInv x μ₀ fr (F + 1)) := by
  obtain ⟨loc, μ⟩ := σ
  have hw := hok.space
  have hokw := hok.word
  have hokc := hok.cells
  have hokd := hok.depth
  simp only [kcNeed] at hokw hokc hokd
  have hfits : ∀ a : ℕ, a ≤ lenH k * x.U + lenH k + x.n ^ numFixed k + x.n + k + 1 →
      (a : ℤ) ≤ lim.word :=
    fun a ha => le_trans (by exact_mod_cast (by omega)) hokw
  obtain ⟨-, -, -, hAt3⟩ := matH_places k x.n fr
  refine Ends.asFrame hσ.locals ?_
  unfold kcRound roundT
  -- buildH k
  refine Ends.pieceToThen [Row, Col, Place, Entry] (buildH_spec hk x hpre
    ⟨hw, by omega, hfits _ (by omega)⟩ hF (by constructor <;> rfl) hσ.kept hσ.choice) ?_
  rintro loc₃ μ₃ B
  -- Answer := the answer of the solver: has H a triangle of weight zero?
  have hneed : (r (x.n ^ width k) (lenH k * x.U)).Ok lim (matH k x.n fr 3) (d + 1) :=
    ⟨le_trans (by exact_mod_cast (by omega)) hokw, by omega, hw, by omega⟩
  have hlen := hfits (lenH k) (by omega)
  have hbound : (lenH k : ℤ) * x.U ≤ lim.word := by exact_mod_cast hfits (lenH k * x.U) (by omega)
  refine Ends.callToThen (T' := T (x.n ^ width k) (lenH k * x.U))
    (hsol.meets R (triInstOf k x.n x.U fr μ₃) _ B.pre hneed) ?_
    (by simp [etTask, triInstOf, hlen, hbound])
  rintro res μ₄ ⟨hres, hK₄⟩
  -- the answer is noted; the solver has changed nothing below its free pointer
  light_piece (noteAnswer_spec hpre.n_pos ⟨hw, hfits _ (by omega), by omega⟩ (hfits _ (by omega))
    ⟨LocalsBut.of_eq (by simp), fun a ha => (hK₄ a (by omega)).trans (B.kept a ha),
      fun p hp => (hK₄ _ (by omega)).trans (B.choice p hp)⟩ ?_)
  exact hres.trans ((congrArg (fun G : TriangleInstance ℤ (x.n ^ width k) => flag G.HasZeroTriangle)
    B.graph).trans (flag_congr ⟨fun h => ⟨hF, h⟩, fun ⟨_, h⟩ => h⟩))

/-- **The host solves Zero-Weight k-Clique.** -/
theorem kc_spec (hsol : Solves etTask P₀ pe T r) (hk : 3 ≤ k) (lim : Limits) (d : ℕ) (x : KcInst k)
    (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr) (hok : (kcNeed k r x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (kcBody k pe) ⟨frame [(x.n : ℤ), x.U, x.g, fr], μ⟩
      (kcTime k T x.n x.U) fun σ' =>
      σ'.loc 0 = flag x.G.HasZeroClique ∧ Kept μ σ'.mem fr := by
  have hw := hok.space
  have hokw := hok.word
  have hokc := hok.cells
  simp only [kcNeed] at hokw hokc
  have hfits : ∀ a : ℕ, a ≤ x.n ^ numFixed k + k + 1 → (a : ℤ) ≤ lim.word :=
    fun a ha => le_trans (by exact_mod_cast (by omega)) hokw
  obtain ⟨-, -, -, hAt3⟩ := matH_places k x.n fr
  unfold kcBody kcTime
  -- Choice := fr; hostSetup k; Found := 0
  light_set fr
  light_piece (hostSetup_spec (k := k) (n := x.n) (fr := fr) rfl rfl hpre.n_pos hw
    (by omega) (hfits _ (by omega))) with ⟨_, μ₁⟩ ⟨rfl, hvt, hout⟩
  rw [updateLocals_frame]
  have h0 := hfits 0 (by omega)
  light_set 0
  -- while Round < Rounds: the rounds for the n^t choices
  refine Ends.next _ (Ends.whileConst (KcInv x μ fr) (x.n ^ numFixed k) (roundT k T x.n x.U)
    ?start ?round ?done le_rfl) (by simp; ring_nf; omega)
  case start =>
    exact ⟨LocalsBut.of_eq (by simp [flag_of_not]), fun a ha => hout a (Or.inl ha), hvt⟩
  case round =>
    intro F σ hF hσ
    have hround : σ.loc Round = F := hσ.locals Round (by decide)
    have hrounds : σ.loc Rounds = (x.n ^ numFixed k : ℕ) := hσ.locals Rounds (by decide)
    exact ⟨⟨trivial, trivial⟩, by
      simp only [Cond.Holds, Expr.val, hround, hrounds]
      exact_mod_cast hF, kcRound_spec hsol hk hpre hok hF hσ⟩
  case done =>
    -- the result
    intro σ hσ
    have hround : σ.loc Round = (x.n ^ numFixed k : ℕ) := hσ.locals Round (by decide)
    have hrounds : σ.loc Rounds = (x.n ^ numFixed k : ℕ) := hσ.locals Rounds (by decide)
    refine ⟨⟨trivial, trivial⟩, by simp [hround, hrounds], Ends.setLast ⟨?_, hσ.kept⟩⟩
    simp only [Expr.val, Function.update_self]
    exact (hσ.locals Found (by decide)).trans (flag_congr (hasZeroClique_iff x).symm)

end host

/-! ## The host, in the form that all hosts have -/

/-- The need of the host is polynomially bounded if the need of the solver is. -/
theorem polyNeed_kcNeed (k : ℕ) {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (kcNeed k r) := by
  unfold kcNeed
  poly_need [hr.word, hr.cells, hr.depth]

/-- **Zero-Weight k-Clique from Exact Triangle** (Corollary 39): the host makes a solver of
Zero-Weight k-Clique from every solver of Exact Triangle. -/
theorem isHost_kc {k : ℕ} (hk : 3 ≤ k) : IsHost etTask (kcTask k) (kcTime k) (kcNeed k) := by
  refine ⟨fun P p T r hsol => ?_, fun r hr => polyNeed_kcNeed k hr⟩
  refine ⟨[kcBody k p], P.length, kcBody k p, by simp, ?_⟩
  intro R lim d x μ fr hpre hok
  rw [List.append_assoc]
  exact kc_spec hsol hk lim d x μ fr hpre hok

end Light.Sec5
