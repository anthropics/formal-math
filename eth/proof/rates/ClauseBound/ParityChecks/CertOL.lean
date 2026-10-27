/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.CertPar
public import ClauseBound.ParityChecks.CertNum
public import ClauseBound.TopN.Cert

/-! # Certificates for the count through parity checks

The program of proof/rates/ClauseBound/ParityChecks/ProgDefs.lean is polynomial-time (PolyT) in the
pad, the index of the clique solver, the numbers n and Δ in unary and the formula: the numbers of
marks that a profile
prescribes (`tl`), the weight of a profile (`GW`), the clauses of the incidences (`incL`), one
evaluation (`evW`), the two functions that the choice of the checks asks (`orcA`, `orcB`), the
choice of the
checks (`runToF`, `runF`, folds whose state the pad cuts off after every round) and the count
(`countOL`). The end is `stCertCountOL`, the interface statement `StCertCountOL`.

The certificates of the value of a network through the solver, of the network of marks and of the
test for admissible profiles are hypotheses, as in proof/rates/ClauseBound/TopN/Cert.lean. The
certificate of one
decision (`StDec`, proved below from a lemma of proof/rates/ClauseBound/ParityChecks/CertNum.lean)
asks for the number of the clause in unary. In the loop over the clauses 0, …, e − 1 that number is
replaced by its minimum with e, which
changes nothing. -/

public section

namespace ClauseBound.ParityChecks.CertOL

open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar

variable {α : Type} [Enc α]

/-- One decision is polynomial-time, for the number of the clause in unary and any two
polynomial-time functions in the place of the sums over marks. -/
@[expose] def StDec : Prop := ∀ (α : Type) [Enc α] (q : α → Par), QU q → ∀ (oA : α → List Chk → ℤ) (oB : α → List Chk → Chk → ℕ → ℕ → ℤ) (Ls : α → List Chk)
  (cur : α → Chk) (e : α → ℕ), (PolyT fun p : α × List Chk => oA p.1 p.2) → (PolyT fun p : α × List Chk × Chk × ℕ × ℕ => oB p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) →
  PolyT Ls → PolyT cur → Unary e → PolyT fun x => (q x).decide1 (oA x) (oB x) (Ls x) (cur x) (e x)

/-! ### The weight of a profile and the clauses of the incidences -/

/-- The number of marks that a profile prescribes for a layer is given in unary, for the number of
nodes in unary. -/
theorem tl_unary {g y i : α → ℕ} {Ls : α → List Fml} (hg : Unary g) (hL : PolyT Ls) (hy : PolyT y) (hi : PolyT i) :
    Unary fun x => tl (g x) (Ls x) (y x) (i x) :=
  unary_sum_map (f := fun x a => mu (g x) (Ls x) (y x) a a (i x))
    (Mark.Cert.mu_unary (PolyT.comp hg.poly PolyT.id'.fst) (PolyT.comp hL PolyT.id'.fst) (PolyT.comp hy PolyT.id'.fst) PolyT.id'.snd PolyT.id'.snd
      (PolyT.comp hi PolyT.id'.fst)) (PolyT.range hg)

/-- The weight of a profile is polynomial-time, for the number of layers and the numbers of marks in
unary. -/
theorem GW_polyT {R : α → ℕ} {ws : α → List ℤ} {lo hi : α → List ℕ} {t : α → ℕ → ℕ} (hR : Unary R) (hws : PolyT ws) (hlo : PolyT lo) (hhi : PolyT hi)
    (ht : Unary fun p : α × ℕ => t p.1 p.2) : PolyT fun x => GW (R x) (ws x) (lo x) (hi x) (t x) := by
  have hj : PolyT fun p : α × ℕ => min p.2 (R p.1) := PolyT.min' PolyT.id'.snd (PolyT.comp hR.poly PolyT.id'.fst)
  have htj : Unary fun p : α × ℕ => t p.1 (min p.2 (R p.1)) := ht.comp (h := fun p : α × ℕ => (p.1, min p.2 (R p.1))) (PolyT.prodMk PolyT.id'.fst hj)
  have hl : PolyT fun p : α × ℕ => (lo p.1).getD (min p.2 (R p.1)) 0 := PolyT.getD (PolyT.comp hlo PolyT.id'.fst) hj (PolyT.const 0)
  have hh : PolyT fun p : α × ℕ => (hi p.1).getD (min p.2 (R p.1)) 0 := PolyT.getD (PolyT.comp hhi PolyT.id'.fst) hj (PolyT.const 0)
  have hw : PolyT fun p : α × ℕ => (ws p.1).getD (min p.2 (R p.1)) 0 := PolyT.getD (PolyT.comp hws PolyT.id'.fst) hj (PolyT.const 0)
  have hs : PolyT fun p : α × ℕ => if min p.2 (R p.1) = 0 then (1 : ℤ) else -1 :=
    PolyT.ite' (PolyT.decide_eq hj (PolyT.const 0)) (PolyT.const 1) (PolyT.const (-1))
  unfold GW
  exact prod_range_polyT (f := fun x i => if (lo x).getD i 0 ≤ t x i ∧ t x i ≤ (hi x).getD i 0 then ((ws x).getD i 0 * (if i = 0 then 1 else -1)) ^ t x i else 0) hR
    (PolyT.ite' (PolyT.decide_and (PolyT.decide_le hl htj.poly) (PolyT.decide_le htj.poly hh)) (powZ_polyT (PolyT.mulZ hw hs) htj) (PolyT.const 0))

/-- The clauses of the incidences are polynomial-time, for the number of complete checks in unary. -/
theorem incL_polyT {n j : α → ℕ} {ψ : α → Fml} {Lam : α → List (List ℕ)} (hn : PolyT n) (hψ : PolyT ψ) (hLam : PolyT Lam) (hj : Unary j) :
    PolyT fun x => incL (n x) (ψ x) (Lam x) (j x) := by
  have h1 : PolyT fun r : (α × ℕ) × ℕ => (ψ r.1.1).getD r.2 [] ++ [(n r.1.1 + r.1.2, false)] :=
    PolyT.append (PolyT.getD (PolyT.comp hψ PolyT.id'.fst.fst) PolyT.id'.snd (PolyT.const []))
      (PolyT.cons' (PolyT.prodMk (PolyT.add (PolyT.comp hn PolyT.id'.fst.fst) PolyT.id'.fst.snd) (PolyT.const false)) (PolyT.const []))
  have h2 : PolyT fun p : α × ℕ => ((Lam p.1).getD p.2 []).map fun e => (ψ p.1).getD e [] ++ [(n p.1 + p.2, false)] :=
    PolyT.map (f := fun (p : α × ℕ) e => (ψ p.1).getD e [] ++ [(n p.1 + p.2, false)]) h1 (PolyT.getD (PolyT.comp hLam PolyT.id'.fst) PolyT.id'.snd (PolyT.const []))
  have h3 : PolyT fun x => ((Lam x).getD (j x) []).map fun e => (ψ x).getD e [] :=
    PolyT.map (f := fun x e => (ψ x).getD e []) (PolyT.getD (PolyT.comp hψ PolyT.id'.fst) PolyT.id'.snd (PolyT.const [])) (PolyT.getD hLam hj.poly (PolyT.const []))
  unfold incL
  exact PolyT.append (PolyT.flatMap (f := fun x j' => ((Lam x).getD j' []).map fun e => (ψ x).getD e [] ++ [(n x + j', false)]) h2 (PolyT.range hj)) h3

/-! ### The program -/

section
variable {Idx : Type} [Enc Idx] {S : Solver Idx}

/-- What the program reads from the context: the pad and the index are polynomial-time, n and Δ are
given in unary, and the parameters `q` satisfy `QU`. -/
structure CU (pad : α → U) (i : α → Idx) (n Δ : α → ℕ) (q : α → Par) : Prop where
  pad : PolyT pad
  i : PolyT i
  n : Unary n
  Δ : Unary Δ
  q : QU q

/-- The property passes to a polynomial-time change of the context. -/
theorem CU.comp {β : Type} [Enc β] {pad : α → U} {i : α → Idx} {n Δ : α → ℕ} {q : α → Par} (h : CU pad i n Δ q) {g : β → α} (hg : PolyT g) :
    CU (fun y => pad (g y)) (fun y => i (g y)) (fun y => n (g y)) (fun y => Δ (g y)) (fun y => q (g y)) :=
  ⟨PolyT.comp h.pad hg, PolyT.comp h.i hg, h.n.comp hg, h.Δ.comp hg, h.q.comp hg⟩

/-- The certificates that come from elsewhere. -/
structure Given (S : Solver Idx) : Prop where
  val : StCertValS
  mark : StCertMark
  adm : StCertAdm
  dec : StDec
  poly : S.Poly

variable (G : Given S) (k : ℕ) {pad : α → U} {i : α → Idx} {n Δ : α → ℕ} {q : α → Par} (hc : CU pad i n Δ q)
include G hc

/-- One evaluation is polynomial-time. -/
theorem evW_polyT {ws : α → List ℤ} {lo hi : α → List ℕ} {Ls : α → List Fml} (hws : PolyT ws) (hlo : PolyT lo) (hhi : PolyT hi) (hL : PolyT Ls) :
    PolyT fun x => evW S k (pad x) (i x) (n x) (Δ x) (q x) (ws x) (lo x) (hi x) (Ls x) := by
  have hK : Unary fun x => S.K (i x) := G.poly.K.comp hc.i
  have hc' := hc.comp (β := α × MCtx) PolyT.id'.fst
  have hK' : Unary fun r : α × MCtx => S.K (i r.1) := hK.comp PolyT.id'.fst
  have hgw : PolyT fun r : α × MCtx => GW r.2.2.1.length (ws r.1) (lo r.1) (hi r.1) (tl r.2.1.1.length r.2.2.1 r.2.2.2) :=
    GW_polyT (t := fun (r : α × MCtx) j => tl r.2.1.1.length r.2.2.1 r.2.2.2 j) (Unary.of_length PolyT.id'.snd.snd.fst) (PolyT.comp hws PolyT.id'.fst)
      (PolyT.comp hlo PolyT.id'.fst) (PolyT.comp hhi PolyT.id'.fst)
      (tl_unary (Unary.of_length PolyT.id'.fst.snd.fst.fst) PolyT.id'.fst.snd.snd.fst PolyT.id'.fst.snd.snd.snd PolyT.id'.snd)
  have hv : PolyT fun r : α × MCtx => valS S (pad r.1) (i r.1) (UbOL k (S.K (i r.1)) (n r.1) (Δ r.1)) (PbOL (S.K (i r.1)) (n r.1) (Δ r.1)) markF r.2 :=
    G.val Idx S G.poly MCtx markF G.mark (α × MCtx) _ _ _ _ _ hc'.pad hc'.i (UbOL_unary k hK' hc'.n hc'.Δ) (PbOL_unary hK' hc'.n hc'.Δ) PolyT.id'.snd
  unfold evW
  exact ClauseBound.TopN.Cert.evalV_polyT (gu := fun x => rep (3 * S.K (i x) ^ 8))
    (val := fun x c => GW c.2.1.length (ws x) (lo x) (hi x) (tl c.1.1.length c.2.1 c.2.2) *
      valS S (pad x) (i x) (UbOL k (S.K (i x)) (n x) (Δ x)) (PbOL (S.K (i x)) (n x) (Δ x)) markF c)
    (k + 1) G.adm hc.pad (g_unary hK) (PolyT.mulZ hgw hv) (parM_polyT hc.q hc.n hc.Δ) hL

/-- The first of the two functions that the choice of the checks asks is polynomial-time. -/
theorem orcA_polyT {ψ : α → Fml} {Ls : α → List Chk} (hψ : PolyT ψ) (hL : PolyT Ls) :
    PolyT fun x => orcA S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) (Ls x) := by
  have hnb : PolyT fun x => (q x).nb + 1 := PolyT.add hc.q.nb.poly (PolyT.const 1)
  have hlen : Unary fun x => (Ls x).length := Unary.of_length hL
  unfold orcA
  exact div_two_pow_polyT (evW_polyT G k hc (PolyT.const [1, -2]) (PolyT.cons' hnb (PolyT.const [0]))
    (PolyT.cons' hnb (PolyT.cons' (capM_unary hc.q).poly (PolyT.const [])))
    (PolyT.cons' hψ (PolyT.cons' (incL_polyT hc.n.poly hψ (PolyT.take hlen.poly hL) hlen) (PolyT.const [])))) hc.q.r

/-- The second of the two functions that the choice of the checks asks is polynomial-time. -/
theorem orcB_polyT {ψ : α → Fml} {Ls : α → List Chk} {cur : α → Chk} {e j : α → ℕ} (hψ : PolyT ψ) (hL : PolyT Ls) (hcur : PolyT cur) (he : PolyT e) (hj : PolyT j) :
    PolyT fun x => orcB S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) (Ls x) (cur x) (e x) (j x) := by
  have hnb : PolyT fun x => (q x).nb + 1 := PolyT.add hc.q.nb.poly (PolyT.const 1)
  have hlen : Unary fun x => (Ls x).length := Unary.of_length hL
  unfold orcB
  exact div_two_pow_polyT (evW_polyT G k hc (PolyT.const [1, -2, 1]) (PolyT.cons' hnb (PolyT.cons' (PolyT.const 0) (PolyT.cons' hj (PolyT.const []))))
    (PolyT.cons' hnb (PolyT.cons' (capM_unary hc.q).poly (PolyT.cons' hj (PolyT.const []))))
    (PolyT.cons' hψ (PolyT.cons' (incL_polyT hc.n.poly hψ (PolyT.append hL (PolyT.cons' hcur (PolyT.const []))) hlen)
      (PolyT.cons' (PolyT.drop he hψ) (PolyT.const []))))) hc.q.r

/-- The decisions for one check are polynomial-time, for their number in unary. -/
theorem runToF_polyT {ψ : α → Fml} {Ls : α → List Chk} {e : α → ℕ} (hψ : PolyT ψ) (hL : PolyT Ls) (he : Unary e) :
    PolyT fun x => runToF S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) (Ls x) (e x) := by
  have hc1 := hc.comp (β := α × Chk × ℕ) PolyT.id'.fst
  have hA : PolyT fun r : (α × Chk × ℕ) × List Chk => orcA S k (pad r.1.1) (i r.1.1) (n r.1.1) (Δ r.1.1) (q r.1.1) (ψ r.1.1) r.2 :=
    orcA_polyT G k (hc.comp (β := (α × Chk × ℕ) × List Chk) PolyT.id'.fst.fst) (PolyT.comp hψ PolyT.id'.fst.fst) PolyT.id'.snd
  have hB : PolyT fun r : (α × Chk × ℕ) × List Chk × Chk × ℕ × ℕ =>
      orcB S k (pad r.1.1) (i r.1.1) (n r.1.1) (Δ r.1.1) (q r.1.1) (ψ r.1.1) r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 :=
    orcB_polyT G k (hc.comp (β := (α × Chk × ℕ) × List Chk × Chk × ℕ × ℕ) PolyT.id'.fst.fst) (PolyT.comp hψ PolyT.id'.fst.fst) PolyT.id'.snd.fst PolyT.id'.snd.snd.fst
      PolyT.id'.snd.snd.snd.fst PolyT.id'.snd.snd.snd.snd
  have hd : PolyT fun p : α × Chk × ℕ => (q p.1).decide1 (orcA S k (pad p.1) (i p.1) (n p.1) (Δ p.1) (q p.1) (ψ p.1))
      (orcB S k (pad p.1) (i p.1) (n p.1) (Δ p.1) (q p.1) (ψ p.1)) (Ls p.1) p.2.1 (min p.2.2 (e p.1)) :=
    G.dec (α × Chk × ℕ) _ hc1.q (fun p => orcA S k (pad p.1) (i p.1) (n p.1) (Δ p.1) (q p.1) (ψ p.1))
      (fun p => orcB S k (pad p.1) (i p.1) (n p.1) (Δ p.1) (q p.1) (ψ p.1)) _ _ _ hA hB (PolyT.comp hL PolyT.id'.fst) PolyT.id'.snd.fst
      (unary_min_right PolyT.id'.snd.snd (he.comp PolyT.id'.fst))
  have h := foldl_cap (pad := pad) (l := fun x => List.range (e x)) (a := fun _ => ([] : Chk))
    (g := fun x cur y => (q x).decide1 (orcA S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x)) (orcB S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x)) (Ls x) cur (min y (e x)))
    [] hc.pad (PolyT.range he) (PolyT.const []) hd
  refine h.congr fun x => ?_
  unfold runToF
  exact foldl_range_min (e x) (fun cur y => cap (pad x) [] ((q x).decide1 (orcA S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x))
    (orcB S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x)) (Ls x) cur y)) _

/-- The choice of all checks is polynomial-time. -/
theorem runF_polyT {ψ : α → Fml} (hψ : PolyT ψ) : PolyT fun x => runF S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) := by
  have hc1 := hc.comp (β := α × List Chk × ℕ) PolyT.id'.fst
  have h1 : PolyT fun p : α × List Chk × ℕ => runToF S k (pad p.1) (i p.1) (n p.1) (Δ p.1) (q p.1) (ψ p.1) p.2.1 (q p.1).m :=
    runToF_polyT G k hc1 (PolyT.comp hψ PolyT.id'.fst) PolyT.id'.snd.fst hc1.q.m
  unfold runF
  exact foldl_cap (pad := pad) (l := fun x => List.range (q x).r) (a := fun _ => ([] : List Chk))
    (g := fun x Ls _ => Ls ++ [runToF S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) Ls (q x).m]) [] hc.pad (PolyT.range hc.q.r) (PolyT.const [])
    (PolyT.append PolyT.id'.snd.fst (PolyT.cons' h1 (PolyT.const [])))

/-- The count is polynomial-time. -/
theorem countOL_polyT {ψ : α → Fml} (hψ : PolyT ψ) : PolyT fun x => countOL S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) := by
  have hr := runF_polyT G k hc hψ
  unfold countOL
  exact PolyT.toNat (mod_two_pow_polyT (div_two_pow_polyT (evW_polyT G k hc (PolyT.const [-1, -2]) (PolyT.const [0, 0])
    (PolyT.cons' hc.q.nb.poly (PolyT.cons' (capM_unary hc.q).poly (PolyT.const [])))
    (PolyT.cons' hψ (PolyT.cons' (incL_polyT hc.n.poly hψ (PolyT.take hc.q.r.poly hr) hc.q.r) (PolyT.const [])))) hc.q.r) (hc.n.add (Unary.const 1)))

end

/-- The count of one sparse formula through parity checks is polynomial-time, given the certificates
of the value of a network through the solver, of the network of marks, of the test for
admissible profiles and of one decision. -/
theorem stCertCountOL_of (hV : StCertValS) (hM : StCertMark) (hA : StCertAdm) (hD : StDec) : StCertCountOL := by
  intro Idx _ S hP k
  have hn : Unary fun x : U × Idx × (U × U) × Fml => x.2.2.1.1.length := Unary.of_length PolyT.id'.snd.snd.fst.fst
  have hΔ : Unary fun x : U × Idx × (U × U) × Fml => x.2.2.1.2.length := Unary.of_length PolyT.id'.snd.snd.fst.snd
  have hm : Unary fun x : U × Idx × (U × U) × Fml => x.2.2.2.length := Unary.of_length PolyT.id'.snd.snd.snd
  exact countOL_polyT (S := S) ⟨hV, hM, hA, hD, hP⟩ k (pad := fun x : U × Idx × (U × U) × Fml => x.1) (i := fun x => x.2.1)
    ⟨PolyT.id'.fst, PolyT.id'.snd.fst, hn, hΔ, parQ_QU hn hΔ hm⟩ PolyT.id'.snd.snd.snd

/-- The certificate of one decision, in the form in which it is used here. -/
theorem stDec : StDec := fun _ _ _ hq _ _ _ _ _ hA hB hL hc he => CertNum.decide1_polyT hq hA hB hL hc he

/-- The count of one sparse formula through parity checks is polynomial-time, given the certificates
of the value of a network through the solver, of the network of marks and of the test for
admissible profiles. -/
theorem stCertCountOL (hV : StCertValS) (hM : StCertMark) (hA : StCertAdm) : StCertCountOL := stCertCountOL_of hV hM hA stDec

end ClauseBound.ParityChecks.CertOL
