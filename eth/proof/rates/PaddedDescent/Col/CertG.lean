/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.CertNet

/-! Certificates (`PolyT`) for the test `goodG` and the rebalancing `rebalG`, jointly in the pad, K,
g and the label length β (data, in unary) and the context.
They follow the certificates of `goodB` and `rebalF` in `PaddedDescent/F/CertNet.lean`. -/

public section

namespace PaddedDescent.F.CertNet

open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F

variable {α : Type} [Enc α] {C : Type} [Enc C] {Np : PNet C}

/-- The test `goodG` is polynomial-time, jointly in K and g (in unary), the label length and the
colouring. -/
theorem goodG2 (h : KeepsU Np) {K g b : α → ℕ} {cx : α → C × ℕ} (hK : Unary K) (hg : Unary g) (hb : PolyT b) (hc : PolyT cx) :
    PolyT fun t => goodG (K t) (g t) Np (b t) (cx t) := by
  have hKp := hK.poly
  have hgp := hg.poly
  have h1 : PolyT fun t => (List.range (K t)).all fun G =>
      decide (K t * (members (K t) (g t) (cx t).2 G).length < 2 * g t) := by fun_prop
  have hb' : PolyT fun q : (α × ℕ) × ℕ => b q.1.1 := by fun_prop
  have hl : PolyT fun q : (α × ℕ) × ℕ => lbLen (K q.1.1) (g q.1.1) Np (cx q.1.1).1 (cx q.1.1).2 q.1.2 q.2 :=
    lbLen2 h (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : PolyT fun t => (List.range (K t)).all fun G => (List.range (K t)).all fun G' =>
      G == G' || decide (lbLen (K t) (g t) Np (cx t).1 (cx t).2 G G' ≤ b t) :=
    PolyT.all (f := fun t G => (List.range (K t)).all fun G' =>
        G == G' || decide (lbLen (K t) (g t) Np (cx t).1 (cx t).2 G G' ≤ b t))
      (PolyT.all (f := fun (q : α × ℕ) G' =>
          q.2 == G' || decide (lbLen (K q.1) (g q.1) Np (cx q.1).1 (cx q.1).2 q.2 G' ≤ b q.1))
        (PolyT.or' (by fun_prop) (PolyT.decide_le hl hb')) (by fun_prop)) (by fun_prop)
  unfold goodG
  exact PolyT.and' h1 h2

/-- `rebalG` is polynomial-time, jointly in the pad, in K, g and the label length (in unary), and in
the context. -/
theorem rebalG_polyT {F : FNet C} (hF : FKeeps F) {pad : α → U} {K g b : α → ℕ} {c : α → C} (hp : PolyT pad) (hK : Unary K)
    (hg : Unary g) (hb : Unary b) (hc : PolyT c) : PolyT fun t => rebalG (pad t) (K t) (g t) (b t) F (c t) := by
  have h := keepsU hF
  have := hK.poly
  have := hg.poly
  have := hb.poly
  have hbU : Unary fun p : α × ℕ => b p.1 := by fun_prop
  have hr : PolyT fun p : α × ℕ => List.replicate (b p.1) () := hbU
  have hm : PolyT fun p : (α × ℕ) × IQ => mergedF (pad p.1.1) (K p.1.1) (g p.1.1) F ((c p.1.1, p.1.2), p.2) :=
    mergedF_polyT hF (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have ht : PolyT fun p : α × ℕ => tabulate (pad p.1) (K p.1) (b p.1)
      fun q => mergedF (pad p.1) (K p.1) (g p.1) F ((c p.1, p.2), q) :=
    tabulate_polyT (F := fun (p : α × ℕ) q => mergedF (pad p.1) (K p.1) (g p.1) F ((c p.1, p.2), q))
      (by fun_prop) (by fun_prop) hbU hm
  have hgood : PolyT fun p : α × ℕ => goodG (K p.1) (g p.1) F.toP (b p.1) (c p.1, p.2) :=
    goodG2 h (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold rebalG; fun_prop

end PaddedDescent.F.CertNet

namespace PaddedDescent.F

/-- The statement `StCertRebalG` holds: `rebalG` is polynomial-time, by `CertNet.rebalG_polyT`. -/
theorem certRebalG : StCertRebalG := fun _ _ _ hF _ _ _ _ _ _ _ hp hK hg hb hc => CertNet.rebalG_polyT hF hp hK hg hb hc

end PaddedDescent.F
