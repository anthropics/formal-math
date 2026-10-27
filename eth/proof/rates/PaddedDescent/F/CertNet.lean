/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import PaddedDescent.F.FuelCert

/-! Certificates (`PolyT`) for the rebalancing on explicit data, jointly in the pad, K, g (data, in
unary), the context and the query:
the plain functions of StepMachines/Prog/NetProg.lean, `termF`, `mergedF`, `tabulate`, `rebalF`
(`StCertRebal`), and the loop over the levels
(`StCertDescend` from `StCertExpand`). -/

@[expose] public section

namespace PaddedDescent.F.CertNet

open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F

variable {α β γ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc ε]

/-! ### K, g as data -/

variable {C : Type} [Enc C] {Np : PNet C}

/-- lengths in unary -/
structure KeepsU (Np : PNet C) : Prop where
  n : Unary fun p : C × ℕ => Np.n p.1 p.2
  cap : Unary fun p : C × ℕ × ℕ => Np.cap p.1 p.2.1 p.2.2

@[fun_prop] theorem col2 {K x a : α → ℕ} (hK : PolyT K) (hx : PolyT x) (ha : PolyT a) :
    PolyT fun t => col (K t) (x t) (a t) := by unfold col; fun_prop
@[fun_prop] theorem members2 {K g x G : α → ℕ} (hK : PolyT K) (hg : Unary g) (hx : PolyT x) (hG : PolyT G) :
    PolyT fun t => members (K t) (g t) (x t) (G t) := by unfold members; fun_prop
@[fun_prop] theorem prs2 {K g x G G' : α → ℕ} (hK : PolyT K) (hg : Unary g) (hx : PolyT x) (hG : PolyT G)
    (hG' : PolyT G') : PolyT fun t => prs (K t) (g t) (x t) (G t) (G' t) := by unfold prs; fun_prop

section
variable (h : KeepsU Np)
include h

@[fun_prop] theorem nU {c : α → C} {a : α → ℕ} (hc : PolyT c) (ha : PolyT a) : Unary fun t => Np.n (c t) (a t) :=
  h.n.comp (h := fun t => (c t, a t)) (by fun_prop)
@[fun_prop] theorem capU {c : α → C} {a b : α → ℕ} (hc : PolyT c) (ha : PolyT a) (hb : PolyT b) :
    Unary fun t => Np.cap (c t) (a t) (b t) := h.cap.comp (h := fun t => (c t, a t, b t)) (by fun_prop)
@[fun_prop] theorem nP {c : α → C} {a : α → ℕ} (hc : PolyT c) (ha : PolyT a) : PolyT fun t => Np.n (c t) (a t) :=
  (nU h hc ha).poly
@[fun_prop] theorem capP {c : α → C} {a b : α → ℕ} (hc : PolyT c) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun t => Np.cap (c t) (a t) (b t) := (capU h hc ha hb).poly

@[fun_prop] theorem stLens2 {K g x G : α → ℕ} {c : α → C} (hK : PolyT K) (hg : Unary g) (hc : PolyT c) (hx : PolyT x)
    (hG : PolyT G) : PolyT fun t => stLens (K t) (g t) Np (c t) (x t) (G t) := by
  unfold stLens; fun_prop (disch := assumption)
@[fun_prop] theorem stLenU {K g x G : α → ℕ} {c : α → C} (hK : PolyT K) (hg : Unary g) (hc : PolyT c) (hx : PolyT x)
    (hG : PolyT G) : Unary fun t => stLen (K t) (g t) Np (c t) (x t) (G t) := by
  unfold stLen stLens; fun_prop (disch := assumption)
@[fun_prop] theorem zAt2 {K g x G a : α → ℕ} {c : α → C} {z : α → List Bool} (hK : PolyT K) (hg : Unary g) (hc : PolyT c)
    (hx : PolyT x) (hG : PolyT G) (hz : PolyT z) (ha : PolyT a) :
    PolyT fun t => zAt (K t) (g t) Np (c t) (x t) (G t) (z t) (a t) := by
  unfold zAt; fun_prop (disch := assumption)
@[fun_prop] theorem lbLens2 {K g x G G' : α → ℕ} {c : α → C} (hK : PolyT K) (hg : Unary g) (hc : PolyT c) (hx : PolyT x)
    (hG : PolyT G) (hG' : PolyT G') : PolyT fun t => lbLens (K t) (g t) Np (c t) (x t) (G t) (G' t) := by
  unfold lbLens; fun_prop (disch := assumption)
@[fun_prop] theorem lbLen2 {K g x G G' : α → ℕ} {c : α → C} (hK : PolyT K) (hg : Unary g) (hc : PolyT c) (hx : PolyT x)
    (hG : PolyT G) (hG' : PolyT G') : PolyT fun t => lbLen (K t) (g t) Np (c t) (x t) (G t) (G' t) := by
  unfold lbLen; fun_prop (disch := assumption)
@[fun_prop] theorem lAt2 {K g x G G' : α → ℕ} {c : α → C} {θ : α → List Bool} {p : α → ℕ × ℕ} (hK : PolyT K) (hg : Unary g)
    (hc : PolyT c) (hx : PolyT x) (hG : PolyT G) (hG' : PolyT G') (hθ : PolyT θ) (hp : PolyT p) :
    PolyT fun t => lAt (K t) (g t) Np (c t) (x t) (G t) (G' t) (θ t) (p t) := by
  unfold lAt; fun_prop (disch := assumption)
@[fun_prop] theorem validB2 {K g : α → ℕ} {u : α → X0 C} (hK : Unary K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => validB (K t) (g t) Np (u t) := by
  have := hK.poly
  unfold validB; fun_prop (disch := assumption)
@[fun_prop] theorem zOf2 {K g : α → ℕ} {u : α → X0 C × ℕ} (hK : PolyT K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => zOf (K t) (g t) Np (u t) := by
  unfold zOf; fun_prop (disch := assumption)
@[fun_prop] theorem zA2 {K g a : α → ℕ} {u : α → X0 C × ℕ} (hK : PolyT K) (hg : Unary g) (hu : PolyT u) (ha : PolyT a) :
    PolyT fun t => zA (K t) (g t) Np (u t) (a t) := by
  unfold zA; fun_prop (disch := assumption)
@[fun_prop] theorem labOf2 {K g a b : α → ℕ} {u : α → X0 C} (hK : PolyT K) (hg : Unary g) (hu : PolyT u) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun t => labOf (K t) (g t) Np (u t) (a t) (b t) := by
  unfold labOf; fun_prop (disch := assumption)
@[fun_prop] theorem qW2 {K g : α → ℕ} {u : α → (X0 C × ℕ) × ℕ} (hK : PolyT K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => qW (K t) (g t) Np (u t) := by
  have := hg.poly
  unfold qW; fun_prop (disch := assumption)
@[fun_prop] theorem qF2 {K g : α → ℕ} {u : α → (X0 C × ℕ) × ℕ} (hK : PolyT K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => qF (K t) (g t) Np (u t) := by
  have := hg.poly
  unfold qF; fun_prop (disch := assumption)
@[fun_prop] theorem qP12 {K g : α → ℕ} {u : α → ((X0 C × ℕ) × ℕ) × ℕ} (hK : PolyT K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => qP1 (K t) (g t) Np (u t) := by
  have := hg.poly
  unfold qP1; fun_prop (disch := assumption)
@[fun_prop] theorem qP22 {K g : α → ℕ} {u : α → ((X0 C × ℕ) × ℕ) × ℕ} (hK : PolyT K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => qP2 (K t) (g t) Np (u t) := by
  have := hg.poly
  unfold qP2; fun_prop (disch := assumption)
@[fun_prop] theorem nLab2 {g : α → ℕ} {u : α → (X0 C × ℕ) × ℕ} (hg : PolyT g) (hu : PolyT u) :
    PolyT fun t => nLab (g t) Np (u t) := by
  unfold nLab; fun_prop (disch := assumption)
@[fun_prop] theorem nStates2 {K g : α → ℕ} {u : α → X0 C} (hK : PolyT K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => nStates (K t) (g t) Np (u t) := by
  unfold nStates; fun_prop (disch := assumption)

end

@[fun_prop] theorem isOne2 {K g : α → ℕ} {u : α → (X0 C × ℕ) × ℕ} (hK : PolyT K) (hg : PolyT g) (hu : PolyT u) :
    PolyT fun t => isOne (K t) (g t) (u t) := by unfold isOne; fun_prop
@[fun_prop] theorem isW2 {g : α → ℕ} {u : α → (X0 C × ℕ) × ℕ} (hg : PolyT g) (hu : PolyT u) :
    PolyT fun t => isW (g t) (u t) := by unfold isW; fun_prop
@[fun_prop] theorem isPsi2 {K g : α → ℕ} {u : α → (X0 C × ℕ) × ℕ} (hK : PolyT K) (hg : PolyT g) (hu : PolyT u) :
    PolyT fun t => isPsi (K t) (g t) (u t) := by unfold isPsi; fun_prop

section
variable (h : KeepsU Np)
include h

@[fun_prop] theorem rowSumU {g a : α → ℕ} {c : α → C} (hg : Unary g) (hc : PolyT c) (ha : PolyT a) :
    Unary fun t => rowSum (g t) Np (c t) (a t) := by
  unfold rowSum; fun_prop (disch := assumption)
@[fun_prop] theorem UcU {g : α → ℕ} {c : α → C} (hg : Unary g) (hc : PolyT c) : Unary fun t => Uc (g t) Np (c t) := by
  unfold Uc; fun_prop (disch := assumption)
@[fun_prop] theorem Pc2 {g : α → ℕ} {c : α → C} (hg : Unary g) (hc : PolyT c) : PolyT fun t => Pc (g t) Np (c t) := by
  have h1 : PolyT fun p : α × ℕ => rowSum (g p.1) Np (c p.1) p.2 :=
    (rowSumU h (g := fun p : α × ℕ => g p.1) (c := fun p => c p.1) (a := fun p => p.2) (by fun_prop) (by fun_prop) (by fun_prop)).poly
  exact foldr_max_polyT (l := fun t => (List.range (g t)).map (rowSum (g t) Np (c t))) (by fun_prop)
@[fun_prop] theorem betaC2 {K g : α → ℕ} {c : α → C} (hK : PolyT K) (hg : Unary g) (hc : PolyT c) :
    PolyT fun t => betaC (K t) (g t) Np (c t) := by
  have := hg.poly
  have := (UcU h hg hc).poly
  unfold betaC Colouring.beta; fun_prop (disch := assumption)
@[fun_prop] theorem betaCU {K g : α → ℕ} {c : α → C} (hK : Unary K) (hg : Unary g) (hc : PolyT c) :
    Unary fun t => betaC (K t) (g t) Np (c t) := by
  have hU := UcU h hg hc
  refine Unary.of_le (g := fun t => 1 + (K t * Uc (g t) Np (c t) + g t * Uc (g t) Np (c t))) (by fun_prop)
    (betaC2 h hK.poly hg hc) fun t => ?_
  have h1 := Pc_le_Uc (g t) Np (c t)
  have h2 : (K t * Uc (g t) Np (c t) + g t * Pc (g t) Np (c t)) / K t ^ 3 ≤ K t * Uc (g t) Np (c t) + g t * Pc (g t) Np (c t) :=
    Nat.div_le_self _ _
  have h3 := Nat.mul_le_mul_left (g t) h1
  unfold betaC Colouring.beta
  omega
@[fun_prop] theorem goodB2 {K g : α → ℕ} {cx : α → C × ℕ} (hK : Unary K) (hg : Unary g) (hc : PolyT cx) :
    PolyT fun t => goodB (K t) (g t) Np (cx t) := by
  have hKp := hK.poly
  have hgp := hg.poly
  have h1 : PolyT fun t => (List.range (K t)).all fun G =>
      decide (K t * (members (K t) (g t) (cx t).2 G).length < 2 * g t) := by fun_prop
  have hb : PolyT fun q : (α × ℕ) × ℕ => betaC (K q.1.1) (g q.1.1) Np (cx q.1.1).1 :=
    betaC2 h (by fun_prop) (by fun_prop) (by fun_prop)
  have hl : PolyT fun q : (α × ℕ) × ℕ => lbLen (K q.1.1) (g q.1.1) Np (cx q.1.1).1 (cx q.1.1).2 q.1.2 q.2 :=
    lbLen2 h (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : PolyT fun t => (List.range (K t)).all fun G => (List.range (K t)).all fun G' =>
      G == G' || decide (lbLen (K t) (g t) Np (cx t).1 (cx t).2 G G' ≤ betaC (K t) (g t) Np (cx t).1) :=
    PolyT.all (f := fun t G => (List.range (K t)).all fun G' =>
        G == G' || decide (lbLen (K t) (g t) Np (cx t).1 (cx t).2 G G' ≤ betaC (K t) (g t) Np (cx t).1))
      (PolyT.all (f := fun (q : α × ℕ) G' =>
          q.2 == G' || decide (lbLen (K q.1) (g q.1) Np (cx q.1).1 (cx q.1).2 q.2 G' ≤ betaC (K q.1) (g q.1) Np (cx q.1).1))
        (PolyT.or' (by fun_prop) (PolyT.decide_le hl hb)) (by fun_prop)) (by fun_prop)
  unfold goodB
  exact PolyT.and' h1 h2

end


@[fun_prop] theorem look_polyT {T : α → Tab} {q : α → IQ} (hT : PolyT T) (hq : PolyT q) :
    PolyT fun t => look (T t) (q t) := by unfold look; fun_prop

theorem tabulate_polyT {pad : α → U} {K ℓ : α → ℕ} {F : α → IQ → ℤ} (hp : PolyT pad) (hK : Unary K) (hℓ : Unary ℓ)
    (hF : PolyT fun p : α × IQ => F p.1 p.2) : PolyT fun t => tabulate (pad t) (K t) (ℓ t) (F t) := by
  have := hK.poly
  have := hℓ.poly
  have hF' : PolyT fun q : (α × ℕ) × ℕ => F q.1.1 (q.1.2, unflat (K q.1.1) (ℓ q.1.1) q.1.2
      (toWord ((K q.1.1 - 1) * ℓ q.1.1) q.2)) := by
    refine PolyT.comp₂ hF (by fun_prop) ?_
    unfold unflat block; fun_prop
  unfold tabulate
  exact PolyT.map (f := fun t v => (rng (pad t) (2 ^ ((K t - 1) * ℓ t))).map fun i =>
      F t (v, unflat (K t) (ℓ t) v (toWord ((K t - 1) * ℓ t) i)))
    (PolyT.map (f := fun (q : α × ℕ) i => F q.1 (q.2, unflat (K q.1) (ℓ q.1) q.2 (toWord ((K q.1 - 1) * ℓ q.1) i)))
      hF' (by fun_prop)) (by fun_prop)

theorem keepsU {F : FNet C} (hF : FKeeps F) : KeepsU F.toP := ⟨hF.n, hF.cap⟩

theorem termF_polyT {F : FNet C} (hF : FKeeps F) {pad : α → U} {K g : α → ℕ} {u : α → (X0 C × ℕ) × ℕ}
    (hp : PolyT pad) (hK : PolyT K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => termF (pad t) (K t) (g t) F (u t) := by
  have h := keepsU hF
  have hW := hF.W
  have hf := hF.f
  have hg' := hg.poly
  have h1 : PolyT fun p : α × ℕ => F.f (qP1 (K p.1) (g p.1) F.toP (u p.1, p.2)) * F.f (qP2 (K p.1) (g p.1) F.toP (u p.1, p.2)) :=
    PolyT.mulZ (PolyT.comp hf (qP12 h (by fun_prop) (by fun_prop) (by fun_prop)))
      (PolyT.comp hf (qP22 h (by fun_prop) (by fun_prop) (by fun_prop)))
  have h2 : PolyT fun t => sumF (nLab (g t) F.toP (u t)) (pad t)
      fun y => F.f (qP1 (K t) (g t) F.toP (u t, y)) * F.f (qP2 (K t) (g t) F.toP (u t, y)) :=
    sumF_polyT (nLab2 h hg' hu) hp h1
  have h3 : PolyT fun t => F.W (qW (K t) (g t) F.toP (u t)) := PolyT.comp hW (qW2 h hK hg hu)
  have h4 : PolyT fun t => F.f (qF (K t) (g t) F.toP (u t)) := PolyT.comp hf (qF2 h hK hg hu)
  unfold termF
  fun_prop

theorem mergedF_polyT {F : FNet C} (hF : FKeeps F) {pad : α → U} {K g : α → ℕ} {u : α → X0 C}
    (hp : PolyT pad) (hK : Unary K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => mergedF (pad t) (K t) (g t) F (u t) := by
  have h := keepsU hF
  have hK' := hK.poly
  have h1 : PolyT fun q : (α × ℕ) × ℕ => termF (pad q.1.1) (K q.1.1) (g q.1.1) F ((u q.1.1, q.1.2), q.2) :=
    termF_polyT hF (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : PolyT fun p : α × ℕ => prodL (g p.1 * g p.1) fun i => termF (pad p.1) (K p.1) (g p.1) F ((u p.1, p.2), i) :=
    prodL_polyT (by fun_prop) h1
  have h3 : PolyT fun t => sumF (nStates (K t) (g t) F.toP (u t)) (pad t)
      fun y => prodL (g t * g t) fun i => termF (pad t) (K t) (g t) F ((u t, y), i) :=
    sumF_polyT (nStates2 h hK' hg hu) hp h2
  have h4 := validB2 h hK hg hu
  unfold mergedF
  fun_prop

theorem rebalF_polyT {F : FNet C} (hF : FKeeps F) {pad : α → U} {K g : α → ℕ} {c : α → C} (hp : PolyT pad) (hK : Unary K)
    (hg : Unary g) (hc : PolyT c) : PolyT fun t => rebalF (pad t) (K t) (g t) F (c t) := by
  have h := keepsU hF
  have := hK.poly
  have := hg.poly
  have hb : PolyT fun p : α × ℕ => List.replicate (betaC (K p.1) (g p.1) F.toP (c p.1)) () :=
    betaCU h (K := fun p : α × ℕ => K p.1) (g := fun p => g p.1) (c := fun p => c p.1) (by fun_prop) (by fun_prop) (by fun_prop)
  have hm : PolyT fun p : (α × ℕ) × IQ => mergedF (pad p.1.1) (K p.1.1) (g p.1.1) F ((c p.1.1, p.1.2), p.2) :=
    mergedF_polyT hF (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have ht : PolyT fun p : α × ℕ => tabulate (pad p.1) (K p.1) (betaC (K p.1) (g p.1) F.toP (c p.1))
      fun q => mergedF (pad p.1) (K p.1) (g p.1) F ((c p.1, p.2), q) :=
    tabulate_polyT (F := fun (p : α × ℕ) q => mergedF (pad p.1) (K p.1) (g p.1) F ((c p.1, p.2), q))
      (by fun_prop) (by fun_prop)
      (betaCU h (K := fun p : α × ℕ => K p.1) (g := fun p => g p.1) (c := fun p => c p.1) (by fun_prop) (by fun_prop) (by fun_prop)) hm
  have hgood : PolyT fun p : α × ℕ => goodB (K p.1) (g p.1) F.toP (c p.1, p.2) :=
    goodB2 h (by fun_prop) (by fun_prop) (by fun_prop)
  unfold rebalF; fun_prop

end PaddedDescent.F.CertNet

namespace PaddedDescent.F

open Groundwork

theorem certRebal : StCertRebal := fun _ _ _ hF _ _ _ _ _ _ hp hK hg hc => CertNet.rebalF_polyT hF hp hK hg hc

theorem certDescend (hE : StCertExpand) : StCertDescend := by
  unfold StCertDescend descend
  unfold StCertExpand at hE
  exact foldl_cap (pad := fun p : U × List Lvl × PInst => p.1) (l := fun p => p.2.1) (a := fun p => [p.2.2])
    (g := fun p w L => w.flatMap (expand p.1 L)) []
    (by fun_prop) (by fun_prop) (by fun_prop)
    (PolyT.flatMap (f := fun (p : (U × List Lvl × PInst) × List PInst × Lvl) J => expand p.1.1 p.2.2 J) (l := fun p => p.2.1)
      (PolyT.comp (g := fun q : ((U × List Lvl × PInst) × List PInst × Lvl) × PInst => (q.1.1.1, q.1.2.2, q.2)) hE (by fun_prop))
      (by fun_prop))

end PaddedDescent.F
