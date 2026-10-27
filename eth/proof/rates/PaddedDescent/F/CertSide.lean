/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
import PaddedDescent.F.FuelCert
import ToTuring.Poly.GridSide

/-! The row network or the column network of the proof of Proposition 3 (Section 5), read off an
explicit table (`sideF`), is polynomial-time: the lengths of its states and
labels are given in unary, and its weights and factors are polynomial-time functions of the context
and the query (`stCertSide`, which
proves the interface statement `StCertSide`). The side g of the grid, the label length ℓ and the pad
are data, in unary. The flag tr (rows
or columns merged) is data too: each certificate is proved for a fixed tr, and the two cases are
joined at the end (`boolCases`). -/

namespace PaddedDescent.F.CertSide

open Groundwork Groundwork.Prog Groundwork.Grid

variable {α : Type} [Enc α]

/-- A function with a truth value as a parameter is polynomial-time in that parameter too, if it is
for both of its values. -/
theorem boolCases {β : Type} [Enc β] {F : Bool → α → β} (h : ∀ b, PolyT (F b)) {tr : α → Bool} (ht : PolyT tr) :
    PolyT fun x => F (tr x) x :=
  (PolyT.cond' ht (h true) (h false)).congr fun x => by cases tr x <;> rfl

/-- The same for lengths given in unary. -/
theorem boolCasesU {F : Bool → α → ℕ} (h : ∀ b, Unary (F b)) {tr : α → Bool} (ht : PolyT tr) : Unary fun x => F (tr x) x :=
  boolCases (F := fun b x => List.replicate (F b x) ()) h ht

/-! ### Positions in the words of the grid, with g as data -/

section plain

variable (tr : Bool)

@[fun_prop] theorem c2U {g : α → ℕ} (hg : Unary g) : Unary fun x => c2 (g x) := by
  have := hg.poly
  unfold c2; fun_prop

@[fun_prop] theorem c2P {g : α → ℕ} (hg : PolyT g) : PolyT fun x => c2 (g x) :=
  PolyT.div (PolyT.mul hg (PolyT.sub hg (PolyT.const 1))) (PolyT.const 2)

@[fun_prop] theorem he2 {g ℓ x u : α → ℕ} {z : α → List Bool} (h0 : PolyT g) (h1 : PolyT ℓ) (h2 : PolyT z) (h3 : PolyT x)
    (h4 : PolyT u) : PolyT fun a => he (g a) (ℓ a) (z a) (x a) (u a) := by unfold he; fun_prop

@[fun_prop] theorem node2 {g a i : α → ℕ} (h0 : PolyT g) (h1 : PolyT a) (h2 : PolyT i) :
    PolyT fun x => node (g x) tr (a x) (i x) := by unfold node; fun_prop

@[fun_prop] theorem rectIx2 {g p κ : α → ℕ} (h0 : PolyT g) (h1 : PolyT p) (h2 : PolyT κ) :
    PolyT fun x => rectIx (g x) tr (p x) (κ x) := by unfold rectIx; fun_prop

@[fun_prop] theorem rectDig2 {g n y p κ : α → ℕ} (h0 : PolyT g) (h1 : PolyT n) (h2 : PolyT y) (h3 : PolyT p) (h4 : PolyT κ) :
    PolyT fun x => rectDig (g x) tr (n x) (y x) (p x) (κ x) := by unfold rectDig; fun_prop

@[fun_prop] theorem rectLen2 {g n y p κ : α → ℕ} (h0 : PolyT g) (hn : Unary n) (hy : PolyT y) (hp : PolyT p) (hκ : PolyT κ) :
    PolyT fun x => rectLen (g x) tr (n x) (y x) (p x) (κ x) := by
  have := hn.poly
  unfold rectLen
  exact capW_polyT hn (by fun_prop) fun _ => sideCnt_rectDig_le _ _ _ _ _ _

@[fun_prop] theorem sideChunk2 {g n y a b κ : α → ℕ} {θ : α → List Bool} (h0 : PolyT g) (hn : Unary n) (hy : PolyT y)
    (ha : PolyT a) (hb : PolyT b) (hθ : PolyT θ) (hκ : PolyT κ) :
    PolyT fun x => sideChunk (g x) tr (n x) (y x) (a x) (b x) (θ x) (κ x) := by
  have hn' := hn.poly
  have h : PolyT fun x =>
      (((θ x).drop (g x * n x)).drop
        (((List.range ((θ x).drop (g x * n x)).length).map fun κ' =>
          if κ' < κ x then rectLen (g x) tr (n x) (y x) (tri (min (a x) (b x)) (max (a x) (b x))) κ' else 0).sum)).take
        (rectLen (g x) tr (n x) (y x) (tri (min (a x) (b x)) (max (a x) (b x))) (κ x)) := by fun_prop
  exact h.congr fun x => by rw [drop_sum_eq (one_le_rectLen (g x) tr _ _ _), sideChunk, chunkAt]

@[fun_prop] theorem sideLabels2 {g ℓ a i u : α → ℕ} {z : α → List Bool} (h0 : PolyT g) (h1 : PolyT ℓ) (h2 : PolyT a)
    (h3 : PolyT z) (h4 : PolyT i) (h5 : PolyT u) : PolyT fun x => sideLabels (g x) tr (ℓ x) (a x) (z x) (i x) (u x) := by
  unfold sideLabels; fun_prop

theorem sideCap2 {g n y a b : α → ℕ} (hg : Unary g) (hn : Unary n) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => sideCap (g x) tr (n x) (y x) (a x) (b x) := by
  have hn' := hn.poly
  have hg' := hg.poly
  have h : PolyT fun x => g x * n x + ((List.range (c2 (g x))).map fun κ =>
      rectLen (g x) tr (n x) (y x) (tri (min (a x) (b x)) (max (a x) (b x))) κ).sum := by fun_prop
  exact h.congr fun x => by rw [← sum_range_eq_list, sideCap]

theorem sideCapU {g n y a b : α → ℕ} (hg : Unary g) (hn : Unary n) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b) :
    Unary fun x => sideCap (g x) tr (n x) (y x) (a x) (b x) :=
  Unary.of_le (g := fun x => g x * n x + c2 (g x) * (3 * n x + 1)) (by fun_prop) (sideCap2 tr hg hn hy ha hb)
    fun x => sideCap_le' (g x) tr _ _ _ _

/-! ### One rectangle under fuel -/

@[fun_prop] theorem botF2 {pad : α → U} {i : α → ℕ} {x y w : α → List Bool} (hp : PolyT pad) (hi : PolyT i) (hx : PolyT x)
    (hy : PolyT y) (hw : PolyT w) : PolyT fun a => botF (pad a) tr (i a) (x a) (y a) (w a) := by
  unfold botF; fun_prop

@[fun_prop] theorem cutF2 {pad : α → U} {top : α → Bool} {i : α → ℕ} {x y w : α → List Bool} (hp : PolyT pad) (ht : PolyT top)
    (hi : PolyT i) (hx : PolyT x) (hy : PolyT y) (hw : PolyT w) :
    PolyT fun a => cutF (pad a) tr (top a) (i a) (x a) (y a) (w a) := by
  unfold cutF; fun_prop

@[fun_prop] theorem itemF2 {pad : α → U} {g n y a b i i' : α → ℕ} {z θ : α → List Bool} (hp : PolyT pad) (hg : PolyT g)
    (hn : Unary n) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b) (hz : PolyT z) (hθ : PolyT θ) (hi : PolyT i) (hi' : PolyT i') :
    PolyT fun x => itemF (pad x) (g x) tr (n x) (y x) (a x) (b x) (z x) (θ x) (i x) (i' x) := by
  have := hn.poly
  unfold itemF; fun_prop

/-! ### The weights and the factors -/

@[fun_prop] theorem look2 {T : α → Tab} {q : α → IQ} (hT : PolyT T) (hq : PolyT q) : PolyT fun x => look (T x) (q x) := by
  unfold look; fun_prop

@[fun_prop] theorem sideChk2 {g : α → ℕ} {x : α → (ℕ × ℕ) × WQ} (hg : Unary g) (hx : PolyT x) :
    PolyT fun a => sideChk (g a) tr (fun n : ℕ => n) (x a) := by
  have := hg.poly
  unfold sideChk; fun_prop

@[fun_prop] theorem sideEdges2 {g : α → ℕ} {x : α → (ℕ × ℕ) × FQ} (hg : Unary g) (hx : PolyT x) :
    PolyT fun a => sideEdges (g a) tr (fun n : ℕ => n) (x a) := by
  have := hg.poly
  unfold sideEdges; fun_prop

theorem sideWF2 {g ℓ y : α → ℕ} {T : α → Tab} {q : α → WQ} (hg : Unary g) (hℓ : PolyT ℓ) (hy : PolyT y) (hT : PolyT T)
    (hq : PolyT q) : PolyT fun x => sideWF (g x) tr (ℓ x) (y x) (T x) (q x) := by
  have := hg.poly
  unfold sideWF; fun_prop

theorem sideFF2 {pad : α → U} {g ℓ y : α → ℕ} {q : α → FQ} (hp : PolyT pad) (hg : Unary g) (hℓ : Unary ℓ) (hy : PolyT y)
    (hq : PolyT q) : PolyT fun x => sideFF (pad x) (g x) tr (ℓ x) (y x) (q x) := by
  have := hg.poly
  have := hℓ.poly
  unfold sideFF; fun_prop

end plain

/-! ### The network -/

theorem side_n : Unary fun p : SideCtx × ℕ => sideF.n p.1 p.2 := by
  have h : Unary fun p : SideCtx × ℕ => p.1.1.2.1.length * p.1.1.2.1.length * p.1.1.2.1.length * p.1.2.1.length := by fun_prop
  exact h.congr fun p => by
    change List.replicate _ () = List.replicate (p.1.1.2.1.length ^ 3 * p.1.2.1.length) ()
    congr 1; ring

theorem side_cap : Unary fun p : SideCtx × ℕ × ℕ => sideF.cap p.1 p.2.1 p.2.2 :=
  boolCasesU (F := fun b (p : SideCtx × ℕ × ℕ) => sideCap p.1.1.2.1.length b p.1.2.1.length p.1.2.2.1 p.2.1 p.2.2)
    (fun b => sideCapU b (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
    (tr := fun p => p.1.1.2.2) (by fun_prop)

theorem side_W : PolyT sideF.W :=
  boolCases (F := fun b (x : SideCtx × WQ) => sideWF x.1.1.2.1.length b x.1.2.1.length x.1.2.2.1 x.1.2.2.2 x.2)
    (fun b => sideWF2 b (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
    (tr := fun x => x.1.1.2.2) (by fun_prop)

theorem side_f : PolyT sideF.f :=
  boolCases (F := fun b (x : SideCtx × FQ) => sideFF x.1.1.1 x.1.1.2.1.length b x.1.2.1.length x.1.2.2.1 x.2)
    (fun b => sideFF2 b (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
    (tr := fun x => x.1.1.2.2) (by fun_prop)

end PaddedDescent.F.CertSide

namespace PaddedDescent.F

/-- The row or column network of Proposition 3, read off an explicit table, keeps polynomial time:
lengths in unary, weights and factors polynomial-time. -/
public theorem stCertSide : StCertSide := ⟨CertSide.side_n, CertSide.side_cap, CertSide.side_W, CertSide.side_f⟩

end PaddedDescent.F
