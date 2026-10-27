/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.Half
public import ClauseBound.Inst.CertHalfPart
public import ClauseBound.Inst.CertHalfTab
public import ClauseBound.Inst.CertHalfSmall

/-! # Certificates for the pieces with ρ = 1/√2: the two functions of a factorization

The programs of proof/rates/ClauseBound/Inst/Half.lean are polynomial-time (PolyT): the number s of
a piece, the weights, the list `labs` of the pairs (j, τ) that the labels stand for, the code `encF`
of a
string, and the two functions of a factorization, first with all their arguments apart (`partT`),
then as functions of one query (`partH`). The number h is given in unary.

The entries of the matrices, `topF` and `botF`, enter through their certificates, in the form of the
statements `StTopF` and `StBotF`. The first of them asks for the number j of a pair in
unary. A member (j, τ) of `labs` has j ≤ 2h, so that j can be replaced by min j (2h) without
changing a value (`partT_eq`); this number is given in unary. The two statements are proved below
(`stTopF`, `stBotF`) from the certificates `topF_polyT` and `botF_polyT` of the imported files. With
them and the five certificates of proof/rates/ClauseBound/Inst/CertHalfSmall.lean, the end is
`halfF_keeps`: for all values of its two parameters the family `halfF`
has the certificates `PiecesF.Keeps` that the algorithm asks of a family of pieces. -/

public section

namespace ClauseBound.Inst.Half.Cert

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec

variable {α : Type} [Enc α]

/-- The entries `topF` are polynomial-time, for W, h and the number i in unary. -/
@[expose] def StTopF : Prop := ∀ (α : Type) [Enc α] (pad : α → U) (W h i : α → ℕ) (flat : α → List (List ℕ)) (μ π σ : α → List ℕ) (r : α → ℤ),
  PolyT pad → Unary W → PolyT flat → Unary h → PolyT μ → Unary i → PolyT r → PolyT π → PolyT σ →
  PolyT fun x => topF (pad x) (W x) (flat x) (h x) (μ x) (i x) (r x) (π x) (σ x)

/-- The entries `botF` are polynomial-time, for W and h in unary. -/
@[expose] def StBotF : Prop := ∀ (α : Type) [Enc α] (pad : α → U) (W h : α → ℕ) (flat : α → List (List ℕ)) (μ π σ : α → List ℕ) (r : α → ℤ),
  PolyT pad → Unary W → PolyT flat → Unary h → PolyT μ → PolyT r → PolyT π → PolyT σ →
  PolyT fun x => botF (pad x) (W x) (flat x) (h x) (μ x) (r x) (π x) (σ x)

/-! ### The labels and the code -/

/-- The number s of a piece is polynomial-time. -/
theorem sOf_polyT {h i : α → ℕ} (hh : PolyT h) (hi : PolyT i) : PolyT fun x => sOf (h x) (i x) :=
  PolyT.subZ (PolyT.natCast (PolyT.min' hi (PolyT.mul (PolyT.const 4) hh))) (PolyT.mulZ (PolyT.const 2) (PolyT.natCast hh))

/-- The weight of τ in a pair (j, τ) is polynomial-time. -/
theorem wOf_polyT {tr : α → Bool} {h j : α → ℕ} {s : α → ℤ} (ht : PolyT tr) (hh : PolyT h) (hs : PolyT s) (hj : PolyT j) :
    PolyT fun x => wOf (tr x) (h x) (s x) (j x) :=
  PolyT.cond' ht (PolyT.subZ (PolyT.subZ (PolyT.mulZ (PolyT.const 2) (PolyT.natCast hh)) hs) (PolyT.natCast hj)) (PolyT.addZ hs (PolyT.natCast hj))

/-- The list of the pairs (j, τ) is polynomial-time, for h in unary. -/
theorem labs_polyT {T : α → PT} {tr : α → Bool} {h : α → ℕ} {s : α → ℤ} (hT : PolyT T) (ht : PolyT tr) (hh : Unary h) (hs : PolyT s) :
    PolyT fun x => labs (T x) (tr x) (h x) (s x) := by
  have hr : PolyT fun x => List.range (2 * h x + 1) := PolyT.range (((Unary.const 2).mul hh).add (Unary.const 1))
  have hw : PolyT fun q : α × ℕ => wOf (tr q.1) (h q.1) (s q.1) q.2 :=
    wOf_polyT (PolyT.comp ht PolyT.id'.fst) (PolyT.comp hh.poly PolyT.id'.fst) (PolyT.comp hs PolyT.id'.fst) PolyT.id'.snd
  have hl : PolyT fun q : α × ℕ => (T q.1).getD (wOf (tr q.1) (h q.1) (s q.1) q.2).toNat [] :=
    PolyT.getD (PolyT.comp hT PolyT.id'.fst) (PolyT.toNat hw) (PolyT.const [])
  have hm : PolyT fun q : α × ℕ => ((T q.1).getD (wOf (tr q.1) (h q.1) (s q.1) q.2).toNat []).map fun τ => (q.2, τ) :=
    PolyT.map (f := fun (q : α × ℕ) (τ : List ℕ) => (q.2, τ)) (PolyT.prodMk PolyT.id'.fst.snd PolyT.id'.snd) hl
  have hf : PolyT fun q : α × ℕ => if 0 ≤ wOf (tr q.1) (h q.1) (s q.1) q.2 then
      ((T q.1).getD (wOf (tr q.1) (h q.1) (s q.1) q.2).toNat []).map fun τ => (q.2, τ) else [] :=
    PolyT.ite' (PolyT.decide_leZ (PolyT.const 0) hw) hm (PolyT.const [])
  unfold labs
  exact PolyT.flatMap (f := fun x j => if 0 ≤ wOf (tr x) (h x) (s x) j then ((T x).getD (wOf (tr x) (h x) (s x) j).toNat []).map fun τ => (j, τ) else []) hf hr

/-- The partition that a string stands for is polynomial-time. -/
theorem encF_polyT {T : α → PT} {h : α → ℕ} {a : α → List Bool} (hT : PolyT T) (hh : PolyT h) (ha : PolyT a) : PolyT fun x => encF (T x) (h x) (a x) :=
  PolyT.getD (PolyT.getD hT hh (PolyT.const [])) (PolyT.ofWord' ha) (PolyT.const [])

/-- A member (j, τ) of the list of the pairs has j ≤ 2h. -/
theorem fst_le_of_mem_labs {T : PT} {tr : Bool} {h : ℕ} {s : ℤ} {p : ℕ × List ℕ} (hp : p ∈ labs T tr h s) : p.1 ≤ 2 * h := by
  obtain ⟨j, hj, hpj⟩ := List.mem_flatMap.1 hp
  have hj' : j ≤ 2 * h := Nat.le_of_lt_succ (List.mem_range.1 hj)
  split_ifs at hpj
  · obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hpj
    exact hj'
  · exact absurd hpj List.not_mem_nil

/-! ### The two functions of a factorization -/

/-- The value of one of the two functions at the pair (j, τ). -/
def bodyT (pad : U) (tr top : Bool) (h : ℕ) (s : ℤ) (T : PT) (a b : List Bool) (j : ℕ) (τ : List ℕ) : ℤ :=
  bif top then
    (bif tr then topF pad (4 * h) T.flatten h (encF T h a) j (s - h + j) (encF T h b) τ
     else topF pad (4 * h) T.flatten h (encF T h a) j (s - h + j) τ (encF T h b))
  else
    (bif tr then botF pad (4 * h) T.flatten h (encF T h b) (h - s - j) τ (encF T h a)
     else botF pad (4 * h) T.flatten h (encF T h b) (h - s - j) (encF T h a) τ)

/-- The number j of a pair may be cut off at 2h. -/
theorem partT_eq (pad : U) (tr top : Bool) (h : ℕ) (s : ℤ) (T : PT) (a b θ : List Bool) :
    partT pad tr top h s T a b θ = ((labs T tr h s)[ofWord θ]?).elim 0 fun p => bodyT pad tr top h s T a b (min p.1 (2 * h)) p.2 := by
  unfold partT
  cases e : (labs T tr h s)[ofWord θ]? with
  | none => rfl
  | some p =>
    rw [Option.elim_some, Option.elim_some, min_eq_left (fst_le_of_mem_labs (List.mem_of_getElem? e))]
    rfl

/-- The value at a pair (j, τ) is polynomial-time, for h and j in unary. -/
theorem bodyT_polyT (Ht : StTopF) (Hb : StBotF) {pad : α → U} {tr top : α → Bool} {h j : α → ℕ} {s : α → ℤ} {T : α → PT} {a b : α → List Bool}
    {τ : α → List ℕ} (hp : PolyT pad) (htr : PolyT tr) (htop : PolyT top) (hh : Unary h) (hs : PolyT s) (hT : PolyT T) (ha : PolyT a) (hb : PolyT b)
    (hj : Unary j) (hτ : PolyT τ) :
    PolyT fun x => bodyT (pad x) (tr x) (top x) (h x) (s x) (T x) (a x) (b x) (j x) (τ x) := by
  have hW : Unary fun x => 4 * h x := (Unary.const 4).mul hh
  have hfl : PolyT fun x => (T x).flatten := PolyT.flatten hT
  have hea := encF_polyT hT hh.poly ha
  have heb := encF_polyT hT hh.poly hb
  have hr1 : PolyT fun x => s x - (h x : ℤ) + (j x : ℤ) := PolyT.addZ (PolyT.subZ hs (PolyT.natCast hh.poly)) (PolyT.natCast hj.poly)
  have hr2 : PolyT fun x => (h x : ℤ) - s x - (j x : ℤ) := PolyT.subZ (PolyT.subZ (PolyT.natCast hh.poly) hs) (PolyT.natCast hj.poly)
  exact PolyT.cond' htop
    (PolyT.cond' htr (Ht α pad _ h j _ _ _ _ _ hp hW hfl hh hea hj hr1 heb hτ) (Ht α pad _ h j _ _ _ _ _ hp hW hfl hh hea hj hr1 hτ heb))
    (PolyT.cond' htr (Hb α pad _ h _ _ _ _ _ hp hW hfl hh heb hr2 hτ hea) (Hb α pad _ h _ _ _ _ _ hp hW hfl hh heb hr2 hea hτ))

/-- One of the two functions of a factorization, with its arguments apart, is polynomial-time, for h
in unary. -/
theorem partT_polyT (Ht : StTopF) (Hb : StBotF) {pad : α → U} {tr top : α → Bool} {h : α → ℕ} {s : α → ℤ} {T : α → PT} {a b θ : α → List Bool}
    (hp : PolyT pad) (htr : PolyT tr) (htop : PolyT top) (hh : Unary h) (hs : PolyT s) (hT : PolyT T) (ha : PolyT a) (hb : PolyT b) (hθ : PolyT θ) :
    PolyT fun x => partT (pad x) (tr x) (top x) (h x) (s x) (T x) (a x) (b x) (θ x) := by
  have h1 : PolyT fun x => (labs (T x) (tr x) (h x) (s x))[ofWord (θ x)]? := PolyT.getElem? (labs_polyT hT htr hh hs) (PolyT.ofWord' hθ)
  have hj : Unary fun q : α × ℕ × List ℕ => min q.2.1 (2 * h q.1) :=
    unary_min_right PolyT.id'.snd.fst ((Unary.const 2).mul (hh.comp PolyT.id'.fst))
  have h2 : PolyT fun q : α × ℕ × List ℕ => bodyT (pad q.1) (tr q.1) (top q.1) (h q.1) (s q.1) (T q.1) (a q.1) (b q.1) (min q.2.1 (2 * h q.1)) q.2.2 :=
    bodyT_polyT Ht Hb (PolyT.comp hp PolyT.id'.fst) (PolyT.comp htr PolyT.id'.fst) (PolyT.comp htop PolyT.id'.fst) (hh.comp PolyT.id'.fst)
      (PolyT.comp hs PolyT.id'.fst) (PolyT.comp hT PolyT.id'.fst) (PolyT.comp ha PolyT.id'.fst) (PolyT.comp hb PolyT.id'.fst) hj PolyT.id'.snd.snd
  exact (PolyT.optionElim (f := fun x (p : ℕ × List ℕ) => bodyT (pad x) (tr x) (top x) (h x) (s x) (T x) (a x) (b x) (min p.1 (2 * h x)) p.2)
    h1 (PolyT.const 0) h2).congr fun x => (partT_eq _ _ _ _ _ _ _ _ _).symm

/-- The two functions of a factorization are polynomial-time in the query, given the certificates of
the entries of the matrices. -/
theorem partH_polyT_of (Ht : StTopF) (Hb : StBotF) (c₀ : ℕ) (top : Bool) : PolyT (partH c₀ top) := by
  have hl : Unary fun q : PQ => q.2.2.1.length := Unary.of_length PolyT.id'.snd.snd.fst
  have hh : Unary fun q : PQ => hF c₀ q.2.2.1.length := hF_unary c₀ hl
  have hpad : PolyT fun q : PQ => q.1.1 := PolyT.id'.fst.fst
  exact partT_polyT Ht Hb hpad PolyT.id'.fst.snd (PolyT.const top) hh (sOf_polyT hh.poly PolyT.id'.snd.fst.snd)
    (allTabF_polyT hpad ((Unary.const 4).mul hh)) PolyT.id'.snd.snd.fst PolyT.id'.snd.snd.snd.fst PolyT.id'.snd.snd.snd.snd

/-! ### The family -/

/-- The certificate of `topF`, in the form in which it is used here. -/
theorem stTopF : StTopF := fun _ _ _ _ _ _ _ _ _ _ _ hp hW hf hh hμ hi hr hπ hσ => topF_polyT hp hW hf hh hμ hi.poly hr hπ hσ

/-- The certificate of `botF`, in the form in which it is used here. -/
theorem stBotF : StBotF := fun _ _ _ _ _ _ _ _ _ _ hp hW hf hh hμ hr hπ hσ => botF_polyT hp hW hf hh hμ hr hπ hσ

/-- The two functions of a factorization are polynomial-time in the query. -/
theorem partH_polyT (c₀ : ℕ) (top : Bool) : PolyT (partH c₀ top) := partH_polyT_of stTopF stBotF c₀ top

/-- The pieces with ρ = 1/√2 keep polynomial time, for all values of the two parameters. -/
theorem halfF_keeps (c₀ c : ℕ) : (halfF c₀ c).Keeps :=
  ⟨CertSmall.cnt c₀ c, CertSmall.d c₀ c, CertSmall.cap c₀ c, partH_polyT c₀ true, partH_polyT c₀ false, CertSmall.need c₀ c, CertSmall.bits c₀ c⟩

end ClauseBound.Inst.Half.Cert
