/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Fuel
public import ToTuring.Poly.NetFun

/-! The certificates for Fuel.lean: `rng`, `sumF`, `prodL`, `cap` are polynomial-time, and so is
every fold whose state is capped by the
pad after each round (`foldl_cap`), without any side condition. `Unary` is made a second property
for the tactic `fun_prop`, so that side goals
«this number is given in unary» are found by the tactic. -/

@[expose] public section

namespace PaddedDescent.F

open Groundwork

variable {α β γ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc ε]

/-! ### Unary as a property for fun_prop -/

attribute [fun_prop] Unary

@[fun_prop] theorem unary_comp {f : β → ℕ} {h : α → β} (hf : Unary f) (hh : PolyT h) : Unary fun x => f (h x) := hf.comp hh
@[fun_prop] theorem unary_const (n : ℕ) : Unary fun _ : α => n := Unary.const n
@[fun_prop] theorem unary_length {w : α → List γ} (hw : PolyT w) : Unary fun c => (w c).length := Unary.of_length hw
@[fun_prop] theorem unary_add {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun c => f c + g c := hf.add hg
@[fun_prop] theorem unary_mul {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun c => f c * g c := hf.mul hg
@[fun_prop] theorem unary_sub {f g : α → ℕ} (hf : Unary f) (hg : PolyT g) : Unary fun c => f c - g c :=
  Unary.of_le hf (by have := hf.poly; fun_prop) fun _ => Nat.sub_le _ _
@[fun_prop] theorem unary_div {f g : α → ℕ} (hf : Unary f) (hg : PolyT g) : Unary fun c => f c / g c :=
  Unary.of_le hf (by have := hf.poly; fun_prop) fun _ => Nat.div_le_self _ _
@[fun_prop] theorem unary_pow_const {f : α → ℕ} (hf : Unary f) (k : ℕ) : Unary fun c => f c ^ k := by
  induction k with
  | zero => simpa using unary_const (α := α) 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf
@[fun_prop] theorem unary_sum_map {f : α → β → ℕ} {l : α → List β} (hf : Unary fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    Unary fun a => ((l a).map (f a)).sum := Prog.NetE.unary_sum_map hf hl
@[fun_prop] theorem range_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun x => List.range (n x) := PolyT.range hn
@[fun_prop] theorem pow_polyT {b e : α → ℕ} (hb : PolyT b) (he : Unary e) : PolyT fun x => b x ^ e x := PolyT.pow_unary hb he
@[fun_prop] theorem toWord_polyT {n y : α → ℕ} (hn : Unary n) (hy : PolyT y) : PolyT fun x => toWord (n x) (y x) :=
  PolyT.toWord' hn hy
/-- A number given in unary, written out as a list of units. -/
@[fun_prop] theorem replicate_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun x => List.replicate (n x) () := hn

/-! ### rng, sums and products -/

@[fun_prop] theorem rng_polyT {pad : α → U} {q : α → ℕ} (hp : PolyT pad) (hq : PolyT q) : PolyT fun x => rng (pad x) (q x) :=
  PolyT.range (PolyT.unary_min_length hq hp)

theorem len_addZ_le (c e : ℤ) : len (c + e) ≤ len c + len e := by
  have h : Nat.size (c + e).natAbs ≤ Nat.size c.natAbs + Nat.size e.natAbs + 1 := by
    rw [Nat.size_le]
    have h0 := Int.natAbs_add_le c e
    have h1 := Nat.lt_size_self c.natAbs
    have h2 := Nat.lt_size_self e.natAbs
    have h3 : 2 ^ Nat.size c.natAbs ≤ 2 ^ (Nat.size c.natAbs + Nat.size e.natAbs) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ Nat.size e.natAbs ≤ 2 ^ (Nat.size c.natAbs + Nat.size e.natAbs) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]
    omega
  simp only [len_int]; omega

theorem len_mulZ_le (c e : ℤ) : len (c * e) ≤ len c + len e := by
  have h : Nat.size (c * e).natAbs ≤ Nat.size c.natAbs + Nat.size e.natAbs := by
    rw [Int.natAbs_mul, Nat.size_le, pow_add]
    exact Nat.mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _)
  simp only [len_int]; omega

@[fun_prop] theorem sumZ_polyT {l : α → List ℤ} (hl : PolyT l) : PolyT fun x => (l x).sum := by
  obtain ⟨t, ht, -, hlen⟩ := PolyT.len_bound hl
  have h : PolyT (fun x => (l x).foldl (fun c e => c + e) 0) := by
    refine PolyT.foldl_add (g := fun _ c e => c + e) hl (by fun_prop) (by fun_prop) ⟨t, ht, fun x c e he => ?_⟩
    exact (len_addZ_le c e).trans (Nat.add_le_add_left ((len_le_of_mem he).trans (hlen x)) _)
  exact h.congr fun x => by rw [List.sum_eq_foldl]

@[fun_prop] theorem prodZ_polyT {l : α → List ℤ} (hl : PolyT l) : PolyT fun x => (l x).prod := by
  obtain ⟨t, ht, -, hlen⟩ := PolyT.len_bound hl
  have h : PolyT (fun x => (l x).foldl (fun c e => c * e) 1) := by
    refine PolyT.foldl_add (g := fun _ c e => c * e) hl (by fun_prop) (by fun_prop) ⟨t, ht, fun x c e he => ?_⟩
    exact (len_mulZ_le c e).trans (Nat.add_le_add_left ((len_le_of_mem he).trans (hlen x)) _)
  exact h.congr fun x => by rw [List.prod_eq_foldl]

@[fun_prop] theorem sumF_polyT {N : α → ℕ} {pad : α → U} {f : α → ℕ → ℤ} (hN : PolyT N) (hp : PolyT pad)
    (hf : PolyT fun p : α × ℕ => f p.1 p.2) : PolyT fun x => sumF (N x) (pad x) (f x) := by
  unfold sumF
  have hr : PolyT fun x => List.range (min (N x) (pad x).length) := PolyT.range (PolyT.unary_min_length hN hp)
  obtain ⟨b, hb, hbl⟩ := PolyT.len_bound_mem hf hr
  refine PolyT.foldl_add (g := fun x acc y => acc + f x y) hr (by fun_prop) ?_ ⟨b, hb, fun x c e he => ?_⟩
  · have : PolyT fun p : α × ℤ × ℕ => f p.1 p.2.2 :=
      PolyT.comp (g := fun p : α × ℤ × ℕ => (p.1, p.2.2)) hf (by fun_prop)
    fun_prop
  · have := len_addZ_le c (f x e)
    have := hbl x e he
    omega

@[fun_prop] theorem prodL_polyT {n : α → ℕ} {f : α → ℕ → ℤ} (hn : Unary n)
    (hf : PolyT fun p : α × ℕ => f p.1 p.2) : PolyT fun x => prodL (n x) (f x) := by
  unfold prodL
  have hr : PolyT fun x => List.range (n x) := PolyT.range hn
  obtain ⟨b, hb, hbl⟩ := PolyT.len_bound_mem hf hr
  refine PolyT.foldl_add (g := fun x acc y => acc * f x y) hr (by fun_prop) ?_ ⟨b, hb, fun x c e he => ?_⟩
  · have : PolyT fun p : α × ℤ × ℕ => f p.1 p.2.2 :=
      PolyT.comp (g := fun p : α × ℤ × ℕ => (p.1, p.2.2)) hf (by fun_prop)
    fun_prop
  · have := len_mulZ_le c (f x e)
    have := hbl x e he
    omega

/-! ### The length of a word, the cap, the capped fold -/

instance : Meas ℕ := ⟨by
  have : PolyT fun n : ℕ => 3 * Nat.size n + 2 := by fun_prop
  exact this.congr fun n => (len_nat n).symm⟩
instance : Meas ℤ := ⟨by
  have : PolyT fun z : ℤ => 3 * Nat.size z.natAbs + 5 := by fun_prop
  exact this.congr fun z => (len_int z).symm⟩
instance : Meas Bool := ⟨(PolyT.const 1).congr fun _ => rfl⟩
instance : Meas Unit := ⟨(PolyT.const 2).congr fun _ => rfl⟩
instance [Meas α] [Meas β] : Meas (α × β) := ⟨by
  have h1 := Meas.poly (α := α)
  have h2 := Meas.poly (α := β)
  have : PolyT fun p : α × β => len p.1 + len p.2 + 2 := by fun_prop
  exact this.congr fun p => (len_pair p.1 p.2).symm⟩
instance [Meas α] : Meas (List α) := ⟨by
  have h1 := Meas.poly (α := α)
  have : PolyT fun l : List α => (l.map fun a => len a + 2).sum + 2 := by fun_prop
  exact this.congr fun l => (len_list l).symm⟩

@[fun_prop] theorem cap_polyT [Meas γ] {pad : α → U} {d x : α → γ} (hp : PolyT pad) (hd : PolyT d) (hx : PolyT x) :
    PolyT fun a => cap (pad a) (d a) (x a) := by
  have := Meas.poly (α := γ)
  unfold cap; fun_prop

/-- A fold whose state is capped by the pad after every round is polynomial-time, with no side
condition. -/
theorem foldl_cap [Meas γ] {pad : α → U} {l : α → List ε} {a : α → γ} {g : α → γ → ε → γ} (d : γ)
    (hp : PolyT pad) (hl : PolyT l) (ha : PolyT a) (hg : PolyT fun p : α × γ × ε => g p.1 p.2.1 p.2.2) :
    PolyT fun x => (l x).foldl (fun c e => cap (pad x) d (g x c e)) (cap (pad x) d (a x)) := by
  obtain ⟨t, ht, -, hlen⟩ := PolyT.len_bound hp
  refine PolyT.foldl (g := fun x c e => cap (pad x) d (g x c e)) hl (by fun_prop) (by fun_prop)
    ⟨fun n => t n + len d, ht.add (PB.const _), fun x k => ?_⟩
  have hpad : (pad x).length ≤ t (len x) := (length_le_len _).trans (hlen x)
  have : ∀ (r : List ε) (c : γ), len c ≤ (pad x).length + len d →
      len (r.foldl (fun c e => cap (pad x) d (g x c e)) c) ≤ (pad x).length + len d := by
    intro r
    induction r with
    | nil => intro c h; exact h
    | cons e r ih => intro c _; exact ih _ (len_cap_le _ _ _)
  exact (this _ _ (len_cap_le _ _ _)).trans (Nat.add_le_add_right hpad _)

end PaddedDescent.F
