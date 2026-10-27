/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Closure.Cases
public import ToTuring.EncLemmas

/-! Closure of polynomial time under folds over lists; a fold is the only form of loop that the
certificates of polynomial time provide. The function folded may use the context x.
The lengths of all intermediate values must be bounded by a polynomial in the length of x. -/

@[expose] public section

namespace Groundwork.PolyT

open TM Turing

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

/-! ### The loop -/

/-- The head of the loop. On the main stack lies the word of a list, then the word of the state. If
the list is empty its word
is removed and the loop is left; else its opening bracket is removed and the body is entered. -/
def foldHead : TM2.Stmt (fun _ : Stk => Sym) Unit (Option Sym) :=
  .pop .main (fun _ _ => none) <| .pop .main (fun _ o => o) <|
    .branch (fun s => s == some .R) (.load (fun _ => none) .halt)
      (.push .main (fun s => s.getD .L) <| .load (fun _ => none) <| .goto fun _ => ())

/-- The body: park the first element on a and the rest of the list on b, remove the closing bracket,
fetch the element, pair it
with the state, apply P, fetch the rest of the list. -/
def foldBody (P : Fr) : Fr :=
  ((((((mv .main .a).seq (mv .main .b)).seq pop1).seq (mv .a .main)).seq consF).seq P).seq (mv .b .main)

/-- The loop: the head, then the body, again and again until the list is empty. -/
def foldLoop (P : Fr) : Fr := Frag.loop foldHead (foldBody P)

theorem code_ne_R (x : V) : ∃ s w, code x = s :: w ∧ (s == Sym.R) = false := by
  cases x with
  | nil => exact ⟨_, _, rfl, by decide⟩
  | bit b => exact ⟨_, _, rfl, by simp⟩
  | cons x y => exact ⟨_, _, rfl, by decide⟩

theorem foldHead_nil (M A B N : List Sym) :
    TM2.stepAux foldHead none (st (.L :: .R :: M) A B N) = ⟨none, none, st M A B N⟩ := by
  simp [foldHead, TM2.stepAux]

theorem foldHead_cons (x : V) (M A B N : List Sym) :
    TM2.stepAux foldHead none (st (.L :: (code x ++ M)) A B N) = ⟨some (), none, st (code x ++ M) A B N⟩ := by
  obtain ⟨s, w, e, hs⟩ := code_ne_R x
  simp [foldHead, TM2.stepAux, e, hs]

/-- The steps of one round: Lb bounds the length of the word of the list, Bd that of the states, t
the steps of P. -/
def roundT (t : ℕ → ℕ) (Lb Bd : ℕ) : ℕ := 6 * Lb + 2 * Bd + 12 + t (Lb + Bd + 2)

/-- The loop computes the fold. -/
theorem foldLoop_within {σ : Type} [Enc σ] {h : ε × σ → σ} {P : Fr} {t : ℕ → ℕ} (ht : Monotone t)
    (hP : ∀ (p : ε × σ) (M A B N : List Sym), P.Within (st (wd p ++ M) A B N) (t (len p)) (st (wd (h p) ++ M) A B N))
    (Lb Bd : ℕ) (M A B N : List Sym) : ∀ (l : List ε) (s : σ), len l ≤ Lb →
      (∀ k, len ((l.take k).foldl (fun s e => h (e, s)) s) ≤ Bd) →
      (foldLoop P).Within (st (wd l ++ (wd s ++ M)) A B N) (l.length * roundT t Lb Bd + 1)
        (st (wd (l.foldl (fun s e => h (e, s)) s) ++ M) A B N)
  | [], s, _, _ => by
    refine ⟨1, by simp, ?_⟩
    exact Frag.loop_runs_exit (foldHead_nil _ A B N)
  | e :: r, s, hL, hB => by
    have hs : len s ≤ Bd := by simpa using hB 0
    have hlc := len_cons e r
    have ih := foldLoop_within ht hP Lb Bd M A B N r (h (e, s)) (by omega) (fun k => by simpa using hB (k + 1))
    -- the body
    have b1 := toA_within (Enc.toV e) (wd r ++ (.R :: (wd s ++ M))) A B N
    have b2 := toB_within (Enc.toV r) (.R :: (wd s ++ M)) (mirror (wd e) ++ A) B N
    have b3 := pop1_within (wd s ++ M) (mirror (wd e) ++ A) (mirror (wd r) ++ B) N .R
    have b4 := fromA_within (Enc.toV e) (wd s ++ M) A (mirror (wd r) ++ B) N
    have b5 := consF_within (Enc.toV e) (Enc.toV s) M A (mirror (wd r) ++ B) N
    have b6 := hP (e, s) M A (mirror (wd r) ++ B) N
    have b7 := fromB_within (Enc.toV r) (wd (h (e, s)) ++ M) A B N
    obtain ⟨n, hn, hbody⟩ := (((((b1.seq b2).seq b3).seq b4).seq b5).seq b6).seq b7
    obtain ⟨m, hm, hrest⟩ := ih
    have hhead := foldHead_cons (Enc.toV e) (wd r ++ (.R :: (wd s ++ M))) A B N
    have e0 : wd (e :: r) ++ (wd s ++ M) = .L :: (code (Enc.toV e) ++ (wd r ++ (.R :: (wd s ++ M)))) := by
      simp only [wd_cons, List.cons_append, List.append_assoc]
      rfl
    refine ⟨1 + n + m, ?_, ?_⟩
    · have h1 : t (len (e, s)) ≤ t (Lb + Bd + 2) := ht (by rw [len_pair]; omega)
      have h2 : (code (Enc.toV e)).length = len e := rfl
      have h3 : (code (Enc.toV r)).length = len r := rfl
      have h4 : (code (Enc.toV s)).length = len s := rfl
      rw [h2, h3, h4] at hn
      have h5 : (e :: r).length * roundT t Lb Bd = r.length * roundT t Lb Bd + roundT t Lb Bd := by
        rw [List.length_cons, Nat.succ_mul]
      unfold roundT at h5 ⊢
      unfold roundT at hm
      omega
    · rw [e0]
      exact Frag.loop_runs_iter hhead hbody hrest

omit [Enc α] [Enc γ] [Enc ε] in
/-- The fold keeps the context in the first component of its state. -/
theorem foldl_ctx (g : α → γ → ε → γ) (x : α) : ∀ (l : List ε) (c : γ),
    l.foldl (fun (s : α × γ) e => (s.1, g s.1 s.2 e)) (x, c) = (x, l.foldl (g x) c)
  | [], _ => rfl
  | e :: r, c => by simp only [List.foldl_cons]; exact foldl_ctx g x r _

/-- The fold: if l, a and g are polynomial-time and a polynomial in len x bounds the lengths of all
intermediate values,
then x ↦ (l x).foldl (g x) (a x) is polynomial-time. -/
theorem foldl {l : α → List ε} {a : α → γ} {g : α → γ → ε → γ} (hl : PolyT l) (ha : PolyT a)
    (hg : PolyT fun p : α × γ × ε => g p.1 p.2.1 p.2.2)
    (hB : ∃ t, PB t ∧ ∀ x (k : ℕ), len (((l x).take k).foldl (g x) (a x)) ≤ t (len x)) :
    PolyT (fun x => (l x).foldl (g x) (a x)) := by
  obtain ⟨tB, htB, hB⟩ := hB
  -- the step on states (x, c), the start, the end
  have hh : PolyT fun p : ε × α × γ => (p.2.1, g p.2.1 p.2.2 p.1) :=
    prodMk (by fun_prop) (comp (g := fun p : ε × α × γ => (p.2.1, p.2.2, p.1)) hg (by fun_prop))
  have h0 : PolyT fun x => (l x, (x, a x)) := by fun_prop
  have h1 : PolyT fun s : α × γ => s.2 := by fun_prop
  obtain ⟨P, t, htp, htm, hP, -⟩ := hh.elim
  obtain ⟨Q, q, hqp, hqm, hQ, hQl⟩ := h0.elim
  obtain ⟨Z, z, hzp, hzm, hZ, -⟩ := h1.elim
  refine PolyT.of (((Q.seq unconsF).seq (foldLoop P)).seq Z)
    (t := fun n => q n + (2 * q n + 6) + (q n * roundT t (q n) (n + tB n + 2) + 1) + z (n + tB n + 2)) (s := tB)
    ?_ htB (fun x M A B N => ?_) (fun x => by simpa using hB x (l x).length)
  · unfold roundT
    have hb : PB fun n => n + tB n + 2 := (PB.id'.add htB).add (PB.const 2)
    exact (((hqp.add (((PB.const 2).mul hqp).add (PB.const 6))).add ((hqp.mul (((((PB.const 6).mul hqp).add
      ((PB.const 2).mul hb)).add (PB.const 12)).add (htp.comp ((hqp.add hb).add (PB.const 2))))).add (PB.const 1)))).add
      (hzp.comp hb)
  · have hlen := hQl x
    rw [len_pair, len_pair] at hlen
    have c1 := hQ x M A B N
    have c2 := unconsF_within (Enc.toV (l x)) (Enc.toV (x, a x)) M A B N
    have hst : ∀ k, len (((l x).take k).foldl (fun (s : α × γ) e => (s.1, g s.1 s.2 e)) (x, a x)) ≤ len x + tB (len x) + 2 := by
      intro k
      rw [foldl_ctx, len_pair]
      have := hB x k
      omega
    have c3 := foldLoop_within (h := fun p : ε × α × γ => (p.2.1, g p.2.1 p.2.2 p.1)) htm hP (q (len x))
      (len x + tB (len x) + 2) M A B N (l x) (x, a x) (by omega) hst
    rw [foldl_ctx] at c3
    have c4 := hZ (x, (l x).foldl (g x) (a x)) M A B N
    refine (((c1.seq c2).seq c3).seq c4).mono ?_
    have e1 : (code (Enc.toV (l x))).length = len (l x) := rfl
    have e2 : (code (Enc.toV (x, a x))).length = len (x, a x) := rfl
    have e3 : z (len (x, (l x).foldl (g x) (a x))) ≤ z (len x + tB (len x) + 2) := hzm (by
      rw [len_pair]; have := hB x (l x).length; simp only [List.take_length] at this; omega)
    have e4 : (l x).length * roundT t (q (len x)) (len x + tB (len x) + 2) ≤
        q (len x) * roundT t (q (len x)) (len x + tB (len x) + 2) :=
      Nat.mul_le_mul_right _ ((length_le_len _).trans (by omega))
    rw [e1, e2, len_pair]
    omega

/-- The fold when every step adds at most b(len x) to the length, b a polynomial bound. -/
theorem foldl_add {l : α → List ε} {a : α → γ} {g : α → γ → ε → γ} (hl : PolyT l) (ha : PolyT a)
    (hg : PolyT fun p : α × γ × ε => g p.1 p.2.1 p.2.2)
    (hB : ∃ b, PB b ∧ ∀ x c, ∀ e ∈ l x, len (g x c e) ≤ len c + b (len x)) :
    PolyT (fun x => (l x).foldl (g x) (a x)) := by
  obtain ⟨b, hb, hB⟩ := hB
  obtain ⟨-, tl, htl, -, -, hll⟩ := hl.elim
  obtain ⟨-, ta, hta, -, -, hla⟩ := ha.elim
  refine foldl hl ha hg ⟨fun n => ta n + tl n * b n, hta.add (htl.mul hb), fun x k => ?_⟩
  have key : ∀ (r : List ε) (c : γ), (∀ e ∈ r, e ∈ l x) → len (r.foldl (g x) c) ≤ len c + r.length * b (len x) := by
    intro r
    induction r with
    | nil => intro c _; simp
    | cons e r ih =>
      intro c hr
      have h1 := ih (g x c e) fun e' he' => hr e' (List.mem_cons_of_mem _ he')
      have h2 := hB x c e (hr e List.mem_cons_self)
      rw [List.foldl_cons, List.length_cons, Nat.succ_mul]
      omega
  have h1 := key ((l x).take k) (a x) fun e he => List.mem_of_mem_take he
  have h2 : ((l x).take k).length * b (len x) ≤ tl (len x) * b (len x) :=
    Nat.mul_le_mul_right _ (((List.length_take_le' _ _).trans (length_le_len _)).trans (hll x))
  have h3 := hla x
  change _ ≤ ta (len x) + tl (len x) * b (len x)
  omega

end Groundwork.PolyT
