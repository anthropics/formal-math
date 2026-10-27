/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.List2
public import ToTuring.Lib.Nat2

/-! Numbers given in unary, as lists of that length: `Unary f` says that the list of `f x` copies of
`()` is `PolyT` in `x`.
This file relates `Unary` to `PolyT` and closes it under constants, composition, sums, products and
smaller functions. -/

@[expose] public section

namespace Groundwork.Unary

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

variable {f g : α → ℕ}

/-- A function that is polynomial-time in unary is polynomial-time as a number: take the length of
the list. -/
theorem poly (hf : Unary f) :
    PolyT f :=
  (PolyT.length hf).congr fun _ => List.length_replicate

/-- The length of a polynomial-time list is polynomial-time in unary. -/
theorem of_length {w : α → List γ} (hw : PolyT w) :
    Unary fun c => (w c).length := by
  have h : PolyT (fun c => (w c).map fun _ => ()) := by fun_prop
  exact h.congr fun c => List.map_const'

theorem const (n : ℕ) :
    Unary fun _ : α => n :=
  PolyT.const _

theorem comp (hf : Unary f) {h : β → α} (hh : PolyT h) :
    Unary fun b => f (h b) :=
  PolyT.comp hf hh

theorem add (hf : Unary f) (hg : Unary g) :
    Unary fun c => f c + g c :=
  (PolyT.append hf hg).congr fun _ => List.replicate_append_replicate

theorem mul (hf : Unary f) (hg : Unary g) :
    Unary fun c => f c * g c := by
  have hg' : PolyT (fun p : α × Unit => List.replicate (g p.1) ()) := PolyT.comp hg PolyT.id'.fst
  refine (PolyT.flatMap (f := fun c _ => List.replicate (g c) ()) hg' hf).congr fun c => ?_
  rw [List.flatMap_replicate, List.flatten_replicate_replicate]

/-- A polynomial-time number bounded by a unary one is itself unary: cut the list of length `g c`
down to length `f c`. -/
theorem of_le (hg : Unary g) (hf : PolyT f) (h : ∀ c, f c ≤ g c) :
    Unary f :=
  (PolyT.take hf hg).congr fun c => by
    rw [List.take_replicate, Nat.min_eq_left (h c)]

end Groundwork.Unary
