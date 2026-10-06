/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Calls

/-!
# Tactics for proofs about programs

A proof about a program follows the text of the program from top to bottom.  The goal is always
`Ends lim P d s ⟨frame l, μ⟩ T Q`, and the statement at the head of `s` decides what comes next:

| the head of the program | what to write                  | what it is told                       |
|-------------------------|--------------------------------|---------------------------------------|
| `x := e`                | `light_set z`                  | the value `z` of `e`                  |
| `mem[a] := e`           | `light_store b z`              | the address `b` and the value `z`     |
| `if c then … else …`    | `light_if h₁ h₂ : p`           | what the test says, and two names     |
| `x := p(args)`          | `light_call fact with …`       | what the procedure does (`Meets`)     |
| a piece with a lemma    | `light_piece fact with …`      | what the piece does (`Ends`)          |
| `skip`, nothing else    | `light_skip`                   |                                       |
| a loop, nothing else    | `refine Ends.forFrame …`       | invariant and number of rounds        |
| a loop, then more       | `refine Ends.next _ (…)`       | the loop's rule with `(hT := le_rfl)` |

Each tactic works whether or not more program follows, hands the steps that are left to the rest of
the program, and proves the side conditions (the expressions stay within the limits and have the
values that were given, the time suffices) by `light_side` and `light_time`.  What is left is the
goal about the rest of the program, or `Q` of the last state.  After `light_if` there are two goals,
first the one in which the test holds.  The patterns after `with` take apart, as those of `rintro`
do, what holds after the call or the piece.  Goals for holes `?_` in a `fact` come before the goal
about the rest of the program.

The side conditions are decided by linear arithmetic over the hypotheses in the context.
`light_facts H` puts the fields of a record `H` there.  What a side condition needs beyond that is
named after `using`: the content of a cell that is read, a definition to be unfolded, a running time
to be unfolded: `light_set K[j] using hkey`.

A program that is a definition is replaced by its text when a single statement is treated.  A
definition that stands at the head of a sequence stays closed: it is a piece, for `light_piece`.
-/

@[expose] public section

namespace Light

/-! ## Records -/

/-- `light_facts H₁ H₂ …` adds every field of the records `H₁`, `H₂`, … to the context, as
hypotheses without names.  A record inside a record is named like any other:
`light_facts H H.limits`.  The records themselves stay: what is taken apart is the copy `id H`. -/
macro "light_facts" hs:(ppSpace colGt term:max)+ : tactic =>
  `(tactic| ($[obtain ⟨⟩ := id $hs];*))

/-! ## One statement -/

/-- Brackets to the right, and a `skip` before the rest of the program is dropped.  No definition is
opened. -/
macro "light_assoc" : tactic =>
  `(tactic| repeat with_unfolding_none first | refine Ends.seqAssoc ?_ | refine Ends.skipThen ?_)

/-- Brings the program into the form "first statement, then the rest": a program that is defined as
a sequence is written out, and a `skip` is put behind a single statement. -/
macro "light_head" : tactic =>
  `(tactic| ((first | refine Ends.seqSelf ?_ | refine Ends.skipLast ?_); light_assoc))

/-- `light_skip` treats a program of which only `skip` is left: the goal becomes `Q` of the state.
-/
macro "light_skip" : tactic => `(tactic| with_unfolding_none refine Ends.skip ?_)

/-- `light_set z using h₁, h₂` treats the assignment `x := e` at the head of the program, where `e`
has the value `z`; `h₁`, `h₂` go to `light_side` and `light_time`. -/
macro "light_set " z:term:max " using " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic|
    focus
      light_head
      refine Ends.setToThen $z ?_ ?_ ?_
      on_goal -1 => light_time [$hs,*]
      on_goal -1 => light_side [$hs,*]
      try light_skip)

/-- `light_set z` treats the assignment `x := e` at the head of the program, where `e` has the value
`z`. -/
macro "light_set " z:term:max : tactic => `(tactic| light_set $z using)

/-- `light_store b z using h₁, h₂` treats the store `mem[a] := e` at the head of the program, where
`a` has the value `b`, a natural number, and `e` the value `z`; `h₁`, `h₂` go to `light_side` and
`light_time`. -/
macro "light_store " b:term:max ppSpace z:term:max " using "
    hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic|
    focus
      light_head
      refine Ends.storeToThen $b $z ?_ ?_ ?_
      on_goal -1 => light_time [$hs,*]
      on_goal -1 => light_side [$hs,*]
      try light_skip)

/-- `light_store b z` treats the store `mem[a] := e` at the head of the program, where `a` has the
value `b`, a natural number, and `e` the value `z`. -/
macro "light_store " b:term:max ppSpace z:term:max : tactic => `(tactic| light_store $b $z using)

/-- `light_if h₁ h₂ : p using h₃, h₄` treats the branch at the head of the program, whose test says
`p`.  It leaves two goals: the first side of the branch with `h₁ : p`, and the second side with
`h₂ : ¬ p`.  One of the side conditions is the equivalence of the test and `p`; `h₃`, `h₄` go to
`light_side` and `light_time`. -/
macro "light_if " h₁:ident ppSpace h₂:ident " : " p:term " using "
    hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic|
    focus
      light_head
      refine Ends.iteIffThen $p (fun $h₁ => ?_) (fun $h₂ => ?_) ?_ ?_
      on_goal -1 => light_time [$hs,*]
      on_goal -1 => light_side [$hs,*]
      all_goals light_assoc)

/-- `light_if h₁ h₂ : p` treats the branch at the head of the program, whose test says `p`.  It
leaves two goals: the first side of the branch with `h₁ : p`, and the second side with `h₂ : ¬ p`.
One of the side conditions is the equivalence of the test and `p`. -/
macro "light_if " h₁:ident ppSpace h₂:ident " : " p:term : tactic =>
  `(tactic| light_if $h₁ $h₂ : $p using)

/-- `light_call fact using h₁, h₂ with r μ' hR` treats the call `x := p(args)` at the head of the
program, where `fact : Meets lim P p (d + 1) vals μ T' R` says what the procedure does.  The
patterns after `with` name the result, the memory after the call, and what `R` says about them;
`h₁`, `h₂` go to `light_side`, which shows that the arguments have the values `vals`, and to
`light_time`.  A `fact` that still asks for a depth `d'` and a bound on it,
`∀ d', d' + k ≤ lim.depth → Meets lim P p d' vals μ T' R`, is accepted as well. -/
macro "light_call " fact:term:max " using " hs:Lean.Parser.Tactic.simpLemma,* " with"
    pats:(ppSpace colGt rintroPat)+ : tactic =>
  `(tactic|
    focus
      light_head
      first
        | refine Ends.callToThen ($fact _ (by omega)) ?_ ?_ ?_ ?_
        | refine Ends.callToThen $fact ?_ ?_ ?_ ?_
      on_goal -1 => light_time [$hs,*]
      on_goal -1 => omega
      on_goal -1 => light_side [$hs,*]
      on_goal -1 => (rintro $pats*; try light_skip))

/-- `light_call fact with r μ' hR` treats the call `x := p(args)` at the head of the program, where
`fact : Meets lim P p (d + 1) vals μ T' R` says what the procedure does.  The patterns after `with`
name the result, the memory after the call, and what `R` says about them.  A `fact` that still asks
for a depth `d'` and a bound on it, `∀ d', d' + k ≤ lim.depth → Meets lim P p d' vals μ T' R`, is
accepted as well. -/
macro "light_call " fact:term:max " with" pats:(ppSpace colGt rintroPat)+ : tactic =>
  `(tactic| light_call $fact using with $pats*)

/-- `light_piece fact using t₁, t₂ with σ' hR` treats a piece `s₁` at the head of the program, where
`fact : Ends lim P d s₁ σ T₁ R` says what the piece does.  The patterns after `with` name the state
after the piece and what `R` says about it; `t₁`, `t₂` go to `light_time`. -/
macro "light_piece " fact:term:max " using " hs:Lean.Parser.Tactic.simpLemma,* " with"
    pats:(ppSpace colGt rintroPat)+ : tactic =>
  `(tactic|
    focus
      light_assoc
      first | refine Ends.pieceThen $fact ?_ ?_ | refine Ends.pieceLast $fact ?_ ?_
      on_goal -1 => light_time [$hs,*]
      on_goal -1 => rintro $pats*)

/-- `light_piece fact with σ' hR` treats a piece `s₁` at the head of the program, where
`fact : Ends lim P d s₁ σ T₁ R` says what the piece does.  The patterns after `with` name the state
after the piece and what `R` says about it. -/
macro "light_piece " fact:term:max " with" pats:(ppSpace colGt rintroPat)+ : tactic =>
  `(tactic| light_piece $fact using with $pats*)

/-- `light_piece fact` treats a piece at the end of the program, where
`fact : Ends lim P d s σ T₁ Q` says that the piece does what is to be shown. -/
macro "light_piece " fact:term:max : tactic =>
  `(tactic| focus (refine Ends.pieceLast $fact (fun _ h => h) ?_; on_goal -1 => light_time))

end Light
