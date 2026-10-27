/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecCrossing_LemPieces
public import Eight.Level.Pieces
public import Eight.Level.Presents
public import Eight.Level.Cert
public import Eight.Level.Min
public import Eight.Level.Arith
public import StepMachines.Prog.GridLoop
public import Eight.Level.Defs
public import Eight.SecPseudocode_Levels
public import Eight.Level.SecPseudocode
public import Eight.SecLevel_EStar

/-! # Lemma 2 from the eight-square identity, in the form that the networks of a grid need

The files of proof/networks/Eight/Level/ take the interface statements of
proof/networks/Eight/Level/Defs.lean as hypotheses. Here one of them, `Level.StPieces`, is derived
from Lemma 2 (`Eight.lemPieces` and `Eight.stFact` of
proof/networks/Eight/SecCrossing_LemPieces.lean), with ρ = 11/12 (`Eight.rho`) and t = ⌈λ/3⌉
(`Eight.tOf`). -/

public section

namespace Eight

open Groundwork Groundwork.Prog Paper

/-- Lemma 2 in the form that the networks of a grid need. -/
theorem stPieces : Level.StPieces := Level.stPieces_of_lemPieces lemPieces stFact

end Eight
