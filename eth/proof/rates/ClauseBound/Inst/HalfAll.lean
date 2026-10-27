/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfSpec
public import ClauseBound.Inst.HalfFact
public import ClauseBound.Inst.HalfLabs
public import ClauseBound.Inst.HalfEnc
public import ClauseBound.Inst.HalfPad
public import ClauseBound.Inst.HalfPar

/-! # The pieces with ρ = 1/√2 as programs: the values that the programs return

`stVal_all` feeds the lemmas `stTopF`, `stBotF` and `stEnc` into `stVal`: with a pad that is long
enough, the programs return the entries of the matrices.
No hypothesis is left. -/

public section

namespace ClauseBound.Inst.Half

/-- With a pad that is long enough, the programs return the entries of the matrices. -/
theorem stVal_all : StVal := stVal stTopF stBotF stEnc

end ClauseBound.Inst.Half
