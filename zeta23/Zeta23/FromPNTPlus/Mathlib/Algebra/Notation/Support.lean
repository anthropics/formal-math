/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 10e1218932db7e2432aa5881d750acb819e91f19, file
PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint
tooling (import Architect, blueprint_comment blocks, @[blueprint ...] attributes),
redirected intra-project imports to Zeta23.FromPNTPlus.*.  Mathematical content unchanged.
Modified 2026 by Anthropic PBC.
-/
import Mathlib.Algebra.Notation.Support

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
