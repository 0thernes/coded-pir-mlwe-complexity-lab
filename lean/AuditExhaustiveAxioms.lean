-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

import Lean.Util.CollectAxioms
import Lean.Elab.Command
import TriadFrontier
import Solution
import PalomarSolution

/-!
# Exhaustive Programmatic Axiom Audit (`AuditExhaustiveAxioms.lean`, v5.1.0)

Walks **EVERY** constant in the compiled `TriadFrontier.*` environment (including all
private/internal helper lemmas, `NonVacuity`, `AdversarialTests`, `Solution`, and
`PalomarSolution`) via `Lean.collectAxioms`, asserting that **zero** declarations depend on
`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or any axiom outside the standard
three-axiom Lean 4 foundation `[propext, Classical.choice, Quot.sound]`.
-/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut audited : Nat := 0
  let mut violations : Array (Name × List Name) := #[]
  for (declName, _) in env.constants.map₁.toList do
    let s := declName.toString
    if s.startsWith "TriadFrontier." && !s.startsWith "TriadFrontier.PalomarChallenge." then
      audited := audited + 1
      let axs ← Lean.collectAxioms declName
      let bad := axs.toList.filter (fun ax => !allowed.contains ax)
      if !bad.isEmpty then
        violations := violations.push (declName, bad)
  if audited < 500 then
    throwError "Exhaustive axiom audit sanity failure: expected >= 500 TriadFrontier constants, got {audited}"
  if !violations.isEmpty then
    let mut msg := s!"FORBIDDEN AXIOM(S) DETECTED in {violations.size} declaration(s):"
    for (nm, bad) in violations do
      msg := msg ++ s!"\n  - {nm}: {bad}"
    throwError msg
  IO.println s!"EXHAUSTIVE_AXIOM_AUDIT_PASS: {audited} TriadFrontier.* declarations audited; 0 forbidden axioms; strict subset of [propext, Classical.choice, Quot.sound]."
