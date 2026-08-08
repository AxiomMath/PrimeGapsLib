/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Lean.Elab.Command
public meta import Lean.Elab.Command

import Mathlib.Tactic.TypeStar

/-! # Batched certificate theorem elaborators -/

@[expose] public section

open Lean Meta Elab Term Command

namespace PrimeGaps

/-- Generate the requested number of consecutively indexed theorem cases. -/
elab "mk_batched_theorem" count:num fi:ident : command => do
  have count := count.getNat
  have f := fi.getId
  let [(_, [])] ← resolveGlobalName f | throwError "Invalid input"
  for i in List.range count do
    have thmName := mkIdent (f.str s!"case_{i}")
    elabCommand <| ← `(command|theorem $thmName : $fi $(quote i) := by decide +kernel)

namespace CertificateMeta

/-- Assemble a dependent function on `Fin 1` from its value at zero. -/
def batchedFinOne {motive : Fin 1 → Sort*} (zero : motive 0) : ∀ i, motive i :=
  fun i ↦ Fin.cases zero (fun j ↦ Fin.elim0 j) i

/-- Assemble a dependent function on `Fin (m + n)` from functions on its two summands. -/
def batchedFinAdd {m n : Nat} {motive : Fin (m + n) → Sort*}
    (left : ∀ i, motive (Fin.castAdd n i)) (right : ∀ i, motive (Fin.natAdd m i)) :
    ∀ i, motive i :=
  fun i ↦ Fin.addCases left right i

end CertificateMeta
end PrimeGaps

private meta def batchedProofTree (theoremNames : Array Name) (start size : Nat) : String :=
  if size = 0 then
    "fun i ↦ Fin.elim0 i"
  else if size = 1 then
    s!"PrimeGaps.CertificateMeta.batchedFinOne {theoremNames[start]!}"
  else
    let leftSize := size / 2
    let rightSize := size - leftSize
    s!"PrimeGaps.CertificateMeta.batchedFinAdd \
      ({batchedProofTree theoremNames start leftSize}) \
      ({batchedProofTree theoremNames (start + leftSize) rightSize})"

/-- Assemble all cases generated for one indexed theorem family into a dependent function. -/
elab "combine_batched_theorems%" family:ident count:num : term <= expectedType => do
  let [(theoremName, [])] ← resolveGlobalName family.getId
    | throwError "Expected one unambiguous theorem family"
  let env ← getEnv
  let mut theoremNames : Array Name := #[]
  for i in [:count.getNat] do
    let caseName := theoremName.str s!"case_{i}"
    unless env.contains caseName do
      throwError "Unknown batched theorem `{caseName}`"
    theoremNames := theoremNames.push caseName
  let source := batchedProofTree theoremNames 0 count.getNat
  let .ok termSyntax := Parser.runParserCategory env `term source
    | throwError "Failed to construct the batched proof function"
  withOptions (fun options ↦ options.set `exponentiation.threshold 3000) do
    elabTerm termSyntax expectedType
