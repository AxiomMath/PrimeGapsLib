/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Meta.Basic
public meta import PrimeGapsCert.Meta.Basic
public meta import PrimeGapsTheory.Sieve.Certificate.Fast
public meta import PrimeGapsTheory.Tactic.Utils

import PrimeGapsTheory.Sieve.Certificate.Fast

/-! # Gap 600 certificate elaborator -/

@[expose] public section

open Lean Meta Elab Term Qq

namespace PrimeGaps

/-- Build a cleared-denominator certificate from packed triples in a JSON file. -/
elab "mk_Mk_certificate%" filename:str : term <= typ => do
  let ⟨2, ~q(Type), ~q(CertificateFastInt $kE)⟩ ← inferTypeQ typ
    | throwError "Invalid certificate type"
  let .some dimension ← (Meta.evalNat kE).run |
    throwError "The sieve dimension {kE} is not a numeral"
  let .some cwd := (System.FilePath.mk (← readThe Core.Context).fileName).parent
    | throwError "Failed to get current working directory"
  let contents ← IO.FS.readFile (cwd / filename.getString)
  let .ok json := Json.parse contents | throwError "Failed to parse certificate"
  let .arr entries := json | throwError "Certificate must be an array"
  let mut data : Array (ℕ × ℕ × ℤ) := #[]
  for entry in entries do
    let .arr #[b, c, a] := entry | throwError s!"Invalid certificate entry {entry}"
    let .ok b := b.getNat? | throwError s!"Invalid certificate entry {entry}"
    let .ok c := c.getNat? | throwError s!"Invalid certificate entry {entry}"
    let .ok a := a.getInt? | throwError s!"Invalid certificate entry {entry}"
    data := data.push (b, c, a)
  let entryCount := data.size
  let cBound := (data.map (·.2.1)).max?.getD 0 + 1
  let cRange := 2 * cBound - 1
  let bBound := (data.map (·.1)).max?.getD 0 + 1
  let bRange := 2 * bBound - 1
  let (certificate, metavariables) ← mkAppMVars <| mkAppN (mkConst ``CertificateFastInt.mk)
    #[kE, mkNatLit entryCount, mkNatLit cRange, mkNatLit cBound]
  metavariables[1]!.assign (mkNatLit bRange)
  metavariables[2]!.assign (mkNatLit bBound)
  metavariables[4]!.assign <| PrimeGapsCert.Meta.mkFastFnNat <|
    .ofFn fun i : Fin cRange ↦ maynardGFast i 2 dimension
  metavariables[6]!.assign <| PrimeGapsCert.Meta.mkFastFnNat <|
    .ofFn fun i : Fin cRange ↦ maynardGFast i 2 (dimension - 1)
  metavariables[8]!.assign <| PrimeGapsCert.Meta.mkFastFnFin bBound <| data.map (·.1)
  metavariables[9]!.assign <| PrimeGapsCert.Meta.mkFastFnFin cBound <| data.map (·.2.1)
  metavariables[10]!.assign <| PrimeGapsCert.Meta.mkFastFnInt <| data.map (·.2.2)
  for index in [0, 3, 5, 7, 11] do
    assignDecideProof metavariables[index]!
  instantiateMVars certificate

end PrimeGaps
