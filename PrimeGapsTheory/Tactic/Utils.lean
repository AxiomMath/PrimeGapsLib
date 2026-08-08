/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Util.Qq


/-! # Utility functions for metaprogramming -/

@[expose] public section

namespace Lean

open Meta

/-- Apply `e` to a fresh metavariable for each of its remaining arguments, returning the saturated
application along with those metavariables. Every metavariable carries the type of the argument it
occupies, so a later one may have a type mentioning an earlier one. -/
partial def mkAppMVars (e : Expr) (mvars : Array MVarId := #[]) : MetaM (Expr × Array MVarId) := do
  let .forallE _ dom _ _ ← whnf (← inferType e) | return (e, mvars)
  let m ← mkFreshExprMVar dom
  mkAppMVars (.app e m) (mvars.push m.mvarId!)

/-- Assign `mvarId` a `decide` proof of its type, leaving the proof for the kernel to check, as
`decide +kernel` does. -/
def assignDecideProof (mvarId : MVarId) : MetaM Unit := do
  mvarId.assign <| ← mkDecideProof <| ← instantiateMVars <| ← mvarId.getType

end Lean
