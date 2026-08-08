/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Sparse.Gen
public meta import PrimeGapsCert.Gap246.Sparse.Gen

/-! # In-process store for data derived from the source certificate

Each generator stage records the structures it derives from the sole external JSON file in a
persistent environment extension, and later stages and check emitters read them back through
the import graph.  The stored values are untrusted: every emitted declaration is checked by
the kernels in `PrimeGapsCert.Gap246.Kernel`.
-/

@[expose] public section

namespace cert246Data.Emit

open Lean

/-- One generator stage's contribution to the derived-data store. -/
inductive DerivedEntry where
  /-- The shared stage: dimensions and the parsed generator input. -/
  | shared (dims : Gen.SharedDims) (input : Gen.SharedInput)
  /-- The moment stage: dimensions and the reconstructed moment arrays. -/
  | moments (dims : Gen.Dims) (top predecessor : Array ℕ)
  /-- The sparse-LHS stage: dimensions. -/
  | lhs (dims : SparseGen.LhsDims)
  /-- The sparse-RHS stage: dimensions. -/
  | rhs (dims : SparseGen.RhsDims)

/-- Everything derived so far from the source certificate. -/
structure Derived where
  shared : Option (Gen.SharedDims × Gen.SharedInput) := none
  moments : Option (Gen.Dims × Array ℕ × Array ℕ) := none
  lhsDims : Option SparseGen.LhsDims := none
  rhsDims : Option SparseGen.RhsDims := none
attribute [nolint docBlame] Derived.shared Derived.moments Derived.lhsDims Derived.rhsDims

meta instance : Inhabited Derived := ⟨{}⟩

/-- Fold one recorded entry into the store. -/
meta def Derived.add (state : Derived) : DerivedEntry → Derived
  | .shared dims input => { state with shared := some (dims, input) }
  | .moments dims top predecessor => { state with moments := some (dims, top, predecessor) }
  | .lhs dims => { state with lhsDims := some dims }
  | .rhs dims => { state with rhsDims := some dims }

/-- Store holding every structure derived from the source certificate. -/
meta initialize derivedExt : SimplePersistentEnvExtension DerivedEntry Derived ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Derived.add
    addImportedFn := fun entries ↦ entries.flatten.foldl Derived.add {}
  }

/-- Record one generator stage's derived output. -/
meta def recordDerived (entry : DerivedEntry) : CoreM Unit :=
  modifyEnv fun env ↦ derivedExt.addEntry env entry

/-- Read the recorded shared dimensions and generator input. -/
meta def readShared : CoreM (Gen.SharedDims × Gen.SharedInput) := do
  let some result := (derivedExt.getState (← getEnv)).shared
    | throwError "cert246Data: the shared certificate data has not been generated"
  return result

/-- Read the recorded shared dimensions. -/
meta def readSharedDims : CoreM Gen.SharedDims := return (← readShared).1

/-- Read the recorded moment dimensions and reconstructed moment arrays. -/
meta def readMoments : CoreM (Gen.Dims × Array ℕ × Array ℕ) := do
  let some result := (derivedExt.getState (← getEnv)).moments
    | throwError "cert246Data: the moment data has not been generated"
  return result

/-- Read the recorded moment dimensions. -/
meta def readDims : CoreM Gen.Dims := return (← readMoments).1

/-- Read the recorded sparse-LHS dimensions. -/
meta def readLhsDims : CoreM SparseGen.LhsDims := do
  let some result := (derivedExt.getState (← getEnv)).lhsDims
    | throwError "cert246Data: the sparse-LHS data has not been generated"
  return result

/-- Read the recorded sparse-RHS dimensions. -/
meta def readRhsDims : CoreM SparseGen.RhsDims := do
  let some result := (derivedExt.getState (← getEnv)).rhsDims
    | throwError "cert246Data: the sparse-RHS data has not been generated"
  return result

end cert246Data.Emit
