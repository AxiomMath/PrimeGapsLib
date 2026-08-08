/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.SijD0.Main

/-!
# The S2m sij bound at D0

Aggregator for the `SijD0/` directory, which proves the bound on the sij sum at `D0`. `GTail`
bounds the guarded g-tail, `MertensFactorG` builds the Mertens-type factor for `g`, and
`PairMasterG` gives the pointwise pair-master majorant; `Main` assembles these into
`lem_S2m_sij_D0`. This module only re-exports those parts.
-/
