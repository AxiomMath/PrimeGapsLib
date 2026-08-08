/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.Error.Main

/-!
# The S2m error term

Aggregator for the `Error/` directory, which bounds the total error contribution of the
second-moment sum. `Basic` sets up the sieve weights and the error contributions, `TauGrowth`
and `TauFourSums` supply the divisor-function estimates, and `WindowError` bounds the
prime-counting discrepancy over a dyadic window; `Main` assembles these into
`exists_totalErrorContribution_le`. This module only re-exports those parts.
-/
