/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.SieveDatumEval.KFold

/-!
# Evaluating the sieve sum against a smooth weight

Partial summation for a `SieveDatum` against a smooth weight, the layer decomposition of
`sieveE`, and the k-fold partial-summation bound.  Split across `SieveDatumEval/`; this
module re-exports the parts.

## Main results

* `sieveDatum_kfold_partial_sum`
-/
