/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Certificate.Fast

import PrimeGapsCert.Meta.Gap600

/-! # Actual certificate for M_k > 4 using packed integer data -/

@[expose] public section

namespace PrimeGaps

/-- Maynard's certificate of `M_105 > 4`, checked entirely with the cleared-denominator integer
infrastructure and compactly encoded coefficient functions. -/
def gap600CertInt : CertificateFastInt 105 := mk_Mk_certificate% "k105d20n15.json"

end PrimeGaps
