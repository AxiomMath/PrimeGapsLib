/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

import PrimeGapsTheory.Tactic.PaperTag

/-! # Power sums -/

@[expose] public section

/-- The polynomial `∑_{i=0}^{k-1} t_i`. -/
@[pg_tag "bg246" "not_power_sum"]
scoped[PrimeGaps] notation "P₁ " k:max => MvPolynomial.psum (Fin k) ℝ 1

/-- The polynomial `∑_{i=0}^{k-1} t_i ^ 2`. -/
@[pg_tag "bg246" "not_power_sum"]
scoped[PrimeGaps] notation "P₂ " k:max => MvPolynomial.psum (Fin k) ℝ 2
