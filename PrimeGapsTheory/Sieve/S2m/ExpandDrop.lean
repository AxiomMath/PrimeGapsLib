/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.ExpandDrop.Main

/-!
# Expansion and decoupling of the second-moment sum

Aggregator for the `ExpandDrop/` directory, which expands the transformed second-moment sum
and bounds the contribution of the failed coprimality conditions. `Expand` performs the
triple-sum expansion, `Drop` introduces the failure mass, and `GSumBounds`, `Collision` and
`Blocks` supply the majorants controlling it; `Main` assembles these into
`lem_S2m_expand_drop`. This module only re-exports those parts.
-/
