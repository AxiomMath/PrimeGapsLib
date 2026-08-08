/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Mathlib.Util.Qq
public import Qq.Macro

/-! # Certificate-independent compact quotation builders -/

@[expose] public section

open Lean Qq

namespace PrimeGapsCert.Meta

private meta def encodeNat (values : Array Nat) : Nat × Nat :=
  have base := values.max?.getD 0 + 1
  (values.foldr (init := 0) fun value rest ↦ rest * base + value, base)

private meta def encodeInt (values : Array Int) : Nat × Nat × Nat :=
  have offset := (-values.min?.getD 0).toNat
  have (code, base) := encodeNat (values.map (· + ↑offset |>.toNat))
  (code, base, offset)

private meta def encodeFin (modulus : Nat) (values : Array Nat) : Nat :=
  values.foldr (init := 0) fun value rest ↦ rest * modulus + value % modulus

/-- Produce a compact natural-valued function by extracting packed digits. -/
meta def mkFastFnNat (values : Array Nat) : Q(Fin $(mkNatLitQ values.size) → Nat) :=
  have (code, base) := encodeNat values
  q(fun i ↦ (($code).div (($base).pow i.val)).mod $base)

/-- Produce a compact integer-valued function by extracting translated packed digits. -/
meta def mkFastFnInt (values : Array Int) : Q(Fin $(mkNatLitQ values.size) → Int) :=
  have (code, base, offset) := encodeInt values
  q(fun i ↦ Int.sub ((($code).div (($base).pow i.val)).mod $base) $offset)

/-- Produce a compact finite-valued function by extracting packed representatives. -/
meta def mkFastFnFin (modulus : Nat) (values : Array Nat) :
    Q(Fin $(mkNatLitQ values.size) → Fin $modulus) :=
  have code := encodeFin modulus values
  have codeQ := mkNatLitQ code
  have positiveQ : Q(decide (0 < $modulus) = true) := reflBoolTrue
  have positiveQ : Q(0 < $modulus) := q(of_decide_eq_true $positiveQ)
  q(fun i ↦ ⟨(($codeQ).div (($modulus).pow i.val)).mod $modulus,
    Nat.mod_lt _ $positiveQ⟩)

end PrimeGapsCert.Meta
