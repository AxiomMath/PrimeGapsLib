/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Lattice.Nat


/-!
# Explicit epsilon-enlarged certificates

Exact rational formulas for the simplex pairings of monomial-symmetric basis polynomials.

## Main definitions

* `Multiset.embeddings`: the exponent vectors realising a given signature.
* `PrimeGaps.facMoment`: the factorial moment of a pair of signatures.
* `PrimeGaps.IEpsExplicit`: the enlarged-simplex pairing of two basis polynomials.
* `PrimeGaps.radialExplicit`: the radial factor of a shrunken-simplex monomial integral.
* `PrimeGaps.JEpsExplicit`: the one-coordinate marginal pairing of two basis polynomials.
* `PrimeGaps.EpsCertificateExplicit`: a finite rational certificate with quotient greater than
  four.
-/

@[expose] public section

open Finset Nat

namespace Multiset

/-- The exponent vectors in `Fin k → ℕ` whose multisets of nonzero entries equal the nonzero
entries of `m`. -/
def embeddings (m : Multiset ℕ) (k : ℕ) : Finset (Fin k → ℕ) :=
  {a ∈ Fintype.piFinset fun _ ↦ Finset.range (m.sup + 1) |
    (ofList (.ofFn a)).filter (· ≠ 0) = m.filter (· ≠ 0)}

theorem mem_embeddings_iff {m : Multiset ℕ} {k : ℕ} {a : Fin k → ℕ} :
    a ∈ embeddings m k ↔ (ofList (.ofFn a)).filter (· ≠ 0) = m.filter (· ≠ 0) := by
  rw [embeddings, Finset.mem_filter, and_iff_right_iff_imp]
  simp_rw [Fintype.mem_piFinset, mem_range_succ_iff]
  rintro ha i
  by_cases! hi : a i = 0
  · simp [hi]
  suffices a i ∈ m.filter (· ≠ 0) from le_sup <| by grind [mem_filter]
  exact ha ▸ mem_filter.mpr ⟨by simp, hi⟩

end Multiset

namespace PrimeGaps

/-- The factorial moment of signatures `α` and `β` in `k` variables:
`∑ A ∈ α.embeddings k, ∑ B ∈ β.embeddings k, ∏ i, (A i + B i)!`. -/
def facMoment (k : ℕ) (α β : Multiset ℕ) : ℚ :=
  ∑ A ∈ α.embeddings k, ∑ B ∈ β.embeddings k, ∏ i : Fin k, (A i + B i)!

/-- The rational enlarged-simplex pairing of the basis polynomials indexed by `(a₁, α₁)` and
`(a₂, α₂)`. The pair `(a, α)` represents `(1 + ε - ∑ i, t i) ^ a * P_α(t)`, where `P_α` is the
monomial-symmetric polynomial with exponent signature `α`. -/
def IEpsExplicit (k : ℕ) (ε : ℚ) (a₁ : ℕ) (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ) : ℚ :=
  (1 + ε) ^ (k + (a₁ + a₂) + (α₁.sum + α₂.sum)) *
  (a₁ + a₂)! / (k + (a₁ + a₂) + (α₁.sum + α₂.sum))! * facMoment k α₁ α₂

/-- The radial factor in a shrunken-simplex monomial integral. If `c : Fin K → ℕ` and
`q = K + ∑ i, c i`, then `∫ t in (1 - ε) • 𝓡 K, (1 + ε - ∑ i, t i) ^ e * ∏ i, t i ^ c i` equals
`radialExplicit q ε e * ∏ i, (c i)!`. -/
def radialExplicit (q : ℕ) (ε : ℚ) (e : ℕ) : ℚ :=
  (1 - ε) ^ q * ∑ m ∈ range (e + 1), e.choose m * (2 * ε) ^ (e - m) * (1 - ε) ^ m * m ! / (m + q)!

/-- The rational pairing of one fixed coordinate marginal of the basis polynomials indexed by
`(a₁, α₁)` and `(a₂, α₂)`, integrated over the `(1 - ε)`-shrunken simplex. By symmetry, the
sum of the pairings over all `k` coordinates is `k * JEpsExplicit k ε a₁ α₁ a₂ α₂`. -/
def JEpsExplicit (k : ℕ) (ε : ℚ) (a₁ : ℕ) (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ) : ℚ :=
  ∑ r₁ ∈ insert 0 α₁.toFinset, ∑ r₂ ∈ insert 0 α₂.toFinset,
    (r₁ ! * a₁ ! / (a₁ + r₁ + 1)!) * (r₂ ! * a₂ ! / (a₂ + r₂ + 1)!) *
    radialExplicit (k - 1 + ((α₁.sum - r₁) + (α₂.sum - r₂))) ε ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
    facMoment (k - 1) (α₁.erase r₁) (α₂.erase r₂)

/-- A finite rational coefficient family whose enlarged-simplex pairing is positive and whose total
marginal pairing is more than four times its enlarged-simplex pairing. -/
structure EpsCertificateExplicit (k : ℕ) (ε : ℚ) : Type where
  /-- The number of basis polynomials. -/
  N : ℕ
  /-- The exponent of the slack factor in each basis polynomial. -/
  a : Fin N → ℕ
  /-- The exponent signature of the monomial-symmetric factor in each basis polynomial. -/
  α : Fin N → Multiset ℕ
  /-- The coefficients of the basis elements. -/
  coeff : Fin N → ℚ
  /-- The total marginal quadratic form is more than four times the enlarged-simplex form. -/
  cert : 4 * ∑ i, ∑ j, coeff i * coeff j * IEpsExplicit k ε (a i) (α i) (a j) (α j) <
    k * ∑ i, ∑ j, coeff i * coeff j * JEpsExplicit k ε (a i) (α i) (a j) (α j)

end PrimeGaps
