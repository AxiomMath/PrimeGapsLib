/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting

/-! # The faster statement file

This file is built by humans to act as the standard to check the main theorems against, using
the comparator. The theorems here skip the large numerical certificate, so that the comparator
finishes faster.

As a cost, this file requires stating the type of the certificate.

-/

@[expose] public section

open Nat Real Finset

section BombieriVinogradov

noncomputable def Real.primeCountingZMod (x : ℝ) (q : ℕ) (a : ZMod q) : ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ≤ x}.ncard

-- from PNT+
noncomputable def pi (x : ℝ) : ℝ :=
  ⌊x⌋₊.primeCounting

local notation "π(" x "; " q ", " a ")" => Real.primeCountingZMod x q a
local notation "π(" x ")" => pi x

-- Corresponds to (1.3) in James Maynard's paper *Small gaps between primes*.
def BombieriVinogradov : Prop := ∀ θ < (1 / 2 : ℝ), ∀ A ≥ (1 : ℝ), ∃ c > (0 : ℝ), ∀ x ≥ (3 : ℝ),
    ∑ q ∈ Icc (1 : ℕ) ⌊x ^ θ⌋₊, ⨆ a : (ZMod q)ˣ, |(π(x; q, a) - π(x) / φ q : ℝ)| ≤ c * x / x.log ^ A

end BombieriVinogradov

section EpsCertificate

namespace Multiset

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

def facMoment (k : ℕ) (α β : Multiset ℕ) : ℚ :=
  ∑ A ∈ α.embeddings k, ∑ B ∈ β.embeddings k, ∏ i : Fin k, (A i + B i)!

def IEpsExplicit (k : ℕ) (ε : ℚ) (a₁ : ℕ) (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ) : ℚ :=
  (1 + ε) ^ (k + (a₁ + a₂) + (α₁.sum + α₂.sum)) *
  (a₁ + a₂)! / (k + (a₁ + a₂) + (α₁.sum + α₂.sum))! * facMoment k α₁ α₂

def radialExplicit (q : ℕ) (ε : ℚ) (e : ℕ) : ℚ :=
  (1 - ε) ^ q * ∑ m ∈ range (e + 1), e.choose m * (2 * ε) ^ (e - m) * (1 - ε) ^ m * m ! / (m + q)!

def JEpsExplicit (k : ℕ) (ε : ℚ) (a₁ : ℕ) (α₁ : Multiset ℕ) (a₂ : ℕ) (α₂ : Multiset ℕ) : ℚ :=
  ∑ r₁ ∈ insert 0 α₁.toFinset, ∑ r₂ ∈ insert 0 α₂.toFinset,
    (r₁ ! * a₁ ! / (a₁ + r₁ + 1)!) * (r₂ ! * a₂ ! / (a₂ + r₂ + 1)!) *
    radialExplicit (k - 1 + ((α₁.sum - r₁) + (α₂.sum - r₂))) ε ((a₁ + r₁ + 1) + (a₂ + r₂ + 1)) *
    facMoment (k - 1) (α₁.erase r₁) (α₂.erase r₂)

structure EpsCertificateExplicit (k : ℕ) (ε : ℚ) : Type where
  N : ℕ
  a : Fin N → ℕ
  α : Fin N → Multiset ℕ
  coeff : Fin N → ℚ
  cert : 4 * ∑ i, ∑ j, coeff i * coeff j * IEpsExplicit k ε (a i) (α i) (a j) (α j) <
    k * ∑ i, ∑ j, coeff i * coeff j * JEpsExplicit k ε (a i) (α i) (a j) (α j)

inductive ExistsEpsCert (k : ℕ) : Prop where
  | mk : {ε : ℚ} → 0 ≤ ε → ε ≤ 1 → EpsCertificateExplicit k ε → ExistsEpsCert k

end PrimeGaps

end EpsCertificate

section Challenges

theorem bombieriVinogradov_implies_prime_gap_le_600 :
    BombieriVinogradov → ∀ n₀ : ℕ, ∃ p q : ℕ, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 600 :=
  sorry

theorem bombieriVinogradov_implies_nth_prime_gap_le_600 :
    BombieriVinogradov → ∀ n₀ : ℕ, ∃ n ≥ n₀, (n + 1).nth Nat.Prime ≤ n.nth Nat.Prime + 600 :=
  sorry

theorem bombieriVinogradov_and_existsEpsCert50_imply_prime_gap_le_246 :
    BombieriVinogradov → PrimeGaps.ExistsEpsCert 50 →
    ∀ n₀ : ℕ, ∃ p q : ℕ, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 246 :=
  sorry

theorem bombieriVinogradov_and_existsEpsCert50_imply_nth_prime_gap_le_246 :
    BombieriVinogradov → PrimeGaps.ExistsEpsCert 50 →
    ∀ n₀ : ℕ, ∃ n ≥ n₀, (n + 1).nth Nat.Prime ≤ n.nth Nat.Prime + 246 :=
  sorry

end Challenges
