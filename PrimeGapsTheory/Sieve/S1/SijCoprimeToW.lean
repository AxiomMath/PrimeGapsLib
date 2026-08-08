/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.Substitution.FirstMoment

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Off-diagonal coprimality with the primorial

Shows that nonzero off-diagonal terms are coprime to the primorial.

## Main results

* `lem_S1_sij_coprime_to_W`: Removes the primorial-coprimality restriction.
-/

@[expose] public section

namespace PrimeGaps

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- For a contributing summand under `HasPermissibleSupport`, every off-diagonal entry `s i j`
with `i ≠ j` is coprime to the `W`-trick modulus `W`. The entry divides `boldB u s j`, which
divides some `d j` whose product is coprime to `W`.
-/
@[pg_tag "bg246" "lem_S1_sij_coprime_to_W"]
theorem lem_S1_sij_coprime_to_W {k : ℕ} (R : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hnz : PrimeGaps.lToY lam (boldA u s) ≠ 0 ∧ PrimeGaps.lToY lam (boldB u s) ≠ 0)
    (i j : Fin k) (hij : i ≠ j) :
    Nat.Coprime (s i j) W := by
  have hB := hnz.2
  rw [PrimeGaps.lToY_apply', mul_ne_zero_iff] at hB
  obtain ⟨d, hd, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hB.2
  rw [ite_ne_right_iff] at hterm
  have hcop_dj : (d j).Coprime W :=
    (hlam.coprime_prod_W_of_ne_zero (Finsupp.mem_support_iff.mp hd)).coprime_dvd_left
      (Finset.dvd_prod_of_mem d (Finset.mem_univ j))
  exact hcop_dj.coprime_dvd_left <|
    (show s i j ∣ boldB u s j from Dvd.dvd.mul_left (Finset.dvd_prod_of_mem
      (fun i' ↦ s i' j) (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)) _).trans (hterm.1 j).1

end PrimeGaps
