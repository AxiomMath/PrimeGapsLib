/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.NumberTheory.BombieriVinogradov

/-!
# A Bombieri–Vinogradov-only certificate-admissible level

`lem_theta_bv`: any strict certificate value `Q > 4` leaves a nonempty
window `2/Q < θ < 1/2`, and Bombieri–Vinogradov supplies distribution at every
such `θ`.  The proof chooses the midpoint of that interval.
-/

@[expose] public section

namespace Gaps246

/-- **`lem_theta_bv`.** Under Bombieri–Vinogradov (`hBV` gives level of distribution
for every `θ' < 1/2`), there is a certificate-admissible level `θ` at which the primes
have level of distribution `θ`; the proof takes the midpoint of `(2/Q, 1/2)`. This is
the sole analytic black box of the `246` development, as in the 600 development. -/
theorem lem_theta_bv (hBV : BombieriVinogradov) (ε Q : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hQ : 4 < Q) :
    ∃ θ : ℝ, θ < 1 / 2 ∧ 2 / θ < Q ∧ 1 + ε < 1 / θ ∧
      Nat.HasLevelOfDistribution Set.univ θ 1 := by
  have hQ0 : 0 < Q := by linarith
  have hlow : 2 / Q < (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hQ0]
    linarith
  let θ : ℝ := (2 / Q + 1 / 2) / 2
  have hθlow : 2 / Q < θ := by
    dsimp only [θ]
    linarith
  have hθhalf : θ < 1 / 2 := by
    dsimp only [θ]
    linarith
  have hθ0 : 0 < θ := lt_trans (div_pos (by norm_num) hQ0) hθlow
  have hθQ : 2 / θ < Q := by
    rw [div_lt_iff₀ hθ0]
    rw [div_lt_iff₀ hQ0] at hθlow
    nlinarith
  have hθε : 1 + ε < 1 / θ := by
    rw [lt_div_iff₀ hθ0]
    nlinarith
  exact ⟨θ, hθhalf, hθQ, hθε, hBV.hasLevelOfDistribution hθhalf⟩

end Gaps246
