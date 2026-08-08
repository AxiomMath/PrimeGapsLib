/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The sieve-positivity window

Under the enlargement room `(1+ε)·θ < 1` (equivalently `1+ε < 1/θ` for `θ > 0`), the
sieve-positivity parameter window is nonempty.

The window is the set of `(δ, ρ)` with `δ ∈ (0, θ/2)`, `ρ ∈ (1, 2)`, and
`(θ/2 − δ)·Q > ρ`, where `Q` is the certified enlarged Rayleigh value.  Such a pair
is what `lem_mollify` / `enlarged_S_positive` need in order to instantiate the
witness inequality at `ρ ≥ 1` (so `⌊ρ+1⌋ ≥ 2`, giving `DHL[k,2]`).  The only input is
the sieve criterion `2/θ < Q`.

## Main results

* `positivity_window_nonempty` — the window is nonempty under the enlargement room.
* `certificateParameters_admissible` — the parameter values `θ = 4995/10000`, `ε = 1/25`,
  `Q = 4004306/1000000` satisfy both `(1+ε)θ < 1` and `2/θ < Q`.
* `certificateParameters_window_nonempty` — the window is nonempty at those values.
-/

@[expose] public section

namespace Gaps246

/-- **The sieve-positivity window is nonempty.**  If `0 < θ < 1/2` and the enlarged
Rayleigh value `Q` clears the sieve criterion `2/θ < Q`, then there is a level margin
`δ ∈ (0, θ/2)` and a multiplier `ρ ∈ (1, 2)` with `(θ/2 − δ)·Q > ρ`.

This is the sieve-positivity window consumed by `enlarged_S_positive` / `lem_mollify`. -/
theorem positivity_window_nonempty (θ Q : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hQ : 2 / θ < Q) :
    ∃ δ ρ : ℝ, δ ∈ Set.Ioo 0 (θ / 2) ∧ ρ ∈ Set.Ioo 1 2 ∧ (θ / 2 - δ) * Q > ρ := by
  have h2θpos : (0 : ℝ) < 2 / θ := div_pos (by norm_num) hθ0
  have hQpos : 0 < Q := lt_trans h2θpos hQ
  -- `2/θ < Q` clears the criterion: `1 < (θ/2)·Q`.
  have h2 : 2 < Q * θ := (div_lt_iff₀ hθ0).mp hQ
  have hM1 : 1 < θ / 2 * Q := by nlinarith [h2]
  set M : ℝ := θ / 2 * Q with hMdef
  -- pick `ρ = (1 + min 2 M)/2 ∈ (1, min 2 M) ⊆ (1, 2)`, and `ρ < M`.
  set u : ℝ := min 2 M with hudef
  have hu2 : u ≤ 2 := min_le_left _ _
  have huM : u ≤ M := min_le_right _ _
  have hu1 : 1 < u := lt_min (by norm_num) hM1
  set ρ : ℝ := (1 + u) / 2 with hρdef
  have hρ1 : 1 < ρ := by rw [hρdef]; linarith
  have hρ2 : ρ < 2 := by rw [hρdef]; linarith
  have hρM : ρ < M := by rw [hρdef]; nlinarith [huM, hM1]
  have hρpos : 0 < ρ := lt_trans one_pos hρ1
  -- pick `δ = (θ/2 − ρ/Q)/2`, so `θ/2 − δ = (θ/2 + ρ/Q)/2` and `(θ/2−δ)·Q = (M+ρ)/2 > ρ`.
  set p : ℝ := ρ / Q with hpdef
  have hpQ : p * Q = ρ := div_mul_cancel₀ ρ (ne_of_gt hQpos)
  have hp_lt : p < θ / 2 := (div_lt_iff₀ hQpos).mpr (by rw [← hMdef]; exact hρM)
  have hp_pos : 0 < p := div_pos hρpos hQpos
  set δ : ℝ := (θ / 2 - p) / 2 with hδdef
  refine ⟨δ, ρ, ⟨?_, ?_⟩, ⟨hρ1, hρ2⟩, ?_⟩
  · rw [hδdef]; linarith
  · rw [hδdef]; linarith
  · rw [hδdef]; nlinarith [hpQ, hρM, hMdef]

/-- The parameter values `θ = 4995/10000`, `ε = 1/25`, `Q = 4004306/1000000` satisfy the
enlargement room `(1+ε)·θ < 1` (`= 0.51948 < 1`) and the sieve criterion `2/θ < Q`
(`2/θ = 4.00400… < 4.004306`). -/
theorem certificateParameters_admissible :
    (1 + (1 : ℝ) / 25) * (4995 / 10000) < 1 ∧ 2 / (4995 / 10000 : ℝ) < 4004306 / 1000000 :=
  ⟨by norm_num, by norm_num⟩

/-- **The window is nonempty at the parameter values above.**  Instantiates
`positivity_window_nonempty` at `θ = 4995/10000`, `ε = 1/25`, `Q = 4004306/1000000`. -/
theorem certificateParameters_window_nonempty :
    ∃ δ ρ : ℝ, δ ∈ Set.Ioo 0 ((4995 / 10000 : ℝ) / 2) ∧ ρ ∈ Set.Ioo 1 2 ∧
      ((4995 / 10000 : ℝ) / 2 - δ) * (4004306 / 1000000) > ρ :=
  positivity_window_nonempty (4995 / 10000) (4004306 / 1000000)
    (by norm_num) (by norm_num) (by norm_num)

end Gaps246
