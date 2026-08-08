/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.Totient.Lcm
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Decoupling least common multiples

Reindexes the first-moment least-common-multiple sum by diagonal and off-diagonal factors.

## Main results

* `lem_S1_decouple_lcm`: Expresses the primed sum in decoupled coordinates.
-/

@[expose] public section

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

/-- of `1/∏ f(lcm(dᵢ,eᵢ))` via a per-coordinate split
`hsplit: 1/f(lcm a b) = 1/(f a · f b) · ∑_{u∣gcd a b} G u`. The `S₁` (`f = id`, `G = φ`) and
`S₂⁽ᵐ⁾` (`f = φ`, `G = g`) decouple lemmas are instantiations, differing only in `(f, G)`, the
split lemma, and the coprimality guard.
-/
theorem lem_decouple_general {k : ℕ}
    (guard : (Fin k → ℕ) → (Fin k → ℕ) → Prop) [∀ d e, Decidable (guard d e)]
    (f G : ℕ → ℝ)
    (D : Finset (Fin k → ℕ)) (lam : (Fin k → ℕ) → ℝ)
    (hsupp : ∀ t, lam t ≠ 0 →
      (∀ i, 0 < t i) ∧ (∀ i, Squarefree (t i)) ∧ (∀ i j, i ≠ j → Nat.Coprime (t i) (t j)))
    (hsplit : ∀ a b : ℕ, Squarefree a → Squarefree b → 0 < a → 0 < b →
        (1 : ℝ) / f (Nat.lcm a b) = (1 : ℝ) / (f a * f b) * ∑ u ∈ (Nat.gcd a b).divisors, G u) :
    (∑ d ∈ D, ∑ e ∈ D, if guard d e then lam d * lam e / (∏ i, f (Nat.lcm (d i) (e i))) else 0) =
    ∑ d ∈ D, ∑ e ∈ D,
        (∑ u ∈ Fintype.piFinset (fun i ↦ (Nat.gcd (d i) (e i)).divisors), (∏ i, G (u i))) *
        (if guard d e then lam d * lam e / (∏ i, (f (d i) * f (e i))) else 0) := by
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  by_cases hg : guard d e
  · simp only [if_pos hg]
    by_cases hld : lam d = 0
    · simp [hld]
    by_cases hle : lam e = 0
    · simp [hle]
    obtain ⟨hdpos, hdsf, _⟩ := hsupp d hld
    obtain ⟨hepos, hesf, _⟩ := hsupp e hle
    have core : (1 : ℝ) / (∏ i, f (Nat.lcm (d i) (e i))) =
        (∑ u ∈ Fintype.piFinset (fun i ↦ (Nat.gcd (d i) (e i)).divisors), (∏ i, G (u i))) *
            (1 / (∏ i, (f (d i) * f (e i)))) := by
      rw [one_div, ← Finset.prod_inv_distrib]
      simp only [← one_div]
      rw [Finset.prod_congr rfl
        (fun i _ ↦ hsplit (d i) (e i) (hdsf i) (hesf i) (hdpos i) (hepos i)),
        Finset.prod_mul_distrib, Finset.prod_univ_sum,
        one_div (∏ i, (f (d i) * f (e i))), ← Finset.prod_inv_distrib]
      simp only [one_div]
      rw [mul_comm]
    rw [div_eq_mul_one_div (lam d * lam e), div_eq_mul_one_div (lam d * lam e), core]
    ring
  · simp only [if_neg hg, mul_zero]

/-- The `S₁` coordinate-decoupling: over weights with permissible support (positive, squarefree,
pairwise-coprime coordinates), `∑ λ(d) λ(e) / ∏ᵢ lcm(dᵢ, eᵢ)` under the cross-coprimality guard
equals the sum, weighted by `∏ᵢ φ(uᵢ)` over common divisors `u`, of `∑ λ(d) λ(e) / ∏ᵢ dᵢ eᵢ`. The
`f = id`, `G = φ` instance of `lem_decouple_general`, reducing per coordinate to `lem_lcm_split`.
-/
@[pg_tag "bg246" "lem_S1_decouple_lcm"]
theorem lem_S1_decouple_lcm {k : ℕ} (D : Finset (Fin k → ℕ)) (lam : (Fin k → ℕ) → ℝ)
    (hsupp : ∀ t, lam t ≠ 0 →
      (∀ i, 0 < t i) ∧ (∀ i, Squarefree (t i)) ∧ (∀ i j, i ≠ j → Nat.Coprime (t i) (t j))) :
    (∑ d ∈ D, ∑ e ∈ D, if (∀ i j, i ≠ j → Nat.Coprime (d i) (e j))
        then lam d * lam e / (∏ i, (Nat.lcm (d i) (e i) : ℝ)) else 0)
      =
    ∑ d ∈ D, ∑ e ∈ D, (∑ u ∈ Fintype.piFinset (fun i ↦ (Nat.gcd (d i) (e i)).divisors),
            (∏ i, (Nat.totient (u i) : ℝ))) * (if (∀ i j, i ≠ j → Nat.Coprime (d i) (e j))
            then lam d * lam e / (∏ i, ((d i : ℝ) * e i)) else 0) :=
  lem_decouple_general (fun d e ↦ ∀ i j, i ≠ j → Nat.Coprime (d i) (e j))
    (fun n ↦ (n : ℝ)) (fun u ↦ (Nat.totient u : ℝ)) D lam hsupp
    (fun a b _ _ ha hb ↦ by
      have hq := lem_lcm_split a b ha hb
      have h2 := congrArg (fun q : ℚ ↦ (q : ℝ)) hq
      push_cast at h2 ⊢
      convert h2 using 2)

end PrimeGaps
