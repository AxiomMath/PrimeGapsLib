/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.GammaLogSum

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The Maynard sieve datum

Constructs the sieve datum associated with the Maynard gamma function and the primorial.

## Main definitions

* `maynardGamma`: The multiplicative Maynard gamma function.
* `maynardSieveDatum`: The sieve datum determined by the Maynard gamma function.

## Main results

* `maynardSieveDatum_γ_prime`: Evaluates the gamma function of the datum at primes.
-/

@[expose] public section

open scoped BigOperators

namespace PrimeGaps

/-- The prime values of Maynard's `γ_g`: `0` if `p ∣ V`, else `p/(p-1)`. -/
noncomputable def maynardGammaPrime (V : ℕ) (p : ℕ) : ℝ :=
  if p ∣ V then 0 else (p : ℝ) / ((p : ℝ) - 1)

/-- Maynard's `γ_g`, the totally-multiplicative extension of `maynardGammaPrime V` via prime
factorization: `γ_g(n) = ∏_{p^k ‖ n} (γ_g(p))^k`.
-/
noncomputable def maynardGamma (V : ℕ) (n : ℕ) : ℝ :=
  n.factorization.prod fun p k ↦ maynardGammaPrime V p ^ k

/-- `maynardGammaPrime V p ≥ 0` for all `V, p`. -/
theorem maynardGammaPrime_nonneg (V p : ℕ) : 0 ≤ maynardGammaPrime V p := by
  unfold maynardGammaPrime
  split_ifs with h
  · rfl
  · rcases lt_or_ge p 2 with hp | hp
    · interval_cases p <;> simp
    · have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity

/-- Maynard's `γ_g` is always nonneg. -/
theorem maynardGamma_nonneg (V n : ℕ) : 0 ≤ maynardGamma V n := by
  unfold maynardGamma
  exact Finset.prod_nonneg fun p _ ↦ pow_nonneg (maynardGammaPrime_nonneg V p) _

/-- `maynardGamma V 1 = 1`. -/
theorem maynardGamma_one (V : ℕ) : maynardGamma V 1 = 1 := by
  simp [maynardGamma]

/-- Total multiplicativity of `maynardGamma V` on positive coprime arguments. -/
theorem maynardGamma_mul_of_ne_zero (V m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    maynardGamma V (m * n) = maynardGamma V m * maynardGamma V n := by
  unfold maynardGamma
  rw [Nat.factorization_mul hm hn,
    Finsupp.prod_add_index' (by intro p; rw [pow_zero]) (by intro p a b; rw [pow_add])]

/-- `maynardGamma V` is coprime-multiplicative (the axiom needed by `SieveDatum`). -/
theorem maynardGamma_mul (V m n : ℕ) (hmn : Nat.Coprime m n) :
    maynardGamma V (m * n) = maynardGamma V m * maynardGamma V n := by
  by_cases hm : m = 0
  · subst hm
    obtain rfl : n = 1 := (Nat.coprime_zero_left n).mp hmn
    simp [maynardGamma_one]
  by_cases hn : n = 0
  · subst hn
    obtain rfl : m = 1 := (Nat.coprime_zero_right m).mp hmn
    simp [maynardGamma_one]
  exact maynardGamma_mul_of_ne_zero V m n hm hn

/-- `maynardGamma V` at a prime `p` equals `maynardGammaPrime V p`. -/
theorem maynardGamma_prime (V : ℕ) (p : ℕ) (hp : p.Prime) :
    maynardGamma V p = maynardGammaPrime V p := by
  unfold maynardGamma
  rw [Nat.Prime.factorization hp, Finsupp.prod_single_index (by rw [pow_zero]), pow_one]

/-- The Maynard density stays below the prime. If `2 ∣ V` then `maynardGamma V p < p` for every
prime `p`: primes dividing `V` are killed outright, and the divisibility hypothesis rules out
`p = 2` among the survivors, leaving `p ≥ 3` where `p / (p - 1) < p`. -/
lemma maynardGamma_prime_lt {V : ℕ} (hV : 2 ∣ V) {p : ℕ} (hp : p.Prime) :
    maynardGamma V p < (p : ℝ) := by
  rw [maynardGamma_prime V p hp]
  unfold maynardGammaPrime
  by_cases hpV : p ∣ V
  · rw [if_pos hpV]
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    linarith
  · rw [if_neg hpV]
    have hp3 : (3 : ℕ) ≤ p := by
      rcases hp.two_le.eq_or_lt with h | h
      · exact absurd (h ▸ hV) hpV
      · omega
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_lt_iff₀ h1]
    nlinarith

/-- The Maynard density is a unit up to `O(1/p)` on the surviving primes: for a prime `p` not
dividing `V`, `|maynardGamma V p - 1| ≤ 2 / p`. -/
lemma abs_maynardGamma_prime_sub_one_le {V p : ℕ} (hp : p.Prime) (hpV : ¬ p ∣ V) :
    |maynardGamma V p - 1| ≤ 2 / (p : ℝ) := by
  rw [maynardGamma_prime V p hp]
  unfold maynardGammaPrime
  rw [if_neg hpV]
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hstep : (p : ℝ) / ((p : ℝ) - 1) - 1 = 1 / ((p : ℝ) - 1) := by
    field_simp; ring
  rw [hstep, abs_of_pos (by positivity), div_le_div_iff₀ h1 hppos]
  nlinarith

open scoped PrimeGaps.sieveModulus in
/-- The level-indexed Maynard density family. At level `M` we use
`maynardGamma (W ⌊M⌋₊)` when `2 ∣ W ⌊M⌋₊`
(the honest W-tricked density); for the small levels where
`2 ∤ W ⌊M⌋₊` we fall back
to the trivial density `n ↦ [n = 1]`, so that `IsGammaDensity` holds unconditionally at every
level.
-/
noncomputable def maynardGammaFamily : ℝ → ℕ → ℝ :=
  fun M n ↦ if 2 ∣ W ⌊M⌋₊ then
      maynardGamma (W ⌊M⌋₊) n
    else if n = 1 then (1 : ℝ) else 0

open scoped PrimeGaps.sieveModulus in
/-- The Maynard family is a W-tricked density family (with empty admissible tuple). -/
theorem maynardGammaFamily_isWTricked : IsWTrickedFamily ∅ maynardGammaFamily where
  density N := by
    have hfloor : ⌊(↑N : ℝ)⌋₊ = N := Nat.floor_natCast N
    by_cases hW : 2 ∣ W N
    · have hfam : maynardGammaFamily (↑N : ℝ) = maynardGamma (W N) := by
        funext n; unfold maynardGammaFamily; rw [hfloor, if_pos hW]
      rw [hfam]
      exact
        { nonneg := fun n ↦ maynardGamma_nonneg (W N) n
          one := maynardGamma_one (W N)
          mul := fun m n hmn ↦ maynardGamma_mul (W N) m n hmn
          lt_prime := fun p hp ↦ maynardGamma_prime_lt hW hp }
    · have hfam : maynardGammaFamily (↑N : ℝ) = fun n ↦ if n = 1 then (1 : ℝ) else 0 := by
        funext n; unfold maynardGammaFamily; rw [hfloor, if_neg hW]
      rw [hfam]
      refine
        { nonneg := fun n ↦ by split_ifs <;> norm_num
          one := by simp
          mul := fun m n _ ↦ ?_
          lt_prime := fun p hp ↦ ?_ }
      · by_cases hmn1 : m * n = 1
        · have hm : m = 1 := Nat.dvd_one.mp ⟨n, hmn1.symm⟩
          have hn : n = 1 := Nat.dvd_one.mp ⟨m, by rw [mul_comm] at hmn1; exact hmn1.symm⟩
          rw [if_pos hmn1, if_pos hm, if_pos hn, mul_one]
        · rw [if_neg hmn1]
          have : m ≠ 1 ∨ n ≠ 1 := by
            by_contra! h
            exact hmn1 (by rw [h.1, h.2, mul_one])
          rcases this with h | h
          · rw [if_neg h, zero_mul]
          · rw [if_neg h, mul_zero]
      · rw [if_neg hp.ne_one]
        exact_mod_cast hp.pos
  kill N p hp hpW := by
    have hfloor : ⌊(↑N : ℝ)⌋₊ = N := Nat.floor_natCast N
    unfold maynardGammaFamily
    rw [hfloor]
    split_ifs with hW hp1
    · rw [maynardGamma_prime (W N) p hp, maynardGammaPrime, if_pos hpW]
    · exact absurd hp1 hp.ne_one
    · rfl
  unit := by
    refine ⟨2, by norm_num, fun N hN hD p hp hpW ↦ ?_⟩
    have hfloor : ⌊(↑N : ℝ)⌋₊ = N := Nat.floor_natCast N
    have hWdvd : 2 ∣ W N := Nat.prime_two.dvd_W_iff_le_D₀.mpr (by exact_mod_cast hD)
    have hfam : maynardGammaFamily (↑N : ℝ) p = maynardGamma (W N) p := by
      unfold maynardGammaFamily; rw [hfloor, if_pos hWdvd]
    rw [hfam]
    exact abs_maynardGamma_prime_sub_one_le hp hpW

/-- The uniform upper Mertens deviation constant `A₂` for the Maynard family. -/
noncomputable def maynardA₂ : ℝ :=
  Classical.choose (upper_bound_A₂ ∅ maynardGammaFamily maynardGammaFamily_isWTricked)

/-- `A₂ > 0`. -/
theorem maynardA₂_pos : 0 < maynardA₂ :=
  (Classical.choose_spec (upper_bound_A₂ ∅ maynardGammaFamily maynardGammaFamily_isWTricked)).1

/-- The upper Mertens bound `Δ (maynardGammaFamily N) w z ≤ A₂`. -/
theorem maynardA₂_bound (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ N)
    (w z : ℝ) (hw : 2 ≤ w) (hwz : w ≤ z) :
    Δ (maynardGammaFamily (↑N : ℝ)) w z ≤ maynardA₂ :=
  (Classical.choose_spec
    (upper_bound_A₂ ∅ maynardGammaFamily maynardGammaFamily_isWTricked)).2 N hN hD w z hw hwz

/-- Existence of a nonnegative lower Mertens deviation parameter `L` at level `N`. -/
theorem maynardL_exists (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ N) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      -L ≤ Δ (maynardGammaFamily (↑N : ℝ)) w z := by
  obtain ⟨_, _, hall⟩ := lower_bound_L ∅ maynardGammaFamily maynardGammaFamily_isWTricked
  obtain ⟨L, hLnn, _, hLb⟩ := hall N hN hD
  exact ⟨L, hLnn, hLb⟩

open scoped PrimeGaps.sieveModulus in
/-- For `N : ℕ` large enough that `2 ∣ W N` (equivalently `2 ≤ ⌊log log log N⌋`), we bundle
`γ := maynardGamma (W N)` (`γ_g` on primes, totally multiplicative), `V := W N`, `A₁ := 1/2` and
`A₃ := 2` into a `SieveDatum`. The hypothesis `2 ∣ W N` is what forces every prime `p ∤ V` to
satisfy `p ≥ 3`, which the `γ_lt` and `γ_density` axioms need at `p = 2`.
-/
@[pg_tag "bg246" "def_maynard_sieve_datum"]
noncomputable def maynardSieveDatum (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ N) :
    SieveDatum where
  γ := maynardGamma (W N)
  A₁ := 1 / 2
  V := W N
  A₃ := 2
  γ_nonneg n := maynardGamma_nonneg (W N) n
  γ_one := maynardGamma_one (W N)
  γ_mul m n hmn := maynardGamma_mul (W N) m n hmn
  γ_lt p hp :=
    maynardGamma_prime_lt (Nat.prime_two.dvd_W_iff_le_D₀.mpr (by exact_mod_cast hD)) hp
  A₁_pos := by norm_num
  A₁_lt_one := by norm_num
  γ_density p hp := by
    have hW : 2 ∣ W N := Nat.prime_two.dvd_W_iff_le_D₀.mpr (by exact_mod_cast hD)
    rw [maynardGamma_prime (W N) p hp]
    unfold maynardGammaPrime
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    by_cases hpW : p ∣ W N
    · rw [if_pos hpW, zero_div]
      norm_num
    · rw [if_neg hpW]
      have hp3 : (3 : ℕ) ≤ p := by
        rcases hp.two_le.eq_or_lt with h | h
        · exact absurd (h ▸ hW) hpW
        · omega
      have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [div_div, div_le_iff₀ (by positivity)]
      nlinarith
  V_pos := W_pos
  V_squarefree := W_squarefree
  A₃_nonneg := by norm_num
  γ_zero_of_dvd p hp hpV := by
    rw [maynardGamma_prime (W N) p hp, maynardGammaPrime]
    exact if_pos hpV
  γ_approx p hp hpV := abs_maynardGamma_prime_sub_one_le hp hpV
  A₂ := maynardA₂
  L := Classical.choose (maynardL_exists N hN hD)
  A₂_pos := maynardA₂_pos
  L_nonneg := (Classical.choose_spec (maynardL_exists N hN hD)).1
  mertens_bound w z hw hwz := by
    have hfloor : ⌊(↑N : ℝ)⌋₊ = N := Nat.floor_natCast N
    have hWdvd : 2 ∣ W N := Nat.prime_two.dvd_W_iff_le_D₀.mpr (by exact_mod_cast hD)
    have hfam : maynardGammaFamily (↑N : ℝ) = maynardGamma (W N) := by
      funext n; unfold maynardGammaFamily; rw [hfloor, if_pos hWdvd]
    rw [← hfam]
    exact ⟨(Classical.choose_spec (maynardL_exists N hN hD)).2 w z hw hwz,
      maynardA₂_bound N hN hD w z hw hwz⟩

open scoped PrimeGaps.sieveModulus in
/-- The `γ` field of `maynardSieveDatum` is `maynardGamma (W N)`. -/
@[simp]
theorem maynardSieveDatum_γ (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ N) :
    (maynardSieveDatum N hN hD).γ = maynardGamma (W N) := rfl

open scoped PrimeGaps.sieveModulus in
/-- The `V` field of `maynardSieveDatum` is `W N`. -/
@[simp]
theorem maynardSieveDatum_V (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ N) :
    (maynardSieveDatum N hN hD).V = W N := rfl

/-- The `A₁` field of `maynardSieveDatum` is `1/2`. -/
@[simp]
theorem maynardSieveDatum_A₁ (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ N) :
    (maynardSieveDatum N hN hD).A₁ = 1 / 2 := rfl

/-- The `A₃` field of `maynardSieveDatum` is `2`. -/
@[simp]
theorem maynardSieveDatum_A₃ (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ N) :
    (maynardSieveDatum N hN hD).A₃ = 2 := rfl

open scoped PrimeGaps.sieveModulus in
/-- Value of `maynardSieveDatum`'s `γ` at a prime `p`: `0` if
`p ∣ W N`, else `p / (p - 1)`. -/
theorem maynardSieveDatum_γ_prime (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ N)
    (p : ℕ) (hp : p.Prime) :
    (maynardSieveDatum N hN hD).γ p =
      if p ∣ W N then 0 else (p : ℝ) / ((p : ℝ) - 1) := by
  rw [maynardSieveDatum_γ, maynardGamma_prime (W N) p hp, maynardGammaPrime]

end PrimeGaps

end
