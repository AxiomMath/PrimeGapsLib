/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import PrimeGapsTheory.Sieve.PermissibleSupport.FunctionW
public import PrimeGapsTheory.Sieve.SieveTruncation

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Sieve data

Defines the density data and associated arithmetic functions used by the sieve.

## Main definitions

* `IsGammaDensity`: The axioms satisfied by a sieve density.
* `SieveDatum`: A sieve density together with its modulus and quantitative constants.
* `gStar`: The multiplicative function determined by the density.
* `bDefect`: The squarefree defect associated with a sieve datum.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius BigOperators PrimeGaps
open ArithmeticFunction

/-- A fixed natural power of the logarithm is little-o of every positive real power of the
identity. This is `Real.isLittleO_log_rpow_rpow_atTop` with the exponent of the logarithm
transported along `Real.rpow_natCast`; it is the common core of the eventual-domination bounds
`eventually_log_pow_le_const_mul` and `eventually_log_pow_le_rpow` below. -/
private theorem isLittleO_log_pow_rpow_atTop (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (fun x : ℝ ↦ (Real.log x) ^ n) =o[Filter.atTop] (fun x : ℝ ↦ x ^ s) := by
  simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (n : ℝ) hs

namespace Real

/-- Any fixed power of the logarithm is eventually dominated by any positive multiple of the
identity: for every exponent `n : ℕ` and every constant `κ > 0` we have `(log x) ^ n ≤ κ * x` for
all sufficiently large real `x`.

This is the linear-domination form of `isLittleO_log_pow_rpow_atTop`; a site needing a
leading constant `C > 0` in `C * (log x) ^ n ≤ κ * x` applies it with `κ / C`. -/
theorem eventually_log_pow_le_const_mul (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ x : ℝ in Filter.atTop, (Real.log x) ^ n ≤ κ * x := by
  filter_upwards [(isLittleO_log_pow_rpow_atTop n one_pos).def hκ,
    Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at hx
  exact le_trans (le_abs_self _) hx

/-- Any fixed power of the logarithm is eventually dominated by any positive real power of the
identity: for every exponent `n : ℕ` and every `s > 0` we have `(log x) ^ n ≤ x ^ s` for all
sufficiently large real `x`.

This is the rpow-domination form of `isLittleO_log_pow_rpow_atTop`; a site indexing over `ℕ`
composes it with `tendsto_natCast_atTop_atTop.eventually`. -/
theorem eventually_log_pow_le_rpow (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in Filter.atTop, (Real.log x) ^ n ≤ x ^ s := by
  filter_upwards [(isLittleO_log_pow_rpow_atTop n hs).def one_pos,
    Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) s), one_mul] at hx
  exact le_trans (le_abs_self _) hx

end Real

namespace PrimeGaps

/-- `∑_{w ≤ p ≤ z} f p * Real.log p / p`, summed over the primes `p` in `[w, z]`. -/
noncomputable def intervalPrimeSum (f : ℕ → ℝ) (w z : ℝ) : ℝ :=
  ∑ p ∈ {p ∈ Finset.range (⌊z⌋₊ + 1) |
      Nat.Prime p ∧ (w : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ z},
    f p * Real.log p / p

/-- The Mertens deviation `Delta(w, z) = sum_{w <= p <= z} f(p)(log p)/p - log(z/w)` (Maynard
Definition 9), for a weight `f`.
-/
noncomputable def Δ (f : ℕ → ℝ) (w z : ℝ) : ℝ := intervalPrimeSum f w z - Real.log (z / w)

/-- `gamma: ℕ → ℝ` is nonnegative, multiplicative with `gamma(1) = 1`,
`gamma(m*n) = gamma(m)*gamma(n)` whenever `m` and `n` are coprime, and `gamma(p) ∈ [0, p)` for
every prime `p`.
-/
structure IsGammaDensity (γ : ℕ → ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ γ n
  one : γ 1 = 1
  mul : ∀ m n, Nat.Coprime m n → γ (m * n) = γ m * γ n
  lt_prime : ∀ p, Nat.Prime p → γ p < (p : ℝ)

/-- An `IsGammaDensity` density `γ` together with a squarefree modulus `V` killing `γ`, and
constants `A₁, A₂, A₃, L` bounding it: `γ p / p ≤ 1 - A₁`, `|γ p - 1| ≤ A₃ / p` for `p ∤ V`, and
`-L ≤ Δ γ w z ≤ A₂` for `2 ≤ w ≤ z`. -/
@[pg_tag "bg246" "def_gamma_hypotheses"]
structure SieveDatum where
  /-- The sieve density function `γ`. -/
  γ : ℕ → ℝ
  /-- The constant `A₁`. -/
  A₁ : ℝ
  /-- The squarefree modulus `V`. -/
  V : ℕ
  /-- The constant `A₃`. -/
  A₃ : ℝ
  γ_nonneg : ∀ n : ℕ, 0 ≤ γ n
  γ_one : γ 1 = 1
  γ_mul : ∀ m n : ℕ, Nat.Coprime m n → γ (m * n) = γ m * γ n
  γ_lt : ∀ p : ℕ, p.Prime → γ p < p
  A₁_pos : 0 < A₁
  A₁_lt_one : A₁ < 1
  γ_density : ∀ p : ℕ, p.Prime → γ p / p ≤ 1 - A₁
  V_pos : 0 < V
  V_squarefree : Squarefree V
  A₃_nonneg : 0 ≤ A₃
  γ_zero_of_dvd : ∀ p : ℕ, p.Prime → p ∣ V → γ p = 0
  γ_approx : ∀ p : ℕ, p.Prime → ¬ p ∣ V → |γ p - 1| ≤ A₃ / p
  /-- The constant `A₂` (upper Mertens deviation). -/
  A₂ : ℝ
  /-- The constant `L` (lower Mertens deviation). -/
  L : ℝ
  A₂_pos : 0 < A₂
  L_nonneg : 0 ≤ L
  mertens_bound : ∀ w z : ℝ, 2 ≤ w → w ≤ z → -L ≤ Δ γ w z ∧ Δ γ w z ≤ A₂

end PrimeGaps

namespace PrimeGaps.SieveDatum

variable (S : SieveDatum)

/-- The totally multiplicative function `g_*: ℕ → ℝ` determined by its values on primes,
`g_*(p) = γ(p) / (p - γ(p))`. A totally multiplicative function is determined on all of `ℕ` by
`g_*(n) = ∏_{p^k ‖ n} g_*(p)^k`, which we realize via the prime factorization of `n`. In particular
`g_*(1) = 1` (empty product) and `g_*(p) = γ(p)/(p - γ(p))` at a prime `p`.
-/
@[pg_tag "bg246" "def_g_star"]
noncomputable def gStar (n : ℕ) : ℝ := n.factorization.prod (fun p k ↦ (S.γ p / (p - S.γ p)) ^ k)

/-- `g_*` at a prime `p` equals `γ(p) / (p - γ(p))`. -/
theorem gStar_prime (p : ℕ) (hp : p.Prime) : S.gStar p = S.γ p / (p - S.γ p) := by
  unfold gStar
  rw [Nat.Prime.factorization hp, Finsupp.prod_single_index (by simp)]
  simp

/-- `g_*` is totally multiplicative: `g_*(m * n) = g_*(m) * g_*(n)` for all `m, n` (with
`m, n ≠ 0`).
-/
theorem gStar_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    S.gStar (m * n) = S.gStar m * S.gStar n := by
  unfold gStar
  rw [Nat.factorization_mul hm hn,
    Finsupp.prod_add_index' (fun a ↦ by simp) (fun a b₁ b₂ ↦ by rw [pow_add])]

/-- On primes dividing `V`, the weight `g_*` vanishes (since `γ` does there, and
`g_*(p) = γ(p)/(p - γ(p))`).
-/
theorem gStar_prime_zero (p : ℕ) (hp : p.Prime) (hpE : p ∣ S.V) : S.gStar p = 0 := by
  rw [S.gStar_prime p hp, S.γ_zero_of_dvd p hp hpE, zero_div]

/-- For squarefree `n`, `g_*(n) = ∏_{p ∣ n} g_*(p)`. Reduces the totally-multiplicative
`Finsupp.prod` to a plain `Finset.prod` over `n.primeFactors`, since each prime `p ∣ n` has
multiplicity `1` in `n`.
-/
theorem gStar_squarefree_eq_prod (n : ℕ) (hn : Squarefree n) :
    S.gStar n = ∏ p ∈ n.primeFactors, S.gStar p := by
  rw [Finset.prod_congr rfl fun p hp ↦ S.gStar_prime p (Nat.prime_of_mem_primeFactors hp)]
  unfold gStar
  rw [Nat.prod_primeFactors_prod_factorization (f := fun p ↦ S.γ p / (p - S.γ p))]
  refine Finsupp.prod_congr fun p hp ↦ ?_
  rw [Nat.support_factorization] at hp
  rw [Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp), pow_one]

/-- At a prime `p`, the weight `g_*` is nonnegative: `g_*(p) = γ(p)/(p - γ(p))` with `0 ≤ γ(p)`
and `γ(p) < p`. -/
theorem gStar_prime_nonneg (p : ℕ) (hp : p.Prime) : 0 ≤ S.gStar p := by
  rw [S.gStar_prime p hp]
  exact div_nonneg (S.γ_nonneg p) (by linarith [S.γ_lt p hp])

/-- `h(d):= μ(d)^2 · g_*(d)`. -/
@[pg_tag "bg246" "def_h_conv"]
noncomputable def h (d : ℕ) : ℝ := ((μ d : ℤ) : ℝ) ^ 2 * S.gStar d

/-- The sieve weight `h` is nonnegative: it vanishes off the squarefree integers, and on them it is
a product of the nonnegative local densities `g_*(p)`. -/
theorem h_nonneg (d : ℕ) : 0 ≤ S.h d := by
  by_cases hsq : Squarefree d
  · refine mul_nonneg (sq_nonneg _) ?_
    rw [S.gStar_squarefree_eq_prod d hsq]
    exact Finset.prod_nonneg fun p hp ↦ S.gStar_prime_nonneg p (Nat.prime_of_mem_primeFactors hp)
  · simp [h, moebius_eq_zero_of_not_squarefree hsq]

/-- `H(z):= ∑_{0 < d < z} h(d)`, taken over positive integers `d` strictly below `z`. The index set
is finite; we realize it as the `d ∈ Finset.range ⌈z⌉₊` satisfying `0 < d ∧ (d: ℝ) < z`.
-/
@[pg_tag "bg246" "def_H_z"]
noncomputable def H (z : ℝ) : ℝ :=
  ∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z), S.h d

/-- If `gcd(d, V) > 1`, then `h(d) = 0`. (A prime divides both `d` and `V`, so `g_*` vanishes at
that prime, and total multiplicativity of `g_*` kills `h(d)`.)
-/
theorem h_eq_zero_of_gcd_gt_one (d : ℕ) (hd : 1 < Nat.gcd d S.V) : S.h d = 0 := by
  obtain ⟨p, hp, hpg⟩ := (Nat.gcd d S.V).exists_prime_and_dvd (Nat.ne_of_gt hd)
  have hpd : p ∣ d := hpg.trans (Nat.gcd_dvd_left d S.V)
  have hpE : p ∣ S.V := hpg.trans (Nat.gcd_dvd_right d S.V)
  obtain ⟨k, rfl⟩ := hpd
  by_cases hk : k = 0
  · simp [h, hk]
  · unfold h
    rw [S.gStar_mul p k hp.ne_zero hk, S.gStar_prime_zero p hp hpE, zero_mul, mul_zero]

/-- The defect function `b: ℕ → ℝ`. Multiplicative, supported on squarefree integers coprime to
`V`, with `b(p) = g_*(p) - 1/(p-1)` for `p ∤ V`. Concretely: `b(n) = 0` unless `n` is squarefree
and coprime to `V`, in which case `b(n) = ∏_{p ∣ n} (g_*(p) - 1/(p-1))`.
-/
@[pg_tag "bg246" "def_b_defect"]
noncomputable def bDefect (n : ℕ) : ℝ :=
  if Squarefree n ∧ Nat.Coprime n S.V then
    n.primeFactors.prod (fun p ↦ S.gStar p - 1 / (p - 1))
  else 0

/-- `b` at a prime `p ∤ V` equals `g_*(p) - 1/(p-1) = γ(p)/(p - γ(p)) - 1/(p-1)`. -/
theorem bDefect_prime (p : ℕ) (hp : p.Prime) (hpE : ¬ p ∣ S.V) :
    S.bDefect p = S.γ p / (p - S.γ p) - 1 / (p - 1) := by
  unfold bDefect
  rw [if_pos]
  · rw [hp.primeFactors, Finset.prod_singleton, S.gStar_prime p hp]
  · exact ⟨hp.squarefree, (hp.coprime_iff_not_dvd).mpr hpE⟩

/-- `b` is multiplicative on coprime inputs: `b(m * n) = b(m) * b(n)` when `(m,n) = 1`. -/
theorem bDefect_mul (m n : ℕ) (hmn : Nat.Coprime m n) :
    S.bDefect (m * n) = S.bDefect m * S.bDefect n := by
  unfold bDefect
  by_cases hsf : Squarefree (m * n) ∧ Nat.Coprime (m * n) S.V
  · obtain ⟨hsfmn, hcopmn⟩ := hsf
    have hsfm : Squarefree m := ((Nat.squarefree_mul hmn).mp hsfmn).1
    have hsfn : Squarefree n := ((Nat.squarefree_mul hmn).mp hsfmn).2
    have hcopm : Nat.Coprime m S.V := Nat.Coprime.coprime_dvd_left (Dvd.intro n rfl) hcopmn
    have hcopn : Nat.Coprime n S.V := Nat.Coprime.coprime_dvd_left (Dvd.intro_left m rfl) hcopmn
    rw [if_pos ⟨hsfmn, hcopmn⟩, if_pos ⟨hsfm, hcopm⟩, if_pos ⟨hsfn, hcopn⟩,
      hmn.primeFactors_mul, Finset.prod_union hmn.disjoint_primeFactors]
  · rw [if_neg hsf]
    have : ¬ (Squarefree m ∧ Nat.Coprime m S.V) ∨ ¬ (Squarefree n ∧ Nat.Coprime n S.V) := by
      by_contra! hcon
      exact hsf ⟨(Nat.squarefree_mul hmn).mpr ⟨hcon.1.1, hcon.2.1⟩,
        Nat.Coprime.mul_left hcon.1.2 hcon.2.2⟩
    rcases this with h | h <;> rw [if_neg h] <;> ring

/-- `b` vanishes off integers coprime to `V`. -/
theorem bDefect_eq_zero_of_not_coprime (n : ℕ) (h : ¬ Nat.Coprime n S.V) : S.bDefect n = 0 := by
  unfold bDefect
  exact if_neg fun hx ↦ h hx.2

/-- `b` vanishes off squarefree integers. -/
theorem bDefect_eq_zero_of_not_squarefree (n : ℕ) (h : ¬ Squarefree n) : S.bDefect n = 0 := by
  unfold bDefect
  exact if_neg fun hx ↦ h hx.1

/-- Combined-fraction form of `b(p)`. -/
theorem bDefect_prime_eq (p : ℕ) (hp : p.Prime) (hpE : ¬ p ∣ S.V) :
    S.bDefect p = (p * (S.γ p - 1)) / ((p - S.γ p) * (p - 1)) := by
  rw [S.bDefect_prime p hp hpE]
  have hγlt : S.γ p < p := S.γ_lt p hp
  have h1 : (0 : ℝ) < (p : ℝ) - S.γ p := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  field_simp
  ring

/-- Every `SieveDatum` 's density `γ` satisfies the abstract `IsGammaDensity` (Definition 6): the
four `IsGammaDensity` fields are exactly `SieveDatum` 's first four axioms. This projection is what
lets the family-level `IsWTrickedFamily` and the per-instance `SieveDatum` share one Definition-6
notion instead of duplicating it.
-/
theorem toIsGammaDensity (S : SieveDatum) : IsGammaDensity S.γ :=
  ⟨S.γ_nonneg, S.γ_one, S.γ_mul, S.γ_lt⟩

end PrimeGaps.SieveDatum

end
