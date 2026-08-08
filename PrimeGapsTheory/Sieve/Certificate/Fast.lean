/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Certificate.Explicit

/-!
# Fast certificate of `M_k > 4`

This file tabulates the values of `G[·, 2]` and clears the factorial denominators, so that the
witnessing inequality `4 * I_k < k * J_k^0` can be checked by `decide` at a feasible cost.

## Main definitions

* `PrimeGaps.IFast` and `PrimeGaps.JFast`: closed forms for `I_k` and `J_k^0` on the basis
  monomials `(1 - P₁)^b P₂^c`.
* `PrimeGaps.CertificateFast`: a `CertificateExplicit` whose values of `G[·, 2]` are tabulated.
* `PrimeGaps.IFastInt`, `PrimeGaps.JFastInt` and `PrimeGaps.CertificateFastInt`: the same data
  with integer coefficients and all factorial denominators cleared by the single common
  denominator `(k + L + 2 * M)!`.
-/

@[expose] public section

open Finset Nat

namespace PrimeGaps

/-- The closed-form value of `∫_{R_k} (1 - P₁)^b P₂^c`. -/
noncomputable def IFast (k : ℕ) {M : ℕ} (gVal : Fin M → ℕ) (b : ℕ) (c : Fin M) : ℚ :=
  b ! * gVal c / (k + b + 2 * c)!

/-- The closed-form value of `J_k^0 ((1 - P₁)^b₁ P₂^c₁, (1 - P₁)^b₂ P₂^c₂)`. -/
noncomputable def JFast (k : ℕ) {M V : ℕ} (hVM : 2 * V = M + 1) (gVal : Fin M → ℕ)
    (b₁ b₂ : ℕ) (c₁ c₂ : Fin V) : ℚ :=
  (∑ c₁' : Fin (c₁ + 1), ∑ c₂' : Fin (c₂ + 1),
    (c₁.val.choose c₁' * c₂.val.choose c₂' * gamma b₁ b₂ c₁ c₂ c₁' c₂' *
      gVal ⟨c₁' + c₂', by omega⟩)) /
  (k + b₁ + b₂ + 2 * c₁ + 2 * c₂ + 1)!

/-- A `CertificateExplicit k` whose values of `G[·, 2]` are tabulated rather than recomputed, so
that the witnessing inequality can be checked by `decide` at a feasible cost. -/
structure CertificateFast (k : ℕ) : Type where
  /-- The number of basis monomials carrying a coefficient. -/
  N : ℕ
  /-- The length of the tabulations `gkVal` and `gk1Val` of `G[·, 2]`. -/
  M : ℕ
  /-- The strict bound on the exponents of `P₂`, so that `c i + c j < M`. -/
  V : ℕ
  /-- The tabulations are exactly long enough for the exponents that occur. -/
  hVM : 2 * V = M + 1
  /-- The tabulated values of `G[b, 2] k` for `b < M`. -/
  gkVal : Fin M → ℕ
  /-- The tabulation `gkVal` is correct. -/
  hgk (b : Fin M) : maynardGFast b 2 k = gkVal b
  /-- The tabulated values of `G[b, 2] (k - 1)` for `b < M`. -/
  gk1Val : Fin M → ℕ
  /-- The tabulation `gk1Val` is correct. -/
  hgk1 (b : Fin M) : maynardGFast b 2 (k - 1) = gk1Val b
  /-- The exponent of `1 - P₁` in the `i`-th basis monomial. -/
  b : Fin N → ℕ
  /-- The exponent of `P₂` in the `i`-th basis monomial. -/
  c : Fin N → Fin V
  /-- The coefficient of the `i`-th basis monomial. -/
  a : Fin N → ℚ
  /-- The witnessing inequality `4 * I_k < k * J_k^0`, which gives `M_k > 4`. -/
  cert : 4 * ∑ i, ∑ j, a i * a j * IFast k gkVal (b i + b j) ⟨c i + c j, by omega⟩ <
    k * ∑ i, ∑ j, a i * a j * JFast k hVM gk1Val (b i) (b j) (c i) (c j)

/-- Read a `CertificateFast` as a `CertificateExplicit`, unfolding the tabulations of `G[·, 2]`. -/
def CertificateFast.toExplicit {k : ℕ} (ct : CertificateFast k) : CertificateExplicit k where
  N := ct.N
  b := ct.b
  c := (ct.c ·)
  a := ct.a
  cert := by simpa [← ct.hgk, ← ct.hgk1, IFast, IExplicit, JFast, JExplicit, sum_range,
    maynardG_eq_maynardGFast] using ct.cert

/-- The integral form of `gamma`; the quotient of factorials is a binomial coefficient. -/
def gammaInt (bi bj ci cj c₁ c₂ : ℕ) : ℕ :=
  bi ! * bj ! * (2 * ci - 2 * c₁)! * (2 * cj - 2 * c₂)! *
    ((bi + 2 * ci - 2 * c₁ + 1) + (bj + 2 * cj - 2 * c₂ + 1)).choose (bi + 2 * ci - 2 * c₁ + 1)

/-- On the indices occurring in `JFast`, `gammaInt` is the integral value of `gamma`. -/
theorem gammaInt_cast (bi bj ci cj c₁ c₂ : ℕ) (hc₁ : c₁ ≤ ci) (hc₂ : c₂ ≤ cj) :
    (gammaInt bi bj ci cj c₁ c₂ : ℚ) = gamma bi bj ci cj c₁ c₂ := by
  let A := bi + 2 * ci - 2 * c₁ + 1
  let B := bj + 2 * cj - 2 * c₂ + 1
  have hAB : A + B = bi + bj + 2 * ci + 2 * cj - 2 * c₁ - 2 * c₂ + 2 := by grind
  have hchooseQ : ((A + B).choose A : ℚ) * A ! * B ! = (A + B)! := by
    exact_mod_cast Nat.add_sub_cancel_left (n := A) (m := B) ▸
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right A B)
  rw [gammaInt, gamma, ← hAB]
  apply (eq_div_iff (by positivity)).2
  grind

/-- `IFast` with its denominator cleared using the common denominator `(k + L + 2 * M)!`. -/
def IFastInt (k L : ℕ) {M : ℕ} (gVal : Fin M → ℕ) (b : Fin L) (c : Fin M) : ℕ :=
  b.val ! * gVal c * (k + L + 2 * M).descFactorial (L + 2 * M - (b + 2 * c))

/-- Clearing a denominator: `A * t = d * t * (A / d)` whenever `d ≠ 0`. -/
private theorem mul_eq_mul_mul_div {K : Type*} [Field K] {A d t : K} (hd : d ≠ 0) :
    A * t = d * t * (A / d) := by field_simp

/-- Clearing `IFast` multiplies it by the common denominator `(k + L + 2 * M)!`. -/
theorem IFastInt_cast (k L : ℕ) {M : ℕ} (gVal : Fin M → ℕ) (b : Fin L) (c : Fin M) :
    (IFastInt k L gVal b c : ℚ) = (k + L + 2 * M)! * IFast k gVal b c := by
  have hsub : k + L + 2 * M - (L + 2 * M - (b + 2 * c)) = k + b + 2 * c := by omega
  have hfacQ : ((k + b + 2 * c)! : ℚ) *
      ((k + L + 2 * M).descFactorial (L + 2 * M - (b + 2 * c)) : ℚ) = ((k + L + 2 * M)! : ℚ) := by
    rw [← hsub]
    exact_mod_cast Nat.factorial_mul_descFactorial (by omega : L + 2 * M - (b + 2 * c) ≤ _)
  rw [IFastInt, IFast]
  norm_num only [Nat.cast_mul]
  rw [← hfacQ]
  exact mul_eq_mul_mul_div (by positivity)

/-- `JFast` with its denominator cleared using the common denominator
`(k + L + 2 * M)!`. The apparent factorial quotient in `gamma` is integral. -/
def JFastInt (k L : ℕ) {M U V : ℕ} (hVM : 2 * V = M + 1) (gVal : Fin M → ℕ)
    (b₁ b₂ : Fin U) (c₁ c₂ : Fin V) : ℕ :=
  (∑ c₁' : Fin (c₁ + 1), ∑ c₂' : Fin (c₂ + 1),
    (c₁.val.choose c₁' * c₂.val.choose c₂' * gammaInt b₁ b₂ c₁ c₂ c₁' c₂' *
      gVal ⟨c₁' + c₂', by omega⟩)) *
  (k + L + 2 * M).descFactorial (L + 2 * M - (b₁ + b₂ + 2 * c₁ + 2 * c₂ + 1))

/-- Clearing `JFast` multiplies it by the common denominator `(k + L + 2 * M)!`. -/
theorem JFastInt_cast (k L : ℕ) {M U V : ℕ} (hUL : 2 * U = L + 1)
    (hVM : 2 * V = M + 1) (gVal : Fin M → ℕ) (b₁ b₂ : Fin U) (c₁ c₂ : Fin V) :
    (JFastInt k L hVM gVal b₁ b₂ c₁ c₂ : ℚ) =
      (k + L + 2 * M)! * JFast k hVM gVal b₁ b₂ c₁ c₂ := by
  have hsub : k + L + 2 * M - (L + 2 * M - (b₁ + b₂ + 2 * c₁ + 2 * c₂ + 1)) =
      k + b₁ + b₂ + 2 * c₁ + 2 * c₂ + 1 := by omega
  have hfacQ : ((k + b₁ + b₂ + 2 * c₁ + 2 * c₂ + 1)! : ℚ) *
      ((k + L + 2 * M).descFactorial (L + 2 * M - (b₁ + b₂ + 2 * c₁ + 2 * c₂ + 1)) : ℚ) =
        ((k + L + 2 * M)! : ℚ) := by
    rw [← hsub]
    exact_mod_cast Nat.factorial_mul_descFactorial
      (by omega : L + 2 * M - (b₁ + b₂ + 2 * c₁ + 2 * c₂ + 1) ≤ _)
  have hgamma (x : Fin (c₁ + 1)) (y : Fin (c₂ + 1)) :
      (gammaInt b₁ b₂ c₁ c₂ x y : ℚ) = gamma b₁ b₂ c₁ c₂ x y :=
    gammaInt_cast _ _ _ _ _ _ (by omega) (by omega)
  rw [JFastInt, JFast, ← hfacQ]
  norm_num only [Nat.cast_mul, Nat.cast_sum]
  simp_rw [hgamma]
  exact mul_eq_mul_mul_div (by positivity)

/-- A `CertificateFast k` with integer coefficients and all factorial denominators cleared by the
single common denominator `(k + L + 2 * M)!`. -/
structure CertificateFastInt (k : ℕ) : Type where
  /-- The number of basis monomials carrying a coefficient. -/
  N : ℕ
  /-- The strict bound on sums of exponents of `P₂`. -/
  M : ℕ
  /-- The strict bound on the exponents of `P₂`. -/
  V : ℕ
  /-- The `P₂` bounds are exactly related by `2 * V = M + 1`. -/
  hVM : 2 * V = M + 1
  /-- The strict bound on sums of exponents of `1 - P₁`. -/
  L : ℕ
  /-- The strict bound on the exponents of `1 - P₁`. -/
  U : ℕ
  /-- The `1 - P₁` bounds are exactly related by `2 * U = L + 1`. -/
  hUL : 2 * U = L + 1
  /-- The tabulated values of `G[b, 2] k` for `b < M`. -/
  gkVal : Fin M → ℕ
  /-- The tabulation `gkVal` is correct. -/
  hgk (b : Fin M) : maynardGFast b 2 k = gkVal b
  /-- The tabulated values of `G[b, 2] (k - 1)` for `b < M`. -/
  gk1Val : Fin M → ℕ
  /-- The tabulation `gk1Val` is correct. -/
  hgk1 (b : Fin M) : maynardGFast b 2 (k - 1) = gk1Val b
  /-- The exponent of `1 - P₁` in the `i`-th basis monomial. -/
  b : Fin N → Fin U
  /-- The exponent of `P₂` in the `i`-th basis monomial. -/
  c : Fin N → Fin V
  /-- The coefficient of the `i`-th basis monomial. -/
  a : Fin N → ℤ
  /-- The witnessing inequality after clearing the common positive denominator. -/
  cert : 4 * ∑ i, a i * ∑ j, a j *
      IFastInt k L gkVal ⟨b i + b j, by omega⟩ ⟨c i + c j, by omega⟩ <
    k * ∑ i, a i * ∑ j, a j * JFastInt k L hVM gk1Val (b i) (b j) (c i) (c j)

/-- Read a cleared-denominator certificate as a `CertificateFast`. -/
def CertificateFastInt.toFast {k : ℕ} (ct : CertificateFastInt k) : CertificateFast k where
  N := ct.N
  M := ct.M
  V := ct.V
  hVM := ct.hVM
  gkVal := ct.gkVal
  hgk := ct.hgk
  gk1Val := ct.gk1Val
  hgk1 := ct.hgk1
  b := (ct.b ·)
  c := ct.c
  a := (ct.a ·)
  cert := by
    have hfac : (0 : ℚ) < (k + ct.L + 2 * ct.M)! := by positivity
    have hcert : (4 : ℚ) * ∑ i, (ct.a i : ℚ) * ∑ j, (ct.a j : ℚ) *
          (IFastInt k ct.L ct.gkVal ⟨ct.b i + ct.b j, by have := ct.hUL; omega⟩
            ⟨ct.c i + ct.c j, by have := ct.hVM; omega⟩ : ℚ) <
        (k : ℚ) * ∑ i, (ct.a i : ℚ) * ∑ j, (ct.a j : ℚ) *
          (JFastInt k ct.L ct.hVM ct.gk1Val (ct.b i) (ct.b j) (ct.c i) (ct.c j) : ℚ) := by
      exact_mod_cast ct.cert
    apply lt_of_mul_lt_mul_left _ hfac.le
    simpa only [IFastInt_cast, JFastInt_cast k ct.L ct.hUL ct.hVM, Nat.cast_ofNat,
      Int.cast_ofNat, Int.cast_natCast, Nat.cast_mul, Int.cast_mul, mul_sum, mul_assoc,
      mul_left_comm, mul_comm] using hcert

/-- Read a cleared-denominator certificate as a `CertificateExplicit`. -/
def CertificateFastInt.toExplicit {k : ℕ} (ct : CertificateFastInt k) : CertificateExplicit k :=
  ct.toFast.toExplicit

end PrimeGaps
