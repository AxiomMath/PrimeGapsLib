/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.RingTheory.Radical.NatInt
public import PrimeGapsTheory.ArithmeticFunction.LYTransform.Basic
public import PrimeGapsTheory.Arithmetic.ConvergentSums

import PrimeGapsTheory.ForMathlib.NumberTheory.ArithmeticFunction.Moebius
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Substitution into the distinguished transform

Establishes the coordinatewise Möbius identities used to substitute the primary transform into
the distinguished transform.

## Main results

* `lem_ym_substitute_y`: Gives the substitution formula for the distinguished transform.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.detotient

namespace PrimeGaps
open ArithmeticFunction UniqueFactorizationMonoid

namespace MaynardSubstitute

variable {k : ℕ} (lam : (Fin k → ℕ) →₀ ℝ) (m : Fin k)

/-- Reindexing a divisor sum over multiples of `d`:
`∑ a ∈ e.divisors, [d ∣ a] f a = ∑ b ∈ (e / d).divisors, f (d * b)` for `d ∣ e`. -/
theorem reindex_div (d e : ℕ) (hd : d ∣ e) (he : 0 < e) (f : ℕ → ℝ) :
    (∑ a ∈ e.divisors, if d ∣ a then f a else 0) = ∑ b ∈ (e / d).divisors, f (d * b) := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)
  have hedpos : 0 < e / d := Nat.div_pos (Nat.le_of_dvd he hd) hdpos
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun a ↦ a / d) (fun b ↦ d * b)
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨hae, hda⟩ := ha
    rw [Nat.mem_divisors] at hae ⊢
    exact ⟨Nat.div_dvd_div hda hae.1, hedpos.ne'⟩
  · intro b hb
    rw [Nat.mem_divisors] at hb
    rw [Finset.mem_filter, Nat.mem_divisors]
    obtain ⟨k, hk⟩ := hb.1
    have hedb : e = d * b * k := by
      have h2 : e = d * (e / d) := (Nat.mul_div_cancel' hd).symm
      rw [h2, hk]; ring
    exact ⟨⟨⟨k, hedb⟩, he.ne'⟩, Dvd.intro b rfl⟩
  · intro a ha
    rw [Finset.mem_filter] at ha
    exact Nat.mul_div_cancel' ha.2
  · intro b hb
    exact Nat.mul_div_cancel_left b hdpos
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Nat.mul_div_cancel' ha.2]

/-- The divisor sum of a multiplicative `f` splits over coprime `a`, `b`:
`∑ c ∈ (a * b).divisors, f c = (∑ c ∈ a.divisors, f c) * (∑ c ∈ b.divisors, f c)`. -/
theorem mult_divisor_sum (a b : ℕ) (h : Nat.Coprime a b)
    (f : ℕ → ℝ) (hf : ∀ x y, Nat.Coprime x y → f (x * y) = f x * f y) :
    (∑ c ∈ (a * b).divisors, f c) = (∑ c ∈ a.divisors, f c) * (∑ c ∈ b.divisors, f c) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  rcases eq_or_ne a 0 with ha | ha
  · subst ha; simp only [Nat.Coprime, Nat.gcd_zero_left] at h; subst h; simp
  rcases eq_or_ne b 0 with hb | hb
  · subst hb; simp only [Nat.Coprime, Nat.gcd_zero_right] at h; subst h; simp
  apply Finset.sum_nbij' (i := fun c ↦ (Nat.gcd c a, Nat.gcd c b)) (j := fun p ↦ p.1 * p.2)
  · intro c hc
    rw [Nat.mem_divisors] at hc
    simp only [Finset.mem_product, Nat.mem_divisors]
    exact ⟨⟨Nat.gcd_dvd_right c a, ha⟩, ⟨Nat.gcd_dvd_right c b, hb⟩⟩
  · intro p hp
    simp only [Finset.mem_product, Nat.mem_divisors] at hp
    rw [Nat.mem_divisors]
    exact ⟨mul_dvd_mul hp.1.1 hp.2.1, mul_ne_zero ha hb⟩
  · intro c hc
    rw [Nat.mem_divisors] at hc
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hc.1
  · intro p hp
    simp only [Finset.mem_product, Nat.mem_divisors] at hp
    obtain ⟨⟨hp1, _⟩, ⟨hp2, _⟩⟩ := hp
    have hca : Nat.gcd (p.1 * p.2) a = p.1 := by
      have hco : Nat.Coprime p.2 a := (Nat.coprime_comm.mp h).coprime_dvd_left hp2
      rw [Nat.gcd_comm, Nat.Coprime.gcd_mul_right_cancel_right]
      · exact Nat.gcd_eq_right hp1
      · exact hco
    have hcb : Nat.gcd (p.1 * p.2) b = p.2 := by
      have hco : Nat.Coprime p.1 b := h.coprime_dvd_left hp1
      rw [mul_comm, Nat.gcd_comm, Nat.Coprime.gcd_mul_right_cancel_right]
      · exact Nat.gcd_eq_right hp2
      · exact hco
    ext
    · exact hca
    · exact hcb
  · intro c hc
    rw [Nat.mem_divisors] at hc
    simp only
    rw [← hf _ _ (Nat.Coprime.gcd_both c c h)]
    rw [(Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hc.1]

/-- Prime-power case: `∑ b ∈ (p ^ n).divisors, [Coprime b d] μ b = 1` if `p ∣ d`, else `0`. -/
theorem coprime_moebius_pp (d p n : ℕ) (hp : p.Prime) (hn : 0 < n) :
    (∑ b ∈ (p ^ n).divisors, if Nat.Coprime b d then (μ b : ℝ) else 0) =
      if p ∣ d then 1 else 0 := by
  by_cases hpd : p ∣ d
  · rw [if_pos hpd, Nat.divisors_prime_pow hp, Finset.sum_map]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj hj0
      simp only [Function.Embedding.coeFn_mk]
      have hco : ¬ Nat.Coprime (p ^ j) d := by
        intro hc
        have hppd : Nat.Coprime p d := Nat.Coprime.coprime_dvd_left (dvd_pow_self p hj0) hc
        exact (Nat.Prime.coprime_iff_not_dvd hp).mp hppd hpd
      rw [if_neg hco]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg hpd]
    have hcong : ∀ b ∈ (p ^ n).divisors,
        (if Nat.Coprime b d then (μ b : ℝ) else 0) =
        (μ b : ℝ) := by
      intro b hb
      have hbdvd : b ∣ p ^ n := (Nat.mem_divisors.mp hb).1
      have hco : Nat.Coprime b d := by
        apply Nat.Coprime.coprime_dvd_left hbdvd
        exact (Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd))
      rw [if_pos hco]
    rw [Finset.sum_congr rfl hcong]
    have hcast : (∑ b ∈ (p ^ n).divisors, (μ b : ℝ)) =
        ((∑ b ∈ (p ^ n).divisors, (μ b : ℤ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [hcast, ArithmeticFunction.sum_divisors_moebius,
      if_neg (Nat.one_lt_pow hn.ne' hp.one_lt).ne']
    simp

/-- The summand `b ↦ [Coprime b d] μ b` is multiplicative on coprime arguments. -/
theorem coprime_moebius_mult (d : ℕ) : ∀ x y, Nat.Coprime x y →
    (if Nat.Coprime (x * y) d then (μ (x * y) : ℝ) else 0) =
    (if Nat.Coprime x d then (μ x : ℝ) else 0) *
      (if Nat.Coprime y d then (μ y : ℝ) else 0) := by
  intro x y hxy
  by_cases hx : Nat.Coprime x d
  · by_cases hy : Nat.Coprime y d
    · have hxyd : Nat.Coprime (x * y) d := Nat.Coprime.mul_left hx hy
      rw [if_pos hxyd, if_pos hx, if_pos hy]
      have := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hxy
      push_cast [this]; ring
    · rw [if_neg hy, mul_zero, if_neg]
      intro hc; exact hy (Nat.Coprime.coprime_dvd_left (Dvd.intro_left x rfl) hc)
  · rw [if_neg hx, zero_mul, if_neg]
    intro hc; exact hx (Nat.Coprime.coprime_dvd_left (Dvd.intro y rfl) hc)

/-- `∑ b ∈ m.divisors, [Coprime b d] μ b = 1` if `radical m ∣ d`, else `0`, for `0 < m`. -/
theorem coprime_moebius_sum (d m : ℕ) (hm : 0 < m) :
    (∑ b ∈ m.divisors, if Nat.Coprime b d then (μ b : ℝ) else 0) =
      if radical m ∣ d then 1 else 0 := by
  revert hm
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro _
    rw [coprime_moebius_pp d p n hp hn]
    congr 1
    rw [show radical (p ^ n) = p by
      rw [Nat.radical_eq_prod_primeFactors, Nat.primeFactors_prime_pow hn.ne' hp]
      simp]
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _
    rw [show radical 1 = 1 by simp]
    simp [Nat.divisors_one]
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [mult_divisor_sum a b hab _ (coprime_moebius_mult d), iha (by omega), ihb (by omega)]
    rw [radical_mul (Nat.coprime_iff_isRelPrime.mp hab)]
    have hradadvd : radical a ∣ a := radical_dvd_self
    have hradbdvd : radical b ∣ b := radical_dvd_self
    have hcop : Nat.Coprime (radical a) (radical b) :=
      (hab.coprime_dvd_right radical_dvd_self).coprime_dvd_left radical_dvd_self
    by_cases hda : radical a ∣ d <;> by_cases hdb : radical b ∣ d
    · rw [if_pos hda, if_pos hdb, if_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hda hdb), mul_one]
    · rw [if_pos hda, if_neg hdb, mul_zero, if_neg]
      intro hc; exact hdb ((Dvd.intro_left (radical a) rfl).trans hc)
    · rw [if_neg hda, if_pos hdb, zero_mul, if_neg]
      intro hc; exact hda ((Dvd.intro (radical b) rfl).trans hc)
    · rw [if_neg hda, zero_mul, if_neg]
      intro hc; exact hda ((Dvd.intro (radical b) rfl).trans hc)

/-- `μ (d * b) = μ d * [Coprime b d] μ b`, both sides vanishing when `d * b` is not squarefree. -/
theorem moebius_mul_squarefree (d : ℕ) (b : ℕ) :
    (μ (d * b) : ℝ) = (μ d : ℝ) *
        (if Nat.Coprime b d then (μ b : ℝ) else 0) := by
  by_cases hcop : Nat.Coprime b d
  · rw [if_pos hcop]
    push_cast [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (Nat.coprime_comm.mp hcop)]
    ring
  · rw [if_neg hcop, mul_zero]
    have hnsf : ¬ Squarefree (d * b) := by
      obtain ⟨p, hp, hpbd⟩ := Nat.exists_prime_and_dvd (hcop : Nat.gcd b d ≠ 1)
      intro hsf
      have := hsf p (mul_dvd_mul (hpbd.trans (Nat.gcd_dvd_right b d))
        (hpbd.trans (Nat.gcd_dvd_left b d)))
      rw [Nat.isUnit_iff] at this; exact hp.ne_one this
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]; simp

/-- The inner Möbius sum over multiples of `d`, for `d ∣ e` and `0 < e`:
`∑ a ∈ e.divisors, [d ∣ a] μ a = μ d * [radical (e / d) ∣ d]`. -/
theorem inner_sum_eq (d e : ℕ) (hd : d ∣ e) (he : 0 < e) :
    (∑ a ∈ e.divisors, if d ∣ a then (μ a : ℝ) else 0) =
      (μ d : ℝ) * (if radical (e / d) ∣ d then 1 else 0) := by
  rw [reindex_div d e hd he (fun a ↦ (μ a : ℝ))]
  by_cases hsf : Squarefree d
  · rw [Finset.sum_congr rfl (fun b _ ↦ moebius_mul_squarefree d b), ← Finset.mul_sum,
      coprime_moebius_sum d (e / d) (Nat.div_pos (Nat.le_of_dvd he hd) hsf.ne_zero.bot_lt)]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
    simp only [Int.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro b _
    have hnsf : ¬ Squarefree (d * b) := fun h ↦ hsf (h.squarefree_of_dvd (Dvd.intro b rfl))
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]; simp

/-- For `d ∣ e` with `0 < e`: `d` is squarefree with `radical (e / d) ∣ d` iff `d = radical e`. -/
theorem squarefree_and_radical_div_dvd_iff_eq_radical (d e : ℕ) (hd : d ∣ e) (he : 0 < e) :
    (Squarefree d ∧ radical (e / d) ∣ d) ↔ d = radical e := by
  have radfact : ∀ (m p : ℕ), (radical m).factorization p =
      if p ∈ m.primeFactors then 1 else 0 := by
    intro m p
    rw [Nat.radical_eq_prod_primeFactors,
      Nat.factorization_prod (fun x hx ↦ (Nat.prime_of_mem_primeFactors hx).ne_zero)]
    rw [Finsupp.finsetSum_apply]
    by_cases hp : p ∈ m.primeFactors
    · rw [if_pos hp, Finset.sum_eq_single p]
      · exact (Nat.prime_of_mem_primeFactors hp).factorization_self
      · intro b hb hbp
        rw [(Nat.prime_of_mem_primeFactors hb).factorization]; simp [hbp]
      · intro h; exact absurd hp h
    · rw [if_neg hp, Finset.sum_eq_zero]
      intro b hb
      rw [(Nat.prime_of_mem_primeFactors hb).factorization]
      have : b ≠ p := fun h ↦ hp (h ▸ hb)
      simp [this]
  have radSqfree : ∀ m : ℕ, Squarefree (radical m) := fun _ ↦ squarefree_radical
  have radNeZero : ∀ m : ℕ, radical m ≠ 0 := fun _ ↦ radical_ne_zero
  constructor
  · rintro ⟨hsf, hrad⟩
    apply Nat.eq_of_factorization_eq hsf.ne_zero (radNeZero e)
    intro p
    rw [radfact]
    by_cases hp : p ∈ e.primeFactors
    · rw [if_pos hp]
      have hple1 : d.factorization p ≤ 1 := by
        rw [Nat.squarefree_iff_factorization_le_one hsf.ne_zero] at hsf
        exact hsf p
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpe : p ∣ e := (Nat.mem_primeFactors.mp hp).2.1
      have hpd : p ∣ d := by
        by_contra hpd
        have hediv : e = d * (e / d) := (Nat.mul_div_cancel' hd).symm
        rw [hediv] at hpe
        rcases (hpprime.dvd_mul.mp hpe) with h | h
        · exact hpd h
        · have hedpos : 0 < e / d := Nat.div_pos (Nat.le_of_dvd he hd) hsf.ne_zero.bot_lt
          have hpdvdrad : p ∣ radical (e / d) := by
            rw [Nat.radical_eq_prod_primeFactors]
            exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hpprime, h, hedpos.ne'⟩)
          exact hpd (hpdvdrad.trans hrad)
      have hge1 : 1 ≤ d.factorization p := hpprime.factorization_pos_of_dvd hsf.ne_zero hpd
      omega
    · rw [if_neg hp]
      have hle : d.factorization p ≤ e.factorization p :=
        (Nat.factorization_le_iff_dvd hsf.ne_zero he.ne').mpr hd p
      have hef : e.factorization p = 0 := by
        rw [← Nat.support_factorization] at hp
        exact Finsupp.notMem_support_iff.mp hp
      omega
  · rintro rfl
    refine ⟨radSqfree e, ?_⟩
    rw [← Nat.factorization_le_iff_dvd (radNeZero _) (radNeZero e)]
    intro p
    rw [radfact, radfact]
    by_cases hp : p ∈ (e / radical e).primeFactors
    · rw [if_pos hp]
      have hsub := Nat.mem_primeFactors.mp hp
      rw [if_pos (Nat.mem_primeFactors.mpr ⟨hsub.1,
        hsub.2.1.trans (Nat.div_dvd_of_dvd radical_dvd_self), he.ne'⟩)]
    · rw [if_neg hp]; split <;> simp

/-- The ratio `n / φ n` depends only on the radical: `radical e / φ (radical e) = e / φ e`. -/
theorem totient_ratio_rad (e : ℕ) (he : 0 < e) :
    ((radical e : ℕ) : ℝ) / (Nat.totient (radical e) : ℝ) =
      (e : ℝ) / (Nat.totient e : ℝ) := by
  have hrad_pos : 0 < radical e := Nat.radical_pos e
  have hpf := Nat.primeFactors_radical e
  have key : radical e * Nat.totient e = e * Nat.totient (radical e) := by
    have h1 := Nat.totient_mul_prod_primeFactors e
    have h2 := Nat.totient_mul_prod_primeFactors (radical e)
    rw [hpf] at h2
    set P := ∏ p ∈ e.primeFactors, p with hP
    set Q := ∏ p ∈ e.primeFactors, (p - 1) with hQ
    have hPne : P ≠ 0 := by rw [hP, ← Nat.radical_eq_prod_primeFactors]; exact radical_ne_zero
    have hstep : (e * Nat.totient (radical e)) * P = (radical e * Nat.totient e) * P :=
      calc (e * Nat.totient (radical e)) * P = e * (Nat.totient (radical e) * P) := by ring
        _ = e * (radical e * Q) := by rw [h2]
        _ = radical e * (e * Q) := by ring
        _ = radical e * (Nat.totient e * P) := by rw [h1]
        _ = (radical e * Nat.totient e) * P := by ring
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hPne) hstep).symm
  rw [div_eq_div_iff (by positivity) (by positivity)]
  exact_mod_cast key

/-- The one-coordinate kernel sum for squarefree `r` and `0 < e`, in which only `d = radical e`
survives: `∑ d ∈ e.divisors, [r ∣ d] (μ d * d / φ d) * ∑ a ∈ e.divisors, [d ∣ a] μ a` equals
`e / φ e` if `r ∣ e`, else `0`. -/
theorem kernel_sum_squarefree (r e : ℕ) (hr : Squarefree r) (he : 0 < e) :
    ∑ d ∈ e.divisors, (if r ∣ d then
        ((μ d : ℝ) * (d : ℝ) / (Nat.totient d : ℝ)) *
          (∑ a ∈ e.divisors, if d ∣ a then (μ a : ℝ) else 0)
      else 0) = if r ∣ e then (e : ℝ) / (Nat.totient e : ℝ) else 0 := by
  classical
  have hstep : ∀ d ∈ e.divisors, (if r ∣ d then
        ((μ d : ℝ) * (d : ℝ) / (Nat.totient d : ℝ)) *
          (∑ a ∈ e.divisors, if d ∣ a then (μ a : ℝ) else 0)
      else 0) = (if (r ∣ d ∧ Squarefree d ∧ radical (e / d) ∣ d) then (d : ℝ) / (Nat.totient d : ℝ)
          else 0) := by
    intro d hd
    have hdvd : d ∣ e := (Nat.mem_divisors.mp hd).1
    rw [inner_sum_eq d e hdvd he]
    by_cases hrd : r ∣ d
    · rw [if_pos hrd]
      by_cases hsq : Squarefree d
      · by_cases hradd : radical (e / d) ∣ d
        · rw [if_pos hradd, if_pos ⟨hrd, hsq, hradd⟩, mul_one]
          have hμ2 : (μ d : ℝ) * (μ d : ℝ) =
              1 := by
            rw [← pow_two]; exact_mod_cast moebius_sq_eq_one_of_squarefree hsq
          rw [div_mul_eq_mul_div, mul_comm ((μ d : ℝ) * (d : ℝ))
                (μ d : ℝ), ← mul_assoc, hμ2, one_mul]
        · rw [if_neg hradd, mul_zero, mul_zero, if_neg (by tauto)]
      · have hμ0 : (μ d : ℝ) = 0 := by
          simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        rw [hμ0, if_neg (show ¬(r ∣ d ∧ Squarefree d ∧ radical (e / d) ∣ d) by tauto)]
        simp
    · rw [if_neg hrd, if_neg (by tauto)]
  rw [Finset.sum_congr rfl hstep]
  have hcond : ∀ d ∈ e.divisors,
      (if (r ∣ d ∧ Squarefree d ∧ radical (e / d) ∣ d) then (d : ℝ) / (Nat.totient d : ℝ) else 0) =
      (if (r ∣ d ∧ d = radical e) then (d : ℝ) / (Nat.totient d : ℝ) else 0) := by
    intro d hd
    have hdvd : d ∣ e := (Nat.mem_divisors.mp hd).1
    have hiff : (r ∣ d ∧ Squarefree d ∧ radical (e / d) ∣ d) ↔ (r ∣ d ∧ d = radical e) := by
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, (squarefree_and_radical_div_dvd_iff_eq_radical d e hdvd he).mp ⟨h2, h3⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (squarefree_and_radical_div_dvd_iff_eq_radical d e hdvd he).mpr h2⟩
    simp only [hiff]
  rw [Finset.sum_congr rfl hcond]
  rw [← Finset.sum_filter]
  by_cases hre : r ∣ e
  · rw [if_pos hre]
    have hrre : r ∣ radical e := (dvd_radical_iff hr.isRadical he.ne').mpr hre
    have hfilter : e.divisors.filter (fun d ↦ r ∣ d ∧ d = radical e) = {radical e} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, _, hde⟩; exact hde
      · rintro rfl
        exact ⟨Nat.mem_divisors.mpr ⟨radical_dvd_self, he.ne'⟩, hrre, rfl⟩
    rw [hfilter, Finset.sum_singleton, totient_ratio_rad e he]
  · rw [if_neg hre]
    have hrre : ¬ r ∣ radical e := fun h ↦ hre ((dvd_radical_iff hr.isRadical he.ne').mp h)
    have hfilter : e.divisors.filter (fun d ↦ r ∣ d ∧ d = radical e) = ∅ := by
      ext d
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨_, hrd, rfl⟩; exact hrre hrd
    rw [hfilter, Finset.sum_empty]
section InnerHelpers

/-- Two `finsum`s agree when their nonvanishing parts match and the summands agree there. -/
theorem finsum_bridge {α M : Type*} [AddCommMonoid M] (s1 s2 : Set α) (P Q : α → M)
    (hset : ∀ a, (a ∈ s1 ∧ P a ≠ 0) ↔ (a ∈ s2 ∧ Q a ≠ 0))
    (hval : ∀ a, a ∈ s1 → P a ≠ 0 → P a = Q a) :
    (∑ᶠ a ∈ s1, P a) = ∑ᶠ a ∈ s2, Q a := by
  rw [← finsum_mem_inter_support P s1, ← finsum_mem_inter_support Q s2]
  apply finsum_mem_congr
  · ext a; simp only [Set.mem_inter_iff, Function.mem_support]; exact hset a
  · intro a ha
    simp only [Set.mem_inter_iff, Function.mem_support] at ha
    have h1 := (hset a).2 ha
    exact hval a h1.1 h1.2

/-- A `finsum` of a product over a box factors:
`∑ᶠ x ∈ {x | ∀ i, x i ∈ s i}, ∏ i, h i (x i) = ∏ i, ∑ j ∈ s i, h i j`. -/
theorem pi_finsum_factor (s : Fin k → Finset ℕ) (h : Fin k → ℕ → ℝ) :
    (∑ᶠ x ∈ {x : Fin k → ℕ | ∀ i, x i ∈ s i}, ∏ i, h i (x i)) = ∏ i, ∑ j ∈ s i, h i j := by
  rw [show {x : Fin k → ℕ | ∀ i, x i ∈ s i} = (↑(Fintype.piFinset s) : Set (Fin k → ℕ)) by
        ext x; simp]
  rw [finsum_mem_coe_finset, Finset.prod_univ_sum]

/-- The inner sum over multiples `a` of `d` restricted to `a i ∣ e i` factors coordinatewise into
`∏ i, ∑ aa ∈ (e i).divisors, [d i ∣ aa] μ aa`. -/
theorem inner_a_sum (e d : Fin k → ℕ) (he : ∀ i, 0 < e i) :
    (∑ᶠ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)},
        (∏ i, (μ (a i) : ℝ)) *
          (if (∀ i, a i ∣ e i) then (1 : ℝ) else 0)) = ∏ i, ∑ aa ∈ (e i).divisors,
          (if d i ∣ aa then (μ aa : ℝ) else 0) := by
  classical
  rw [← pi_finsum_factor (fun i ↦ (e i).divisors)
        (fun i x ↦ if d i ∣ x then (μ x : ℝ) else 0)]
  apply finsum_bridge
  · intro a
    constructor
    · rintro ⟨⟨hpos, hdvd⟩, hne⟩
      have hdvde : ∀ i, a i ∣ e i := by
        by_contra h
        rw [if_neg h, mul_zero] at hne; exact hne rfl
      constructor
      · intro i; simp only [Nat.mem_divisors, ne_eq]; exact ⟨hdvde i, (he i).ne'⟩
      · rw [if_pos hdvde, mul_one] at hne
        intro hcon
        apply hne
        rw [Finset.prod_eq_zero_iff] at hcon ⊢
        obtain ⟨i, _, hi⟩ := hcon
        rw [if_pos (hdvd i)] at hi
        exact ⟨i, Finset.mem_univ i, hi⟩
    · rintro ⟨hmem, hne⟩
      have hdvd : ∀ i, d i ∣ a i := by
        intro i
        by_contra h
        apply hne
        rw [Finset.prod_eq_zero_iff]
        exact ⟨i, Finset.mem_univ i, by rw [if_neg h]⟩
      have hdvde : ∀ i, a i ∣ e i := fun i ↦ (Nat.mem_divisors.mp (hmem i)).1
      have hpos : ∀ i, 0 < a i := fun i ↦ Nat.pos_of_mem_divisors (hmem i)
      refine ⟨⟨hpos, hdvd⟩, ?_⟩
      rw [if_pos hdvde, mul_one]
      intro hcon
      apply hne
      rw [Finset.prod_eq_zero_iff] at hcon ⊢
      obtain ⟨i, _, hi⟩ := hcon
      exact ⟨i, Finset.mem_univ i, by rw [if_pos (hdvd i)]; exact hi⟩
  · intro a ha hne
    obtain ⟨hpos, hdvd⟩ := ha
    have hdvde : ∀ i, a i ∣ e i := by
      by_contra h
      rw [if_neg h, mul_zero] at hne; exact hne rfl
    rw [if_pos hdvde, mul_one]
    apply Finset.prod_congr rfl
    intro i _
    rw [if_pos (hdvd i)]

/-- The outer sum over `d` factors coordinatewise, the distinguished coordinate ranging over `{1}`
and each other over the divisors of `e i` divisible by `r i`. -/
theorem outer_d_sum (m : Fin k) (r e : Fin k → ℕ) (he : ∀ i, 0 < e i) (hrm : r m = 1) :
    (∑ᶠ d ∈ {d : Fin k → ℕ | (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ d m = 1},
        (∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
          (∏ i, ∑ aa ∈ (e i).divisors,
            (if d i ∣ aa then (μ aa : ℝ) else 0))) =
      ∏ i, ∑ dd ∈ (if i = m then ({1} : Finset ℕ) else (e i).divisors.filter (r i ∣ ·)),
          ((μ dd : ℝ) * (dd : ℝ) / (Nat.totient dd : ℝ)) *
            (∑ aa ∈ (e i).divisors,
              (if dd ∣ aa then (μ aa : ℝ) else 0)) := by
  classical
  set s : Fin k → Finset ℕ :=
    fun i ↦ if i = m then ({1} : Finset ℕ) else (e i).divisors.filter (r i ∣ ·) with hs
  set H : Fin k → ℕ → ℝ :=
    fun i dd ↦ ((μ dd : ℝ) * (dd : ℝ) / (Nat.totient dd : ℝ)) *
            (∑ aa ∈ (e i).divisors,
              (if dd ∣ aa then (μ aa : ℝ) else 0)) with hH
  rw [← pi_finsum_factor s H]
  apply finsum_bridge
  · intro d
    constructor
    · rintro ⟨⟨hpos, hrdvd, hdm⟩, hne⟩
      have hQ :
          (∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
          (∏ i, ∑ aa ∈ (e i).divisors,
            (if d i ∣ aa then (μ aa : ℝ) else 0)) = ∏ i, H i (d i) := by
        rw [hH]; simp only; rw [← Finset.prod_mul_distrib]
      refine ⟨?_, ?_⟩
      · intro i
        rw [hs]; simp only
        by_cases him : i = m
        · subst him; simp [hdm]
        · rw [if_neg him, Finset.mem_filter, Nat.mem_divisors]
          refine ⟨⟨?_, (he i).ne'⟩, hrdvd i⟩
          rw [hQ] at hne
          have hi : H i (d i) ≠ 0 := by
            intro h0; apply hne; rw [Finset.prod_eq_zero_iff]; exact ⟨i, Finset.mem_univ i, h0⟩
          rw [hH] at hi; simp only at hi
          have hinner : (∑ aa ∈ (e i).divisors,
              (if d i ∣ aa then (μ aa : ℝ) else 0)) ≠ 0 := by
            intro h0; apply hi; rw [h0, mul_zero]
          obtain ⟨aa, haa, haane⟩ := Finset.exists_ne_zero_of_sum_ne_zero hinner
          by_cases hd : d i ∣ aa
          · exact hd.trans (Nat.mem_divisors.mp haa).1
          · rw [if_neg hd] at haane; exact absurd rfl haane
      · rw [hQ] at hne; exact hne
    · rintro ⟨hmem, hne⟩
      have hQ :
          (∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
          (∏ i, ∑ aa ∈ (e i).divisors,
            (if d i ∣ aa then (μ aa : ℝ) else 0)) = ∏ i, H i (d i) := by
        rw [hH]; simp only; rw [← Finset.prod_mul_distrib]
      have hdmem : ∀ i, d i ∈ s i := hmem
      have hdm : d m = 1 := by
        have h := hdmem m; rw [hs] at h; simp only [↓reduceIte, Finset.mem_singleton] at h; exact h
      have hrdvd : ∀ i, r i ∣ d i := by
        intro i
        by_cases him : i = m
        · subst him; rw [hrm, hdm]
        · have h := hdmem i; rw [hs] at h; simp only [if_neg him, Finset.mem_filter] at h; exact h.2
      have hpos : ∀ i, 0 < d i := by
        intro i
        by_cases him : i = m
        · subst him; rw [hdm]; exact one_pos
        · have h := hdmem i; rw [hs] at h; simp only [if_neg him, Finset.mem_filter] at h
          exact Nat.pos_of_mem_divisors h.1
      exact ⟨⟨hpos, hrdvd, hdm⟩, by rw [hQ]; exact hne⟩
  · intro d _ _
    rw [hH]; simp only; rw [← Finset.prod_mul_distrib]

/-- Evaluation of the outer `d`-sum: it equals `∏ i` of `[e m = 1]` at `i = m` and
`[r i ∣ e i] * e i / φ (e i)` otherwise. -/
theorem Ce_eval (m : Fin k) (r e : Fin k → ℕ) (he : ∀ i, 0 < e i) (hrm : r m = 1)
    (hsf : ∀ i, Squarefree (r i)) :
    (∑ᶠ d ∈ {d : Fin k → ℕ | (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ d m = 1},
        (∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
          (∏ i, ∑ aa ∈ (e i).divisors,
            (if d i ∣ aa then (μ aa : ℝ) else 0))) =
      ∏ i, (if i = m then (if e i = 1 then (1 : ℝ) else 0)
              else (if r i ∣ e i then (e i : ℝ) / (Nat.totient (e i) : ℝ) else 0)) := by
  rw [outer_d_sum m r e he hrm]
  apply Finset.prod_congr rfl
  intro i _
  by_cases him : i = m
  · subst him
    rw [if_pos rfl, if_pos rfl, Finset.sum_singleton]
    simp only [ArithmeticFunction.moebius_apply_one, Nat.cast_one, Nat.totient_one, mul_one]
    have h1 : ∀ aa : ℕ, (1 : ℕ) ∣ aa := fun aa ↦ one_dvd aa
    simp only [h1, if_true]
    have hcast : (∑ aa ∈ (e i).divisors, (μ aa : ℝ)) =
        ((∑ aa ∈ (e i).divisors, (μ aa : ℤ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [hcast, ArithmeticFunction.sum_divisors_moebius]
    split <;> simp
  · rw [if_neg him, if_neg him, Finset.sum_filter]
    exact kernel_sum_squarefree (r i) (e i) (hsf i) (he i)

/-- The weight `lamval / ∏ i, e i` times the factor from `Ce_eval` collapses to
`lamval / ∏ i, φ (e i)` on `{0 < e i, r i ∣ e i, e m = 1}`, and to `0` off it. -/
theorem collapse (m : Fin k) (r e : Fin k → ℕ) (lamval : ℝ) (he : ∀ i, 0 < e i) (hrm : r m = 1) :
    (lamval / ∏ i, (e i : ℝ)) * (∏ i, (if i = m then (if e i = 1 then (1 : ℝ) else 0)
              else (if r i ∣ e i then (e i : ℝ) / (Nat.totient (e i) : ℝ) else 0))) =
    if ((∀ i, 0 < e i) ∧ (∀ i, r i ∣ e i) ∧ e m = 1) then lamval / ∏ i, (Nat.totient (e i) : ℝ)
      else 0 := by
  classical
  by_cases hS : (∀ i, 0 < e i) ∧ (∀ i, r i ∣ e i) ∧ e m = 1
  · obtain ⟨_, hrdvd, hem⟩ := hS
    rw [if_pos ⟨he, hrdvd, hem⟩]
    have hfac : ∀ i, (if i = m then (if e i = 1 then (1 : ℝ) else 0)
              else (if r i ∣ e i then (e i : ℝ) / (Nat.totient (e i) : ℝ) else 0)) =
              (if i = m then (1 : ℝ) else (e i : ℝ) / (Nat.totient (e i) : ℝ)) := by
      intro i
      by_cases him : i = m
      · subst him; rw [if_pos rfl, if_pos rfl, if_pos hem]
      · rw [if_neg him, if_neg him, if_pos (hrdvd i)]
    rw [Finset.prod_congr rfl (fun i _ ↦ hfac i)]
    rw [Fintype.prod_eq_mul_prod_compl m
        (fun i ↦ (if i = m then (1 : ℝ) else (e i : ℝ) / (Nat.totient (e i) : ℝ))),
      Fintype.prod_eq_mul_prod_compl m (fun i ↦ (e i : ℝ)),
      Fintype.prod_eq_mul_prod_compl m (fun i ↦ (Nat.totient (e i) : ℝ))]
    have hcompl_fac : (∏ i ∈ ({m}ᶜ : Finset (Fin k)),
        (if i = m then (1 : ℝ) else (e i : ℝ) / (Nat.totient (e i) : ℝ))) =
        ∏ i ∈ ({m}ᶜ : Finset (Fin k)), (e i : ℝ) / (Nat.totient (e i) : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_compl, Finset.mem_singleton] at hi
      rw [if_neg hi]
    rw [hcompl_fac, Finset.prod_div_distrib, if_pos rfl, hem]
    simp only [one_mul, Nat.cast_one, Nat.totient_one]
    have hcompl_e : (∏ i ∈ ({m}ᶜ : Finset (Fin k)), (e i : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _; exact_mod_cast (he i).ne'
    have hcompl_phi : (∏ i ∈ ({m}ᶜ : Finset (Fin k)), (Nat.totient (e i) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _; exact_mod_cast (Nat.totient_pos.mpr (he i)).ne'
    field_simp
  · rw [if_neg hS]
    have hprod : (∏ i, (if i = m then (if e i = 1 then (1 : ℝ) else 0)
              else (if r i ∣ e i then (e i : ℝ) / (Nat.totient (e i) : ℝ) else 0))) = 0 := by
      have hbad : ∃ i, (if i = m then (if e i = 1 then (1 : ℝ) else 0)
              else (if r i ∣ e i then (e i : ℝ) / (Nat.totient (e i) : ℝ) else 0)) = 0 := by
        by_cases hem : e m = 1
        · have hnr : ¬ (∀ i, r i ∣ e i) := by
            intro hr; exact hS ⟨he, hr, hem⟩
          push Not at hnr
          obtain ⟨i, hi⟩ := hnr
          have him : i ≠ m := by
            intro h; subst h; rw [hrm] at hi; exact hi (one_dvd _)
          exact ⟨i, by rw [if_neg him, if_neg hi]⟩
        · exact ⟨m, by rw [if_pos rfl, if_neg hem]⟩
      obtain ⟨i, hi⟩ := hbad
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hprod, mul_zero]

/-- Exchange a `finsum` over a set with a finite sum, given finite support in each fibre. -/
theorem finsum_mem_sum_comm {α β M : Type*} [AddCommMonoid M] (s : Set α) (t : Finset β)
    (F : α → β → M)
    (hfin : ∀ b ∈ t, (Function.support (s.indicator (fun a ↦ F a b))).Finite) :
    (∑ᶠ a ∈ s, ∑ b ∈ t, F a b) = ∑ b ∈ t, ∑ᶠ a ∈ s, F a b := by
  classical
  rw [finsum_mem_def]
  have h1 : ∀ a, s.indicator (fun a ↦ ∑ b ∈ t, F a b) a =
      ∑ b ∈ t, s.indicator (fun a ↦ F a b) a := by
    intro a
    have h2 : (s.indicator fun a ↦ ∑ b ∈ t, F a b) = ∑ b ∈ t, s.indicator (fun a ↦ F a b) := by
      rw [← Finset.indicator_sum t s fun b a ↦ F a b]; congr 1; funext a; rw [Finset.sum_apply]
    rw [h2, Finset.sum_apply]
  simp_rw [h1]
  rw [finsum_sum_comm t (fun a b ↦ s.indicator (fun a ↦ F a b) a) hfin]
  apply Finset.sum_congr rfl
  intro b _
  rw [← finsum_mem_def]
end InnerHelpers

/-- `s.indicator G` has finite support once `G x ≠ 0` forces `x i ∈ (e i).divisors` for all `i`. -/
theorem support_div_finite (e : Fin k → ℕ) (s : Set (Fin k → ℕ)) (G : (Fin k → ℕ) → ℝ)
    (hbd : ∀ x, G x ≠ 0 → ∀ i, x i ∈ (e i).divisors) :
    (Function.support (s.indicator G)).Finite := by
  classical
  apply Set.Finite.subset (Fintype.piFinset (fun i ↦ (e i).divisors)).finite_toSet
  intro x hx
  rw [Function.mem_support] at hx
  simp only [Finset.mem_coe, Fintype.mem_piFinset]
  exact hbd x fun h0 ↦ hx (by rw [Set.indicator_apply]; split <;> simp [h0])

/-- `∑ᶠ e ∈ S, f e = ∑ e ∈ lam.support, S.indicator f e` when `f` vanishes off `lam.support`. -/
theorem finsum_mem_to_support (S : Set (Fin k → ℕ)) (f : (Fin k → ℕ) → ℝ)
    (hf : ∀ e, f e ≠ 0 → lam e ≠ 0) :
    (∑ᶠ e ∈ S, f e) = ∑ e ∈ lam.support, S.indicator f e := by
  classical
  rw [finsum_mem_eq_sum_of_inter_support_eq f (t := lam.support.filter (· ∈ S))]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _; rw [Set.indicator_apply]
  · ext e
    simp only [Set.mem_inter_iff, Function.mem_support, Finset.coe_filter,
      Finsupp.mem_support_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨heS, hf0⟩; exact ⟨⟨hf e hf0, heS⟩, hf0⟩
    · rintro ⟨⟨_, heS⟩, hf0⟩; exact ⟨heS, hf0⟩

/-- Expanding `lToY lam a` in one summand: the `d`-weight times `lToY lam a / ∏ i, φ (a i)` becomes
the `d`-weight times `∏ i, μ (a i)` times `∑ᶠ e, a i ∣ e i, lam e / ∏ i, e i`. -/
theorem stepA {R W : ℕ} (hl : lam.HasPermissibleSupport R W) (d a : Fin k → ℕ) (ha : ∀ i, 0 < a i) :
    (∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
        lToY lam a / ∏ i, (Nat.totient (a i) : ℝ) =
    (∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
        (∏ i, (μ (a i) : ℝ)) *
        (∑ᶠ e ∈ {e : Fin k → ℕ | (∀ i, 0 < e i) ∧ (∀ i, a i ∣ e i)}, lam e / ∏ i, (e i : ℝ)) := by
  rw [PrimeGaps.lToY_apply hl]
  simp_rw [Int.cast_prod, Int.cast_mul, Int.cast_natCast, Nat.cast_prod]
  have hsum : lam.sum (fun e le ↦ if ∀ i, a i ∣ e i then le / ∏ i, (e i : ℝ) else 0) =
      ∑ᶠ e ∈ {e : Fin k → ℕ | (∀ i, 0 < e i) ∧ (∀ i, a i ∣ e i)},
        lam e / ∏ i, (e i : ℝ) := by
    rw [finsum_mem_to_support lam
      {e : Fin k → ℕ | (∀ i, 0 < e i) ∧ (∀ i, a i ∣ e i)}
      (fun e ↦ lam e / ∏ i, (e i : ℝ)) (by intro e h0 hc; apply h0; simp [hc]), Finsupp.sum]
    apply Finset.sum_congr rfl
    intro e he
    have hle : lam e ≠ 0 := Finsupp.mem_support_iff.mp he
    have hsq := hl.squarefree_prod_of_ne_zero hle
    have hepos : ∀ i, 0 < e i := fun i ↦ Nat.pos_of_ne_zero fun hei ↦
      hsq.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) hei)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases hdvd : ∀ i, a i ∣ e i <;> simp [hdvd, hepos]
  rw [hsum]
  have hφ : (∏ i, (Nat.totient (a i) : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _; exact_mod_cast (Nat.totient_pos.mpr (ha i)).ne'
  have key : (∏ i, (μ (a i) : ℝ) * (Nat.totient (a i) : ℝ)) =
      (∏ i, (μ (a i) : ℝ)) * (∏ i, (Nat.totient (a i) : ℝ)) := by
    rw [← Finset.prod_mul_distrib]
  rw [key]; field_simp

/-- The coefficient of `lam e` in the expanded double sum is `lam e / ∏ i, φ (e i)` on
`{0 < e i, r i ∣ e i, e m = 1}`, and `0` off it. -/
theorem per_e (r e : Fin k → ℕ) (hrm : r m = 1) (hsf : ∀ i, Squarefree (r i)) :
    (∑ᶠ d ∈ {d : Fin k → ℕ | (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ d m = 1},
        ∑ᶠ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)},
          (∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
            (∏ i, (μ (a i) : ℝ)) *
            ({e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)}.indicator
                (fun e' ↦ lam e' / ∏ i, (e' i : ℝ)) e)) =
    ({d : Fin k → ℕ | (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ d m = 1}.indicator
        (fun e' ↦ lam e' / ∏ i, (Nat.totient (e' i) : ℝ)) e) := by
  classical
  by_cases he : ∀ i, 0 < e i
  · have hind : ∀ a : Fin k → ℕ, ({e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)}.indicator
                (fun e' ↦ lam e' / ∏ i, (e' i : ℝ)) e) =
        (if (∀ i, a i ∣ e i) then (1 : ℝ) else 0) * (lam e / ∏ i, (e i : ℝ)) := by
      intro a
      by_cases hae : ∀ i, a i ∣ e i
      · rw [Set.indicator_of_mem
            (s := {e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)}) ⟨he, hae⟩,
          if_pos hae, one_mul]
      · rw [Set.indicator_of_notMem (s := {e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)})
          (by intro hc; exact hae hc.2), if_neg hae, zero_mul]
    simp_rw [hind]
    set Le := lam e / ∏ i, (e i : ℝ) with hLe
    have hrw : ∀ d a : Fin k → ℕ,
        ((∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
            (∏ i, (μ (a i) : ℝ))) *
          ((if (∀ i, a i ∣ e i) then (1 : ℝ) else 0) * Le) = Le *
            ((∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
            ((∏ i, (μ (a i) : ℝ)) *
              (if (∀ i, a i ∣ e i) then (1 : ℝ) else 0))) := by
      intro d a; ring
    simp_rw [hrw]
    have hpull_in : ∀ d : Fin k → ℕ, (∑ᶠ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)},
          Le *
            ((∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
            ((∏ i, (μ (a i) : ℝ)) *
              (if (∀ i, a i ∣ e i) then (1 : ℝ) else 0)))) = Le *
            ((∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
            (∑ᶠ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)},
              ((∏ i, (μ (a i) : ℝ)) *
                (if (∀ i, a i ∣ e i) then (1 : ℝ) else 0)))) := by
      intro d
      rw [← mul_finsum_mem, ← mul_finsum_mem]
    simp_rw [hpull_in]
    simp_rw [inner_a_sum e _ he]
    rw [← mul_finsum_mem]
    rw [Ce_eval m r e he hrm hsf]
    rw [hLe, collapse m r e (lam e) he hrm]
    rw [Set.indicator_apply]
    simp only [Set.mem_ofPred_eq]
  · rw [Set.indicator_apply, if_neg]
    · apply finsum_mem_eq_zero_of_forall_eq_zero
      intro d hd
      apply finsum_mem_eq_zero_of_forall_eq_zero
      intro a ha
      rw [Set.indicator_apply, if_neg (by intro hc; exact he hc.1), mul_zero]
    · intro hc; exact he hc.1

/-- The inner `d`-sum of `lam d / ∏ i, φ (d i)` equals the double `d`, `a` sum with the primary
transform `lToY lam` substituted in. -/
theorem inner_sum_substitute {R W : ℕ} (hl : lam.HasPermissibleSupport R W) (r : Fin k → ℕ)
    (hrm : r m = 1) (hsf : ∀ i, Squarefree (r i)) :
    (∑ᶠ d ∈ {d : Fin k → ℕ | (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ d m = 1},
        lam d / ∏ i, (Nat.totient (d i) : ℝ)) =
      ∑ᶠ d ∈ {d : Fin k → ℕ | (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ d m = 1},
          ∑ᶠ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)},
            (∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
              lToY lam a / ∏ i, (Nat.totient (a i) : ℝ) := by
  classical
  set S := {d : Fin k → ℕ | (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ d m = 1} with hSdef
  rw [finsum_mem_to_support lam S (fun e ↦ lam e / ∏ i, (Nat.totient (e i) : ℝ)) (by
        intro e h0 hc; apply h0; simp [hc])]
  rw [show (∑ᶠ d ∈ S, ∑ᶠ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)},
            (∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
              lToY lam a / ∏ i, (Nat.totient (a i) : ℝ)) =
        (∑ᶠ d ∈ S, ∑ᶠ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)}, ∑ e ∈ lam.support,
              ((∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
                (∏ i, (μ (a i) : ℝ))) *
              ({e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)}.indicator
                  (fun e' ↦ lam e' / ∏ i, (e' i : ℝ)) e)) from ?_]
  · have hinner : ∀ d : Fin k → ℕ, (∑ᶠ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)},
            ∑ e ∈ lam.support,
              ((∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
                (∏ i, (μ (a i) : ℝ))) *
              ({e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)}.indicator
                  (fun e' ↦ lam e' / ∏ i, (e' i : ℝ)) e)) =
        ∑ e ∈ lam.support, (∑ᶠ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)},
              ((∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
                (∏ i, (μ (a i) : ℝ))) *
              ({e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)}.indicator
                  (fun e' ↦ lam e' / ∏ i, (e' i : ℝ)) e)) := by
      intro d
      apply finsum_mem_sum_comm
      intro e _
      apply support_div_finite e
      intro a ha i
      have h2 : ({e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)}.indicator
                  (fun e' ↦ lam e' / ∏ i, (e' i : ℝ)) e) ≠ 0 := by
        intro h0; apply ha; rw [h0, mul_zero]
      rw [Set.indicator_apply] at h2
      have he : e ∈ {e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)} := by
        by_contra hmem; rw [if_neg hmem] at h2; exact h2 rfl
      obtain ⟨hpos, hdvd⟩ := he
      rw [Nat.mem_divisors]
      exact ⟨hdvd i, (hpos i).ne'⟩
    simp_rw [hinner]
    rw [finsum_mem_sum_comm S lam.support
        (fun d e ↦ ∑ᶠ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)},
              ((∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
                (∏ i, (μ (a i) : ℝ))) *
              ({e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)}.indicator
                  (fun e' ↦ lam e' / ∏ i, (e' i : ℝ)) e)) ?_]
    · apply Finset.sum_congr rfl
      intro e _
      exact (per_e lam m r e hrm hsf).symm
    · intro e _
      apply support_div_finite e
      intro d hd i
      have hex : ∃ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)},
          ((∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
                (∏ i, (μ (a i) : ℝ))) *
              ({e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)}.indicator
                  (fun e' ↦ lam e' / ∏ i, (e' i : ℝ)) e) ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hd (finsum_mem_eq_zero_of_forall_eq_zero hc)
      obtain ⟨a, ha, hane⟩ := hex
      have h2 : ({e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)}.indicator
                  (fun e' ↦ lam e' / ∏ i, (e' i : ℝ)) e) ≠ 0 := by
        intro h0; apply hane; rw [h0, mul_zero]
      rw [Set.indicator_apply] at h2
      have he : e ∈ {e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)} := by
        by_contra hmem; rw [if_neg hmem] at h2; exact h2 rfl
      obtain ⟨hpos, hdvd⟩ := he
      rw [Nat.mem_divisors]
      exact ⟨(ha.2 i).trans (hdvd i), (hpos i).ne'⟩
  · apply finsum_mem_congr rfl
    intro d _
    apply finsum_mem_congr rfl
    intro a ha
    rw [stepA lam hl d a ha.1,
      finsum_mem_to_support lam {e' : Fin k → ℕ | (∀ i, 0 < e' i) ∧ (∀ i, a i ∣ e' i)}
        (fun e' ↦ lam e' / ∏ i, (e' i : ℝ)) (by intro e h0 hc; apply h0; simp [hc]),
      Finset.mul_sum]

/-- Expresses `ym` as an iterated finite sum over positive tuples `d` and `a` satisfying
`r i ∣ d i`, `d i ∣ a i`, and `d m = 1`, with the coordinatewise Möbius, totient, and `g`
-weights. -/
@[pg_tag "bg246" "lem_ym_substitute_y"]
theorem lem_ym_substitute_y {R W : ℕ} (hl : lam.HasPermissibleSupport R W) (r : Fin k → ℕ)
    (hrm : r m = 1) :
    ym m lam r = (∏ i, (μ (r i) : ℝ) * (g (r i) : ℝ)) *
        ∑ᶠ d ∈ {d : Fin k → ℕ | (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ d m = 1},
          ∑ᶠ a ∈ {a : Fin k → ℕ | (∀ i, 0 < a i) ∧ (∀ i, d i ∣ a i)},
            (∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)) *
              lToY lam a / ∏ i, (Nat.totient (a i) : ℝ) := by
  by_cases hsf : ∀ i, Squarefree (r i)
  · rw [PrimeGaps.ym_apply hl]
    simp_rw [Int.cast_prod, Int.cast_mul, Int.cast_natCast, Nat.cast_prod]
    congr 1
    have hsum : lam.sum (fun d ld ↦ if d m = 1 ∧ ∀ i, r i ∣ d i then
          ld / ∏ i, (Nat.totient (d i) : ℝ) else 0) =
        ∑ᶠ d ∈ {d : Fin k → ℕ | (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ d m = 1},
          lam d / ∏ i, (Nat.totient (d i) : ℝ) := by
      rw [finsum_mem_to_support lam
        {d : Fin k → ℕ | (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ d m = 1}
        (fun d ↦ lam d / ∏ i, (Nat.totient (d i) : ℝ))
        (by intro d h0 hc; apply h0; simp [hc]), Finsupp.sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hld : lam d ≠ 0 := Finsupp.mem_support_iff.mp hd
      have hsq := hl.squarefree_prod_of_ne_zero hld
      have hdpos : ∀ i, 0 < d i := fun i ↦ Nat.pos_of_ne_zero fun hdi ↦
        hsq.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) hdi)
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      by_cases hcond : d m = 1 ∧ ∀ i, r i ∣ d i <;> simp [hcond, hdpos, and_comm]
    rw [hsum]
    exact inner_sum_substitute lam m hl r hrm hsf
  · simp only [not_forall] at hsf
    obtain ⟨i, hi⟩ := hsf
    have hμ : (μ (r i) : ℝ) = 0 := by
      have h0 : μ (r i) = 0 := by
        by_contra h
        exact hi ((ArithmeticFunction.moebius_ne_zero_iff_squarefree).1 h)
      simp [h0]
    have hP : (∏ j, (μ (r j) : ℝ) * (g (r j) : ℝ)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp [hμ]
    rw [hP, zero_mul]
    rw [PrimeGaps.ym_apply']
    simp_rw [Int.cast_prod, Int.cast_mul, Int.cast_natCast, Nat.cast_prod]
    rw [hP, zero_mul]
end MaynardSubstitute

end PrimeGaps
