/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.RestrictedReciprocalSum
public import PrimeGapsTheory.Arithmetic.TdDecomposition
public import PrimeGapsTheory.Sieve.Transforms.YmSubstituteSmooth

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The second-moment sieve asymptotic

Combines the second-moment reductions into the asymptotic formula for the sieve sum.

## Main definitions

* `gcoordPrimes`: The eligible odd primes below a cutoff that do not divide the sieve modulus.

## Main results

* `lem_S2m_g_coord_cutoff`: The one-coordinate `g`-mass cutoff bound.
* `lem_S2m_tuple_g_mass_cutoff`: The `k`-tuple `g`-mass cutoff bound.
* `lem_S2m_second_moment`: Gives the second-moment sieve asymptotic with its error term.
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius
open scoped Finset

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

/-- A coordinate dividing a squarefree coordinate of some permissible tuple in the support of `l`
is at most `R`, since the whole product of that tuple is. -/
private theorem coord_le_R_of_dvd_of_mem_support {k : ℕ} {l : (Fin k → ℕ) →₀ ℝ}
    {R : ℝ} {W : ℕ} (hSS : l.HasPermissibleSupport ⌊R⌋₊ W)
    {d : Fin k → ℕ} (hld : l d ≠ 0) {i : Fin k} {n : ℕ}
    (hdvd : n ∣ d i) (hsqd : Squarefree (d i)) :
    (n : ℝ) ≤ R := by
  have hprodNat := hSS.prod_lt_R_of_ne_zero hld
  have hsqprod := hSS.squarefree_prod_of_ne_zero hld
  have hfloorpos : 0 < ⌊R⌋₊ := lt_of_lt_of_le (Nat.pos_of_ne_zero hsqprod.ne_zero) hprodNat
  have hn : n ≤ ∏ j, d j :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hsqd.ne_zero) hdvd).trans <|
      Nat.le_of_dvd (Nat.pos_of_ne_zero hsqprod.ne_zero) <|
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  exact le_trans (by exact_mod_cast hn.trans hprodNat)
    (Nat.floor_le (Nat.pos_of_floor_pos hfloorpos).le)

open ArithmeticFunction in
/-- `ym m l r ≠ 0` forces `r i ≤ R` in every coordinate, for `l` of permissible support at level
`⌊R⌋₊`. -/
theorem ym_coord_lt_of_ne_zero {k : ℕ} {l : (Fin k → ℕ) →₀ ℝ}
    {R : ℝ} {W : ℕ} (hSS : l.HasPermissibleSupport ⌊R⌋₊ W)
    {m : Fin k} {r : Fin k → ℕ} (hr : (PrimeGaps.ym m) l r ≠ 0) :
    ∀ i, (r i : ℝ) ≤ R := by
  intro i
  rw [PrimeGaps.ym_apply', Finsupp.sum] at hr
  obtain ⟨d, hd, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero (mul_ne_zero_iff.mp hr).2
  obtain ⟨hdvd, hsqd⟩ : r i ∣ d i ∧ Squarefree (d i) := by
    by_contra hcon
    exact hterm (if_neg fun h ↦ hcon (h.2 i))
  exact coord_le_R_of_dvd_of_mem_support hSS (Finsupp.mem_support_iff.mp hd) hdvd hsqd

/-- `ym m l r = 0` once some coordinate has `R < r i`. -/
theorem ym_eq_zero_of_coord_ge {k : ℕ} {l : (Fin k → ℕ) →₀ ℝ}
    {R : ℝ} {W : ℕ} (hSS : l.HasPermissibleSupport ⌊R⌋₊ W)
    {m i : Fin k} {r : Fin k → ℕ}
    (hri : R < (r i : ℝ)) :
    (PrimeGaps.ym m) l r = 0 := by
  by_contra h
  exact absurd (ym_coord_lt_of_ne_zero hSS h i) (not_le.mpr hri)

/-- `lToY l x ≠ 0` forces `x i ≤ R` in every coordinate, for `l` of permissible support at level
`⌊R⌋₊`. -/
theorem lToY_coord_lt_of_ne_zero {k : ℕ} {l : (Fin k → ℕ) →₀ ℝ}
    {R : ℝ} {W : ℕ} (hSS : l.HasPermissibleSupport ⌊R⌋₊ W)
    {x : Fin k → ℕ} (hx : (PrimeGaps.lToY l) x ≠ 0) :
    ∀ i, (x i : ℝ) ≤ R := by
  intro i
  rw [PrimeGaps.lToY_apply', Finsupp.sum] at hx
  obtain ⟨d, hd, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero (mul_ne_zero_iff.mp hx).2
  obtain ⟨hdvd, hsqd⟩ : x i ∣ d i ∧ Squarefree (d i) := by
    by_contra hcon
    exact hterm (if_neg fun h ↦ hcon (h i))
  exact coord_le_R_of_dvd_of_mem_support hSS (Finsupp.mem_support_iff.mp hd) hdvd hsqd

/-- `lToY l x = 0` once some coordinate has `R < x i`. -/
theorem lToY_eq_zero_of_coord_ge {k : ℕ} {l : (Fin k → ℕ) →₀ ℝ}
    {R : ℝ} {W : ℕ} (hSS : l.HasPermissibleSupport ⌊R⌋₊ W)
    {i : Fin k} {x : Fin k → ℕ}
    (hxi : R < (x i : ℝ)) :
    (PrimeGaps.lToY l) x = 0 := by
  by_contra h
  exact absurd (lToY_coord_lt_of_ne_zero hSS h i) (not_le.mpr hxi)

/-- `yInverseSum l m r = 0` once `R < r i` for some `i ≠ m`, since `m` is the only coordinate the
sum overwrites. -/
theorem yInverseSum_eq_zero_of_coord_ge {k : ℕ} {l : (Fin k → ℕ) →₀ ℝ}
    {R : ℝ} {W : ℕ} (hSS : l.HasPermissibleSupport ⌊R⌋₊ W)
    {m i : Fin k} {r : Fin k → ℕ} (hi : i ≠ m)
    (hri : R < (r i : ℝ)) :
    yInverseSum l m r = 0 := by
  change (∑' a : ℕ, (PrimeGaps.lToY l) (Function.update r m a) / (a.totient : ℝ)) = 0
  have hterm (a : ℕ) : (PrimeGaps.lToY l) (Function.update r m a) = 0 :=
    lToY_eq_zero_of_coord_ge (i := i) hSS (by rwa [Function.update_of_ne hi])
  simp [hterm]

/-- Both `ym m l r` and `yInverseSum l m r` vanish once some coordinate `r i` with `i ≠ m` fails
to be squarefree: the Möbius factor at coordinate `i` is then zero in both defining products, and
`i` is untouched by the `m`-update over which `yInverseSum` sums. -/
private theorem ym_eq_zero_and_yInverseSum_eq_zero_of_not_squarefree {k : ℕ} (m : Fin k)
    (l : (Fin k → ℕ) →₀ ℝ) (r : Fin k → ℕ) {i : Fin k} (him : i ≠ m)
    (hi : ¬ Squarefree (r i)) :
    (PrimeGaps.ym m) l r = 0 ∧ yInverseSum l m r = 0 := by
  have hμ0 : μ (r i) = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi
  constructor
  · have hp : (∏ j, μ (r j) * g (r j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hμ0, zero_mul])
    rw [PrimeGaps.ym_apply', hp]
    simp
  · change (∑' a : ℕ, (PrimeGaps.lToY l) (Function.update r m a) / (a.totient : ℝ)) = 0
    have hterm (a : ℕ) : (PrimeGaps.lToY l) (Function.update r m a) = 0 := by
      have hp : (∏ j, μ (Function.update r m a j) *
          ((Function.update r m a j).totient : ℤ)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i)
          (by rw [Function.update_of_ne him, hμ0, zero_mul])
      rw [PrimeGaps.lToY_apply', hp]
      simp
    simp [hterm]

/-- The coordinate kernel `r ↦ 1 / g r`, cut off to `1 ≤ r ≤ R` squarefree and coprime to `W`, is
summable, being supported in `Finset.range (⌈R⌉₊ + 1)`. -/
theorem gcoord_summable (R : ℝ) (W : ℕ) : Summable (fun r : ℕ ↦
      if 1 ≤ r ∧ (r : ℝ) ≤ R ∧ r.Coprime W ∧ Squarefree r
      then (1 : ℝ) / (g r : ℝ) else 0) :=
  summable_of_ne_finset_zero (s := Finset.range (⌈R⌉₊ + 1)) fun r hr ↦ if_neg fun hg ↦
    hr (Finset.mem_range.mpr (Nat.lt_succ_of_le (by exact_mod_cast hg.2.1.trans (Nat.le_ceil _))))

/-- Eligible odd primes below `Rr` not dividing `Ww`:
`𝒫(Rr,Ww) = { p prime: p ≤ ⌊Rr⌋₊, 3 ≤ p, p ∤ Ww }`. (Binders avoid the ambient `R` /`W`
notations of this environment.) -/
noncomputable def gcoordPrimes (Rr : ℝ) (Ww : ℕ) : Finset ℕ :=
  {p ∈ ((⌊Rr⌋₊ + 1).primesBelow) | 3 ≤ p ∧ ¬ p ∣ Ww}

/-- The cut-off kernel sum is at most the Euler product
`∏ p ∈ gcoordPrimes Rr Ww, (1 + 1 / (p - 2))`. -/
theorem gcoord_sum_le_eulerP (Rr : ℝ) (Ww : ℕ) :
    (∑' r : ℕ, if 1 ≤ r ∧ (r : ℝ) ≤ Rr ∧ r.Coprime Ww ∧ Squarefree r
        then (1 : ℝ) / (g r : ℝ) else 0) ≤ ∏ p ∈ gcoordPrimes Rr Ww, (1 + 1 / ((p : ℝ) - 2)) := by
  set P : Finset ℕ := gcoordPrimes Rr Ww with hP
  set Q : ℕ → Prop := fun r ↦ 1 ≤ r ∧ (r : ℝ) ≤ Rr ∧ r.Coprime Ww ∧ Squarefree r with hQ
  have hstep1 : (∑' r : ℕ, if Q r then (1 : ℝ) / (g r : ℝ) else 0) =
      ∑ r ∈ Finset.range (⌈Rr⌉₊ + 1), if Q r then (1 : ℝ) / (g r : ℝ) else 0 :=
    tsum_eq_sum fun r hr ↦ if_neg fun hQr ↦ hr (Finset.mem_range.mpr
      (Nat.lt_succ_of_le (by exact_mod_cast hQr.2.1.trans (Nat.le_ceil _))))
  set Val : Finset ℕ := (Finset.range (⌈Rr⌉₊ + 1)).filter Q with hVal
  have hstep2 : (∑ r ∈ Finset.range (⌈Rr⌉₊ + 1), if Q r then (1 : ℝ) / (g r : ℝ) else 0) =
      ∑ r ∈ Val, (1 : ℝ) / (g r : ℝ) := by rw [hVal, Finset.sum_filter]
  have hstep3 : (∏ p ∈ P, (1 + 1 / ((p : ℝ) - 2))) =
      ∑ t ∈ P.powerset, ∏ p ∈ t, (1 : ℝ) / ((p : ℝ) - 2) := by
    rw [Finset.prod_congr rfl fun (p : ℕ) _ ↦ add_comm (1 : ℝ) (1 / ((p : ℝ) - 2)),
      Finset.prod_add_one]
  rw [hstep1, hstep2, hstep3]
  set Val3 : Finset ℕ := Val.filter (fun r ↦ ¬ 2 ∣ r) with hVal3
  have hsqf : ∀ r ∈ Val, Squarefree r := fun r hr ↦ (Finset.mem_filter.mp hr).2.2.2.2
  have hval_eq_val3 : (∑ r ∈ Val, (1 : ℝ) / (g r : ℝ)) = ∑ r ∈ Val3, (1 : ℝ) / (g r : ℝ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun r hrVal hrVal3 ↦ ?_).symm
    have hr2 : 2 ∣ r := by
      by_contra h2
      exact hrVal3 (Finset.mem_filter.mpr ⟨hrVal, h2⟩)
    have hrsqf := hsqf r hrVal
    have hg0 : (g r : ℝ) = 0 := by
      rw [ArithmeticFunction.coe_detotient_squarefree_eq_prod hrsqf]
      exact Finset.prod_eq_zero
        ((Nat.mem_primeFactors_of_ne_zero hrsqf.ne_zero).mpr ⟨Nat.prime_two, hr2⟩) (by norm_num)
    rw [hg0]
    simp
  have hterm_eq : ∀ r ∈ Val3, (1 : ℝ) / (g r : ℝ) =
      ∏ p ∈ r.primeFactors, (1 : ℝ) / ((p : ℝ) - 2) := by
    intro r hr
    rw [ArithmeticFunction.coe_detotient_squarefree_eq_prod (hsqf r (Finset.mem_filter.mp hr).1),
      one_div, ← Finset.prod_inv_distrib]
    simp only [one_div]
  have hInj : Set.InjOn (fun r : ℕ ↦ r.primeFactors) (Val3 : Set ℕ) := by
    intro a ha b hb hab
    have hpf : a.primeFactors = b.primeFactors := hab
    rw [← Nat.prod_primeFactors_of_squarefree (hsqf a (Finset.mem_filter.mp ha).1),
      ← Nat.prod_primeFactors_of_squarefree (hsqf b (Finset.mem_filter.mp hb).1), hpf]
  have hreindex : (∑ r ∈ Val3, ∏ p ∈ r.primeFactors, (1 : ℝ) / ((p : ℝ) - 2)) =
      ∑ t ∈ Val3.image (fun r : ℕ ↦ r.primeFactors), ∏ p ∈ t, (1 : ℝ) / ((p : ℝ) - 2) := by
    rw [Finset.sum_image hInj]
  rw [hval_eq_val3, Finset.sum_congr rfl hterm_eq, hreindex]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro t ht
    obtain ⟨r, hrVal3, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.mem_powerset]
    intro q hq
    have hr2 : ¬ 2 ∣ r := (Finset.mem_filter.mp hrVal3).2
    have hrQ : Q r := (Finset.mem_filter.mp (Finset.mem_filter.mp hrVal3).1).2
    have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ r := Nat.dvd_of_mem_primeFactors hq
    have hqfloor : q ≤ ⌊Rr⌋₊ :=
      Nat.le_floor (le_trans (by exact_mod_cast Nat.le_of_dvd hrQ.1 hqdvd) hrQ.2.1)
    have hq3 : 3 ≤ q := by
      have hq2 := hqp.two_le
      have hqne2 : q ≠ 2 := fun h2 ↦ hr2 (h2 ▸ hqdvd)
      omega
    have hqnW : ¬ q ∣ Ww := fun hqW ↦ by
      have hdvd1 : q ∣ Nat.gcd r Ww := Nat.dvd_gcd hqdvd hqW
      rw [hrQ.2.2.1] at hdvd1
      exact hqp.one_lt.ne' (Nat.eq_one_of_dvd_one hdvd1)
    rw [hP, gcoordPrimes, Finset.mem_filter, Nat.mem_primesBelow]
    exact ⟨⟨by omega, hqp⟩, hq3, hqnW⟩
  · intro t ht _
    rw [Finset.mem_powerset] at ht
    refine Finset.prod_nonneg fun p hp ↦ ?_
    have hpP := ht hp
    rw [hP, gcoordPrimes, Finset.mem_filter] at hpP
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpP.2.1
    apply div_nonneg zero_le_one
    linarith

/-- `∏ (1 + 1 / (p - 2)) ≤ C₀ * ∏ (1 + 1 / (p - 1))` over `gcoordPrimes Rr Ww`, for a single `C₀`
independent of `Rr` and `Ww`. -/
theorem gcoord_eulerP_factor : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (Rr : ℝ) (Ww : ℕ),
      ∏ p ∈ gcoordPrimes Rr Ww, (1 + 1 / ((p : ℝ) - 2)) ≤
        C₀ * ∏ p ∈ gcoordPrimes Rr Ww, (1 + 1 / ((p : ℝ) - 1)) := by
  refine ⟨rexp 1, (Real.exp_pos 1).le, ?_⟩
  intro Rr Ww
  set P : Finset ℕ := gcoordPrimes Rr Ww with hP
  have hp3 : ∀ p ∈ P, 3 ≤ p := fun p hp ↦ by
    rw [hP, gcoordPrimes, Finset.mem_filter] at hp
    exact hp.2.1
  have hp3R : ∀ p ∈ P, (3 : ℝ) ≤ (p : ℝ) := fun p hp ↦ by exact_mod_cast hp3 p hp
  have hfactor : ∀ p ∈ P,
      (1 + 1 / ((p : ℝ) - 2)) = (1 + 1 / ((p : ℝ) - 1)) * (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    intro p hp
    have h3 := hp3R p hp
    have h1 : (p : ℝ) - 2 ≠ 0 := by linarith
    have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h0 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hsplit : ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 2)) = (∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1))) *
        (∏ p ∈ P, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) :=
    (Finset.prod_congr rfl hfactor).trans Finset.prod_mul_distrib
  rw [hsplit, mul_comm (rexp 1) _]
  apply mul_le_mul_of_nonneg_left _ ?_
  · have hexp : ∏ p ∈ P, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) ≤
        rexp (∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
      set fg : ℕ → ℝ := fun p ↦ if 3 ≤ p then 1 / ((p : ℝ) * ((p : ℝ) - 2)) else 0 with hfg
      have hfg0 : ∀ p, 0 ≤ fg p := by
        intro p
        rw [hfg]
        dsimp only
        split
        · rename_i h
          have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h
          exact div_nonneg zero_le_one (by nlinarith)
        · rfl
      have hprodeq : ∏ p ∈ P, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) = ∏ p ∈ P, (1 + fg p) :=
        Finset.prod_congr rfl fun p hp ↦ by simp only [hfg, if_pos (hp3 p hp)]
      have hsumeq : ∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 2)) = ∑ p ∈ P, fg p :=
        Finset.sum_congr rfl fun p hp ↦ by simp only [hfg, if_pos (hp3 p hp)]
      rw [hprodeq, hsumeq]
      exact Real.prod_one_add_le_exp_sum (s := P) (f := fg) hfg0
    refine le_trans hexp ?_
    have hsum1 : ∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 2)) ≤ 1 := by
      have hterm : ∀ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 2)) ≤
          1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
        intro p hp
        have h3 := hp3R p hp
        have h1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
        have h2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        have h0 : (0 : ℝ) < (p : ℝ) := by linarith
        rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      refine le_trans (Finset.sum_le_sum hterm) ?_
      have hPsub : P ⊆ Finset.Icc 3 (⌊Rr⌋₊) := fun p hp ↦ by
        rw [hP, gcoordPrimes, Finset.mem_filter, Nat.mem_primesBelow] at hp
        exact Finset.mem_Icc.mpr ⟨hp.2.1, by omega⟩
      have hnn2 : ∀ p ∈ Finset.Icc 3 (⌊Rr⌋₊), (0 : ℝ) ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
        intro p hp
        rw [Finset.mem_Icc] at hp
        have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1
        rw [sub_nonneg]
        exact div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith)
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun p hp _ ↦ hnn2 p hp)) ?_
      set M := ⌊Rr⌋₊ with hM
      by_cases hM3 : 3 ≤ M
      · have htele : ∑ i ∈ Finset.Icc 3 M, (1 / ((i : ℝ) - 2) - 1 / ((i : ℝ) - 1)) =
            ∑ i ∈ Finset.Icc 3 M, ((fun j : ℕ ↦ -1 / ((j : ℝ) - 2)) (i + 1) -
                  (fun j : ℕ ↦ -1 / ((j : ℝ) - 2)) i) := by
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          rw [Finset.mem_Icc] at hi
          have h3 : (3 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi.1
          simp only
          have h1 : (i : ℝ) - 2 ≠ 0 := by linarith
          have h2 : (i : ℝ) - 1 ≠ 0 := by linarith
          have h2' : ((i : ℝ) + 1) - 2 ≠ 0 := by linarith
          push_cast
          field_simp
          ring
        have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
          have : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3
          linarith
        have hM1' : (0 : ℝ) ≤ 1 / ((M : ℝ) - 1) := by positivity
        rw [htele, Finset.sum_Icc_sub hM3 (fun j : ℕ ↦ -1 / ((j : ℝ) - 2)),
          show ((M + 1 : ℕ) : ℝ) - 2 = (M : ℝ) - 1 by push_cast; ring,
          show ((3 : ℕ) : ℝ) - 2 = (1 : ℝ) by norm_num, neg_div, neg_div]
        linarith
      · rw [show Finset.Icc 3 M = ∅ by rw [Finset.Icc_eq_empty]; omega, Finset.sum_empty]
        norm_num
    exact Real.exp_le_exp.mpr hsum1
  · refine Finset.prod_nonneg fun p hp ↦ ?_
    have h3 := hp3R p hp
    have h1 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    linarith

/-- `∏ p ∈ Ww.primeFactors, (1 + 1 / (p - 1)) = Ww / φ(Ww)` for squarefree `Ww`. -/
theorem prodPf_totient_id (Ww : ℕ) (hsqf : Squarefree Ww) :
    ∏ p ∈ Ww.primeFactors, (1 + 1 / ((p : ℝ) - 1)) = (Ww : ℝ) / (Ww.totient : ℝ) := by
  have hp2 : ∀ p ∈ Ww.primeFactors, 2 ≤ p :=
    fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le
  have hstep : ∏ p ∈ Ww.primeFactors, (1 + 1 / ((p : ℝ) - 1)) =
      ∏ p ∈ Ww.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) :=
    Finset.prod_congr rfl fun p hp ↦ by
      have hppos : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2 p hp
      have hne : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
  have hnum : ∏ p ∈ Ww.primeFactors, (p : ℝ) = (Ww : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsqf]
  have hden : ∏ p ∈ Ww.primeFactors, ((p : ℝ) - 1) = (Ww.totient : ℝ) := by
    rw [Nat.totient_squarefree_prod hsqf (Nat.pos_of_ne_zero hsqf.ne_zero), Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    rw [Nat.cast_sub (by have := hp2 p hp; omega)]
    simp
  rw [hstep, Finset.prod_div_distrib, hnum, hden]

/-- `∏ p ∈ gcoordPrimes Rr Ww, (1 + 1 / (p - 1)) ≤ C * log Rr * (φ(Ww) / Ww)`, uniformly in `Rr` and
in squarefree `Ww` all of whose prime factors are at most `Rr`. -/
theorem gcoord_A_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (Rr : ℝ) (Ww : ℕ), Squarefree Ww → 1 ≤ Ww →
      (∀ p ∈ Ww.primeFactors, (p : ℝ) ≤ Rr) → rexp 1 ≤ Rr →
      ∏ p ∈ gcoordPrimes Rr Ww, (1 + 1 / ((p : ℝ) - 1)) ≤
        C * Real.log Rr * ((Ww.totient : ℝ) / (Ww : ℝ)) := by
  obtain ⟨C, hC0, hEP⟩ := RestrictedReciprocalSum.euler_prod_le 1 (le_refl 1)
  refine ⟨C, hC0.le, ?_⟩
  intro Rr Ww hsqf hW1 hpfle hRexp
  have hR2 : (2 : ℝ) ≤ Rr := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hWpos : 0 < Ww := hW1
  have hWposR : (0 : ℝ) < (Ww : ℝ) := by exact_mod_cast hWpos
  have hφposR : (0 : ℝ) < (Ww.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hWpos
  set Q : Finset ℕ := (⌊Rr⌋₊ + 1).primesBelow with hQ
  set D : Finset ℕ := Ww.primeFactors with hD
  set P : Finset ℕ := gcoordPrimes Rr Ww with hPdef
  set f : ℕ → ℝ := fun p ↦ 1 + 1 / ((p : ℝ) - 1) with hf
  have hf1 : ∀ p, Nat.Prime p → 1 ≤ f p := fun p hp ↦ by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have h1 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    rw [hf]
    linarith
  have hPQ : P ⊆ Q := by
    rw [hPdef, hQ, gcoordPrimes]
    exact Finset.filter_subset _ _
  have hDQ : D ⊆ Q := fun p hp ↦ by
    rw [hD] at hp
    rw [hQ, Nat.mem_primesBelow]
    have hfloor : p ≤ ⌊Rr⌋₊ := Nat.le_floor (hpfle p hp)
    exact ⟨by omega, Nat.prime_of_mem_primeFactors hp⟩
  have hdisj : Disjoint P D := by
    rw [Finset.disjoint_left]
    intro p hpP hpD
    rw [hPdef, gcoordPrimes, Finset.mem_filter] at hpP
    rw [hD, Nat.mem_primeFactors] at hpD
    exact hpP.2.2 hpD.2.1
  have hDprod : ∏ p ∈ D, f p = (Ww : ℝ) / (Ww.totient : ℝ) := by
    rw [hD, hf]
    exact prodPf_totient_id Ww hsqf
  have hunion : (∏ p ∈ P, f p) * (∏ p ∈ D, f p) ≤ ∏ p ∈ Q, f p := by
    rw [← Finset.prod_union hdisj]
    apply Finset.prod_le_prod_of_subset_of_one_le
    · exact Finset.union_subset hPQ hDQ
    · intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · rw [hPdef, gcoordPrimes, Finset.mem_filter, Nat.mem_primesBelow] at h
        exact le_trans zero_le_one (hf1 p h.1.2)
      · exact le_trans zero_le_one (hf1 p (Nat.prime_of_mem_primeFactors (by rwa [hD] at h)))
    · intro p hpQ _
      rw [hQ, Nat.mem_primesBelow] at hpQ
      exact hf1 p hpQ.2
  have hEPle : ∏ p ∈ Q, f p ≤ C * Real.log Rr := by
    have := hEP Rr hR2
    rw [hQ]
    simp only [Nat.cast_one, pow_one] at this
    convert this using 2
  have hPle : ∏ p ∈ P, f p ≤ (∏ p ∈ Q, f p) * ((Ww.totient : ℝ) / (Ww : ℝ)) := by
    have hunion' : (∏ p ∈ P, f p) * ((Ww : ℝ) / (Ww.totient : ℝ)) ≤ ∏ p ∈ Q, f p := by
      rw [← hDprod]
      exact hunion
    have hprodP0 : 0 ≤ ∏ p ∈ P, f p := Finset.prod_nonneg fun p hpP ↦ by
      rw [hPdef, gcoordPrimes, Finset.mem_filter, Nat.mem_primesBelow] at hpP
      exact le_trans zero_le_one (hf1 p hpP.1.2)
    have hWratio : (0 : ℝ) < (Ww : ℝ) / (Ww.totient : ℝ) := div_pos hWposR hφposR
    have hid : ((Ww : ℝ) / (Ww.totient : ℝ)) * ((Ww.totient : ℝ) / (Ww : ℝ)) = 1 := by
      field_simp
    nlinarith [hunion', hprodP0, hWratio,
      mul_le_mul_of_nonneg_right hunion' (le_of_lt (div_pos hφposR hWposR))]
  calc ∏ p ∈ P, f p ≤ (∏ p ∈ Q, f p) * ((Ww.totient : ℝ) / (Ww : ℝ)) := hPle
    _ ≤ C * Real.log Rr * ((Ww.totient : ℝ) / (Ww : ℝ)) :=
        mul_le_mul_of_nonneg_right hEPle (div_nonneg hφposR.le hWposR.le)

/-- The cut-off kernel sum obeys `∑ 1 / g r ≤ Cg * φ(W) * log R / W`. -/
theorem gcoord_kernel_constant : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (R : ℝ) (W : ℕ), Squarefree W → 1 ≤ W →
      (∀ p ∈ W.primeFactors, (p : ℝ) ≤ R) →
      rexp 1 ≤ R →
      (∑' r : ℕ, if 1 ≤ r ∧ (r : ℝ) ≤ R ∧ r.Coprime W ∧ Squarefree r
        then (1 : ℝ) / (g r : ℝ) else 0) ≤ Cg * ((W.totient : ℝ) *
                Real.log R / W) := by
  obtain ⟨C₀, hC₀0, hfac⟩ := gcoord_eulerP_factor
  obtain ⟨C, hC0, hAle⟩ := gcoord_A_le
  refine ⟨C₀ * C, mul_nonneg hC₀0 hC0, ?_⟩
  intro R W hWsqf hW1 hpf hRexp
  calc (∑' r : ℕ, if 1 ≤ r ∧ (r : ℝ) ≤ R ∧ r.Coprime W ∧ Squarefree r
        then (1 : ℝ) / (g r : ℝ) else 0) ≤ ∏ p ∈ gcoordPrimes R W, (1 + 1 / ((p : ℝ) - 2)) :=
        gcoord_sum_le_eulerP R W
    _ ≤ C₀ * ∏ p ∈ gcoordPrimes R W, (1 + 1 / ((p : ℝ) - 1)) := hfac R W
    _ ≤ C₀ * (C * Real.log R * ((W.totient : ℝ) / (W : ℝ))) :=
        mul_le_mul_of_nonneg_left (hAle R W hWsqf hW1 hpf hRexp) hC₀0
    _ = (C₀ * C) * ((W.totient : ℝ) * Real.log R / (W : ℝ)) := by ring

/-- The one-coordinate `g`-mass cutoff: the kernel `r ↦ 1 / g r` cut off at `R` is summable with
`∑ 1 / g r ≤ Cg * φ(W) * log R / W`. -/
theorem lem_S2m_g_coord_cutoff : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (R : ℝ) (W : ℕ), Squarefree W → 1 ≤ W →
      (∀ p ∈ W.primeFactors, (p : ℝ) ≤ R) →
      rexp 1 ≤ R →
      Summable (fun r : ℕ ↦ if 1 ≤ r ∧ (r : ℝ) ≤ R ∧ r.Coprime W ∧ Squarefree r
        then (1 : ℝ) / (g r : ℝ) else 0) ∧
      (∑' r : ℕ, if 1 ≤ r ∧ (r : ℝ) ≤ R ∧ r.Coprime W ∧ Squarefree r
        then (1 : ℝ) / (g r : ℝ) else 0) ≤ Cg * ((W.totient : ℝ) *
                Real.log R / W) := by
  obtain ⟨Cg, hCg0, hbound⟩ := gcoord_kernel_constant
  exact ⟨Cg, hCg0, fun R W hWsqf hW1 hpf hRexp ↦
    ⟨gcoord_summable R W, hbound R W hWsqf hW1 hpf hRexp⟩⟩

/-- The `k`-tuple `g`-mass cutoff: the kernel `r ↦ 1 / ∏_{i ≠ m} g (r i)` on tuples with `r m = 1`
and the other coordinates cut off at `R` is summable, with sum at most
`C * (φ(W) * log R / W) ^ (k - 1)`. -/
theorem lem_S2m_tuple_g_mass_cutoff {k : ℕ} : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (m : Fin k) (R : ℝ) (W : ℕ), Squarefree W → 1 ≤ W → (∀ p ∈ W.primeFactors, (p : ℝ) ≤ R) →
      rexp 1 ≤ R →
      Summable (fun r : Fin k → ℕ ↦ if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i : ℝ) ≤ R ∧
           (r i).Coprime W ∧ Squarefree (r i))
        then (1 : ℝ) / (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ)) else 0) ∧
      (∑' r : Fin k → ℕ, if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i : ℝ) ≤ R ∧
           (r i).Coprime W ∧ Squarefree (r i))
        then (1 : ℝ) / (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ)) else 0) ≤
        C * ((W.totient : ℝ) * Real.log R / W) ^ (k - 1) := by
  obtain ⟨Cg, hCg0, hcoord⟩ := lem_S2m_g_coord_cutoff
  refine ⟨Cg ^ (k - 1), pow_nonneg hCg0 _, ?_⟩
  intro m R W hWsqf hW1 hpf hRexp
  set L : ℝ := (W.totient : ℝ) * Real.log R / W with hL
  set sf : ℕ → ℝ := fun n ↦ if 1 ≤ n ∧ (n : ℝ) ≤ R ∧ n.Coprime W ∧ Squarefree n
    then (1 : ℝ) / (g n : ℝ) else 0 with hsf
  obtain ⟨-, hSbound⟩ := hcoord R W hWsqf hW1 hpf hRexp
  have hsf0 : ∀ n, 0 ≤ sf n := fun n ↦ by
    rw [hsf]
    dsimp only
    split
    · exact div_nonneg zero_le_one (by positivity)
    · rfl
  set S : ℝ := ∑' n, sf n with hS
  have hS0 : 0 ≤ S := by rw [hS]; exact tsum_nonneg hsf0
  have hSle : S ≤ Cg * L := by
    rw [hS, hsf, hL]
    exact hSbound
  have hR1 : (1 : ℝ) < R :=
    lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) (Real.add_one_le_exp 1)) hRexp
  have hceil1 : 1 < ⌈R⌉₊ := Nat.lt_ceil.mpr (by rw [Nat.cast_one]; exact hR1)
  set B : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ : Fin k ↦ Finset.range (⌈R⌉₊ + 1)) with hB
  set gf : Fin k → ℕ → ℝ := fun i n ↦
    if i = m then (if n = 1 then (1 : ℝ) else 0) else sf n with hgf
  set F : (Fin k → ℕ) → ℝ := fun r ↦ if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i : ℝ) ≤ R ∧
        (r i).Coprime W ∧ Squarefree (r i))
    then (1 : ℝ) / (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ)) else 0 with hF
  have hFprod : ∀ r : Fin k → ℕ, F r = ∏ i, gf i (r i) := by
    intro r
    rw [hF]
    dsimp only
    by_cases hguard : r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i : ℝ) ≤ R ∧
        (r i).Coprime W ∧ Squarefree (r i))
    · have hmfac : gf m (r m) = 1 := by
        rw [hgf]; dsimp only; rw [if_pos rfl, if_pos hguard.1]
      rw [if_pos hguard, ← Finset.prod_erase_mul _ _ (Finset.mem_univ m), hmfac, mul_one, one_div,
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      have hi' : i ≠ m := Finset.ne_of_mem_erase hi
      rw [hgf]; dsimp only; rw [if_neg hi', hsf]; dsimp only
      rw [if_pos (hguard.2 i hi'), one_div]
    · rw [if_neg hguard]
      symm
      by_cases hrm : r m = 1
      · rw [not_and] at hguard
        obtain ⟨i, hi⟩ := not_forall.mp (hguard hrm)
        obtain ⟨hi', hQ⟩ := Classical.not_imp.mp hi
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [hgf]; dsimp only; rw [if_neg hi', hsf]; dsimp only
        rw [if_neg hQ]
      · refine Finset.prod_eq_zero (Finset.mem_univ m) ?_
        rw [hgf]; dsimp only; rw [if_pos rfl, if_neg hrm]
  have hFoff : ∀ r ∉ B, F r = 0 := by
    intro r hr
    rw [hF]
    dsimp only
    refine if_neg fun hguard ↦ hr ?_
    rw [hB, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    by_cases hi : i = m
    · subst hi; rw [hguard.1]; exact Nat.lt_succ_of_lt hceil1
    · exact Nat.lt_succ_of_le
        (by exact_mod_cast (hguard.2 i hi).2.1.trans (Nat.le_ceil _))
  refine ⟨summable_of_ne_finset_zero (s := B) hFoff, ?_⟩
  have htsum_eq : (∑' r : Fin k → ℕ, F r) = ∑ r ∈ B, F r := tsum_eq_sum hFoff
  have hBsum : (∑ r ∈ B, F r) = ∏ i, (∑ j ∈ Finset.range (⌈R⌉₊ + 1), gf i j) := by
    rw [Finset.prod_univ_sum (fun _ : Fin k ↦ Finset.range (⌈R⌉₊ + 1)) gf, hB]
    exact Finset.sum_congr rfl fun r _ ↦ hFprod r
  have hfac : ∀ i, (∑ j ∈ Finset.range (⌈R⌉₊ + 1), gf i j) = if i = m then (1 : ℝ) else S := by
    intro i
    by_cases hi : i = m
    · subst hi
      have hrw : (∑ j ∈ Finset.range (⌈R⌉₊ + 1), gf i j) =
          ∑ j ∈ Finset.range (⌈R⌉₊ + 1), (if j = 1 then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun j _ ↦ by rw [hgf]; dsimp only; rw [if_pos rfl]
      rw [if_pos rfl, hrw]
      simp [Finset.sum_ite_eq', Finset.mem_range.mpr (Nat.lt_succ_of_lt hceil1)]
    · have hstep : (∑ j ∈ Finset.range (⌈R⌉₊ + 1), gf i j) =
          ∑ j ∈ Finset.range (⌈R⌉₊ + 1), sf j :=
        Finset.sum_congr rfl fun j _ ↦ by rw [hgf]; dsimp only; rw [if_neg hi]
      rw [if_neg hi, hstep, hS]
      refine (tsum_eq_sum fun n hn ↦ ?_).symm
      rw [hsf]
      dsimp only
      refine if_neg ?_
      rintro ⟨_, hlt, _, _⟩
      exact hn (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (by exact_mod_cast hlt.trans (Nat.le_ceil _))))
  have hprodval : (∏ i, (if i = m then (1 : ℝ) else S)) = S ^ (k - 1) := by
    have hconst : (∏ i ∈ Finset.univ.erase m, (if i = m then (1 : ℝ) else S)) =
        ∏ i ∈ Finset.univ.erase m, S :=
      Finset.prod_congr rfl fun i hi ↦ if_neg (Finset.ne_of_mem_erase hi)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ m), if_pos rfl, mul_one, hconst,
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ,
      Fintype.card_fin]
  calc (∑' r, F r) = ∑ r ∈ B, F r := htsum_eq
    _ = ∏ i, (∑ j ∈ Finset.range (⌈R⌉₊ + 1), gf i j) := hBsum
    _ = ∏ i, (if i = m then (1 : ℝ) else S) := Finset.prod_congr rfl fun i _ ↦ hfac i
    _ = S ^ (k - 1) := hprodval
    _ ≤ (Cg * L) ^ (k - 1) := pow_le_pow_left₀ hS0 hSle (k - 1)
    _ = Cg ^ (k - 1) * L ^ (k - 1) := mul_pow Cg L (k - 1)

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Replacing `ym m l r` by `yInverseSum l m r` in the `g`-weighted second moment costs at most
`C * Fmax F ^ 2 * φ(W) ^ (k + 1) * (log R) ^ (k + 1) / (W ^ (k + 1) * D₀ N)`. -/
@[pg_tag "bg246" "lem_S2m_second_moment"]
theorem lem_S2m_second_moment {k : ℕ} (hk : 2 ≤ k) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H : Finset ℕ), H.Admissible → #H = k →
      ∀ (θ δ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 → 0 < δ → δ < θ / 2 →
      ∀ (F : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F → Function.support F ⊆ 𝓡 k →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (l : (Fin k → ℕ) →₀ ℝ), l.HasPermissibleSupport ⌊R⌋₊ (W N) →
          (PrimeGaps.lToY l).maxRealAbs ≤ MaynardSmoothY.Fmax F →
        ∀ (m : Fin k),
          |(∑' r : Fin k → ℕ, if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) then
                (PrimeGaps.ym m l r) ^ 2 / (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ))
              else 0) - (∑' r : Fin k → ℕ,
              if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) then
                (yInverseSum l m r) ^ 2 / (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ))
              else 0)| ≤ C * (MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ (k + 1) *
              (Real.log (R)) ^ (k + 1) /
              ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  obtain ⟨C_A, hC_A, hA⟩ := MaynardSmoothY.exists_abs_ym_sub_yInverseSum_le (k := k)
  obtain ⟨C_B, hC_B, hB⟩ := (yInverseSum_triangle_bound (k := k))
  obtain ⟨C_C, hC_C, hC⟩ := lem_S2m_tuple_g_mass_cutoff
  refine ⟨C_A * (4 * C_B + 2 + C_A) * C_C, ?_, ?_⟩
  · have h2 : (0 : ℝ) ≤ 4 * C_B + 2 + C_A := by nlinarith [hC_A, hC_B.le]
    exact mul_nonneg (mul_nonneg hC_A h2) hC_C
  intro H hH hHcard θ δ hθ hδ hδθ F hF hFsupp
  obtain ⟨N₀, hAbody⟩ := hA H hH hHcard θ δ hθ hδ hδθ F hF hFsupp
  have hexp : 0 < θ / 2 - δ := by linarith
  obtain ⟨N₁, _, hN₁⟩ := PrimeGaps.MaynardOffDiagonal.primorial_D0_primeFactors_le_Rval θ δ hexp
  have hev := R_eventually_ge θ δ hδθ (rexp 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₂, hN₂⟩ := hev
  refine ⟨max N₀ (max N₁ (max (N₂ : ℝ) (rexp (rexp (rexp 2))))), ?_⟩
  intro N hN l hSS hyMax m
  have hN₀ : N₀ ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hNN₁ : N₁ ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN₂ : (N₂ : ℝ) ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNN₂' : N₂ ≤ N := by exact_mod_cast hNN₂
  have hND0 : rexp (rexp (rexp 2)) ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hD0_2 : (2 : ℝ) ≤ PrimeGaps.D₀ (N : ℝ) :=
    PrimeGaps.MaynardOffDiagonal.two_le_D0_of_large hND0
  have hD0_pos : 0 < PrimeGaps.D₀ (N : ℝ) := by linarith
  have hD0_1 : (1 : ℝ) ≤ PrimeGaps.D₀ (N : ℝ) := by linarith
  set Wr : ℝ := (W N : ℝ) with hW
  set φW : ℝ := ((W N).totient : ℝ) with hφW
  set Fm : ℝ := MaynardSmoothY.Fmax F with hFm
  set M₀ : ℝ := Fm * φW * Real.log R / Wr with hM₀
  set M : ℝ := (2 * C_B + 1) * M₀ with hM
  set ε : ℝ := MaynardSmoothY.errorSize R (W N) F N with hε
  set A₁ : ℝ := (∑' r : Fin k → ℕ, if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) then
        (PrimeGaps.ym m l r) ^ 2 / (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ))
      else 0) with hA₁
  set A₂ : ℝ := (∑' r : Fin k → ℕ, if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) then
        (yInverseSum l m r) ^ 2 / (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ))
      else 0) with hA₂
  have hFm0 : 0 ≤ Fm := by rw [hFm]; exact MaynardSmoothY.Fmax_nonneg F hF
  have hφW0 : 0 ≤ φW := by rw [hφW]; positivity
  have hW0 : 0 < Wr := by rw [hW]; exact_mod_cast (primorial_pos _)
  have hCB0 : 0 ≤ C_B := le_of_lt hC_B
  have hpf : ∀ p ∈ (W N).primeFactors, (p : ℝ) ≤ R := hN₁ (N : ℝ) hNN₁
  have hRexp : Real.exp 1 ≤ R := hN₂ N hNN₂'
  have hR1 : (1 : ℝ) < R :=
    lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) (Real.add_one_le_exp 1)) hRexp
  have hceil1 : 1 < ⌈R⌉₊ := Nat.lt_ceil.mpr (by rw [Nat.cast_one]; exact hR1)
  have hlogR1 : (1 : ℝ) ≤ Real.log R := by
    simpa using Real.log_le_log (Real.exp_pos 1) hRexp
  have hM₀0 : 0 ≤ M₀ := by
    rw [hM₀]; positivity
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (by linarith) hM₀0
  have hεM₀ : ε = M₀ / PrimeGaps.D₀ (N : ℝ) := by
    have hεeq : ε = Fm * φW * Real.log R / (Wr * PrimeGaps.D₀ (N : ℝ)) := by rw [hε]; rfl
    rw [hεeq, hM₀, div_div]
  have hε0 : 0 ≤ ε := by rw [hεM₀]; exact div_nonneg hM₀0 (le_of_lt hD0_pos)
  have hεM₀le : ε ≤ M₀ := by
    rw [hεM₀]
    exact div_le_self hM₀0 hD0_1
  have hCAε0 : 0 ≤ C_A * ε := mul_nonneg hC_A hε0
  have hδpt : ∀ r : Fin k → ℕ, r m = 1 → (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) →
      |(PrimeGaps.ym m l r) - yInverseSum l m r| ≤ C_A * ε := by
    intro r hrm _
    by_cases hsqf : ∀ i, Squarefree (r i)
    · rw [hε]; exact hAbody N hN₀ l hSS hyMax m r hrm hsqf
    · push Not at hsqf
      obtain ⟨i₀, hi₀⟩ := hsqf
      have him : i₀ ≠ m := by
        rintro rfl
        exact hi₀ (by rw [hrm]; exact squarefree_one)
      obtain ⟨hym0, hY0⟩ := ym_eq_zero_and_yInverseSum_eq_zero_of_not_squarefree m l r him hi₀
      rw [hym0, hY0]
      simpa using hCAε0
  have hYpt : ∀ r : Fin k → ℕ, |yInverseSum l m r| ≤ M := by
    intro r
    have hbb : |yInverseSum l m r| ≤ C_B * (PrimeGaps.lToY l).maxRealAbs * φW * (Real.log R + 1) /
      Wr :=
      hB R (W N) l hSS m r PrimeGaps.W_pos hpf hR1.le
    refine le_trans hbb ?_
    have hstep1 : C_B * (PrimeGaps.lToY l).maxRealAbs * φW * (Real.log R + 1) / Wr ≤
        C_B * Fm * φW * (Real.log R + 1) / Wr := by gcongr
    refine le_trans hstep1 ?_
    have hMeq : M = (2 * C_B + 1) * Fm * φW * Real.log R / Wr := by rw [hM, hM₀]; ring
    rw [hMeq, div_le_div_iff_of_pos_right hW0]
    linarith only [mul_nonneg (mul_nonneg (mul_nonneg hFm0 hφW0)
        (by linarith only [hCB0] : (0 : ℝ) ≤ C_B + 1))
        (by linarith only [hlogR1] : (0 : ℝ) ≤ Real.log R - 1),
      mul_nonneg hFm0 hφW0]
  have hympt : ∀ r : Fin k → ℕ, r m = 1 → (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) →
      |PrimeGaps.ym m l r| ≤ M + C_A * ε := by
    intro r hrm hrdiag
    calc |PrimeGaps.ym m l r|
        = |yInverseSum l m r + (PrimeGaps.ym m l r - yInverseSum l m r)| := by ring_nf
      _ ≤ |yInverseSum l m r| + |PrimeGaps.ym m l r - yInverseSum l m r| := abs_add_le _ _
      _ ≤ M + C_A * ε := add_le_add (hYpt r) (hδpt r hrm hrdiag)
  have hsqpt : ∀ r : Fin k → ℕ, r m = 1 → (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) →
      |(PrimeGaps.ym m l r) ^ 2 - (yInverseSum l m r) ^ 2| ≤ (C_A * ε) * (2 * M + C_A * ε) := by
    intro r hrm hrdiag
    have h1 : |(PrimeGaps.ym m l r) - yInverseSum l m r| ≤ C_A * ε := hδpt r hrm hrdiag
    have h2 : |(PrimeGaps.ym m l r) + yInverseSum l m r| ≤ 2 * M + C_A * ε :=
      calc |(PrimeGaps.ym m l r) + yInverseSum l m r|
          ≤ |PrimeGaps.ym m l r| + |yInverseSum l m r| := abs_add_le _ _
        _ ≤ (M + C_A * ε) + M := add_le_add (hympt r hrm hrdiag) (hYpt r)
        _ = 2 * M + C_A * ε := by ring
    rw [sq_sub_sq, abs_mul, mul_comm (C_A * ε) (2 * M + C_A * ε)]
    exact mul_le_mul h2 h1 (abs_nonneg _) (le_trans (abs_nonneg _) h2)
  obtain ⟨hKsum, hKbound⟩ := hC m R (W N) PrimeGaps.W_squarefree PrimeGaps.W_pos hpf hRexp
  set P : (Fin k → ℕ) → Prop :=
    fun r ↦ r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) with hP
  set Pcut : (Fin k → ℕ) → Prop := fun r ↦ r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i : ℝ) ≤ R ∧
      (r i).Coprime (W N) ∧ Squarefree (r i)) with hPcut
  set G : (Fin k → ℕ) → ℝ := fun r ↦ ∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ) with hG
  set Kf : (Fin k → ℕ) → ℝ := fun r ↦ if Pcut r then (1 : ℝ) / G r else 0 with hKf
  set f₁ : (Fin k → ℕ) → ℝ := fun r ↦ if P r then (PrimeGaps.ym m l r) ^ 2 / G r else 0 with hf₁
  set f₂ : (Fin k → ℕ) → ℝ := fun r ↦ if P r then (yInverseSum l m r) ^ 2 / G r else 0 with hf₂
  have hG0 : ∀ r, 0 ≤ G r := fun r ↦ Finset.prod_nonneg fun i _ ↦ by positivity
  have hKf0 : ∀ r, 0 ≤ Kf r := by
    intro r; rw [hKf]; dsimp only
    split
    · exact div_nonneg zero_le_one (hG0 r)
    · rfl
  have hvanish : ∀ r, P r → ¬ Pcut r → PrimeGaps.ym m l r = 0 ∧ yInverseSum l m r = 0 := by
    intro r hPr hnotcut
    rw [hPcut] at hnotcut
    simp only [hPr.1, true_and, not_forall] at hnotcut
    obtain ⟨i, hi, hbody⟩ := hnotcut
    obtain ⟨h1i, hcop⟩ := hPr.2 i hi
    have hfail : ¬ ((r i : ℝ) ≤ R ∧ Squarefree (r i)) := by
      intro ⟨hlt, hsq⟩
      exact hbody ⟨h1i, hlt, hcop, hsq⟩
    by_cases hlt : (r i : ℝ) ≤ R
    · exact ym_eq_zero_and_yInverseSum_eq_zero_of_not_squarefree m l r hi
        fun hsq ↦ hfail ⟨hlt, hsq⟩
    · exact ⟨ym_eq_zero_of_coord_ge hSS (not_le.mp hlt),
        yInverseSum_eq_zero_of_coord_ge hSS hi (not_le.mp hlt)⟩
  set Bc : ℝ := (C_A * ε) * (2 * M + C_A * ε) with hBc
  have hBc0 : 0 ≤ Bc := by
    rw [hBc]; apply mul_nonneg hCAε0; linarith only [hM0, hCAε0]
  have hdiffdom : ∀ r, |f₁ r - f₂ r| ≤ Bc * Kf r := by
    intro r
    by_cases hpr : P r
    · by_cases hcut : Pcut r
      · rw [hf₁, hf₂, hKf]; dsimp only
        simp only [if_pos hpr, if_pos hcut]
        rw [← sub_div, abs_div, abs_of_nonneg (hG0 r)]
        calc |(PrimeGaps.ym m l r) ^ 2 - (yInverseSum l m r) ^ 2| / G r ≤ Bc / G r := by
              apply div_le_div_of_nonneg_right _ (hG0 r)
              rw [hBc]; exact hsqpt r hpr.1 hpr.2
          _ = Bc * (1 / G r) := by rw [mul_one_div]
      · obtain ⟨hym0, hY0⟩ := hvanish r hpr hcut
        rw [hf₁, hf₂]; dsimp only
        simp only [if_pos hpr, hym0, hY0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, zero_div, sub_zero, abs_zero]
        exact mul_nonneg hBc0 (hKf0 r)
    · rw [hf₁, hf₂]; dsimp only
      simpa only [if_neg hpr, sub_zero, abs_zero] using mul_nonneg hBc0 (hKf0 r)
  have hsummable : ∀ y : (Fin k → ℕ) → ℝ, (∀ r, P r → ¬ Pcut r → y r = 0) →
      Summable (fun r ↦ if P r then y r ^ 2 / G r else 0) := by
    intro y hy
    apply summable_of_ne_finset_zero
      (s := Fintype.piFinset (fun _ : Fin k ↦ Finset.range (⌈R⌉₊ + 1)))
    intro r hr
    by_contra hne
    have hPr : P r := by by_contra hp; rw [if_neg hp] at hne; exact hne rfl
    rw [if_pos hPr] at hne
    have hPcutr : Pcut r := by
      by_contra hpc
      rw [hy r hPr hpc] at hne
      simp at hne
    apply hr
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    simp only [hPcut] at hPcutr
    by_cases hi : i = m
    · subst hi
      rw [hPcutr.1]
      exact Nat.lt_succ_of_lt hceil1
    · exact Nat.lt_succ_of_le
        (by exact_mod_cast (hPcutr.2 i hi).2.1.trans (Nat.le_ceil _))
  have hsummf₁ : Summable f₁ :=
    hsummable (fun r ↦ PrimeGaps.ym m l r) (fun r hPr hpc ↦ (hvanish r hPr hpc).1)
  have hsummf₂ : Summable f₂ :=
    hsummable (fun r ↦ yInverseSum l m r) (fun r hPr hpc ↦ (hvanish r hPr hpc).2)
  have hsummBK : Summable (fun r ↦ Bc * Kf r) := hKsum.mul_left Bc
  have hsummabsd : Summable (fun r ↦ |f₁ r - f₂ r|) :=
    Summable.of_nonneg_of_le (fun r ↦ abs_nonneg _) hdiffdom hsummBK
  have hAdiff : A₁ - A₂ = ∑' r, (f₁ r - f₂ r) := by
    rw [hA₁, hA₂, Summable.tsum_sub hsummf₁ hsummf₂]
  have habs1 : |A₁ - A₂| ≤ ∑' r, |f₁ r - f₂ r| := by
    rw [hAdiff]
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun r ↦ f₁ r - f₂ r)
      (by simpa [Real.norm_eq_abs] using hsummabsd)
  have habs2 : (∑' r, |f₁ r - f₂ r|) ≤ ∑' r, Bc * Kf r :=
    Summable.tsum_le_tsum hdiffdom hsummabsd hsummBK
  have habs3 : (∑' r, Bc * Kf r) = Bc * ∑' r, Kf r := tsum_mul_left
  have hKtsum : (∑' r, Kf r) ≤ C_C * (φW * Real.log R / Wr) ^ (k - 1) := by
    rw [hKf]; exact hKbound
  have hBcbound : Bc ≤ C_A * (4 * C_B + 2 + C_A) * M₀ ^ 2 / PrimeGaps.D₀ (N : ℝ) := by
    rw [hBc]
    have hfac2 : 2 * M + C_A * ε ≤ (4 * C_B + 2 + C_A) * M₀ := by
      rw [hM]
      linarith only [mul_le_mul_of_nonneg_left hεM₀le hC_A]
    have hCAεeq : C_A * ε = C_A * M₀ / PrimeGaps.D₀ (N : ℝ) := by
      rw [hεM₀]; ring
    have h2Mnn : 0 ≤ 2 * M + C_A * ε := by linarith only [hM0, hCAε0]
    have hDMnn : 0 ≤ C_A * M₀ / PrimeGaps.D₀ (N : ℝ) :=
      div_nonneg (mul_nonneg hC_A hM₀0) (le_of_lt hD0_pos)
    have hstep : C_A * ε * (2 * M + C_A * ε) ≤
        (C_A * M₀ / PrimeGaps.D₀ (N : ℝ)) * ((4 * C_B + 2 + C_A) * M₀) :=
      mul_le_mul (le_of_eq hCAεeq) hfac2 h2Mnn hDMnn
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  have hLid : M₀ ^ 2 * (φW * Real.log R / Wr) ^ (k - 1) =
      Fm ^ 2 * φW ^ (k + 1) * Real.log R ^ (k + 1) / Wr ^ (k + 1) := by
    have eφ : φW ^ (k + 1) = φW ^ 2 * φW ^ (k - 1) := by rw [← pow_add]; congr 1; omega
    have eL : Real.log R ^ (k + 1) = Real.log R ^ 2 * Real.log R ^ (k - 1) := by
      rw [← pow_add]; congr 1; omega
    have eW : Wr ^ (k + 1) = Wr ^ 2 * Wr ^ (k - 1) := by rw [← pow_add]; congr 1; omega
    rw [hM₀, div_pow, mul_pow, mul_pow, div_pow, mul_pow, eφ, eL, eW]
    field_simp
  calc |A₁ - A₂| ≤ ∑' r, |f₁ r - f₂ r| := habs1
    _ ≤ ∑' r, Bc * Kf r := habs2
    _ = Bc * ∑' r, Kf r := habs3
    _ ≤ Bc * (C_C * (φW * Real.log R / Wr) ^ (k - 1)) := mul_le_mul_of_nonneg_left hKtsum hBc0
    _ ≤ (C_A * (4 * C_B + 2 + C_A) * M₀ ^ 2 / PrimeGaps.D₀ (N : ℝ)) *
          (C_C * (φW * Real.log R / Wr) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_right hBcbound (mul_nonneg hC_C (by positivity))
    _ = C_A * (4 * C_B + 2 + C_A) * C_C *
          (M₀ ^ 2 * (φW * Real.log R / Wr) ^ (k - 1)) / PrimeGaps.D₀ (N : ℝ) := by
        ring
    _ = C_A * (4 * C_B + 2 + C_A) * C_C *
          (Fm ^ 2 * φW ^ (k + 1) * Real.log R ^ (k + 1) / Wr ^ (k + 1)) /
            PrimeGaps.D₀ (N : ℝ) := by
        rw [hLid]
    _ = C_A * (4 * C_B + 2 + C_A) * C_C * Fm ^ 2 * φW ^ (k + 1) *
          Real.log R ^ (k + 1) / (Wr ^ (k + 1) * PrimeGaps.D₀ ↑N) := by
        field_simp

end PrimeGaps
