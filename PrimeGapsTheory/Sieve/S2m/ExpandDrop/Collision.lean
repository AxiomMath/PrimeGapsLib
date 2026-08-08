/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.ExpandDrop.GSumBounds

/-!
# Collision mass

The collision mass and the prime-divisibility bounds controlling it.

## Main results

* `PrimeGaps.failureMass_eq_collision_mass`
* `PrimeGaps.gsum_dvd_prime_le`, `PrimeGaps.phisum_dvd_prime_le`
* `PrimeGaps.collisionMass`
* `PrimeGaps.failureMass_le_collision_majorant`
* `PrimeGaps.tsum_aSumP_le`, `PrimeGaps.tsum_cSumP_le`
* `PrimeGaps.tsum_bSumP_le`, `PrimeGaps.tsum_bSumPP_le`
* `PrimeGaps.tsum_ite_dvd_mul_and_le`
-/

@[expose] public section

open scoped Finset

open scoped ArithmeticFunction.detotient
open PrimeGaps

/-- `failureMass` as the triple sum of `|S2mDecTerm|` over the terms passing the base guard but
failing the coprimality coupling. -/
theorem PrimeGaps.failureMass_eq_collision_mass {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) :
    failureMass R W F m = ∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ),
          (if ((ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧ Squarefree u ∧ Squarefree u' ∧
                (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i))) ∧
              ¬((∀ i, i ≠ m → (u * u').Coprime (ρ i)) ∧ (∀ i j, i ≠ j → (ρ i).Coprime (ρ j))))
            then |S2mDecTerm R W F m ρ u u'| else 0) := by
  rw [failureMass_eq_triple R W F m]
  exact tsum_congr fun u ↦ tsum_congr fun u' ↦ tsum_congr fun ρ ↦ abs_diff_eq R W F m ρ u u'

/-- For squarefree `n` and a prime `p ∣ n`, the cofactor `n / p` is again coprime to `p`:
otherwise `p ^ 2` would divide `n`. -/
private lemma coprime_div_self_of_squarefree {n p : ℕ} (hp : p.Prime) (hsqf : Squarefree n)
    (hpdvd : p ∣ n) : Nat.Coprime p (n / p) := by
  rw [hp.coprime_iff_not_dvd]
  exact fun hpb ↦ hp.ne_one <| Nat.isUnit_iff.mp <| hsqf p <|
    Nat.mul_div_cancel' hpdvd ▸ Nat.mul_dvd_mul_left p hpb

/-- Division by `p` maps the multiples of `p` in the squarefree box `[1, M]` coprime to `W`
injectively into that box, so a nonnegative weight sums to no more over the cofactors than over
the whole box. -/
private lemma sum_div_prime_le_sum_of_nonneg (W M p : ℕ) (hppos : 0 < p) (w : ℕ → ℝ)
    (hw : ∀ b, 0 ≤ w b) :
    ∑ n ∈ {n ∈ (Finset.Icc 1 M) | Squarefree n ∧ n.Coprime W ∧ p ∣ n}, w (n / p) ≤
      ∑ b ∈ {n ∈ (Finset.Icc 1 M) | Squarefree n ∧ n.Coprime W}, w b := by
  rw [← Finset.sum_image (show Set.InjOn (· / p)
      ↑{n ∈ (Finset.Icc 1 M) | Squarefree n ∧ n.Coprime W ∧ p ∣ n} from
    fun a ha b hb hab ↦ by
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      have h : a / p = b / p := hab
      rw [← Nat.mul_div_cancel' ha.2.2.2, ← Nat.mul_div_cancel' hb.2.2.2, h])]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb ↦ ?_) fun b _ _ ↦ hw b
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnM⟩, hsqf, hcopW, hpdvd⟩ := hn
  have hdvd' : (n / p) ∣ n := Nat.div_dvd_of_dvd hpdvd
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.div_pos (Nat.le_of_dvd hn1 hpdvd) hppos, (Nat.div_le_self n p).trans hnM⟩,
    hsqf.squarefree_of_dvd hdvd', hcopW.of_dvd_left hdvd'⟩

/-- `∑_{n ≤ M, p ∣ n} 1 / g n ≤ (1 / (p - 2)) * ∑_{n ≤ M} 1 / g n` for a prime `p ≥ 3`, both sums
over squarefree `n` coprime to `W`. -/
theorem PrimeGaps.gsum_dvd_prime_le (W : ℕ) (M : ℕ) (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    ∑ n ∈ Finset.Icc 1 M,
        (if Squarefree n ∧ n.Coprime W ∧ p ∣ n then 1 / (g n : ℝ) else 0) ≤ (1 / ((p : ℝ) - 2)) *
        ∑ n ∈ Finset.Icc 1 M,
          (if Squarefree n ∧ n.Coprime W then 1 / (g n : ℝ) else 0) := by
  have hp2R' : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    linarith
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hval : ∀ n ∈ {n ∈ (Finset.Icc 1 M) | Squarefree n ∧ n.Coprime W ∧ p ∣ n},
      1 / (g n : ℝ) = (1 / ((p : ℝ) - 2)) * (1 / (g (n / p) : ℝ)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, _⟩, hsqf, _, hpdvd⟩ := hn
    have hcop : Nat.Coprime p (n / p) := coprime_div_self_of_squarefree hp hsqf hpdvd
    have hpf : (n / p).primeFactors = n.primeFactors.erase p := by
      have hprod := Nat.Coprime.primeFactors_mul hcop
      rw [Nat.mul_div_cancel' hpdvd, hp.primeFactors, Finset.singleton_union] at hprod
      rw [hprod, Finset.erase_insert fun h ↦ hp.coprime_iff_not_dvd.mp hcop
        (Nat.dvd_of_mem_primeFactors h)]
    have hgn : (g n : ℝ) = ((p : ℝ) - 2) * (g (n / p) : ℝ) := by
      rw [ArithmeticFunction.coe_detotient_squarefree_eq_prod (R := ℝ) hsqf,
        ArithmeticFunction.coe_detotient_squarefree_eq_prod (R := ℝ)
          (hsqf.squarefree_of_dvd (Nat.div_dvd_of_dvd hpdvd)), hpf,
        ← Finset.mul_prod_erase n.primeFactors (fun q ↦ ((q : ℝ) - 2))
          (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by omega⟩)]
    rw [hgn, one_div_mul_one_div]
  rw [Finset.sum_congr rfl hval, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_div_prime_le_sum_of_nonneg W M p hp.pos (fun b ↦ 1 / (g b : ℝ)) fun b ↦ by positivity)
    (one_div_nonneg.mpr hp2R'.le)

/-- `∑' u, ∑' u', ∑' ρ, aSum u * aSum u' * bSum ρ` over the triples on which the coprimality
coupling fails. -/
noncomputable def PrimeGaps.collisionMass {k : ℕ} (W : ℕ) (X : ℝ) (m : Fin k) : ℝ :=
  ∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ),
    (if ¬((∀ i, i ≠ m → (u * u').Coprime (ρ i)) ∧ (∀ i j, i ≠ j → (ρ i).Coprime (ρ j)))
      then PrimeGaps.aSum W X u * PrimeGaps.aSum W X u' * PrimeGaps.bSum W X m ρ else 0)

/-- `failureMass R W F m ≤ Fmax F ^ 2 * collisionMass W R m`. -/
theorem PrimeGaps.failureMass_le_collision_majorant {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k)
    (hR : 1 < R) (m : Fin k) :
    failureMass R W F m ≤ MaynardSmoothY.Fmax F ^ 2 * PrimeGaps.collisionMass W R m := by
  set Coup : ℕ × ℕ × (Fin k → ℕ) → Prop := fun p ↦
    (∀ i, i ≠ m → (p.1 * p.2.1).Coprime (p.2.2 i)) ∧ ∀ i j, i ≠ j → (p.2.2 i).Coprime (p.2.2 j)
  set Guard : ℕ × ℕ × (Fin k → ℕ) → Prop := fun p ↦ p.2.2 m = 1 ∧ p.1.Coprime W ∧
    p.2.1.Coprime W ∧ Squarefree p.1 ∧ Squarefree p.2.1 ∧
      ∀ i, i ≠ m → (p.2.2 i).Coprime W ∧ Squarefree (p.2.2 i)
  set D' : ℕ × ℕ × (Fin k → ℕ) → ℝ :=
    fun p ↦ if Guard p ∧ ¬Coup p then |S2mDecTerm R W F m p.2.2 p.1 p.2.1| else 0 with hD'
  set E' : ℕ × ℕ × (Fin k → ℕ) → ℝ := fun p ↦ if ¬Coup p then
        MaynardSmoothY.Fmax F ^ 2 * PrimeGaps.aSum W R p.1 *
          PrimeGaps.aSum W R p.2.1 * PrimeGaps.bSum W R m p.2.2 else 0 with hE'
  have hDfin0 : (Function.support (fun p : ℕ × ℕ × (Fin k → ℕ) ↦
      S2mDecTerm R W F m p.2.2 p.1 p.2.1)).Finite :=
    PrimeGaps.S2mDecTerm_flat_support_finite R W hR F hsupp m
  have hDfin : (Function.support D').Finite := by
    refine hDfin0.subset fun p hp hz ↦ hp ?_
    simp only [hD']; split <;> simp [hz]
  have hEfin0 : (Function.support (fun p : ℕ × ℕ × (Fin k → ℕ) ↦
      MaynardSmoothY.Fmax F ^ 2 * PrimeGaps.aSum W R p.1 *
        PrimeGaps.aSum W R p.2.1 * PrimeGaps.bSum W R m p.2.2)).Finite :=
    PrimeGaps.prod_flat_support_finite W R (MaynardSmoothY.Fmax F ^ 2) m
  have hEfin : (Function.support E').Finite := by
    refine hEfin0.subset fun p hp hz ↦ hp ?_
    simp only [hE']; split <;> simp [hz]
  have hDsum : Summable D' := summable_of_hasFiniteSupport hDfin
  have hEsum : Summable E' := summable_of_hasFiniteSupport hEfin
  have hpoint : ∀ p, D' p ≤ E' p := by
    intro p
    simp only [hD', hE']
    by_cases hc : Coup p
    · rw [if_neg (by simp [hc]), if_neg (by simp [hc])]
    · rw [if_pos hc]
      by_cases hg : Guard p
      · rw [if_pos ⟨hg, hc⟩]
        exact PrimeGaps.abs_S2mDecTerm_le_prod R W F hF hsupp hR m p.2.2 p.1 p.2.1
      · rw [if_neg (by tauto)]
        exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (PrimeGaps.aSum_nonneg W R p.1))
          (PrimeGaps.aSum_nonneg W R p.2.1)) (PrimeGaps.bSum_nonneg W R m p.2.2)
  have hLHS : failureMass R W F m = ∑' p, D' p := by
    rw [PrimeGaps.failureMass_eq_collision_mass R W F m]
    exact PrimeGaps.triple_tsum_eq_prod
      (fun ρ u u' ↦ if ((ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧ Squarefree u ∧ Squarefree u' ∧
            (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i))) ∧
          ¬((∀ i, i ≠ m → (u * u').Coprime (ρ i)) ∧ (∀ i j, i ≠ j → (ρ i).Coprime (ρ j))))
        then |S2mDecTerm R W F m ρ u u'| else 0) hDfin
  have hRHS : MaynardSmoothY.Fmax F ^ 2 * PrimeGaps.collisionMass W R m = ∑' p, E' p := by
    rw [PrimeGaps.collisionMass, PrimeGaps.triple_tsum_eq_prod
      (fun ρ u u' ↦ if ¬((∀ i, i ≠ m → (u * u').Coprime (ρ i)) ∧
                    (∀ i j, i ≠ j → (ρ i).Coprime (ρ j)))
                then MaynardSmoothY.Fmax F ^ 2 * PrimeGaps.aSum W R u *
                      PrimeGaps.aSum W R u' * PrimeGaps.bSum W R m ρ
                else 0) hEfin |>.symm]
    rw [← tsum_mul_left]; refine tsum_congr fun u ↦ ?_
    rw [← tsum_mul_left]; refine tsum_congr fun u' ↦ ?_
    rw [← tsum_mul_left]; refine tsum_congr fun ρ ↦ ?_
    split_ifs <;> ring
  rw [hLHS, hRHS]
  exact Summable.tsum_le_tsum hpoint hDsum hEsum

/-- `∑_{n ≤ M, p ∣ n} 1 / φ n ≤ (1 / (p - 2)) * ∑_{n ≤ M} 1 / φ n` for a prime `p ≥ 3`, both sums
over squarefree `n` coprime to `W`. -/
theorem PrimeGaps.phisum_dvd_prime_le (W : ℕ) (M : ℕ) (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    ∑ n ∈ Finset.Icc 1 M, (if Squarefree n ∧ n.Coprime W ∧ p ∣ n then 1 / (n.totient : ℝ) else 0) ≤
      (1 / ((p : ℝ) - 2)) * ∑ n ∈ Finset.Icc 1 M,
          (if Squarefree n ∧ n.Coprime W then 1 / (n.totient : ℝ) else 0) := by
  have hp2R' : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    linarith
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hval : ∀ n ∈ {n ∈ (Finset.Icc 1 M) | Squarefree n ∧ n.Coprime W ∧ p ∣ n},
      1 / (n.totient : ℝ) = (1 / ((p : ℝ) - 1)) * (1 / ((n / p).totient : ℝ)) := by
    intro n hn
    obtain ⟨-, hsqf, -, hpdvd⟩ := Finset.mem_filter.mp hn
    have hcop : Nat.Coprime p (n / p) := coprime_div_self_of_squarefree hp hsqf hpdvd
    have htot : n.totient = (p - 1) * (n / p).totient := by
      conv_lhs => rw [← Nat.mul_div_cancel' hpdvd]
      rw [Nat.totient_mul hcop, Nat.totient_prime hp]
    rw [htot, one_div_mul_one_div]
    push_cast [Nat.cast_sub hp.pos]
    ring
  rw [Finset.sum_congr rfl hval, ← Finset.mul_sum]
  have hnonneg : ∀ b : ℕ, (0 : ℝ) ≤ 1 / (b.totient : ℝ) := fun b ↦ by positivity
  exact mul_le_mul (one_div_le_one_div_of_le hp2R' (by linarith))
    (sum_div_prime_le_sum_of_nonneg W M p hp.pos (fun b ↦ 1 / (b.totient : ℝ)) hnonneg)
    (Finset.sum_nonneg fun n _ ↦ hnonneg _) (one_div_nonneg.mpr hp2R'.le)

open scoped PrimeGaps.sieveModulus in
/-- `⌊D₀ N⌋ < p` for a prime `p` coprime to `W N`, the modulus being the primorial of `⌊D₀ N⌋`. -/
theorem PrimeGaps.floor_D0_lt_of_prime_coprime (N p : ℕ) (hp : p.Prime)
    (hcop : p.Coprime (W N)) : ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < p :=
  (Nat.floor_lt' hp.pos.ne').mpr
    (PrimeGaps.primeFactor_large (N : ℝ) p p (PrimeGaps.W_eq_primorial_D₀ ▸ hcop) hp dvd_rfl)

/-- A weight vanishing off the squarefree `n ≤ X` coprime to `W`, summed over the multiples of `p`,
is the sum over `Icc 1 ⌊X⌋₊` with `p ∣ n` added to the guard. -/
theorem PrimeGaps.tsum_guard_dvd_eq (W : ℕ) (X : ℝ) (p : ℕ) (f : ℕ → ℝ) :
    (∑' n : ℕ, if p ∣ n then
        (if Squarefree n ∧ n.Coprime W ∧ n ≤ ⌊X⌋₊ then f n else 0) else 0) =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (if Squarefree n ∧ n.Coprime W ∧ p ∣ n then f n else 0) := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊X⌋₊)]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [Finset.mem_Icc] at hn
    split_ifs <;> tauto
  · intro n hn
    rw [Finset.mem_Icc, not_and_or] at hn
    rw [if_neg (fun h : Squarefree n ∧ n.Coprime W ∧ n ≤ ⌊X⌋₊ ↦
      hn.elim (fun h1 ↦ h1 h.1.ne_zero.bot_lt) (fun h2 ↦ h2 h.2.2)), ite_self]

/-- `∑' n, (if p ∣ n then aSum W X n else 0) ≤ (1 / (p - 2)) * sumA W X` for a prime `p ≥ 3`. -/
theorem PrimeGaps.tsum_aSumP_le (W : ℕ) (X : ℝ) (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∑' n : ℕ, if p ∣ n then PrimeGaps.aSum W X n else 0) ≤
      (1 / ((p : ℝ) - 2)) * PrimeGaps.MaynardOffDiagonal.sumA W X := by
  simp only [PrimeGaps.aSum]
  rw [PrimeGaps.tsum_guard_dvd_eq W X p fun n ↦ 1 / (n.totient : ℝ), PrimeGaps.sumA_eq_ite_sum]
  exact PrimeGaps.phisum_dvd_prime_le W ⌊X⌋₊ p hp hp3

/-- `∑' n, (if p ∣ n then cSum W X n else 0) ≤ (1 / (p - 2)) * gSum W X` for a prime `p ≥ 3`. -/
theorem PrimeGaps.tsum_cSumP_le (W : ℕ) (X : ℝ) (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∑' n : ℕ, if p ∣ n then PrimeGaps.cSum W X n else 0) ≤
      (1 / ((p : ℝ) - 2)) * PrimeGaps.gSum W X := by
  simp only [PrimeGaps.cSum]
  rw [PrimeGaps.tsum_guard_dvd_eq W X p fun n ↦ 1 / (g n : ℝ), PrimeGaps.gSum]
  exact PrimeGaps.gsum_dvd_prime_le W ⌊X⌋₊ p hp hp3

/-- `∑' ρ, (if p ∣ ρ i then bSum W X m ρ else 0) ≤ (1 / (p - 2)) * (gSum W X) ^ (k - 1)` for
`i ≠ m` and a prime `p ≥ 3`. -/
theorem PrimeGaps.tsum_bSumP_le {k : ℕ} (hk : 2 ≤ k) (W : ℕ) (X : ℝ) (m i : Fin k) (hi : i ≠ m)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∑' ρ : Fin k → ℕ, if p ∣ ρ i then PrimeGaps.bSum W X m ρ else 0) ≤
      (1 / ((p : ℝ) - 2)) * (PrimeGaps.gSum W X) ^ (k - 1) := by
  have hgSum_nonneg : (0 : ℝ) ≤ PrimeGaps.gSum W X := PrimeGaps.gSum_nonneg W X
  have hi' : i ∈ Finset.univ.erase m := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
  set coordWeight : Fin k → ℕ → ℝ := fun j n ↦
    if j = i then (if p ∣ n then PrimeGaps.cSum W X n else 0) else PrimeGaps.cSum W X n with hg
  have hsupp : ∀ (j : Fin k) (n : ℕ), coordWeight j n ≠ 0 → n ≤ ⌊X⌋₊ := by
    intro j n hne
    have hcne : PrimeGaps.cSum W X n ≠ 0 := by
      simp only [hg] at hne
      split_ifs at hne <;> first | exact hne | simp at hne
    simp only [PrimeGaps.cSum] at hcne
    split_ifs at hcne with hguard
    exacts [hguard.2.2, absurd rfl hcne]
  have hfactor : ∀ ρ : Fin k → ℕ,
      (∏ j ∈ Finset.univ.erase m, coordWeight j (ρ j)) = (if p ∣ ρ i then (1 : ℝ) else 0) *
          ∏ j ∈ Finset.univ.erase m, PrimeGaps.cSum W X (ρ j) := by
    intro ρ
    by_cases hpi : p ∣ ρ i
    · rw [if_pos hpi, one_mul]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      rcases eq_or_ne j i with rfl | hji
      · simp only [hg, if_pos rfl, if_pos hpi]
      · simp only [hg, if_neg hji]
    · rw [if_neg hpi, zero_mul]
      exact Finset.prod_eq_zero hi' (by simp only [hg, if_pos rfl, if_neg hpi])
  have hLHS_eq : ∀ ρ : Fin k → ℕ, (if p ∣ ρ i then PrimeGaps.bSum W X m ρ else 0) =
        (if ρ m = 1 then ∏ j ∈ Finset.univ.erase m, coordWeight j (ρ j) else 0) := by
    intro ρ
    rw [PrimeGaps.bSum, hfactor ρ]
    by_cases hm1 : ρ m = 1
    · rw [if_pos hm1, if_pos hm1]
      by_cases hpi : p ∣ ρ i <;> simp [hpi]
    · rw [if_neg hm1, if_neg hm1]; simp
  rw [tsum_congr hLHS_eq, tsum_pin_coord_prod ⌊X⌋₊ m coordWeight hsupp,
    ← Finset.prod_erase_mul (Finset.univ.erase m) (fun j ↦ ∑' n : ℕ, coordWeight j n) hi']
  have hother : ∀ j ∈ (Finset.univ.erase m).erase i,
      (∑' n : ℕ, coordWeight j n) = PrimeGaps.gSum W X := by
    intro j hj
    rw [show (fun n : ℕ ↦ coordWeight j n) = fun n : ℕ ↦ PrimeGaps.cSum W X n from
      funext fun n ↦ by simp only [hg, if_neg (Finset.mem_erase.mp hj).1],
      PrimeGaps.tsum_cSum_eq_gSum]
  rw [Finset.prod_congr rfl hother, Finset.prod_const,
    show #((Finset.univ.erase m).erase i) = k - 2 by
      rw [Finset.card_erase_of_mem hi', Finset.card_erase_of_mem (Finset.mem_univ m),
        Finset.card_univ, Fintype.card_fin]
      omega,
    show (∑' n : ℕ, coordWeight i n) = ∑' n : ℕ, if p ∣ n then PrimeGaps.cSum W X n else 0 from
      tsum_congr fun n ↦ by simp only [hg, if_pos rfl],
    show k - 1 = (k - 2) + 1 by omega, pow_succ]
  exact (mul_le_mul_of_nonneg_left (PrimeGaps.tsum_cSumP_le W X p hp hp3)
    (pow_nonneg hgSum_nonneg (k - 2))).trans_eq (by ring)

/-- `∑' ρ, (if p ∣ ρ i ∧ p ∣ ρ j then bSum W X m ρ else 0) ≤ (1 / (p - 2)) ^ 2 *
(gSum W X) ^ (k - 1)` for distinct `i, j ≠ m` and a prime `p ≥ 3`. -/
theorem PrimeGaps.tsum_bSumPP_le {k : ℕ} (hk : 2 ≤ k) (W : ℕ) (X : ℝ) (m i j : Fin k)
    (hi : i ≠ m) (hj : j ≠ m) (hij : i ≠ j)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∑' ρ : Fin k → ℕ, if p ∣ ρ i ∧ p ∣ ρ j then PrimeGaps.bSum W X m ρ else 0) ≤
      (1 / ((p : ℝ) - 2)) ^ 2 * (PrimeGaps.gSum W X) ^ (k - 1) := by
  have hk3 : 3 ≤ k := by
    by_contra hk3
    push Not at hk3
    interval_cases k
    fin_cases i <;> fin_cases j <;> fin_cases m <;> simp_all
  have hgSum_nonneg : (0 : ℝ) ≤ PrimeGaps.gSum W X := PrimeGaps.gSum_nonneg W X
  have hi' : i ∈ Finset.univ.erase m := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
  have hjm' : j ∈ Finset.univ.erase m := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
  have hj' : j ∈ (Finset.univ.erase m).erase i := Finset.mem_erase.mpr ⟨hij.symm, hjm'⟩
  set coordWeight : Fin k → ℕ → ℝ := fun l n ↦
    if l = i then (if p ∣ n then PrimeGaps.cSum W X n else 0)
    else if l = j then (if p ∣ n then PrimeGaps.cSum W X n else 0)
    else PrimeGaps.cSum W X n with hg
  have hsupp : ∀ (l : Fin k) (n : ℕ), coordWeight l n ≠ 0 → n ≤ ⌊X⌋₊ := by
    intro l n hne
    have hcne : PrimeGaps.cSum W X n ≠ 0 := by
      simp only [hg] at hne
      split_ifs at hne <;> first | exact hne | simp at hne
    simp only [PrimeGaps.cSum] at hcne
    split_ifs at hcne with hguard
    exacts [hguard.2.2, absurd rfl hcne]
  have hfactor : ∀ ρ : Fin k → ℕ,
      (∏ l ∈ Finset.univ.erase m, coordWeight l (ρ l)) =
        (if p ∣ ρ i ∧ p ∣ ρ j then (1 : ℝ) else 0) *
          ∏ l ∈ Finset.univ.erase m, PrimeGaps.cSum W X (ρ l) := by
    intro ρ
    by_cases hpij : p ∣ ρ i ∧ p ∣ ρ j
    · rw [if_pos hpij, one_mul]
      refine Finset.prod_congr rfl fun l _ ↦ ?_
      rcases eq_or_ne l i with rfl | hli
      · simp only [hg, if_true, if_pos hpij.1]
      · rcases eq_or_ne l j with rfl | hlj
        · simp only [hg, if_neg hli, if_true, if_pos hpij.2]
        · simp only [hg, if_neg hli, if_neg hlj]
    · rw [if_neg hpij, zero_mul]
      rw [not_and_or] at hpij
      rcases hpij with hni | hnj
      · exact Finset.prod_eq_zero hi' (by simp only [hg, if_true, if_neg hni])
      · exact Finset.prod_eq_zero hjm' (by simp only [hg, if_neg hij.symm, if_true, if_neg hnj])
  have hLHS_eq : ∀ ρ : Fin k → ℕ, (if p ∣ ρ i ∧ p ∣ ρ j then PrimeGaps.bSum W X m ρ else 0) =
        (if ρ m = 1 then ∏ l ∈ Finset.univ.erase m, coordWeight l (ρ l) else 0) := by
    intro ρ
    rw [PrimeGaps.bSum, hfactor ρ]
    by_cases hm1 : ρ m = 1
    · rw [if_pos hm1, if_pos hm1]
      by_cases hpij : p ∣ ρ i ∧ p ∣ ρ j <;> simp [hpij]
    · rw [if_neg hm1, if_neg hm1]; simp
  rw [tsum_congr hLHS_eq, tsum_pin_coord_prod ⌊X⌋₊ m coordWeight hsupp,
    ← Finset.prod_erase_mul (Finset.univ.erase m) (fun l ↦ ∑' n : ℕ, coordWeight l n) hi',
    ← Finset.prod_erase_mul ((Finset.univ.erase m).erase i)
      (fun l ↦ ∑' n : ℕ, coordWeight l n) hj']
  have hifac : (∑' n : ℕ, coordWeight i n) =
      ∑' n : ℕ, if p ∣ n then PrimeGaps.cSum W X n else 0 :=
    tsum_congr fun n ↦ by simp only [hg, if_true]
  have hjfac : (∑' n : ℕ, coordWeight j n) =
      ∑' n : ℕ, if p ∣ n then PrimeGaps.cSum W X n else 0 :=
    tsum_congr fun n ↦ by simp only [hg, if_neg hij.symm, if_true]
  have hother : ∀ l ∈ ((Finset.univ.erase m).erase i).erase j,
      (∑' n : ℕ, coordWeight l n) = PrimeGaps.gSum W X := by
    intro l hl
    rw [Finset.mem_erase] at hl
    rw [show (fun n : ℕ ↦ coordWeight l n) = fun n : ℕ ↦ PrimeGaps.cSum W X n from
      funext fun n ↦ by simp only [hg, if_neg (Finset.mem_erase.mp hl.2).1, if_neg hl.1],
      PrimeGaps.tsum_cSum_eq_gSum]
  rw [Finset.prod_congr rfl hother, Finset.prod_const, hjfac, hifac,
    show #(((Finset.univ.erase m).erase i).erase j) = k - 3 by
      rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi',
        Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
      omega,
    show k - 1 = (k - 3) + 2 by omega]
  have hiSum := PrimeGaps.tsum_cSumP_le W X p hp hp3
  have hcSumP_nonneg : (0 : ℝ) ≤ ∑' n : ℕ, if p ∣ n then PrimeGaps.cSum W X n else 0 :=
    tsum_nonneg fun n ↦ by rw [PrimeGaps.cSum]; split_ifs <;> positivity
  have hp2 : (0 : ℝ) ≤ (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    linarith
  have hRHSbound : (0 : ℝ) ≤ (1 / ((p : ℝ) - 2)) * PrimeGaps.gSum W X :=
    mul_nonneg (one_div_nonneg.mpr hp2) hgSum_nonneg
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hiSum (pow_nonneg hgSum_nonneg _)) hiSum
    hcSumP_nonneg (mul_nonneg (pow_nonneg hgSum_nonneg _) hRHSbound)).trans_eq (by
      rw [pow_add]; ring)

/-- `∑' u, ∑' u', (if p ∣ u * u' then f u * v u' else 0) ≤ (∑'_{p ∣ u} f u) * (∑' u', v u') +
(∑' u, f u) * (∑'_{p ∣ u'} v u')` for nonnegative summable `f`, `v` and a prime `p`. -/
theorem PrimeGaps.dvd_mul_double_tsum_le (p : ℕ) (hp : p.Prime) (f v : ℕ → ℝ)
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ v n)
    (hf : Summable f) (hg : Summable v)
    (hfP : Summable (fun n ↦ if p ∣ n then f n else 0))
    (hgP : Summable (fun n ↦ if p ∣ n then v n else 0)) :
    (∑' (u : ℕ), ∑' (u' : ℕ), (if p ∣ u * u' then f u * v u' else 0)) ≤
      (∑' (u : ℕ), if p ∣ u then f u else 0) * (∑' (u' : ℕ), v u') +
        (∑' (u : ℕ), f u) * (∑' (u' : ℕ), if p ∣ u' then v u' else 0) := by
  have hpoint : ∀ u u', (if p ∣ u * u' then f u * v u' else 0) ≤
        (if p ∣ u then f u else 0) * v u' + f u * (if p ∣ u' then v u' else 0) := by
    intro u u'
    have h1 : 0 ≤ (if p ∣ u then f u else 0) * v u' :=
      mul_nonneg (by split_ifs; exacts [hf0 u, le_rfl]) (hg0 u')
    have h2 : 0 ≤ f u * (if p ∣ u' then v u' else 0) :=
      mul_nonneg (hf0 u) (by split_ifs; exacts [hg0 u', le_rfl])
    by_cases huu : p ∣ u * u'
    · rw [if_pos huu]
      rcases hp.dvd_mul.mp huu with hpu | hpu'
      · rw [if_pos hpu]; linarith
      · rw [if_pos hpu']; linarith
    · rw [if_neg huu]; linarith
  set Sg := ∑' (u' : ℕ), v u'
  set SgP := ∑' (u' : ℕ), if p ∣ u' then v u' else 0
  have hinnerRHS : ∀ u,
      (∑' (u' : ℕ), ((if p ∣ u then f u else 0) * v u' + f u * (if p ∣ u' then v u' else 0))) =
        (if p ∣ u then f u else 0) * Sg + f u * SgP := fun u ↦ by
    rw [Summable.tsum_add (hg.mul_left _) (hgP.mul_left _), tsum_mul_left, tsum_mul_left]
  have hinnerLHS_summable : ∀ u, Summable (fun u' ↦ if p ∣ u * u' then f u * v u' else 0) := by
    intro u
    refine Summable.of_nonneg_of_le (fun u' ↦ ?_) (fun u' ↦ ?_) (hg.mul_left (f u)) <;>
      split_ifs <;> first | exact le_rfl | exact mul_nonneg (hf0 u) (hg0 u')
  have hinnerRHS_summable : ∀ u,
      Summable (fun u' ↦ (if p ∣ u then f u else 0) * v u' + f u * (if p ∣ u' then v u' else 0)) :=
    fun u ↦ (hg.mul_left _).add (hgP.mul_left _)
  have hinner : ∀ u, (∑' (u' : ℕ), (if p ∣ u * u' then f u * v u' else 0)) ≤
      (if p ∣ u then f u else 0) * Sg + f u * SgP := fun u ↦
    (Summable.tsum_le_tsum (hpoint u) (hinnerLHS_summable u)
      (hinnerRHS_summable u)).trans_eq (hinnerRHS u)
  have houterRHS_summable : Summable (fun u ↦ (if p ∣ u then f u else 0) * Sg + f u * SgP) :=
    (hfP.mul_right Sg).add (hf.mul_right SgP)
  have houterLHS_summable : Summable (fun u ↦ ∑' (u' : ℕ), if p ∣ u * u' then f u * v u' else 0) :=
    Summable.of_nonneg_of_le (fun u ↦ tsum_nonneg fun u' ↦ by
      split_ifs; exacts [mul_nonneg (hf0 u) (hg0 u'), le_rfl]) hinner houterRHS_summable
  refine (Summable.tsum_le_tsum hinner houterLHS_summable houterRHS_summable).trans_eq ?_
  rw [Summable.tsum_add (hfP.mul_right Sg) (hf.mul_right SgP), tsum_mul_right, tsum_mul_right]

/-- **Splitting a joint divisibility constraint.** For a nonnegative summable weight `A` on `ℕ`
and a nonnegative weight `B` cut down by a predicate `P`, the triple sum over
`{p ∣ u * u'} ∩ {P ρ}` is at most the sum of the two one-sided triple sums. -/
theorem PrimeGaps.tsum_ite_dvd_mul_and_le {ι : Type*} (p : ℕ) (hp : p.Prime)
    (A : ℕ → ℝ) (B : ι → ℝ) (P : ι → Prop) [DecidablePred P]
    (hA_nonneg : ∀ n, 0 ≤ A n) (hB_nonneg : ∀ ρ, 0 ≤ B ρ)
    (hAsummable : Summable A) (hAPsummable : Summable (fun n ↦ if p ∣ n then A n else 0))
    (hBsum_nonneg : (0 : ℝ) ≤ ∑' ρ : ι, (if P ρ then B ρ else 0)) :
    (∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : ι), (if p ∣ u * u' ∧ P ρ then A u * A u' * B ρ else 0)) ≤
      (∑' u : ℕ, if p ∣ u then A u else 0) * (∑' u' : ℕ, A u') *
          (∑' ρ : ι, if P ρ then B ρ else 0) +
        (∑' u : ℕ, A u) * (∑' u' : ℕ, if p ∣ u' then A u' else 0) *
          (∑' ρ : ι, if P ρ then B ρ else 0) := by
  have hinner : ∀ (u u' : ℕ), (∑' (ρ : ι), (if p ∣ u * u' ∧ P ρ then A u * A u' * B ρ else 0)) ≤
      (if p ∣ u * u' then A u * A u' else 0) * (∑' ρ : ι, (if P ρ then B ρ else 0)) := by
    intro u u'
    by_cases huu : p ∣ u * u'
    · rw [if_pos huu, ← tsum_mul_left]
      refine le_of_eq (tsum_congr fun ρ ↦ ?_)
      by_cases hρ : P ρ
      · rw [if_pos ⟨huu, hρ⟩, if_pos hρ]
      · rw [if_neg (fun h ↦ hρ h.2), if_neg hρ, mul_zero]
    · rw [if_neg huu, zero_mul, tsum_congr fun ρ ↦ if_neg (fun h ↦ huu h.1), tsum_zero]
  set SB := ∑' (ρ : ι), (if P ρ then B ρ else 0)
  have hAAsummable : ∀ u, Summable (fun u' ↦ if p ∣ u * u' then A u * A u' else 0) := by
    intro u
    refine Summable.of_nonneg_of_le (fun u' ↦ ?_) (fun u' ↦ ?_) (hAsummable.mul_left (A u)) <;>
      split_ifs <;> first | exact le_rfl | exact mul_nonneg (hA_nonneg u) (hA_nonneg u')
  have hred_summable_u' : ∀ u, Summable
      (fun u' ↦ (if p ∣ u * u' then A u * A u' else 0) * SB) := fun u ↦
    (hAAsummable u).mul_right SB
  have hLHS_inner_summable_u' : ∀ u, Summable (fun u' ↦ ∑' (ρ : ι),
        (if p ∣ u * u' ∧ P ρ then A u * A u' * B ρ else 0)) := fun u ↦
    Summable.of_nonneg_of_le (fun u' ↦ tsum_nonneg fun ρ ↦ by
        split_ifs
        exacts [mul_nonneg (mul_nonneg (hA_nonneg u) (hA_nonneg u')) (hB_nonneg ρ), le_rfl])
      (hinner u) (hred_summable_u' u)
  have hstep_u' : ∀ u, (∑' (u' : ℕ), ∑' (ρ : ι),
          (if p ∣ u * u' ∧ P ρ then A u * A u' * B ρ else 0)) ≤
        ∑' (u' : ℕ), (if p ∣ u * u' then A u * A u' else 0) * SB := fun u ↦
    Summable.tsum_le_tsum (hinner u) (hLHS_inner_summable_u' u) (hred_summable_u' u)
  have hred_summable_u : Summable
      (fun u ↦ ∑' (u' : ℕ), (if p ∣ u * u' then A u * A u' else 0) * SB) := by
    have hbase : Summable (fun u ↦ (∑' (u' : ℕ), if p ∣ u * u' then A u * A u' else 0) * SB) :=
      Summable.mul_right SB (Summable.of_nonneg_of_le
        (fun u ↦ tsum_nonneg fun u' ↦ by
          split_ifs; exacts [mul_nonneg (hA_nonneg u) (hA_nonneg u'), le_rfl])
        (fun u ↦ (Summable.tsum_le_tsum (fun u' ↦ by
              split_ifs; exacts [le_rfl, mul_nonneg (hA_nonneg u) (hA_nonneg u')])
            (hAAsummable u) (hAsummable.mul_left (A u))).trans_eq tsum_mul_left)
        (hAsummable.mul_right (∑' (n : ℕ), A n)))
    exact hbase.congr fun u ↦ tsum_mul_right.symm
  have hstep_u : (∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : ι),
          (if p ∣ u * u' ∧ P ρ then A u * A u' * B ρ else 0)) ≤
        ∑' (u : ℕ), ∑' (u' : ℕ), (if p ∣ u * u' then A u * A u' else 0) * SB :=
    Summable.tsum_le_tsum hstep_u'
      (Summable.of_nonneg_of_le (fun u ↦ tsum_nonneg fun u' ↦ tsum_nonneg fun ρ ↦ by
          split_ifs
          exacts [mul_nonneg (mul_nonneg (hA_nonneg u) (hA_nonneg u')) (hB_nonneg ρ), le_rfl])
        hstep_u' hred_summable_u) hred_summable_u
  have hfactorSB : (∑' (u : ℕ), ∑' (u' : ℕ), (if p ∣ u * u' then A u * A u' else 0) * SB) =
        (∑' (u : ℕ), ∑' (u' : ℕ), (if p ∣ u * u' then A u * A u' else 0)) * SB := by
    rw [← tsum_mul_right]
    exact tsum_congr fun u ↦ tsum_mul_right
  have hhelper : (∑' (u : ℕ), ∑' (u' : ℕ), (if p ∣ u * u' then A u * A u' else 0)) ≤
        (∑' (u : ℕ), if p ∣ u then A u else 0) * (∑' (u' : ℕ), A u') +
          (∑' (u : ℕ), A u) * (∑' (u' : ℕ), if p ∣ u' then A u' else 0) :=
    PrimeGaps.dvd_mul_double_tsum_le p hp A A hA_nonneg hA_nonneg hAsummable hAsummable
      hAPsummable hAPsummable
  exact (hstep_u.trans_eq hfactorSB).trans
    ((mul_le_mul_of_nonneg_right hhelper hBsum_nonneg).trans_eq (by ring))
