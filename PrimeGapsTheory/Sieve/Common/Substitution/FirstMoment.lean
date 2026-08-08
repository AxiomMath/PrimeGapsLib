/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.Substitution.Basic
public import PrimeGapsTheory.Sieve.S1.Expansion
public import PrimeGapsTheory.Sieve.S1.RestrictSij
public import PrimeGapsTheory.Sieve.S2m.QFactor

import PrimeGapsTheory.Tactic.PaperTag

/-!
# First-moment substitution of transformed weights

Identifies the first-moment primed sum with its transformed-weight expression.

## Main definitions

* `yWeightedSum`: The decoupled sum expressed in transformed weights.

## Main results

* `primedSum_eq_yWeightedSum`: Identifies the primed and transformed-weight sums.
* `lem_S1_substitute_y`: Approximates the first moment by the transformed-weight sum.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius


open GPYSieveS1 PrimeGaps.LemS1RestrictSij

namespace PrimeGaps

/-- The decoupled sum in the transformed weights `y = PrimeGaps.lToY lam`, namely
`∑_{u,s} ∏ᵢ μ(uᵢ)²/φ(uᵢ) * ∏_{i≠j} μ(sᵢⱼ)/φ(sᵢⱼ)² * y (boldA u s) * y (boldB u s)`. -/
noncomputable def yWeightedSum {k : ℕ} (lam : (Fin k → ℕ) →₀ ℝ) : ℝ :=
  ∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
    (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
          RestrictedCoprime u s) then
        (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
        (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s p.1 p.2) : ℝ) / (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
        PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
      else 0)

/-- Everything a permissible support says about one of its tuples. If `lam` has permissible support
for the truncation `⌊Rb⌋₊` and modulus `W`, then any `d` with `lam d ≠ 0` is coordinatewise
positive, has squarefree product coprime to `W`, and satisfies `∏ᵢ dᵢ ≤ Rb` over `ℝ`. -/
private lemma permissibleSupport_facts {k W : ℕ} {Rb : ℝ} {lam : (Fin k → ℕ) →₀ ℝ}
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) {d : Fin k → ℕ} (hd : lam d ≠ 0) :
    (∀ i, 1 ≤ d i) ∧ (∏ i, d i).Coprime W ∧ Squarefree (∏ i, d i) ∧ ∏ i, (d i : ℝ) ≤ Rb := by
  obtain ⟨hleNat, hcop, hsq⟩ :=
    Finset.mem_permissibleSupport_iff.mp (hs (Finsupp.mem_support_iff.mpr hd))
  have hpos : ∀ i, 1 ≤ d i := fun i ↦ Nat.one_le_iff_ne_zero.mpr (hs.ne_zero_of_ne_zero hd i)
  have hfloorpos : 0 < ⌊Rb⌋₊ := lt_of_lt_of_le (Finset.prod_pos fun i _ ↦ hpos i) hleNat
  exact ⟨hpos, hcop, hsq, le_trans (by exact_mod_cast hleNat)
    (Nat.floor_le (Nat.pos_of_floor_pos hfloorpos).le)⟩

/-- The coprime-gated finite `(d,e)` -sum (equal to `SigmaFull D lam` via `lem_S1_mobius_coprime`)
equals `primedSum W lam`, using `HasPermissibleSupport` to discharge the `W`-coprimality gate of
`PairwiseCoprimeModuli`, `∑_{u∣gcd} φ(u) = gcd` (`Nat.sum_totient`), `lcm·gcd = d·e`,
squarefreeness, and the translation of the off-diagonal `Coprime (d i) (e j)` gate into
pairwise coprimality of the moduli.
-/
theorem sigmaFull_eq_primedSum {k : ℕ} (Rb : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) (D : Finset (Fin k → ℕ))
    (hD : ∀ d, lam d ≠ 0 → d ∈ D) :
    SigmaFull D lam = primedSum W lam := by
  classical
  rw [← lem_S1_mobius_coprime D lam]
  rw [primedSum]
  rw [tsum_eq_sum (s := D ×ˢ D) ?_]
  · rw [Finset.sum_product]
    refine Finset.sum_congr rfl ?_
    intro d hd
    refine Finset.sum_congr rfl ?_
    intro e he
    dsimp only
    have htot : (∑ u ∈ Fintype.piFinset fun i ↦ ((d i).gcd (e i)).divisors,
          ∏ i, ((u i).totient : ℝ)) = ∏ i, ((d i).gcd (e i) : ℝ) := by
      rw [← Finset.prod_univ_sum (fun i ↦ ((d i).gcd (e i)).divisors)
            (fun i x ↦ ((Nat.totient x : ℝ)))]
      refine Finset.prod_congr rfl ?_
      intro i _
      rw [← Nat.cast_sum]
      norm_cast
      exact Nat.sum_totient _
    rw [htot]
    by_cases hlam : lam d = 0 ∨ lam e = 0
    · have hz : lam d * lam e = 0 := by rcases hlam with h | h <;> simp [h]
      rw [hz]
      by_cases hC1 : (∀ i j : Fin k, i ≠ j → (d i).Coprime (e j)) <;>
        by_cases hC2 : ((∀ i, 1 ≤ d i) ∧ (∀ i, 1 ≤ e i) ∧ PrimeGaps.PairwiseCoprimeModuli W (fun i ↦
          Nat.lcm (d i) (e i))) <;>
        simp [hC1, hC2]
    · push Not at hlam
      obtain ⟨hdne, hene⟩ := hlam
      obtain ⟨hdpos, hdcop, hdsq, hdle⟩ := permissibleSupport_facts hs hdne
      obtain ⟨hepos, hecop, hesq, hele⟩ := permissibleSupport_facts hs hene
      have pair_dvd : ∀ (f : Fin k → ℕ) (i j : Fin k), i ≠ j → f i * f j ∣ ∏ x, f x := by
        intro f i j hij
        have hsub : ({i, j} : Finset (Fin k)) ⊆ Finset.univ := Finset.subset_univ _
        have hpair : (∏ x ∈ ({i, j} : Finset (Fin k)), f x) = f i * f j := Finset.prod_pair hij
        have := Finset.prod_dvd_prod_of_subset ({i, j} : Finset (Fin k)) Finset.univ f hsub
        rwa [hpair] at this
      have hDcop : ∀ i j, i ≠ j → (d i).Coprime (d j) :=
        fun i j hij ↦ Nat.coprime_of_squarefree_mul (hdsq.squarefree_of_dvd (pair_dvd d i j hij))
      have hEcop : ∀ i j, i ≠ j → (e i).Coprime (e j) :=
        fun i j hij ↦ Nat.coprime_of_squarefree_mul (hesq.squarefree_of_dvd (pair_dvd e i j hij))
      have single_dvd : ∀ (f : Fin k → ℕ) (i : Fin k), f i ∣ ∏ x, f x :=
        fun f i ↦ Finset.dvd_prod_of_mem f (Finset.mem_univ i)
      have hWd : ∀ i, W.Coprime (d i) :=
        fun i ↦ (Nat.Coprime.coprime_dvd_left (single_dvd d i) hdcop).symm
      have hWe : ∀ i, W.Coprime (e i) :=
        fun i ↦ (Nat.Coprime.coprime_dvd_left (single_dvd e i) hecop).symm
      have lcm_dvd_mul : ∀ a b : ℕ, a.lcm b ∣ a * b :=
        fun a b ↦ Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)
      have hiff : (∀ i j : Fin k, i ≠ j → (d i).Coprime (e j)) ↔
          ((∀ i, 1 ≤ d i) ∧ (∀ i, 1 ≤ e i) ∧ PrimeGaps.PairwiseCoprimeModuli W (fun i ↦
            Nat.lcm (d i) (e i))) := by
        constructor
        · intro hC1
          refine ⟨hdpos, hepos, ?_⟩
          intro a b hab
          unfold Function.onFun
          revert hab
          refine Fin.cases ?_ ?_ a
          · refine Fin.cases ?_ ?_ b
            · intro hab
              exact absurd rfl hab
            · intro j _
              simp only [Fin.cons_zero, Fin.cons_succ]
              exact Nat.Coprime.coprime_dvd_right (lcm_dvd_mul (d j) (e j))
                ((hWd j).mul_right (hWe j))
          · intro i
            refine Fin.cases ?_ ?_ b
            · intro _
              simp only [Fin.cons_zero, Fin.cons_succ]
              exact (Nat.Coprime.coprime_dvd_right (lcm_dvd_mul (d i) (e i))
                ((hWd i).mul_right (hWe i))).symm
            · intro j hab
              simp only [Fin.cons_succ]
              have hij : i ≠ j := by
                intro hij
                subst j
                exact hab rfl
              have hprodcop : ((d i) * (e i)).Coprime ((d j) * (e j)) := by
                have h1 : (d i).Coprime ((d j) * (e j)) := (hDcop i j hij).mul_right (hC1 i j hij)
                have h2 : (e i).Coprime ((d j) * (e j)) :=
                  (hC1 j i (Ne.symm hij)).symm.mul_right (hEcop i j hij)
                exact Nat.Coprime.mul_left h1 h2
              exact Nat.Coprime.coprime_dvd_left (lcm_dvd_mul (d i) (e i))
                (Nat.Coprime.coprime_dvd_right (lcm_dvd_mul (d j) (e j)) hprodcop)
        · rintro ⟨_, _, hpw⟩
          intro i j hij
          have hlcmcop := hpw ((Fin.succ_injective _).ne hij)
          simp only [Function.onFun, Fin.cons_succ] at hlcmcop
          exact Nat.Coprime.coprime_dvd_left (Nat.dvd_lcm_left (d i) (e i))
            (Nat.Coprime.coprime_dvd_right (Nat.dvd_lcm_right (d j) (e j)) hlcmcop)
      by_cases hC : (∀ i j : Fin k, i ≠ j → (d i).Coprime (e j))
      · rw [if_pos hC, if_pos (hiff.mp hC)]
        have hgl : ∀ i, ((d i).gcd (e i) : ℝ) * ((d i).lcm (e i) : ℝ) =
            (d i : ℝ) * (e i : ℝ) := fun i ↦ by
          rw [← Nat.cast_mul, Nat.gcd_mul_lcm]; push_cast; ring
        have hprodgl : (∏ i, ((d i).gcd (e i) : ℝ)) * (∏ i, ((d i).lcm (e i) : ℝ)) =
            ∏ i, ((d i : ℝ) * (e i : ℝ)) := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl (fun i _ ↦ hgl i)
        have hlcm_pos : ∀ i, (0 : ℝ) < ((d i).lcm (e i) : ℝ) := fun i ↦ by
          have : 0 < (d i).lcm (e i) := Nat.pos_of_ne_zero (Nat.lcm_ne_zero
            (Nat.one_le_iff_ne_zero.mp (hdpos i)) (Nat.one_le_iff_ne_zero.mp (hepos i)))
          exact_mod_cast this
        have hd_pos : ∀ i, (0 : ℝ) < (d i : ℝ) := fun i ↦ by exact_mod_cast (hdpos i)
        have he_pos : ∀ i, (0 : ℝ) < (e i : ℝ) := fun i ↦ by exact_mod_cast (hepos i)
        have hprodlcm_ne : (∏ i, ((d i).lcm (e i) : ℝ)) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr (fun i _ ↦ (hlcm_pos i).ne')
        have hproddei_ne : (∏ i, ((d i : ℝ) * (e i : ℝ))) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr (fun i _ ↦ mul_ne_zero (hd_pos i).ne' (he_pos i).ne')
        rw [mul_div_assoc']
        rw [div_eq_div_iff hproddei_ne hprodlcm_ne]
        linear_combination (lam d * lam e) * hprodgl
      · rw [if_neg hC, if_neg (fun hc ↦ hC (hiff.mpr hc)), mul_zero]
  · intro de hde
    by_cases hcond : ((∀ i, 1 ≤ de.1 i) ∧ (∀ i, 1 ≤ de.2 i) ∧
      PrimeGaps.PairwiseCoprimeModuli W (fun i ↦ Nat.lcm (de.1 i) (de.2 i)))
    · rw [if_pos hcond]
      rw [Finset.mem_product, not_and_or] at hde
      rcases hde with h1 | h2
      · have : lam de.1 = 0 := by by_contra hne; exact h1 (hD _ hne)
        rw [this]; ring
      · have : lam de.2 = 0 := by by_contra hne; exact h2 (hD _ hne)
        rw [this]; ring
    · rw [if_neg hcond]

/-- Box for the `u` -index: each coordinate in `Iic ⌊Rb⌋₊`. -/
noncomputable def Ubox (k : ℕ) (Rb : ℝ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ ↦ Finset.Iic ⌊Rb⌋₊)

/-- Box for the `s` -index: each coordinate in `Iic ⌊Rb⌋₊`. -/
noncomputable def Sbox (k : ℕ) (Rb : ℝ) : Finset (Fin k → Fin k → ℕ) :=
  Fintype.piFinset (fun _ ↦ Fintype.piFinset (fun _ ↦ Finset.Iic ⌊Rb⌋₊))

/-- Distributing the product of two guarded `D` -sums over a guarded coefficient, merging the
three guards into one. Both moments pass through this step when they turn their `(u, s)` box sum
into a quadruple `(u, s, d, e)` sum. -/
lemma ite_mul_sum_mul_sum {k : ℕ} (D : Finset (Fin k → ℕ)) (P : Prop) [Decidable P] (c : ℝ)
    (PA PB : (Fin k → ℕ) → Prop) [DecidablePred PA] [DecidablePred PB]
    (fa fb : (Fin k → ℕ) → ℝ) :
    (if P then c * (∑ d ∈ D, if PA d then fa d else 0) * (∑ e ∈ D, if PB e then fb e else 0)
        else 0) =
      ∑ d ∈ D, ∑ e ∈ D, if P ∧ PA d ∧ PB e then c * fa d * fb e else 0 := by
  by_cases hP : P
  · rw [if_pos hP, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    by_cases hA : PA d
    · by_cases hB : PB e
      · rw [if_pos hA, if_pos hB, if_pos ⟨hP, hA, hB⟩]; ring
      · simp [hB]
    · simp [hA]
  · rw [if_neg hP]
    exact (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ if_neg fun h ↦ hP h.1).symm

/-- The two boxes catch a guarded pair `(u, s)` as soon as `boldA u s` is bounded coordinatewise
by `⌊Rb⌋₊`: every `u i` and every off-diagonal `s i j` divides `boldA u s i`, and the diagonal
entries are one. Both moments use this to replace their `(u, s)` -`tsum` by a finite box sum. -/
lemma mem_Ubox_Sbox_of_boldA_le {k : ℕ} (Rb : ℝ) (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hupos : ∀ i, 1 ≤ u i) (hsii : ∀ i, s i i = 1) (hspos : ∀ i j, i ≠ j → 1 ≤ s i j)
    (hle : ∀ i, boldA u s i ≤ ⌊Rb⌋₊) :
    u ∈ Ubox k Rb ∧ s ∈ Sbox k Rb := by
  classical
  have hApos : ∀ i, 1 ≤ boldA u s i := fun i ↦ boldA_pos u s hupos hspos i
  refine ⟨?_, ?_⟩
  · rw [Ubox, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Iic]
    exact le_trans (Nat.le_of_dvd (hApos i) (Dvd.intro _ rfl)) (hle i)
  · rw [Sbox, Fintype.mem_piFinset]
    intro i
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Iic]
    rcases eq_or_ne i j with rfl | hij
    · rw [hsii i]; exact le_trans (hApos i) (hle i)
    · refine le_trans (Nat.le_of_dvd (hApos i) ?_) (hle i)
      unfold boldA
      exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _
        (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)) _

/-- The shared reindexed finite sum over `(u,s)` boxes with inner `(d,e)` sums. -/
noncomputable def reindexedSum {k : ℕ} (Rb : ℝ) (lam : (Fin k → ℕ) →₀ ℝ)
    (D : Finset (Fin k → ℕ)) : ℝ :=
  ∑ u ∈ Ubox k Rb, ∑ s ∈ Sbox k Rb, (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧
          (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s) then
        ((∏ i, (Nat.totient (u i) : ℝ)) * (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              (μ (s p.1 p.2) : ℝ))) *
        (∑ d ∈ D, if (∀ i, 1 ≤ d i) ∧ (∀ i, boldA u s i ∣ d i)
                    then lam d / ∏ i, (d i : ℝ) else 0) *
        (∑ e ∈ D, if (∀ i, 1 ≤ e i) ∧ (∀ i, boldB u s i ∣ e i)
                    then lam e / ∏ i, (e i : ℝ) else 0)
      else 0)

end PrimeGaps

namespace Nat

/-- Product of pairwise-coprime factors divides `n` ⟺ each factor divides `n`. -/
lemma pairwise_coprime_prod_dvd_iff {ι : Type*} (S : Finset ι) (f : ι → ℕ) (n : ℕ)
    (hpair : (S : Set ι).Pairwise (fun i j ↦ Nat.Coprime (f i) (f j))) :
    (∀ i ∈ S, f i ∣ n) ↔ (∏ i ∈ S, f i) ∣ n := by
  classical
  constructor
  · intro h
    induction S using Finset.induction with
    | empty => simp
    | @insert a T ha ih =>
        rw [Finset.prod_insert ha]
        have hpairT : (T : Set ι).Pairwise (fun i j ↦ Nat.Coprime (f i) (f j)) :=
          hpair.mono (by simp)
        have hcop : Nat.Coprime (f a) (∏ i ∈ T, f i) := by
          refine Nat.Coprime.prod_right ?_
          intro i hi
          exact hpair (by simp) (by simp [hi]) (by rintro rfl; exact ha hi)
        refine hcop.mul_dvd_of_dvd_of_dvd (h a (by simp)) ?_
        refine ih hpairT ?_
        intro i hi; exact h i (by simp [hi])
  · intro h i hi; exact dvd_trans (Finset.dvd_prod_of_mem f hi) h

/-- Totient over a finite pairwise-coprime product. -/
lemma totient_prod_of_pairwise_coprime {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    (hpair : (S : Set ι).Pairwise (fun i j ↦ Nat.Coprime (f i) (f j))) :
    Nat.totient (∏ i ∈ S, f i) = ∏ i ∈ S, Nat.totient (f i) :=
  Nat.map_prod_of_pairwise_coprime Nat.totient Nat.totient_one
    (fun _ _ hab ↦ Nat.totient_mul hab) S f hpair

end Nat

namespace PrimeGaps

/-- `PrimeGaps.lToY lam r` expands to a finite sum over `D` (support argument). -/
lemma yWeight_eq_sum_D {k : ℕ} (lam : (Fin k → ℕ) →₀ ℝ)
    {R W : ℕ} (hl : lam.HasPermissibleSupport R W)
    (D : Finset (Fin k → ℕ)) (hD : ∀ d, lam d ≠ 0 → d ∈ D) (r : Fin k → ℕ) :
    PrimeGaps.lToY lam r = (∏ i, (μ (r i) : ℝ) * (Nat.totient (r i) : ℝ)) *
        ∑ d ∈ D, (if (∀ i, 1 ≤ d i) ∧ (∀ i, r i ∣ d i)
                    then lam d / ∏ i, (d i : ℝ) else 0) := by
  classical
  rw [PrimeGaps.lToY_apply hl]
  simp_rw [Int.cast_prod, Int.cast_mul, Int.cast_natCast, Nat.cast_prod]
  congr 1
  rw [Finsupp.sum]
  calc
    ∑ d ∈ lam.support, (if ∀ i, r i ∣ d i then lam d / ∏ i, (d i : ℝ) else 0) =
        ∑ d ∈ lam.support, (if (∀ i, 1 ≤ d i) ∧ (∀ i, r i ∣ d i) then
          lam d / ∏ i, (d i : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hld : lam d ≠ 0 := Finsupp.mem_support_iff.mp hd
            have hdpos : ∀ i, 1 ≤ d i := fun i ↦ Nat.one_le_iff_ne_zero.mpr
              (hl.ne_zero_of_ne_zero hld i)
            simp [hdpos]
    _ = ∑ d ∈ D, (if (∀ i, 1 ≤ d i) ∧ (∀ i, r i ∣ d i) then
          lam d / ∏ i, (d i : ℝ) else 0) := by
            apply Finset.sum_subset
            · intro d hd
              exact hD d (Finsupp.mem_support_iff.mp hd)
            · intro d _ hd
              rw [Finsupp.mem_support_iff, not_not] at hd
              simp [hd]

/-- The μ/φ coefficient collapse:
`(∏μ(u)²/φ(u))(∏_{offDiag}μ(s)/φ(s)²)·(∏μ(A)φ(A))(∏μ(B)φ(B))
   = (∏φ(u))(∏_{offDiag}μ(s))`.
-/
lemma coefficient_collapse {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hcop : RestrictedCoprime u s)
    (hupos : ∀ i, 1 ≤ u i)
    (hspos : ∀ i j, i ≠ j → 1 ≤ s i j)
    (hsq_u : ∀ i, Squarefree (u i))
    (hsq_s : ∀ i j, i ≠ j → Squarefree (s i j)) :
    (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
    (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
        (μ (s p.1 p.2) : ℝ) / (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
    (∏ i, (μ (boldA u s i) : ℝ) * (Nat.totient (boldA u s i) : ℝ)) *
    (∏ i, (μ (boldB u s i) : ℝ) * (Nat.totient (boldB u s i) : ℝ)) =
      (∏ i, (Nat.totient (u i) : ℝ)) * (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s p.1 p.2) : ℝ)) := by
  classical
  have hφ1 : ((Nat.totient 1 : ℕ) : ℝ) = 1 := by simp
  have hφmul : ∀ a b : ℕ, Nat.Coprime a b →
      ((Nat.totient (a * b) : ℕ) : ℝ) = (Nat.totient a : ℝ) * (Nat.totient b : ℝ) :=
    fun a b hab ↦ by rw [Nat.totient_mul hab]; push_cast; ring
  have wA : ∀ i, (Nat.totient (boldA u s i) : ℝ) =
      (Nat.totient (u i) : ℝ) * ∏ a ∈ Finset.univ.erase i, (Nat.totient (s i a) : ℝ) :=
    map_boldA (fun n ↦ (Nat.totient n : ℝ)) hφ1 hφmul u s hcop
  have wB : ∀ i, (Nat.totient (boldB u s i) : ℝ) =
      (Nat.totient (u i) : ℝ) * ∏ a ∈ Finset.univ.erase i, (Nat.totient (s a i) : ℝ) :=
    map_boldB (fun n ↦ (Nat.totient n : ℝ)) hφ1 hφmul u s hcop
  have hwu_ne : ∀ i, (Nat.totient (u i) : ℝ) ≠ 0 := by
    intro i; have : 0 < Nat.totient (u i) := Nat.totient_pos.mpr (hupos i); exact_mod_cast this.ne'
  have hws_ne : ∀ i j, i ≠ j → (Nat.totient (s i j) : ℝ) ≠ 0 := by
    intro i j hij
    have : 0 < Nat.totient (s i j) := Nat.totient_pos.mpr (hspos i j hij); exact_mod_cast this.ne'
  exact coeff_collapse_gen u s (fun n ↦ (Nat.totient n : ℝ))
    hcop hsq_u hsq_s hwu_ne hws_ne wA wB

/-- Pairwise-coprime divisibility collapses to a single product. For a distinguished index `i`, a
number `a` and an off-diagonal family `t` that is pairwise coprime and coprime to `a`, the number
`n` is divisible by `a` and by every `t j` with `j ≠ i` exactly when it is divisible by the single
product `a * ∏_{j ≠ i} t j`.

`boldA` and `boldB` are this product for `t` a row, respectively a column, of `s`, so `row_collapse`
and `col_collapse` are the two instances of this lemma along the two axes. -/
private lemma mul_prod_erase_dvd_iff {k : ℕ} (i : Fin k) (a : ℕ) (t : Fin k → ℕ) (n : ℕ)
    (hcop_at : ∀ j, j ≠ i → Nat.Coprime a (t j))
    (hcop_tt : ∀ j j', j ≠ i → j' ≠ i → j ≠ j' → Nat.Coprime (t j) (t j')) :
    ((a ∣ n) ∧ ∀ j, j ≠ i → t j ∣ n) ↔ (a * ∏ j ∈ Finset.univ.erase i, t j) ∣ n := by
  classical
  set g : Fin k → ℕ := fun j ↦ if j = i then a else t j with hg
  have hprodg : ∏ j, g j = a * ∏ j ∈ Finset.univ.erase i, t j := by
    rw [← Finset.prod_erase_mul _ g (Finset.mem_univ i)]
    have h1 : g i = a := by simp only [hg, if_pos rfl]
    have h2 : ∏ j ∈ Finset.univ.erase i, g j = ∏ j ∈ Finset.univ.erase i, t j := by
      refine Finset.prod_congr rfl (fun j hj ↦ ?_)
      simp only [hg, if_neg (Finset.ne_of_mem_erase hj)]
    rw [h1, h2, mul_comm]
  have hpair : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise
      (fun x y ↦ Nat.Coprime (g x) (g y)) := by
    intro x _ y _ hxy
    simp only [hg]
    by_cases hx : x = i
    · subst hx
      rw [if_pos rfl, if_neg (Ne.symm hxy)]
      exact hcop_at y (Ne.symm hxy)
    · by_cases hy : y = i
      · subst hy
        rw [if_neg hx, if_pos rfl]
        exact (hcop_at x hx).symm
      · rw [if_neg hx, if_neg hy]
        exact hcop_tt x y hx hy hxy
  have hiff := Nat.pairwise_coprime_prod_dvd_iff (Finset.univ : Finset (Fin k)) g n hpair
  rw [hprodg] at hiff
  rw [← hiff]
  constructor
  · rintro ⟨ha, htdvd⟩ j _
    simp only [hg]
    by_cases hj : j = i
    · subst hj; rw [if_pos rfl]; exact ha
    · rw [if_neg hj]; exact htdvd j hj
  · intro h
    refine ⟨?_, ?_⟩
    · have := h i (Finset.mem_univ i); simp only [hg, if_pos rfl] at this; exact this
    · intro j hj; have := h j (Finset.mem_univ j); simp only [hg, if_neg hj] at this; exact this

/-- Given the family `{u_i} ∪ {s_{i,j}: j ≠ i}` pairwise coprime,
`(u_i ∣ di ∧ ∀ j ≠ i, s_{i,j} ∣ di) ↔ boldA u s i ∣ di`.
-/
lemma row_collapse {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (i : Fin k) (di : ℕ)
    (hcop_us : ∀ j, j ≠ i → Nat.Coprime (u i) (s i j))
    (hcop_ss : ∀ j j', j ≠ i → j' ≠ i → j ≠ j' → Nat.Coprime (s i j) (s i j')) :
    ((u i ∣ di) ∧ ∀ j, j ≠ i → s i j ∣ di) ↔ boldA u s i ∣ di :=
  mul_prod_erase_dvd_iff i (u i) (s i) di hcop_us hcop_ss

/-- Given the family `{u_i} ∪ {s_{j,i}: j ≠ i}` pairwise coprime,
`(u_i ∣ ei ∧ ∀ j ≠ i, s_{j,i} ∣ ei) ↔ boldB u s i ∣ ei`.
-/
lemma col_collapse {k : ℕ} (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) (i : Fin k) (ei : ℕ)
    (hcop_us : ∀ j, j ≠ i → Nat.Coprime (u i) (s j i))
    (hcop_ss : ∀ j j', j ≠ i → j' ≠ i → j ≠ j' → Nat.Coprime (s j i) (s j' i)) :
    ((u i ∣ ei) ∧ ∀ j, j ≠ i → s j i ∣ ei) ↔ boldB u s i ∣ ei :=
  mul_prod_erase_dvd_iff i (u i) (fun j ↦ s j i) ei hcop_us hcop_ss

/-- The reindexing bridge shared by both moments. For a positive tuple `d`, a pair `(u, s)` ranges
over `uDomain d e × sDomain d e` subject to `RestrictedCoprime u s` exactly when `(u, s)` satisfies
the box guard (`u ≥ 1`, unit diagonal, off-diagonal `s ≥ 1`, restricted coprimality) and
`boldA u s` divides `d` while `boldB u s` divides `e`, coordinatewise. This is the substitution
`(d, e) ↦ (u, s)` of the first moment and of the second moment alike; the two differ only in the
extra guards (`d` positive, resp. `d m = 1` and `d` squarefree) they carry alongside.
-/
lemma mem_domain_iff_bold_dvd {k : ℕ} (d e : Fin k → ℕ) (hdpos : ∀ i, 1 ≤ d i)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) :
    (u ∈ uDomain d e ∧ s ∈ sDomain d e ∧ RestrictedCoprime u s) ↔
      (((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s) ∧
          (∀ i, boldA u s i ∣ d i) ∧ (∀ i, boldB u s i ∣ e i)) := by
  classical
  have humem : u ∈ uDomain d e ↔ ∀ a, u a ∣ (d a).gcd (e a) ∧ (d a).gcd (e a) ≠ 0 := by
    unfold uDomain
    simp only [Fintype.mem_piFinset, Nat.mem_divisors]
  have hsmem : s ∈ sDomain d e ↔
      ∀ a b, s a b ∈ (if a = b then ({1} : Finset ℕ) else ((d a).gcd (e b)).divisors) := by
    unfold sDomain sEntryDomain
    simp only [Fintype.mem_piFinset]
  constructor
  · rintro ⟨hu, hsm, hRA⟩
    rw [humem] at hu
    rw [hsmem] at hsm
    have hsdiag : ∀ i, s i i = 1 := by
      intro i
      have := hsm i i
      rw [if_pos rfl] at this
      simpa using this
    have hsoff : ∀ i j, i ≠ j → s i j ∣ (d i).gcd (e j) ∧ (d i).gcd (e j) ≠ 0 := by
      intro i j hij
      have := hsm i j
      rw [if_neg hij] at this
      rw [Nat.mem_divisors] at this
      exact this
    have hupos : ∀ i, 1 ≤ u i := by
      intro i
      obtain ⟨hdvd, hne⟩ := hu i
      have : u i ≠ 0 := by
        intro h0; rw [h0] at hdvd
        exact hne (Nat.eq_zero_of_zero_dvd hdvd)
      omega
    have hspos : ∀ i j, i ≠ j → 1 ≤ s i j := by
      intro i j hij
      obtain ⟨hdvd, hne⟩ := hsoff i j hij
      have : s i j ≠ 0 := by
        intro h0; rw [h0] at hdvd
        exact hne (Nat.eq_zero_of_zero_dvd hdvd)
      omega
    have cop_u_sia : ∀ i a, i ≠ a → Nat.Coprime (u i) (s i a) := fun i a hia ↦
      (Nat.coprime_iff_gcd_eq_one.mpr (hRA i a hia).1).symm
    have cop_u_sai : ∀ i a, a ≠ i → Nat.Coprime (u i) (s a i) := fun i a hai ↦
      (Nat.coprime_iff_gcd_eq_one.mpr (hRA a i hai).2.1).symm
    have cop_row : ∀ i a a', i ≠ a → i ≠ a' → a ≠ a' →
        Nat.Coprime (s i a) (s i a') := fun i a a' hia hia' haa' ↦
      Nat.coprime_iff_gcd_eq_one.mpr ((hRA i a hia).2.2.1 a' (Ne.symm haa') (Ne.symm hia'))
    have cop_col : ∀ i a a', a ≠ i → a' ≠ i → a ≠ a' →
        Nat.Coprime (s a i) (s a' i) := fun i a a' hai ha'i haa' ↦
      Nat.coprime_iff_gcd_eq_one.mpr ((hRA a i hai).2.2.2 a' (Ne.symm haa') ha'i)
    refine ⟨⟨hupos, hsdiag, hspos, hRA⟩, fun i ↦ ?_, fun i ↦ ?_⟩
    · rw [← row_collapse u s i (d i) (fun j hj ↦ cop_u_sia i j (Ne.symm hj))
        (fun j j' hj hj' hjj' ↦ cop_row i j j' (Ne.symm hj) (Ne.symm hj') hjj')]
      exact ⟨dvd_trans (hu i).1 (Nat.gcd_dvd_left _ _),
        fun j hj ↦ dvd_trans (hsoff i j (Ne.symm hj)).1 (Nat.gcd_dvd_left _ _)⟩
    · rw [← col_collapse u s i (e i) (fun j hj ↦ cop_u_sai i j hj)
        (fun j j' hj hj' hjj' ↦ cop_col i j j' hj hj' hjj')]
      exact ⟨dvd_trans (hu i).1 (Nat.gcd_dvd_right _ _),
        fun j hj ↦ dvd_trans (hsoff j i hj).1 (Nat.gcd_dvd_right _ _)⟩
  · rintro ⟨⟨hupos, hsdiag, hspos, hRA⟩, hAdvd, hBdvd⟩
    have cop_u_sia : ∀ i a, i ≠ a → Nat.Coprime (u i) (s i a) := fun i a hia ↦
      (Nat.coprime_iff_gcd_eq_one.mpr (hRA i a hia).1).symm
    have cop_u_sai : ∀ i a, a ≠ i → Nat.Coprime (u i) (s a i) := fun i a hai ↦
      (Nat.coprime_iff_gcd_eq_one.mpr (hRA a i hai).2.1).symm
    have cop_row : ∀ i a a', i ≠ a → i ≠ a' → a ≠ a' →
        Nat.Coprime (s i a) (s i a') := fun i a a' hia hia' haa' ↦
      Nat.coprime_iff_gcd_eq_one.mpr ((hRA i a hia).2.2.1 a' (Ne.symm haa') (Ne.symm hia'))
    have cop_col : ∀ i a a', a ≠ i → a' ≠ i → a ≠ a' →
        Nat.Coprime (s a i) (s a' i) := fun i a a' hai ha'i haa' ↦
      Nat.coprime_iff_gcd_eq_one.mpr ((hRA a i hai).2.2.2 a' (Ne.symm haa') ha'i)
    have hArow : ∀ i, (u i ∣ d i) ∧ ∀ j, j ≠ i → s i j ∣ d i := by
      intro i
      rw [row_collapse u s i (d i) (fun j hj ↦ cop_u_sia i j (Ne.symm hj))
        (fun j j' hj hj' hjj' ↦ cop_row i j j' (Ne.symm hj) (Ne.symm hj') hjj')]
      exact hAdvd i
    have hBcol : ∀ i, (u i ∣ e i) ∧ ∀ j, j ≠ i → s j i ∣ e i := by
      intro i
      rw [col_collapse u s i (e i) (fun j hj ↦ cop_u_sai i j hj)
        (fun j j' hj hj' hjj' ↦ cop_col i j j' hj hj' hjj')]
      exact hBdvd i
    refine ⟨humem.mpr ?_, hsmem.mpr ?_, hRA⟩
    · intro i
      refine ⟨Nat.dvd_gcd (hArow i).1 (hBcol i).1, ?_⟩
      have : 0 < (d i).gcd (e i) := Nat.gcd_pos_of_pos_left _ (hdpos i)
      omega
    · intro a b
      by_cases hab : a = b
      · rw [if_pos hab]
        subst hab
        rw [hsdiag a]; simp
      · rw [if_neg hab, Nat.mem_divisors]
        refine ⟨Nat.dvd_gcd ((hArow a).2 b (Ne.symm hab)) ((hBcol b).2 a hab), ?_⟩
        have : 0 < (d a).gcd (e b) := Nat.gcd_pos_of_pos_left _ (hdpos a)
        omega

/-- `uDomain d e ⊆ Ubox` when `d` is positive with `∏ d ≤ Rb`. -/
lemma uDomain_sub {k : ℕ} (Rb : ℝ) (d e : Fin k → ℕ)
    (hdpos : ∀ i, 1 ≤ d i) (hdle : ((∏ i, d i : ℕ) : ℝ) ≤ Rb) :
    uDomain d e ⊆ Ubox k Rb := by
  classical
  intro u hu
  unfold uDomain at hu
  simp only [Fintype.mem_piFinset, Nat.mem_divisors] at hu
  simp only [Ubox, Fintype.mem_piFinset, Finset.mem_Iic]
  intro i
  obtain ⟨hdvd, -⟩ := hu i
  have hui_le : u i ≤ ∏ j, d j :=
    (Nat.le_of_dvd (hdpos i) (hdvd.trans (Nat.gcd_dvd_left _ _))).trans
      (Finset.single_le_prod' (fun j _ ↦ hdpos j) (Finset.mem_univ i))
  exact Nat.le_floor (le_trans (by exact_mod_cast hui_le) hdle)

/-- `sDomain d e ⊆ Sbox` when `d` is positive with `∏ d ≤ Rb`. -/
lemma sDomain_sub {k : ℕ} (Rb : ℝ) (d e : Fin k → ℕ)
    (hdpos : ∀ i, 1 ≤ d i) (hdle : ((∏ i, d i : ℕ) : ℝ) ≤ Rb) :
    sDomain d e ⊆ Sbox k Rb := by
  classical
  have hRb1 : 1 ≤ ⌊Rb⌋₊ := by
    have hprod1 : 1 ≤ ∏ j, d j := Finset.one_le_prod' fun j _ ↦ hdpos j
    have h1 : (1 : ℝ) ≤ Rb := le_trans (by exact_mod_cast hprod1) hdle
    exact Nat.le_floor (by exact_mod_cast h1)
  intro s hs
  unfold sDomain sEntryDomain at hs
  simp only [Fintype.mem_piFinset] at hs
  simp only [Sbox, Fintype.mem_piFinset, Finset.mem_Iic]
  intro a b
  have hab := hs a b
  by_cases heq : a = b
  · rw [if_pos heq] at hab
    simp only [Finset.mem_singleton] at hab
    rw [hab]; exact hRb1
  · rw [if_neg heq] at hab
    simp only [Nat.mem_divisors] at hab
    obtain ⟨hdvd, -⟩ := hab
    have hsab_le : s a b ≤ ∏ j, d j :=
      (Nat.le_of_dvd (hdpos a) (hdvd.trans (Nat.gcd_dvd_left _ _))).trans
        (Finset.single_le_prod' (fun j _ ↦ hdpos j) (Finset.mem_univ a))
    exact Nat.le_floor (le_trans (by exact_mod_cast hsab_le) hdle)

end PrimeGaps

namespace Finset

/-- Rewrite a sum over `A ⊆ B` as a membership-indicator sum over `B`. -/
lemma sum_eq_sum_ite_mem {ι M : Type*} [DecidableEq ι] [AddCommMonoid M] (A B : Finset ι)
    (hAB : A ⊆ B) (f : ι → M) :
    (∑ x ∈ A, f x) = ∑ x ∈ B, if x ∈ A then f x else 0 := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hAB]

/-- Rewrite a filtered sum over `A ⊆ B` as an indicator sum over `B`. -/
lemma sum_filter_eq_sum_ite_mem {ι M : Type*} [DecidableEq ι] [AddCommMonoid M] (A B : Finset ι)
    (hAB : A ⊆ B) (P : ι → Prop) [DecidablePred P] (f : ι → M) :
    (∑ x ∈ A.filter (fun x ↦ P x), f x) = ∑ x ∈ B, if x ∈ A ∧ P x then f x else 0 := by
  rw [Finset.sum_filter]
  rw [show (∑ x ∈ A, if P x then f x else 0) = ∑ x ∈ A, if x ∈ A ∧ P x then f x else 0 from
    Finset.sum_congr rfl (fun x hx ↦ if_congr ⟨fun h ↦ ⟨hx, h⟩, fun h ↦ h.2⟩ rfl rfl)]
  rw [Finset.sum_subset hAB ?_]
  intro x _ hxA; rw [if_neg (by tauto)]

end Finset

namespace PrimeGaps

/-- Pointwise identity underlying the per-`(d,e)` reindexing: for fixed `u,s` the domain-membership
indicator equals the box-gate indicator, with matching value.
-/
lemma inner_reindex_point {k : ℕ} (lam : (Fin k → ℕ) →₀ ℝ)
    (d e : Fin k → ℕ) (hdpos : ∀ i, 1 ≤ d i) (hepos : ∀ i, 1 ≤ e i)
    (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) :
    (if u ∈ uDomain d e ∧ (s ∈ sDomain d e ∧ RestrictedCoprime u s)
        then T lam u s d e else 0) = (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧
              (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s) ∧
            ((∀ i, 1 ≤ d i) ∧ (∀ i, boldA u s i ∣ d i)) ∧
            ((∀ i, 1 ≤ e i) ∧ (∀ i, boldB u s i ∣ e i)) then
          ((∏ i, (Nat.totient (u i) : ℝ)) * (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                (μ (s p.1 p.2) : ℝ))) * (lam d / ∏ i, (d i : ℝ)) *
          (lam e / ∏ i, (e i : ℝ))
        else 0) := by
  classical
  set C2 : Prop := ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧
              (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s) ∧
            ((∀ i, 1 ≤ d i) ∧ (∀ i, boldA u s i ∣ d i)) ∧
            ((∀ i, 1 ≤ e i) ∧ (∀ i, boldB u s i ∣ e i)) with hC2def
  have hpred : (u ∈ uDomain d e ∧ (s ∈ sDomain d e ∧ RestrictedCoprime u s)) ↔ C2 := by
    rw [mem_domain_iff_bold_dvd d e hdpos u s, hC2def]
    exact ⟨fun h ↦ ⟨h.1, ⟨hdpos, h.2.1⟩, hepos, h.2.2⟩, fun h ↦ ⟨h.1, h.2.1.2, h.2.2.2⟩⟩
  have hval : (u ∈ uDomain d e ∧ (s ∈ sDomain d e ∧ RestrictedCoprime u s)) →
      T lam u s d e = ((∏ i, (Nat.totient (u i) : ℝ)) *
            (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                (μ (s p.1 p.2) : ℝ))) * (lam d / ∏ i, (d i : ℝ)) *
          (lam e / ∏ i, (e i : ℝ)) := by
    intro _
    unfold PrimeGaps.LemS1RestrictSij.T
    rw [Nat.cast_prod, Nat.cast_prod]
    ring
  by_cases h1 : u ∈ uDomain d e ∧ (s ∈ sDomain d e ∧ RestrictedCoprime u s)
  · rw [if_pos h1, if_pos (hpred.mp h1), hval h1]
  · rw [if_neg h1, if_neg (fun h2 ↦ h1 (hpred.mpr h2))]

/-- Per-`(d,e)` reindexing of the inner `(u,s)` sum. -/
lemma inner_reindex {k : ℕ} (Rb : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) (d e : Fin k → ℕ) :
    (∑ u ∈ uDomain d e, ∑ s ∈ {s ∈ sDomain d e | RestrictedCoprime u s},
        T lam u s d e) = ∑ u ∈ Ubox k Rb, ∑ s ∈ Sbox k Rb,
        (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧
              (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s) ∧
            ((∀ i, 1 ≤ d i) ∧ (∀ i, boldA u s i ∣ d i)) ∧
            ((∀ i, 1 ≤ e i) ∧ (∀ i, boldB u s i ∣ e i)) then
          ((∏ i, (Nat.totient (u i) : ℝ)) * (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                (μ (s p.1 p.2) : ℝ))) * (lam d / ∏ i, (d i : ℝ)) *
          (lam e / ∏ i, (e i : ℝ))
        else 0) := by
  classical
  by_cases hlam : lam d = 0 ∨ lam e = 0
  · have hz2 : (lam d / ∏ i, (d i : ℝ)) * (lam e / ∏ i, (e i : ℝ)) = 0 := by
      rcases hlam with h | h <;> simp [h]
    rw [Finset.sum_eq_zero]
    · symm
      refine Finset.sum_eq_zero (fun u _ ↦ Finset.sum_eq_zero (fun s _ ↦ ?_))
      by_cases hg : ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧
              (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s) ∧
            ((∀ i, 1 ≤ d i) ∧ (∀ i, boldA u s i ∣ d i)) ∧
            ((∀ i, 1 ≤ e i) ∧ (∀ i, boldB u s i ∣ e i))
      · rw [if_pos hg, mul_assoc, hz2, mul_zero]
      · rw [if_neg hg]
    · intro u _
      refine Finset.sum_eq_zero (fun s _ ↦ ?_)
      unfold PrimeGaps.LemS1RestrictSij.T
      rw [show lam d * lam e = 0 by rcases hlam with h | h <;> simp [h]]
      simp
  · push Not at hlam
    obtain ⟨hdne, hene⟩ := hlam
    obtain ⟨hdpos, -, -, hdle⟩ := permissibleSupport_facts hs hdne
    obtain ⟨hepos, -, -, hele⟩ := permissibleSupport_facts hs hene
    have hdle' : ((∏ i, d i : ℕ) : ℝ) ≤ Rb := by rwa [Nat.cast_prod]
    have hele' : ((∏ i, e i : ℕ) : ℝ) ≤ Rb := by rwa [Nat.cast_prod]
    have husub : uDomain d e ⊆ Ubox k Rb := uDomain_sub Rb d e hdpos hdle'
    have hssub : sDomain d e ⊆ Sbox k Rb := sDomain_sub Rb d e hdpos hdle'
    rw [show (∑ u ∈ uDomain d e, ∑ s ∈ {s ∈ sDomain d e | RestrictedCoprime u s},
                T lam u s d e) = ∑ u ∈ uDomain d e, ∑ s ∈ Sbox k Rb,
              (if s ∈ sDomain d e ∧ RestrictedCoprime u s then T lam u s d e else 0)
        from Finset.sum_congr rfl (fun u _ ↦ Finset.sum_filter_eq_sum_ite_mem (sDomain d e)
            (Sbox k Rb) hssub (fun s ↦ RestrictedCoprime u s) (fun s ↦ T lam u s d e))]
    rw [Finset.sum_eq_sum_ite_mem (uDomain d e) (Ubox k Rb) husub (fun u ↦ ∑ s ∈ Sbox k Rb,
          (if s ∈ sDomain d e ∧ RestrictedCoprime u s then T lam u s d e else 0))]
    rw [show (∑ u ∈ Ubox k Rb, if u ∈ uDomain d e then
                (∑ s ∈ Sbox k Rb,
                  (if s ∈ sDomain d e ∧ RestrictedCoprime u s then T lam u s d e else 0))
              else 0) = ∑ u ∈ Ubox k Rb, ∑ s ∈ Sbox k Rb,
              (if u ∈ uDomain d e ∧ (s ∈ sDomain d e ∧ RestrictedCoprime u s)
                then T lam u s d e else 0)
        from Finset.sum_congr rfl (fun u _ ↦ ?_)]
    · refine Finset.sum_congr rfl (fun u hu ↦ Finset.sum_congr rfl (fun s hs' ↦ ?_))
      exact inner_reindex_point lam d e hdpos hepos u s
    · by_cases hud : u ∈ uDomain d e
      · rw [if_pos hud]
        refine Finset.sum_congr rfl (fun s _ ↦ ?_)
        by_cases hsc : s ∈ sDomain d e ∧ RestrictedCoprime u s
        · rw [if_pos hsc, if_pos ⟨hud, hsc⟩]
        · rw [if_neg hsc, if_neg (fun h ↦ hsc h.2)]
      · rw [if_neg hud]
        symm
        refine Finset.sum_eq_zero (fun s _ ↦ ?_)
        rw [if_neg (fun h ↦ hud h.1)]

/-- `reindexedSum` reshaped to a `d,e` -outer / `u,s` -inner form matching the `SigmaRestr` layout
after `inner_reindex`.
-/
lemma reindex_de_outer {k : ℕ} (Rb : ℝ) (lam : (Fin k → ℕ) →₀ ℝ) (D : Finset (Fin k → ℕ)) :
    reindexedSum Rb lam D = ∑ d ∈ D, ∑ e ∈ D, ∑ u ∈ Ubox k Rb, ∑ s ∈ Sbox k Rb,
          (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧
                (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s) ∧
              ((∀ i, 1 ≤ d i) ∧ (∀ i, boldA u s i ∣ d i)) ∧
              ((∀ i, 1 ≤ e i) ∧ (∀ i, boldB u s i ∣ e i)) then
            ((∏ i, (Nat.totient (u i) : ℝ)) * (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                  (μ (s p.1 p.2) : ℝ))) * (lam d / ∏ i, (d i : ℝ)) *
            (lam e / ∏ i, (e i : ℝ))
          else 0) := by
  classical
  rw [reindexedSum]
  rw [show (∑ u ∈ Ubox k Rb, ∑ s ∈ Sbox k Rb, (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧
                  (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s) then
                ((∏ i, (Nat.totient (u i) : ℝ)) *
                  (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                      (μ (s p.1 p.2) : ℝ))) *
                (∑ d ∈ D, if (∀ i, 1 ≤ d i) ∧ (∀ i, boldA u s i ∣ d i)
                            then lam d / ∏ i, (d i : ℝ) else 0) *
                (∑ e ∈ D, if (∀ i, 1 ≤ e i) ∧ (∀ i, boldB u s i ∣ e i)
                            then lam e / ∏ i, (e i : ℝ) else 0)
              else 0)) = ∑ u ∈ Ubox k Rb, ∑ s ∈ Sbox k Rb, ∑ d ∈ D, ∑ e ∈ D,
            (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧
                  (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s) ∧
                ((∀ i, 1 ≤ d i) ∧ (∀ i, boldA u s i ∣ d i)) ∧
                ((∀ i, 1 ≤ e i) ∧ (∀ i, boldB u s i ∣ e i)) then
              ((∏ i, (Nat.totient (u i) : ℝ)) *
                (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s p.1 p.2) : ℝ))) * (lam d / ∏ i, (d i : ℝ)) *
              (lam e / ∏ i, (e i : ℝ))
            else 0)
      from ?_]
  · rw [show (∑ u ∈ Ubox k Rb, ∑ s ∈ Sbox k Rb, ∑ d ∈ D, ∑ e ∈ D,
            (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧
                  (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s) ∧
                ((∀ i, 1 ≤ d i) ∧ (∀ i, boldA u s i ∣ d i)) ∧
                ((∀ i, 1 ≤ e i) ∧ (∀ i, boldB u s i ∣ e i)) then
              ((∏ i, (Nat.totient (u i) : ℝ)) *
                (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s p.1 p.2) : ℝ))) * (lam d / ∏ i, (d i : ℝ)) *
              (lam e / ∏ i, (e i : ℝ))
            else 0)) = ∑ u ∈ Ubox k Rb, ∑ d ∈ D, ∑ s ∈ Sbox k Rb, ∑ e ∈ D, _
        from Finset.sum_congr rfl (fun u _ ↦ Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ ↦ ?_)
    rw [show (∑ u ∈ Ubox k Rb, ∑ s ∈ Sbox k Rb, ∑ e ∈ D, _) =
          ∑ u ∈ Ubox k Rb, ∑ e ∈ D, ∑ s ∈ Sbox k Rb, _
        from Finset.sum_congr rfl (fun u _ ↦ Finset.sum_comm)]
    rw [Finset.sum_comm]
  · exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun s _ ↦
      ite_mul_sum_mul_sum D _ _ _ _ _ _

/-- `SigmaRestr` rewritten as the shared `reindexedSum`. -/
lemma sigmaRestr_eq_reindexed {k : ℕ} (Rb : ℝ) (W : ℕ)
    (lam : (Fin k → ℕ) →₀ ℝ) (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W)
    (D : Finset (Fin k → ℕ)) :
    SigmaRestr D lam = reindexedSum Rb lam D := by
  classical
  rw [reindex_de_outer]
  unfold PrimeGaps.LemS1RestrictSij.SigmaRestr
  refine Finset.sum_congr rfl (fun d _ ↦ Finset.sum_congr rfl (fun e _ ↦ ?_))
  exact inner_reindex Rb W lam hs d e

/-- If `PrimeGaps.lToY lam r ≠ 0` then every coordinate of `r` is `≤ ⌊Rb⌋₊`. -/
lemma yWeight_arg_le_of_ne_zero {k : ℕ} (Rb : ℝ) (W : ℕ)
    (lam : (Fin k → ℕ) →₀ ℝ) (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W)
    (r : Fin k → ℕ) (hr : PrimeGaps.lToY lam r ≠ 0) (i : Fin k) :
    r i ≤ ⌊Rb⌋₊ := by
  have hsY := hs.lToY
  have hone : ∀ j ∈ (Finset.univ : Finset (Fin k)), 1 ≤ r j := fun j _ ↦
    Nat.one_le_iff_ne_zero.mpr (hsY.ne_zero_of_ne_zero hr j)
  exact (Finset.single_le_prod' hone (Finset.mem_univ i)).trans (hsY.prod_lt_R_of_ne_zero hr)

/-- The `D` -sum guarded by `r i ∣ d i` (as in `yWeight_eq_sum_D`); if nonzero, every `r i` is
squarefree.
-/
lemma Dsum_ne_zero_squarefree {k : ℕ} (Rb : ℝ) (W : ℕ)
    (lam : (Fin k → ℕ) →₀ ℝ) (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W)
    (D : Finset (Fin k → ℕ)) (r : Fin k → ℕ)
    (hne : (∑ d ∈ D, if (∀ i, 1 ≤ d i) ∧ (∀ i, r i ∣ d i)
              then lam d / ∏ i, (d i : ℝ) else 0) ≠ 0) (i : Fin k) :
    Squarefree (r i) := by
  classical
  obtain ⟨d, _, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  by_cases hc : (∀ i, 1 ≤ d i) ∧ (∀ i, r i ∣ d i)
  · rw [if_pos hc] at hd
    obtain ⟨_, hrdvd⟩ := hc
    have hlamne : lam d ≠ 0 := by intro h0; apply hd; rw [h0]; simp
    have hsq := hs.squarefree_prod_of_ne_zero hlamne
    have hri_dvd : r i ∣ ∏ j, d j :=
      dvd_trans (hrdvd i) (Finset.dvd_prod_of_mem d (Finset.mem_univ i))
    exact hsq.squarefree_of_dvd hri_dvd
  · rw [if_neg hc] at hd; exact absurd rfl hd

/-- `yWeightedSum` rewritten as the shared `reindexedSum`. -/
lemma yWeightedSum_eq_reindexed {k : ℕ} (Rb : ℝ) (W : ℕ)
    (lam : (Fin k → ℕ) →₀ ℝ) (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W)
    (D : Finset (Fin k → ℕ)) (hD : ∀ d, lam d ≠ 0 → d ∈ D) :
    yWeightedSum lam = reindexedSum Rb lam D := by
  classical
  rw [yWeightedSum, reindexedSum, tsum_tsum_eq_sum_sum _ (Ubox k Rb) (Sbox k Rb) ?_]
  · refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
    by_cases hgate : ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
          RestrictedCoprime u s)
    · rw [if_pos hgate, if_pos hgate]
      obtain ⟨hupos, hsdiag, hspos, hcop⟩ := hgate
      rw [yWeight_eq_sum_D lam hs D hD (boldA u s), yWeight_eq_sum_D lam hs D hD (boldB u s)]
      set Sd := (∑ d ∈ D, if (∀ i, 1 ≤ d i) ∧ (∀ i, boldA u s i ∣ d i)
                  then lam d / ∏ i, (d i : ℝ) else 0) with hSdDef
      set Se := (∑ e ∈ D, if (∀ i, 1 ≤ e i) ∧ (∀ i, boldB u s i ∣ e i)
                  then lam e / ∏ i, (e i : ℝ) else 0) with hSeDef
      by_cases hSdz : Sd = 0
      · rw [hSdz]; ring
      by_cases hSez : Se = 0
      · rw [hSez]; ring
      · have hsqA : ∀ i, Squarefree (boldA u s i) :=
          Dsum_ne_zero_squarefree Rb W lam hs D (boldA u s) hSdz
        have hsqB : ∀ i, Squarefree (boldB u s i) :=
          Dsum_ne_zero_squarefree Rb W lam hs D (boldB u s) hSez
        have hsq_u : ∀ i, Squarefree (u i) := by
          intro i
          have hdvd : u i ∣ boldA u s i := by unfold boldA; exact Dvd.intro _ rfl
          exact (hsqA i).squarefree_of_dvd hdvd
        have hsq_s : ∀ i j, i ≠ j → Squarefree (s i j) := by
          intro i j hij
          have hmem : j ∈ Finset.univ.erase i := by
            simp [Finset.mem_erase, Ne.symm hij]
          have hdvd : s i j ∣ boldA u s i := by
            unfold boldA
            exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun a ↦ s i a) hmem) (u i)
          exact (hsqA i).squarefree_of_dvd hdvd
        have hcoef := coefficient_collapse u s hcop hupos hspos hsq_u hsq_s
        calc (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
              (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                  (μ (s p.1 p.2) : ℝ) /
                    (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
              ((∏ i, (μ (boldA u s i) : ℝ) *
                    (Nat.totient (boldA u s i) : ℝ)) * Sd) *
              ((∏ i, (μ (boldB u s i) : ℝ) *
                    (Nat.totient (boldB u s i) : ℝ)) * Se) =
            ((∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
              (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                  (μ (s p.1 p.2) : ℝ) /
                    (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
              (∏ i, (μ (boldA u s i) : ℝ) *
                    (Nat.totient (boldA u s i) : ℝ)) *
              (∏ i, (μ (boldB u s i) : ℝ) *
                    (Nat.totient (boldB u s i) : ℝ))) * Sd * Se := by ring
          _ = ((∏ i, (Nat.totient (u i) : ℝ)) *
                (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s p.1 p.2) : ℝ))) * Sd * Se := by
              rw [hcoef]
    · rw [if_neg hgate, if_neg hgate]
  · intro u s hne
    by_cases hgate : ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
          RestrictedCoprime u s)
    · have hyA : PrimeGaps.lToY lam (boldA u s) ≠ 0 := fun h0 ↦ hne (by
        rw [if_pos hgate, h0]; ring)
      exact mem_Ubox_Sbox_of_boldA_le Rb u s hgate.1 hgate.2.1 hgate.2.2.1
        fun i ↦ yWeight_arg_le_of_ne_zero Rb W lam hs (boldA u s) hyA i
    · exact absurd (if_neg hgate) hne

/-- The restricted finite sum `SigmaRestr D lam` equals `yWeightedSum W lam`. This hides the μ/φ
multiplicative collapse
`∏_i μ(a_i)μ(b_i)/(φ(a_i)φ(b_i)) = ∏_i μ(u_i)²/φ(u_i)·∏_{i≠j}μ(s_ij)/φ(s_ij)²`
(with the `∏ φ(u_i)` prefactors of `PrimeGaps.lToY (boldA)`, `PrimeGaps.lToY (boldB)` absorbing
the extra `φ`), and the reindexing of
`PrimeGaps.lToY` 's internal `tsum` against the `(d,e)` freedom.
-/
theorem sigmaRestr_eq_yWeightedSum {k : ℕ} (Rb : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) (D : Finset (Fin k → ℕ))
    (hD : ∀ d, lam d ≠ 0 → d ∈ D) :
    SigmaRestr D lam = yWeightedSum lam := by
  rw [sigmaRestr_eq_reindexed Rb W lam hs D, ← yWeightedSum_eq_reindexed Rb W lam hs D hD]

/-- Squarefreeness of `∏ i, t i` upgrades `HasPermissibleSupport` to
`HasPositivePairwiseCoprimeSupport`. -/
theorem hasPositivePairwiseCoprimeSupport_of_hasPermissibleSupport {k : ℕ} (Rb : ℝ) (W : ℕ)
    (lam : (Fin k → ℕ) →₀ ℝ) (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) :
    HasPositivePairwiseCoprimeSupport lam := by
  classical
  intro t ht
  refine ⟨fun i ↦ Nat.one_le_iff_ne_zero.mpr (hs.ne_zero_of_ne_zero ht i), ?_⟩
  intro i j hij
  have hdvd : (t i * t j) ∣ ∏ x, t x := by
    have := Finset.prod_dvd_prod_of_subset ({i, j} : Finset (Fin k)) Finset.univ t
      (Finset.subset_univ _)
    rwa [Finset.prod_pair hij] at this
  exact Nat.coprime_of_squarefree_mul ((hs.squarefree_prod_of_ne_zero ht).squarefree_of_dvd hdvd)

/-- `primedSum W lam = yWeightedSum lam` for `lam` with permissible support. -/
theorem primedSum_eq_yWeightedSum {k : ℕ} (Rb : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) :
    primedSum W lam = yWeightedSum lam := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : Finset (Fin k → ℕ), ∀ d, lam d ≠ 0 → d ∈ D := by
    refine ⟨Fintype.piFinset (fun _ ↦ Finset.Iic ⌊Rb⌋₊), ?_⟩
    intro d hd
    have hle := (Finset.mem_permissibleSupport_iff.mp (hs (Finsupp.mem_support_iff.mpr hd))).1
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Iic]
    exact le_trans (Finset.single_le_prod'
      (fun j _ ↦ Nat.one_le_iff_ne_zero.mpr (hs.ne_zero_of_ne_zero hd j)) (Finset.mem_univ i)) hle
  rw [← sigmaFull_eq_primedSum Rb W lam hs D hD,
    ← lem_S1_restrict_sij D lam
      (hasPositivePairwiseCoprimeSupport_of_hasPermissibleSupport Rb W lam hs),
    sigmaRestr_eq_yWeightedSum Rb W lam hs D hD]

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Let `k ≥ 2`, let `h: Fin k → ℕ` be admissible. Fix `θ ∈ (0,1)`, `δ ∈ (0, θ/2)`, and assume
`Nat.HasLevelOfDistribution Set.univ θ 1`. Use the paper parameters `R` and `W N`. Then
there exists `C > 0` and a threshold `N₀` such that for every `N ≥ N₀`, every weight `λ` with
`λ.HasPermissibleSupport ⌊R⌋₊ W`, and every `v0` with `V0Valid h W v0`,
`|S₁(h, λ, N, W, v0) - (N/W) · yWeightedSum(W, λ)|
  ≤ C · Finsupp.maxRealAbs (PrimeGaps.lToY λ) ² · φ(W)^k · N · (log R)^k /
    (W^{k+1} · D₀(N))`.
-/
@[pg_tag "bg246" "lem_S1_substitute_y"]
theorem lem_S1_substitute_y {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h) :
    ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      ∀ lam : (Fin k → ℕ) →₀ ℝ, lam.HasPermissibleSupport ⌊R⌋₊ (W N) →
      ∀ v0 : ℕ, V0Valid h (W N) v0 →
        |S1 h lam N (W N) v0 - (N / (W N : ℝ)) * yWeightedSum lam| ≤
          C * (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 * (Nat.totient (W N) : ℝ) ^ k * N *
            (Real.log (R)) ^ k /
              ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ N) := by
  intro θ δ hθ hδ
  obtain ⟨C, hCpos, N₀, hN₀⟩ := main_S1_asymptotic hk h hadm θ δ hθ hδ
  refine ⟨C, hCpos, N₀, ?_⟩
  intro N hN lam hlam v0 hv0
  have hbound := hN₀ N hN lam hlam v0 hv0
  rwa [primedSum_eq_yWeightedSum R (W N) lam hlam] at hbound

end PrimeGaps
