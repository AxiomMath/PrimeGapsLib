/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.ExpandDrop.Expand

/-!
# The decoupled term and its majorant

Introduces `S2mDecTerm`, `failureMass` and the `aSum`/`bSum`/`cSum`/`gSum` family, and
bounds the decoupling error by the failure mass.

## Main results

* `PrimeGaps.S2mDecTerm`
* `PrimeGaps.failureMass`
* `PrimeGaps.drop_difference_le_failure_mass`
* `PrimeGaps.gSum`, `PrimeGaps.aSum`, `PrimeGaps.bSum`, `PrimeGaps.cSum`
* `PrimeGaps.abs_S2mDecTerm_le_prod`
* `PrimeGaps.tsum_aSum_eq_sumA`, `PrimeGaps.tsum_cSum_eq_gSum`, `PrimeGaps.tsum_bSum_eq`
-/

@[expose] public section

open scoped ArithmeticFunction.detotient
open PrimeGaps

namespace PrimeGaps

/-- The summand of `decoupledSum` at `(ρ, u, u')`, i.e. `S2mTerm` with the coprimality coupling
between the variables dropped. -/
noncomputable def S2mDecTerm {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) (ρ : Fin k → ℕ) (u u' : ℕ) : ℝ :=
  if (ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧ Squarefree u ∧ Squarefree u' ∧
      (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i))) then
    (1 / ((u.totient : ℝ) * (u'.totient : ℝ))) *
    (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) *
    F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u) i : ℝ) / Real.log R)) *
    F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u') i : ℝ) / Real.log R))
  else 0

end PrimeGaps

/-- `∑' u, ∑' u', ∑' ρ, h ρ u u' = ∑' p : ℕ × ℕ × (Fin k → ℕ), h p.2.2 p.1 p.2.1`, for `h` with
finite flattened support. -/
theorem PrimeGaps.triple_tsum_eq_prod {k : ℕ} (h : (Fin k → ℕ) → ℕ → ℕ → ℝ)
    (hfin : (Function.support (fun p : ℕ × ℕ × (Fin k → ℕ) ↦ h p.2.2 p.1 p.2.1)).Finite) :
    (∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), h ρ u u') =
      ∑' p : ℕ × ℕ × (Fin k → ℕ), h p.2.2 p.1 p.2.1 := by
  have hsum : Summable (fun p : ℕ × ℕ × (Fin k → ℕ) ↦ h p.2.2 p.1 p.2.1) :=
    summable_of_hasFiniteSupport hfin
  exact (hsum.tsum_prod.trans (tsum_congr fun u ↦ (hsum.prod_factor u).tsum_prod)).symm

/-- `fun (u, u', ρ) ↦ S2mDecTerm R W F m ρ u u'` has finite support. -/
theorem PrimeGaps.S2mDecTerm_flat_support_finite {k : ℕ} (R : ℝ) (W : ℕ) (hR : 1 < R)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 k) (m : Fin k) :
    (Function.support (fun p : ℕ × ℕ × (Fin k → ℕ) ↦
      S2mDecTerm R W F m p.2.2 p.1 p.2.1)).Finite := by
  refine Set.Finite.subset (Finset.finite_toSet ((Finset.Iic ⌊R⌋₊) ×ˢ (Finset.Iic ⌊R⌋₊) ×ˢ
    (Fintype.piFinset (fun _ : Fin k ↦ Finset.Iic ⌊R⌋₊)))) fun p hp ↦ ?_
  simp only [Function.mem_support, S2mDecTerm] at hp
  split_ifs at hp with hΔ
  swap
  · exact absurd rfl hp
  have hFu : F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update p.2.2 m p.1) i : ℝ) /
      Real.log R)) ≠ 0 := fun h0 ↦ hp (by rw [h0]; ring)
  have hFu' : F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update p.2.2 m p.2.1) i : ℝ) /
      Real.log R)) ≠ 0 := fun h0 ↦ hp (by rw [h0]; ring)
  have hρge : ∀ i, i ≠ m → 1 ≤ p.2.2 i :=
    fun i hi ↦ Nat.pos_of_ne_zero (hΔ.2.2.2.2.2 i hi).2.ne_zero
  have hcoordu := PrimeGaps.support_truncates_update_coord R F hsupp hR m p.2.2 p.1
    (Nat.pos_of_ne_zero hΔ.2.2.2.1.ne_zero) hρge hFu
  have hcoordu' := PrimeGaps.support_truncates_update_coord R F hsupp hR m p.2.2 p.2.1
    (Nat.pos_of_ne_zero hΔ.2.2.2.2.1.ne_zero) hρge hFu'
  have hρle : ∀ i, p.2.2 i ≤ ⌊R⌋₊ := fun i ↦ by
    by_cases hi : i = m
    · rw [hi, hΔ.1]; exact Nat.le_floor (by exact_mod_cast hR.le)
    · exact Nat.le_floor (by simpa only [Function.update_of_ne hi] using hcoordu i)
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Iic, Set.mem_Iic,
    Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ, true_implies]
  exact ⟨Nat.le_floor (by simpa using hcoordu m), Nat.le_floor (by simpa using hcoordu' m), hρle⟩

/-- `fun (u, u', ρ) ↦ S2mTerm R W F m ρ u u'` has finite support. -/
theorem PrimeGaps.S2mTerm_flat_support_finite {k : ℕ} (R : ℝ) (W : ℕ)
    (hR : 1 < R) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 k) (m : Fin k) :
    (Function.support (fun p : ℕ × ℕ × (Fin k → ℕ) ↦
      S2mTerm R W F m p.2.2 p.1 p.2.1)).Finite := by
  refine (PrimeGaps.S2mDecTerm_flat_support_finite R W hR F hsupp m).subset fun p hp ↦ ?_
  simp only [Function.mem_support, S2mTerm, S2mDecTerm] at hp ⊢
  split_ifs at hp with hfull
  · rwa [if_pos ⟨hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2.1,
      hfull.2.2.2.2.2.1⟩]
  · exact absurd rfl hp

namespace PrimeGaps

/-- `∑' u, ∑' u', ∑' ρ, |S2mTerm - S2mDecTerm|`, the mass carried by the terms on which the
coprimality coupling fails. -/
noncomputable def failureMass {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) : ℝ :=
  ∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ),
    |S2mTerm R W F m ρ u u' - S2mDecTerm R W F m ρ u u'|

/-- `decoupledSum R W F m = ∑' u, ∑' u', ∑' ρ, S2mDecTerm R W F m ρ u u'`. -/
theorem decoupledSum_eq_triple {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) :
    decoupledSum R W F m =
      ∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), S2mDecTerm R W F m ρ u u' :=
  rfl

/-- `failureMass R W F m = ∑' u, ∑' u', ∑' ρ, |S2mTerm - S2mDecTerm|`. -/
theorem failureMass_eq_triple {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) :
    failureMass R W F m = ∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ),
          |S2mTerm R W F m ρ u u' - S2mDecTerm R W F m ρ u u'| :=
  rfl

/-- `|coupledSum R W F m - decoupledSum R W F m| ≤ failureMass R W F m`. -/
theorem drop_difference_le_failure_mass {k : ℕ} (R : ℝ) (W : ℕ) (hR : 1 < R)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 k) (m : Fin k) :
    |coupledSum R W F m - decoupledSum R W F m| ≤ failureMass R W F m := by
  set T' : ℕ × ℕ × (Fin k → ℕ) → ℝ := fun p ↦ S2mTerm R W F m p.2.2 p.1 p.2.1
  set D' : ℕ × ℕ × (Fin k → ℕ) → ℝ := fun p ↦ S2mDecTerm R W F m p.2.2 p.1 p.2.1
  have hTfin : (Function.support T').Finite :=
    PrimeGaps.S2mTerm_flat_support_finite R W hR F hsupp m
  have hDfin : (Function.support D').Finite :=
    PrimeGaps.S2mDecTerm_flat_support_finite R W hR F hsupp m
  have hTsum : Summable T' := summable_of_hasFiniteSupport hTfin
  have hDsum : Summable D' := summable_of_hasFiniteSupport hDfin
  have hdiff_fin : (Function.support (fun p ↦ |T' p - D' p|)).Finite :=
    (hTfin.union hDfin).subset fun p hp ↦ by
      by_contra hnot
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hnot
      exact hp (by simp [hnot.1, hnot.2])
  have hdiff_sum : Summable (fun p ↦ |T' p - D' p|) := summable_of_hasFiniteSupport hdiff_fin
  have hC : coupledSum R W F m = ∑' p, T' p := by
    rw [lem_S2m_coupledSum_eq_triple R W F m]
    exact PrimeGaps.triple_tsum_eq_prod (S2mTerm R W F m) hTfin
  have hD : decoupledSum R W F m = ∑' p, D' p := by
    rw [decoupledSum_eq_triple R W F m]
    exact PrimeGaps.triple_tsum_eq_prod (S2mDecTerm R W F m) hDfin
  have hFM : failureMass R W F m = ∑' p, |T' p - D' p| := by
    rw [failureMass_eq_triple R W F m]
    exact PrimeGaps.triple_tsum_eq_prod
      (fun ρ u u' ↦ |S2mTerm R W F m ρ u u' - S2mDecTerm R W F m ρ u u'|) hdiff_fin
  rw [hC, hD, hFM, ← Summable.tsum_sub hTsum hDsum]
  simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun p ↦ T' p - D' p)
    (by simpa only [Real.norm_eq_abs] using hdiff_sum)

end PrimeGaps

/-- `|S2mTerm - S2mDecTerm|` is `|S2mDecTerm|` on the terms passing the base guard but failing the
coprimality coupling, and `0` elsewhere. -/
theorem PrimeGaps.abs_diff_eq {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) (ρ : Fin k → ℕ) (u u' : ℕ) :
    |S2mTerm R W F m ρ u u' - S2mDecTerm R W F m ρ u u'| =
      if ((ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧ Squarefree u ∧ Squarefree u' ∧
            (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i))) ∧
          ¬((∀ i, i ≠ m → (u * u').Coprime (ρ i)) ∧ (∀ i j, i ≠ j → (ρ i).Coprime (ρ j))))
        then |S2mDecTerm R W F m ρ u u'| else 0 := by
  unfold S2mTerm S2mDecTerm
  by_cases hbase : (ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧ Squarefree u ∧ Squarefree u' ∧
            (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i)))
  · by_cases hcoup : ((∀ i, i ≠ m → (u * u').Coprime (ρ i)) ∧ (∀ i j, i ≠ j → (ρ i).Coprime (ρ j)))
    · rw [if_pos (show (ρ m = 1 ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) from
          ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1, hbase.2.2.2.2.1,
            hbase.2.2.2.2.2, hcoup.1, hcoup.2⟩),
        if_pos hbase, if_neg (show ¬ (_ ∧ ¬ (_ ∧ _)) from fun h ↦ h.2 hcoup), sub_self, abs_zero]
    · rw [if_neg (show ¬ (ρ m = 1 ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ (∀ i, i ≠ m → (u * u').Coprime (ρ i)) ∧
            (∀ i j, i ≠ j → (ρ i).Coprime (ρ j))) from fun h ↦ hcoup ⟨h.2.2.2.2.2.2.1,
              h.2.2.2.2.2.2.2⟩),
        if_pos hbase, if_pos (show (_ ∧ ¬ (_ ∧ _)) from ⟨hbase, hcoup⟩), zero_sub, abs_neg]
  · rw [if_neg (show ¬ (ρ m = 1 ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) from fun h ↦
          hbase ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩),
      if_neg hbase, if_neg (show ¬ (_ ∧ ¬ (_ ∧ _)) from fun h ↦ hbase h.1), sub_zero, abs_zero]

/-- The canonical free-coordinate sum in its equivalent indicator-sum presentation. -/
theorem PrimeGaps.sumA_eq_ite_sum (W : ℕ) (X : ℝ) : PrimeGaps.MaynardOffDiagonal.sumA W X =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        if Squarefree n ∧ n.Coprime W then 1 / (n.totient : ℝ) else 0 := by
  unfold PrimeGaps.MaynardOffDiagonal.sumA PrimeGaps.MaynardOffDiagonal.Sset
  rw [Finset.sum_filter]

/-- `gSum W X = ∑_{1 ≤ n ≤ X, n squarefree, (n, W) = 1} 1 / g n`. -/
noncomputable def PrimeGaps.gSum (W : ℕ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (if Squarefree n ∧ n.Coprime W then 1 / (g n : ℝ) else 0)

/-- `gSum` is nonnegative: every summand is either `1 / g n` with `g n ≥ 0`, or `0`. -/
theorem PrimeGaps.gSum_nonneg (W : ℕ) (X : ℝ) : (0 : ℝ) ≤ PrimeGaps.gSum W X := by
  refine Finset.sum_nonneg fun n _ ↦ ?_
  positivity

/-- `aSum W X n = 1 / φ n` for `n ≤ X` squarefree and coprime to `W`, and `0` otherwise. -/
noncomputable def PrimeGaps.aSum (W : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n ∧ n.Coprime W ∧ n ≤ ⌊X⌋₊ then 1 / (n.totient : ℝ) else 0

/-- `cSum W X n = 1 / g n` for `n ≤ X` squarefree and coprime to `W`, and `0` otherwise. -/
noncomputable def PrimeGaps.cSum (W : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n ∧ n.Coprime W ∧ n ≤ ⌊X⌋₊ then 1 / (g n : ℝ) else 0

/-- `bSum W X m ρ = ∏_{i ≠ m} cSum W X (ρ i)` when `ρ m = 1`, and `0` otherwise. -/
noncomputable def PrimeGaps.bSum {k : ℕ} (W : ℕ) (X : ℝ) (m : Fin k) (ρ : Fin k → ℕ) : ℝ :=
  if ρ m = 1 then ∏ i ∈ Finset.univ.erase m, PrimeGaps.cSum W X (ρ i) else 0

/-- `0 ≤ aSum W X n`. -/
theorem PrimeGaps.aSum_nonneg (W : ℕ) (X : ℝ) (n : ℕ) : (0 : ℝ) ≤ PrimeGaps.aSum W X n := by
  rw [PrimeGaps.aSum]; positivity

/-- `0 ≤ bSum W X m ρ`. -/
theorem PrimeGaps.bSum_nonneg {k : ℕ} (W : ℕ) (X : ℝ) (m : Fin k) (ρ : Fin k → ℕ) :
    (0 : ℝ) ≤ PrimeGaps.bSum W X m ρ := by
  rw [PrimeGaps.bSum]
  split
  · exact Finset.prod_nonneg fun n _ ↦ by rw [PrimeGaps.cSum]; positivity
  · exact le_rfl

/-- `fun ρ ↦ bSum W X m ρ` is summable: `bSum` vanishes unless every coordinate is at most
`⌊X⌋₊`, so its support sits inside a product of finite intervals. -/
theorem PrimeGaps.bSum_summable {k : ℕ} (W : ℕ) (X : ℝ) (m : Fin k) :
    Summable (fun ρ : Fin k → ℕ ↦ PrimeGaps.bSum W X m ρ) := by
  refine summable_of_hasFiniteSupport (Set.Finite.subset
    (Set.Finite.pi fun _ : Fin k ↦ Set.finite_Icc 0 (⌊X⌋₊ + 1)) fun u hu ↦ ?_)
  simp only [Function.mem_support] at hu
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  refine fun i ↦ ⟨Nat.zero_le _, ?_⟩
  by_contra hlt
  push Not at hlt
  refine hu ?_
  unfold PrimeGaps.bSum
  by_cases hm : u m = 1
  · rw [if_pos hm]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨by rintro rfl; omega, Finset.mem_univ i⟩)
      (if_neg (by rintro ⟨-, -, hle⟩; omega))
  · rw [if_neg hm]

/-- `|S2mDecTerm R W F m ρ u u'| ≤ Fmax F ^ 2 * aSum W R u * aSum W R u' * bSum W R m ρ`. -/
theorem PrimeGaps.abs_S2mDecTerm_le_prod {k : ℕ} (R : ℝ) (W : ℕ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k)
    (hR : 1 < R) (m : Fin k) (ρ : Fin k → ℕ) (u u' : ℕ) :
    |S2mDecTerm R W F m ρ u u'| ≤ (MaynardSmoothY.Fmax F) ^ 2 * PrimeGaps.aSum W R u *
      PrimeGaps.aSum W R u' * PrimeGaps.bSum W R m ρ := by
  have hRHS_nonneg : (0 : ℝ) ≤ (MaynardSmoothY.Fmax F) ^ 2 *
      PrimeGaps.aSum W R u * PrimeGaps.aSum W R u' * PrimeGaps.bSum W R m ρ := by
    have := PrimeGaps.aSum_nonneg W R u
    have := PrimeGaps.aSum_nonneg W R u'
    have := PrimeGaps.bSum_nonneg W R m ρ
    positivity
  by_cases hne : S2mDecTerm R W F m ρ u u' = 0
  · rw [hne, abs_zero]
    exact hRHS_nonneg
  have hΔ : (ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧ Squarefree u ∧ Squarefree u' ∧
      (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i))) := by
    by_contra hΔ
    exact hne (if_neg hΔ)
  have hcoeff : S2mDecTerm R W F m ρ u u' = (1 / ((u.totient : ℝ) * (u'.totient : ℝ))) *
      (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) *
      F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u) i : ℝ) / Real.log R)) *
      F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u') i : ℝ) / Real.log R)) :=
    if_pos hΔ
  rw [hcoeff] at hne
  set Fu := F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u) i : ℝ) / Real.log R))
    with hFudef
  set Fu' := F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u') i : ℝ) / Real.log R))
    with hFu'def
  have hFu : Fu ≠ 0 := fun h0 ↦ hne (by rw [h0]; ring)
  have hFu' : Fu' ≠ 0 := fun h0 ↦ hne (by rw [h0]; ring)
  have hupos : 0 < u := Nat.pos_of_ne_zero hΔ.2.2.2.1.ne_zero
  have hu'pos : 0 < u' := Nat.pos_of_ne_zero hΔ.2.2.2.2.1.ne_zero
  have hρge : ∀ i, i ≠ m → 1 ≤ ρ i := fun i hi ↦ Nat.pos_of_ne_zero (hΔ.2.2.2.2.2 i hi).2.ne_zero
  have hRpos : (0 : ℝ) < R := zero_lt_one.trans hR
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hcoordu := PrimeGaps.support_truncates_update_coord R F hsupp hR m ρ u hupos hρge
    (by rwa [← hFudef])
  have hcoordu' := PrimeGaps.support_truncates_update_coord R F hsupp hR m ρ u' hu'pos hρge
    (by rwa [← hFu'def])
  have hule : (u : ℝ) ≤ R := by simpa using hcoordu m
  have hu'le : (u' : ℝ) ≤ R := by simpa using hcoordu' m
  have hρfloor : ∀ i, i ≠ m → ρ i ≤ ⌊R⌋₊ :=
    fun i hi ↦ Nat.le_floor (by simpa only [Function.update_of_ne hi] using hcoordu i)
  have haSumu : PrimeGaps.aSum W R u = 1 / (u.totient : ℝ) :=
    if_pos ⟨hΔ.2.2.2.1, hΔ.2.1, Nat.le_floor hule⟩
  have haSumu' : PrimeGaps.aSum W R u' = 1 / (u'.totient : ℝ) :=
    if_pos ⟨hΔ.2.2.2.2.1, hΔ.2.2.1, Nat.le_floor hu'le⟩
  have hbSum : PrimeGaps.bSum W R m ρ = ∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ) := by
    rw [PrimeGaps.bSum, if_pos hΔ.1]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    have hi := (Finset.mem_erase.mp hi).1
    exact if_pos ⟨(hΔ.2.2.2.2.2 i hi).2, (hΔ.2.2.2.2.2 i hi).1, hρfloor i hi⟩
  have hbox : ∀ (ww : ℕ), 0 < ww → (ww : ℝ) ≤ R →
      ∀ i, (WithLp.toLp 2 (fun j ↦ Real.log ((Function.update ρ m ww) j : ℝ) /
        Real.log R)).ofLp i ∈ Set.Icc (0 : ℝ) 1 := by
    intro ww hwpos hwle i
    have hge : (1 : ℝ) ≤ ((Function.update ρ m ww) i : ℝ) := by
      by_cases hi : i = m
      · rw [hi, Function.update_self]; exact_mod_cast hwpos
      · rw [Function.update_of_ne hi]; exact_mod_cast hρge i hi
    have hle : ((Function.update ρ m ww) i : ℝ) ≤ R := by
      by_cases hi : i = m
      · rw [hi, Function.update_self]; exact hwle
      · rw [Function.update_of_ne hi]
        exact (Nat.cast_le.mpr (hρfloor i hi)).trans (Nat.floor_le hRpos.le)
    exact ⟨div_nonneg (Real.log_nonneg hge) hlogR.le,
      (div_le_one hlogR).mpr (Real.log_le_log (by linarith) hle)⟩
  have hFu_le : |Fu| ≤ MaynardSmoothY.Fmax F := by
    rw [hFudef]
    exact MaynardSmoothY.abs_F_le_Fmax F hF (hbox u hupos hule)
  have hFu'_le : |Fu'| ≤ MaynardSmoothY.Fmax F := by
    rw [hFu'def]
    exact MaynardSmoothY.abs_F_le_Fmax F hF (hbox u' hu'pos hu'le)
  have hFmax_nonneg : (0 : ℝ) ≤ MaynardSmoothY.Fmax F := (abs_nonneg _).trans hFu_le
  rw [hcoeff, haSumu, haSumu', hbSum, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 1 / ((u.totient : ℝ) * (u'.totient : ℝ)) by positivity),
    abs_of_nonneg (Finset.prod_nonneg fun i _ ↦ by positivity :
      (0 : ℝ) ≤ ∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ))]
  calc 1 / ((u.totient : ℝ) * (u'.totient : ℝ)) *
        (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) * |Fu| * |Fu'| ≤
      1 / ((u.totient : ℝ) * (u'.totient : ℝ)) *
        (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) *
        (MaynardSmoothY.Fmax F) * (MaynardSmoothY.Fmax F) := by
        gcongr
    _ = (MaynardSmoothY.Fmax F) ^ 2 * (1 / (u.totient : ℝ)) * (1 / (u'.totient : ℝ)) *
        (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) := by
        rw [one_div_mul_eq_div]; ring

/-- `fun (u, u', ρ) ↦ C * aSum W X u * aSum W X u' * bSum W X m ρ` has finite support. -/
theorem PrimeGaps.prod_flat_support_finite {k : ℕ} (W : ℕ) (X : ℝ) (C : ℝ) (m : Fin k) :
    (Function.support (fun p : ℕ × ℕ × (Fin k → ℕ) ↦
      C * PrimeGaps.aSum W X p.1 * PrimeGaps.aSum W X p.2.1 *
        PrimeGaps.bSum W X m p.2.2)).Finite := by
  have haSum_guard : ∀ n : ℕ, PrimeGaps.aSum W X n ≠ 0 →
      (Squarefree n ∧ n.Coprime W ∧ n ≤ ⌊X⌋₊) := fun n hne ↦ by
    by_contra h
    exact hne (if_neg h)
  have hcSum_guard : ∀ n : ℕ, PrimeGaps.cSum W X n ≠ 0 →
      (Squarefree n ∧ n.Coprime W ∧ n ≤ ⌊X⌋₊) := fun n hne ↦ by
    by_contra h
    exact hne (if_neg h)
  refine Set.Finite.subset (Finset.finite_toSet ((Finset.Iic ⌊X⌋₊) ×ˢ (Finset.Iic ⌊X⌋₊) ×ˢ
    (Fintype.piFinset (fun _ : Fin k ↦ Finset.Iic ⌊X⌋₊)))) fun p hp ↦ ?_
  simp only [Function.mem_support] at hp
  have haU : PrimeGaps.aSum W X p.1 ≠ 0 := fun h0 ↦ hp (by rw [h0]; ring)
  have haU' : PrimeGaps.aSum W X p.2.1 ≠ 0 := fun h0 ↦ hp (by rw [h0]; ring)
  have hbρ : PrimeGaps.bSum W X m p.2.2 ≠ 0 := fun h0 ↦ hp (by rw [h0]; ring)
  have hule : p.1 ≤ ⌊X⌋₊ := (haSum_guard p.1 haU).2.2
  have hM1 : 1 ≤ ⌊X⌋₊ := le_trans (Nat.pos_of_ne_zero (haSum_guard p.1 haU).1.ne_zero) hule
  have hbdef : PrimeGaps.bSum W X m p.2.2 =
      if p.2.2 m = 1 then ∏ i ∈ Finset.univ.erase m, PrimeGaps.cSum W X (p.2.2 i) else 0 := rfl
  have hρm : p.2.2 m = 1 := by
    by_contra hne
    exact hbρ (by rw [hbdef, if_neg hne])
  have hprodne : (∏ i ∈ Finset.univ.erase m, PrimeGaps.cSum W X (p.2.2 i)) ≠ 0 :=
    fun h0 ↦ hbρ (by rwa [hbdef, if_pos hρm])
  have hρle : ∀ i, p.2.2 i ≤ ⌊X⌋₊ := fun i ↦ by
    by_cases hi : i = m
    · rw [hi, hρm]; exact hM1
    · exact (hcSum_guard _ (Finset.prod_ne_zero_iff.mp hprodne i
        (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩))).2.2
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Iic, Set.mem_Iic,
    Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ, true_implies]
  exact ⟨hule, (haSum_guard p.2.1 haU').2.2, hρle⟩

/-- A weight vanishing off the squarefree `n ≤ X` coprime to `W` sums to the finite sum over
`Icc 1 ⌊X⌋₊`, where the bound is automatic. -/
theorem PrimeGaps.tsum_guard_eq (W : ℕ) (X : ℝ) (f : ℕ → ℝ) :
    (∑' n : ℕ, if Squarefree n ∧ n.Coprime W ∧ n ≤ ⌊X⌋₊ then f n else 0) =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (if Squarefree n ∧ n.Coprime W then f n else 0) := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊X⌋₊)]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [Finset.mem_Icc] at hn
    simp only [hn.2, and_true]
  · intro n hn
    rw [Finset.mem_Icc, not_and_or] at hn
    exact if_neg fun h ↦ hn.elim (fun h1 ↦ h1 h.1.ne_zero.bot_lt) fun h2 ↦ h2 h.2.2

/-- `∑' n, aSum W X n = sumA W X`. -/
theorem PrimeGaps.tsum_aSum_eq_sumA (W : ℕ) (X : ℝ) :
    (∑' (n : ℕ), PrimeGaps.aSum W X n) = PrimeGaps.MaynardOffDiagonal.sumA W X := by
  rw [PrimeGaps.sumA_eq_ite_sum]
  simpa only [PrimeGaps.aSum] using PrimeGaps.tsum_guard_eq W X fun n ↦ 1 / (n.totient : ℝ)

/-- `∑' n, cSum W X n = gSum W X`. -/
theorem PrimeGaps.tsum_cSum_eq_gSum (W : ℕ) (X : ℝ) :
    (∑' (n : ℕ), PrimeGaps.cSum W X n) = PrimeGaps.gSum W X := by
  rw [PrimeGaps.gSum]
  simpa only [PrimeGaps.cSum] using PrimeGaps.tsum_guard_eq W X fun n ↦ 1 / (g n : ℝ)

/-- `∑' ρ, bSum W X m ρ = (gSum W X) ^ (k - 1)`, one factor per non-free coordinate. -/
theorem PrimeGaps.tsum_bSum_eq {k : ℕ} (W : ℕ) (X : ℝ) (m : Fin k) :
    (∑' (ρ : Fin k → ℕ), PrimeGaps.bSum W X m ρ) = (PrimeGaps.gSum W X) ^ (k - 1) := by
  have hsupp : ∀ (_ : Fin k) (n : ℕ), PrimeGaps.cSum W X n ≠ 0 → n ≤ ⌊X⌋₊ := fun _ n hne ↦ by
    by_contra h
    exact hne (if_neg fun hguard ↦ h hguard.2.2)
  rw [show (∑' (ρ : Fin k → ℕ), PrimeGaps.bSum W X m ρ) = ∑' (ρ : Fin k → ℕ),
            if ρ m = 1 then ∏ i ∈ Finset.univ.erase m, PrimeGaps.cSum W X (ρ i) else 0
      from rfl,
    tsum_pin_coord_prod ⌊X⌋₊ m (fun _ ↦ PrimeGaps.cSum W X) hsupp,
    Finset.prod_congr rfl fun i _ ↦ PrimeGaps.tsum_cSum_eq_gSum W X, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
