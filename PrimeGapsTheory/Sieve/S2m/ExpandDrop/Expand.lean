/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.SijD0.FirstMoment
public import PrimeGapsTheory.Sieve.S1.DropUij
public import PrimeGapsTheory.Sieve.S2m.GCoord
public import PrimeGapsTheory.Sieve.S2m.SecondMoment

/-!
# Expansion of the second-moment sum

Expands the transformed second-moment sum into its triple-sum form and identifies the
diagonal part with `coupledSum`.

## Main results

* `decoupledSum`, `coupledSum`: the two triple sums produced by expanding `S₂^{(m)}`.
* `lem_S2m_guard_factor`: factors the squarefree/coprimality guard through the `m`-th coordinate.
* `lem_S2m_LHS_eq_triple`, `lem_S2m_triple_comm`: reorganise the diagonal sum as a triple sum.
* `lem_S2m_expand_diag_eq_coupled`: identifies the diagonal sum with `coupledSum`.
-/

@[expose] public section

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

/-- `∑ p ∈ S, 1 / p ^ 2 ≤ A / D` for an absolute `A ≥ 0`, whenever `2 ≤ D` and every `p ∈ S`
exceeds `D`. -/
theorem prime_tail_inv_sub_two_sq :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (D : ℕ), 2 ≤ D → ∀ (S : Finset ℕ), (∀ p ∈ S, D < p) →
      ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ A / (D : ℝ) := by
  obtain ⟨A, hA, hbound⟩ := tail_sum_one_over_sq
  exact ⟨A, hA.le, hbound⟩

/-- Every coordinate of a point of the simplex `𝓡 k` is at most `1`. -/
theorem mem_R_coord_le_one {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (hx : x ∈ 𝓡 k) :
    ∀ i, x i ≤ 1 := by
  rw [EuclideanSpace.mem_scaledStdSimplex_iff] at hx
  exact fun i ↦ (Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)).trans hx.2

/-- Support truncation: if `Function.support F ⊆ 𝓡 k` and `F` is nonzero at
`fun j ↦ log (ρ[m ↦ u] j) / log R`, then `ρ[m ↦ u] i ≤ R` for every `i`. -/
theorem support_truncates_update_coord {k : ℕ} (R : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hsupp : Function.support F ⊆ 𝓡 k)
    (hR : 1 < R) (m : Fin k) (ρ : Fin k → ℕ) (u : ℕ)
    (hu : 0 < u) (hρ : ∀ i, i ≠ m → 1 ≤ ρ i)
    (hFne : F (WithLp.toLp 2 (fun j ↦ Real.log ((Function.update ρ m u) j : ℝ) / Real.log R)) ≠ 0) :
    ∀ i, ((Function.update ρ m u) i : ℝ) ≤ R := by
  intro i
  have hnpos : (0 : ℝ) < ((Function.update ρ m u) i : ℝ) := by
    rcases eq_or_ne i m with rfl | hi
    · rw [Function.update_self]; exact_mod_cast hu
    · rw [Function.update_of_ne hi]
      exact_mod_cast Nat.zero_lt_one.trans_le (hρ i hi)
  exact (Real.log_le_log_iff hnpos (zero_lt_one.trans hR)).mp ((div_le_one (Real.log_pos hR)).mp
    (mem_R_coord_le_one _ (hsupp (Function.mem_support.mpr hFne)) i))

/-- `∑' u u' ρ, F(log ρ[m ↦ u]/log R) * F(log ρ[m ↦ u']/log R) / (φ u * φ u' * ∏_{i≠m} g (ρ i))`
over `ρ m = 1` with `u`, `u'`, `ρ i` squarefree and coprime to `W`, and no coprimality imposed
between the variables. -/
noncomputable def decoupledSum {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) : ℝ :=
  ∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), if (ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧
        Squarefree u ∧ Squarefree u' ∧
        (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i))) then
      (1 / ((u.totient : ℝ) * (u'.totient : ℝ))) *
      (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) *
      F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u) i : ℝ) / Real.log R)) *
      F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u') i : ℝ) / Real.log R))
    else 0

/-- `decoupledSum` with the coupling `(u * u', ρ i) = 1` and `(ρ i, ρ j) = 1` also imposed; the
sum produced by expanding the second moment `S₂^{(m)}`. -/
noncomputable def coupledSum {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) : ℝ :=
  ∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), if (ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧
        Squarefree u ∧ Squarefree u' ∧
        (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i)) ∧
        (∀ i, i ≠ m → (u * u').Coprime (ρ i)) ∧ (∀ i j, i ≠ j → (ρ i).Coprime (ρ j))) then
      (1 / ((u.totient : ℝ) * (u'.totient : ℝ))) *
      (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) *
      F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u) i : ℝ) / Real.log R)) *
      F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u') i : ℝ) / Real.log R))
    else 0

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `yInverseSum (l₀ R (W N) F) m r = ∑' a, F(log r[m ↦ a] / log R) / φ a`, guarded by
`∏ i, r[m ↦ a] i` squarefree and coprime to `W N`. -/
theorem lem_S2m_yInverseSum_smooth_expand {k : ℕ} (hk : 2 ≤ k) (N : ℕ) (hN : 0 < N)
    (δ θ : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k) (m : Fin k)
    (r : Fin k → ℕ) :
    yInverseSum (PrimeGaps.l₀ (R) (W N) (fun x ↦
      F (WithLp.toLp 2 x.ofLp))) m r =
      ∑' a : ℕ, (if Squarefree (∏ i, (Function.update r m a) i) ∧
            (∏ i, (Function.update r m a) i).Coprime (W N)
          then F (WithLp.toLp 2 fun i ↦ Real.log ((Function.update r m a) i : ℝ) /
              Real.log (R)) else 0) / (a.totient : ℝ) := by
  unfold yInverseSum
  congr 1
  ext a
  rw [MaynardSmoothY.y_from_lambda_smooth R (W N) F hk
    (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) hF.continuous hsupp]

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `fun a ↦ lToY (l₀ R (W N) F) (r[m ↦ a])` has finite support. -/
theorem lem_S2m_inner_a_support_finite {k : ℕ} (N : ℕ) (δ θ : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) (r : Fin k → ℕ) :
    (Function.support (fun a : ℕ ↦ (PrimeGaps.lToY (PrimeGaps.l₀ (R)
        (W N) F)) (Function.update r m a))).Finite := by
  have hp : Finsupp.HasPermissibleSupport ⌊R⌋₊ (W N) (PrimeGaps.lToY (PrimeGaps.l₀ (R) (W N) F)) :=
    (PrimeGaps.hasPermissibleSupport_y₀ (F := F)).yToL.lToY
  have hinj : Function.Injective (fun a : ℕ ↦ Function.update r m a) :=
    fun a b hab ↦ by simpa using congrFun hab m
  exact ((Finset.permissibleSupport k ⌊R⌋₊ (W N)).finite_toSet.preimage hinj.injOn).subset
    fun a ha ↦ hp.support_subset (Finsupp.mem_support_iff.mpr ha)

/-- For `r i` (`i ≠ m`) squarefree, coprime to `W` and pairwise coprime, `∏ i, r[m ↦ a] i` is
squarefree and coprime to `W` iff `a` is squarefree, coprime to `W`, and coprime to each `r i`. -/
theorem lem_S2m_guard_factor {k : ℕ} (W : ℕ) (m : Fin k) (r : Fin k → ℕ) (a : ℕ)
    (hsq : ∀ i, i ≠ m → Squarefree (r i))
    (hcopW : ∀ i, i ≠ m → (r i).Coprime W)
    (hpair : ∀ i j, i ≠ j → i ≠ m → j ≠ m → (r i).Coprime (r j)) :
    (Squarefree (∏ i, (Function.update r m a) i) ∧ (∏ i, (Function.update r m a) i).Coprime W) ↔
    (Squarefree a ∧ a.Coprime W ∧ (∀ i, i ≠ m → a.Coprime (r i))) := by
  have hprod : (∏ i, (Function.update r m a) i) = a * ∏ i ∈ Finset.univ \ {m}, r i :=
    Finset.prod_update_of_mem (Finset.mem_univ m) r a
  set P := ∏ i ∈ Finset.univ \ {m}, r i with hP
  have hsqP : Squarefree P := by
    rw [hP]
    exact Finset.squarefree_prod_of_pairwise_isCoprime
      (fun i hi j hj hij ↦ Nat.coprime_iff_isRelPrime.mp
        (hpair i j hij (by simpa using hi) (by simpa using hj)))
      fun i hi ↦ hsq i (by simpa using hi)
  have hcopPW : P.Coprime W := by
    rw [hP]
    exact Nat.Coprime.prod_left fun i hi ↦ hcopW i (by simpa using hi)
  have hcopaP : a.Coprime P ↔ (∀ i, i ≠ m → a.Coprime (r i)) := by
    rw [hP, Nat.coprime_prod_right_iff]
    exact ⟨fun h i hi ↦ h i (by simp [hi]), fun h i hi ↦ h i (by simpa using hi)⟩
  rw [hprod, Nat.squarefree_mul_iff, Nat.coprime_mul_iff_left]
  exact ⟨fun ⟨⟨hcop, hsqa, _⟩, haW, _⟩ ↦ ⟨hsqa, haW, hcopaP.mp hcop⟩,
    fun ⟨hsqa, haW, hcopr⟩ ↦ ⟨⟨hcopaP.mpr hcopr, hsqa, hsqP⟩, haW, hcopPW⟩⟩

/-- The summand of `coupledSum` at `(ρ, u, u')`. -/
noncomputable def S2mTerm {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) (ρ : Fin k → ℕ) (u u' : ℕ) : ℝ :=
  if (ρ m = 1 ∧ u.Coprime W ∧ u'.Coprime W ∧
      Squarefree u ∧ Squarefree u' ∧ (∀ i, i ≠ m → (ρ i).Coprime W ∧ Squarefree (ρ i)) ∧
      (∀ i, i ≠ m → (u * u').Coprime (ρ i)) ∧ (∀ i j, i ≠ j → (ρ i).Coprime (ρ j))) then
    (1 / ((u.totient : ℝ) * (u'.totient : ℝ))) *
    (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (ρ i) : ℝ)) *
    F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u) i : ℝ) / Real.log R)) *
    F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u') i : ℝ) / Real.log R))
  else 0

/-- `coupledSum R W F m = ∑' u, ∑' u', ∑' ρ, S2mTerm R W F m ρ u u'`. -/
theorem lem_S2m_coupledSum_eq_triple {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (m : Fin k) :
    coupledSum R W F m =
      ∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), S2mTerm R W F m ρ u u' := rfl

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `(yInverseSum (l₀ R (W N) F) m r) ^ 2` as the double sum over `u, u'` of the product of the two
guarded terms `F(log r[m ↦ u] / log R) / φ u`. -/
theorem lem_S2m_Y_sq_expand {k : ℕ} (hk : 2 ≤ k) (N : ℕ) (hN : 0 < N)
    (δ θ : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k) (m : Fin k)
    (r : Fin k → ℕ) :
    (yInverseSum (PrimeGaps.l₀ (R) (W N) (fun x ↦
      F (WithLp.toLp 2 x.ofLp))) m r) ^ 2 =
      ∑' (u : ℕ), ∑' (u' : ℕ), ((if Squarefree (∏ i, (Function.update r m u) i) ∧
              (∏ i, (Function.update r m u) i).Coprime (W N)
            then F (WithLp.toLp 2 fun i ↦ Real.log ((Function.update r m u) i : ℝ) /
                Real.log (R)) else 0) / (u.totient : ℝ)) *
          ((if Squarefree (∏ i, (Function.update r m u') i) ∧
              (∏ i, (Function.update r m u') i).Coprime (W N)
            then F (WithLp.toLp 2 fun i ↦ Real.log ((Function.update r m u') i : ℝ) /
                Real.log (R)) else 0) / (u'.totient : ℝ)) := by
  rw [lem_S2m_yInverseSum_smooth_expand hk N hN δ θ F hF hsupp m r]
  let summand : ℕ → ℝ := fun a ↦ (if Squarefree (∏ i, (Function.update r m a) i) ∧
          (∏ i, (Function.update r m a) i).Coprime (W N)
        then F (WithLp.toLp 2 fun i ↦ Real.log ((Function.update r m a) i : ℝ) /
            Real.log (R)) else 0) / (a.totient : ℝ)
  have hfin : (Function.support summand).Finite := by
    refine (lem_S2m_inner_a_support_finite (k := k) N δ θ
      (fun x ↦ F (WithLp.toLp 2 x.ofLp)) m r).subset fun a ha ↦ ?_
    simp only [Function.mem_support] at ha ⊢
    rw [MaynardSmoothY.y_from_lambda_smooth R (W N) F hk
      (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) hF.continuous hsupp]
    exact fun hzero ↦ ha (by simp only [summand, hzero, zero_div])
  have hns : Summable (fun a ↦ ‖summand a‖) :=
    summable_of_hasFiniteSupport (hfin.subset fun a ha ↦ by simpa using ha)
  change (∑' a, summand a) ^ 2 = ∑' u, ∑' u', summand u * summand u'
  rw [sq, tsum_mul_tsum_of_summable_norm hns hns,
    (Summable.of_norm (hns.mul_norm hns)).tsum_prod]
end PrimeGaps

namespace Nat

/-- If `∏ i ∈ s, f i` is squarefree then each `f i` is squarefree and the `f i` are pairwise
coprime. -/
theorem sqfree_finset_extract {ι : Type*} {s : Finset ι} {f : ι → ℕ}
    (h : Squarefree (∏ i ∈ s, f i)) :
    (∀ i ∈ s, Squarefree (f i)) ∧ (∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).Coprime (f j)) := by
  classical
  refine ⟨fun i hi ↦ ?_, fun i hi j hj hij ↦ ?_⟩
  · rw [← Finset.mul_prod_erase s f hi] at h
    exact (Nat.squarefree_mul_iff.mp h).2.1
  · rw [← Finset.mul_prod_erase s f hi,
      ← Finset.mul_prod_erase (s.erase i) f (Finset.mem_erase.mpr ⟨hij.symm, hj⟩)] at h
    exact Nat.Coprime.coprime_dvd_right (dvd_mul_right (f j) _) (Nat.squarefree_mul_iff.mp h).1

end Nat

namespace PrimeGaps

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The diagonal sum `∑' r, (yInverseSum … m r) ^ 2 / ∏_{i ≠ m} g (r i)` equals
`∑' r, ∑' u, ∑' u', S2mTerm R (W N) F m r u u'`. -/
theorem lem_S2m_LHS_eq_triple {k : ℕ} (hk : 2 ≤ k) (N : ℕ) (hN : 0 < N)
    (δ θ : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k) (m : Fin k) :
    (∑' r : Fin k → ℕ, if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) then
          (yInverseSum (PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp))) m r) ^ 2 /
            (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ))
        else 0) = ∑' (r : Fin k → ℕ), ∑' (u : ℕ), ∑' (u' : ℕ), S2mTerm R (W N) F m r u u' := by
  refine tsum_congr fun r ↦ ?_
  by_cases hg : r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N))
  · rw [if_pos hg]
    obtain ⟨hrm, hr⟩ := hg
    rw [lem_S2m_Y_sq_expand hk N hN δ θ F hF hsupp m r, ← tsum_div_const]
    refine tsum_congr fun u ↦ ?_
    rw [← tsum_div_const]
    refine tsum_congr fun u' ↦ ?_
    set Δ := (r m = 1 ∧ u.Coprime (W N) ∧ u'.Coprime (W N) ∧ Squarefree u ∧ Squarefree u' ∧
        (∀ i, i ≠ m → (r i).Coprime (W N) ∧ Squarefree (r i)) ∧
        (∀ i, i ≠ m → (u * u').Coprime (r i)) ∧ (∀ i j, i ≠ j → (r i).Coprime (r j)))
    set Gu := (Squarefree (∏ i, (Function.update r m u) i) ∧
        (∏ i, (Function.update r m u) i).Coprime (W N))
    set Gu' := (Squarefree (∏ i, (Function.update r m u') i) ∧
        (∏ i, (Function.update r m u') i).Coprime (W N))
    have hkey : ∀ v : ℕ, ∀ hd : Δ, Squarefree v → v.Coprime (W N) →
        (∀ i, i ≠ m → v.Coprime (r i)) → Squarefree (∏ i, (Function.update r m v) i) ∧
          (∏ i, (Function.update r m v) i).Coprime (W N) :=
      fun v hd hsqv hcopv hcoprv ↦ (lem_S2m_guard_factor (W N) m r v
        (fun i hi ↦ (hd.2.2.2.2.2.1 i hi).2)
        (fun i hi ↦ (hd.2.2.2.2.2.1 i hi).1)
        (fun i j hij _ _ ↦ hd.2.2.2.2.2.2.2 i j hij)).mpr ⟨hsqv, hcopv, hcoprv⟩
    have hΔ_Gu : Δ → Gu := fun hd ↦ hkey u hd hd.2.2.2.1 hd.2.1
      fun i hi ↦ Nat.Coprime.coprime_dvd_left (dvd_mul_right u u') (hd.2.2.2.2.2.2.1 i hi)
    have hΔ_Gu' : Δ → Gu' := fun hd ↦ hkey u' hd hd.2.2.2.2.1 hd.2.2.1
      fun i hi ↦ Nat.Coprime.coprime_dvd_left (dvd_mul_left u' u) (hd.2.2.2.2.2.2.1 i hi)
    rw [show S2mTerm R (W N) F m r u u' = if Δ then
            (1 / ((u.totient : ℝ) * (u'.totient : ℝ))) *
            (∏ i ∈ Finset.univ.erase m, (1 : ℝ) / (g (r i) : ℝ)) *
            F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update r m u) i : ℝ) / Real.log (R))) *
            F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update r m u') i : ℝ) / Real.log (R)))
          else 0 from by rw [S2mTerm]]
    by_cases hGuv : Gu ∧ Gu'
    · obtain ⟨hGuh, hGu'h⟩ := hGuv
      have hsqP : Squarefree (∏ i ∈ Finset.univ \ {m}, r i) :=
        (Nat.squarefree_mul_iff.mp (Finset.prod_update_of_mem (Finset.mem_univ m) r u ▸ hGuh.1)).2.2
      obtain ⟨hsqeach, hpaireach⟩ := Nat.sqfree_finset_extract hsqP
      have hsq_off : ∀ i, i ≠ m → Squarefree (r i) :=
        fun i hi ↦ hsqeach i (by simp [Finset.mem_sdiff, hi])
      have hpair_off : ∀ i j, i ≠ j → i ≠ m → j ≠ m → (r i).Coprime (r j) := fun i j hij hi hj ↦
          hpaireach i (by simp [Finset.mem_sdiff, hi]) j (by simp [Finset.mem_sdiff, hj]) hij
      obtain ⟨hsqu, hcopuW, hcopu_r⟩ :=
        (lem_S2m_guard_factor (W N) m r u hsq_off (fun i hi ↦ (hr i hi).2) hpair_off).mp hGuh
      obtain ⟨hsqu', hcopu'W, hcopu'_r⟩ :=
        (lem_S2m_guard_factor (W N) m r u' hsq_off (fun i hi ↦ (hr i hi).2) hpair_off).mp hGu'h
      have hpair_all : ∀ i j, i ≠ j → (r i).Coprime (r j) := by
        intro i j hij
        rcases eq_or_ne i m with rfl | hi
        · rw [hrm]; exact Nat.coprime_one_left _
        rcases eq_or_ne j m with rfl | hj
        · rw [hrm]; exact Nat.coprime_one_right _
        exact hpair_off i j hij hi hj
      have hΔh : Δ :=
        ⟨hrm, hcopuW, hcopu'W, hsqu, hsqu', fun i hi ↦ ⟨(hr i hi).2, hsq_off i hi⟩,
          fun i hi ↦ Nat.coprime_mul_iff_left.mpr ⟨hcopu_r i hi, hcopu'_r i hi⟩, hpair_all⟩
      rw [if_pos hΔh, if_pos hGuh, if_pos hGu'h, Finset.prod_div_distrib]
      simp only [Finset.prod_const_one, one_div]
      field_simp
    · rw [not_and_or] at hGuv
      rw [if_neg (fun hd ↦ hGuv.elim (· (hΔ_Gu hd)) (· (hΔ_Gu' hd)))]
      rcases hGuv with h | h <;> (rw [if_neg h]; simp)
  · rw [if_neg hg]
    symm
    have hzero : ∀ u u' : ℕ, S2mTerm R (W N) F m r u u' = 0 := fun u u' ↦
      if_neg fun hd ↦ hg ⟨hd.1, fun i hi ↦
        ⟨Nat.pos_of_ne_zero (hd.2.2.2.2.2.1 i hi).2.ne_zero, (hd.2.2.2.2.2.1 i hi).1⟩⟩
    simp only [hzero, tsum_zero]

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- **Finiteness of the `S2mTerm` support.**  The map `(r, u, u') ↦ (update r m u,
update r m u')` is injective on the support of `S2mTerm` and lands in the square of the
(finite) support of the `y`-weights, so the support is finite. -/
private theorem support_S2mTerm_finite {k : ℕ} (hk : 2 ≤ k) (N : ℕ) (hN : 0 < N) (δ θ : ℝ)
    (m : Fin k)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k) :
    (Function.support (fun p : (Fin k → ℕ) × ℕ × ℕ ↦
      S2mTerm R (W N) F m p.1 p.2.1 p.2.2)).Finite := by
  set Y : (Fin k → ℕ) → ℝ := fun s ↦ (PrimeGaps.lToY (PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) s
  have hstar : ∀ s : Fin k → ℕ, Y s = (if Squarefree (∏ i, s i) ∧ (∏ i, s i).Coprime (W N)
        then F (WithLp.toLp 2 fun i ↦ Real.log (s i : ℝ) / Real.log (R)) else 0) := fun s ↦
    MaynardSmoothY.y_from_lambda_smooth R (W N) F hk
      (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) hF.continuous hsupp s
  have hTfin : (Function.support Y).Finite := by
    have hp : Finsupp.HasPermissibleSupport ⌊R⌋₊ (W N) (PrimeGaps.lToY (PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp)))) :=
      (PrimeGaps.hasPermissibleSupport_y₀ (F := fun x ↦ F (WithLp.toLp 2 x.ofLp))).yToL.lToY
    exact (Finset.permissibleSupport k ⌊R⌋₊ (W N)).finite_toSet.subset fun s hs ↦
      hp.support_subset (Finsupp.mem_support_iff.mpr hs)
  set f : (Fin k → ℕ) × ℕ × ℕ → ℝ := fun p ↦ S2mTerm R (W N) F m p.1 p.2.1 p.2.2 with hf
  have hguard : ∀ (r : Fin k → ℕ) (u u' : ℕ), S2mTerm R (W N) F m r u u' ≠ 0 →
      (r m = 1 ∧ u.Coprime (W N) ∧ u'.Coprime (W N) ∧ Squarefree u ∧ Squarefree u' ∧
        (∀ i, i ≠ m → (r i).Coprime (W N) ∧ Squarefree (r i)) ∧
        (∀ i, i ≠ m → (u * u').Coprime (r i)) ∧ (∀ i j, i ≠ j → (r i).Coprime (r j))) :=
    fun r u u' hne ↦ not_not.mp fun hΔ ↦ hne (by unfold S2mTerm; rw [if_neg hΔ])
  have hYupd : ∀ (r : Fin k → ℕ) (v : ℕ), (r m = 1 ∧ v.Coprime (W N) ∧ Squarefree v ∧
        (∀ i, i ≠ m → (r i).Coprime (W N) ∧ Squarefree (r i)) ∧
        (∀ i, i ≠ m → v.Coprime (r i)) ∧ (∀ i j, i ≠ j → (r i).Coprime (r j))) →
      F (WithLp.toLp 2 fun i ↦ Real.log ((Function.update r m v) i : ℝ) / Real.log (R)) ≠ 0 →
      Y (Function.update r m v) ≠ 0 := by
    intro r v hΔv hFne
    rw [hstar, if_pos ((lem_S2m_guard_factor (W N) m r v
      (fun i hi ↦ (hΔv.2.2.2.1 i hi).2) (fun i hi ↦ (hΔv.2.2.2.1 i hi).1)
      (fun i j hij _ _ ↦ hΔv.2.2.2.2.2 i j hij)).mpr ⟨hΔv.2.2.1, hΔv.2.1, hΔv.2.2.2.2.1⟩)]
    exact hFne
  set Φ : (Fin k → ℕ) × ℕ × ℕ → (Fin k → ℕ) × (Fin k → ℕ) :=
    fun p ↦ (Function.update p.1 m p.2.1, Function.update p.1 m p.2.2) with hΦ
  have hinj : Set.InjOn Φ (Function.support f) := by
    intro p hp q hq hpq
    simp only [Function.mem_support, hf] at hp hq
    have hΔp := hguard p.1 p.2.1 p.2.2 hp
    have hΔq := hguard q.1 q.2.1 q.2.2 hq
    simp only [hΦ, Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    have hu1 : p.2.1 = q.2.1 := by
      have := congrFun h1 m
      rwa [Function.update_self, Function.update_self] at this
    have hu2 : p.2.2 = q.2.2 := by
      have := congrFun h2 m
      rwa [Function.update_self, Function.update_self] at this
    have hr : p.1 = q.1 := by
      funext i
      by_cases hi : i = m
      · rw [hi, hΔp.1, hΔq.1]
      · have := congrFun h1 i
        rwa [Function.update_of_ne hi, Function.update_of_ne hi] at this
    exact Prod.ext hr (Prod.ext hu1 hu2)
  refine Set.Finite.of_finite_image ((hTfin.prod hTfin).subset
    (Set.image_subset_iff.mpr fun p hp ↦ ?_)) hinj
  simp only [Function.mem_support, hf] at hp
  simp only [Set.mem_preimage, hΦ, Set.mem_prod, Function.mem_support]
  have hΔ := hguard p.1 p.2.1 p.2.2 hp
  have hFu : F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update p.1 m p.2.1) i : ℝ) /
            Real.log (R))) ≠ 0 := fun h0 ↦ hp (by unfold S2mTerm; rw [if_pos hΔ, h0]; ring)
  have hFu' : F (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update p.1 m p.2.2) i : ℝ) /
            Real.log (R))) ≠ 0 := fun h0 ↦ hp (by unfold S2mTerm; rw [if_pos hΔ, h0]; ring)
  exact ⟨hYupd p.1 p.2.1 ⟨hΔ.1, hΔ.2.1, hΔ.2.2.2.1, hΔ.2.2.2.2.2.1,
      fun i hi ↦ Nat.Coprime.coprime_dvd_left (dvd_mul_right p.2.1 p.2.2)
        (hΔ.2.2.2.2.2.2.1 i hi), hΔ.2.2.2.2.2.2.2⟩ hFu,
    hYupd p.1 p.2.2 ⟨hΔ.1, hΔ.2.2.1, hΔ.2.2.2.2.1, hΔ.2.2.2.2.2.1,
      fun i hi ↦ Nat.Coprime.coprime_dvd_left (dvd_mul_left p.2.2 p.2.1)
        (hΔ.2.2.2.2.2.2.1 i hi), hΔ.2.2.2.2.2.2.2⟩ hFu'⟩

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Summing `S2mTerm` in the order `r, u, u'` gives the same value as in the order `u, u', ρ`. -/
theorem lem_S2m_triple_comm {k : ℕ} (hk : 2 ≤ k) (N : ℕ) (hN : 0 < N) (δ θ : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k) (m : Fin k) :
    (∑' (r : Fin k → ℕ), ∑' (u : ℕ), ∑' (u' : ℕ), S2mTerm R (W N) F m r u u') =
      ∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), S2mTerm R (W N) F m ρ u u' := by
  set f : (Fin k → ℕ) × ℕ × ℕ → ℝ := fun p ↦ S2mTerm R (W N) F m p.1 p.2.1 p.2.2
  have hfsum : Summable f :=
    summable_of_hasFiniteSupport (support_S2mTerm_finite hk N hN δ θ m F hF hsupp)
  let e : ℕ × ℕ × (Fin k → ℕ) ≃ (Fin k → ℕ) × ℕ × ℕ :=
    { toFun := fun p ↦ (p.2.2, (p.1, p.2.1))
      invFun := fun p ↦ (p.2.1, (p.2.2, p.1))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hgsum : Summable fun p ↦ f (e p) := hfsum.comp_injective e.injective
  have hLHS : (∑' (r : Fin k → ℕ), ∑' (u : ℕ), ∑' (u' : ℕ), S2mTerm R (W N) F m r u u') =
      ∑' p, f p := by
    rw [hfsum.tsum_prod]
    exact tsum_congr fun r ↦ ((hfsum.prod_factor r).tsum_prod).symm
  have hRHS : (∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), S2mTerm R (W N) F m ρ u u') =
      ∑' p, f (e p) := by
    rw [hgsum.tsum_prod]
    exact tsum_congr fun u ↦ ((hgsum.prod_factor u).tsum_prod).symm
  rw [hLHS, hRHS]
  exact (Equiv.tsum_eq e f).symm

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The diagonal sum `∑' r, (yInverseSum … m r) ^ 2 / ∏_{i ≠ m} g (r i)` equals
`coupledSum R (W N) F m`. -/
theorem lem_S2m_expand_diag_eq_coupled {k : ℕ} (hk : 2 ≤ k) (N : ℕ) (hN : 0 < N)
    (δ θ : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k) (m : Fin k) :
    (∑' r : Fin k → ℕ, if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) then
          (yInverseSum (PrimeGaps.l₀ (R)
        (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp))) m r) ^ 2 /
            (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ))
        else 0) = coupledSum R (W N) F m := by
  rw [lem_S2m_LHS_eq_triple hk N hN δ θ F hF hsupp m, lem_S2m_triple_comm hk N hN δ θ F hF hsupp m,
    ← lem_S2m_coupledSum_eq_triple R (W N) F m]

end PrimeGaps
