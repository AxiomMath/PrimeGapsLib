/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Separation.CompletelyRegular
public import PrimeGapsTheory.NumberTheory.Admissible
public import PrimeGapsTheory.NumberTheory.LevelOfDistribution
public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeDensity
public import PrimeGapsTheory.Sieve.Transforms.YmAjNeRj

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The distinguished transform in terms of the primary transform

Expresses the distinguished-coordinate transform through a totient-weighted sum of primary
transformed weights.

## Main definitions

* `yInverseSum`: The totient-weighted sum over the free coordinate.
* `retainedL`: Cuts off a primary transform and transforms it back.
* `discardedL`: The complementary divisor weight.
* `crFactor`: The `r`-only diagonal factor left over after collapsing the diagonal sum.

## Main results

* `ym_eq_diag_plus_offdiag`: Splits the distinguished transform into a diagonal term and an
  off-diagonal sum.
* `maynard_ym_identity`: Approximates the distinguished transform by the free-coordinate
  inverse sum.
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius
open scoped Finset

open scoped ArithmeticFunction.detotient

open scoped BigOperators
open ArithmeticFunction Moebius detotient

namespace PrimeGaps

/-- The totient-weighted sum over the free coordinate `a_m` appearing on the right-hand side of the
identity: `∑_{a_m} y_{r₁,…,a_m,…,r_k} / φ(a_m)`. The summation variable `a_m` ranges over `ℕ`;
since `PrimeGaps.lToY l` is a `Finsupp`, all but finitely many terms vanish and the `tsum` is a
finite sum. The `a_m = 0` term is `0` under Lean's `x/0 = 0` convention. -/
noncomputable def yInverseSum {k : ℕ} (l : (Fin k → ℕ) →₀ ℝ) (m : Fin k) (r : Fin k → ℕ) : ℝ :=
  ∑' a : ℕ, (PrimeGaps.lToY l) (Function.update r m a) / (Nat.totient a : ℝ)

/-- The product cutoff on all coordinates other than `m`. -/
noncomputable def outerProductCutoff {k : ℕ} (B : ℝ) (m : Fin k) (r : Fin k → ℕ) : Prop :=
  (∏ i ∈ Finset.univ.erase m, (r i : ℝ)) ≤ B

open Classical in
/-- The part of `lToY L` satisfying the outer-coordinate product cutoff. -/
noncomputable def retainedY {k : ℕ} (B : ℝ) (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ) : (Fin k → ℕ) →₀ ℝ :=
  (PrimeGaps.lToY L).filter (outerProductCutoff B m)

/-- The divisor weight obtained by transforming the retained primary transform back. -/
noncomputable def retainedL {k : ℕ} (B : ℝ) (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ) : (Fin k → ℕ) →₀ ℝ :=
  PrimeGaps.yToL (retainedY B m L)

/-- The complementary divisor weight. -/
noncomputable def discardedL {k : ℕ} (B : ℝ) (m : Fin k)
    (L : (Fin k → ℕ) →₀ ℝ) : (Fin k → ℕ) →₀ ℝ :=
  L - retainedL B m L

open Classical in
/-- `retainedY B m L r = lToY L r` on the cutoff region, and `0` off it. -/
theorem retainedY_apply {k : ℕ} (B : ℝ) (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ) (r : Fin k → ℕ) :
    retainedY B m L r = if outerProductCutoff B m r then PrimeGaps.lToY L r else 0 := by
  simp [retainedY, Finsupp.filter_apply]

open Classical in
/-- Transforming the retained divisor weight recovers its retained primary transform. -/
theorem lToY_retainedL {k : ℕ} (B : ℝ) (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ) (r : Fin k → ℕ) :
    PrimeGaps.lToY (retainedL B m L) r = retainedY B m L r := by
  rw [retainedL, PrimeGaps.lToY_yToL]
  split_ifs with hsq
  · rfl
  · symm
    by_contra hyr0
    refine hsq fun i ↦ PrimeGaps.squarefree_of_lToY_ne_zero (l := L) (i := i) fun hz ↦ hyr0 ?_
    rw [retainedY_apply, hz]
    split <;> simp

open Classical in
/-- Cutting off does not increase the sup-norm of the primary transform. -/
theorem maxRealAbs_retainedL_le {k : ℕ} (B : ℝ) (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ) :
    (PrimeGaps.lToY (retainedL B m L)).maxRealAbs ≤
      (PrimeGaps.lToY L).maxRealAbs := by
  rw [Finsupp.maxRealAbs_le_iff]
  intro r
  rw [lToY_retainedL, retainedY_apply]
  split_ifs
  · exact Finsupp.le_maxRealAbs
  · simp

open Classical in
/-- The retained divisor weight satisfies the sharp outer-coordinate product cutoff. -/
theorem retainedL_outer_support {k : ℕ} (B : ℝ) (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ) (d : Fin k → ℕ)
    (hd : retainedL B m L d ≠ 0) :
    (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) ≤ B := by
  rw [retainedL, PrimeGaps.yToL_apply', mul_ne_zero_iff] at hd
  obtain ⟨r, hrmem, hrterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd.2
  dsimp only at hrterm
  split_ifs at hrterm with hdr
  · have hcut : outerProductCutoff B m r := by
      by_contra h
      exact Finsupp.mem_support_iff.mp hrmem (by rw [retainedY_apply, if_neg h])
    refine le_trans (Finset.prod_le_prod (fun i _ ↦ by positivity) fun i _ ↦ ?_) hcut
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (hdr i).2.ne_zero) (hdr i).1
  · simp at hrterm

/-- The retained and discarded divisor weights recombine to `L`. -/
theorem retainedL_add_discardedL {k : ℕ} (B : ℝ) (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ) :
    retainedL B m L + discardedL B m L = L := by
  simp [discardedL]

open Classical in
/-- `lToY (discardedL B m L) r = 0` on the cutoff region, and `lToY L r` off it. -/
theorem lToY_discardedL {k : ℕ} (B : ℝ) (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ) (r : Fin k → ℕ) :
    PrimeGaps.lToY (discardedL B m L) r =
      if outerProductCutoff B m r then 0 else PrimeGaps.lToY L r := by
  rw [discardedL, LinearMap.map_sub, Finsupp.sub_apply, lToY_retainedL, retainedY_apply]
  split_ifs <;> simp

open Classical in
/-- Discarding does not increase the sup-norm of the primary transform. -/
theorem maxRealAbs_discardedL_le {k : ℕ} (B : ℝ) (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ) :
    (PrimeGaps.lToY (discardedL B m L)).maxRealAbs ≤
      (PrimeGaps.lToY L).maxRealAbs := by
  rw [Finsupp.maxRealAbs_le_iff]
  intro r
  rw [lToY_discardedL]
  split_ifs
  · simp
  · exact Finsupp.le_maxRealAbs

open Classical in
/-- The cutoff ignores the distinguished coordinate, so it is unaffected by changing `r` at `m`. -/
theorem outerProductCutoff_update_m {k : ℕ} (B : ℝ) (m : Fin k) (r : Fin k → ℕ) (a : ℕ) :
    outerProductCutoff B m (Function.update r m a) ↔ outerProductCutoff B m r := by
  unfold outerProductCutoff
  rw [Finset.prod_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]

open Classical in
/-- The retained inverse marginal is the unsplit marginal on the cutoff region. -/
theorem yInverseSum_retainedL {k : ℕ} (B : ℝ) (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ) (r : Fin k → ℕ) :
    yInverseSum (retainedL B m L) m r =
      if outerProductCutoff B m r then yInverseSum L m r else 0 := by
  unfold yInverseSum
  simp_rw [lToY_retainedL, retainedY_apply, outerProductCutoff_update_m]
  split_ifs <;> simp

open Classical in
/-- `yInverseSum (discardedL B m L) m r = 0` on the cutoff region, `yInverseSum L m r` off it. -/
theorem yInverseSum_discardedL {k : ℕ} (B : ℝ) (m : Fin k) (L : (Fin k → ℕ) →₀ ℝ) (r : Fin k → ℕ) :
    yInverseSum (discardedL B m L) m r =
      if outerProductCutoff B m r then 0 else yInverseSum L m r := by
  unfold yInverseSum
  simp_rw [lToY_discardedL, outerProductCutoff_update_m]
  split_ifs <;> simp

open Classical in
/-- Restricting the primary transform to the cutoff region preserves permissible support. -/
theorem retainedY_hasPermissibleSupport {k R W : ℕ} (B : ℝ) (m : Fin k)
    (L : (Fin k → ℕ) →₀ ℝ) (hL : L.HasPermissibleSupport R W) :
    (retainedY B m L).HasPermissibleSupport R W := by
  intro r hr
  apply hL.lToY
  rw [Finsupp.mem_support_iff] at hr ⊢
  rw [retainedY_apply] at hr
  split_ifs at hr
  · exact hr
  · simp at hr

/-- The retained divisor weight inherits permissible support from `L`. -/
theorem retainedL_hasPermissibleSupport {k R W : ℕ} (B : ℝ) (m : Fin k)
    (L : (Fin k → ℕ) →₀ ℝ) (hL : L.HasPermissibleSupport R W) :
    (retainedL B m L).HasPermissibleSupport R W :=
  (retainedY_hasPermissibleSupport B m L hL).yToL

/-- The discarded divisor weight inherits permissible support from `L`. -/
theorem discardedL_hasPermissibleSupport {k R W : ℕ} (B : ℝ) (m : Fin k)
    (L : (Fin k → ℕ) →₀ ℝ) (hL : L.HasPermissibleSupport R W) :
    (discardedL B m L).HasPermissibleSupport R W := by
  refine Finsupp.HasPermissibleSupport.of_forall fun d hd ↦ ?_
  have hor : L d ≠ 0 ∨ retainedL B m L d ≠ 0 := by
    by_contra h
    push Not at h
    exact hd (by simp [discardedL, h.1, h.2])
  rcases hor with hbase | hret
  · exact Finset.mem_permissibleSupport_iff.mp (hL (Finsupp.mem_support_iff.mpr hbase))
  · exact Finset.mem_permissibleSupport_iff.mp
      (retainedL_hasPermissibleSupport B m L hL (Finsupp.mem_support_iff.mpr hret))

/-- The `r` -only diagonal factor `crFactor(m, r) = ∏_{i ≠ m} g(r_i) · r_i / φ(r_i)²`, arising
after collapsing the diagonal sum. For coordinatewise squarefree `r`, each per-prime factor is
`(p-2)·p / (p-1)² = 1 - 1/(p-1)²`, giving the perturbation controlled by `crFactor_sub_one_le`
below. -/
noncomputable def crFactor {k : ℕ} (m : Fin k) (r : Fin k → ℕ) : ℝ :=
  ∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ) * (r i : ℝ) / ((Nat.totient (r i) : ℝ)) ^ 2

/-- For `r m = 1`, the diagonal at `r` is the range of `Function.update r m`. -/
theorem diag_set_eq_range {k : ℕ} (m : Fin k) (r : Fin k → ℕ) (hrm : r m = 1) :
    {a : Fin k → ℕ | PrimeGaps.MaynardOffDiagonal.Diag m r a} =
      Set.range (Function.update r m) := by
  ext a
  constructor
  · rintro ⟨_, heq⟩
    refine ⟨a m, funext fun i ↦ ?_⟩
    rcases eq_or_ne i m with rfl | hi
    · simp
    · rw [Function.update_of_ne hi _ _, heq i hi]
  · rintro ⟨x, rfl⟩
    refine ⟨fun i ↦ ?_, fun i hi ↦ Function.update_of_ne hi _ _⟩
    rcases eq_or_ne i m with rfl | hi
    · simp [hrm]
    · rw [Function.update_of_ne hi]

/-- On the diagonal the summand factors:
`Tsummand y m r (Function.update r m x) = crFactor m r * (y (Function.update r m x) / φ x)`. -/
theorem Tsummand_update_eq {k : ℕ} (l : (Fin k → ℕ) →₀ ℝ)
    (m : Fin k) (r : Fin k → ℕ) (hrm : r m = 1) (hrsq : ∀ i, Squarefree (r i))
    (x : ℕ) :
    PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r
        (Function.update r m x) = crFactor m r * ((PrimeGaps.lToY l) (Function.update r m x) /
          (Nat.totient x : ℝ)) := by
  classical
  unfold PrimeGaps.MaynardOffDiagonal.Tsummand crFactor
  have hupd_ne : ∀ i, i ≠ m → (Function.update r m x) i = r i := fun i hi ↦
    Function.update_of_ne hi _ _
  have hprod_phi : (∏ i, (Nat.totient ((Function.update r m x) i) : ℝ)) =
      (Nat.totient x : ℝ) * ∏ i ∈ Finset.univ.erase m, (Nat.totient (r i) : ℝ) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), Function.update_self,
      Finset.prod_congr rfl fun i hi ↦ by rw [hupd_ne i (Finset.ne_of_mem_erase hi)]]
  have hprod_erase_upd : (∏ i ∈ Finset.univ.erase m,
      ((μ ((Function.update r m x) i) : ℝ) * (r i : ℝ)) /
        (Nat.totient ((Function.update r m x) i) : ℝ)) = ∏ i ∈ Finset.univ.erase m,
          ((μ (r i) : ℝ) * (r i : ℝ)) / (Nat.totient (r i) : ℝ) :=
    Finset.prod_congr rfl fun i hi ↦ by rw [hupd_ne i (Finset.ne_of_mem_erase hi)]
  have hpref_m_eq_one : (μ (r m) : ℝ) * (g (r m) : ℝ) = 1 := by
    rw [hrm, show μ 1 = 1 from ArithmeticFunction.moebius_apply_one,
      ArithmeticFunction.isMultiplicative_detotient.map_one]
    simp
  have hpref : (∏ i, (μ (r i) : ℝ) * (g (r i) : ℝ)) =
      ∏ i ∈ Finset.univ.erase m, (μ (r i) : ℝ) * (g (r i) : ℝ) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), hpref_m_eq_one, one_mul]
  rw [hpref, hprod_phi, hprod_erase_upd]
  have hmu2 : ∀ i ∈ Finset.univ.erase m, (μ (r i) : ℝ) ^ 2 = 1 :=
    fun i _ ↦ by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hrsq i)
  have hphi_pos : ∀ i, 0 < (Nat.totient (r i) : ℝ) := fun i ↦ by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hrsq i).ne_zero)
  set P : ℝ := ∏ i ∈ Finset.univ.erase m, (μ (r i) : ℝ) *
        (g (r i) : ℝ) with hP
  set Q : ℝ := ∏ i ∈ Finset.univ.erase m,
      ((μ (r i) : ℝ) * (r i : ℝ)) / (Nat.totient (r i) : ℝ) with hQ
  set S : ℝ := (Nat.totient x : ℝ) * ∏ i ∈ Finset.univ.erase m, (Nat.totient (r i) : ℝ) with hS
  have hphi_prod_ne : (∏ i ∈ Finset.univ.erase m, (Nat.totient (r i) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hphi_pos i).ne'
  have hPQ : P * Q = ∏ i ∈ Finset.univ.erase m,
      ((g (r i) : ℝ) * (r i : ℝ)) / (Nat.totient (r i) : ℝ) := by
    rw [hP, hQ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    have hring : (μ (r i) : ℝ) * (g (r i) : ℝ) *
        ((μ (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ)) =
      (μ (r i) : ℝ) ^ 2 *
          ((g (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ)) := by ring
    rw [hring, hmu2 i hi, one_mul]
  set y : ℝ := (PrimeGaps.lToY l) (Function.update r m x)
  have hstep1 : P * (y / S) * Q = P * Q * y / S := by ring
  rw [hstep1, hPQ, hS]
  have hcombine : (∏ i ∈ Finset.univ.erase m,
      (g (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2) = (∏ i ∈ Finset.univ.erase m,
          ((g (r i) : ℝ) * (r i : ℝ)) / (Nat.totient (r i) : ℝ)) /
        (∏ i ∈ Finset.univ.erase m, (Nat.totient (r i) : ℝ)) := by
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib, div_div, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun i _ ↦ by rw [sq]
  rw [hcombine]
  field_simp

/-- The diagonal sum collapses to `crFactor m r * yInverseSum l m r`. -/
theorem diag_sum_eq_crFactor_yInverseSum
    {k : ℕ} (l : (Fin k → ℕ) →₀ ℝ) (m : Fin k) (r : Fin k → ℕ)
    (hrm : r m = 1) (hrsq : ∀ i, Squarefree (r i)) :
    (∑ᶠ (a : Fin k → ℕ) (_ : PrimeGaps.MaynardOffDiagonal.Diag m r a),
        PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r a) =
      crFactor m r * yInverseSum l m r := by
  classical
  set S : Finset (Fin k → ℕ) := (PrimeGaps.lToY l).support with hSdef
  set T : Finset ℕ := S.preimage (Function.update r m)
      (Set.injOn_of_injective (Function.update_injective r m)) with hTdef
  have hT_mem : ∀ x, x ∈ T ↔ Function.update r m x ∈ S := fun x ↦ by
    rw [hTdef, Finset.mem_preimage]
  have hLHS : (∑ᶠ (a : Fin k → ℕ) (_ : PrimeGaps.MaynardOffDiagonal.Diag m r a),
        PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r a) =
      ∑ x ∈ T, crFactor m r *
          ((PrimeGaps.lToY l) (Function.update r m x) / (Nat.totient x : ℝ)) := by
    change (∑ᶠ a ∈ {a : Fin k → ℕ | PrimeGaps.MaynardOffDiagonal.Diag m r a},
      PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r a) = _
    rw [diag_set_eq_range m r hrm, finsum_mem_range (Function.update_injective r m)]
    simp_rw [Tsummand_update_eq l m r hrm hrsq]
    apply finsum_eq_finsetSum_of_support_subset
    intro x hx
    simp only [Function.mem_support] at hx
    rw [Finset.mem_coe, hT_mem, hSdef, Finsupp.mem_support_iff]
    exact fun hy0 ↦ hx (by rw [hy0, zero_div, mul_zero])
  have hRHS : yInverseSum l m r =
      ∑ x ∈ T, (PrimeGaps.lToY l) (Function.update r m x) / (Nat.totient x : ℝ) := by
    unfold yInverseSum
    refine tsum_eq_sum fun x hx ↦ ?_
    rw [show (PrimeGaps.lToY l) (Function.update r m x) = 0 from
      not_not.mp fun hne ↦ hx ((hT_mem x).mpr (Finsupp.mem_support_iff.mpr hne)), zero_div]
  rw [hLHS, hRHS, Finset.mul_sum]

/-- The summand of `PrimeGaps.lem_ym_intermediate` rearranges to `Tsummand`. -/
theorem intermediate_summand_eq_Tsummand
    {k : ℕ} {l : (Fin k → ℕ) →₀ ℝ} (m : Fin k) (r a : Fin k → ℕ) :
    (∏ i, (μ (r i) : ℝ) * (g (r i) : ℝ)) *
      ((PrimeGaps.lToY l a / (∏ i, (Nat.totient (a i) : ℝ))) *
        ∏ i ∈ Finset.univ.erase m, ((μ (a i) : ℝ) * (r i : ℝ)) /
            (Nat.totient (a i) : ℝ)) =
      PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r a := by
  unfold PrimeGaps.MaynardOffDiagonal.Tsummand
  ring

/-- `Tsummand` vanishes at a tuple with a zero coordinate, since then `∏ i, φ (a i) = 0`. -/
theorem Tsummand_eq_zero_of_zero_coord
    {k : ℕ} (l : (Fin k → ℕ) →₀ ℝ) (m : Fin k) (r a : Fin k → ℕ)
    (hz : ∃ i, a i = 0) :
    PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r a = 0 := by
  obtain ⟨i, hi⟩ := hz
  unfold PrimeGaps.MaynardOffDiagonal.Tsummand
  have hphi : (Nat.totient (a i) : ℝ) = 0 := by simp [hi]
  rw [show (∏ j, (Nat.totient (a j) : ℝ)) = 0 from Finset.prod_eq_zero (Finset.mem_univ i) hphi,
    div_zero, mul_zero, zero_mul]

/-- `ym m l r = crFactor m r * yInverseSum l m r` plus the off-diagonal sum of `Tsummand`. -/
theorem ym_eq_diag_plus_offdiag
    {k : ℕ} {l : (Fin k → ℕ) →₀ ℝ} {R : ℝ} {W : ℕ}
    (hl : l.HasPermissibleSupport ⌊R⌋₊ W)
    (m : Fin k) (r : Fin k → ℕ) (hr : ∀ i, 0 < r i) (hrm : r m = 1)
    (hrsq : ∀ i, Squarefree (r i)) :
    (PrimeGaps.ym m l) r = crFactor m r * yInverseSum l m r +
        ∑ᶠ (a : Fin k → ℕ) (_ : PrimeGaps.MaynardOffDiagonal.OffDiag m r a),
            PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r a := by
  classical
  rw [PrimeGaps.lem_ym_intermediate l hl m r hr hrm]
  set P : ℝ := ∏ i, (μ (r i) : ℝ) * (g (r i) : ℝ) with hPdef
  rw [mul_finsum]
  have hterm : ∀ a : Fin k → ℕ, P * (if (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i) then
        ((PrimeGaps.lToY l a / (∏ i, (Nat.totient (a i) : ℝ))) *
          ∏ i ∈ Finset.univ.erase m, ((μ (a i) : ℝ) * (r i : ℝ)) /
              (Nat.totient (a i) : ℝ))
      else 0) = if (∀ i, r i ∣ a i) then
          PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r a
        else 0 := by
    intro a
    by_cases hpos : ∀ i, 0 < a i
    · by_cases hdvd : ∀ i, r i ∣ a i
      · rw [if_pos ⟨hpos, hdvd⟩, if_pos hdvd, hPdef]
        exact intermediate_summand_eq_Tsummand m r a
      · rw [if_neg (fun h ↦ hdvd h.2), if_neg hdvd, mul_zero]
    · push Not at hpos
      obtain ⟨i, hi⟩ := hpos
      have hi' : a i = 0 := Nat.le_zero.mp hi
      rw [if_neg (fun h ↦ absurd (h.1 i) (by simp [hi'])), mul_zero]
      by_cases hdvd : ∀ i, r i ∣ a i
      · rw [if_pos hdvd]
        exact (Tsummand_eq_zero_of_zero_coord l m r a ⟨i, hi'⟩).symm
      · rw [if_neg hdvd]
  simp_rw [hterm]
  have hunion : {a : Fin k → ℕ | ∀ i, r i ∣ a i} =
      {a | PrimeGaps.MaynardOffDiagonal.Diag m r a} ∪
        {a | PrimeGaps.MaynardOffDiagonal.OffDiag m r a} :=
    Set.ext (PrimeGaps.MaynardOffDiagonal.diag_union_offDiag m r)
  have hdisj : Disjoint {a : Fin k → ℕ | PrimeGaps.MaynardOffDiagonal.Diag m r a}
      {a | PrimeGaps.MaynardOffDiagonal.OffDiag m r a} :=
    Set.disjoint_left.mpr fun a ha1 ha2 ↦
      PrimeGaps.MaynardOffDiagonal.diag_offDiag_disjoint m r a ⟨ha1, ha2⟩
  have hconv : (∑ᶠ a : Fin k → ℕ, if (∀ i, r i ∣ a i) then
        PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r a
      else 0) = ∑ᶠ a ∈ {a : Fin k → ℕ | ∀ i, r i ∣ a i},
          PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r a := by
    rw [finsum_mem_def]
    refine finsum_congr fun a ↦ ?_
    rw [Set.indicator_apply]
    congr
  rw [hconv, hunion]
  have hfin_supp : (Function.support (PrimeGaps.MaynardOffDiagonal.Tsummand
      (PrimeGaps.lToY l) m r)).Finite := by
    apply Set.Finite.subset (PrimeGaps.lToY l).hasFiniteSupport
    intro a ha
    simp only [Function.mem_support] at ha ⊢
    intro hy0
    apply ha
    unfold PrimeGaps.MaynardOffDiagonal.Tsummand
    rw [hy0, zero_div, mul_zero, zero_mul]
  have hfin_diag : ({a : Fin k → ℕ | PrimeGaps.MaynardOffDiagonal.Diag m r a} ∩
      Function.support (PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r)).Finite :=
    hfin_supp.inter_of_right _
  have hfin_offdiag : ({a : Fin k → ℕ | PrimeGaps.MaynardOffDiagonal.OffDiag m r a} ∩
      Function.support (PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r)).Finite :=
    hfin_supp.inter_of_right _
  rw [finsum_mem_union' hdisj hfin_diag hfin_offdiag]
  congr 1
  exact diag_sum_eq_crFactor_yInverseSum l m r hrm hrsq

/-- Every prime factor of an `n` coprime to `primorial ⌊D₀ N⌋₊` exceeds `⌊D₀ N⌋₊`. -/
theorem primorial_D0_prime_factor_gt (N : ℝ) {n p : ℕ}
    (hcop : Nat.Coprime n (primorial ⌊D₀ N⌋₊)) (hp : p.Prime) (hpn : p ∣ n) :
    ⌊D₀ N⌋₊ < p := by
  by_contra! hle
  have hpW : p ∣ primorial ⌊D₀ N⌋₊ := by
    unfold primorial
    exact Finset.dvd_prod_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hle), hp⟩)
  rw [Nat.Coprime] at hcop
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hpn hpW))

/-- `∑ p ∈ S, 1 / (p - 1) ^ 2 ≤ 1 / (M - 1)` when `2 ≤ M` and every `p ∈ S` exceeds `M`. -/
theorem prime_tail_inv_sq_le (S : Finset ℕ) (M : ℕ) (hM : 2 ≤ M) (hgt : ∀ p ∈ S, M < p) :
    ∑ p ∈ S, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / ((M : ℝ) - 1) := by
  classical
  have hM' : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hterm : ∀ p : ℕ, 3 ≤ p →
      1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have h2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hnn : ∀ p : ℕ, 3 ≤ p → 0 ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) :=
    fun p hp ↦ le_trans (by positivity) (hterm p hp)
  refine le_trans (Finset.sum_le_sum fun p hpS ↦ hterm p (by have := hgt p hpS; omega)) ?_
  set T := S.sup id + 1 with hT
  have hSsub : S ⊆ Finset.Ico (M + 1) T := fun p hpS ↦ Finset.mem_Ico.mpr
    ⟨by have := hgt p hpS; omega, by
      have : p ≤ S.sup id := Finset.le_sup (f := id) hpS
      omega⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hSsub
    (fun p hp _ ↦ hnn p (by rw [Finset.mem_Ico] at hp; omega))) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  set n := T - (M + 1) with hn
  have htel : ∀ k ∈ Finset.range n,
      1 / (((M + 1 + k : ℕ) : ℝ) - 2) - 1 / (((M + 1 + k : ℕ) : ℝ) - 1) =
        (fun i : ℕ ↦ 1 / ((M : ℝ) + i - 1)) k - (fun i : ℕ ↦ 1 / ((M : ℝ) + i - 1)) (k + 1) := by
    intro k _
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl htel, Finset.sum_range_sub']
  have hb : (0 : ℝ) ≤ 1 / ((M : ℝ) + n - 1) :=
    le_of_lt (one_div_pos.mpr (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  simp only [Nat.cast_zero, add_zero]
  linarith

/-- Value of a `crFactor` factor on a squarefree `n`:
`g n * n / φ n ^ 2 = ∏ p ∈ n.primeFactors, (1 - 1 / (p - 1) ^ 2)`. -/
theorem crFactor_factor_eq {n : ℕ} (hn : Squarefree n) : (g n : ℝ) * (n : ℝ) /
        (Nat.totient n : ℝ) ^ 2 = ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  classical
  rw [show (g n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 2) from
    ArithmeticFunction.coe_detotient_squarefree_eq_prod hn]
  rw [show ((n : ℝ) : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]]
  rw [PrimeGaps.totient_eq_prod_sub_one n (Nat.pos_of_ne_zero hn.ne_zero) hn,
    ← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h0 : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
  field_simp
  ring

/-- `|crFactor m r - 1| ≤ C / D₀ N` for a `C = C k ≥ 0`, when each `r i` is squarefree and coprime
to `primorial ⌊D₀ N⌋₊`. -/
theorem crFactor_sub_one_le {k : ℕ} : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℝ) (m : Fin k) (r : Fin k → ℕ),
      (∀ i, Squarefree (r i)) →
      (∀ i, Nat.Coprime (r i) (primorial ⌊D₀ N⌋₊)) →
      2 ≤ D₀ N →
      |crFactor m r - 1| ≤ C / D₀ N := by
  classical
  refine ⟨3 * (k : ℝ), by positivity, ?_⟩
  intro N m r hsq hcop hD0
  set M := ⌊D₀ N⌋₊ with hMdef
  have hM2 : 2 ≤ M := by
    rw [hMdef]; exact Nat.le_floor (by exact_mod_cast hD0)
  set f : Fin k → ℝ := fun i ↦ (g (r i) : ℝ) * (r i : ℝ) / ((Nat.totient (r i) : ℝ)) ^ 2 with hfdef
  have hcr : crFactor m r = ∏ i ∈ Finset.univ.erase m, f i := rfl
  have hpgt : ∀ i : Fin k, ∀ p ∈ (r i).primeFactors, M < p := fun i p hp ↦
    primorial_D0_prime_factor_gt N (hcop i) (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  have hinner_le1 : ∀ i : Fin k, ∀ p ∈ (r i).primeFactors, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
    intro i p hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by have := hpgt i p hp; omega : 3 ≤ p)
    rw [div_le_one (by nlinarith)]
    nlinarith
  have hinner_nn : ∀ i : Fin k, ∀ p ∈ (r i).primeFactors, 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 :=
    fun _ _ _ ↦ by positivity
  have hf_eq : ∀ i : Fin k, f i = ∏ p ∈ (r i).primeFactors, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    fun i ↦ by rw [hfdef]; exact crFactor_factor_eq (hsq i)
  have hf_bounds : ∀ i : Fin k, 0 ≤ f i ∧ f i ≤ 1 ∧
      1 - f i ≤ ∑ p ∈ (r i).primeFactors, 1 / ((p : ℝ) - 1) ^ 2 := by
    intro i
    have hk := weierstrass_abs (r i).primeFactors
      (fun p ↦ 1 / ((p : ℝ) - 1) ^ 2) (hinner_nn i) (hinner_le1 i)
    rw [← hf_eq i] at hk
    rw [abs_sub_le_iff] at hk
    have hprod0 : (0 : ℝ) ≤ f i := by
      rw [hf_eq i]
      exact Finset.prod_nonneg fun p hp ↦ by have := hinner_le1 i p hp; linarith
    have hprod1 : f i ≤ 1 := by
      rw [hf_eq i]
      apply Finset.prod_le_one
      · intro p hp; have := hinner_le1 i p hp; have := hinner_nn i p hp; linarith
      · intro p hp; have := hinner_nn i p hp; linarith
    exact ⟨hprod0, hprod1, hk.2⟩
  set x : Fin k → ℝ := fun i ↦ 1 - f i with hxdef
  have hx0 : ∀ i ∈ Finset.univ.erase m, 0 ≤ x i := by
    intro i _; rw [hxdef]; have := (hf_bounds i).2.1; linarith
  have hx1 : ∀ i ∈ Finset.univ.erase m, x i ≤ 1 := by
    intro i _; rw [hxdef]; have := (hf_bounds i).1; linarith
  have hprodrw : ∏ i ∈ Finset.univ.erase m, (1 - x i) = crFactor m r := by
    rw [hcr]; apply Finset.prod_congr rfl; intro i _; rw [hxdef]; ring
  have houter := weierstrass_abs (Finset.univ.erase m) x hx0 hx1
  rw [hprodrw] at houter
  refine le_trans houter ?_
  have hMR1 : (1 : ℝ) ≤ (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    linarith
  have hxbound : ∀ i ∈ Finset.univ.erase m, x i ≤ 1 / ((M : ℝ) - 1) := by
    intro i _
    have hb := (hf_bounds i).2.2
    have htail := prime_tail_inv_sq_le (r i).primeFactors M hM2 (hpgt i)
    rw [hxdef]
    exact le_trans hb htail
  have hsumx : ∑ i ∈ Finset.univ.erase m, x i ≤ ∑ i ∈ Finset.univ.erase m, (1 / ((M : ℝ) - 1)) :=
    Finset.sum_le_sum hxbound
  rw [Finset.sum_const, nsmul_eq_mul] at hsumx
  refine le_trans hsumx ?_
  have hcard : (#(Finset.univ.erase m) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Finset.card_erase_le (a := m)).trans_eq (Finset.card_fin k)
  have hD0pos : 0 < D₀ N := by linarith
  have hMR0 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hDle : D₀ N ≤ 3 * ((M : ℝ) - 1) := by
    have hfloor : D₀ N < (M : ℝ) + 1 := by
      rw [hMdef]; exact Nat.lt_floor_add_one (D₀ N)
    have h2M : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    linarith
  have hinvle : 1 / ((M : ℝ) - 1) ≤ 3 / D₀ N := by
    rw [div_le_div_iff₀ hMR0 hD0pos]
    nlinarith [hDle, hD0pos]
  calc (#(Finset.univ.erase m) : ℝ) * (1 / ((M : ℝ) - 1)) ≤ (k : ℝ) * (3 / D₀ N) :=
        mul_le_mul hcard hinvle (by positivity) (by positivity)
    _ = 3 * (k : ℝ) / D₀ N := by ring

/-- `yInverseSum l m r = 0` when some `r j` with `j ≠ m` is not coprime to `W`. -/
theorem yInverseSum_eq_zero_of_r_not_coprime
    {k : ℕ} (l : (Fin k → ℕ) →₀ ℝ) {R : ℝ} {W : ℕ}
    (hl : l.HasPermissibleSupport ⌊R⌋₊ W)
    (m : Fin k) (r : Fin k → ℕ) {j : Fin k} (hjm : j ≠ m)
    (hnotcop : ¬ Nat.Coprime (r j) W) :
    yInverseSum l m r = 0 := by
  unfold yInverseSum
  have hzero : ∀ a : ℕ, (PrimeGaps.lToY l) (Function.update r m a) / (Nat.totient a : ℝ) = 0 := by
    intro a
    have hval : (PrimeGaps.lToY l) (Function.update r m a) = 0 := by
      by_contra hne
      have hdvd : r j ∣ ∏ i, (Function.update r m a) i := by
        rw [← Function.update_of_ne hjm a r]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      exact hnotcop <| Nat.Coprime.coprime_dvd_left hdvd
        (hl.lToY.coprime_prod_W_of_ne_zero hne)
    rw [hval, zero_div]
  simp only [hzero, tsum_zero]

/-- Every prime factor of `primorial ⌊D₀ N⌋₊` is at most `D₀ N`. -/
theorem primorial_D0_primeFactor_le_D0 (N : ℝ) (p : ℕ) (hp : p ∈ (primorial ⌊D₀ N⌋₊).primeFactors) :
    (p : ℝ) ≤ D₀ N := by
  rw [primorial, Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpdvd, -⟩ := hp
  have hp_le_floor : p ≤ ⌊D₀ N⌋₊ := by
    obtain ⟨q, hqmem, hpq⟩ := hpp.prime.exists_mem_finset_dvd hpdvd
    rw [Finset.mem_filter, Finset.mem_range] at hqmem
    obtain ⟨hqlt, hqp⟩ := hqmem
    rw [(Nat.prime_dvd_prime_iff_eq hpp hqp).mp hpq]
    omega
  have hp1 : 1 ≤ p := hpp.one_le
  have hD0pos : 0 ≤ D₀ N := by
    by_contra! hneg
    have : ⌊D₀ N⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  calc (p : ℝ) ≤ (⌊D₀ N⌋₊ : ℝ) := by exact_mod_cast hp_le_floor
    _ ≤ D₀ N := Nat.floor_le hD0pos

/-- Only `a ∈ Sset W R` contribute to `yInverseSum l m r`. -/
theorem yInverseSum_support_subset
    {k : ℕ} (l : (Fin k → ℕ) →₀ ℝ) {R : ℝ} {W : ℕ}
    (hl : l.HasPermissibleSupport ⌊R⌋₊ W)
    (m : Fin k) (r : Fin k → ℕ) :
    ∀ a : ℕ, (PrimeGaps.lToY l) (Function.update r m a) ≠ 0 →
      a ∈ PrimeGaps.MaynardOffDiagonal.Sset W R := by
  intro a hne
  obtain ⟨hlt, hcop, hsq⟩ :=
    Finset.mem_permissibleSupport_iff.mp (hl.lToY (Finsupp.mem_support_iff.mpr hne))
  have ha_dvd : a ∣ ∏ i, (Function.update r m a) i := by
    have hm : (Function.update r m a) m = a := by simp
    conv_lhs => rw [← hm]
    exact Finset.dvd_prod_of_mem (Function.update r m a) (Finset.mem_univ m)
  have hprod_ne : ∏ i, (Function.update r m a) i ≠ 0 := hsq.ne_zero
  have ha_pos : 0 < a := by
    by_contra! h0
    exact hprod_ne (Finset.prod_eq_zero (Finset.mem_univ m) (by simp [Nat.le_zero.mp h0]))
  have ha_floor : a ≤ ⌊R⌋₊ := (Nat.le_of_dvd (Nat.pos_of_ne_zero hprod_ne) ha_dvd).trans hlt
  have ha_cop : Nat.Coprime a W := Nat.Coprime.coprime_dvd_left ha_dvd hcop
  have ha_sq : Squarefree a := hsq.squarefree_of_dvd ha_dvd
  rw [PrimeGaps.MaynardOffDiagonal.Sset, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨ha_pos, ha_floor⟩, ha_sq, ha_cop⟩

/-- `|yInverseSum l m r| ≤ C * (lToY l).maxRealAbs * φ W * (log R + 1) / W` for a `C = C k > 0`. -/
theorem yInverseSum_triangle_bound {k : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (W : ℕ) (l : (Fin k → ℕ) →₀ ℝ) (_ : l.HasPermissibleSupport ⌊R⌋₊ W)
      (m : Fin k) (r : Fin k → ℕ),
      1 ≤ W →
      (∀ p ∈ W.primeFactors, (p : ℝ) ≤ R) →
      (1 : ℝ) ≤ R →
      |yInverseSum l m r| ≤
        C * (PrimeGaps.lToY l).maxRealAbs * (Nat.totient W : ℝ) * (Real.log R + 1) / (W : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := PrimeGaps.MaynardOffDiagonal.moment_sum_le
  obtain ⟨C_H, hC_H0, hC_H⟩ := PrimeGaps.MaynardOffDiagonal.coprime_harmonic_le
  refine ⟨K * C_H, mul_pos hK0 hC_H0, ?_⟩
  intro R W l hl m r hW1 hsmooth hR1
  have hWpos : (0 : ℝ) < (W : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hW1
  set S : Finset ℕ := PrimeGaps.MaynardOffDiagonal.Sset W R with hSdef
  unfold yInverseSum
  have habs_tsum : |∑' a : ℕ, (PrimeGaps.lToY l) (Function.update r m a) / (Nat.totient a : ℝ)| ≤
      ∑ a ∈ S, |(PrimeGaps.lToY l) (Function.update r m a) / (Nat.totient a : ℝ)| := by
    have hz : ∀ a ∉ S, (PrimeGaps.lToY l) (Function.update r m a) / (Nat.totient a : ℝ) = 0 :=
      fun a haS ↦ by
        rw [show (PrimeGaps.lToY l) (Function.update r m a) = 0 from
          not_not.mp fun hne ↦ haS (yInverseSum_support_subset l hl m r a hne), zero_div]
    rw [tsum_eq_sum hz]
    exact Finset.abs_sum_le_sum_abs _ _
  refine le_trans habs_tsum ?_
  have hbound_termwise : ∀ a ∈ S,
      |(PrimeGaps.lToY l) (Function.update r m a) / (Nat.totient a : ℝ)| ≤
        (PrimeGaps.lToY l).maxRealAbs / (Nat.totient a : ℝ) := by
    intro a haS
    rw [hSdef, PrimeGaps.MaynardOffDiagonal.Sset, Finset.mem_filter, Finset.mem_Icc] at haS
    have hphi_pos : 0 < (Nat.totient a : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr haS.1.1
    rw [abs_div, abs_of_pos hphi_pos]
    exact div_le_div_of_nonneg_right Finsupp.le_maxRealAbs hphi_pos.le
  refine le_trans (Finset.sum_le_sum hbound_termwise) ?_
  have hpull : ∑ a ∈ S, (PrimeGaps.lToY l).maxRealAbs / (Nat.totient a : ℝ) =
      (PrimeGaps.lToY l).maxRealAbs * ∑ a ∈ S, 1 / (Nat.totient a : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ (mul_one_div _ _).symm
  rw [hpull, show ∑ a ∈ S, 1 / (Nat.totient a : ℝ) =
    PrimeGaps.MaynardOffDiagonal.sumA W R from rfl]
  have hharm_nn : 0 ≤ PrimeGaps.coprimeReciprocalSum W R := by
    unfold PrimeGaps.coprimeReciprocalSum
    refine Finset.sum_nonneg fun a ha ↦ ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    have : 0 < a := ha.1.1
    positivity
  have hstep1 : PrimeGaps.MaynardOffDiagonal.sumA W R ≤
      K * (C_H * (Nat.totient W : ℝ) / (W : ℝ) * (Real.log R + 1)) :=
    calc PrimeGaps.MaynardOffDiagonal.sumA W R ≤ PrimeGaps.MaynardOffDiagonal.momentSum W ⌊R⌋₊ *
              PrimeGaps.coprimeReciprocalSum W R :=
          PrimeGaps.MaynardOffDiagonal.sumA_le_momentSum_mul_coprimeReciprocalSum W R
      _ ≤ K * PrimeGaps.coprimeReciprocalSum W R :=
          mul_le_mul_of_nonneg_right (hK W ⌊R⌋₊) hharm_nn
      _ ≤ K * (C_H * (Nat.totient W : ℝ) / (W : ℝ) * (Real.log R + 1)) :=
          mul_le_mul_of_nonneg_left (hC_H W R hW1 hR1 hsmooth) hK0.le
  refine le_trans (mul_le_mul_of_nonneg_left hstep1 Finsupp.maxRealAbs_nonneg) ?_
  have hW_ne : (W : ℝ) ≠ 0 := hWpos.ne'
  field_simp
  ring_nf
  rfl

/-- For `δ < θ / 2`, all large `N` satisfy the four largeness conditions used by
`maynard_ym_identity`: `4 ≤ D₀ N`, `3 ≤ N ^ (θ / 2 - δ)`, `1 ≤ log (N ^ (θ / 2 - δ))`, and every
prime factor of `primorial ⌊D₀ N⌋₊` is at most `N ^ (θ / 2 - δ)`. -/
theorem exists_large_N0_for_ym (θ δ : ℝ) (hδθ : δ < θ / 2) : ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      4 ≤ D₀ N ∧ 3 ≤ N ^ (θ / 2 - δ) ∧ 1 ≤ Real.log (N ^ (θ / 2 - δ)) ∧
        (∀ p ∈ (primorial ⌊D₀ N⌋₊).primeFactors, (p : ℝ) ≤ N ^ (θ / 2 - δ)) := by
  set p_exp : ℝ := θ / 2 - δ with hp_def
  have hp : 0 < p_exp := by rw [hp_def]; linarith
  obtain ⟨N_smooth, hN_smooth⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_atTop hp).def (c := 1) (by norm_num))
  set A : ℝ := rexp (rexp (rexp 4)) with hA_def
  set B : ℝ := (3 : ℝ) ^ p_exp⁻¹ with hB_def
  refine ⟨max A (max B (max N_smooth 2)), ?_⟩
  intro N hN
  have hNA : A ≤ N := le_trans (le_max_left _ _) hN
  have hNB : B ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN_sm : N_smooth ≤ N := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hN2 : (2 : ℝ) ≤ N := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)) |>.trans hN
  have hNpos : 0 < N := by linarith
  have he1 : (0 : ℝ) < rexp 4 := Real.exp_pos _
  have he2 : (0 : ℝ) < rexp (rexp 4) := Real.exp_pos _
  have he3 : (0 : ℝ) < A := by rw [hA_def]; exact Real.exp_pos _
  have hlogA : Real.log A = rexp (rexp 4) := by rw [hA_def, Real.log_exp]
  have hlogN_ge : rexp (rexp 4) ≤ Real.log N := by
    rw [← hlogA]; exact Real.log_le_log he3 hNA
  have hloglogN : rexp 4 ≤ Real.log (Real.log N) :=
    calc rexp 4 = Real.log (rexp (rexp 4)) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log N) := Real.log_le_log he2 hlogN_ge
  have hD4 : 4 ≤ D₀ N := by
    rw [D₀]
    calc (4 : ℝ) = Real.log (rexp 4) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log (Real.log N)) := Real.log_le_log he1 hloglogN
  have hR3 : (3 : ℝ) ≤ N ^ (θ / 2 - δ) := by
    rw [← hp_def]
    have hBnn : (0 : ℝ) ≤ B := by rw [hB_def]; positivity
    have hstep : B ^ p_exp ≤ N ^ p_exp := Real.rpow_le_rpow hBnn hNB hp.le
    have hBp : B ^ p_exp = 3 := by
      rw [hB_def, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), inv_mul_cancel₀ hp.ne',
        Real.rpow_one]
    linarith
  have hlogR : 1 ≤ Real.log (N ^ (θ / 2 - δ)) := by
    have he : rexp 1 ≤ N ^ (θ / 2 - δ) := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (rexp 1) := (Real.log_exp _).symm
      _ ≤ Real.log (N ^ (θ / 2 - δ)) := Real.log_le_log (Real.exp_pos _) he
  have hlogN_le_R : Real.log N ≤ N ^ (θ / 2 - δ) := by
    have hbnd := hN_smooth N hN_sm
    have hlogN_nn : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    have hrpow_nn : 0 ≤ N ^ p_exp := Real.rpow_nonneg hNpos.le _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogN_nn,
      abs_of_nonneg hrpow_nn, one_mul] at hbnd
    rwa [← hp_def]
  have hD0_le_logN : D₀ N ≤ Real.log N := by
    unfold D₀
    have hlogN_ge_0 : 0 ≤ Real.log N := by
      have := Real.add_one_le_exp (rexp 4)
      linarith
    have hloglog_ge_0 : 0 ≤ Real.log (Real.log N) := by
      have := Real.add_one_le_exp (4 : ℝ)
      linarith
    have h1 : Real.log (Real.log N) ≤ Real.log N := Real.log_le_self hlogN_ge_0
    have h2 : Real.log (Real.log (Real.log N)) ≤ Real.log (Real.log N) :=
      Real.log_le_self hloglog_ge_0
    linarith
  exact ⟨hD4, hR3, hlogR, fun p hp ↦
    (primorial_D0_primeFactor_le_D0 N p hp).trans (hD0_le_logN.trans hlogN_le_R)⟩

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- For an admissible tuple `H` of size `k`, a level of distribution `θ`, `δ ∈ (0, θ/2)`, and
sufficiently large `N`, any sieve-supported `l` with squarefree `r` (with `r_m = 1` ) satisfies
`|ym m l r - yInverseSum l m r| ≤ C · (PrimeGaps.lToY l).maxRealAbs · φ(W) · log R /
  (W · D₀)` with `C = C(k)`. -/
@[pg_tag "bg246" "lem_ym_from_y"]
theorem maynard_ym_identity {k : ℕ} : ∃ C : ℝ, 0 < C ∧ ∀ (H : Finset ℕ), H.Admissible → #H = k →
      ∀ (θ δ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 → 0 < δ → δ < θ / 2 →
        ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ l : (Fin k → ℕ) →₀ ℝ, l.HasPermissibleSupport ⌊R⌋₊ (W N) →
              ∀ (m : Fin k) (r : Fin k → ℕ), r m = 1 → (∀ i, Squarefree (r i)) →
                |(PrimeGaps.ym m l) r - yInverseSum l m r| ≤ C * ((PrimeGaps.lToY l).maxRealAbs *
                  (Nat.totient (W N) : ℝ) * Real.log R) /
                      ((W N : ℝ) * D₀ N) := by
  classical
  obtain ⟨C_off, hC_off_pos, hC_off⟩ := PrimeGaps.MaynardOffDiagonal.offDiagonal_bound (k := k)
  obtain ⟨C_cr, hC_cr_nn, hC_cr⟩ := crFactor_sub_one_le (k := k)
  obtain ⟨C_inv, hC_inv_pos, hC_inv⟩ := yInverseSum_triangle_bound (k := k)
  refine ⟨C_off + 2 * C_cr * C_inv, by positivity, ?_⟩
  intro H hH hHcard θ δ hθIoo hδ hδθ
  obtain ⟨N_off, hN_off_ge_3, hbound_off⟩ := hC_off θ δ hθIoo ⟨hδ, hδθ⟩
  obtain ⟨N_thresh, hthresh⟩ := exists_large_N0_for_ym θ δ hδθ
  refine ⟨max N_off N_thresh, ?_⟩
  intro N hN
  obtain ⟨hD4, hR3, hlogR_ge_1, hRsmooth⟩ := hthresh N (le_trans (le_max_right _ _) hN)
  have hD2 : (2 : ℝ) ≤ D₀ N := by linarith
  have hDpos : 0 < D₀ N := by linarith
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hlogR_pos : 0 < Real.log R := by linarith
  have hWpos : 0 < (W N : ℝ) := by exact_mod_cast PrimeGaps.W_pos
  have hφWnn : (0 : ℝ) ≤ (Nat.totient (W N) : ℝ) := Nat.cast_nonneg _
  intro l hl m r hrm hrsq
  have hr : ∀ i, 0 < r i := fun i ↦ Nat.pos_of_ne_zero (hrsq i).ne_zero
  have hyMax_nn : 0 ≤ (PrimeGaps.lToY l).maxRealAbs := Finsupp.maxRealAbs_nonneg
  set B : ℝ := (PrimeGaps.lToY l).maxRealAbs * (Nat.totient (W N) : ℝ) * Real.log R with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (mul_nonneg hyMax_nn hφWnn) hlogR_pos.le
  rw [ym_eq_diag_plus_offdiag hl m r hr hrm hrsq]
  set S_off : ℝ := ∑ᶠ (a : Fin k → ℕ) (_ : PrimeGaps.MaynardOffDiagonal.OffDiag m r a),
        PrimeGaps.MaynardOffDiagonal.Tsummand (PrimeGaps.lToY l) m r a with hSoff
  have hrewrite : crFactor m r * yInverseSum l m r + S_off - yInverseSum l m r =
      (crFactor m r - 1) * yInverseSum l m r + S_off := by ring
  rw [hrewrite]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul]
  have hoff : |S_off| ≤ C_off * B / ((W N : ℝ) * D₀ N) := by
    rw [hSoff, hBdef]
    calc _ ≤ C_off * (PrimeGaps.lToY l).maxRealAbs * (Nat.totient (W N) : ℝ) * Real.log R /
              ((W N : ℝ) * D₀ N) :=
          hbound_off N (le_trans (le_max_left _ _) hN) (PrimeGaps.lToY l) hl.lToY m r hr hrm
      _ = C_off * ((PrimeGaps.lToY l).maxRealAbs * (Nat.totient (W N) : ℝ) *
                    Real.log R) / ((W N : ℝ) * D₀ N) := by ring
  have hdiag : |crFactor m r - 1| * |yInverseSum l m r| ≤
      2 * C_cr * C_inv * B / ((W N : ℝ) * D₀ N) := by
    by_cases hcop : ∀ i, Nat.Coprime (r i) (W N)
    · have hcr := hC_cr N m r hrsq hcop hD2
      have hinv := hC_inv R (W N) l hl m r
        (Nat.one_le_iff_ne_zero.mpr PrimeGaps.W_pos.ne') hRsmooth hR1
      have hinv_alt : |yInverseSum l m r| ≤ 2 * C_inv * B / (W N : ℝ) := by
        refine le_trans hinv (div_le_div_of_nonneg_right ?_ hWpos.le)
        rw [hBdef]
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC_inv_pos.le hyMax_nn) hφWnn)
          (sub_nonneg.mpr hlogR_ge_1)]
      calc |crFactor m r - 1| * |yInverseSum l m r| ≤ (C_cr / D₀ N) * (2 * C_inv * B / (W N : ℝ)) :=
            mul_le_mul hcr hinv_alt (abs_nonneg _) (div_nonneg hC_cr_nn hDpos.le)
        _ = 2 * C_cr * C_inv * B / ((W N : ℝ) * D₀ N) := by
            field_simp
    · push Not at hcop
      obtain ⟨j, hj⟩ := hcop
      have hjm : j ≠ m := fun heq ↦ hj (by rw [heq, hrm]; exact Nat.coprime_one_left _)
      rw [yInverseSum_eq_zero_of_r_not_coprime l hl m r hjm hj, abs_zero, mul_zero]
      exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC_cr_nn)
        hC_inv_pos.le) hBnn) (mul_nonneg hWpos.le hDpos.le)
  refine le_trans (add_le_add hdiag hoff) (le_of_eq ?_)
  rw [← add_div, hBdef]
  ring

end PrimeGaps
