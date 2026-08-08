/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.ExpandDrop.Collision

/-!
# Block bounds and the flat majorants

The cross and rho block bounds, and the flattened majorants `collisionFlat`,
`crossFlat`, `rhoFlat`.

## Main results

* `PrimeGaps.crossBlock_le`, `PrimeGaps.rhoBlock_le`
* `PrimeGaps.collisionFlat`, `PrimeGaps.crossFlat`, `PrimeGaps.rhoFlat`
* `PrimeGaps.collisionFlat_le_union`
* `PrimeGaps.tsum_collisionFlat_eq`, `PrimeGaps.tsum_crossFlat_eq`, `PrimeGaps.tsum_rhoFlat_eq`
-/

@[expose] public section

open scoped ArithmeticFunction.detotient
open PrimeGaps

/-- The block `p ∣ u * u' ∧ p ∣ ρ i` contributes at most
`2 * (1 / (p - 2)) ^ 2 * (sumA W X) ^ 2 * (gSum W X) ^ (k - 1)`. -/
theorem PrimeGaps.crossBlock_le {k : ℕ} (hk : 2 ≤ k) (W : ℕ) (X : ℝ) (m i : Fin k) (hi : i ≠ m)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), (if p ∣ u * u' ∧ p ∣ ρ i then
          PrimeGaps.aSum W X u * PrimeGaps.aSum W X u' * PrimeGaps.bSum W X m ρ else 0)) ≤
      2 * (1 / ((p : ℝ) - 2)) ^ 2 * PrimeGaps.MaynardOffDiagonal.sumA W X ^ 2 *
        PrimeGaps.gSum W X ^ (k - 1) := by
  classical
  set A := fun n ↦ PrimeGaps.aSum W X n with hA
  set Bi := fun ρ : Fin k → ℕ ↦ (if p ∣ ρ i then PrimeGaps.bSum W X m ρ else 0) with hBi
  have hA_nonneg : ∀ n : ℕ, (0 : ℝ) ≤ A n := PrimeGaps.aSum_nonneg W X
  have hbSum_nonneg : ∀ ρ : Fin k → ℕ, (0 : ℝ) ≤ PrimeGaps.bSum W X m ρ :=
    PrimeGaps.bSum_nonneg W X m
  have hBi_nonneg : ∀ ρ : Fin k → ℕ, (0 : ℝ) ≤ Bi ρ := fun ρ ↦ by
    simp only [hBi]; split; exacts [hbSum_nonneg ρ, le_rfl]
  have hphi_nonneg : (0 : ℝ) ≤ PrimeGaps.MaynardOffDiagonal.sumA W X := sumA_nonneg X W
  have hinv_nonneg : (0 : ℝ) ≤ 1 / ((p : ℝ) - 2) := by
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    exact one_div_nonneg.mpr (by linarith)
  have hAP_le : (∑' u : ℕ, if p ∣ u then A u else 0) ≤
      1 / ((p : ℝ) - 2) * PrimeGaps.MaynardOffDiagonal.sumA W X := by
    simpa only [hA] using PrimeGaps.tsum_aSumP_le W X p hp hp3
  have hA_eq : (∑' u : ℕ, A u) = PrimeGaps.MaynardOffDiagonal.sumA W X := by
    simpa only [hA] using PrimeGaps.tsum_aSum_eq_sumA W X
  have hBi_le : (∑' ρ : Fin k → ℕ, Bi ρ) ≤
      1 / ((p : ℝ) - 2) * PrimeGaps.gSum W X ^ (k - 1) := by
    simpa only [hBi] using PrimeGaps.tsum_bSumP_le hk W X m i hi p hp hp3
  have hBi_sum_nonneg : (0 : ℝ) ≤ (∑' ρ : Fin k → ℕ, Bi ρ) := tsum_nonneg hBi_nonneg
  have hbound1 : (∑' u : ℕ, if p ∣ u then A u else 0) * (∑' u' : ℕ, A u') *
      (∑' ρ : Fin k → ℕ, Bi ρ) ≤ (1 / ((p : ℝ) - 2)) ^ 2 *
        PrimeGaps.MaynardOffDiagonal.sumA W X ^ 2 * PrimeGaps.gSum W X ^ (k - 1) := by
    rw [hA_eq]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hAP_le hphi_nonneg) hBi_le hBi_sum_nonneg
      (mul_nonneg (mul_nonneg hinv_nonneg hphi_nonneg) hphi_nonneg)).trans_eq (by ring)
  have hAsummable : Summable A :=
    summable_of_ne_finset_zero (s := Finset.Iic ⌊X⌋₊) fun n hn ↦ by
      simpa only [hA, PrimeGaps.aSum] using if_neg fun h ↦ hn (Finset.mem_Iic.mpr h.2.2)
  have hAPsummable : Summable (fun n : ℕ ↦ if p ∣ n then A n else 0) :=
    Summable.of_nonneg_of_le (fun n ↦ by split; exacts [hA_nonneg n, le_rfl])
      (fun n ↦ by split; exacts [le_rfl, hA_nonneg n]) hAsummable
  have hkey := PrimeGaps.tsum_ite_dvd_mul_and_le p hp A (PrimeGaps.bSum W X m) (fun ρ ↦ p ∣ ρ i)
    hA_nonneg hbSum_nonneg hAsummable hAPsummable hBi_sum_nonneg
  exact hkey.trans (by linarith only [hbound1])

/-- The block `p ∣ ρ i ∧ p ∣ ρ j` contributes at most
`(1 / (p - 2)) ^ 2 * (sumA W X) ^ 2 * (gSum W X) ^ (k - 1)`. -/
theorem PrimeGaps.rhoBlock_le {k : ℕ} (hk : 2 ≤ k) (W : ℕ) (X : ℝ) (m i j : Fin k)
    (hi : i ≠ m) (hj : j ≠ m) (hij : i ≠ j)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), (if p ∣ ρ i ∧ p ∣ ρ j then
          PrimeGaps.aSum W X u * PrimeGaps.aSum W X u' * PrimeGaps.bSum W X m ρ else 0)) ≤
      (1 / ((p : ℝ) - 2)) ^ 2 * PrimeGaps.MaynardOffDiagonal.sumA W X ^ 2 *
        PrimeGaps.gSum W X ^ (k - 1) := by
  classical
  set A := fun n ↦ PrimeGaps.aSum W X n with hA
  set B := fun ρ : Fin k → ℕ ↦ (if p ∣ ρ i ∧ p ∣ ρ j then PrimeGaps.bSum W X m ρ else 0) with hB
  set SA := ∑' (n : ℕ), A n with hSA
  set SB := ∑' (ρ : Fin k → ℕ), B ρ with hSB
  have hSA_eq : SA = PrimeGaps.MaynardOffDiagonal.sumA W X := by
    simpa only [hSA, hA] using PrimeGaps.tsum_aSum_eq_sumA W X
  have hfac : (∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ),
        (if p ∣ ρ i ∧ p ∣ ρ j then A u * A u' * PrimeGaps.bSum W X m ρ else 0)) =
          SA ^ 2 * SB := by
    have h1 : ∀ u u' : ℕ, (∑' (ρ : Fin k → ℕ),
        (if p ∣ ρ i ∧ p ∣ ρ j then A u * A u' * PrimeGaps.bSum W X m ρ else 0)) =
          A u * (A u' * SB) := fun u u' ↦ by
      rw [hSB, ← mul_assoc, ← tsum_mul_left]
      refine tsum_congr fun ρ ↦ ?_
      simp only [hB]; by_cases h : p ∣ ρ i ∧ p ∣ ρ j
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]; ring
    simp only [h1, tsum_mul_left, tsum_mul_right, ← hSA]
    ring
  rw [hfac, hSA_eq]
  have hSB_le : SB ≤ (1 / ((p : ℝ) - 2)) ^ 2 * PrimeGaps.gSum W X ^ (k - 1) := by
    simpa only [hSB, hB] using PrimeGaps.tsum_bSumPP_le hk W X m i j hi hj hij p hp hp3
  exact (mul_le_mul_of_nonneg_left hSB_le (sq_nonneg _)).trans_eq (by ring)

/-- The summand of `collisionMass` on the flattened index type `ℕ × ℕ × (Fin k → ℕ)`. -/
noncomputable def PrimeGaps.collisionFlat {k : ℕ} (W : ℕ) (X : ℝ) (m : Fin k)
    (q : ℕ × ℕ × (Fin k → ℕ)) : ℝ :=
  if ¬((∀ i, i ≠ m → (q.1 * q.2.1).Coprime (q.2.2 i)) ∧
        (∀ i j, i ≠ j → (q.2.2 i).Coprime (q.2.2 j)))
    then PrimeGaps.aSum W X q.1 * PrimeGaps.aSum W X q.2.1 * PrimeGaps.bSum W X m q.2.2 else 0

/-- `aSum u * aSum u' * bSum ρ` when `p ∣ u * u'` and `p ∣ ρ i`, and `0` otherwise, on the
flattened index type. -/
noncomputable def PrimeGaps.crossFlat {k : ℕ} (W : ℕ) (X : ℝ) (m i : Fin k) (p : ℕ)
    (q : ℕ × ℕ × (Fin k → ℕ)) : ℝ :=
  if p ∣ q.1 * q.2.1 ∧ p ∣ q.2.2 i
    then PrimeGaps.aSum W X q.1 * PrimeGaps.aSum W X q.2.1 * PrimeGaps.bSum W X m q.2.2 else 0

/-- `aSum u * aSum u' * bSum ρ` when `p ∣ ρ i` and `p ∣ ρ j`, and `0` otherwise, on the flattened
index type. -/
noncomputable def PrimeGaps.rhoFlat {k : ℕ} (W : ℕ) (X : ℝ) (m i j : Fin k) (p : ℕ)
    (q : ℕ × ℕ × (Fin k → ℕ)) : ℝ :=
  if p ∣ q.2.2 i ∧ p ∣ q.2.2 j
    then PrimeGaps.aSum W X q.1 * PrimeGaps.aSum W X q.2.1 * PrimeGaps.bSum W X m q.2.2 else 0

/-- `fun (u, u', ρ) ↦ aSum W X u * aSum W X u' * bSum W X m ρ` is summable. -/
theorem PrimeGaps.prodFlat_summable {k : ℕ} (W : ℕ) (X : ℝ) (m : Fin k) :
    Summable (fun q : ℕ × ℕ × (Fin k → ℕ) ↦
      PrimeGaps.aSum W X q.1 * PrimeGaps.aSum W X q.2.1 * PrimeGaps.bSum W X m q.2.2) := by
  have hfin := PrimeGaps.prod_flat_support_finite W X (1 : ℝ) m
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun q hq ↦ ?_
  rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hq
  simpa using hq

/-- Every collision is witnessed by a prime `D < p ≤ X`: `collisionFlat` is at most the
`crossFlat` sum over `i ≠ m` plus the `rhoFlat` sum over pairs `i < j` in `univ.erase m`. -/
theorem PrimeGaps.collisionFlat_le_union {k : ℕ} (W D : ℕ) (X : ℝ) (m : Fin k)
    (hWcop : ∀ p : ℕ, p.Prime → p.Coprime W → D < p)
    (q : ℕ × ℕ × (Fin k → ℕ)) :
    PrimeGaps.collisionFlat W X m q ≤ (∑ i ∈ Finset.univ.erase m,
            ∑ p ∈ (Finset.Icc (D + 1) ⌊X⌋₊).filter Nat.Prime, PrimeGaps.crossFlat W X m i p q) +
        (∑ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
            ∑ p ∈ (Finset.Icc (D + 1) ⌊X⌋₊).filter Nat.Prime,
              PrimeGaps.rhoFlat W X m ij.1 ij.2 p q) := by
  classical
  obtain ⟨u, u', ρ⟩ := q
  set P := (Finset.Icc (D + 1) ⌊X⌋₊).filter Nat.Prime with hP
  set A := PrimeGaps.aSum W X u * PrimeGaps.aSum W X u' * PrimeGaps.bSum W X m ρ with hAdef
  have hprod_nonneg : (0 : ℝ) ≤
      PrimeGaps.aSum W X u * PrimeGaps.aSum W X u' * PrimeGaps.bSum W X m ρ :=
    mul_nonneg (mul_nonneg (PrimeGaps.aSum_nonneg W X u) (PrimeGaps.aSum_nonneg W X u'))
      (PrimeGaps.bSum_nonneg W X m ρ)
  have hcross_nonneg : ∀ (i : Fin k) (p : ℕ),
      (0 : ℝ) ≤ PrimeGaps.crossFlat W X m i p (u, u', ρ) := fun i p ↦ by
    rw [PrimeGaps.crossFlat]; split; exacts [hprod_nonneg, le_rfl]
  have hrho_nonneg : ∀ (i j : Fin k) (p : ℕ),
      (0 : ℝ) ≤ PrimeGaps.rhoFlat W X m i j p (u, u', ρ) := fun i j p ↦ by
    rw [PrimeGaps.rhoFlat]; split; exacts [hprod_nonneg, le_rfl]
  have hCross_block_nonneg : (0 : ℝ) ≤ ∑ i ∈ Finset.univ.erase m, ∑ p ∈ P,
        PrimeGaps.crossFlat W X m i p (u, u', ρ) :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun p _ ↦ hcross_nonneg i p
  have hRho_block_nonneg :
      (0 : ℝ) ≤ ∑ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
        ∑ p ∈ P, PrimeGaps.rhoFlat W X m ij.1 ij.2 p (u, u', ρ) :=
    Finset.sum_nonneg fun ij _ ↦ Finset.sum_nonneg fun p _ ↦ hrho_nonneg ij.1 ij.2 p
  have hR_nonneg : (0 : ℝ) ≤ (∑ i ∈ Finset.univ.erase m, ∑ p ∈ P,
              PrimeGaps.crossFlat W X m i p (u, u', ρ)) +
          (∑ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
              ∑ p ∈ P, PrimeGaps.rhoFlat W X m ij.1 ij.2 p (u, u', ρ)) :=
    add_nonneg hCross_block_nonneg hRho_block_nonneg
  rw [PrimeGaps.collisionFlat]
  split
  case isFalse => exact hR_nonneg
  case isTrue hnc =>
    change A ≤ _
    by_cases hA : A = 0
    · rw [hA]; exact hR_nonneg
    · have hbρ : PrimeGaps.bSum W X m ρ ≠ 0 := by
        intro h; apply hA; rw [hAdef, h]; ring
      have hρm : ρ m = 1 := by
        by_contra hc
        rw [PrimeGaps.bSum, if_neg hc] at hbρ
        exact hbρ rfl
      have hcSum_ne : ∀ i ∈ Finset.univ.erase m, PrimeGaps.cSum W X (ρ i) ≠ 0 := by
        rw [← Finset.prod_ne_zero_iff]
        rwa [PrimeGaps.bSum, if_pos hρm] at hbρ
      have guard_ρ : ∀ i, i ≠ m → Squarefree (ρ i) ∧ (ρ i).Coprime W ∧ ρ i ≤ ⌊X⌋₊ := by
        intro i hi
        have hne := hcSum_ne i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
        by_contra hc
        rw [PrimeGaps.cSum, if_neg hc] at hne
        exact hne rfl
      rw [not_and_or] at hnc
      rcases hnc with h1 | h2
      · push Not at h1
        obtain ⟨i, hi_ne, hncop⟩ := h1
        have hgcd : Nat.gcd (u * u') (ρ i) ≠ 1 := hncop
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd
        have hpr : p ∣ ρ i := hpdvd.trans (Nat.gcd_dvd_right _ _)
        obtain ⟨hρi_sqf, hρi_cop, hρi_le⟩ := guard_ρ i hi_ne
        have hlo : D < p := hWcop p hp (hρi_cop.coprime_dvd_left hpr)
        have hpX : p ≤ ⌊X⌋₊ := (Nat.le_of_dvd (Nat.pos_of_ne_zero hρi_sqf.ne_zero) hpr).trans hρi_le
        have hpP : p ∈ P := by
          rw [hP, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, hpX⟩, hp⟩
        have hcross_eq : PrimeGaps.crossFlat W X m i p (u, u', ρ) = A := by
          rw [PrimeGaps.crossFlat, if_pos ⟨hpdvd.trans (Nat.gcd_dvd_left _ _), hpr⟩]
        calc A = PrimeGaps.crossFlat W X m i p (u, u', ρ) := hcross_eq.symm
          _ ≤ ∑ p ∈ P, PrimeGaps.crossFlat W X m i p (u, u', ρ) :=
              Finset.single_le_sum (fun p _ ↦ hcross_nonneg i p) hpP
          _ ≤ ∑ i ∈ Finset.univ.erase m, ∑ p ∈ P, PrimeGaps.crossFlat W X m i p (u, u', ρ) :=
              Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg (fun p _ ↦ hcross_nonneg i p))
                (Finset.mem_erase.mpr ⟨hi_ne, Finset.mem_univ i⟩)
          _ ≤ _ := le_add_of_nonneg_right hRho_block_nonneg
      · push Not at h2
        obtain ⟨i, j, hij, hncop⟩ := h2
        have hncop' : ¬(ρ i).Coprime (ρ j) := hncop
        have hi_ne : i ≠ m := by
          intro hh; rw [hh, hρm] at hncop'; exact hncop' (Nat.coprime_one_left _)
        have hj_ne : j ≠ m := by
          intro hh; rw [hh, hρm] at hncop'; exact hncop' (Nat.coprime_one_right _)
        have main : ∀ a b : Fin k, a ≠ m → b ≠ m → a < b → ¬(ρ a).Coprime (ρ b) →
            A ≤ (∑ i ∈ Finset.univ.erase m, ∑ p ∈ P, PrimeGaps.crossFlat W X m i p (u, u', ρ)) +
                (∑ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
                    ∑ p ∈ P, PrimeGaps.rhoFlat W X m ij.1 ij.2 p (u, u', ρ)) := by
          intro a b ha_ne hb_ne hab hnc_ab
          have hgcd : Nat.gcd (ρ a) (ρ b) ≠ 1 := hnc_ab
          obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd
          have hpa : p ∣ ρ a := hpdvd.trans (Nat.gcd_dvd_left _ _)
          obtain ⟨hρa_sqf, hρa_cop, hρa_le⟩ := guard_ρ a ha_ne
          have hlo : D < p := hWcop p hp (hρa_cop.coprime_dvd_left hpa)
          have hpX : p ≤ ⌊X⌋₊ :=
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hρa_sqf.ne_zero) hpa).trans hρa_le
          have hpP : p ∈ P := by
            rw [hP, Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨by omega, hpX⟩, hp⟩
          have hrho_eq : PrimeGaps.rhoFlat W X m a b p (u, u', ρ) = A := by
            rw [PrimeGaps.rhoFlat, if_pos ⟨hpa, hpdvd.trans (Nat.gcd_dvd_right _ _)⟩]
          have hab_mem : (a, b) ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2} := by
            rw [Finset.mem_filter, Finset.mem_offDiag]
            exact ⟨⟨Finset.mem_erase.mpr ⟨ha_ne, Finset.mem_univ a⟩,
              Finset.mem_erase.mpr ⟨hb_ne, Finset.mem_univ b⟩, hab.ne⟩, hab⟩
          calc A = PrimeGaps.rhoFlat W X m a b p (u, u', ρ) := hrho_eq.symm
            _ ≤ ∑ p ∈ P, PrimeGaps.rhoFlat W X m a b p (u, u', ρ) :=
                Finset.single_le_sum (fun p _ ↦ hrho_nonneg a b p) hpP
            _ ≤ ∑ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
                  ∑ p ∈ P, PrimeGaps.rhoFlat W X m ij.1 ij.2 p (u, u', ρ) :=
                Finset.single_le_sum
                  (fun ij _ ↦ Finset.sum_nonneg (fun p _ ↦ hrho_nonneg ij.1 ij.2 p)) hab_mem
            _ ≤ _ := le_add_of_nonneg_left hCross_block_nonneg
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact main i j hi_ne hj_ne hlt hncop
        · exact main j i hj_ne hi_ne hgt fun h ↦ hncop h.symm

/-- Under any guard `P`, the iterated sum of `aSum u * aSum u' * bSum ρ` over `u`, `u'`, `ρ` is the
sum over the triple. -/
theorem PrimeGaps.tsum_guarded_prod_flat {k : ℕ} (W : ℕ) (X : ℝ) (m : Fin k)
    (P : (Fin k → ℕ) → ℕ → ℕ → Prop) [∀ ρ u u', Decidable (P ρ u u')] :
    (∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), (if P ρ u u' then
        PrimeGaps.aSum W X u * PrimeGaps.aSum W X u' * PrimeGaps.bSum W X m ρ else 0)) =
      ∑' q : ℕ × ℕ × (Fin k → ℕ), (if P q.2.2 q.1 q.2.1 then
        PrimeGaps.aSum W X q.1 * PrimeGaps.aSum W X q.2.1 * PrimeGaps.bSum W X m q.2.2 else 0) :=
  PrimeGaps.triple_tsum_eq_prod _ (by
    refine (PrimeGaps.prod_flat_support_finite W X (1 : ℝ) m).subset fun q hq ↦ ?_
    simp only [Function.mem_support, one_mul] at hq ⊢
    exact fun hz ↦ hq (by split; exacts [hz, rfl]))

/-- `∑' q, crossFlat W X m i p q` as the triple sum over `u`, `u'`, `ρ`. -/
theorem PrimeGaps.tsum_crossFlat_eq {k : ℕ} (W : ℕ) (X : ℝ) (m i : Fin k) (p : ℕ) :
    (∑' q : ℕ × ℕ × (Fin k → ℕ), PrimeGaps.crossFlat W X m i p q) =
      ∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), (if p ∣ u * u' ∧ p ∣ ρ i then
            PrimeGaps.aSum W X u * PrimeGaps.aSum W X u' * PrimeGaps.bSum W X m ρ else 0) := by
  rw [PrimeGaps.tsum_guarded_prod_flat W X m fun ρ u u' ↦ p ∣ u * u' ∧ p ∣ ρ i]
  rfl

/-- `∑' q, rhoFlat W X m i j p q` as the triple sum over `u`, `u'`, `ρ`. -/
theorem PrimeGaps.tsum_rhoFlat_eq {k : ℕ} (W : ℕ) (X : ℝ) (m i j : Fin k) (p : ℕ) :
    (∑' q : ℕ × ℕ × (Fin k → ℕ), PrimeGaps.rhoFlat W X m i j p q) =
      ∑' (u : ℕ), ∑' (u' : ℕ), ∑' (ρ : Fin k → ℕ), (if p ∣ ρ i ∧ p ∣ ρ j then
            PrimeGaps.aSum W X u * PrimeGaps.aSum W X u' * PrimeGaps.bSum W X m ρ else 0) := by
  rw [PrimeGaps.tsum_guarded_prod_flat W X m fun ρ _ _ ↦ p ∣ ρ i ∧ p ∣ ρ j]
  rfl

/-- `∑' q, collisionFlat W X m q = collisionMass W X m`. -/
theorem PrimeGaps.tsum_collisionFlat_eq {k : ℕ} (W : ℕ) (X : ℝ) (m : Fin k) :
    (∑' q : ℕ × ℕ × (Fin k → ℕ), PrimeGaps.collisionFlat W X m q) =
      PrimeGaps.collisionMass W X m := by
  rw [PrimeGaps.collisionMass, PrimeGaps.tsum_guarded_prod_flat W X m
    fun ρ u u' ↦ ¬((∀ i, i ≠ m → (u * u').Coprime (ρ i)) ∧ (∀ i j, i ≠ j → (ρ i).Coprime (ρ j)))]
  rfl
