/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.ExpandDrop.Blocks

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The expand-and-drop bound

Assembles the collision bounds into `lem_S2m_expand_drop`.

## Main results

* `PrimeGaps.collisionMass_le_primeSum`
* `PrimeGaps.collisionMass_le_tail`
* `PrimeGaps.gSum_cutoff_le`
* `PrimeGaps.failure_le_majorant_tail`
* `PrimeGaps.lem_S2m_drop_couplings_bound`
* `PrimeGaps.lem_S2m_expand_drop`
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius
open scoped Finset

open scoped ArithmeticFunction.detotient
open PrimeGaps

/-- **Diagonal-pair collision bound.**  Summing `rhoBlock_le` over the `(k-1)(k-2)/2` unordered
pairs `i < j` of coordinates other than `m`, the total `rhoFlat` mass over the prime set `P` is at
most `(k-1)(k-2)/2 * (∑_{p ∈ P} (p-2)⁻²) * (sumA W X) ^ 2 * (gSum W X) ^ (k-1)`. -/
private theorem PrimeGaps.sum_rhoFlat_le {k : ℕ} (hk : 2 ≤ k) (W : ℕ) (X : ℝ) (m : Fin k)
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, p.Prime ∧ 3 ≤ p) :
    (∑ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
        ∑ p ∈ P, (∑' q, PrimeGaps.rhoFlat W X m ij.1 ij.2 p q)) ≤
      ((k : ℝ) - 1) * ((k : ℝ) - 2) / 2 * ((∑ p ∈ P, (1 / ((p : ℝ) - 2)) ^ 2) *
        ((PrimeGaps.MaynardOffDiagonal.sumA W X) ^ 2 * (PrimeGaps.gSum W X) ^ (k - 1))) := by
  classical
  set PH : ℝ := PrimeGaps.MaynardOffDiagonal.sumA W X with hPH
  set GG : ℝ := PrimeGaps.gSum W X with hGG
  have hbd : ∀ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
      (∑ p ∈ P, (∑' q, PrimeGaps.rhoFlat W X m ij.1 ij.2 p q)) ≤
      (∑ p ∈ P, (1 / ((p : ℝ) - 2)) ^ 2 * (PH ^ 2 * GG ^ (k - 1))) := by
    intro ij hij
    rw [Finset.mem_filter, Finset.mem_offDiag] at hij
    refine Finset.sum_le_sum fun p hp ↦ ?_
    rw [PrimeGaps.tsum_rhoFlat_eq]
    have := PrimeGaps.rhoBlock_le hk W X m ij.1 ij.2 (Finset.ne_of_mem_erase hij.1.1)
      (Finset.ne_of_mem_erase hij.1.2.1) hij.1.2.2 p (hPprime p hp).1 (hPprime p hp).2
    rw [hPH, hGG]
    exact this.trans_eq (by ring)
  have hcard : #{ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2} =
      (k - 1) * (k - 2) / 2 := by
    set s := Finset.univ.erase m with hs
    have hsc : #s = k - 1 := by
      rw [hs, Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
    have hbij : #(s.offDiag.filter (fun ij ↦ ij.1 < ij.2)) =
        #(s.offDiag.filter (fun ij ↦ ij.2 < ij.1)) := by
      refine Finset.card_bij' (fun ij _ ↦ Prod.swap ij) (fun ij _ ↦ Prod.swap ij) ?_ ?_
        (fun ij _ ↦ Prod.swap_swap ij) (fun ij _ ↦ Prod.swap_swap ij) <;>
      · intro ij hij
        rw [Finset.mem_filter, Finset.mem_offDiag] at hij ⊢
        exact ⟨⟨hij.1.2.1, hij.1.1, fun h ↦ hij.1.2.2 h.symm⟩, hij.2⟩
    have hunion : #(s.offDiag.filter (fun ij ↦ ij.1 < ij.2)) +
        #(s.offDiag.filter (fun ij ↦ ij.2 < ij.1)) = #s.offDiag := by
      have hfe : s.offDiag.filter (fun ij ↦ ij.2 < ij.1) =
          s.offDiag.filter (fun ij ↦ ¬ ij.1 < ij.2) :=
        Finset.filter_congr fun ij hij ↦ ⟨fun h ↦ not_lt.2 h.le,
            fun h ↦ (not_lt.1 h).lt_of_ne (Ne.symm (Finset.mem_offDiag.1 hij).2.2)⟩
      rw [hfe, Finset.card_filter_add_card_filter_not]
    have hoff : #s.offDiag = (k - 1) * (k - 2) := by
      rw [Finset.offDiag_card, hsc, show k - 2 = k - 1 - 1 from by omega,
        Nat.mul_sub_one (k - 1) (k - 1)]
    rw [hbij, hoff] at hunion
    omega
  calc (∑ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
          ∑ p ∈ P, (∑' q, PrimeGaps.rhoFlat W X m ij.1 ij.2 p q)) ≤
      ∑ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
          (∑ p ∈ P, (1 / ((p : ℝ) - 2)) ^ 2 * (PH ^ 2 * GG ^ (k - 1))) := Finset.sum_le_sum hbd
    _ = #{ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2}
          • (∑ p ∈ P, (1 / ((p : ℝ) - 2)) ^ 2 * (PH ^ 2 * GG ^ (k - 1))) := Finset.sum_const _
    _ = ((k : ℝ) - 1) * ((k : ℝ) - 2) / 2 *
          ((∑ p ∈ P, (1 / ((p : ℝ) - 2)) ^ 2) * (PH ^ 2 * GG ^ (k - 1))) := by
        rw [hcard, nsmul_eq_mul]
        have hkk : (((k - 1) * (k - 2) / 2 : ℕ) : ℝ) = ((k : ℝ) - 1) * ((k : ℝ) - 2) / 2 := by
          have hdvd : 2 ∣ (k - 1) * (k - 2) := by
            have h := Nat.two_dvd_mul_sub_one (k - 1)
            rwa [show k - 1 - 1 = k - 2 from by omega] at h
          rw [Nat.cast_div hdvd (by norm_num), Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k),
            Nat.cast_sub (by omega : 2 ≤ k)]
          norm_num
        rw [hkk, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]

/-- `collisionMass W X m ≤ (∑_{D < p ≤ X} (1 / (p - 2)) ^ 2) * (2 (k - 1) + (k - 1)(k - 2) / 2) *
(sumA W X) ^ 2 * (gSum W X) ^ (k - 1)`, when `2 ≤ D` and every prime coprime to `W` exceeds `D`. -/
theorem PrimeGaps.collisionMass_le_primeSum {k : ℕ} (hk : 2 ≤ k) (W D : ℕ) (X : ℝ)
    (m : Fin k) (hD2 : 2 ≤ D)
    (hWcop : ∀ p : ℕ, p.Prime → p.Coprime W → D < p) :
    PrimeGaps.collisionMass W X m ≤ (∑ p ∈ (Finset.Icc (D + 1) ⌊X⌋₊).filter Nat.Prime,
            (1 / ((p : ℝ) - 2)) ^ 2) * ((2 * ((k : ℝ) - 1) + ((k : ℝ) - 1) * ((k : ℝ) - 2) / 2) *
              (PrimeGaps.MaynardOffDiagonal.sumA W X) ^ 2 * (PrimeGaps.gSum W X) ^ (k - 1)) := by
  classical
  set P : Finset ℕ := (Finset.Icc (D + 1) ⌊X⌋₊).filter Nat.Prime with hP
  set PH : ℝ := PrimeGaps.MaynardOffDiagonal.sumA W X with hPH
  set GG : ℝ := PrimeGaps.gSum W X with hGG
  have hPprime : ∀ p ∈ P, p.Prime ∧ 3 ≤ p := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_Icc] at hp
    exact ⟨hp.2, by omega⟩
  rw [← PrimeGaps.tsum_collisionFlat_eq W X m]
  have hprod_nonneg : ∀ q : ℕ × ℕ × (Fin k → ℕ), (0 : ℝ) ≤
      PrimeGaps.aSum W X q.1 * PrimeGaps.aSum W X q.2.1 * PrimeGaps.bSum W X m q.2.2 := fun q ↦
    mul_nonneg (mul_nonneg (PrimeGaps.aSum_nonneg W X q.1) (PrimeGaps.aSum_nonneg W X q.2.1))
      (PrimeGaps.bSum_nonneg W X m q.2.2)
  -- Every `*Flat` function is the product `aSum * aSum * bSum` cut off by a predicate, so it is
  -- squeezed between `0` and the summable `prodFlat`.
  have hsum_of : ∀ f : ℕ × ℕ × (Fin k → ℕ) → ℝ, (∀ q, f q = 0 ∨ f q =
      PrimeGaps.aSum W X q.1 * PrimeGaps.aSum W X q.2.1 * PrimeGaps.bSum W X m q.2.2) →
      Summable f := by
    intro f hf
    refine Summable.of_nonneg_of_le (fun q ↦ ?_) (fun q ↦ ?_) (PrimeGaps.prodFlat_summable W X m)
    · exact (hf q).elim (fun h ↦ h.ge) fun h ↦ (hprod_nonneg q).trans h.ge
    · exact (hf q).elim (fun h ↦ h.le.trans (hprod_nonneg q)) fun h ↦ h.le
  have hcross_sum : ∀ (i : Fin k) (p : ℕ), Summable (PrimeGaps.crossFlat W X m i p) :=
    fun i p ↦ hsum_of _ fun q ↦ by
      simp only [PrimeGaps.crossFlat]; split
      exacts [Or.inr rfl, Or.inl rfl]
  have hrho_sum : ∀ (i j : Fin k) (p : ℕ), Summable (PrimeGaps.rhoFlat W X m i j p) :=
    fun i j p ↦ hsum_of _ fun q ↦ by
      simp only [PrimeGaps.rhoFlat]; split
      exacts [Or.inr rfl, Or.inl rfl]
  have hcoll_sum : Summable (PrimeGaps.collisionFlat W X m) :=
    hsum_of _ fun q ↦ by
      simp only [PrimeGaps.collisionFlat]; split
      exacts [Or.inr rfl, Or.inl rfl]
  have hcrossFam : ∀ i ∈ Finset.univ.erase m,
      Summable (fun q : ℕ × ℕ × (Fin k → ℕ) ↦ ∑ p ∈ P, PrimeGaps.crossFlat W X m i p q) :=
    fun i _ ↦ summable_sum (fun p _ ↦ hcross_sum i p)
  have hrhoFam : ∀ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
      Summable (fun q : ℕ × ℕ × (Fin k → ℕ) ↦ ∑ p ∈ P, PrimeGaps.rhoFlat W X m ij.1 ij.2 p q) :=
    fun ij _ ↦ summable_sum (fun p _ ↦ hrho_sum ij.1 ij.2 p)
  have hcrossS : Summable (fun q : ℕ × ℕ × (Fin k → ℕ) ↦
      ∑ i ∈ Finset.univ.erase m, ∑ p ∈ P, PrimeGaps.crossFlat W X m i p q) :=
    summable_sum hcrossFam
  have hrhoS : Summable (fun q : ℕ × ℕ × (Fin k → ℕ) ↦
      ∑ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
        ∑ p ∈ P, PrimeGaps.rhoFlat W X m ij.1 ij.2 p q) :=
    summable_sum hrhoFam
  have hstep2 : (∑' q, PrimeGaps.collisionFlat W X m q) ≤
      ∑' q, ((∑ i ∈ Finset.univ.erase m, ∑ p ∈ P, PrimeGaps.crossFlat W X m i p q) +
          (∑ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
              ∑ p ∈ P, PrimeGaps.rhoFlat W X m ij.1 ij.2 p q)) :=
    Summable.tsum_le_tsum (PrimeGaps.collisionFlat_le_union W D X m hWcop) hcoll_sum
      (hcrossS.add hrhoS)
  rw [Summable.tsum_add hcrossS hrhoS, Summable.tsum_finsetSum hcrossFam,
    Summable.tsum_finsetSum hrhoFam] at hstep2
  have hpullCross : ∀ i : Fin k,
      (∑' q : ℕ × ℕ × (Fin k → ℕ), ∑ p ∈ P, PrimeGaps.crossFlat W X m i p q) =
        ∑ p ∈ P, ∑' q : ℕ × ℕ × (Fin k → ℕ), PrimeGaps.crossFlat W X m i p q :=
    fun i ↦ Summable.tsum_finsetSum (fun p _ ↦ hcross_sum i p)
  have hpullRho : ∀ i j : Fin k,
      (∑' q : ℕ × ℕ × (Fin k → ℕ), ∑ p ∈ P, PrimeGaps.rhoFlat W X m i j p q) =
        ∑ p ∈ P, ∑' q : ℕ × ℕ × (Fin k → ℕ), PrimeGaps.rhoFlat W X m i j p q :=
    fun i j ↦ Summable.tsum_finsetSum (fun p _ ↦ hrho_sum i j p)
  simp only [hpullCross, hpullRho] at hstep2
  refine hstep2.trans ?_
  have hcross_bd : (∑ i ∈ Finset.univ.erase m, ∑ p ∈ P, (∑' q, PrimeGaps.crossFlat W X m i p q)) ≤
      2 * ((k : ℝ) - 1) * ((∑ p ∈ P, (1 / ((p : ℝ) - 2)) ^ 2) * (PH ^ 2 * GG ^ (k - 1))) := by
    have hbd : ∀ i ∈ Finset.univ.erase m, (∑ p ∈ P, (∑' q, PrimeGaps.crossFlat W X m i p q)) ≤
        (∑ p ∈ P, 2 * (1 / ((p : ℝ) - 2)) ^ 2 * (PH ^ 2 * GG ^ (k - 1))) := by
      intro i hi
      refine Finset.sum_le_sum fun p hp ↦ ?_
      rw [PrimeGaps.tsum_crossFlat_eq]
      have := PrimeGaps.crossBlock_le hk W X m i (Finset.ne_of_mem_erase hi) p
        (hPprime p hp).1 (hPprime p hp).2
      rw [hPH, hGG]
      exact this.trans_eq (by ring)
    calc (∑ i ∈ Finset.univ.erase m, ∑ p ∈ P, (∑' q, PrimeGaps.crossFlat W X m i p q))
        ≤ ∑ i ∈ Finset.univ.erase m,
            (∑ p ∈ P, 2 * (1 / ((p : ℝ) - 2)) ^ 2 * (PH ^ 2 * GG ^ (k - 1))) :=
          Finset.sum_le_sum hbd
      _ = #(Finset.univ.erase m)
            • (∑ p ∈ P, 2 * (1 / ((p : ℝ) - 2)) ^ 2 * (PH ^ 2 * GG ^ (k - 1))) :=
          Finset.sum_const _
      _ = 2 * ((k : ℝ) - 1) * ((∑ p ∈ P, (1 / ((p : ℝ) - 2)) ^ 2) * (PH ^ 2 * GG ^ (k - 1))) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
          simpa only [Finset.mul_sum, Finset.sum_mul] using Finset.sum_congr rfl fun p _ ↦ by ring
  calc (∑ i ∈ Finset.univ.erase m, ∑ p ∈ P, (∑' q, PrimeGaps.crossFlat W X m i p q)) +
        (∑ ij ∈ {ij ∈ (Finset.univ.erase m).offDiag | ij.1 < ij.2},
            ∑ p ∈ P, (∑' q, PrimeGaps.rhoFlat W X m ij.1 ij.2 p q)) ≤
      2 * ((k : ℝ) - 1) * ((∑ p ∈ P, (1 / ((p : ℝ) - 2)) ^ 2) * (PH ^ 2 * GG ^ (k - 1))) +
          ((k : ℝ) - 1) * ((k : ℝ) - 2) / 2 *
              ((∑ p ∈ P, (1 / ((p : ℝ) - 2)) ^ 2) * (PH ^ 2 * GG ^ (k - 1))) :=
        add_le_add hcross_bd (PrimeGaps.sum_rhoFlat_le hk W X m P hPprime)
    _ = (∑ p ∈ P, (1 / ((p : ℝ) - 2)) ^ 2) *
          ((2 * ((k : ℝ) - 1) + ((k : ℝ) - 1) * ((k : ℝ) - 2) / 2) *
              (PrimeGaps.MaynardOffDiagonal.sumA W X) ^ 2 * (PrimeGaps.gSum W X) ^ (k - 1)) := by
        rw [hPH, hGG]; ring

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `collisionMass (W N) R m ≤ Ktail₀ * (sumA (W N) R) ^ 2 * (gSum (W N) R) ^ (k - 1) / D₀ N` for
some `Ktail₀ ≥ 0` and all large `N`. -/
theorem PrimeGaps.collisionMass_le_tail {k : ℕ} (hk : 2 ≤ k) : ∃ Ktail₀ : ℝ, 0 ≤ Ktail₀ ∧
      ∀ (θ δ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 → 0 < δ → δ < θ / 2 →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (m : Fin k), PrimeGaps.collisionMass (W N) R m ≤
          Ktail₀ * (PrimeGaps.MaynardOffDiagonal.sumA (W N) R) ^ 2 *
            (PrimeGaps.gSum (W N) R) ^ (k - 1) / PrimeGaps.D₀ (N : ℝ) := by
  obtain ⟨A, hA0, hA⟩ := PrimeGaps.prime_tail_inv_sub_two_sq
  refine ⟨18 * A * (k : ℝ) ^ 2, by positivity, ?_⟩
  intro θ δ hθ hδ hδθ
  refine ⟨rexp (rexp (rexp 2)), ?_⟩
  intro N hN m
  set RR : ℝ := R
  have hD0 : (2 : ℝ) ≤ PrimeGaps.D₀ (N : ℝ) := MaynardOffDiagonal.two_le_D0_of_large hN
  have hD0pos : (0 : ℝ) < PrimeGaps.D₀ (N : ℝ) := by linarith
  set D : ℕ := ⌊PrimeGaps.D₀ (N : ℝ)⌋₊
  have hfloorgt : PrimeGaps.D₀ (N : ℝ) - 1 < (D : ℝ) := by
    have := Nat.lt_floor_add_one (PrimeGaps.D₀ (N : ℝ)); linarith
  have hD2 : 2 ≤ D := Nat.le_floor (by exact_mod_cast hD0)
  have hDposR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < D)
  have hWcop : ∀ p : ℕ, p.Prime → p.Coprime (W N) → D < p :=
    fun p ↦ PrimeGaps.floor_D0_lt_of_prime_coprime N p
  have hprime := PrimeGaps.collisionMass_le_primeSum hk (W N) D RR m hD2 hWcop
  set S : Finset ℕ := (Finset.Icc (D + 1) ⌊RR⌋₊).filter Nat.Prime with hSdef
  set Ck : ℝ := 2 * ((k : ℝ) - 1) + ((k : ℝ) - 1) * ((k : ℝ) - 2) / 2 with hCkdef
  set P : ℝ := (PrimeGaps.MaynardOffDiagonal.sumA (W N) RR) ^ 2 *
    (PrimeGaps.gSum (W N) RR) ^ (k - 1) with hPdef
  have hP_nonneg : (0 : ℝ) ≤ P := by
    rw [hPdef]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (PrimeGaps.gSum_nonneg _ _) _)
  have hSP : ∑ p ∈ S, (1 / ((p : ℝ) - 2)) ^ 2 ≤ 9 * A / (D : ℝ) := by
    have hmem : ∀ p ∈ S, D < p := by
      intro p hp; rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hp; omega
    have hterm : ∀ p ∈ S, (1 / ((p : ℝ) - 2)) ^ 2 ≤ 9 * (1 / (p : ℝ) ^ 2) := by
      intro p hp
      have hp3 : 3 ≤ p := by have := hmem p hp; omega
      have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      have hpm2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      have hkey : (p : ℝ) ^ 2 ≤ 9 * ((p : ℝ) - 2) ^ 2 := by
        linarith only [mul_nonneg (by linarith only [hp3R] : (0 : ℝ) ≤ 2 * (p : ℝ) - 3)
          (by linarith only [hp3R] : (0 : ℝ) ≤ (p : ℝ) - 3)]
      rw [div_pow, one_pow, mul_one_div]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((p : ℝ) - 2) ^ 2)
        (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)]
      linarith only [hkey]
    calc ∑ p ∈ S, (1 / ((p : ℝ) - 2)) ^ 2
        ≤ ∑ p ∈ S, 9 * (1 / (p : ℝ) ^ 2) := Finset.sum_le_sum hterm
      _ = 9 * ∑ p ∈ S, (1 / (p : ℝ) ^ 2) := by rw [Finset.mul_sum]
      _ ≤ 9 * (A / (D : ℝ)) := mul_le_mul_of_nonneg_left (hA D hD2 S hmem) (by norm_num)
      _ = 9 * A / (D : ℝ) := by ring
  have h9le : 9 * A / (D : ℝ) ≤ 18 * A / PrimeGaps.D₀ (N : ℝ) := by
    rw [div_le_div_iff₀ hDposR hD0pos]
    have hD0le2D : PrimeGaps.D₀ (N : ℝ) ≤ 2 * (D : ℝ) := by
      linarith only [hfloorgt, hD0]
    linarith only [mul_nonneg hA0 (sub_nonneg.mpr hD0le2D)]
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hCk_nonneg : (0 : ℝ) ≤ Ck := by
    rw [hCkdef]
    linarith only [mul_nonneg (by linarith only [hk2] : (0 : ℝ) ≤ (k : ℝ) - 1)
      (by linarith only [hk2] : (0 : ℝ) ≤ (k : ℝ) - 2), hk2]
  have hCk_le : Ck ≤ (k : ℝ) ^ 2 := by
    rw [hCkdef]
    linarith only [mul_nonneg (by linarith only [hk2] : (0 : ℝ) ≤ (k : ℝ))
      (by linarith only [hk2] : (0 : ℝ) ≤ (k : ℝ) - 1)]
  calc PrimeGaps.collisionMass (W N) RR m ≤ (∑ p ∈ S, (1 / ((p : ℝ) - 2)) ^ 2) * (Ck * P) := by
        rw [show Ck * P = Ck * PrimeGaps.MaynardOffDiagonal.sumA (W N) RR ^ 2 *
          PrimeGaps.gSum (W N) RR ^ (k - 1) from by rw [hPdef]; ring]
        exact hprime
    _ ≤ (9 * A / (D : ℝ)) * ((k : ℝ) ^ 2 * P) :=
        mul_le_mul hSP (mul_le_mul_of_nonneg_right hCk_le hP_nonneg) (by positivity) (by positivity)
    _ ≤ (18 * A / PrimeGaps.D₀ (N : ℝ)) * ((k : ℝ) ^ 2 * P) :=
        mul_le_mul_of_nonneg_right h9le (by positivity)
    _ = 18 * A * (k : ℝ) ^ 2 * (PrimeGaps.MaynardOffDiagonal.sumA (W N) RR) ^ 2 *
          (PrimeGaps.gSum (W N) RR) ^ (k - 1) / PrimeGaps.D₀ (N : ℝ) := by
        rw [hPdef]; ring

/-- `gSum W R ≤ Cg * (φ W / W) * log R` for an absolute `Cg ≥ 0`, uniformly over squarefree
`W ≥ 1` with every prime factor at most `R`, given `e ≤ R` and `1 ≤ (φ W / W) * log R`. -/
theorem PrimeGaps.gSum_cutoff_le : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (R : ℝ) (W : ℕ), Squarefree W → 1 ≤ W →
      (∀ p ∈ W.primeFactors, (p : ℝ) ≤ R) → rexp 1 ≤ R →
      (1 : ℝ) ≤ (W.totient : ℝ) / (W : ℝ) * Real.log R →
      PrimeGaps.gSum W R ≤ Cg * ((W.totient : ℝ) / (W : ℝ)) * Real.log R := by
  obtain ⟨Cc, hCc0, hcut⟩ := lem_S2m_g_coord_cutoff
  refine ⟨Cc + 1, by positivity, ?_⟩
  intro R W hWsq hW1 hpf hRe h1
  obtain ⟨hsum_le, hbound⟩ := hcut R W hWsq hW1 hpf hRe
  have hRpos : (0 : ℝ) < R := (Real.exp_pos 1).trans_le hRe
  have hbdry := PrimeGaps.gSum_le_range_add_one W R hRpos
  have htsum_eq : (∑' r : ℕ, if 1 ≤ r ∧ (r : ℝ) < R ∧ r.Coprime W ∧ Squarefree r
        then (1 : ℝ) / (g r : ℝ) else 0) =
        ∑ r ∈ (Finset.range ⌈R⌉₊).filter (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R ∧ Nat.Coprime r W),
            (μ r : ℝ) ^ 2 / (g r : ℝ) := by
    have hvanish : ∀ b ∉ (Finset.range ⌈R⌉₊).filter
        (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R ∧ Nat.Coprime r W),
        (if 1 ≤ b ∧ (b : ℝ) < R ∧ b.Coprime W ∧ Squarefree b
          then (1 : ℝ) / (g b : ℝ) else 0) = 0 := by
      intro b hb
      by_cases hguard : 1 ≤ b ∧ (b : ℝ) < R ∧ b.Coprime W ∧ Squarefree b
      · refine absurd ?_ hb
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_ceil.mpr hguard.2.1, hguard.1, hguard.2.1, hguard.2.2.1⟩
      · exact if_neg hguard
    rw [tsum_eq_sum hvanish]
    refine Finset.sum_congr rfl fun r hr ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨_, hr0, hrR, hrcop⟩ := hr
    by_cases hsf : Squarefree r
    · rw [if_pos ⟨hr0, hrR, hrcop, hsf⟩]
      have hmu : (μ r : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      rw [hmu]
    · rw [if_neg (fun h ↦ hsf h.2.2.2), ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      push_cast; ring
  rw [← htsum_eq] at hbdry
  have hMeq : Cc * ((W.totient : ℝ) * Real.log R / (W : ℝ)) =
      Cc * ((W.totient : ℝ) / (W : ℝ) * Real.log R) := by ring
  rw [hMeq] at hbound
  have hgnn : ∀ r : ℕ, (0 : ℝ) ≤ 1 / (g r : ℝ) := fun r ↦ by positivity
  have hdom : ∀ r : ℕ, (if 1 ≤ r ∧ (r : ℝ) < R ∧ r.Coprime W ∧ Squarefree r
        then (1 : ℝ) / (g r : ℝ) else 0) ≤ (if 1 ≤ r ∧ (r : ℝ) ≤ R ∧ r.Coprime W ∧ Squarefree r
        then (1 : ℝ) / (g r : ℝ) else 0) := by
    intro r
    by_cases hlt : 1 ≤ r ∧ (r : ℝ) < R ∧ r.Coprime W ∧ Squarefree r
    · rw [if_pos hlt, if_pos ⟨hlt.1, hlt.2.1.le, hlt.2.2.1, hlt.2.2.2⟩]
    · rw [if_neg hlt]; split_ifs; exacts [hgnn r, le_rfl]
  have hsum_lt : Summable (fun r : ℕ ↦ if 1 ≤ r ∧ (r : ℝ) < R ∧ r.Coprime W ∧ Squarefree r
        then (1 : ℝ) / (g r : ℝ) else 0) :=
    Summable.of_nonneg_of_le
      (fun r ↦ by split_ifs with h; exacts [hgnn r, le_rfl]) hdom hsum_le
  have hmono := hsum_lt.tsum_le_tsum hdom hsum_le
  have hgoal_eq : (Cc + 1) * ((W.totient : ℝ) / (W : ℝ)) * Real.log R =
      Cc * ((W.totient : ℝ) / (W : ℝ) * Real.log R) +
        (W.totient : ℝ) / (W : ℝ) * Real.log R := by ring
  rw [hgoal_eq]
  linarith [hbdry, hbound, h1, hmono]

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `failureMass R (W N) F m ≤ Ktail * Fmax F ^ 2 * φ (W N) ^ (k + 1) * (log R) ^ (k + 1) /
(W N ^ (k + 1) * D₀ N)` for some `Ktail ≥ 0` and all large `N`. -/
theorem PrimeGaps.failure_le_majorant_tail {k : ℕ} (hk : 2 ≤ k) : ∃ Ktail : ℝ, 0 ≤ Ktail ∧
      ∀ (θ δ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 → 0 < δ → δ < θ / 2 →
      ∀ (F : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F → Function.support F ⊆ 𝓡 k →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (m : Fin k), failureMass R (W N) F m ≤
          Ktail * (MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ (k + 1) *
            (Real.log R) ^ (k + 1) / ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  obtain ⟨Cg, hCg0, hCg⟩ := PrimeGaps.gSum_cutoff_le
  obtain ⟨Ktail₀, hKtail0, hTail⟩ := PrimeGaps.collisionMass_le_tail hk
  refine ⟨Ktail₀ * (Cg ^ 2 * Cg ^ (k - 1)), by positivity, ?_⟩
  intro θ δ hθ hδ hδθ F hF hsupp
  have hδ' : (θ / 2 - δ) ∈ Set.Ioo (0 : ℝ) ((2 * θ - 4 * δ) / 2) := ⟨by linarith, by linarith⟩
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (PrimeGaps.R_eventually_ge θ δ hδθ 2)
  obtain ⟨cN, hcN⟩ := hTail θ δ hθ hδ hδθ
  obtain ⟨N₁, _, hpf'⟩ := MaynardOffDiagonal.primorial_D0_primeFactors_le_Rval
    (2 * θ - 4 * δ) (θ / 2 - δ) (by linarith)
  obtain ⟨N₂, _, hF2'⟩ :=
    MaynardOffDiagonal.phi_logRval_ge_one_of_large (2 * θ - 4 * δ) (θ / 2 - δ) hδ'
  refine ⟨max (max (max (a : ℝ) cN) (max N₁ N₂)) (rexp (rexp (rexp 2))), ?_⟩
  intro N hN m
  obtain ⟨hNrest, hNe⟩ := max_le_iff.mp hN
  obtain ⟨hNac, hN12⟩ := max_le_iff.mp hNrest
  obtain ⟨hNa', hNc⟩ := max_le_iff.mp hNac
  obtain ⟨hN₁, hN₂⟩ := max_le_iff.mp hN12
  have hNa : a ≤ N := by exact_mod_cast hNa'
  have hR1 : (1 : ℝ) < R := one_lt_two.trans_le (ha N hNa)
  have hWpos : 0 < W N := PrimeGaps.W_pos
  have hWposR : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast hWpos
  have hD0 : (2 : ℝ) ≤ PrimeGaps.D₀ (N : ℝ) := MaynardOffDiagonal.two_le_D0_of_large hNe
  have hD0pos : (0 : ℝ) < PrimeGaps.D₀ (N : ℝ) := by linarith
  have hW2 : 2 ∣ W N := by
    rw [PrimeGaps.W_eq_primorial_D₀]
    exact MaynardOffDiagonal.prime_dvd_primorial_D0 (N : ℝ) 2 Nat.prime_two
      (Nat.le_floor (by exact_mod_cast hD0))
  set RR : ℝ := R with hRR
  have hlogR_nonneg : (0 : ℝ) ≤ Real.log RR := Real.log_nonneg (by rw [hRR]; linarith)
  have hExpEq : (2 * θ - 4 * δ) / 2 - (θ / 2 - δ) = θ / 2 - δ := by ring
  have h1 : (1 : ℝ) ≤ ((W N).totient : ℝ) / (W N : ℝ) * Real.log RR := by
    have h := hF2' (N : ℝ) hN₂
    rw [hExpEq,
      show (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) = W N from (PrimeGaps.W_eq_primorial_D₀).symm] at h
    rwa [hRR]
  have hpf : ∀ p ∈ (W N).primeFactors, (p : ℝ) ≤ RR := by
    intro p hp
    have h := hpf' (N : ℝ) hN₁ p (by rwa [PrimeGaps.W_eq_primorial_D₀] at hp)
    rw [hExpEq] at h
    rwa [hRR]
  have hRe : rexp 1 ≤ RR := by
    have hRpos : (0 : ℝ) < RR := by rw [hRR]; linarith
    have hratio_le : ((W N).totient : ℝ) / (W N : ℝ) ≤ 1 := by
      rw [div_le_one hWposR]; exact_mod_cast Nat.totient_le (W N)
    have hlogR1 : (1 : ℝ) ≤ Real.log RR := by
      linarith only [h1, mul_nonneg (sub_nonneg.mpr hratio_le) hlogR_nonneg]
    exact (Real.le_log_iff_exp_le hRpos).mp hlogR1
  have hg : PrimeGaps.gSum (W N) RR ≤ Cg * (((W N).totient : ℝ) / (W N : ℝ)) * Real.log RR :=
    hCg RR (W N) PrimeGaps.W_squarefree PrimeGaps.W_pos hpf hRe h1
  have hphi_nonneg : (0 : ℝ) ≤ PrimeGaps.MaynardOffDiagonal.sumA (W N) RR := sumA_nonneg RR (W N)
  have hg_nonneg : (0 : ℝ) ≤ PrimeGaps.gSum (W N) RR := PrimeGaps.gSum_nonneg _ _
  have hFmax_nonneg : (0 : ℝ) ≤ (MaynardSmoothY.Fmax F) ^ 2 := sq_nonneg _
  set MM : ℝ := (((W N).totient : ℝ) / (W N : ℝ)) * Real.log RR with hMM
  have hphi' : PrimeGaps.MaynardOffDiagonal.sumA (W N) RR ≤ Cg * MM := by
    rw [hMM, ← mul_assoc]; exact (PrimeGaps.sumA_le_gSum (W N) RR hW2).trans hg
  have hg' : PrimeGaps.gSum (W N) RR ≤ Cg * MM := by rw [hMM, ← mul_assoc]; exact hg
  have hmaj := PrimeGaps.failureMass_le_collision_majorant R (W N) F hF hsupp
    (by rwa [← hRR]) m
  rw [← hRR] at hmaj
  have htail := hcN N hNc m
  rw [← hRR] at htail
  have hexp : 2 + (k - 1) = k + 1 := by omega
  have hkey : (Cg * MM) ^ 2 * (Cg * MM) ^ (k - 1) =
      (Cg ^ 2 * Cg ^ (k - 1)) * (((W N).totient : ℝ) ^ (k + 1) *
          (Real.log RR) ^ (k + 1) / ((W N : ℝ) ^ (k + 1))) := by
    rw [← pow_add, hexp, mul_pow, hMM, mul_pow, div_pow, ← pow_add, hexp]
    field_simp
  calc failureMass R (W N) F m
      ≤ (MaynardSmoothY.Fmax F) ^ 2 * (Ktail₀ * (PrimeGaps.MaynardOffDiagonal.sumA (W N) RR) ^ 2 *
          (PrimeGaps.gSum (W N) RR) ^ (k - 1) / PrimeGaps.D₀ (N : ℝ)) :=
        hmaj.trans (mul_le_mul_of_nonneg_left htail hFmax_nonneg)
    _ ≤ (MaynardSmoothY.Fmax F) ^ 2 *
          (Ktail₀ * (Cg * MM) ^ 2 * (Cg * MM) ^ (k - 1) / PrimeGaps.D₀ (N : ℝ)) := by
        gcongr
    _ = Ktail₀ * (Cg ^ 2 * Cg ^ (k - 1)) * (MaynardSmoothY.Fmax F) ^ 2 *
          ((W N).totient : ℝ) ^ (k + 1) * (Real.log R) ^ (k + 1) /
          ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
        rw [← hRR, show (MaynardSmoothY.Fmax F) ^ 2 *
              (Ktail₀ * (Cg * MM) ^ 2 * (Cg * MM) ^ (k - 1) / PrimeGaps.D₀ (N : ℝ)) =
            (MaynardSmoothY.Fmax F) ^ 2 * Ktail₀ * ((Cg * MM) ^ 2 * (Cg * MM) ^ (k - 1)) /
              PrimeGaps.D₀ (N : ℝ) by ring, hkey]
        field_simp

namespace PrimeGaps

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `|coupledSum R (W N) F m - decoupledSum R (W N) F m| ≤ C * Fmax F ^ 2 * φ (W N) ^ (k + 1) *
(log R) ^ (k + 1) / (W N ^ (k + 1) * D₀ N)` for some `C ≥ 0` and all large `N`. -/
theorem lem_S2m_drop_couplings_bound {k : ℕ} (hk : 2 ≤ k) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (θ δ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 → 0 < δ → δ < θ / 2 →
      ∀ (F : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F → Function.support F ⊆ 𝓡 k →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (m : Fin k),
        |coupledSum R (W N) F m - decoupledSum R (W N) F m| ≤
          C * (MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ (k + 1) *
            (Real.log R) ^ (k + 1) / ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  obtain ⟨Cfail, hCfail0, hfail⟩ := PrimeGaps.failure_le_majorant_tail hk
  refine ⟨Cfail, hCfail0, ?_⟩
  intro θ δ hθ hδ hδθ F hF hsupp
  obtain ⟨N₀, hN₀⟩ := hfail θ δ hθ hδ hδθ F hF hsupp
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (PrimeGaps.R_eventually_ge θ δ hδθ 2)
  refine ⟨max N₀ (a : ℝ), ?_⟩
  intro N hN m
  have hNN₀ : N₀ ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNa : a ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hR : 1 < R := one_lt_two.trans_le (ha N hNa)
  exact (drop_difference_le_failure_mass R (W N) hR F hsupp m).trans (hN₀ N hNN₀ m)

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The diagonal sum `∑' r, (yInverseSum (l₀ R (W N) F) m r) ^ 2 / ∏_{i ≠ m} g (r i)` differs from
`decoupledSum R (W N) F m` by at most `C * Fmax F ^ 2 * φ (W N) ^ (k + 1) * (log R) ^ (k + 1) /
(W N ^ (k + 1) * D₀ N)`, for all large `N`. -/
@[pg_tag "bg246" "lem_S2m_expand_drop"]
theorem lem_S2m_expand_drop {k : ℕ} (hk : 2 ≤ k) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H : Finset ℕ), H.Admissible → #H = k →
      ∀ (θ δ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 → 0 < δ → δ < θ / 2 →
      ∀ (F : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F → Function.support F ⊆ 𝓡 k →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (m : Fin k),
          |(∑' r : Fin k → ℕ, if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N)) then
                (yInverseSum (PrimeGaps.l₀ R (W N) (fun x ↦ F (WithLp.toLp 2 x.ofLp))) m r) ^ 2 /
                  (∏ i ∈ Finset.univ.erase m, (g (r i) : ℝ))
              else 0) - (decoupledSum R (W N) F m)| ≤
          C * (MaynardSmoothY.Fmax F) ^ 2 * ((W N).totient : ℝ) ^ (k + 1) *
            (Real.log R) ^ (k + 1) / ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  obtain ⟨C, hC0, hB⟩ := lem_S2m_drop_couplings_bound hk
  refine ⟨C, hC0, ?_⟩
  intro H hHadm hHcard θ δ hθ hδ hδθ F hF hsupp
  obtain ⟨N₀, hN₀⟩ := hB θ δ hθ hδ hδθ F hF hsupp
  refine ⟨max N₀ 1, ?_⟩
  intro N hN m
  have hN0 : (0 : ℕ) < N := by
    exact_mod_cast zero_lt_one.trans_le ((le_max_right _ _).trans hN : (1 : ℝ) ≤ (N : ℝ))
  have hNN₀ : N₀ ≤ (N : ℝ) := (le_max_left _ _).trans hN
  rw [lem_S2m_expand_diag_eq_coupled hk N hN0 δ θ F hF hsupp m]
  exact hN₀ N hNN₀ m

end PrimeGaps
