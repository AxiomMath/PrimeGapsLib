/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.HAsymptotic.Helpers

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The `H` asymptotic

The termwise bound and the quantitative assembly of the `H` asymptotic.

## Main results

* `PrimeGaps.slem_H_error_assembly`
-/

@[expose] public section

open scoped Finset

namespace PrimeGaps

/-- The termwise error bound.  For every `e`, the per-term error
`b_e * partialSumALt(V*e)(z/e) - bt_e * rhoV * log z` is bounded by `c1*D_e + c2*E_e` with
`D_e = 2*rhoV*(1+lV)*|bt_e|*(1+log e)` and `E_e = tauV*log(2Vz)/sqrt z*|b_e|*taue*sqrt e`. -/
theorem termwise_bound (S : SieveDatum) (z : ℝ) (hz : 2 ≤ z) (CA : ℝ) (hCA : 0 < CA)
    (hCAmain : ∀ (m : ℕ), 1 ≤ m → Squarefree m → ∀ (x : ℝ), 2 ≤ x →
      |PrimeGaps.MaynardOffDiagonal.sumA m x - (m.totient : ℝ) / m * (Real.log x + ellV m)| ≤
        CA * ((m.totient : ℝ) / m + (#m.divisors : ℝ) * Real.log (2 * m * x) / √x))
    (Cb : ℝ) (hCb : 0 < Cb)
    (hCbbd : ∀ (m : ℕ) (x : ℝ), 1 ≤ x →
      |partialSumALt m x - PrimeGaps.MaynardOffDiagonal.sumA m x| ≤ Cb / √x)
    (e : ℕ) :
    |S.bDefect e * partialSumALt (S.V * e) (z / e) -
        S.bTilde e * ((S.V.totient : ℝ) / S.V) * Real.log z| ≤ (1 + CA / 2) *
          (2 * ((S.V.totient : ℝ) / S.V) * (1 + ellV S.V) *
              (|S.bTilde e| * (1 + Real.log e))) + (2 * √2 + CA + Cb) *
          ((#S.V.divisors : ℝ) * Real.log (2 * S.V * z) / √z *
              (|S.bDefect e| * (#e.divisors : ℝ) * √e)) := by
  classical
  set be : ℝ := S.bDefect e with hbe
  set bte : ℝ := S.bTilde e with hbte
  set rhoV : ℝ := (S.V.totient : ℝ) / S.V with hrhoV
  set lV : ℝ := ellV S.V with hlV
  set tauV : ℝ := (#S.V.divisors : ℝ) with htauV
  set taue : ℝ := (#e.divisors : ℝ) with htaue
  set L2Vz : ℝ := Real.log (2 * S.V * z) with hL2Vz
  set D : ℝ := 2 * rhoV * (1 + lV) * (|bte| * (1 + Real.log e)) with hD
  set E : ℝ := tauV * L2Vz / √z * (|be| * taue * √e) with hE
  change |be * partialSumALt (S.V * e) (z / e) - bte * rhoV * Real.log z| ≤
      (1 + CA / 2) * D + (2 * √2 + CA + Cb) * E
  have hzpos : (0 : ℝ) < z := by linarith
  have hVpos : 0 < S.V := S.V_pos
  have hVR : (1 : ℝ) ≤ (S.V : ℝ) := by exact_mod_cast hVpos
  have hVR0 : (0 : ℝ) < (S.V : ℝ) := by linarith
  have hrhoV_nn : 0 ≤ rhoV := by rw [hrhoV]; positivity
  have hrhoV_le : rhoV ≤ 1 := by
    rw [hrhoV, div_le_one hVR0]; exact_mod_cast Nat.totient_le S.V
  have hlV_nn : 0 ≤ lV := by rw [hlV]; exact ellV_nonneg S.V
  have htauV_ge : (1 : ℝ) ≤ tauV := by
    rw [htauV]
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hVpos.ne'⟩
  have hL2Vz_ge : (1 : ℝ) ≤ L2Vz := by rw [hL2Vz]; exact log_2Vz_ge_one hVpos hz
  have hL2Vz_nn : 0 ≤ L2Vz := by linarith
  have hlogz_nn : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hlogz_le : Real.log z ≤ L2Vz := by
    rw [hL2Vz]; apply Real.log_le_log hzpos
    linarith only [mul_nonneg hzpos.le (by linarith only [hVR] : (0 : ℝ) ≤ 2 * (S.V : ℝ) - 1)]
  have hsqrtz_pos : (0 : ℝ) < √z := Real.sqrt_pos.mpr hzpos
  have hsqrte_nn : 0 ≤ √e := Real.sqrt_nonneg _
  have hbt_le : |bte| ≤ |be| := by rw [hbte, hbe]; exact bTilde_le_bDefect_abs S e
  have hbt_nn : 0 ≤ |bte| := abs_nonneg _
  have hbe_nn : 0 ≤ |be| := abs_nonneg _
  have hloge_nn : 0 ≤ Real.log e := Real.log_natCast_nonneg e
  have hD_nn : 0 ≤ D := by
    rw [hD]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hrhoV_nn) (by linarith only [hlV_nn]))
      (mul_nonneg (abs_nonneg _) (by linarith only [hloge_nn]))
  have hE_nn : 0 ≤ E := by
    rw [hE, htauV, htaue]
    exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hL2Vz_nn) (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (Real.sqrt_nonneg _))
  have hsqrt2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
  by_cases hb0 : be = 0
  · have hbt0 : bte = 0 := abs_nonpos_iff.mp (by simpa only [hb0, abs_zero] using hbt_le)
    rw [hb0, hbt0]; simp only [zero_mul, sub_zero, abs_zero]
    have h1 : 0 ≤ (1 + CA / 2) * D := mul_nonneg (by linarith) hD_nn
    have h2 : 0 ≤ (2 * √2 + CA + Cb) * E := mul_nonneg (by linarith) hE_nn
    linarith
  · have he_sf : Squarefree e := by
      by_contra h; exact hb0 (by rw [hbe]; exact S.bDefect_eq_zero_of_not_squarefree e h)
    have he_cop : e.Coprime S.V := by
      by_contra h; exact hb0 (by rw [hbe]; exact S.bDefect_eq_zero_of_not_coprime e h)
    have he_ne : e ≠ 0 := by
      intro h; apply hb0; rw [hbe, h]; exact S.bDefect_eq_zero_of_not_squarefree 0 (by simp)
    have hepos : 0 < e := Nat.pos_of_ne_zero he_ne
    have heR : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast hepos
    have heR0 : (0 : ℝ) < (e : ℝ) := by linarith
    have hsqrte_pos : 0 < √e := Real.sqrt_pos.mpr heR0
    have htaue_ge : (1 : ℝ) ≤ taue := by
      rw [htaue]
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hepos.ne'⟩
    have hVe : (S.V).Coprime e := he_cop.symm
    set m : ℕ := S.V * e with hm
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hVpos.ne' he_ne)
    have hm_sf : Squarefree m := by
      rw [hm, Nat.squarefree_mul_iff]; exact ⟨hVe, S.V_squarefree, he_sf⟩
    have hphi : ((m.totient : ℝ) / m) = rhoV * ((e.totient : ℝ) / e) := by
      rw [hm, hrhoV]; push_cast; exact phi_mul_div hVe
    have hbte_eq : bte = be * ((e.totient : ℝ) / e) := by
      rw [hbte, hbe, show S.bTilde e = S.bDefect e * (e.totient : ℝ) / e from rfl, mul_div_assoc]
    have hfrac_e_nn : (0 : ℝ) ≤ (e.totient : ℝ) / e :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hbe_phi : be * ((m.totient : ℝ) / m) = rhoV * bte := by
      rw [hphi, hbte_eq]; ring
    have habs_be_phi : |be| * ((m.totient : ℝ) / m) = rhoV * |bte| := by
      rw [hphi, hbte_eq, abs_mul, abs_of_nonneg hfrac_e_nn]; ring
    have htaum : (#m.divisors : ℝ) = tauV * taue := by
      rw [hm, htauV, htaue]; exact tau_mul hVe
    have hlm : ellV m = lV + ellV e := by
      rw [hm, hlV]; exact ellV_mul hVe
    have hle_nn : 0 ≤ ellV e := ellV_nonneg e
    have hle_le : ellV e ≤ Real.log e := ellV_le_log hepos
    set x : ℝ := z / e with hx
    set P : ℝ := partialSumALt m x with hP
    have hsqrtx : √x = √z / √e := by
      rw [hx]; exact Real.sqrt_div hzpos.le e
    set r : ℝ := √e / √z with hr
    have hr_nn : 0 ≤ r := by
      rw [hr]; exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hE_ge : |be| * r * L2Vz ≤ E := by
      have htt : (1 : ℝ) ≤ tauV * taue :=
        htauV_ge.trans (le_mul_of_one_le_right (by linarith only [htauV_ge]) htaue_ge)
      have hb2 : 0 ≤ |be| * r * L2Vz := mul_nonneg (mul_nonneg hbe_nn hr_nn) hL2Vz_nn
      have h1 : E = (tauV * taue) * (|be| * r * L2Vz) := by rw [hE, hr]; field_simp
      rw [h1]
      exact le_mul_of_one_le_left hb2 htt
    have hrb_le : rhoV * |bte| ≤ |be| := (mul_le_of_le_one_left hbt_nn hrhoV_le).trans hbt_le
    rcases lt_or_ge x 1 with hxlt1 | hxge1
    · rw [hP.trans (partialSumALt_eq_zero_of_lt_one m x hxlt1)]
      have hzlt : z < e := by rw [hx, div_lt_one heR0] at hxlt1; exact hxlt1
      have hr_ge1 : 1 ≤ r := by
        rw [hr, le_div_iff₀ hsqrtz_pos, one_mul]
        exact Real.sqrt_le_sqrt (by linarith)
      rw [show |be * 0 - bte * rhoV * Real.log z| = rhoV * |bte| * Real.log z by
        rw [mul_zero, zero_sub, abs_neg, abs_mul, abs_mul, abs_of_nonneg hrhoV_nn,
          abs_of_nonneg hlogz_nn]; ring]
      have step1 : rhoV * |bte| * Real.log z ≤ |be| * Real.log z :=
        mul_le_mul_of_nonneg_right hrb_le hlogz_nn
      have step2 : |be| * Real.log z ≤ |be| * L2Vz := mul_le_mul_of_nonneg_left hlogz_le hbe_nn
      have step3 : |be| * L2Vz ≤ |be| * r * L2Vz := by
        nlinarith only [mul_nonneg hbe_nn hL2Vz_nn, hr_ge1]
      have hcE : E ≤ (1 + CA / 2) * D + (2 * √2 + CA + Cb) * E := by
        nlinarith only [mul_nonneg hCA.le hD_nn, mul_nonneg hCA.le hE_nn, mul_nonneg hCb.le hE_nn,
          mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * √2 - 1) hE_nn, hD_nn]
      linarith only [step1, step2, step3, hE_ge, hcE]
    · have hxge1' : (1 : ℝ) ≤ x := hxge1
      rcases lt_or_ge x 2 with hxlt2 | hxge2
      · have hP_nn : 0 ≤ P := by rw [hP]; exact partialSumALt_nonneg m x
        have hP_le : P ≤ 1 := by rw [hP]; exact partialSumALt_le_one_of_lt_two m x hxlt2
        have hzlt2 : z < 2 * e := by
          rw [hx] at hxlt2; rw [div_lt_iff₀ heR0] at hxlt2; linarith only [hxlt2]
        have hr_ge : 1 ≤ √2 * r := by
          rw [hr, ← mul_div_assoc, le_div_iff₀ hsqrtz_pos, one_mul]
          have hz2e : √z ≤ √(2 * e) := Real.sqrt_le_sqrt (by linarith)
          calc √z ≤ √(2 * e) := hz2e
            _ = √2 * √e := by rw [Real.sqrt_mul (by norm_num)]
        have hLHS_le :
            |be * P - bte * rhoV * Real.log z| ≤ |be| * 1 + rhoV * |bte| * Real.log z := by
          have h1 : |be * P - bte * rhoV * Real.log z| ≤ |be * P| + |bte * rhoV * Real.log z| :=
            abs_sub _ _
          rw [abs_mul, abs_of_nonneg hP_nn, abs_mul, abs_mul, abs_of_nonneg hrhoV_nn,
            abs_of_nonneg hlogz_nn] at h1
          linarith only [h1, mul_le_mul_of_nonneg_left hP_le hbe_nn]
        have hb1 : |be| * 1 ≤ |be| * L2Vz := mul_le_mul_of_nonneg_left hL2Vz_ge hbe_nn
        have hb2 : rhoV * |bte| * Real.log z ≤ |be| * L2Vz :=
          calc rhoV * |bte| * Real.log z ≤ |be| * Real.log z :=
                mul_le_mul_of_nonneg_right hrb_le hlogz_nn
            _ ≤ |be| * L2Vz := mul_le_mul_of_nonneg_left hlogz_le hbe_nn
        have hsum : |be * P - bte * rhoV * Real.log z| ≤ 2 * (|be| * L2Vz) := by linarith
        have hkey : 2 * (|be| * L2Vz) ≤ 2 * √2 * (|be| * r * L2Vz) := by
          nlinarith only [mul_nonneg hbe_nn hL2Vz_nn, hr_ge]
        have hfin : 2 * √2 * (|be| * r * L2Vz) ≤ (2 * √2 + CA + Cb) * E := by
          have h2s : (0 : ℝ) ≤ 2 * √2 := by linarith
          linarith only [mul_le_mul_of_nonneg_left hE_ge h2s, mul_nonneg hCA.le hE_nn,
            mul_nonneg hCb.le hE_nn]
        have hDpart : 0 ≤ (1 + CA / 2) * D := mul_nonneg (by linarith) hD_nn
        linarith only [hsum, hkey, hfin, hDpart]
      · set PA : ℝ := PrimeGaps.MaynardOffDiagonal.sumA m x with hPA
        have hCbterm : |P - PA| ≤ Cb / √x := by
          rw [hP, hPA]; exact hCbbd m x hxge1'
        set fm : ℝ := (m.totient : ℝ) / m with hfm
        set lm : ℝ := ellV m with hlmset
        set L2mx : ℝ := Real.log (2 * m * x) with hL2mx
        have hCAterm :
            |PA - fm * (Real.log x + lm)| ≤
              CA * (fm + (#m.divisors : ℝ) * L2mx / √x) := by
          rw [hPA, hfm, hlmset, hL2mx]; exact hCAmain m hm1 hm_sf x hxge2
        have hlogx : Real.log x = Real.log z - Real.log e := by
          rw [hx, Real.log_div hzpos.ne' heR0.ne']
        have hlm_val : lm = lV + ellV e := by rw [hlmset]; exact hlm
        have hthird : be * fm * (Real.log x + lm) - bte * rhoV * Real.log z =
            rhoV * bte * (lV + ellV e - Real.log e) := by
          have hbf : be * fm = rhoV * bte := by rw [hfm]; exact hbe_phi
          rw [hlm_val, hlogx]
          linear_combination (Real.log z - Real.log e + (lV + ellV e)) * hbf
        have hdecomp : be * P - bte * rhoV * Real.log z =
            be * (P - PA) + be * (PA - fm * (Real.log x + lm)) +
              rhoV * bte * (lV + ellV e - Real.log e) := by
          rw [← hthird]; ring
        rw [hdecomp]
        have h1abs : |be * (P - PA)| ≤ |be| * (Cb / √x) := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hCbterm hbe_nn
        have h2abs :
            |be * (PA - fm * (Real.log x + lm))| ≤
              |be| * (CA * (fm + (#m.divisors : ℝ) * L2mx / √x)) := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hCAterm hbe_nn
        have hinvsqrtx : Cb / √x = Cb * r := by
          rw [hsqrtx, hr]; field_simp
        have h2mx : (2 : ℝ) * m * x = 2 * S.V * z := by
          rw [hx, hm]; push_cast; field_simp
        have hL2mx_eq : L2mx = L2Vz := by rw [hL2mx, hL2Vz, h2mx]
        have hτm : (#m.divisors : ℝ) = tauV * taue := htaum
        have h2rw : |be| * (CA * (fm + (#m.divisors : ℝ) * L2mx / √x)) =
            CA * (|be| * fm) + CA * (|be| * ((#m.divisors : ℝ) * L2mx / √x)) := by ring
        have hbe_fm : |be| * fm = rhoV * |bte| := by rw [hfm]; exact habs_be_phi
        have hbe_second : |be| * ((#m.divisors : ℝ) * L2mx / √x) = E := by
          rw [hτm, hL2mx_eq, hsqrtx, hE]; field_simp
        have hT3 : |rhoV * bte * (lV + ellV e - Real.log e)| ≤ D := by
          have hfac : |lV + ellV e - Real.log e| ≤ 2 * (1 + lV) * (1 + Real.log e) := by
            rw [abs_le]
            constructor <;>
              linarith only [mul_nonneg hlV_nn hloge_nn, hlV_nn, hle_nn, hle_le, hloge_nn]
          rw [abs_mul, abs_mul, abs_of_nonneg hrhoV_nn, hD]
          linarith only [mul_le_mul_of_nonneg_left hfac (mul_nonneg hrhoV_nn hbt_nn)]
        have htri :
            |be * (P - PA) + be * (PA - fm * (Real.log x + lm)) +
              rhoV * bte * (lV + ellV e - Real.log e)| ≤
            |be * (P - PA)| + |be * (PA - fm * (Real.log x + lm))| +
              |rhoV * bte * (lV + ellV e - Real.log e)| :=
          abs_add_three _ _ _
        have h2abs' : |be * (PA - fm * (Real.log x + lm))| ≤ CA * (rhoV * |bte|) + CA * E :=
          calc |be * (PA - fm * (Real.log x + lm))|
              ≤ |be| * (CA * (fm + (#m.divisors : ℝ) * L2mx / √x)) := h2abs
            _ = CA * (|be| * fm) +
                  CA * (|be| * ((#m.divisors : ℝ) * L2mx / √x)) := h2rw
            _ = CA * (rhoV * |bte|) + CA * E := by rw [hbe_fm, hbe_second]
        have h1abs' : |be * (P - PA)| ≤ Cb * (|be| * r) :=
          calc |be * (P - PA)| ≤ |be| * (Cb / √x) := h1abs
            _ = |be| * (Cb * r) := by rw [hinvsqrtx]
            _ = Cb * (|be| * r) := by ring
        have hber_le_E : |be| * r ≤ E :=
          (le_mul_of_one_le_right (mul_nonneg hbe_nn hr_nn) hL2Vz_ge).trans hE_ge
        have hrbte_D : rhoV * |bte| ≤ D / 2 := by
          rw [hD]
          nlinarith only [mul_nonneg (mul_nonneg hrhoV_nn hbt_nn) hlV_nn,
            mul_nonneg (mul_nonneg hrhoV_nn hbt_nn) hloge_nn,
            mul_nonneg (mul_nonneg (mul_nonneg hrhoV_nn hbt_nn) hlV_nn) hloge_nn]
        have hCbE : Cb * (|be| * r) ≤ Cb * E := mul_le_mul_of_nonneg_left hber_le_E hCb.le
        have hCArb : CA * (rhoV * |bte|) ≤ CA * (D / 2) := mul_le_mul_of_nonneg_left hrbte_D hCA.le
        have hfinal :
            |be * (P - PA)| + |be * (PA - fm * (Real.log x + lm))| +
              |rhoV * bte * (lV + ellV e - Real.log e)| ≤
            (1 + CA / 2) * D + (2 * √2 + CA + Cb) * E :=
          by linarith only [h1abs'.trans hCbE, h2abs', hCArb, hT3,
            mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg 2)) hE_nn]
        exact le_trans htri hfinal

/-- (c) Final quantitative assembly, stitching together the named estimates above. -/
@[pg_tag "bg246" "slem_H_asymptotic"]
theorem slem_H_error_assembly : ∃ C₁ C₂ : ℝ → ℝ → ℝ,
      (∀ A₁ A₃ : ℝ, 0 < C₁ A₁ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 < C₂ A₁ A₃) ∧
      ∀ (S : SieveDatum) (z : ℝ), 2 ≤ z →
        |S.H z - PrimeGaps.singularSeries S.γ * Real.log z| ≤
          C₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
            C₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) *
                z ^ (-(1 : ℝ) / 8) * Real.log (2 * S.V * z) := by
  obtain ⟨CA, hCApos, hCAmain⟩ := exists_abs_sumA_sub_le
  obtain ⟨Cb, hCbpos, hCbbd⟩ := boundary_sqrt
  obtain ⟨Klog, hKlogpos, hKlog⟩ := bTilde_log_tsum_uniform
  obtain ⟨Kdef, hKdefpos, hKdef⟩ := bDefect_tau_sqrt_tsum_uniform
  obtain ⟨frho, hfrhopos, hfrho⟩ := singularSeries_rhoV_uniform_lower
  refine ⟨fun A₁ A₃ ↦ 2 * (1 + CA / 2) * frho A₃ * Klog A₁ A₃,
          fun A₁ A₃ ↦ (2 * √2 + CA + Cb) * Kdef A₁ A₃, ?_, ?_, ?_⟩
  · intro A₁ A₃
    have h1 := hfrhopos A₃
    have h2 := hKlogpos A₁ A₃
    positivity
  · intro A₁ A₃
    have h1 := hKdefpos A₁ A₃
    have h2 : (0 : ℝ) < 2 * √2 + CA + Cb := by
      have := Real.sqrt_nonneg 2; linarith
    positivity
  · intro S z hz
    simp only []
    set rhoV : ℝ := (S.V.totient : ℝ) / S.V with hrhoV
    set lV : ℝ := ellV S.V with hlV
    set tauV : ℝ := (#S.V.divisors : ℝ) with htauV
    set L2Vz : ℝ := Real.log (2 * S.V * z) with hL2Vz
    set singular : ℝ := PrimeGaps.singularSeries S.γ with hSS
    set f : ℕ → ℝ := fun e ↦ S.bDefect e * partialSumALt (S.V * e) (z / e) with hf
    set g : ℕ → ℝ := fun e ↦ S.bTilde e * (rhoV * Real.log z) with hg
    set Dw : ℕ → ℝ := fun e ↦ |S.bTilde e| * (1 + Real.log e) with hDw
    set Ew : ℕ → ℝ := fun e ↦ |S.bDefect e| * (#e.divisors : ℝ) * √e with hEw
    set Rd : ℕ → ℝ := fun e ↦ (1 + CA / 2) * (2 * rhoV * (1 + lV) * Dw e) with hRd
    set Re : ℕ → ℝ := fun e ↦
      (2 * √2 + CA + Cb) * (tauV * L2Vz / √z * Ew e) with hRe
    set remainder : ℕ → ℝ := fun e ↦ Rd e + Re e with hR
    have hzpos : (0 : ℝ) < z := by linarith
    have hz1 : (1 : ℝ) ≤ z := by linarith
    have hEw_sum : Summable Ew := bDefect_tau_sqrt_summable S
    have hDw_nonneg : ∀ e, 0 ≤ Dw e := fun e ↦ by
      rw [hDw]
      exact mul_nonneg (abs_nonneg _) (by linarith [Real.log_natCast_nonneg e])
    have hEw_nonneg : ∀ e, 0 ≤ Ew e := fun e ↦ by rw [hEw]; positivity
    have hDw_le_3Ew : ∀ e, Dw e ≤ 3 * Ew e := fun e ↦ by
      rw [hDw, hEw]; exact abs_bTilde_mul_log_le S e
    have hDw_sum : Summable Dw :=
      Summable.of_nonneg_of_le hDw_nonneg hDw_le_3Ew (hEw_sum.mul_left 3)
    have hf_sum : Summable f :=
      summable_of_ne_finset_zero (s := Finset.range ⌈z⌉₊) fun e he ↦ by
        simp only [Finset.mem_range, not_lt] at he
        rw [hf]
        change S.bDefect e * partialSumALt (S.V * e) (z / e) = 0
        rw [partialSumALt_div_eq_zero_of_ceil_le _ e z he, mul_zero]
    have hbt_sum : Summable (fun e ↦ S.bTilde e) := (bTilde_norm_summable S).of_norm
    have hg_sum : Summable g := by simpa only [hg] using hbt_sum.mul_right (rhoV * Real.log z)
    have hT_le : ∀ e, |f e - g e| ≤ remainder e := fun e ↦ by
      have hb := termwise_bound S z hz CA hCApos hCAmain Cb hCbpos hCbbd e
      have heq : f e - g e = S.bDefect e * partialSumALt (S.V * e) (z / e) -
              S.bTilde e * ((S.V.totient : ℝ) / S.V) * Real.log z := by
        rw [hf, hg, hrhoV]; ring
      rw [heq, hR, hRd, hRe, hDw, hEw]
      simpa only [hrhoV, hlV, htauV, hL2Vz] using hb
    have hRd_sum : Summable Rd :=
      (hDw_sum.mul_left ((1 + CA / 2) * (2 * rhoV * (1 + lV)))).congr fun e ↦ by rw [hRd]; ring
    have hRe_sum : Summable Re :=
      (hEw_sum.mul_left ((2 * √2 + CA + Cb) * (tauV * L2Vz / √z))).congr
        fun e ↦ by rw [hRe]; ring
    have hR_sum : Summable remainder := hRd_sum.add hRe_sum
    have hT_sum : Summable (fun e ↦ f e - g e) :=
      Summable.of_norm_bounded hR_sum fun e ↦ by rw [Real.norm_eq_abs]; exact hT_le e
    have hTabs_sum : Summable (fun e ↦ |f e - g e|) := hT_sum.abs
    have hHconv : S.H z = ∑' e, f e := by rw [hf]; exact slem_H_convolution_form S z
    have hbridge : singular = rhoV * ∑' e, S.bTilde e := by
      rw [hSS, hrhoV]; exact slem_singularSeries_bTilde_bridge S
    have hglink : singular * Real.log z = ∑' e, g e := by
      rw [hbridge, hg, tsum_mul_right]; ring
    have hstep1 : S.H z - singular * Real.log z = ∑' e, (f e - g e) := by
      rw [hHconv, hglink, Summable.tsum_sub hf_sum hg_sum]
    have hstep2 : |S.H z - singular * Real.log z| ≤ ∑' e, |f e - g e| := by
      rw [hstep1]
      calc |∑' e, (f e - g e)| = ‖∑' e, (f e - g e)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' e, ‖f e - g e‖ := norm_tsum_le_tsum_norm hTabs_sum
        _ = ∑' e, |f e - g e| := by simp only [Real.norm_eq_abs]
    have hstep3 : ∑' e, |f e - g e| ≤ ∑' e, remainder e :=
      Summable.tsum_le_tsum hT_le hTabs_sum hR_sum
    have hsumR : ∑' e, remainder e = (1 + CA / 2) * (2 * rhoV * (1 + lV)) * (∑' e, Dw e) +
          (2 * √2 + CA + Cb) * (tauV * L2Vz / √z) * (∑' e, Ew e) := by
      rw [hR, Summable.tsum_add hRd_sum hRe_sum]
      congr 1
      · have : ∑' e, Rd e = ∑' e, ((1 + CA / 2) * (2 * rhoV * (1 + lV))) * Dw e := by
          congr 1; funext e; rw [hRd]; ring
        rw [this, tsum_mul_left]
      · have : ∑' e, Re e =
            ∑' e, ((2 * √2 + CA + Cb) * (tauV * L2Vz / √z)) * Ew e := by
          congr 1; funext e; rw [hRe]; ring
        rw [this, tsum_mul_left]
    have hDwsum_le : ∑' e, Dw e ≤ Klog S.A₁ S.A₃ := by rw [hDw]; exact hKlog S
    have hEwsum_le : ∑' e, Ew e ≤ Kdef S.A₁ S.A₃ := by rw [hEw]; exact hKdef S
    have hSS_nonneg : 0 ≤ singular := by rw [hSS]; exact (singularSeries_pos S).le
    have hrhoV_nn : 0 ≤ rhoV := by rw [hrhoV]; positivity
    have hlV_nn : 0 ≤ lV := by rw [hlV]; exact ellV_nonneg S.V
    have hKlog_nn : 0 ≤ Klog S.A₁ S.A₃ := (hKlogpos S.A₁ S.A₃).le
    have hKdef_nn : 0 ≤ Kdef S.A₁ S.A₃ := (hKdefpos S.A₁ S.A₃).le
    have hCA_half_nn : 0 ≤ 1 + CA / 2 := by linarith [hCApos]
    have hDwsum_nn : 0 ≤ ∑' e, Dw e := tsum_nonneg hDw_nonneg
    have hEwsum_nn : 0 ≤ ∑' e, Ew e := tsum_nonneg hEw_nonneg
    have hrhoV_le : rhoV ≤ frho S.A₃ * singular := by rw [hrhoV, hSS]; exact hfrho S
    have hterm1 : (1 + CA / 2) * (2 * rhoV * (1 + lV)) * (∑' e, Dw e) ≤
        2 * (1 + CA / 2) * frho S.A₃ * Klog S.A₁ S.A₃ * singular * (1 + lV) := by
      have hcoef_nn : 0 ≤ (1 + CA / 2) * (2 * rhoV * (1 + lV)) :=
        mul_nonneg hCA_half_nn (mul_nonneg (by linarith) (by linarith))
      have hcoef2_nn : 0 ≤ 2 * (1 + CA / 2) * (1 + lV) * Klog S.A₁ S.A₃ :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) hKlog_nn
      linarith only [mul_le_mul_of_nonneg_left hDwsum_le hcoef_nn,
        mul_le_mul_of_nonneg_left hrhoV_le hcoef2_nn]
    have hc2_nn : 0 ≤ 2 * √2 + CA + Cb := by
      have := Real.sqrt_nonneg 2; linarith [hCApos, hCbpos]
    have htauV_pos : (0 : ℝ) < tauV := by
      rw [htauV]
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr S.V_pos.ne'⟩
    have hL2Vz_pos : (0 : ℝ) < L2Vz := by
      rw [hL2Vz]
      refine Real.log_pos ?_
      have hVR : (1 : ℝ) ≤ (S.V : ℝ) := by exact_mod_cast S.V_pos
      linarith only [mul_nonneg (sub_nonneg.mpr hVR) (sub_nonneg.mpr hz), hVR, hz]
    have hsqrtz_pos : (0 : ℝ) < √z := Real.sqrt_pos.mpr hzpos
    have hsqrtz_rpow : √z = z ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow z
    have hinv_le : 1 / √z ≤ z ^ (-(1 : ℝ) / 8) := by
      rw [hsqrtz_rpow, one_div, ← Real.rpow_neg hzpos.le]
      exact Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
    have hterm2 : (2 * √2 + CA + Cb) * (tauV * L2Vz / √z) * (∑' e, Ew e) ≤
        (2 * √2 + CA + Cb) * Kdef S.A₁ S.A₃ * tauV * z ^ (-(1 : ℝ) / 8) * L2Vz := by
      have hcoef_nn : 0 ≤ (2 * √2 + CA + Cb) * (tauV * L2Vz / √z) :=
        mul_nonneg hc2_nn (div_nonneg (mul_nonneg htauV_pos.le hL2Vz_pos.le) hsqrtz_pos.le)
      have hpre_nn : 0 ≤ (2 * √2 + CA + Cb) * Kdef S.A₁ S.A₃ * tauV * L2Vz :=
        mul_nonneg (mul_nonneg (mul_nonneg hc2_nn hKdef_nn) htauV_pos.le) hL2Vz_pos.le
      calc (2 * √2 + CA + Cb) * (tauV * L2Vz / √z) * (∑' e, Ew e)
          ≤ (2 * √2 + CA + Cb) * (tauV * L2Vz / √z) * Kdef S.A₁ S.A₃ :=
            mul_le_mul_of_nonneg_left hEwsum_le hcoef_nn
        _ = ((2 * √2 + CA + Cb) * Kdef S.A₁ S.A₃ * tauV * L2Vz) * (1 / √z) := by
            ring
        _ ≤ ((2 * √2 + CA + Cb) * Kdef S.A₁ S.A₃ * tauV * L2Vz) * z ^ (-(1 : ℝ) / 8) :=
            mul_le_mul_of_nonneg_left hinv_le hpre_nn
        _ = (2 * √2 + CA + Cb) * Kdef S.A₁ S.A₃ * tauV * z ^ (-(1 : ℝ) / 8) * L2Vz := by
            ring
    calc |S.H z - singular * Real.log z| ≤ ∑' e, |f e - g e| := hstep2
      _ ≤ ∑' e, remainder e := hstep3
      _ = (1 + CA / 2) * (2 * rhoV * (1 + lV)) * (∑' e, Dw e) +
            (2 * √2 + CA + Cb) * (tauV * L2Vz / √z) * (∑' e, Ew e) := hsumR
      _ ≤ 2 * (1 + CA / 2) * frho S.A₃ * Klog S.A₁ S.A₃ * singular * (1 + lV) +
            (2 * √2 + CA + Cb) * Kdef S.A₁ S.A₃ * tauV * z ^ (-(1 : ℝ) / 8) * L2Vz :=
          add_le_add hterm1 hterm2
      _ = (fun A₁ A₃ ↦ 2 * (1 + CA / 2) * frho A₃ * Klog A₁ A₃) S.A₁ S.A₃ * singular *
            (1 + ellV S.V) +
            (fun A₁ A₃ ↦ (2 * √2 + CA + Cb) * Kdef A₁ A₃) S.A₁ S.A₃ *
                (#S.V.divisors : ℝ) * z ^ (-(1 : ℝ) / 8) * Real.log (2 * S.V * z) := by
          simp only [hlV, htauV, hL2Vz]

end PrimeGaps
