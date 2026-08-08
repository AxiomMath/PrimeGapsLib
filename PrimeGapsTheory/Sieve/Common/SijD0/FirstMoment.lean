/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Pi.Interval
public import Mathlib.Topology.Separation.CompletelyRegular
public import PrimeGapsTheory.Arithmetic.Mertens.W
public import PrimeGapsTheory.Sieve.Common.SijD0.Basic
public import PrimeGapsTheory.Sieve.S1.SijDichotomy
public import PrimeGapsTheory.Sieve.Transforms.YmAjNeRj

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Bounding first-moment off-diagonal terms

Bounds the first-moment contribution from nontrivial off-diagonal variables.

## Main definitions

* `PrimeGaps.Uterm`, `PrimeGaps.S0term`, `PrimeGaps.Sijterm`, `PrimeGaps.DiagTerm`: the
  coordinatewise majorant weights for the `u`-coordinates, the bulk off-diagonal coordinates,
  the distinguished off-diagonal coordinate and the diagonal coordinates.
* `PrimeGaps.S0fin`, `PrimeGaps.Sijfin`: the finite coordinate sums of `S0term` and `Sijterm`.
* `PrimeGaps.matrixWeight`, `PrimeGaps.MatrixTerm`: the matrix-coordinate weight pinning a
  distinguished off-diagonal pair.

## Main results

* `PrimeGaps.lem_S1_sij_D0`: Bounds the union of nontrivial off-diagonal contributions.
-/

@[expose] public section

open Real

open scoped Finset
open scoped ArithmeticFunction.Moebius

open SijD0

namespace PrimeGaps

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- Under `HasPermissibleSupport`, every nonzero-coefficient index has all coordinates in
`[1, Rb]`.
-/
theorem lamsupp_bound {k : ℕ} (Rb : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) (d : Fin k → ℕ) (hd : lam d ≠ 0) (i : Fin k) :
    1 ≤ d i ∧ (d i : ℝ) ≤ Rb := by
  have h1 : ∀ j, 1 ≤ d j := fun j ↦ Nat.one_le_iff_ne_zero.mpr (hs.ne_zero_of_ne_zero hd j)
  refine ⟨h1 i, ?_⟩
  have hprod := hs.prod_lt_R_of_ne_zero hd
  have hfloorpos : 0 < ⌊Rb⌋₊ := lt_of_lt_of_le (Finset.prod_pos fun j _ ↦ h1 j) hprod
  have hnat : d i ≤ ⌊Rb⌋₊ :=
    (Finset.single_le_prod' (f := fun j ↦ d j) (fun j _ ↦ h1 j) (Finset.mem_univ i)).trans hprod
  exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le (Nat.pos_of_floor_pos hfloorpos).le)

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- `PrimeGaps.lToY lam r ≠ 0` forces each coordinate `r i ≤ Rb`. -/
theorem yWeight_supp {k : ℕ} (Rb : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) (r : Fin k → ℕ)
    (hr : PrimeGaps.lToY lam r ≠ 0) (i : Fin k) :
    (r i : ℝ) ≤ Rb :=
  (lamsupp_bound Rb W (PrimeGaps.lToY lam) hs.lToY r hr i).2

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- From `PrimeGaps.lToY lam (boldA u s) ≠ 0`: each `u j ≤ Rb`. -/
theorem u_bound {k : ℕ} (Rb : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hsij : ∀ i j, i ≠ j → 1 ≤ s i j)
    (hA : PrimeGaps.lToY lam (boldA u s) ≠ 0) (j : Fin k) :
    (u j : ℝ) ≤ Rb := by
  have hb := yWeight_supp Rb W lam hs (boldA u s) hA j
  unfold boldA at hb
  have hle : u j ≤ u j * ∏ i ∈ Finset.univ.erase j, s j i :=
    Nat.le_mul_of_pos_right _ <|
      Finset.one_le_prod' fun i hi ↦ hsij j i (Ne.symm (Finset.mem_erase.mp hi).1)
  exact le_trans (by exact_mod_cast hle) hb

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- From `PrimeGaps.lToY lam (boldA u s) ≠ 0`: each off-diagonal `s j i ≤ Rb` (for `i ≠ j`). -/
theorem s_bound {k : ℕ} (Rb : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hu : ∀ i, 1 ≤ u i) (hsij : ∀ i j, i ≠ j → 1 ≤ s i j)
    (hA : PrimeGaps.lToY lam (boldA u s) ≠ 0) (j i : Fin k) (hji : i ≠ j) :
    (s j i : ℝ) ≤ Rb := by
  have hb := yWeight_supp Rb W lam hs (boldA u s) hA j
  unfold boldA at hb
  have hle : s j i ≤ u j * ∏ m ∈ Finset.univ.erase j, s j m :=
    (Finset.single_le_prod' (f := fun m ↦ s j m)
      (fun m hm ↦ hsij j m (Ne.symm (Finset.mem_erase.mp hm).1))
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ i⟩)).trans (Nat.le_mul_of_pos_left _ (hu j))
  exact le_trans (by exact_mod_cast hle) hb

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- Coprimality part of the support of `lam`: every nonzero-coefficient index has each coordinate
coprime to `W`.
-/
theorem lamsupp_coprime {k : ℕ} (Rb : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) (d : Fin k → ℕ) (hd : lam d ≠ 0) (i : Fin k) :
    (d i).Coprime W :=
  (hs.coprime_prod_W_of_ne_zero hd).coprime_dvd_left
    (Finset.dvd_prod_of_mem d (Finset.mem_univ i))

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- `PrimeGaps.lToY lam r ≠ 0` yields a nonzero-coefficient index `d` with `r i ∣ d i` for
all `i`. -/
theorem yWeight_supp_dvd {k : ℕ} (lam : (Fin k → ℕ) →₀ ℝ)
    (r : Fin k → ℕ) (hr : PrimeGaps.lToY lam r ≠ 0) :
    ∃ d, lam d ≠ 0 ∧ ∀ i, r i ∣ d i := by
  rw [PrimeGaps.lToY_apply', mul_ne_zero_iff] at hr
  obtain ⟨d, hd, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr.2
  rw [ite_ne_right_iff] at hterm
  exact ⟨d, Finsupp.mem_support_iff.mp hd, fun i ↦ (hterm.1 i).1⟩

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- If `PrimeGaps.lToY lam (boldA u s) ≠ 0` then each `u j` is coprime to `W`. From
`yWeight_supp_dvd` get `d` with `(boldA u s) j ∣ d j` and `lam d ≠ 0`; since
`u j ∣ (boldA u s) j` (`boldA u s j = u j·∏ s j i`), we get `u j ∣ d j`, and
`lamsupp_coprime` gives `(d j).Coprime W`.
-/
theorem u_coprime {k : ℕ} (Rb : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ)
    (hA : PrimeGaps.lToY lam (boldA u s) ≠ 0) (j : Fin k) :
    (u j).Coprime W := by
  obtain ⟨d, hdne, hdvd⟩ := yWeight_supp_dvd lam (boldA u s) hA
  exact (lamsupp_coprime Rb W lam hs d hdne j).coprime_dvd_left
    (dvd_trans (by unfold boldA; exact Dvd.intro _ rfl) (hdvd j))

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- For a fixed pair `p`, the absolute value of the single-pair-guarded summand (as a function of
`(u,s)` jointly) is summable, because its support sits inside the finite box
`{(u,s) | ∀ i, u i ≤ ⌊Rb⌋₊ ∧ ∀ i j, s i j ≤ ⌊Rb⌋₊}`.
-/
theorem guarded_summable {k : ℕ} (N : ℕ) (Rb : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hs : lam.HasPermissibleSupport ⌊Rb⌋₊ W) (p : Fin k × Fin k) :
    Summable (fun us : (Fin k → ℕ) × (Fin k → Fin k → ℕ) ↦
      |(if ((∀ i, 1 ≤ us.1 i) ∧ (∀ i, us.2 i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ us.2 i j) ∧
            RestrictedCoprime us.1 us.2 ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < us.2 p.1 p.2) then
          (∏ i, (μ (us.1 i) : ℝ) ^ 2 / (Nat.totient (us.1 i) : ℝ)) *
          (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              (μ (us.2 q.1 q.2) : ℝ) /
                (Nat.totient (us.2 q.1 q.2) : ℝ) ^ 2) *
          PrimeGaps.lToY lam (boldA us.1 us.2) * PrimeGaps.lToY lam (boldB us.1 us.2)
        else 0)|) := by
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  apply Set.Finite.subset (s := {us : (Fin k → ℕ) × (Fin k → Fin k → ℕ) |
      (∀ i, us.1 i ∈ Finset.Iic ⌊Rb⌋₊) ∧ (∀ i j, us.2 i j ∈ Finset.Iic ⌊Rb⌋₊)})
  · have hfin1 : {u : Fin k → ℕ | ∀ i, u i ∈ Finset.Iic ⌊Rb⌋₊}.Finite :=
      (Set.finite_Icc (0 : Fin k → ℕ) fun _ ↦ ⌊Rb⌋₊).subset fun u hu ↦
        Set.mem_Icc.mpr ⟨fun i ↦ Nat.zero_le _, fun i ↦ Finset.mem_Iic.mp (hu i)⟩
    have hfin2 : {s : Fin k → Fin k → ℕ | ∀ i j, s i j ∈ Finset.Iic ⌊Rb⌋₊}.Finite :=
      (Set.finite_Icc (0 : Fin k → Fin k → ℕ) fun _ _ ↦ ⌊Rb⌋₊).subset fun s hs' ↦
        Set.mem_Icc.mpr ⟨fun i j ↦ Nat.zero_le _, fun i j ↦ Finset.mem_Iic.mp (hs' i j)⟩
    exact (hfin1.prod hfin2).subset fun us hus ↦ hus
  · intro us hus
    simp only [Set.mem_ofPred_eq, Function.mem_support] at hus ⊢
    have hval : (if ((∀ i, 1 ≤ us.1 i) ∧ (∀ i, us.2 i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ us.2 i j) ∧
            RestrictedCoprime us.1 us.2 ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < us.2 p.1 p.2) then
          (∏ i, (μ (us.1 i) : ℝ) ^ 2 / (Nat.totient (us.1 i) : ℝ)) *
          (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              (μ (us.2 q.1 q.2) : ℝ) /
                (Nat.totient (us.2 q.1 q.2) : ℝ) ^ 2) *
          PrimeGaps.lToY lam (boldA us.1 us.2) * PrimeGaps.lToY lam (boldB us.1 us.2)
        else 0) ≠ 0 := fun h ↦ hus (by rw [h, abs_zero])
    by_cases hg : (∀ i, 1 ≤ us.1 i) ∧ (∀ i, us.2 i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ us.2 i j) ∧
            RestrictedCoprime us.1 us.2 ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < us.2 p.1 p.2
    · rw [if_pos hg] at hval
      obtain ⟨hu, hdiag, hsij, _, _⟩ := hg
      have hA : PrimeGaps.lToY lam (boldA us.1 us.2) ≠ 0 := fun h ↦ hval (by rw [h]; ring)
      refine ⟨fun i ↦ Finset.mem_Iic.mpr <|
          Nat.le_floor (u_bound Rb W lam hs us.1 us.2 hsij hA i),
        fun i j ↦ Finset.mem_Iic.mpr ?_⟩
      by_cases hij : i = j
      · subst hij
        rw [hdiag i]
        have h1u : (1 : ℝ) ≤ (us.1 i : ℝ) := by exact_mod_cast hu i
        exact Nat.le_floor (by
          exact_mod_cast h1u.trans (u_bound Rb W lam hs us.1 us.2 hsij hA i))
      · exact Nat.le_floor (s_bound Rb W lam hs us.1 us.2 hu hsij hA i j (Ne.symm hij))
    · exact absurd (if_neg hg) hval

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- On the base guard (`u i ≥ 1`, off-diagonal `s i j ≥ 1`), the absolute value of the summand
`σ = P_u · P_s · PrimeGaps.lToY(boldA)·PrimeGaps.lToY(boldB)` is bounded by
`Finsupp.maxRealAbs (PrimeGaps.lToY lam) ² · P_u · |P_s|`.
-/
theorem sigma_abs_le {k : ℕ} (lam : (Fin k → ℕ) →₀ ℝ) (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) :
    |(∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
        (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s q.1 q.2) : ℝ) / (Nat.totient (s q.1 q.2) : ℝ) ^ 2) *
        PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)| ≤
          Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 *
        (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
        |∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s q.1 q.2) : ℝ) / (Nat.totient (s q.1 q.2) : ℝ) ^ 2| := by
  have hyA : |PrimeGaps.lToY lam (boldA u s)| ≤ Finsupp.maxRealAbs (PrimeGaps.lToY lam) :=
    Finsupp.le_maxRealAbs
  have hyB : |PrimeGaps.lToY lam (boldB u s)| ≤ Finsupp.maxRealAbs (PrimeGaps.lToY lam) :=
    Finsupp.le_maxRealAbs
  have hyMax0 : 0 ≤ Finsupp.maxRealAbs (PrimeGaps.lToY lam) := (abs_nonneg _).trans hyA
  have hPunn : 0 ≤ ∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ) :=
    Finset.prod_nonneg fun i _ ↦ by positivity
  set Pu := (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) with hPu
  set Ps := (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            (μ (s q.1 q.2) : ℝ) /
              (Nat.totient (s q.1 q.2) : ℝ) ^ 2) with hPs
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hPunn]
  calc Pu * |Ps| * |PrimeGaps.lToY lam (boldA u s)| * |PrimeGaps.lToY lam (boldB u s)|
      ≤ Pu * |Ps| * Finsupp.maxRealAbs (PrimeGaps.lToY lam) *
        Finsupp.maxRealAbs (PrimeGaps.lToY lam) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hyA (by positivity)) hyB (abs_nonneg _)
          (by positivity)
    _ = Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 * Pu * |Ps| := by ring

/-- Finite off-diagonal coordinate sum over `[1, ⌊R⌋₊]`. -/
noncomputable def S0fin (R : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊R⌋₊,
    |(μ n : ℝ) / (Nat.totient n : ℝ) ^ 2|

open scoped Classical in
/-- Finite distinguished-coordinate tail sum: `n > ⌊D₀⌋₊`, all prime factors `> ⌊D₀⌋₊`. -/
noncomputable def Sijfin (N : ℕ) (R : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊R⌋₊ with
      (⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < n ∧ ∀ q, Nat.Prime q → q ∣ n → ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < q),
    |(μ n : ℝ) / (Nat.totient n : ℝ) ^ 2|

/-- `u` -coordinate term: `μ(n)²/φ(n)` on `[1,⌊R⌋₊]` coprime to `W`, else `0`. Its ℕ-tsum is
`PrimeGaps.MaynardOffDiagonal.sumA W R`.
-/
noncomputable def Uterm (W : ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  if (1 ≤ n ∧ n ≤ ⌊R⌋₊ ∧ n.Coprime W) then
    (μ n : ℝ) ^ 2 / (Nat.totient n : ℝ) else 0

/-- off-diagonal coordinate term: `|μ(n)/φ(n)²|` on `[1,⌊R⌋₊]`, else `0`. ℕ-tsum is `S0fin R`. -/
noncomputable def S0term (R : ℝ) (n : ℕ) : ℝ :=
  if (1 ≤ n ∧ n ≤ ⌊R⌋₊) then
    |(μ n : ℝ) / (Nat.totient n : ℝ) ^ 2| else 0

open scoped Classical in
/-- distinguished coordinate term: `|μ(n)/φ(n)²|` on the tail box, else `0`. ℕ-tsum is
`Sijfin N R`.
-/
noncomputable def Sijterm (N : ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  if (1 ≤ n ∧ n ≤ ⌊R⌋₊ ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < n ∧
        ∀ q, Nat.Prime q → q ∣ n → ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < q) then
    |(μ n : ℝ) / (Nat.totient n : ℝ) ^ 2| else 0

/-- diagonal coordinate term: Kronecker delta forcing `s a a = 1`. Its ℕ-tsum is `1`. Needed so the
coordinatewise majorant actually depends on (and is summable over) the diagonal coordinates
`s a a`.
-/
noncomputable def DiagTerm (n : ℕ) : ℝ := if n = 1 then (1 : ℝ) else 0

/-- The matrix-coordinate weight shared by the two moments: on the distinguished off-diagonal slot
`(i, j)` it is the tail weight `tail`, on the remaining off-diagonal slots the bulk weight `bulk`,
and on the diagonal the unit indicator `DiagTerm`. -/
noncomputable def matrixWeight {k : ℕ} (i j : Fin k) (tail bulk : ℕ → ℝ) :
    (Fin k × Fin k) → ℕ → ℝ := fun p n ↦
  if p = (i, j) then tail n
  else if p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)) then bulk n
  else DiagTerm n

/-- Distinguished-pair-pinned matrix coordinate weight over `Fin k × Fin k`: on the distinguished
pair `(i,j)` it is `Sijterm`; on the remaining off-diagonal slots it is `S0term`; on the diagonal
(and any slot outside `offDiag` ) it is `DiagTerm`.
-/
noncomputable def MatrixTerm {k : ℕ} (N : ℕ) (R : ℝ) (i j : Fin k) :
    (Fin k × Fin k) → ℕ → ℝ := matrixWeight i j (Sijterm N R) (S0term R)

/-- `Uterm` has ℕ-tsum equal to `PrimeGaps.MaynardOffDiagonal.sumA`. -/
theorem tsum_Uterm (W : ℕ) (R : ℝ) :
    ∑' n : ℕ, Uterm W R n = PrimeGaps.MaynardOffDiagonal.sumA W R := by
  classical
  rw [PrimeGaps.sumA_eq_mobiusTotientSum, tsum_eq_sum (s := Finset.Icc 1 ⌊R⌋₊)]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [Finset.mem_Icc] at hn
    unfold Uterm
    by_cases hcop : n.Coprime W
    · rw [if_pos ⟨hn.1, hn.2, hcop⟩, if_pos hcop]
    · rw [if_neg (fun h ↦ hcop h.2.2), if_neg hcop]
  · intro n hn
    unfold Uterm
    exact if_neg fun hcond ↦ hn (Finset.mem_Icc.mpr ⟨hcond.1, hcond.2.1⟩)

/-- `S0term` has ℕ-tsum equal to `S0fin`. -/
theorem tsum_S0term (R : ℝ) : ∑' n : ℕ, S0term R n = S0fin R := by
  classical
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊R⌋₊)]
  · unfold S0fin
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [Finset.mem_Icc] at hn
    unfold S0term
    rw [if_pos ⟨hn.1, hn.2⟩]
  · intro n hn
    unfold S0term
    exact if_neg fun hcond ↦ hn (Finset.mem_Icc.mpr ⟨hcond.1, hcond.2⟩)

/-- `Sijterm` has ℕ-tsum equal to `Sijfin`. -/
theorem tsum_Sijterm (N : ℕ) (R : ℝ) : ∑' n : ℕ, Sijterm N R n = Sijfin N R := by
  classical
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊R⌋₊)]
  · unfold Sijfin
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [Finset.mem_Icc] at hn
    unfold Sijterm
    by_cases htail : ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < n ∧
        ∀ q, Nat.Prime q → q ∣ n → ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < q
    · rw [if_pos ⟨hn.1, hn.2, htail.1, htail.2⟩, if_pos htail]
    · rw [if_neg (fun hc ↦ htail ⟨hc.2.2.1, hc.2.2.2⟩), if_neg htail]
  · intro n hn
    unfold Sijterm
    exact if_neg fun hcond ↦ hn (Finset.mem_Icc.mpr ⟨hcond.1, hcond.2.1⟩)

/-- `DiagTerm` is summable, being supported on `{1}`. -/
theorem summable_DiagTerm : Summable DiagTerm :=
  summable_of_support_le (M := 1) fun n hn ↦ by
    unfold DiagTerm at hn
    by_cases hne : n = 1
    · exact hne.le
    · exact absurd (if_neg hne) hn

/-- `S0term R` is summable, being supported on `[0, ⌊R⌋₊]`. -/
theorem summable_S0term (R : ℝ) : Summable (S0term R) :=
  summable_of_support_le (M := ⌊R⌋₊) fun n hn ↦ by
    unfold S0term at hn
    by_cases hc : 1 ≤ n ∧ n ≤ ⌊R⌋₊
    · exact hc.2
    · exact absurd (if_neg hc) hn

open scoped Classical in
/-- `Sijterm N R` is summable, being supported on `[0, ⌊R⌋₊]`. -/
theorem summable_Sijterm (N : ℕ) (R : ℝ) : Summable (Sijterm N R) :=
  summable_of_support_le (M := ⌊R⌋₊) fun n hn ↦ by
    unfold Sijterm at hn
    by_cases hc : 1 ≤ n ∧ n ≤ ⌊R⌋₊ ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < n ∧
        ∀ q, Nat.Prime q → q ∣ n → ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < q
    · exact hc.2.1
    · exact absurd (if_neg hc) hn

/-- `Uterm W R` is supported on `[0, ⌊R⌋₊]`. -/
theorem Uterm_support (W : ℕ) (R : ℝ) (n : ℕ) (hn : Uterm W R n ≠ 0) : n ≤ ⌊R⌋₊ := by
  unfold Uterm at hn
  by_cases hc : 1 ≤ n ∧ n ≤ ⌊R⌋₊ ∧ n.Coprime W
  · exact hc.2.1
  · exact absurd (if_neg hc) hn

/-- `Uterm W R` is summable, being supported on `[0, ⌊R⌋₊]`. -/
theorem summable_Uterm (W : ℕ) (R : ℝ) : Summable (Uterm W R) :=
  summable_of_support_le (Uterm_support W R)

/-- `matrixWeight` is nonnegative when both coordinate weights are. -/
theorem matrixWeight_nonneg {k : ℕ} (i j : Fin k) {tail bulk : ℕ → ℝ}
    (htail : ∀ n, 0 ≤ tail n) (hbulk : ∀ n, 0 ≤ bulk n) (p : Fin k × Fin k) (n : ℕ) :
    0 ≤ matrixWeight i j tail bulk p n := by
  unfold matrixWeight DiagTerm
  split_ifs <;> simp [htail, hbulk]

/-- `matrixWeight` is summable in each of its three cases. -/
theorem matrixWeight_summable {k : ℕ} (i j : Fin k) {tail bulk : ℕ → ℝ}
    (htail : Summable tail) (hbulk : Summable bulk) (p : Fin k × Fin k) :
    Summable (matrixWeight i j tail bulk p) := by
  classical
  unfold matrixWeight
  split_ifs
  · exact htail
  · exact hbulk
  · exact summable_DiagTerm

/-- On the diagonal guard `s a a = 1` the full `matrixWeight` product over `Fin k × Fin k`
collapses to the distinguished-pair term times the remaining off-diagonal terms. -/
theorem prod_matrixWeight_of_diag {k : ℕ} (i j : Fin k) (hij : i ≠ j) (tail bulk : ℕ → ℝ)
    (s : Fin k → Fin k → ℕ) (hdiag : ∀ a, s a a = 1) :
    (∏ p : Fin k × Fin k, matrixWeight i j tail bulk p (s p.1 p.2)) = tail (s i j) *
      ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)).erase (i, j), bulk (s p.1 p.2) := by
  classical
  rw [show (Finset.univ : Finset (Fin k × Fin k)) =
        Finset.univ.offDiag ∪ (Finset.univ \ Finset.univ.offDiag) by
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)],
    Finset.prod_union Finset.disjoint_sdiff]
  have hcompl : (∏ p ∈ Finset.univ \ Finset.univ.offDiag,
      matrixWeight i j tail bulk p (s p.1 p.2)) = 1 := by
    refine Finset.prod_eq_one fun p hp ↦ ?_
    have hpoff : p ∉ (Finset.univ.offDiag : Finset (Fin k × Fin k)) := (Finset.mem_sdiff.mp hp).2
    have hpd : p.1 = p.2 := not_not.mp fun hne ↦
      hpoff (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩)
    have hpij : p ≠ (i, j) := fun h ↦ hpoff (by rw [h]; exact mem_offDiag_pair i j hij)
    unfold matrixWeight DiagTerm
    rw [if_neg hpij, if_neg hpoff, ← hpd, hdiag p.1, if_pos rfl]
  rw [hcompl, mul_one, ← Finset.mul_prod_erase _ _ (mem_offDiag_pair i j hij)]
  congr 1
  · simp [matrixWeight]
  · refine Finset.prod_congr rfl fun p hp ↦ ?_
    unfold matrixWeight
    rw [if_neg (Finset.ne_of_mem_erase hp), if_pos (Finset.mem_of_mem_erase hp)]

/-- The matrix-block `tsum` of `matrixWeight` factors as the tail sum times the `(k² - k - 1)`-st
power of the bulk sum. -/
theorem tsum_prod_matrixWeight {k : ℕ} (i j : Fin k) (hij : i ≠ j) {tail bulk : ℕ → ℝ}
    (htailnn : ∀ n, 0 ≤ tail n) (hbulknn : ∀ n, 0 ≤ bulk n)
    (htail : Summable tail) (hbulk : Summable bulk) :
    (∑' s : Fin k → Fin k → ℕ, ∏ p : Fin k × Fin k, matrixWeight i j tail bulk p (s p.1 p.2)) =
      (∑' n : ℕ, tail n) * (∑' n : ℕ, bulk n) ^ (k ^ 2 - k - 1) := by
  classical
  refine matrix_block_factor i j hij (matrixWeight i j tail bulk)
    (matrixWeight_nonneg i j htailnn hbulknn) (matrixWeight_summable i j htail hbulk)
    tail bulk ?_ ?_ ?_
  · intro n
    simp [matrixWeight]
  · intro p hp n
    unfold matrixWeight
    rw [if_neg (Finset.ne_of_mem_erase hp), if_pos (Finset.mem_of_mem_erase hp)]
  · intro p hp n
    have hpij : p ≠ (i, j) := fun h ↦ hp (by rw [h]; exact mem_offDiag_pair i j hij)
    unfold matrixWeight
    rw [if_neg hpij, if_neg hp]
    rfl

/-- `0 ≤ MatrixTerm N R i j p n`. -/
theorem MatrixTerm_nonneg {k : ℕ} (N : ℕ) (R : ℝ) (i j : Fin k) (p : Fin k × Fin k) (n : ℕ) :
    0 ≤ MatrixTerm N R i j p n :=
  matrixWeight_nonneg i j (fun n ↦ by unfold Sijterm; split <;> positivity)
    (fun n ↦ by unfold S0term; split <;> positivity) p n

/-- `MatrixTerm N R i j p` is summable in each of its three cases. -/
theorem MatrixTerm_summable {k : ℕ} (N : ℕ) (R : ℝ) (i j : Fin k) (p : Fin k × Fin k) :
    Summable (MatrixTerm N R i j p) :=
  matrixWeight_summable i j (summable_Sijterm N R) (summable_S0term R) p

/-- On the diagonal guard `s a a = 1` the full `MatrixTerm` product over `Fin k × Fin k` collapses
to the distinguished-pair term times the remaining off-diagonal terms.
-/
theorem prod_MatrixTerm_of_diag {k : ℕ} (N : ℕ) (R : ℝ) (i j : Fin k) (hij : i ≠ j)
    (s : Fin k → Fin k → ℕ) (hdiag : ∀ a, s a a = 1) :
    (∏ p : Fin k × Fin k, MatrixTerm N R i j p (s p.1 p.2)) = Sijterm N R (s i j) *
      ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)).erase (i, j), S0term R (s p.1 p.2) :=
  prod_matrixWeight_of_diag i j hij _ _ s hdiag

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- On the single-pair guard the absolute value of the summand is bounded by the coordinatewise
product majorant: `Finsupp.maxRealAbs (PrimeGaps.lToY lam) ²` times the product over `u`
-coordinates of `Uterm`, times the product over the matrix coordinates of `MatrixTerm`.
-/
theorem pair_pointwise_majorant {k : ℕ} (N : ℕ) (R : ℝ) (W : ℕ)
    (hW : W = primorial ⌊PrimeGaps.D₀ N⌋₊) (lam : (Fin k → ℕ) →₀ ℝ)
    (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W)
    (i j : Fin k) (hij : i ≠ j) (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ) :
    |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
      RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s i j) then
            (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
            (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                (μ (s p.1 p.2) : ℝ) / (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
            PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
          else 0)| ≤ (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 *
        (∏ a, Uterm W R (u a)) *
        (∏ p : Fin k × Fin k, MatrixTerm N R i j p (s p.1 p.2)) := by
  classical
  have hUnn : ∀ n, 0 ≤ Uterm W R n := fun n ↦ by unfold Uterm; split <;> positivity
  have hRHSnn : (0 : ℝ) ≤ (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 * (∏ a,
      Uterm W R (u a)) * (∏ p : Fin k × Fin k, MatrixTerm N R i j p (s p.1 p.2)) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun a _ ↦ hUnn _))
      (Finset.prod_nonneg fun p _ ↦ MatrixTerm_nonneg N R i j p _)
  by_cases hg : (∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
              RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s i j
  · rw [if_pos hg]
    obtain ⟨hu, hdiag, hsij, _, hD⟩ := hg
    by_cases hz : PrimeGaps.lToY lam (boldA u s) = 0 ∨ PrimeGaps.lToY lam (boldB u s) = 0
    · have hσ0 : (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
            (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                (μ (s p.1 p.2) : ℝ) / (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
            PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s) = 0 := by
        rcases hz with h | h <;> simp [h]
      rw [hσ0, abs_zero]
      exact hRHSnn
    · push Not at hz
      obtain ⟨hzA, hzB⟩ := hz
      have hUeq : (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) =
          ∏ a, Uterm W R (u a) := by
        refine Finset.prod_congr rfl fun a _ ↦ ?_
        unfold Uterm
        rw [if_pos ⟨hu a, Nat.le_floor (u_bound R W lam hlam u s hsij hzA a),
          u_coprime R W lam hlam u s hzA a⟩]
      have hijmem : (i, j) ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)) :=
        mem_offDiag_pair i j hij
      have hPsabs : |∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              (μ (s p.1 p.2) : ℝ) / (Nat.totient (s p.1 p.2) : ℝ) ^ 2| =
          ∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              |(μ (s p.1 p.2) : ℝ) / (Nat.totient (s p.1 p.2) : ℝ) ^ 2| :=
        Finset.abs_prod _ _
      have hSijeq : |(μ (s i j) : ℝ) / (Nat.totient (s i j) : ℝ) ^ 2| =
          Sijterm N R (s i j) := by
        unfold Sijterm
        have hprime : ∀ q, Nat.Prime q → q ∣ s i j → ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < q := by
          rcases lem_S1_sij_dichotomy N R W hW lam hlam u s ⟨hzA, hzB⟩ i j hij with h1 | h2
          · intro q hq hqd
            rw [h1] at hqd
            exact absurd (Nat.dvd_one.mp hqd) hq.ne_one
          · exact h2
        rw [if_pos ⟨hsij i j hij,
          Nat.le_floor (s_bound R W lam hlam u s hu hsij hzA i j hij.symm), hD, hprime⟩]
      have hS0eq : ∀ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)).erase (i, j),
          |(μ (s p.1 p.2) : ℝ) / (Nat.totient (s p.1 p.2) : ℝ) ^ 2| =
            S0term R (s p.1 p.2) := by
        intro p hp
        have hpoff := Finset.mem_offDiag.mp (Finset.mem_of_mem_erase hp)
        unfold S0term
        rw [if_pos ⟨hsij p.1 p.2 hpoff.2.2,
          Nat.le_floor (s_bound R W lam hlam u s hu hsij hzA p.1 p.2 hpoff.2.2.symm)⟩]
      have hPsfull : |∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              (μ (s p.1 p.2) : ℝ) / (Nat.totient (s p.1 p.2) : ℝ) ^ 2| =
          ∏ p : Fin k × Fin k, MatrixTerm N R i j p (s p.1 p.2) := by
        rw [prod_MatrixTerm_of_diag N R i j hij s hdiag, hPsabs,
          ← Finset.mul_prod_erase _ _ hijmem, hSijeq]
        congr 1
        exact Finset.prod_congr rfl hS0eq
      calc |(∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s p.1 p.2) : ℝ) /
                      (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
                PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)| ≤
                  Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 *
              (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
              |∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                  (μ (s p.1 p.2) : ℝ) /
                    (Nat.totient (s p.1 p.2) : ℝ) ^ 2| := sigma_abs_le lam u s
        _ = (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 * (∏ a, Uterm W R (u a)) *
              (∏ p : Fin k × Fin k, MatrixTerm N R i j p (s p.1 p.2)) := by
            rw [hUeq, hPsfull]
  · rw [if_neg hg, abs_zero]
    exact hRHSnn

/-- The `u`-block: the `tsum` over `u`-tuples of the coordinatewise `Uterm` product is
`PrimeGaps.MaynardOffDiagonal.sumA ^ k`. -/
theorem tsum_prod_Uterm {k : ℕ} (R : ℝ) (W : ℕ) :
    (∑' u : Fin k → ℕ, ∏ a, Uterm W R (u a)) = (PrimeGaps.MaynardOffDiagonal.sumA W R) ^ k := by
  classical
  rw [pinned_block_factor (ι := Fin k) Finset.univ (fun _ ↦ Uterm W R) (Uterm W R)
      (Uterm_support W R) (fun _ _ _ ↦ rfl) (fun a ha ↦ absurd (Finset.mem_univ a) ha),
    Finset.card_univ, Fintype.card_fin, tsum_Uterm]

/-- The `s`-block: the `tsum` over matrix tuples of the coordinatewise `MatrixTerm` product is
the distinguished-pair tail `Sijfin` times `S0fin ^ (k² - k - 1)`. -/
theorem tsum_prod_MatrixTerm {k : ℕ} (N : ℕ) (R : ℝ) (i j : Fin k) (hij : i ≠ j) :
    (∑' s : Fin k → Fin k → ℕ, ∏ p : Fin k × Fin k, MatrixTerm N R i j p (s p.1 p.2)) =
      Sijfin N R * (S0fin R) ^ (k ^ 2 - k - 1) := by
  unfold MatrixTerm
  rw [tsum_prod_matrixWeight i j hij (fun n ↦ by unfold Sijterm; split <;> positivity)
      (fun n ↦ by unfold S0term; split <;> positivity) (summable_Sijterm N R) (summable_S0term R),
    tsum_Sijterm, tsum_S0term]

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- The single-pair-guarded double tsum of absolute values is bounded by
`Finsupp.maxRealAbs (PrimeGaps.lToY lam) ²` times a product of finite coordinate sums: the `k`
diagonal `u`-blocks each contribute
`PrimeGaps.MaynardOffDiagonal.sumA`, the
distinguished off-diagonal pair `(i,j)` contributes the tail `Sijfin`, and the remaining
`k²-k-1` off-diagonal coordinates each `S0fin`. Route: pointwise `sigma_abs_le` + guard
absorption (`u_coprime`,
`lem_S1_sij_coprime_to_W`, `lem_S1_sij_dichotomy`) to a fully-factored majorant, then reduce the
double tsum to a finite `Finset.sum` (via `guarded_summable` 's finite support) and apply
`Finset.prod_sum`.
-/
theorem pair_master {k : ℕ} (N : ℕ) (R : ℝ) (W : ℕ) (hW : W = primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)
    (lam : (Fin k → ℕ) →₀ ℝ) (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W)
    (i j : Fin k) (hij : i ≠ j) :
    (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
        |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
              RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s i j) then
            (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
            (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                (μ (s p.1 p.2) : ℝ) / (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
            PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
          else 0)|) ≤ (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 *
            (PrimeGaps.MaynardOffDiagonal.sumA W R) ^
            k *
        (S0fin R) ^ (k ^ 2 - k - 1) *
        Sijfin N R := by
  classical
  set Y : ℝ := (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 with hY
  set Pu : (Fin k → ℕ) → ℝ := fun u ↦ ∏ a, Uterm W R (u a) with hPu
  set Ps : (Fin k → Fin k → ℕ) → ℝ := fun s ↦
    ∏ p : Fin k × Fin k, MatrixTerm N R i j p (s p.1 p.2) with hPs
  have hUnn : ∀ n, 0 ≤ Uterm W R n := by intro n; unfold Uterm; split <;> positivity
  have hPu_summable : Summable Pu :=
    summable_prod_of_summable (fun _ : Fin k ↦ Uterm W R) (fun _ n ↦ hUnn n)
      fun _ ↦ summable_Uterm W R
  have hPs_summable : Summable Ps := by
    have hcomp : Ps = (fun t : Fin k × Fin k → ℕ ↦ ∏ p, MatrixTerm N R i j p (t p))
        ∘ (Equiv.curry (Fin k) (Fin k) ℕ).symm := rfl
    rw [hcomp]
    exact (Equiv.summable_iff _).mpr (summable_prod_of_summable (MatrixTerm N R i j)
      (MatrixTerm_nonneg N R i j) (MatrixTerm_summable N R i j))
  refine le_trans (tsum_tsum_le_of_prod_majorant _ Y Pu Ps (fun _ _ ↦ abs_nonneg _)
    (pair_pointwise_majorant N R W hW lam hlam i j hij) hPu_summable hPs_summable)
    (le_of_eq ?_)
  rw [hPu, hPs, tsum_prod_Uterm, tsum_prod_MatrixTerm N R i j hij, hY]
  ring

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Mertens bound on the moment sum: `sumA (W N) R ≤ C₁ * (φ (W N) / W N) * log R` for all large
`N`. -/
theorem mertens_factor (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ N₁ : ℝ, ∀ N : ℕ, N₁ ≤ N →
      PrimeGaps.MaynardOffDiagonal.sumA (W N) R ≤
        C₁ * ((Nat.totient (W N) : ℝ) / (W N : ℝ)) * Real.log R := by
  obtain ⟨hδ0, hδθ2, hθ1⟩ := hδθ
  have hθ0 : 0 < θ := by linarith
  obtain ⟨c₁, hc₁pos, hsumA⟩ := PrimeGaps.MaynardOffDiagonal.sumA_le
  obtain ⟨N₀, hN0, hbound⟩ := hsumA θ δ ⟨hθ0, hθ1⟩ ⟨hδ0, hδθ2⟩
  refine ⟨c₁, hc₁pos, N₀, fun N hN ↦ ?_⟩
  calc PrimeGaps.MaynardOffDiagonal.sumA (W N) R
      ≤ c₁ * (Nat.totient (W N) : ℝ) / (W N : ℝ) * Real.log R := hbound (N : ℝ) hN
    _ = c₁ * ((Nat.totient (W N) : ℝ) / (W N : ℝ)) * Real.log R := by ring

/-- `S0fin` is bounded by an absolute constant `C₂:= ∑' μ²/φ²`, uniformly (drop `Coprime` /box
constraints then `sumB_le_tsum`).
-/
theorem s0_factor : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ R : ℝ, S0fin R ≤ C₂ := by
  classical
  have hsummable :
      Summable (fun n ↦ (μ n : ℝ) ^ 2 / (Nat.totient n : ℝ) ^ 2) :=
    PrimeGaps.lem_convergent_sum_phi
  refine ⟨∑' n, (μ n : ℝ) ^ 2 / (Nat.totient n : ℝ) ^ 2, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ ∑' n, (μ n : ℝ) ^ 2 / (Nat.totient n : ℝ) ^ 2 := by
      simpa using Summable.sum_le_tsum ({1} : Finset ℕ) (fun n _ ↦ by positivity) hsummable
    linarith
  · intro R
    unfold S0fin
    have heq : ∀ n : ℕ, |(μ n : ℝ) / (Nat.totient n : ℝ) ^ 2| =
        (μ n : ℝ) ^ 2 / (Nat.totient n : ℝ) ^ 2 := fun n ↦ by
      rw [abs_div, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient n : ℝ))]
      congr 1
      rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ ↦ heq n)) ?_
    exact Summable.sum_le_tsum _ (fun n _ ↦ by positivity) hsummable

end PrimeGaps

namespace Nat

/-- If every prime factor of `n` exceeds `Y`, then `n` is coprime to `primorial Y` (the product of
primes `≤ Y`).
-/
theorem coprime_primorial (n Y : ℕ) (h : ∀ q, Nat.Prime q → q ∣ n → Y < q) :
    Nat.Coprime n (primorial Y) := by
  rw [Nat.coprime_comm]
  unfold primorial
  refine Nat.Coprime.prod_left fun p hp ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hple, hpp⟩ := hp
  rw [hpp.coprime_iff_not_dvd]
  exact fun hdvd ↦ absurd (h p hpp hdvd) (by omega)

end Nat

namespace PrimeGaps

/-- `Sijfin` (tail over `n` with all prime factors `> ⌊D₀⌋₊`) is dominated by
`MaynardOffDiagonal.sumT (primorial ⌊D₀⌋₊)`: each such `n` with `μ(n) ≠ 0` is squarefree, coprime
to `primorial ⌊D₀⌋₊`, and `≠ 1`, with `|μ(n)/φ(n)²| = 1/φ(n)²`.
-/
theorem Sijfin_le_sumT (N : ℕ) (R : ℝ) (hY1 : 1 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) :
    Sijfin N R ≤ PrimeGaps.MaynardOffDiagonal.sumT
          (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) R := by
  classical
  unfold Sijfin PrimeGaps.MaynardOffDiagonal.sumT
    PrimeGaps.MaynardOffDiagonal.Sset
  set Y := ⌊PrimeGaps.D₀ (N : ℝ)⌋₊
  apply le_trans (Finset.sum_le_sum
    (g := fun n ↦ if Squarefree n then 1 / (Nat.totient n : ℝ) ^ 2 else 0) ?_)
  · rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn ↦ ?_) fun n _ _ ↦ by positivity
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨⟨h1, hR⟩, hgt, hprime⟩, hsf⟩ := hn
    exact ⟨⟨⟨h1, hR⟩, hsf, Nat.coprime_primorial n Y hprime⟩, by omega⟩
  · intro n hn
    by_cases hsf : Squarefree n
    · rw [if_pos hsf, abs_div, abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient n : ℝ)),
        ArithmeticFunction.moebius_apply_of_squarefree hsf]
      refine le_of_eq (congrArg (· / (Nat.totient n : ℝ) ^ 2) ?_)
      push_cast
      rw [abs_pow]
      simp
    · rw [if_neg hsf, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      simp

/-- `PrimeGaps.D₀ ↑N = log(log(log N)) → ∞`, so `2 ≤ D₀ ↑N` for `N` large. We take the threshold
`N₂ = exp(exp(exp 2))` and use monotonicity of `Real.log`.
-/
theorem two_le_D0_eventually : ∃ N₂ : ℝ, ∀ N : ℕ, N₂ ≤ N → 2 ≤ PrimeGaps.D₀ (N : ℝ) := by
  refine ⟨rexp (rexp (rexp 2)), fun N hN ↦ ?_⟩
  unfold PrimeGaps.D₀
  have h1 : rexp (rexp 2) ≤ Real.log (N : ℝ) := by
    rw [← Real.log_exp (rexp (rexp 2))]
    exact Real.log_le_log (Real.exp_pos _) hN
  have h2 : rexp 2 ≤ Real.log (Real.log (N : ℝ)) := by
    rw [← Real.log_exp (rexp 2)]
    exact Real.log_le_log (Real.exp_pos _) h1
  rw [← Real.log_exp 2]
  exact Real.log_le_log (Real.exp_pos 2) h2

/-- Eventually `Sijfin ≤ C₃/D₀`, via `Sijfin ≤ sumT (primorial ⌊D₀⌋₊)` (`Sijfin_le_sumT`) and the
tail estimate `MaynardOffDiagonal.sumB_sumT_le` (`sumT ≤ 2·C_B/D₀` once `2 ≤ D₀`).
-/
theorem sij_factor (R₀ : ℕ → ℝ) : ∃ C₃ : ℝ, 0 < C₃ ∧ ∃ N₂ : ℝ, ∀ N : ℕ, N₂ ≤ N →
      Sijfin N (R₀ N) ≤ C₃ / PrimeGaps.D₀ (N : ℝ) := by
  obtain ⟨C_B, hCBpos, _, hsumT⟩ := PrimeGaps.MaynardOffDiagonal.sumB_sumT_le
  obtain ⟨N₂, hN2⟩ := two_le_D0_eventually
  refine ⟨2 * C_B, by linarith, N₂, ?_⟩
  intro N hN
  have hD0 : 2 ≤ PrimeGaps.D₀ (N : ℝ) := hN2 N hN
  have hY1 : 1 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ :=
    Nat.le_floor (by push_cast; linarith)
  calc Sijfin N (R₀ N) ≤ PrimeGaps.MaynardOffDiagonal.sumT
          (primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) (R₀ N) :=
        Sijfin_le_sumT N (R₀ N) hY1
    _ ≤ 2 * C_B / PrimeGaps.D₀ (N : ℝ) := hsumT (N : ℝ) (R₀ N) hD0

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- For a fixed off-diagonal pair `(i,j)`, the `N/W` -weighted absolute value of the
single-pair-restricted double tsum is bounded by the common error term.
-/
theorem lem_S1_sij_D0_pair {k : ℕ} :
    ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    ∀ lam : (Fin k → ℕ) →₀ ℝ, lam.HasPermissibleSupport ⌊R⌋₊ (W N) →
    ∀ i j : Fin k, i ≠ j → (N / (W N : ℝ)) * (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
            |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                  RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s i j) then
                (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s p.1 p.2) : ℝ) /
                      (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
                PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
              else 0)|) ≤ C * (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 *
                (Nat.totient (W N) : ℝ) ^ k *
            N * (Real.log R) ^ k /
            ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  intro θ δ hθ hδ
  obtain ⟨hθ0, hθ1⟩ := hθ
  obtain ⟨hδ0, hδθ2⟩ := hδ
  obtain ⟨C₁, hC₁pos, N₁, hmert⟩ := mertens_factor δ θ ⟨hδ0, hδθ2, hθ1⟩
  obtain ⟨C₂, hC₂pos, hs0⟩ := s0_factor
  obtain ⟨C₃, hC₃pos, N₂, hsij⟩ := sij_factor (fun N : ℕ ↦ R)
  refine ⟨C₁ ^ k * C₂ ^ (k ^ 2 - k - 1) * C₃, by positivity, max N₁ N₂, ?_⟩
  intro N hN lam hlam i j hij
  have hN1 : N₁ ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  set Wt := W N with hW
  set D := PrimeGaps.D₀ (N : ℝ) with hD
  have hWprim : Wt = primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ := by
    rw [hW, PrimeGaps.W_eq_primorial_D₀]
  have hlam' : lam.HasPermissibleSupport ⌊R⌋₊ Wt := by simpa only [hW] using hlam
  have hmaster := pair_master N R Wt hWprim lam hlam' i j hij
  have hUf := hmert N hN1
  have hSf := hs0 R
  have hTf := hsij N hN2
  simp only [← hW, ← hD] at hmaster hUf hSf hTf
  have hUfnn : (0 : ℝ) ≤ PrimeGaps.MaynardOffDiagonal.sumA Wt R :=
    Finset.sum_nonneg fun n _ ↦ by positivity
  have hS0nn : (0 : ℝ) ≤ S0fin R := Finset.sum_nonneg fun n _ ↦ abs_nonneg _
  have hSijnn : (0 : ℝ) ≤ Sijfin N R := Finset.sum_nonneg fun n _ ↦ abs_nonneg _
  have hNWnn : (0 : ℝ) ≤ (N : ℝ) / (Wt : ℝ) := by positivity
  have key : (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 *
    (PrimeGaps.MaynardOffDiagonal.sumA Wt R) ^ k * (S0fin R) ^ (k ^ 2 - k - 1) * Sijfin N R ≤
      (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 * (C₁ * ((Nat.totient Wt : ℝ) / (Wt : ℝ)) *
        Real.log R) ^ k *
          C₂ ^ (k ^ 2 - k - 1) * (C₃ / D) := by
    have hym0 : (0 : ℝ) ≤ (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 := sq_nonneg _
    have hAk0 : (0 : ℝ) ≤ (C₁ * ((Nat.totient Wt : ℝ) / (Wt : ℝ)) * Real.log R) ^ k :=
      pow_nonneg (hUfnn.trans hUf) k
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hUfnn hUf k) hym0)
      (pow_le_pow_left₀ hS0nn hSf _) (pow_nonneg hS0nn _) (mul_nonneg hym0 hAk0)) hTf hSijnn
      (mul_nonneg (mul_nonneg hym0 hAk0) (pow_nonneg hC₂pos.le _))
  calc (N / (Wt : ℝ)) * (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
            |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                  RestrictedCoprime u s ∧ ⌊D⌋₊ < s i j) then
                (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s p.1 p.2) : ℝ) /
                      (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
                PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
              else 0)|) ≤ (N / (Wt : ℝ)) *
          ((Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 *
            (PrimeGaps.MaynardOffDiagonal.sumA Wt R) ^ k *
            (S0fin R) ^ (k ^ 2 - k - 1) * Sijfin N R) :=
        mul_le_mul_of_nonneg_left hmaster hNWnn
    _ ≤ (N / (Wt : ℝ)) * ((Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 *
          (C₁ * ((Nat.totient Wt : ℝ) / (Wt : ℝ)) * Real.log R) ^ k *
            C₂ ^ (k ^ 2 - k - 1) * (C₃ / D)) :=
        mul_le_mul_of_nonneg_left key hNWnn
    _ = C₁ ^ k * C₂ ^ (k ^ 2 - k - 1) * C₃ * (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 *
          (Nat.totient Wt : ℝ) ^ k * N * (Real.log R) ^ k / ((Wt : ℝ) ^ (k + 1) * D) := by
        rw [mul_pow, mul_pow, div_pow, pow_succ]
        ring

open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- With `B(u,s) = ∃ (i,j)∈offDiag, ⌊D₀⌋₊ < s i j`, the guarded double tsum is dominated, in
absolute value, by the sum over the `k(k-1)` off-diagonal pairs of the single-pair-restricted
double tsums. Pointwise: any `(u,s)` satisfying `B` satisfies the single-pair condition for at
least one `(i,j)∈offDiag`, so triangle inequality across the finite `offDiag` index gives the
bound. Hints: `Finset.abs_sum_le_sum_abs`, `tsum` monotonicity / `abs_tsum_le`, split `if B` into
the finite union over `offDiag`.
-/
theorem lem_S1_sij_D0_union {k : ℕ} (N : ℕ) (R : ℝ) (Wt : ℕ)
    (lam : (Fin k → ℕ) →₀ ℝ) (hlam : lam.HasPermissibleSupport ⌊R⌋₊ Wt) :
      |∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
            (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                  RestrictedCoprime u s ∧
                  (∃ i j : Fin k, i ≠ j ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s i j)) then
                (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s p.1 p.2) : ℝ) /
                      (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
                PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
              else 0)| ≤ ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
          (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
            |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                  RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s p.1 p.2) then
                (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s q.1 q.2) : ℝ) /
                      (Nat.totient (s q.1 q.2) : ℝ) ^ 2) *
                PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
              else 0)|) := by
  classical
  set σ : (Fin k → ℕ) → (Fin k → Fin k → ℕ) → ℝ := fun u s ↦
      (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
      (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
          (μ (s q.1 q.2) : ℝ) / (Nat.totient (s q.1 q.2) : ℝ) ^ 2) *
      PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s) with hσ
  set G : (Fin k → ℕ) → (Fin k → Fin k → ℕ) → Prop := fun u s ↦
      (∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s with hG
  set fB : (Fin k → ℕ) × (Fin k → Fin k → ℕ) → ℝ := fun us ↦
      if (G us.1 us.2 ∧ (∃ i j : Fin k, i ≠ j ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < us.2 i j))
        then σ us.1 us.2 else 0 with hfB
  set gp : Fin k × Fin k → (Fin k → ℕ) × (Fin k → Fin k → ℕ) → ℝ := fun p us ↦
      if (G us.1 us.2 ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < us.2 p.1 p.2)
        then σ us.1 us.2 else 0 with hgp
  have hsum_gp : ∀ p : Fin k × Fin k, Summable (fun us ↦ |gp p us|) := by
    intro p
    have hfeq : (fun us ↦ |gp p us|) = (fun us : (Fin k → ℕ) × (Fin k → Fin k → ℕ) ↦
      |(if ((∀ i, 1 ≤ us.1 i) ∧ (∀ i, us.2 i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ us.2 i j) ∧
            RestrictedCoprime us.1 us.2 ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < us.2 p.1 p.2) then
          (∏ i, (μ (us.1 i) : ℝ) ^ 2 / (Nat.totient (us.1 i) : ℝ)) *
          (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              (μ (us.2 q.1 q.2) : ℝ) /
                (Nat.totient (us.2 q.1 q.2) : ℝ) ^ 2) *
          PrimeGaps.lToY lam (boldA us.1 us.2) * PrimeGaps.lToY lam (boldB us.1 us.2)
        else 0)|) := by
      funext us
      simp only [hgp, hG, hσ, and_assoc]
    rw [hfeq]
    exact guarded_summable N R Wt lam hlam p
  have hpt : ∀ us, |fB us| ≤ ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), |gp p us| := by
    intro us
    by_cases hB : (G us.1 us.2 ∧ (∃ i j : Fin k, i ≠ j ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < us.2 i j))
    · obtain ⟨hGok, i, j, hij, hlt⟩ := hB
      have hgpij : gp (i, j) us = σ us.1 us.2 := by
        simp only [hgp]
        rw [if_pos ⟨hGok, hlt⟩]
      have hfBeq : fB us = σ us.1 us.2 := by
        simp only [hfB]
        rw [if_pos ⟨hGok, i, j, hij, hlt⟩]
      rw [hfBeq, ← hgpij]
      exact Finset.single_le_sum (f := fun p ↦ |gp p us|) (fun p _ ↦ abs_nonneg _)
        (Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩)
    · have hfB0 : fB us = 0 := by
        simp only [hfB]
        rw [if_neg hB]
      rw [hfB0, abs_zero]
      exact Finset.sum_nonneg fun p _ ↦ abs_nonneg _
  have hsum_bound :
      Summable (fun us ↦ ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), |gp p us|) :=
    summable_sum (fun p _ ↦ hsum_gp p)
  have hsum_absfB : Summable (fun us ↦ |fB us|) :=
    Summable.of_nonneg_of_le (fun us ↦ abs_nonneg _) hpt hsum_bound
  have hsum_fB : Summable fB := hsum_absfB.of_abs
  have hLHS : (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
            (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                  RestrictedCoprime u s ∧
                  (∃ i j : Fin k, i ≠ j ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s i j)) then
                (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s p.1 p.2) : ℝ) /
                      (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
                PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
              else 0)) = ∑' us : (Fin k → ℕ) × (Fin k → Fin k → ℕ), fB us := by
    rw [Summable.tsum_prod' hsum_fB hsum_fB.prod_factor]
    simp only [hfB, hG, hσ, and_assoc]
  have hRHS : ∀ p : Fin k × Fin k, (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
            |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                  RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s p.1 p.2) then
                (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s q.1 q.2) : ℝ) /
                      (Nat.totient (s q.1 q.2) : ℝ) ^ 2) *
                PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
              else 0)|) = ∑' us : (Fin k → ℕ) × (Fin k → Fin k → ℕ), |gp p us| := by
    intro p
    rw [Summable.tsum_prod' (hsum_gp p) (hsum_gp p).prod_factor]
    simp only [hgp, hG, hσ, and_assoc]
  rw [hLHS]
  calc |∑' us, fB us| ≤ ∑' us, |fB us| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fB)
          (by simpa only [Real.norm_eq_abs] using hsum_absfB)
    _ ≤ ∑' us, ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), |gp p us| :=
        Summable.tsum_le_tsum hpt hsum_absfB hsum_bound
    _ = ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), ∑' us, |gp p us| :=
        Summable.tsum_finsetSum (fun p _ ↦ hsum_gp p)
    _ = ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
          (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
            |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                  RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s p.1 p.2) then
                (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s q.1 q.2) : ℝ) /
                      (Nat.totient (s q.1 q.2) : ℝ) ^ 2) *
                PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
              else 0)|) := Finset.sum_congr rfl fun p _ ↦ (hRHS p).symm

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
open GPYSieveS1 PrimeGaps.LemS1RestrictSij in
/-- — the aggregate bound: the total contribution from terms with *at least one* `s_{i,j} > D₀` is
`O(y_max² φ(W)^k N (log R)^k / (W^{k+1} D₀))`.
-/
@[pg_tag "bg246" "lem_S1_sij_D0"]
theorem lem_S1_sij_D0 {k : ℕ} (hk : 2 ≤ k) :
    ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    ∀ lam : (Fin k → ℕ) →₀ ℝ, lam.HasPermissibleSupport ⌊R⌋₊ (W N) → (N / (W N : ℝ)) *
        |∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
            (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                  RestrictedCoprime u s ∧
                  (∃ i j : Fin k, i ≠ j ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s i j)) then
                (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                    (μ (s p.1 p.2) : ℝ) /
                      (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
                PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
              else 0)| ≤ C * (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 *
                (Nat.totient (W N) : ℝ) ^ k *
            N * (Real.log R) ^ k /
            ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  intro θ δ hθ hδ
  obtain ⟨C', hC'pos, N₀, hpair⟩ := lem_S1_sij_D0_pair (k := k) θ δ hθ hδ
  refine ⟨#(Finset.univ.offDiag : Finset (Fin k × Fin k)) * C', ?_, N₀, ?_⟩
  · have hcard : 0 < #(Finset.univ.offDiag : Finset (Fin k × Fin k)) := by
      rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      have hle : 2 * k ≤ k * k := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right k hk
      omega
    have hcardR : (0 : ℝ) < (#(Finset.univ.offDiag : Finset (Fin k × Fin k)) : ℝ) := by
      exact_mod_cast hcard
    positivity
  · intro N hN lam hlam
    set RHS1 : ℝ := C' * (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 *
      (Nat.totient (W N) : ℝ) ^ k * N * (Real.log R) ^ k /
        ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) with hRHS1
    have hNWnonneg : (0 : ℝ) ≤ (N / (W N : ℝ)) := by positivity
    have hunion := lem_S1_sij_D0_union (k := k) N R (W N) lam hlam
    calc (N / (W N : ℝ)) *
            |∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
              (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                    RestrictedCoprime u s ∧
                    (∃ i j : Fin k, i ≠ j ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s i j)) then
                  (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                  (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                      (μ (s p.1 p.2) : ℝ) /
                        (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
                  PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
                else 0)| ≤ (N / (W N : ℝ)) *
            ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
                |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                      RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s p.1 p.2) then
                    (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                    (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                        (μ (s q.1 q.2) : ℝ) /
                          (Nat.totient (s q.1 q.2) : ℝ) ^ 2) *
                    PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
                  else 0)|) :=
          mul_le_mul_of_nonneg_left hunion hNWnonneg
      _ = ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), (N /
        (W N : ℝ)) * (∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
                |(if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
                      RestrictedCoprime u s ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s p.1 p.2) then
                    (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
                    (∏ q ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
                        (μ (s q.1 q.2) : ℝ) /
                          (Nat.totient (s q.1 q.2) : ℝ) ^ 2) *
                    PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s)
                  else 0)|) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), RHS1 :=
          Finset.sum_le_sum fun p hp ↦
            hpair N hN lam hlam p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
      _ = (#(Finset.univ.offDiag : Finset (Fin k × Fin k)) : ℝ) * RHS1 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (#(Finset.univ.offDiag : Finset (Fin k × Fin k)) : ℝ) * C' *
        (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 * (Nat.totient (W N) : ℝ) ^ k * N *
            (Real.log R) ^ k /
            ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
          rw [hRHS1]
          ring

end PrimeGaps
