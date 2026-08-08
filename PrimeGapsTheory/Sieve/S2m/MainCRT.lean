/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Sums
public import PrimeGapsTheory.Arithmetic.SingularSeries
public import PrimeGapsTheory.Sieve.S2m.CRT
public import PrimeGapsTheory.Sieve.S2m.DmEmOne
public import PrimeGapsTheory.Sieve.S2m.Error
public import PrimeGapsTheory.Sieve.Transforms.YmFromY

import PrimeGapsTheory.Tactic.PaperTag
import PrimeGapsTheory.Sieve.Common.Substitution.FirstMoment

/-!
# CRT decomposition of the second-moment sieve sum

Decomposes the second-moment sieve sum into its main term and aggregate arithmetic-progression
error.

## Main results

* `PrimeGaps.S₂m_CRT_main_term_BV_error`: Bounds the difference between the sieve sum and the
  totient-weighted main term.
-/

@[expose] public section

open scoped BigOperators

namespace PrimeGaps

/-- `Nat.primeCountingIocError N (2 * N) q = MaynardS2Error.windowError N q`. -/
theorem primeCountingIocError_eq_windowError (N q : ℕ) :
    Nat.primeCountingIocError N (2 * N) q = MaynardS2Error.windowError (N : ℝ) q := by
  simp only [MaynardS2Error.windowError, Nat.floor_natCast]
  congr 2
  rw [show 2 * (N : ℝ) = ((2 * N : ℕ) : ℝ) by norm_num, Nat.floor_natCast]

/-- `weight h l n = (∑ d ∈ L.support with ∀ i, d i ∣ n + h i, l d) ^ 2`, for `l = ⇑L` and
`n + h i ≠ 0`. -/
theorem S2m_weight_eq_support_square {k : ℕ} (h : Fin k → ℕ)
    (l : (Fin k → ℕ) → ℝ) (L : (Fin k → ℕ) →₀ ℝ) (hLl : ⇑L = l) (n : ℕ)
    (hn : ∀ i, n + h i ≠ 0) :
    PrimeGaps.weight h l n = (∑ d ∈ L.support with (∀ i, d i ∣ n + h i), l d) ^ 2 := by
  unfold PrimeGaps.weight
  congr 1
  have hmem : ∀ d : Fin k → ℕ,
      d ∈ Fintype.piFinset (fun i ↦ (n + h i).divisors) ↔ (∀ i, d i ∣ n + h i) := fun d ↦ by
    rw [Fintype.mem_piFinset]
    exact ⟨fun hd i ↦ (Nat.mem_divisors.mp (hd i)).1,
      fun hd i ↦ Nat.mem_divisors.mpr ⟨hd i, hn i⟩⟩
  have hLHS : (∑ d ∈ Fintype.piFinset (fun i ↦ (n + h i).divisors), l d) =
        ∑ d ∈ Fintype.piFinset (fun i ↦ (n + h i).divisors) with d ∈ L.support, l d :=
    (Finset.sum_filter_of_ne
      (fun d _ hne ↦ Finsupp.mem_support_iff.mpr (by rw [hLl]; exact hne))).symm
  rw [hLHS]
  apply Finset.sum_congr _ (fun _ _ ↦ rfl)
  ext d
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨hpi, hsup⟩ ↦ ⟨hsup, (hmem d).mp hpi⟩, fun ⟨hsup, hP⟩ ↦ ⟨(hmem d).mpr hP, hsup⟩⟩

open scoped PrimeGaps.sieveModulus in
/-- The sieve modulus `W N` is nonzero. -/
instance instNeZeroW (N : ℕ) : NeZero (W N) := ⟨PrimeGaps.W_pos.ne'⟩

end PrimeGaps

namespace ZMod

/-- A natural number reduces to `a : ZMod m` exactly when its residue modulo `m` is `a.val`. -/
theorem natCast_eq_iff_mod_eq_val {m : ℕ} [NeZero m] (n : ℕ) (a : ZMod m) :
    (n : ZMod m) = a ↔ n % m = a.val := by
  rw [← (ZMod.val_injective m).eq_iff, ZMod.val_natCast]

end ZMod

namespace PrimeGaps

open scoped PrimeGaps.sieveModulus in
/-- `S₂m` as a sum over `n ∈ Ioc N (2N)` of the residue-class indicator for `wt₀ mod W N` times
`χ_P(n + h m)` times the squared support sum. -/
theorem S2m_eq_expansion_lhs {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (N : ℕ) (wt₀ : ZMod (W N))
    (l : (Fin k → ℕ) → ℝ) (L : (Fin k → ℕ) →₀ ℝ) (hLl : ⇑L = l) :
    PrimeGaps.S₂m h l N wt₀ m = ∑ n ∈ Finset.Ioc N (2 * N), if n % (W N) = (wt₀.val) % (W N) then
            PrimeGaps.primeIndicator (n + h m) *
              (∑ d ∈ L.support with (∀ i, d i ∣ n + h i), l d) ^ 2
          else 0 := by
  unfold PrimeGaps.S₂m
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Finset.mem_Ioc] at hn
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hn.1
  have hne : ∀ i, n + h i ≠ 0 := fun i ↦ by positivity
  rw [S2m_weight_eq_support_square h l L hLl n hne, PrimeGaps.primeIndicator_apply]
  simp only [ZMod.natCast_eq_iff_mod_eq_val, Nat.mod_eq_of_lt wt₀.val_lt]

/-- The cast `ℕ → ℤ` as an embedding, used to transport the window `Ioc N (2N)` to `ℤ`. -/
private def natCastEmb : ℕ ↪ ℤ := ⟨Nat.cast, fun _ _ h ↦ by exact_mod_cast h⟩

@[simp] private lemma natCastEmb_apply (n : ℕ) : natCastEmb n = (n : ℤ) := rfl

open scoped PrimeGaps.sieveModulus in
/-- The prime count over `n ∈ Ioc N (2N)` with `n ≡ wt₀ (mod W N)` and `[dᵢ, eᵢ] ∣ n + hᵢ` is
`PrimeGaps.sieveCount h m (W N) wt₀.val d e N`. -/
theorem inner_sum_eq_crux_S {k : ℕ} (h : Fin k → ℕ) (m : Fin k)
    (N : ℕ) (wt₀ : ZMod (W N)) (d e : Fin k → ℕ) :
    (∑ n ∈ Finset.Ioc N (2 * N), if n % (W N) = (wt₀.val) % (W N) ∧ ∀ i,
          (d i).lcm (e i) ∣ n + h i then
          PrimeGaps.primeIndicator (n + h m)
        else 0) = PrimeGaps.sieveCount (fun i ↦ (↑(h i) : ℤ)) m
          (W N) (↑wt₀.val : ℤ) d e N := by
  unfold PrimeGaps.sieveCount window
  rw [Finset.sum_filter]
  have hcast : (Finset.Ioc (↑N : ℤ) (2 * ↑N)) = (Finset.Ioc N (2 * N)).map natCastEmb := by
    ext z
    simp only [Finset.mem_Ioc, Finset.mem_map, natCastEmb_apply]
    constructor
    · rintro ⟨h1, h2⟩
      have hz : (0 : ℤ) < z := lt_of_le_of_lt (Int.natCast_nonneg N) h1
      exact ⟨z.toNat, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
      exact ⟨by exact_mod_cast ha1, by exact_mod_cast ha2⟩
  rw [hcast, Finset.sum_map]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Finset.mem_Ioc] at hn
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hn.1
  simp only [natCastEmb_apply]
  have hcong : ((↑n : ℤ) ≡ (↑wt₀.val : ℤ) [ZMOD ↑(W N)]) ↔ n % (W N) = (wt₀.val) % (W N) := by
    rw [Int.ModEq, ← Int.natCast_mod, ← Int.natCast_mod, Int.natCast_inj]
  have hdvd : (∀ i, (↑((d i).lcm (e i)) : ℤ) ∣ (↑n : ℤ) + ↑(h i)) ↔
      (∀ i, (d i).lcm (e i) ∣ n + h i) := by
    have hc : ∀ i, (↑n : ℤ) + ↑(h i) = ((n + h i : ℕ) : ℤ) := fun i ↦ by push_cast; ring
    simp only [hc, Int.natCast_dvd_natCast]
  have hchi : chiP ((↑n : ℤ) + ↑(h m)) = PrimeGaps.primeIndicator (n + h m) := by
    unfold chiP
    rw [PrimeGaps.primeIndicator_apply]
    have hpos : (0 : ℤ) < (↑n : ℤ) + ↑(h m) := by positivity
    have hnatabs : ((↑n : ℤ) + ↑(h m)).natAbs = n + h m := by
      rw [show (↑n : ℤ) + ↑(h m) = ((n + h m : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
    rw [hnatabs]
    by_cases hp : Nat.Prime (n + h m)
    · rw [if_pos ⟨hpos, hp⟩, if_pos hp]
    · rw [if_neg (fun hh ↦ hp hh.2), if_neg hp]
  simp only [and_congr hcong hdvd, hchi]

open scoped PrimeGaps.sieveModulus in
/-- Expanding the square: the window sum equals `∑_{d, e ∈ L.support} l d * l e` times the count
of `n ∈ Ioc N (2N)` in the residue class with `[dᵢ, eᵢ] ∣ n + hᵢ`. -/
theorem S2m_ioc_expand {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (N : ℕ) (wt₀ : ZMod (W N))
    (l : (Fin k → ℕ) → ℝ) (L : (Fin k → ℕ) →₀ ℝ) :
    (∑ n ∈ Finset.Ioc N (2 * N), if n % (W N) = (wt₀.val) % (W N) then
          PrimeGaps.primeIndicator (n + h m) * (∑ d ∈ L.support with (∀ i, d i ∣ n + h i), l d) ^ 2
        else 0) = ∑ d ∈ L.support, ∑ e ∈ L.support, l d * l e *
            (∑ n ∈ Finset.Ioc N (2 * N), if n % (W N) = (wt₀.val) %
              (W N) ∧ ∀ i, (d i).lcm (e i) ∣ n + h i then
                  PrimeGaps.primeIndicator (n + h m)
                else 0) := by
  classical
  have step1 : (∑ d ∈ L.support, ∑ e ∈ L.support, l d * l e *
          (∑ n ∈ Finset.Ioc N (2 * N), if n % (W N) = (wt₀.val) %
            (W N) ∧ ∀ i, (d i).lcm (e i) ∣ n + h i then
                PrimeGaps.primeIndicator (n + h m)
              else 0)) = ∑ n ∈ Finset.Ioc N (2 * N), ∑ d ∈ L.support, ∑ e ∈ L.support,
          l d * l e * (if n % (W N) = (wt₀.val) % (W N) ∧ ∀ i, (d i).lcm (e i) ∣ n + h i then
              PrimeGaps.primeIndicator (n + h m)
            else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm_cycle]
  rw [step1]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  by_cases hc : n % (W N) = (wt₀.val) % (W N)
  · rw [if_pos hc, sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    by_cases hd : ∀ i, d i ∣ n + h i
    · rw [if_pos hd, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      by_cases he : ∀ i, e i ∣ n + h i
      · rw [if_pos he, if_pos ⟨hc, fun i ↦ Nat.lcm_dvd (hd i) (he i)⟩]
        ring
      · obtain ⟨i, hei⟩ : ∃ i, ¬ e i ∣ n + h i := by push Not at he; exact he
        rw [if_neg he, if_neg fun hh ↦ hei ((Nat.dvd_lcm_right _ _).trans (hh.2 i))]
        ring
    · obtain ⟨i, hdi⟩ : ∃ i, ¬ d i ∣ n + h i := by push Not at hd; exact hd
      rw [if_neg hd]
      exact (Finset.sum_eq_zero fun e _ ↦ by
        rw [if_neg fun hh ↦ hdi ((Nat.dvd_lcm_left _ _).trans (hh.2 i)), mul_zero]).symm
  · rw [if_neg hc]
    exact (Finset.sum_eq_zero fun d _ ↦ Finset.sum_eq_zero fun e _ ↦ by
      rw [if_neg fun hh ↦ hc hh.1, mul_zero]).symm

open scoped PrimeGaps.sieveModulus in
/-- `S₂m h l N wt₀ m = ∑_{d, e ∈ L.support} l d * l e * S h m (W N) wt₀.val d e N`. -/
theorem S2m_expand_to_crux_S {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (N : ℕ) (wt₀ : ZMod (W N))
    (l : (Fin k → ℕ) → ℝ) (L : (Fin k → ℕ) →₀ ℝ) (hLl : ⇑L = l) :
    PrimeGaps.S₂m h l N wt₀ m = ∑ d ∈ L.support, ∑ e ∈ L.support, l d * l e *
            PrimeGaps.sieveCount (fun i ↦ (↑(h i) : ℤ)) m
               (W N) (↑wt₀.val : ℤ) d e N := by
  rw [S2m_eq_expansion_lhs h m N wt₀ l L hLl, S2m_ioc_expand h m N wt₀ l L]
  exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ by
    rw [inner_sum_eq_crux_S h m N wt₀ d e]

/-- `sieveCount` is symmetric in its two divisor tuples, since `[d, e] = [e, d]`. -/
theorem sieveCount_comm {k : ℕ} (h : Fin k → ℤ) (m : Fin k)
    (W : ℕ) (v₀ : ℤ) (d e : Fin k → ℕ) (N : ℕ) :
    PrimeGaps.sieveCount h m W v₀ d e N = PrimeGaps.sieveCount h m W v₀ e d N := by
  unfold PrimeGaps.sieveCount
  simp_rw [Nat.lcm_comm]

open scoped PrimeGaps.sieveModulus in
/-- `S2m_expand_to_crux_S` with the double sum taken over any `D ⊇ L.support`. -/
theorem S2m_expand_to_crux_S_on {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (N : ℕ) (wt₀ : ZMod (W N))
    (l : (Fin k → ℕ) → ℝ) (L : (Fin k → ℕ) →₀ ℝ) (hLl : ⇑L = l)
    (D : Finset (Fin k → ℕ)) (hLD : L.support ⊆ D) :
    PrimeGaps.S₂m h l N wt₀ m = ∑ d ∈ D, ∑ e ∈ D, l d * l e *
        PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m (W N) (wt₀.val : ℤ) d e N := by
  rw [S2m_expand_to_crux_S h m N wt₀ l L hLl]
  calc
    (∑ d ∈ L.support, ∑ e ∈ L.support, l d * l e *
          PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m (W N) (wt₀.val : ℤ) d e N) =
        ∑ d ∈ L.support, ∑ e ∈ D, l d * l e *
          PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m (W N) (wt₀.val : ℤ) d e N := by
      refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_subset hLD fun e _ heL ↦ ?_
      have he0 : l e = 0 := by rw [← hLl]; simpa [Finsupp.mem_support_iff] using heL
      simp [he0]
    _ = ∑ d ∈ D, ∑ e ∈ D, l d * l e *
          PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m (W N) (wt₀.val : ℤ) d e N := by
      refine Finset.sum_subset hLD fun d _ hdL ↦ ?_
      have hd0 : l d = 0 := by rw [← hLl]; simpa [Finsupp.mem_support_iff] using hdL
      simp [hd0]

/-- `φ(W * ∏ᵢ [dᵢ, eᵢ]) = φ(W) * ∏ᵢ φ([dᵢ, eᵢ])` when `W` is coprime to each `[dᵢ, eᵢ]` and the
`[dᵢ, eᵢ]` are pairwise coprime. -/
theorem totient_W_mul_lcm_prod {k : ℕ} (W : ℕ) (d e : Fin k → ℕ)
    (hWcop : ∀ i, W.Coprime ((d i).lcm (e i)))
    (hpair : ∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) :
    Nat.totient (W * ∏ i, (d i).lcm (e i)) =
      Nat.totient W * ∏ i, Nat.totient ((d i).lcm (e i)) := by
  rw [Nat.totient_mul (Nat.Coprime.prod_right fun i _ ↦ hWcop i),
    Nat.totient_prod_of_pairwise_coprime _ _ fun i _ j _ hij ↦ hpair i j hij]

open scoped PrimeGaps.sieveModulus in
/-- `S h m (W N) wt₀.val d e N = 0` for a support pair `(d, e)` failing one of the CRT
eligibility clauses gating `restrictedSummand`. -/
theorem crux_S_vanish_of_not_restricted {k : ℕ}
    (h : Fin k → ℕ) (m : Fin k) (hinj : Function.Injective h)
    (θ δ : ℝ) (N : ℕ) (wt₀ : ZMod (W N))
    (hw₀ : ∀ i, ((↑wt₀.val : ℤ) + (↑(h i) : ℤ)).gcd (↑(W N)) = 1)
    (l : (Fin k → ℕ) → ℝ)
    (hsupp : ∀ d, l d ≠ 0 → d ∈ Finset.permissibleSupport k ⌊(↑N : ℝ) ^ (θ / 2 -
      δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊))
    (hD0_large : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊)
    (hcoord_lcm_lt_prime : ∀ dd ee : Fin k → ℕ, l dd ≠ 0 → l ee ≠ 0 →
        ∀ i, (dd i).lcm (ee i) < N + h m)
    (d e : Fin k → ℕ) (hd : l d ≠ 0) (he : l e ≠ 0)
    (hnot : ¬ ((d m = 1) ∧ (e m = 1) ∧ (∀ i, (W N).Coprime ((d i).lcm (e i))) ∧
        (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) ∧ (∀ i, i ≠ m →
              ((↑(h m) : ℤ) - (↑(h i) : ℤ)).gcd (↑((d i).lcm (e i))) = 1))) :
    PrimeGaps.sieveCount (fun i ↦ (↑(h i) : ℤ)) m
      (W N) (↑wt₀.val : ℤ) d e N = 0 := by
  classical
  have hSSd := hsupp d hd
  have hSSe := hsupp e he
  have hdi : ∀ i, 1 ≤ d i := fun i ↦ Nat.one_le_iff_ne_zero.mpr
    (Finset.squarefree_of_mem_permissibleSupport hSSd i).ne_zero
  have hei : ∀ i, 1 ≤ e i := fun i ↦ Nat.one_le_iff_ne_zero.mpr
    (Finset.squarefree_of_mem_permissibleSupport hSSe i).ne_zero
  unfold PrimeGaps.sieveCount
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  rw [Finset.mem_filter] at hn
  obtain ⟨hnwin, hncong, hndvd⟩ := hn
  rw [window, Finset.mem_Ioc] at hnwin
  have hnpos : (0 : ℤ) < n := lt_of_le_of_lt (by exact_mod_cast Nat.zero_le N) hnwin.1
  have hposm : (0 : ℤ) < n + ↑(h m) := by positivity
  rw [chiP, if_neg]
  rintro ⟨ - , hprime⟩
  simp only at hndvd hprime hposm
  set x : ℕ := (n + (↑(h m) : ℤ)).natAbs with hxdef
  have hxcast : (x : ℤ) = n + (↑(h m) : ℤ) := by
    rw [hxdef]; exact Int.natAbs_of_nonneg hposm.le
  have hxgtN : N + h m < x := by
    have : ((N + h m : ℕ) : ℤ) < (x : ℤ) := by rw [hxcast]; push_cast; linarith only [hnwin.1]
    exact_mod_cast this
  -- If either pinned coordinate exceeds `1` then the local modulus `[d m, e m]` is a proper
  -- divisor of `x = n + h m` exceeding `1`, so `x` is not prime.
  have hpin : ¬ (d m = 1 ∧ e m = 1) → False := by
    intro hne
    have hlcmpos : 0 < (d m).lcm (e m) :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by have := hdi m; omega) (by have := hei m; omega))
    have hlcm_ge : 2 ≤ (d m).lcm (e m) := by
      rcases not_and_or.mp hne with hdm | hem
      · exact le_trans (by have := hdi m; omega : 2 ≤ d m)
          (Nat.le_of_dvd hlcmpos (Nat.dvd_lcm_left _ _))
      · exact le_trans (by have := hei m; omega : 2 ≤ e m)
          (Nat.le_of_dvd hlcmpos (Nat.dvd_lcm_right _ _))
    have hlcm_lt : (d m).lcm (e m) < N + h m := hcoord_lcm_lt_prime d e hd he m
    have hlcm_dvd : (d m).lcm (e m) ∣ x := by
      have hZ : (↑((d m).lcm (e m)) : ℤ) ∣ (x : ℤ) := by rw [hxcast]; exact hndvd m
      exact_mod_cast hZ
    exact lem_S2m_dm_em_one x ((d m).lcm (e m)) hlcm_ge (lt_trans hlcm_lt hxgtN) hlcm_dvd hprime
  by_cases hdm : d m = 1
  · by_cases hem : e m = 1
    · have hnot' : ¬ ((∀ i, (W N).Coprime ((d i).lcm (e i))) ∧
          (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) ∧ (∀ i, i ≠ m →
                ((↑(h m) : ℤ) - (↑(h i) : ℤ)).gcd (↑((d i).lcm (e i))) = 1)) := by
        intro hcon; exact hnot ⟨hdm, hem, hcon.1, hcon.2.1, hcon.2.2⟩
      have hcopd : (∏ i, d i).Coprime (W N) := (Finset.mem_permissibleSupport_iff.mp hSSd).2.1
      have hcope : (∏ i, e i).Coprime (W N) := (Finset.mem_permissibleSupport_iff.mp hSSe).2.1
      have hbig : ∀ i (p : ℕ), p.Prime → p ∣ (d i).lcm (e i) → ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊ < p :=
        fun i p hp hpdvd ↦ (Nat.floor_lt' hp.pos.ne').mpr
          (PrimeGaps.lcm_prime_factor_large (↑N : ℝ) d e hcopd hcope i p hp hpdvd)
      by_cases hA : ∀ i, (W N).Coprime ((d i).lcm (e i))
      · by_cases hB : ∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))
        · have hC : ¬ ∀ i, i ≠ m → ((↑(h m) : ℤ) - (↑(h i) : ℤ)).gcd (↑((d i).lcm (e i))) = 1 := by
            intro hC; exact hnot' ⟨hA, hB, hC⟩
          push Not at hC
          obtain ⟨i, him, hgcd⟩ := hC
          obtain ⟨p, hp, hpdvd⟩ :=
            (Int.gcd ((↑(h m) : ℤ) - ↑(h i)) (↑((d i).lcm (e i)))) |>.exists_prime_and_dvd hgcd
          have hpaZ : (↑p : ℤ) ∣ (↑(h m) : ℤ) - ↑(h i) := Int.dvd_natAbs.mp
            (Int.natCast_dvd_natCast.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _)))
          have hplcm : p ∣ (d i).lcm (e i) := by
            simpa using hpdvd.trans (Nat.gcd_dvd_right _ _)
          have hpni : (↑p : ℤ) ∣ n + ↑(h i) := dvd_trans (by exact_mod_cast hplcm) (hndvd i)
          have hpxnat : p ∣ x := by
            have hsum : (↑p : ℤ) ∣ (n + ↑(h i)) + ((↑(h m) : ℤ) - ↑(h i)) := dvd_add hpni hpaZ
            rw [show (n + ↑(h i)) + ((↑(h m) : ℤ) - ↑(h i)) = (x : ℤ) by rw [hxcast]; ring] at hsum
            exact_mod_cast hsum
          have hpe : p = x := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hpxnat
          have hplcm_le : p ≤ (d i).lcm (e i) := Nat.le_of_dvd (Nat.pos_of_ne_zero
            (Nat.lcm_ne_zero (by have := hdi i; omega) (by have := hei i; omega))) hplcm
          have hlcm_lt : (d i).lcm (e i) < N + h m := hcoord_lcm_lt_prime d e hd he i
          omega
        · push Not at hB
          obtain ⟨i, j, hij, hncop⟩ := hB
          obtain ⟨p, hp, hpdvd⟩ :=
            ((d i).lcm (e i)).gcd ((d j).lcm (e j)) |>.exists_prime_and_dvd hncop
          have hpi : p ∣ (d i).lcm (e i) := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
          have hpj : p ∣ (d j).lcm (e j) := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
          have hpni : (↑p : ℤ) ∣ n + ↑(h i) := dvd_trans (by exact_mod_cast hpi) (hndvd i)
          have hpnj : (↑p : ℤ) ∣ n + ↑(h j) := dvd_trans (by exact_mod_cast hpj) (hndvd j)
          have hpdiff : (↑p : ℤ) ∣ (↑(h i) : ℤ) - ↑(h j) := by
            have h1 : (↑p : ℤ) ∣ (n + ↑(h i)) - (n + ↑(h j)) := dvd_sub hpni hpnj
            rwa [show (n + ↑(h i)) - (n + ↑(h j)) = (↑(h i) : ℤ) - ↑(h j) by ring] at h1
          have hpgt : ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊ < p := hbig i p hp hpi
          have hhij : h i ≠ h j := fun heq ↦ hij (hinj heq)
          have hpabs : p ∣ ((↑(h i) : ℤ) - ↑(h j)).natAbs := by
            have hnat := Int.natAbs_dvd_natAbs.mpr hpdiff
            rwa [Int.natAbs_natCast] at hnat
          have hple : p ≤ ((↑(h i) : ℤ) - ↑(h j)).natAbs := Nat.le_of_dvd (by omega) hpabs
          have hdistabs : ((↑(h i) : ℤ) - ↑(h j)).natAbs = (h i).dist (h j) := by
            unfold Nat.dist
            omega
          have hdist : (h i).dist (h j) < ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊ := hD0_large i j hij
          omega
      · push Not at hA
        obtain ⟨i, hncop⟩ := hA
        obtain ⟨p, hp, hpdvd⟩ := (W N).gcd ((d i).lcm (e i)) |>.exists_prime_and_dvd hncop
        have hpW : p ∣ W N := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
        have hplcm : p ∣ (d i).lcm (e i) := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
        have hpni : (↑p : ℤ) ∣ n + ↑(h i) := dvd_trans (by exact_mod_cast hplcm) (hndvd i)
        have hpW' : (↑p : ℤ) ∣ ↑(W N) := by exact_mod_cast hpW
        have hpsub : (↑p : ℤ) ∣ n - ↑wt₀.val := hpW'.trans (Int.modEq_iff_dvd.mp hncong.symm)
        have hpwi : (↑p : ℤ) ∣ ↑wt₀.val + ↑(h i) := by
          have h1 : (↑p : ℤ) ∣ (n + ↑(h i)) - (n - ↑wt₀.val) := dvd_sub hpni hpsub
          rwa [show (n + ↑(h i)) - (n - ↑wt₀.val) = ↑wt₀.val + ↑(h i) by ring] at h1
        have hpgcd : p ∣ Int.gcd (↑wt₀.val + ↑(h i)) ↑(W N) :=
          Nat.dvd_gcd (Int.ofNat_dvd_right.mp hpwi) (Int.ofNat_dvd_right.mp hpW')
        rw [hw₀ i] at hpgcd
        exact hp.ne_one (Nat.dvd_one.mp hpgcd)
    · exact hpin (fun hcon ↦ hem hcon.2)
  · exact hpin (fun hcon ↦ hdm hcon.1)

open scoped PrimeGaps.sieveModulus in
/-- `∑_{d, e ∈ D} |λ_d| |λ_e| · windowError N (qMod (W N) d e) ≤ totalErrorContribution wt`, for
any `D` containing the support of `wt.lam`. -/
theorem finite_double_sum_le_totalErrorContribution {k : ℕ}
    (N : ℕ) (θ δ : ℝ) (wt : MaynardS2Error.SieveWeights k (↑N : ℝ) θ δ)
    (D : Finset (Fin k → ℕ)) (hD : ∀ d, wt.lam d ≠ 0 → d ∈ D) :
    (∑ d ∈ D, ∑ e ∈ D,
        |wt.lam d| * |wt.lam e| * MaynardS2Error.windowError (↑N : ℝ) (PrimeGaps.qMod (W N) d e)) ≤
      MaynardS2Error.totalErrorContribution wt := by
  let g : (Fin k → ℕ) → (Fin k → ℕ) → ℝ := fun d e ↦ if wt.lam d * wt.lam e ≠ 0 then
      |wt.lam d| * |wt.lam e| * MaynardS2Error.windowError (↑N : ℝ) (PrimeGaps.qMod (W N) d e)
    else 0
  have hfg : ∀ d e,
      |wt.lam d| * |wt.lam e| * MaynardS2Error.windowError (↑N : ℝ)
            (PrimeGaps.qMod (W N) d e) ≤ g d e := by
    intro d e
    change |wt.lam d| * |wt.lam e| * MaynardS2Error.windowError (↑N : ℝ)
              (PrimeGaps.qMod (W N) d e) ≤ if wt.lam d * wt.lam e ≠ 0 then
            |wt.lam d| * |wt.lam e| * MaynardS2Error.windowError (↑N : ℝ) (PrimeGaps.qMod (W N) d e)
          else 0
    split_ifs with hc
    · exact le_rfl
    · rw [show |wt.lam d| * |wt.lam e| = 0 from by rw [← abs_mul, not_not.mp hc, abs_zero],
        zero_mul]
  have hgD_out : ∀ d e, wt.lam d * wt.lam e = 0 → g d e = 0 :=
    fun _ _ hz ↦ if_neg (not_not.mpr hz)
  have hgD_out_e : ∀ d e, e ∉ D → g d e = 0 := fun d e he ↦
    hgD_out d e (by rw [not_imp_comm.mp (hD e) he, mul_zero])
  have hgD_out_d : ∀ d e, d ∉ D → g d e = 0 := fun d e hd ↦
    hgD_out d e (by rw [not_imp_comm.mp (hD d) hd, zero_mul])
  have hInner : ∀ d, (∑' e, g d e) = ∑ e ∈ D, g d e :=
    fun d ↦ tsum_eq_sum fun e he ↦ hgD_out_e d e he
  have hOuter : (∑' d, ∑' e, g d e) = ∑ d ∈ D, ∑ e ∈ D, g d e := by
    rw [tsum_eq_sum (s := D) (fun d hd ↦ by
      rw [hInner d]
      exact Finset.sum_eq_zero (fun e _ ↦ hgD_out_d d e hd))]
    exact Finset.sum_congr rfl (fun d _ ↦ hInner d)
  rw [show MaynardS2Error.totalErrorContribution wt = ∑ d ∈ D, ∑ e ∈ D, g d e from hOuter]
  exact Finset.sum_le_sum fun d _ ↦ Finset.sum_le_sum fun e _ ↦ hfg d e

open scoped PrimeGaps.sieveModulus in
/-- The restricted-double-sum summand `Σ*(d, e)`, as a function of the pair `(d, e)`, gated by the
CRT eligibility clauses; it is `l d * l e / ∏ i, φ([dᵢ, eᵢ])` on eligible pairs and `0`
otherwise. -/
noncomputable def restrictedSummand {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ)
    (l : (Fin k → ℕ) → ℝ) (p : (Fin k → ℕ) × (Fin k → ℕ)) : ℝ :=
  let d := p.1
  let e := p.2
  if (d m = 1) ∧ (e m = 1) ∧ (∀ i, modulus.Coprime ((d i).lcm (e i))) ∧
      (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) ∧
      (∀ i, i ≠ m → ((↑(h m) : ℤ) - (↑(h i) : ℤ)).gcd (↑((d i).lcm (e i))) = 1)
  then l d * l e / ∏ i, (↑(Nat.totient ((d i).lcm (e i))) : ℝ)
  else 0

/-- The weight-independent kernel of the restricted CRT quadratic form. -/
noncomputable def restrictedKernel {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ)
    (p : (Fin k → ℕ) × (Fin k → ℕ)) : ℝ :=
  restrictedSummand h m modulus (fun _ ↦ 1) p

/-- The restricted CRT kernel is symmetric in its two divisor tuples. -/
theorem restrictedKernel_comm {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (modulus : ℕ) (d e : Fin k → ℕ) :
    restrictedKernel h m modulus (d, e) = restrictedKernel h m modulus (e, d) := by
  unfold restrictedKernel restrictedSummand
  simp_rw [Nat.lcm_comm]
  by_cases hd : d m = 1 <;> by_cases he : e m = 1 <;> simp [hd, he]

/-- For all large `N`, every pairwise gap `dist (h i) (h j)` with `i ≠ j` is below `⌊D₀ N⌋₊`. -/
theorem shiftGap_threshold {k : ℕ} (h : Fin k → ℕ) :
    ∃ Ngap : ℝ, 0 < Ngap ∧ ∀ N : ℕ, Ngap ≤ (↑N : ℝ) → ∀ i j : Fin k, i ≠ j →
      (h i).dist (h j) < ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊ := by
  obtain ⟨N₀, hN₀3, hN₀⟩ := PrimeGaps.exists_shift_gap_threshold h
  refine ⟨N₀, by linarith, fun N hN i j hij ↦ ?_⟩
  have hb := hN₀ (↑N : ℝ) hN i j hij
  have hle : (h i).dist (h j) + 1 ≤ ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊ :=
    Nat.le_floor (by push_cast; linarith)
  omega

/-- For `θ / 2 - δ < 1 / 2` and all large `N`, permissible tuples satisfy
`(dd i).lcm (ee i) < N + h m` in every coordinate. -/
theorem permissibleSupport_lcm_lt {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (θ δ : ℝ)
    (hexp : θ / 2 - δ < 1 / 2) :
    ∃ Nlcm : ℝ, 0 < Nlcm ∧ ∀ N : ℕ, Nlcm ≤ (↑N : ℝ) → ∀ dd ee : Fin k → ℕ,
        dd ∈ Finset.permissibleSupport k ⌊(↑N : ℝ) ^ (θ / 2 -
          δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊) →
        ee ∈ Finset.permissibleSupport k ⌊(↑N : ℝ) ^ (θ / 2 -
          δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊) →
        ∀ i : Fin k, (dd i).lcm (ee i) < N + h m := by
  refine ⟨2, by norm_num, ?_⟩
  intro N hN dd ee hdd hee i
  have hN1 : (1 : ℝ) ≤ (↑N : ℝ) := by linarith
  have hNgt1 : (1 : ℝ) < (↑N : ℝ) := by linarith
  have hNpos : 0 < N := by exact_mod_cast lt_of_lt_of_le one_pos hN1
  have hddi : ∀ j, 1 ≤ dd j := fun j ↦ Nat.one_le_iff_ne_zero.mpr
    (Finset.squarefree_of_mem_permissibleSupport hdd j).ne_zero
  have heei : ∀ j, 1 ≤ ee j := fun j ↦ Nat.one_le_iff_ne_zero.mpr
    (Finset.squarefree_of_mem_permissibleSupport hee j).ne_zero
  have hprodd : (↑(∏ j, dd j) : ℝ) ≤ (↑N : ℝ) ^ (θ / 2 - δ) :=
    le_trans (by exact_mod_cast (Finset.mem_permissibleSupport_iff.mp hdd).1)
      (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hN1) _))
  have hprode : (↑(∏ j, ee j) : ℝ) ≤ (↑N : ℝ) ^ (θ / 2 - δ) :=
    le_trans (by exact_mod_cast (Finset.mem_permissibleSupport_iff.mp hee).1)
      (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hN1) _))
  have hddle : dd i ≤ ∏ j, dd j := Finset.single_le_prod' (fun j _ ↦ hddi j) (Finset.mem_univ i)
  have heele : ee i ≤ ∏ j, ee j := Finset.single_le_prod' (fun j _ ↦ heei j) (Finset.mem_univ i)
  have hlcmleR : (↑((dd i).lcm (ee i)) : ℝ) ≤ (↑(∏ j, dd j) : ℝ) * (↑(∏ j, ee j) : ℝ) := by
    exact_mod_cast le_trans (Nat.le_of_dvd (Nat.mul_pos (hddi i) (heei i))
      (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))) (Nat.mul_le_mul hddle heele)
  have hprodenn : (0 : ℝ) ≤ (↑(∏ j, ee j) : ℝ) := by positivity
  have hrpownn : (0 : ℝ) ≤ (↑N : ℝ) ^ (θ / 2 - δ) := by positivity
  have hmul : (↑(∏ j, dd j) : ℝ) * (↑(∏ j, ee j) : ℝ) ≤
      ((↑N : ℝ) ^ (θ / 2 - δ)) * ((↑N : ℝ) ^ (θ / 2 - δ)) :=
    mul_le_mul hprodd hprode hprodenn hrpownn
  have hcombine : ((↑N : ℝ) ^ (θ / 2 - δ)) * ((↑N : ℝ) ^ (θ / 2 - δ)) = (↑N : ℝ) ^ (θ - 2 * δ) := by
    rw [← Real.rpow_add (by exact_mod_cast hNpos)]
    ring_nf
  have hrpowlt : (↑N : ℝ) ^ (θ - 2 * δ) < (↑N : ℝ) :=
    calc (↑N : ℝ) ^ (θ - 2 * δ) < (↑N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt hNgt1 (by linarith)
      _ = (↑N : ℝ) := Real.rpow_one _
  have hlcm_ltN : (↑((dd i).lcm (ee i)) : ℝ) < (↑N : ℝ) :=
    calc (↑((dd i).lcm (ee i)) : ℝ) ≤ (↑(∏ j, dd j) : ℝ) * (↑(∏ j, ee j) : ℝ) := hlcmleR
      _ ≤ ((↑N : ℝ) ^ (θ / 2 - δ)) * ((↑N : ℝ) ^ (θ / 2 - δ)) := hmul
      _ = (↑N : ℝ) ^ (θ - 2 * δ) := hcombine
      _ < (↑N : ℝ) := hrpowlt
  have hlcm_lt_nat : (dd i).lcm (ee i) < N := by exact_mod_cast hlcm_ltN
  omega

/-- `Σ*` is supported on `l.support ×ˢ l.support`: off that square one of the two weights
`l d`, `l e` vanishes, so the numerator `l d * l e` does. -/
private lemma restrictedSummand_eq_zero_of_notMem_support {k : ℕ} (h : Fin k → ℕ) (m : Fin k)
    (modulus : ℕ) (l : (Fin k → ℕ) →₀ ℝ) (p : (Fin k → ℕ) × (Fin k → ℕ))
    (hp : p ∉ l.support ×ˢ l.support) : restrictedSummand h m modulus (⇑l) p = 0 := by
  rw [Finset.mem_product, not_and_or] at hp
  unfold restrictedSummand
  simp only
  have hz : l p.1 * l p.2 = 0 := by
    rcases hp with h1 | h2
    · rw [Finsupp.notMem_support_iff.mp h1, zero_mul]
    · rw [Finsupp.notMem_support_iff.mp h2, mul_zero]
  split
  · rw [hz, zero_div]
  · rfl

/-- `Σ*` vanishes on any pair failing the CRT eligibility gate. -/
private lemma restrictedSummand_eq_zero_of_not_eligible {k : ℕ} (h : Fin k → ℕ) (m : Fin k)
    (modulus : ℕ) (l : (Fin k → ℕ) → ℝ) (d e : Fin k → ℕ)
    (hgate : ¬ ((d m = 1) ∧ (e m = 1) ∧ (∀ i, modulus.Coprime ((d i).lcm (e i))) ∧
        (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) ∧
        (∀ i, i ≠ m → ((↑(h m) : ℤ) - (↑(h i) : ℤ)).gcd (↑((d i).lcm (e i))) = 1))) :
    restrictedSummand h m modulus l (d, e) = 0 := by
  unfold restrictedSummand
  simp only
  exact if_neg hgate

/-- Multiplying `Σ*(d, e)` by `X / φ(modulus)` merges the modulus into the product of local
totients: on an eligible pair the totient is multiplicative across `modulus` and the pairwise
coprime local moduli `[dᵢ, eᵢ]`, so the result is `l d * l e * X / φ(modulus * ∏ i [dᵢ, eᵢ])`. -/
private lemma mul_restrictedSummand_eq_of_eligible {k : ℕ} (h : Fin k → ℕ) (m : Fin k)
    (modulus : ℕ) (l : (Fin k → ℕ) → ℝ) (X : ℝ) (d e : Fin k → ℕ)
    (hdm : d m = 1) (hem : e m = 1) (hWcop : ∀ i, modulus.Coprime ((d i).lcm (e i)))
    (hpaircop : ∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j)))
    (hoff : ∀ i, i ≠ m → ((↑(h m) : ℤ) - (↑(h i) : ℤ)).gcd (↑((d i).lcm (e i))) = 1) :
    X / (Nat.totient modulus : ℝ) * restrictedSummand h m modulus l (d, e) =
      l d * l e * (X / (Nat.totient (modulus * ∏ i, (d i).lcm (e i)) : ℝ)) := by
  unfold restrictedSummand
  simp only
  rw [if_pos (show _ from ⟨hdm, hem, hWcop, hpaircop, hoff⟩),
    totient_W_mul_lcm_prod modulus d e hWcop hpaircop]
  push_cast
  ring

/-- The prime-counting main term attached to one CRT-eligible divisor pair. -/
noncomputable def restrictedPrimeTerm {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (N modulus : ℕ)
    (d e : Fin k → ℕ) : ℝ :=
  if d m = 1 ∧ e m = 1 ∧ (∀ i, modulus.Coprime ((d i).lcm (e i))) ∧
      (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) ∧ (∀ i, i ≠ m →
          ((h m : ℤ) - (h i : ℤ)).gcd ((d i).lcm (e i) : ℤ) = 1)
  then (Nat.primeCountingIoc N (2 * N) : ℝ) / (PrimeGaps.qMod modulus d e).totient
  else 0

/-- A weight-independent, per-pair CRT discrepancy estimate. -/
theorem crux_sub_restrictedPrimeTerm_le {k : ℕ}
    (h : Fin k → ℕ) (m : Fin k) (hinj : Function.Injective h)
    (θ δ : ℝ) (N : ℕ) (w₀ : ZMod (PrimeGaps.sieveModulus N))
    (hw₀ : ∀ i, ((w₀.val : ℤ) + (h i : ℤ)).gcd (PrimeGaps.sieveModulus N) = 1)
    (l : (Fin k → ℕ) → ℝ)
    (hsupp : ∀ d, l d ≠ 0 → d ∈ Finset.permissibleSupport k
      ⌊(N : ℝ) ^ (θ / 2 - δ)⌋₊ (PrimeGaps.sieveModulus N))
    (hD0_large : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊)
    (hcoord_lcm_lt_prime : ∀ dd ee, l dd ≠ 0 → l ee ≠ 0 → ∀ i, (dd i).lcm (ee i) < N + h m)
    (Ccrt : ℝ) (hCcrt : 0 < Ccrt)
    (hCRT : ∀ (W : ℕ) (v0 : ℤ) (d e : Fin k → ℕ) (q Narg : ℕ),
      1 ≤ W → (∀ i, 1 ≤ d i) → (∀ i, 1 ≤ e i) → d m = 1 → e m = 1 →
      (∀ i, W.Coprime ((d i).lcm (e i))) →
      (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) →
      q = W * ∏ i, (d i).lcm (e i) →
      (∀ i, (v0 + (h i : ℤ)).gcd W = 1) →
      (∀ i, i ≠ m → ((h m : ℤ) - (h i : ℤ)).gcd ((d i).lcm (e i) : ℤ) = 1) →
      |PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m W v0 d e Narg -
          (Nat.primeCountingIoc Narg (2 * Narg) : ℝ) / q.totient| ≤
        Ccrt * Nat.primeCountingIocError Narg (2 * Narg) q)
    (d e : Fin k → ℕ) (hd : l d ≠ 0) (he : l e ≠ 0) :
    |PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m (PrimeGaps.sieveModulus N) (w₀.val : ℤ) d e N -
            restrictedPrimeTerm h m N (PrimeGaps.sieveModulus N) d e| ≤
      Ccrt * MaynardS2Error.windowError (N : ℝ)
          (PrimeGaps.qMod (PrimeGaps.sieveModulus N) d e) := by
  let elig : Prop :=
    d m = 1 ∧ e m = 1 ∧ (∀ i, (PrimeGaps.sieveModulus N).Coprime ((d i).lcm (e i))) ∧
      (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) ∧ (∀ i, i ≠ m →
        ((h m : ℤ) - (h i : ℤ)).gcd ((d i).lcm (e i) : ℤ) = 1)
  let q := PrimeGaps.qMod (PrimeGaps.sieveModulus N) d e
  have hqeq : q = PrimeGaps.sieveModulus N * ∏ i, (d i).lcm (e i) := rfl
  have hdsupp := Finset.mem_permissibleSupport_iff'.mp (hsupp d hd)
  have hesupp := Finset.mem_permissibleSupport_iff'.mp (hsupp e he)
  have hdpos : ∀ i, 1 ≤ d i := fun i ↦ Nat.one_le_iff_ne_zero.mpr (hdsupp.1 i)
  have hepos : ∀ i, 1 ≤ e i := fun i ↦ Nat.one_le_iff_ne_zero.mpr (hesupp.1 i)
  by_cases helig : elig
  · obtain ⟨hdm, hem, hWcop, hpaircop, hoff⟩ := helig
    have hmain : restrictedPrimeTerm h m N (PrimeGaps.sieveModulus N) d e =
          (Nat.primeCountingIoc N (2 * N) : ℝ) / q.totient := by
      unfold restrictedPrimeTerm
      rw [if_pos ⟨hdm, hem, hWcop, hpaircop, hoff⟩]
    rw [hmain, ← primeCountingIocError_eq_windowError]
    exact hCRT (PrimeGaps.sieveModulus N) (w₀.val : ℤ) d e q N
      PrimeGaps.W_pos hdpos hepos hdm hem hWcop hpaircop hqeq hw₀ hoff
  · have hzero : PrimeGaps.sieveCount (fun i ↦ (h i : ℤ)) m
        (PrimeGaps.sieveModulus N) (w₀.val : ℤ) d e N = 0 :=
      crux_S_vanish_of_not_restricted h m hinj θ δ N w₀ hw₀ l hsupp
        hD0_large hcoord_lcm_lt_prime d e hd he helig
    have hmain : restrictedPrimeTerm h m N (PrimeGaps.sieveModulus N) d e = 0 := by
      unfold restrictedPrimeTerm
      rw [if_neg helig]
    rw [hzero, hmain, sub_zero, abs_zero]
    exact mul_nonneg hCcrt.le (MaynardS2Error.windowError_nonneg _ _)

open scoped PrimeGaps.sieveModulus in
/-- Given a CRT estimate with constant `Ccrt` for the individual counts `S`,
`|S₂m - (X_N / φ(W N)) * ∑' p, restrictedSummand h m (W N) l p| ≤
Ccrt * totalErrorContribution wt`, where `X_N = Nat.primeCountingIoc N (2N)`. -/
theorem S2m_decomp_bound {k : ℕ} (h : Fin k → ℕ) (m : Fin k) (hinj : Function.Injective h)
    (θ δ : ℝ) (N : ℕ) (wt₀ : ZMod (W N))
    (hw₀ : ∀ i, ((↑wt₀.val : ℤ) + (↑(h i) : ℤ)).gcd (↑(W N)) = 1)
    (l : (Fin k → ℕ) →₀ ℝ)
    (hsupp : l.HasPermissibleSupport ⌊(↑N : ℝ) ^ (θ / 2 - δ)⌋₊ (primorial ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊))
    (wt : MaynardS2Error.SieveWeights k (↑N : ℝ) θ δ) (hw : wt = ⟨l, hsupp⟩)
    (Ccrt : ℝ) (hCcrt : 0 < Ccrt)
    (hCRT : ∀ («W» : ℕ) (v0 : ℤ) (d e : Fin k → ℕ) (q Narg : ℕ),
        1 ≤ «W» → (∀ i, 1 ≤ d i) → (∀ i, 1 ≤ e i) → d m = 1 → e m = 1 →
        (∀ i, «W».Coprime ((d i).lcm (e i))) →
        (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) →
        q = «W» * ∏ i, (d i).lcm (e i) →
        (∀ i, (v0 + (↑(h i) : ℤ)).gcd ↑«W» = 1) →
        (∀ i, i ≠ m → ((↑(h m) : ℤ) - (↑(h i) : ℤ)).gcd ↑((d i).lcm (e i)) = 1) →
        |PrimeGaps.sieveCount (fun i ↦ (↑(h i) : ℤ)) m «W» v0 d e Narg -
            ↑(Nat.primeCountingIoc Narg (2 * Narg)) / ↑q.totient| ≤
          Ccrt * Nat.primeCountingIocError Narg (2 * Narg) q)
    (hD0_large : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊)
    (hcoord_lcm_lt_prime : ∀ dd ee : Fin k → ℕ, l dd ≠ 0 → l ee ≠ 0 →
        ∀ i, (dd i).lcm (ee i) < N + h m) :
    |PrimeGaps.S₂m h l N wt₀ m - (↑(Nat.primeCountingIoc N (2 * N)) / ↑(Nat.totient (W N))) *
            ∑' p : (Fin k → ℕ) × (Fin k → ℕ), restrictedSummand h m (W N) l p| ≤
      Ccrt * MaynardS2Error.totalErrorContribution wt := by
  classical
  set X : ℕ := Nat.primeCountingIoc N (2 * N) with hX
  set elig : (Fin k → ℕ) → (Fin k → ℕ) → Prop := fun d e ↦
      (d m = 1) ∧ (e m = 1) ∧ (∀ i, (W N).Coprime ((d i).lcm (e i))) ∧
        (∀ i j, i ≠ j → ((d i).lcm (e i)).Coprime ((d j).lcm (e j))) ∧
        (∀ i, i ≠ m → ((↑(h m) : ℤ) - (↑(h i) : ℤ)).gcd (↑((d i).lcm (e i))) = 1)
      with helig
  set q : (Fin k → ℕ) → (Fin k → ℕ) → ℕ := fun d e ↦ W N * ∏ i, (d i).lcm (e i) with hq
  set f : (Fin k → ℕ) → (Fin k → ℕ) → ℝ := fun d e ↦ l d * l e *
        PrimeGaps.sieveCount (fun i ↦ (↑(h i) : ℤ)) m (W N) (↑wt₀.val : ℤ) d e N with hf
  set restrictedTerm : (Fin k → ℕ) → (Fin k → ℕ) → ℝ := fun d e ↦
      if elig d e then (↑X / ↑(q d e).totient : ℝ) else 0 with hrt
  set g : (Fin k → ℕ) → (Fin k → ℕ) → ℝ := fun d e ↦ l d * l e * restrictedTerm d e with hg
  have hcm : ∀ d e : Fin k → ℕ, PrimeGaps.qMod (W N) d e = q d e := fun _ _ ↦ rfl
  have hS2m : PrimeGaps.S₂m h l N wt₀ m = ∑ d ∈ l.support, ∑ e ∈ l.support, f d e := by
    rw [S2m_expand_to_crux_S h m N wt₀ (⇑l) l rfl]
  have hMain : (↑X / ↑(Nat.totient (W N))) *
          ∑' p : (Fin k → ℕ) × (Fin k → ℕ), restrictedSummand h m (W N) l p =
        ∑ d ∈ l.support, ∑ e ∈ l.support, g d e := by
    rw [tsum_eq_sum (fun p hp ↦ restrictedSummand_eq_zero_of_notMem_support h m (W N) l p hp)]
    rw [Finset.mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    refine Finset.sum_congr rfl fun e he ↦ ?_
    change (↑X / ↑(Nat.totient (W N))) * restrictedSummand h m (W N) l (d, e) = g d e
    rw [hg]
    change (↑X / ↑(Nat.totient (W N))) * restrictedSummand h m (W N) l (d, e) =
        l d * l e * restrictedTerm d e
    by_cases helg : elig d e
    · obtain ⟨hdm, hem, hWcop, hpaircop, hoff⟩ := helg
      rw [show restrictedTerm d e = (↑X / ↑(q d e).totient : ℝ) from by
        rw [hrt]; exact if_pos ⟨hdm, hem, hWcop, hpaircop, hoff⟩]
      exact mul_restrictedSummand_eq_of_eligible h m (W N) (⇑l) (X : ℝ) d e hdm hem hWcop
        hpaircop hoff
    · rw [show restrictedTerm d e = 0 from by rw [hrt]; exact if_neg helg,
        restrictedSummand_eq_zero_of_not_eligible h m (W N) (⇑l) d e helg, mul_zero, mul_zero]
  -- Per-pair CRT discrepancy, from `crux_sub_restrictedPrimeTerm_le` above with
  -- `restrictedTerm = restrictedPrimeTerm h m N (W N)`.
  have hpair : ∀ d ∈ l.support, ∀ e ∈ l.support,
      |f d e - g d e| ≤ |l d| * |l e| * (Ccrt * MaynardS2Error.windowError (↑N : ℝ)
                    (PrimeGaps.qMod (W N) d e)) := by
    intro d hd e he
    have hld : l d ≠ 0 := Finsupp.mem_support_iff.mp hd
    have hle : l e ≠ 0 := Finsupp.mem_support_iff.mp he
    have hfg_eq : f d e - g d e = l d * l e * (PrimeGaps.sieveCount (fun i ↦ (↑(h i) : ℤ)) m
                 (W N) (↑wt₀.val : ℤ) d e N - restrictedTerm d e) := by
      rw [hf, hg]; ring
    rw [hfg_eq, abs_mul, abs_mul]
    have hrtP : restrictedTerm d e = restrictedPrimeTerm h m N (W N) d e := by
      unfold restrictedPrimeTerm
      simp only [hrt, helig, hX, hcm d e]
    have hcore :
        |PrimeGaps.sieveCount (fun i ↦ (↑(h i) : ℤ)) m
             (W N) (↑wt₀.val : ℤ) d e N - restrictedTerm d e| ≤
          Ccrt * MaynardS2Error.windowError (↑N : ℝ)
              (PrimeGaps.qMod (W N) d e) := by
      rw [hrtP]
      exact crux_sub_restrictedPrimeTerm_le h m hinj θ δ N wt₀ hw₀ (⇑l)
        (fun d hd ↦ hsupp (Finsupp.mem_support_iff.mpr hd)) hD0_large hcoord_lcm_lt_prime
        Ccrt hCcrt hCRT d e hld hle
    exact mul_le_mul_of_nonneg_left hcore (by positivity)
  rw [hS2m, hMain, ← Finset.sum_sub_distrib]
  have hstep2 : (∑ d ∈ l.support, ∑ e ∈ l.support, |f d e - g d e|) ≤ Ccrt *
            ∑ d ∈ l.support, ∑ e ∈ l.support,
                |l d| * |l e| * MaynardS2Error.windowError (↑N : ℝ)
                      (PrimeGaps.qMod (W N) d e) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun d hd ↦ ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun e he ↦ ?_)
    calc |f d e - g d e| ≤ |l d| * |l e| * (Ccrt * MaynardS2Error.windowError (↑N : ℝ)
                      (PrimeGaps.qMod (W N) d e)) := hpair d hd e he
      _ = Ccrt * (|l d| * |l e| * MaynardS2Error.windowError (↑N : ℝ)
                  (PrimeGaps.qMod (W N) d e)) := by ring
  have hL6 : (∑ d ∈ l.support, ∑ e ∈ l.support,
          |l d| * |l e| * MaynardS2Error.windowError (↑N : ℝ) (PrimeGaps.qMod (W N) d e)) ≤
        MaynardS2Error.totalErrorContribution wt := by
    have hlam : wt.lam = l := by rw [hw]
    have hh := finite_double_sum_le_totalErrorContribution N θ δ wt l.support
      fun d hd ↦ Finsupp.mem_support_iff.mpr (hlam ▸ hd)
    rwa [hlam] at hh
  calc |∑ d ∈ l.support, (∑ e ∈ l.support, f d e - ∑ e ∈ l.support, g d e)|
      ≤ ∑ d ∈ l.support, |∑ e ∈ l.support, f d e - ∑ e ∈ l.support, g d e| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ l.support, |∑ e ∈ l.support, (f d e - g d e)| := by
        simp_rw [Finset.sum_sub_distrib]
    _ ≤ ∑ d ∈ l.support, ∑ e ∈ l.support, |f d e - g d e| :=
        Finset.sum_le_sum fun d _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ Ccrt * ∑ d ∈ l.support, ∑ e ∈ l.support,
              |l d| * |l e| * MaynardS2Error.windowError (↑N : ℝ)
                    (PrimeGaps.qMod (W N) d e) := hstep2
    _ ≤ Ccrt * MaynardS2Error.totalErrorContribution wt :=
        mul_le_mul_of_nonneg_left hL6 hCcrt.le

open scoped PrimeGaps.sieveModulus in
/-- For every `A > 0` there are constants
`C, N₀ > 0` such that `PrimeGaps.S₂m h l N wt₀ m` differs from the CRT main term `(X_N /
  φ(W N)) · ∑' Σ*`
by at most `C · maxRealAbs (lToY l)² · N / (log N)^A`, for all large `N`, compatible residues
`wt₀`, and sieve-supported weights `l = ⇑l`. -/
@[pg_tag "bg246" "lem_S2m_main_CRT"]
theorem S₂m_CRT_main_term_BV_error
    {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (m : Fin k)
    (hinj : Function.Injective h)
    (θ δ : ℝ) (hδ : 0 < δ) (hδθ : δ < θ / 2) (hθ : θ < 1 / 2)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1) :
    ∀ A : ℝ, 0 < A → ∃ C N₀ : ℝ, 0 < C ∧ 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ (↑N : ℝ) → ∀ wt₀ : ZMod (W N),
            (∀ i, ((↑wt₀.val : ℤ) + (↑(h i) : ℤ)).gcd (↑(W N)) = 1) → ∀ l : (Fin k → ℕ) →₀ ℝ,
                l.HasPermissibleSupport ⌊(↑N : ℝ) ^ (θ / 2 - δ)⌋₊
                  (primorial ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊) →
                  |PrimeGaps.S₂m h l N wt₀ m -
                      (↑(Nat.primeCountingIoc N (2 * N)) / ↑(Nat.totient (W N))) *
                          ∑' p : (Fin k → ℕ) × (Fin k → ℕ), restrictedSummand h m (W N) l p| ≤
                    C * (Finsupp.maxRealAbs (PrimeGaps.lToY l)) ^ 2 *
                        (↑N : ℝ) / (Real.log ↑N) ^ A := by
  intro A hA
  obtain ⟨C₂, N₂, hC₂, hMain⟩ :=
    MaynardS2Error.exists_totalErrorContribution_le k hk A hA θ δ hδ hδθ hθ hBV
  obtain ⟨C₁, hC₁, hCRT⟩ := PrimeGaps.lem_S2m_CRT (fun i ↦ (↑(h i) : ℤ)) m
  obtain ⟨Ngap, hNgap_pos, hNgap⟩ := shiftGap_threshold h
  obtain ⟨Nlcm, hNlcm_pos, hNlcm⟩ :=
    permissibleSupport_lcm_lt h m θ δ (by linarith [hδ, hθ])
  refine ⟨C₁ * C₂ + 1, max (max N₂ 1) (max Ngap Nlcm),
    by positivity, by positivity, ?_⟩
  intro N hN wt₀ hw₀ l hsupp
  set wt : MaynardS2Error.SieveWeights k (↑N : ℝ) θ δ := ⟨l, hsupp⟩ with hw
  have hNlb : N₂ ≤ (↑N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNgap_le : Ngap ≤ (↑N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNlcm_le : Nlcm ≤ (↑N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hErr : MaynardS2Error.totalErrorContribution wt ≤
      C₂ * Finsupp.maxRealAbs (PrimeGaps.lToY wt.lam) ^ 2 * (↑N : ℝ) / Real.log (↑N) ^ A :=
    hMain (↑N : ℝ) hNlb wt
  have hD0_large : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (↑N : ℝ)⌋₊ :=
    hNgap N hNgap_le
  have hcoord_lcm_lt_prime : ∀ dd ee : Fin k → ℕ, l dd ≠ 0 → l ee ≠ 0 →
      ∀ i, (dd i).lcm (ee i) < N + h m := fun dd ee hdd hee i ↦
    hNlcm N hNlcm_le dd ee (hsupp (Finsupp.mem_support_iff.mpr hdd))
      (hsupp (Finsupp.mem_support_iff.mpr hee)) i
  have hDecomp :
      |PrimeGaps.S₂m h l N wt₀ m - (↑(Nat.primeCountingIoc N (2 * N)) / ↑(Nat.totient (W N))) *
              ∑' p : (Fin k → ℕ) × (Fin k → ℕ), restrictedSummand h m (W N) l p| ≤
        C₁ * MaynardS2Error.totalErrorContribution wt :=
    S2m_decomp_bound h m hinj θ δ N wt₀ hw₀ l hsupp wt hw C₁ hC₁ hCRT
      hD0_large hcoord_lcm_lt_prime
  have hNpos : (1 : ℝ) ≤ (↑N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hLogNonneg : 0 ≤ Real.log (↑N) := Real.log_nonneg hNpos
  have hLogPowNonneg : 0 ≤ Real.log (↑N) ^ A := Real.rpow_nonneg hLogNonneg A
  have hNnonneg : (0 : ℝ) ≤ (↑N : ℝ) := le_trans zero_le_one hNpos
  calc |PrimeGaps.S₂m h l N wt₀ m - (↑(Nat.primeCountingIoc N (2 * N)) / ↑(Nat.totient (W N))) *
              ∑' p : (Fin k → ℕ) × (Fin k → ℕ), restrictedSummand h m (W N) l p| ≤
        C₁ * MaynardS2Error.totalErrorContribution wt := hDecomp
    _ ≤ C₁ * (C₂ * Finsupp.maxRealAbs (PrimeGaps.lToY wt.lam) ^ 2 * (↑N : ℝ) / Real.log (↑N) ^ A) :=
          mul_le_mul_of_nonneg_left hErr (by positivity)
    _ ≤ (C₁ * C₂ + 1) * (Finsupp.maxRealAbs (PrimeGaps.lToY l)) ^ 2 *
          (↑N : ℝ) / Real.log (↑N) ^ A := by
      rw [hw]
      have hbase : 0 ≤ (Finsupp.maxRealAbs (PrimeGaps.lToY l)) ^ 2 * (↑N : ℝ) / Real.log (↑N) ^ A :=
        div_nonneg (mul_nonneg (sq_nonneg _) hNnonneg) hLogPowNonneg
      calc
        C₁ * (C₂ * Finsupp.maxRealAbs (PrimeGaps.lToY l) ^ 2 * ↑N / Real.log (↑N) ^ A) =
            (C₁ * C₂) * (Finsupp.maxRealAbs (PrimeGaps.lToY l) ^ 2 * ↑N /
              Real.log (↑N) ^ A) := by ring
        _ ≤ (C₁ * C₂ + 1) * (Finsupp.maxRealAbs (PrimeGaps.lToY l) ^ 2 * ↑N /
              Real.log (↑N) ^ A) := mul_le_mul_of_nonneg_right (by linarith) hbase
        _ = (C₁ * C₂ + 1) * Finsupp.maxRealAbs (PrimeGaps.lToY l) ^ 2 * ↑N /
              Real.log (↑N) ^ A := by ring

end PrimeGaps
