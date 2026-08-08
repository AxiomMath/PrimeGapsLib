/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.Error.TauGrowth

/-!
# The window error

Bounds for the prime-counting discrepancy over a dyadic window in arithmetic
progressions.

## Main results

* `windowDisc_pointwise_bound`
* `windowDisc_le_bvError`
* `windowDisc_sum_le_hLoD`
-/

@[expose] public section

open Real
open PrimeGaps

open scoped Finset

namespace MaynardS2Error

open ArithmeticFunction
open PrimeGaps (primeIndicator primeIndicator_apply)

/-- A residue class mod `q` meets `Finset.Ico A B` in at most `B / q + 1` points. -/
lemma card_Ico_filter_mod_le (A B q r : ℕ) :
    (#{n ∈ (Finset.Ico A B) | n % q = r % q} : ℝ) ≤ (B : ℝ) / (q : ℝ) + 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [Nat.mod_zero, Nat.cast_zero, div_zero, zero_add, Finset.filter_eq']
    split_ifs <;> simp
  have hcard : #{n ∈ (Finset.Ico A B) | n % q = r % q} ≤ B / q + 1 := by
    have hsub : {n ∈ (Finset.Ico A B) | n % q = r % q} ⊆
        {n ∈ (Finset.range B) | n ≡ r [MOD q]} := fun n hn ↦ by
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn.1.2, hn.2⟩
    have hc := Nat.count_modEq_card B hq r
    rw [Nat.count_eq_card_filter_range] at hc
    refine (Finset.card_le_card hsub).trans ?_
    rw [hc]
    split_ifs <;> omega
  refine le_trans (by exact_mod_cast hcard : _ ≤ ((B / q : ℕ) : ℝ) + 1) ?_
  gcongr
  exact Nat.cast_div_le

/-- `∑ n ∈ T, primeIndicator n = (T.filter Nat.Prime).card`. -/
theorem sum_primeIndicator_eq (T : Finset ℕ) :
    (∑ n ∈ T, primeIndicator n) = (#(T.filter Nat.Prime) : ℝ) := by
  simp [primeIndicator_apply, Finset.sum_boole]

/-- Inside a finite set, the primes lying in the class of `u` mod `q` are exactly the primes
congruent to a natural representative `a` of `u`. -/
private lemma filter_prime_class_eq (T : Finset ℕ) (q a : ℕ) (u : ZMod q)
    (hua : (a : ZMod q) = u) :
    T.filter (fun n : ℕ ↦ n.Prime ∧ (n : ZMod q) = u) =
      (T.filter (fun n ↦ n % q = a % q)).filter Nat.Prime := by
  ext n
  simp only [Finset.mem_filter]
  rw [← hua, ZMod.natCast_eq_natCast_iff']
  tauto

/-- The trivial pointwise bound `windowDisc N q ≤ Cp * N / φ q`, valid for `1 ≤ q ≤ N`. -/
lemma windowDisc_pointwise_bound : ∃ Cp : ℝ, 0 < Cp ∧ ∀ (N : ℝ), (1 : ℝ) ≤ N → ∀ (q : ℕ), 1 ≤ q →
      (q : ℝ) ≤ N → windowDisc N q ≤ Cp * N / (Nat.totient q : ℝ) := by
  have hsumnn : ∀ S : Finset ℕ, 0 ≤ ∑ n ∈ S, primeIndicator n := fun S ↦ by
    rw [sum_primeIndicator_eq]; positivity
  have hsumle : ∀ S : Finset ℕ, (∑ n ∈ S, primeIndicator n) ≤ (#S : ℝ) := fun S ↦ by
    rw [sum_primeIndicator_eq]; exact_mod_cast Finset.card_filter_le S Nat.Prime
  refine ⟨10, by norm_num, fun N hN1 q hq1 hqN ↦ ?_⟩
  have hq0 : 0 < q := hq1
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hφR : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hφleq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hN0 : (0 : ℝ) < N := one_pos.trans_le hN1
  set win := Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊ with hwin
  set Y := (∑ n ∈ win, primeIndicator n)
  have hYnn : 0 ≤ Y := hsumnn win
  have hYle3 : Y ≤ 3 * N := by
    refine (hsumle win).trans ?_
    rw [hwin, Nat.card_Ioc]
    have h1 : ((⌊2 * N⌋₊ - ⌊N⌋₊ : ℕ) : ℝ) ≤ (⌊2 * N⌋₊ : ℝ) := by exact_mod_cast Nat.sub_le _ _
    have h2 : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by positivity)
    linarith
  unfold windowDisc windowError Nat.primeCountingIocError
  rw [add_sub_cancel_left]
  refine ciSup_le fun u ↦ ?_
  letI : NeZero q := ⟨by omega⟩
  let a : ℕ := (u : ZMod q).val
  have hua : (a : ZMod q) = (u : ZMod q) := ZMod.natCast_zmod_val _
  have hAPset : (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
      (fun n : ℕ ↦ n.Prime ∧ (n : ZMod q) = (u : ZMod q)) =
      ((win.filter (fun n ↦ n % q = a % q)).filter Nat.Prime) :=
    filter_prime_class_eq _ q a _ hua
  unfold ZMod.primeCountingIoc Nat.primeCountingIoc
  rw [hAPset, ← sum_primeIndicator_eq, ← sum_primeIndicator_eq]
  set Xa := (∑ n ∈ win.filter (fun n ↦ n % q = a % q), primeIndicator n)
  have hXann : 0 ≤ Xa := hsumnn _
  have hXa4 : Xa ≤ 4 * N / (q.totient : ℝ) := by
    have hcard : Xa ≤ (2 * N + 1) / (q : ℝ) + 1 := by
      refine (hsumle (win.filter (fun n ↦ n % q = a % q))).trans ?_
      rw [hwin, show Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊ = Finset.Ico (⌊N⌋₊ + 1) (⌊2 * N⌋₊ + 1) from by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega]
      refine (card_Ico_filter_mod_le (⌊N⌋₊ + 1) (⌊2 * N⌋₊ + 1) q a).trans ?_
      gcongr
      have hf : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by positivity)
      push_cast
      linarith
    have h1 : (2 * N + 1) / (q : ℝ) ≤ 3 * N / (q.totient : ℝ) := by
      rw [div_le_div_iff₀ hqR hφR]
      nlinarith [hφleq, hN1, hφR, hqR]
    have h2 : (1 : ℝ) ≤ N / (q.totient : ℝ) := by rw [le_div_iff₀ hφR]; linarith
    calc Xa ≤ (2 * N + 1) / (q : ℝ) + 1 := hcard
      _ ≤ 3 * N / (q.totient : ℝ) + N / (q.totient : ℝ) := by linarith
      _ = 4 * N / (q.totient : ℝ) := by ring
  have hsplit : 4 * N / (q.totient : ℝ) + 3 * N / (q.totient : ℝ) ≤ 10 * N / (q.totient : ℝ) := by
    rw [← add_div]; gcongr; linarith
  have hYdiv : Y / (q.totient : ℝ) ≤ 3 * N / (q.totient : ℝ) := by gcongr
  have hYdivnn : 0 ≤ Y / (q.totient : ℝ) := div_nonneg hYnn hφR.le
  rw [abs_le]
  constructor <;> linarith

/-- The level-of-distribution hypothesis directly bounds the canonical cumulative error. -/
lemma levelOfDistribution_bvError {θ : ℝ} (hLoD : Nat.HasLevelOfDistribution Set.univ θ 1)
    (A : ℝ) (hA : 1 ≤ A) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (∑ q ∈ {q ∈ (Finset.range (⌊x ^ θ⌋₊ + 1)) | 1 ≤ q}, PrimeGaps.bvError x q) ≤
        C * x / (Real.log x) ^ A := by
  obtain ⟨c, -, hbound⟩ := hLoD A hA
  refine ⟨c, 3, fun x hx ↦ ?_⟩
  have hidx : {q ∈ (Finset.range (⌊x ^ θ⌋₊ + 1)) | 1 ≤ q} =
      {q ∈ (Finset.Icc (1 : ℕ) ⌊x ^ θ⌋₊) | Nat.gcd q 1 = 1} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Nat.gcd_one_right,
      Nat.lt_succ_iff, and_true]
    omega
  rw [hidx]
  simpa only [PrimeGaps.bvError_eq_cumulative, Real.primeCountingZModWithin_univ,
    Real.primeCountingWithin_univ] using hbound x hx

/-- Splitting `Finset.Ico 0 M` at `m ≤ M` splits the filtered cardinality additively. -/
theorem filter_Ico_split (P : ℕ → Prop) [DecidablePred P] (m M : ℕ) (h : m ≤ M) :
    #((Finset.Ico 0 M).filter P) =
      #((Finset.Ico 0 m).filter P) + #((Finset.Ico m M).filter P) := by
  rw [← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le m) h, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter
      (Finset.Ico_disjoint_Ico_consecutive 0 m M))]

/-- The primes of the window `Ioc ⌊N⌋₊ ⌊2N⌋₊` in the class `a` mod `q` number
`π(2N; q, a) - π(N; q, a)`. -/
theorem window_ap_eq (N : ℝ) (hN1 : (1 : ℝ) ≤ N) (q a : ℕ) :
    (∑ n ∈ {n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊) | n % q = a % q}, primeIndicator n) =
      (Real.primeCountingZMod (2 * N) q (a : ZMod q) : ℝ) -
        (Real.primeCountingZMod N q (a : ZMod q) : ℝ) := by
  have hfloormono : ⌊N⌋₊ ≤ ⌊2 * N⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit := filter_Ico_split (fun n ↦ n.Prime ∧ n % q = a % q)
    (⌊N⌋₊ + 1) (⌊2 * N⌋₊ + 1) (by omega)
  have hset : Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊ = Finset.Ico (⌊N⌋₊ + 1) (⌊2 * N⌋₊ + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [sum_primeIndicator_eq, Finset.filter_comm, Finset.filter_filter, primesInAP_eq_filter,
    primesInAP_eq_filter, Finset.range_eq_Ico, Finset.range_eq_Ico, hset, hsplit]
  push_cast
  ring

/-- `∑ n ∈ Ioc ⌊N⌋₊ ⌊2N⌋₊, primeIndicator n = π(2N) - π(N)`. -/
theorem window_total_eq (N : ℝ) (hN1 : (1 : ℝ) ≤ N) :
    (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, primeIndicator n) =
      (pi (2 * N) : ℝ) - (pi N : ℝ) := by
  rw [sum_primeIndicator_eq]
  exact Nat.cast_primeCountingIoc (Nat.floor_le_floor (by linarith))

/-- `windowDisc N q ≤ bvError (2 * N) q + bvError N q`, splitting the window discrepancy into the
two cumulative discrepancies at its endpoints. -/
lemma windowDisc_le_bvError (N : ℝ) (hN1 : (1 : ℝ) ≤ N) (q : ℕ) (hq1 : 1 ≤ q) :
    windowDisc N q ≤ PrimeGaps.bvError (2 * N) q + PrimeGaps.bvError N q := by
  unfold windowDisc windowError Nat.primeCountingIocError
  rw [add_sub_cancel_left]
  refine ciSup_le fun u ↦ ?_
  letI : NeZero q := ⟨by omega⟩
  let a : ℕ := (u : ZMod q).val
  have hua : (a : ZMod q) = (u : ZMod q) := ZMod.natCast_zmod_val _
  have hAPset : (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
      (fun n : ℕ ↦ n.Prime ∧ (n : ZMod q) = (u : ZMod q)) =
      (((Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n ↦ n % q = a % q)).filter Nat.Prime) :=
    filter_prime_class_eq _ q a _ hua
  unfold ZMod.primeCountingIoc Nat.primeCountingIoc
  have key : ∀ x : ℝ, |(Real.primeCountingZMod x q (a : ZMod q) : ℝ) -
      (pi x : ℝ) / (q.totient : ℝ)| ≤ PrimeGaps.bvError x q := fun x ↦ by
    simpa [hua] using PrimeGaps.bvError_term_le x q u
  rw [hAPset, ← sum_primeIndicator_eq, ← sum_primeIndicator_eq, window_ap_eq N hN1 q a,
    window_total_eq N hN1, sub_div, sub_sub_sub_comm]
  exact (abs_sub _ _).trans (add_le_add (key (2 * N)) (key N))

/-- Under a level of distribution `θ`, `∑_{1 ≤ q ≤ N ^ θ} windowDisc N q ≤ Cd * N / Real.log N ^ A`
for all large `N`. -/
lemma windowDisc_sum_le_hLoD (θ : ℝ) (hθ0 : 0 < θ)
    (hLoD : Nat.HasLevelOfDistribution Set.univ θ 1) (A : ℝ) (hA : 1 ≤ A) :
    ∃ (Cd N₀ : ℝ), 0 < Cd ∧ ∀ (N : ℝ), N₀ ≤ N →
      (∑ q ∈ {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q},
        windowDisc N q) ≤ Cd * N / (Real.log N) ^ A := by
  obtain ⟨C, x₀, hbound⟩ := levelOfDistribution_bvError hLoD A hA
  have h1e : (1 : ℝ) < rexp 1 := Real.one_lt_exp_iff.2 one_pos
  have hCnn : 0 ≤ C := by
    set x := max x₀ (rexp 1) + 1 with hxdef
    have hxe : rexp 1 ≤ x := (le_max_right _ _).trans (by rw [hxdef]; linarith)
    have hxlog : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
    have hle : 0 ≤ C * x / (Real.log x) ^ A :=
      (Finset.sum_nonneg fun q _ ↦ PrimeGaps.bvError_nonneg x q).trans
        (hbound x ((le_max_left _ _).trans (by rw [hxdef]; linarith)))
    have hpos : (0 : ℝ) < x / (Real.log x) ^ A := by positivity
    nlinarith [hle, hpos, mul_div_assoc C x ((Real.log x) ^ A)]
  refine ⟨2 * C + C + 1, max (max x₀ (x₀ / 2)) (max 3 (rexp 1)), by positivity, fun N hN ↦ ?_⟩
  have hNe : rexp 1 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := one_pos.trans_le hN1
  have hNx0 : x₀ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN2x0 : x₀ ≤ 2 * N := by
    have : x₀ / 2 ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
    linarith
  have hlog0 : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  set Q := {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q} with hQ
  have hpoint : ∀ q ∈ Q, windowDisc N q ≤ PrimeGaps.bvError (2 * N) q + PrimeGaps.bvError N q :=
    fun q hq ↦ by
      rw [hQ, Finset.mem_filter] at hq
      exact windowDisc_le_bvError N hN1 q hq.2
  have hEN : (∑ q ∈ Q, PrimeGaps.bvError N q) ≤ C * N / (Real.log N) ^ A := by
    rw [hQ]; exact hbound N hNx0
  set Q₂ := {q ∈ (Finset.range (⌊(2 * N) ^ θ⌋₊ + 1)) | 1 ≤ q} with hQ2
  have hsub : Q ⊆ Q₂ := fun q hq ↦ by
    rw [hQ, Finset.mem_filter, Finset.mem_range] at hq
    rw [hQ2, Finset.mem_filter, Finset.mem_range]
    refine ⟨hq.1.trans_le ?_, hq.2⟩
    have : ⌊N ^ θ⌋₊ ≤ ⌊(2 * N) ^ θ⌋₊ :=
      Nat.floor_le_floor (Real.rpow_le_rpow hN0.le (by linarith) hθ0.le)
    omega
  have hextend : (∑ q ∈ Q, PrimeGaps.bvError (2 * N) q) ≤ (∑ q ∈ Q₂, PrimeGaps.bvError (2 * N) q) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ ↦ PrimeGaps.bvError_nonneg (2 * N) q)
  have hE2N : (∑ q ∈ Q₂, PrimeGaps.bvError (2 * N) q) ≤ C * (2 * N) / (Real.log (2 * N)) ^ A := by
    rw [hQ2]; exact hbound (2 * N) hN2x0
  have hden2 : (Real.log N) ^ A ≤ (Real.log (2 * N)) ^ A :=
    Real.rpow_le_rpow hlog0.le (Real.log_le_log hN0 (by linarith)) (by linarith)
  have hE2N' : (∑ q ∈ Q₂, PrimeGaps.bvError (2 * N) q) ≤ C * (2 * N) / (Real.log N) ^ A :=
    hE2N.trans (by gcongr)
  have hE2Nfinal : (∑ q ∈ Q, PrimeGaps.bvError (2 * N) q) ≤ 2 * C * N / (Real.log N) ^ A :=
    hextend.trans (hE2N'.trans_eq (by ring))
  calc (∑ q ∈ Q, windowDisc N q)
      ≤ ∑ q ∈ Q, (PrimeGaps.bvError (2 * N) q + PrimeGaps.bvError N q) := Finset.sum_le_sum hpoint
    _ = (∑ q ∈ Q, PrimeGaps.bvError (2 * N) q) + (∑ q ∈ Q, PrimeGaps.bvError N q) :=
        Finset.sum_add_distrib
    _ ≤ 2 * C * N / (Real.log N) ^ A + C * N / (Real.log N) ^ A := add_le_add hE2Nfinal hEN
    _ ≤ (2 * C + C + 1) * N / (Real.log N) ^ A := by rw [← add_div]; gcongr; linarith

end MaynardS2Error
