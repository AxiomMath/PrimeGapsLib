/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.HAsymptotic.ConvForm

/-!
# Summability and the singular series

Summability of the `bTilde` series, its Euler product, and uniform bounds on the
singular series.

## Main results

* `slem_singularSeries_bTilde_bridge`
-/

@[expose] public section

open Real

open scoped Finset

namespace PrimeGaps

/-- The prime series `∑_p p ^ (-3/2)` converges. -/
private theorem summable_one_div_prime_rpow_three_halves :
    Summable (fun p : Nat.Primes ↦ 1 / ((p : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) :=
  ((Nat.Primes.summable_rpow (r := -((3 : ℝ) / 2))).mpr (by norm_num)).congr fun p ↦ by
    rw [Real.rpow_neg (by positivity), one_div]

/-- The `bDefect`-weighted `τ√` term `|S.bDefect e| * τ e * √e` is nonnegative. -/
private theorem bDefect_tau_sqrt_nonneg (S : SieveDatum) (e : ℕ) :
    0 ≤ |S.bDefect e| * (#e.divisors : ℝ) * √e := by positivity

/-- The `bDefect`-weighted `τ√` term vanishes at `0`. -/
private theorem bDefect_tau_sqrt_zero (S : SieveDatum) :
    |S.bDefect 0| * (#(0 : ℕ).divisors : ℝ) * √((0 : ℕ) : ℝ) = 0 := by
  simp

/-- The `bDefect`-weighted `τ√` term equals `1` at `1`. -/
private theorem bDefect_tau_sqrt_one (S : SieveDatum) :
    |S.bDefect 1| * (#(1 : ℕ).divisors : ℝ) * √((1 : ℕ) : ℝ) = 1 := by
  simp [SieveDatum.bDefect]

/-- The `bDefect`-weighted `τ√` term is supported on the squarefree integers. -/
private theorem bDefect_tau_sqrt_eq_zero_of_not_squarefree (S : SieveDatum) {n : ℕ}
    (hn : ¬ Squarefree n) :
    |S.bDefect n| * (#n.divisors : ℝ) * √n = 0 := by
  simp [S.bDefect_eq_zero_of_not_squarefree n hn]

/-- The `bDefect`-weighted `τ√` term is multiplicative on coprime arguments. -/
private theorem bDefect_tau_sqrt_mul_of_coprime (S : SieveDatum) {m n : ℕ} (hmn : m.Coprime n) :
    |S.bDefect (m * n)| * ((#(m * n).divisors : ℕ) : ℝ) * √((m * n : ℕ) : ℝ) =
      (|S.bDefect m| * (#m.divisors : ℝ) * √m) *
        (|S.bDefect n| * (#n.divisors : ℝ) * √n) := by
  rw [S.bDefect_mul m n hmn, abs_mul, Nat.Coprime.card_divisors_mul hmn,
    show ((m * n : ℕ) : ℝ) = (m : ℝ) * (n : ℝ) by push_cast; ring,
    Real.sqrt_mul (by positivity)]
  push_cast; ring

/-- At a prime `p` the `bDefect`-weighted term `|S.bDefect p| * τ p * √p` is at most
`4 * S.A₃ / S.A₁ * p ^ (-3/2)`: either `p ∣ S.V` and the term vanishes, or `S.bDefect_bound`
applies. -/
private theorem bDefect_tau_sqrt_prime_le (S : SieveDatum) (p : Nat.Primes) :
    |S.bDefect (p : ℕ)| * (#(p : ℕ).divisors : ℝ) * √((p : ℕ) : ℝ) ≤
      4 * S.A₃ / S.A₁ * (1 / ((p : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := by
  have hp : (p : ℕ).Prime := p.2
  have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.pos
  have hcnn : (0 : ℝ) ≤ 4 * S.A₃ / S.A₁ :=
    div_nonneg (by linarith [S.A₃_nonneg]) S.A₁_pos.le
  have hbd : |S.bDefect (p : ℕ)| ≤ 2 * S.A₃ / S.A₁ * (1 / ((p : ℕ) : ℝ) ^ 2) := by
    by_cases hpV : (p : ℕ) ∣ S.V
    · rw [S.bDefect_eq_zero_of_not_coprime (p : ℕ) (by rw [hp.coprime_iff_not_dvd]; exact (· hpV)),
        abs_zero]
      exact mul_nonneg (div_nonneg (by linarith [S.A₃_nonneg]) S.A₁_pos.le) (by positivity)
    · exact S.bDefect_bound (p : ℕ) hp hpV
  have hsq : √((p : ℕ) : ℝ) * (1 / ((p : ℕ) : ℝ) ^ 2) =
      1 / ((p : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity), one_mul,
      Real.sqrt_eq_rpow, ← Real.rpow_add hpR, ← Real.rpow_natCast ((p : ℕ) : ℝ) 2]
    norm_num
  rw [hp.divisors, Finset.card_pair hp.ne_one.symm, Nat.cast_ofNat]
  calc |S.bDefect (p : ℕ)| * (2 : ℝ) * √((p : ℕ) : ℝ)
      ≤ 2 * S.A₃ / S.A₁ * (1 / ((p : ℕ) : ℝ) ^ 2) * 2 * √((p : ℕ) : ℝ) := by gcongr
    _ = 4 * S.A₃ / S.A₁ * (√((p : ℕ) : ℝ) * (1 / ((p : ℕ) : ℝ) ^ 2)) := by ring
    _ = 4 * S.A₃ / S.A₁ * (1 / ((p : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := by rw [hsq]

/-- **Summability from the primes.**  A nonnegative multiplicative weight `w` that vanishes at
`0` and off the squarefree integers, with `w 1 = 1`, is summable over `ℕ` as soon as it is
summable over the primes: the partial sums are dominated by the Euler product
`∏_p (1 + |w p|)`. -/
private theorem summable_norm_of_summable_primes {w : ℕ → ℝ} (hw_nonneg : ∀ e, 0 ≤ w e)
    (hw0 : w 0 = 0) (hw1 : w 1 = 1) (hsupp : ∀ n, ¬ Squarefree n → w n = 0)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → w (m * n) = w m * w n)
    (hsumwp : Summable (fun p : Nat.Primes ↦ w (p : ℕ))) :
    Summable (fun n ↦ ‖w n‖) := by
  classical
  have hge1 : ∀ p : Nat.Primes, (1 : ℝ) ≤ 1 + |w (p : ℕ)| :=
    fun _ ↦ le_add_of_nonneg_right (abs_nonneg _)
  have hmultC : Multipliable (fun p : Nat.Primes ↦ 1 + |w (p : ℕ)|) :=
    Real.multipliable_one_add_of_summable
      (by simpa only [abs_of_nonneg (hw_nonneg _)] using hsumwp)
  refine summable_of_sum_range_le (c := ∏' p : Nat.Primes, (1 + |w (p : ℕ)|))
    (fun _ ↦ norm_nonneg _) fun Nr ↦ ?_
  set T : Finset ℕ := (Finset.range Nr).biUnion (fun i ↦ i.primeFactors) with hTdef
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp ↦ by
    rw [hTdef, Finset.mem_biUnion] at hp
    obtain ⟨i, _, hpi⟩ := hp
    exact Nat.prime_of_mem_primeFactors hpi
  set M : ℕ := ∏ p ∈ T, p
  have hMpf : M.primeFactors = T := Nat.primeFactors_prod hTprime
  have hMsq : Squarefree M :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq ↦ Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hTprime p hp) (hTprime q hq)).mpr hpq))
      (fun p hp ↦ (hTprime p hp).squarefree)
  calc ∑ i ∈ Finset.range Nr, ‖w i‖
      = ∑ i ∈ (Finset.range Nr).filter Squarefree, ‖w i‖ :=
        (Finset.sum_filter_of_ne fun i _ hne ↦ by
          by_contra hns; exact hne (by rw [hsupp i hns, norm_zero])).symm
    _ ≤ ∑ d ∈ M.divisors, ‖w d‖ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi ↦ ?_) fun _ _ _ ↦ norm_nonneg _
        rw [Finset.mem_filter] at hi
        rw [Nat.mem_divisors]
        refine ⟨?_, hMsq.ne_zero⟩
        calc i = ∏ p ∈ i.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hi.2).symm
          _ ∣ ∏ p ∈ M.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ (by
              rw [hMpf, hTdef]; exact fun p hp ↦ Finset.mem_biUnion.mpr ⟨i, hi.1, hp⟩)
          _ = M := Nat.prod_primeFactors_of_squarefree hMsq
    _ = ∏ p ∈ T, (1 + |w p|) := by
        simp only [Real.norm_eq_abs]
        let G : ArithmeticFunction ℝ := ⟨fun n ↦ |w n|, by simp [hw0]⟩
        have hGval : ∀ n, G n = |w n| := fun _ ↦ rfl
        have hGmul : G.IsMultiplicative := by
          rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
          refine ⟨by rw [hGval, hw1]; norm_num, ?_⟩
          intro m n _ _ hco
          rw [hGval, hGval, hGval, hmul hco, abs_mul]
        have hpp := hGmul.prodPrimeFactors_one_add_of_squarefree hMsq
        rw [hMpf] at hpp
        simp only [hGval] at hpp
        exact hpp.symm
    _ ≤ ∏' p : Nat.Primes, (1 + |w (p : ℕ)|) := by
        have hTeq : ∏ p ∈ T.subtype (fun p : ℕ ↦ p.Prime), (1 + |w (p : ℕ)|) =
            ∏ p ∈ T, (1 + |w p|) := by
          rw [Finset.prod_subtype_eq_prod_filter (fun n : ℕ ↦ 1 + |w n|) (s := T)
            (p := fun n : ℕ ↦ n.Prime), Finset.filter_true_of_mem hTprime]
        rw [← hTeq]
        exact ge_of_tendsto hmultC.hasProd (Filter.eventually_atTop.mpr
          ⟨T.subtype (fun p : ℕ ↦ p.Prime), fun s hs ↦
            Finset.prod_le_prod_of_subset_of_one_le hs (fun i _ ↦ by linarith [hge1 i])
              fun i _ _ ↦ hge1 i⟩)

/-- Per-`S` summability of the `bDefect`-weighted `τ·√` sum (the leaf-5 summand).
Reuses the finite-Euler partial-sum machinery of `summable_norm_of_summable_primes`. -/
theorem bDefect_tau_sqrt_summable (S : SieveDatum) :
    Summable (fun e : ℕ ↦ |S.bDefect e| * (#e.divisors : ℝ) * √e) := by
  classical
  refine Summable.congr (summable_norm_of_summable_primes
    (w := fun e : ℕ ↦ |S.bDefect e| * (#e.divisors : ℝ) * √e)
    (bDefect_tau_sqrt_nonneg S) (bDefect_tau_sqrt_zero S) (bDefect_tau_sqrt_one S)
    (fun _ hn ↦ bDefect_tau_sqrt_eq_zero_of_not_squarefree S hn)
    (fun {_ _} hmn ↦ bDefect_tau_sqrt_mul_of_coprime S hmn)
    (Summable.of_nonneg_of_le (fun p ↦ bDefect_tau_sqrt_nonneg S p)
      (fun p ↦ bDefect_tau_sqrt_prime_le S p)
      (summable_one_div_prime_rpow_three_halves.mul_left (4 * S.A₃ / S.A₁)))) fun n ↦ ?_
  exact (Real.norm_eq_abs _).trans (abs_of_nonneg (bDefect_tau_sqrt_nonneg S n))

/-- `‖bTilde‖` is summable over `ℕ`. -/
theorem bTilde_norm_summable (S : SieveDatum) : Summable (fun n ↦ ‖S.bTilde n‖) := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_) (bDefect_tau_sqrt_summable S)
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [bTilde_zero]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
  have hτ1 : (1 : ℝ) ≤ (#n.divisors : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hpos.ne'⟩
  have hsqrt1 : (1 : ℝ) ≤ √(n : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hpos)
  have hfrac_le : ((n.totient : ℝ)) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hnR]; exact_mod_cast n.totient_le
  rw [Real.norm_eq_abs,
    show S.bTilde n = S.bDefect n * (n.totient : ℝ) / (n : ℝ) from rfl,
    mul_div_assoc, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n.totient : ℝ) / (n : ℝ))]
  calc |S.bDefect n| * ((n.totient : ℝ) / (n : ℝ))
      ≤ |S.bDefect n| * ((#n.divisors : ℝ) * √(n : ℝ)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
    _ = |S.bDefect n| * (#n.divisors : ℝ) * √(n : ℝ) := (mul_assoc _ _ _).symm

/-- Euler product form: `∑'_e b̃(e) = ∏'_p (1 + b̃(p))`. -/
theorem bTilde_euler (S : SieveDatum) :
    (∑' e : ℕ, S.bTilde e) = ∏' p : Nat.Primes, (1 + S.bTilde (p : ℕ)) := by
  rw [← EulerProduct.eulerProduct_tprod (f := S.bTilde) (bTilde_one S)
    (fun {m n} hmn ↦ bTilde_mul S hmn) (bTilde_norm_summable S) (bTilde_zero S)]
  exact tprod_congr fun p ↦ bTilde_localFactor S p.2

/-- `singularSeries S.γ = (φ S.V / S.V) * ∑' e, S.bTilde e`. -/
theorem slem_singularSeries_bTilde_bridge (S : SieveDatum) :
    PrimeGaps.singularSeries S.γ = (S.V.totient : ℝ) / S.V * ∑' e : ℕ, S.bTilde e := by
  classical
  set F : ℕ → ℝ := fun p ↦ if Nat.Prime p then (1 - 1 / (p : ℝ)) / (1 - S.γ p / p) else 1
    with hF
  rw [show PrimeGaps.singularSeries S.γ = ∏' p : ℕ, F p by
    unfold PrimeGaps.singularSeries; rfl]
  have hsupp : Function.mulSupport F ⊆ {p : ℕ | Nat.Prime p} := fun p hp ↦ by
    by_contra hpp
    apply hp
    simp only [hF, Set.mem_ofPred_eq] at hpp ⊢
    rw [if_neg hpp]
  rw [← tprod_subtype_eq_of_mulSupport_subset hsupp]
  set vFac : ℕ → ℝ := fun p ↦ if p ∣ S.V then (1 - 1 / (p : ℝ)) else 1 with hvFac
  have hFp : ∀ p : {p : ℕ // p ∈ {q : ℕ | Nat.Prime q}},
      F (p : ℕ) = (1 + S.bTilde (p : ℕ)) * vFac (p : ℕ) := by
    rintro ⟨p, hp⟩
    simp only [Set.mem_ofPred_eq] at hp
    simp only [hF, if_pos hp]
    by_cases hpV : p ∣ S.V
    · simp only [hvFac, if_pos hpV, bTilde_prime_dvd_V S hp hpV, S.γ_zero_of_dvd p hp hpV,
        zero_div, sub_zero, add_zero, one_mul, div_one]
    · simp only [hvFac, if_neg hpV, mul_one]
      exact (bTilde_prime_add_one S hp hpV).symm
  rw [tprod_congr hFp]
  have hsumc : Summable (fun p : {p : ℕ // p ∈ {q : ℕ | Nat.Prime q}} ↦ S.bTilde (p : ℕ)) :=
    ((bTilde_norm_summable S).comp_injective Subtype.val_injective).of_norm
  have hmulA : Multipliable (fun p : {p : ℕ // p ∈ {q : ℕ | Nat.Prime q}} ↦ 1 + S.bTilde (p : ℕ)) :=
    Real.multipliable_one_add_of_summable hsumc
  have hmulB : Multipliable (fun p : {p : ℕ // p ∈ {q : ℕ | Nat.Prime q}} ↦ vFac (p : ℕ)) := by
    refine multipliable_of_hasFiniteMulSupport
      (Set.Finite.subset (s := (Subtype.val ⁻¹' (↑S.V.primeFactors : Set ℕ)))
        (Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective)
          S.V.primeFactors.finite_toSet) fun p hp ↦ ?_)
    simp only [Function.mem_mulSupport, hvFac] at hp
    by_cases hpd : (p : ℕ) ∣ S.V
    · simp only [Set.mem_preimage, Finset.mem_coe]
      exact Nat.mem_primeFactors.mpr ⟨p.2, hpd, S.V_pos.ne'⟩
    · exact absurd (if_neg hpd) hp
  rw [Multipliable.tprod_mul hmulA hmulB]
  have hA : (∏' p : {p : ℕ // p ∈ {q : ℕ | Nat.Prime q}}, (1 + S.bTilde (p : ℕ))) =
      ∑' e : ℕ, S.bTilde e := (bTilde_euler S).symm
  have hB : (∏' p : {p : ℕ // p ∈ {q : ℕ | Nat.Prime q}}, vFac (p : ℕ)) =
      (S.V.totient : ℝ) / (S.V : ℝ) := by
    have htot : (S.V.totient : ℝ) / (S.V : ℝ) = ∏ p ∈ S.V.primeFactors, (1 - 1 / (p : ℝ)) := by
      have hR : (S.V.totient : ℝ) = S.V * ∏ p ∈ S.V.primeFactors, (1 - (p : ℝ)⁻¹) := by
        have := congrArg (fun q : ℚ ↦ (q : ℝ)) (Nat.totient_eq_mul_prod_factors S.V)
        push_cast at this
        convert this using 2
      rw [hR, mul_comm, mul_div_assoc,
        div_self (by exact_mod_cast S.V_pos.ne' : (S.V : ℝ) ≠ 0), mul_one]
      exact Finset.prod_congr rfl fun p _ ↦ by rw [one_div]
    have hfin : (∏' p : {p : ℕ // p ∈ {q : ℕ | Nat.Prime q}}, vFac (p : ℕ)) =
        ∏ p ∈ (S.V.primeFactors.subtype (fun q : ℕ ↦ q ∈ {r : ℕ | Nat.Prime r})),
            vFac (p : ℕ) := by
      refine tprod_eq_prod fun p hp ↦ ?_
      simp only [Finset.mem_subtype, Set.mem_ofPred_eq] at hp
      by_cases hpd : (p : ℕ) ∣ S.V
      · exact absurd (Nat.mem_primeFactors.mpr ⟨p.2, hpd, S.V_pos.ne'⟩) hp
      · simp only [hvFac, if_neg hpd]
    rw [htot, hfin, Finset.prod_subtype_eq_prod_filter]
    simp only [Set.mem_ofPred_eq]
    rw [Finset.filter_true_of_mem (fun q hq ↦ Nat.prime_of_mem_primeFactors hq)]
    exact Finset.prod_congr rfl fun p hp ↦ by
      simp only [hvFac, if_pos (Nat.dvd_of_mem_primeFactors hp)]
  rw [hA, hB, mul_comm]

/-- Positivity of the singular series for a legal sieve datum.
Route: `slem_singularSeries_bTilde_bridge` gives `𝔖 = (φV/V)·∑bTilde`; via `bTilde_euler`
`∑bTilde = ∏'(1+bTilde p)`, and each factor `(1-1/p)/(1-γp/p) > 0` (γp<p from `γ_lt`,
γp≥0 from `γ_nonneg`), with `φV/V > 0`. Use `Real.tprod_pos` / positivity of tprod of
positives. -/
theorem singularSeries_pos (S : SieveDatum) : 0 < PrimeGaps.singularSeries S.γ := by
  rw [slem_singularSeries_bTilde_bridge S, bTilde_euler S]
  have hVpos : (0 : ℝ) < (S.V : ℝ) := by exact_mod_cast S.V_pos
  have hφpos : (0 : ℝ) < (S.V.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr S.V_pos
  have hfrac : (0 : ℝ) < (S.V.totient : ℝ) / S.V := div_pos hφpos hVpos
  have hpos : ∀ p : Nat.Primes, 0 < 1 + S.bTilde (p : ℕ) := one_add_bTilde_prime_pos S
  have hsumc : Summable (fun p : Nat.Primes ↦ S.bTilde (p : ℕ)) :=
    ((bTilde_norm_summable S).comp_injective Subtype.val_injective).of_norm
  have hlog : Summable (fun p : Nat.Primes ↦ Real.log (1 + S.bTilde (p : ℕ))) :=
    Real.summable_log_one_add_of_summable hsumc
  have hprodpos : 0 < ∏' p : Nat.Primes, (1 + S.bTilde (p : ℕ)) := by
    rw [← Real.rexp_tsum_eq_tprod hpos hlog]; exact Real.exp_pos _
  exact mul_pos hfrac hprodpos

/-- `|bTilde|` is summable over `ℕ` (from `bTilde_norm_summable`). -/
theorem absBTilde_summable (S : SieveDatum) : Summable (fun n ↦ |S.bTilde n|) := by
  simpa [Real.norm_eq_abs] using bTilde_norm_summable S

/-- `|bTilde|` is multiplicative on coprimes. -/
theorem absBTilde_mul (S : SieveDatum) {m n : ℕ} (hmn : m.Coprime n) :
    |S.bTilde (m * n)| = |S.bTilde m| * |S.bTilde n| := by
  rw [bTilde_mul S hmn, abs_mul]

/-- Per-prime Euler factor for `|bTilde|`: `∑'_k |bTilde (p^k)| = 1 + |bTilde p|`. -/
theorem absBTilde_localFactor (S : SieveDatum) {p : ℕ} (hp : p.Prime) :
    ∑' k : ℕ, |S.bTilde (p ^ k)| = 1 + |S.bTilde p| := by
  rw [tsum_eq_sum (s := {0, 1})]
  · simp [Finset.sum_insert, bTilde_one]
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [bTilde_prime_pow_eq_zero S hp (by omega), abs_zero]

/-- Euler product form for `|bTilde|`: `∑'_e |b̃(e)| = ∏'_p (1 + |b̃(p)|)`. -/
theorem absBTilde_euler (S : SieveDatum) :
    (∑' e : ℕ, |S.bTilde e|) = ∏' p : Nat.Primes, (1 + |S.bTilde (p : ℕ)|) := by
  rw [← EulerProduct.eulerProduct_tprod (f := fun n ↦ |S.bTilde n|)
    (by rw [bTilde_one]; norm_num) (fun {m n} hmn ↦ absBTilde_mul S hmn)
    (by simpa [Real.norm_eq_abs] using absBTilde_summable S) (by rw [bTilde_zero]; norm_num)]
  exact tprod_congr fun p ↦ absBTilde_localFactor S p.2

/-- Concrete uniform bound on the prime reciprocal-square sum: `∑'_p (1/p²) ≤ 1`.
Since `∑_{n≥2} 1/n² = π²/6 − 1 < 1`, and primes ⊆ `{n : n ≥ 2}`. -/
theorem primes_recip_sq_le : (∑' p : Nat.Primes, (1 / ((p : ℕ) : ℝ) ^ 2)) ≤ 1 := by
  classical
  have hsubtype : (∑' p : Nat.Primes, (1 / ((p : ℕ) : ℝ) ^ 2)) =
        ∑' n : ℕ, {p : ℕ | p.Prime}.indicator (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) n :=
    tsum_subtype {p : ℕ | p.Prime} (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2)
  rw [hsubtype]
  refine Real.tsum_le_of_sum_range_le
    (Set.indicator_nonneg fun _ _ ↦ by positivity) fun N ↦ ?_
  have hbound : ∀ i ∈ Finset.range N,
      {p : ℕ | p.Prime}.indicator (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) i ≤
        (if 2 ≤ i then ((i : ℝ) ^ 2)⁻¹ else 0) := by
    intro i _
    rw [Set.indicator_apply]
    by_cases hpi : i ∈ {p : ℕ | p.Prime}
    · rw [if_pos hpi, if_pos (hpi : i.Prime).two_le, one_div]
    · rw [if_neg hpi]
      split
      · positivity
      · exact le_rfl
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [show (∑ i ∈ Finset.range N, (if 2 ≤ i then ((i : ℝ) ^ 2)⁻¹ else 0)) =
      ∑ i ∈ Finset.Ioc 1 (N - 1), ((i : ℝ) ^ 2)⁻¹ by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega]
  rcases Nat.eq_zero_or_pos (N - 1) with hN | hN
  · rw [hN]; simp
  · refine (sum_Ioc_inv_sq_le_sub (by norm_num) hN).trans ?_
    simp only [Nat.cast_one, inv_one]
    linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) (N - 1))]

/-- At a prime `p`, `|S.bTilde p| ≤ 2 * S.A₃ / S.A₁ * (1 / p ^ 2)`: either `p ∣ S.V` and
`S.bTilde p = 0`, or `S.bDefect_bound` applies and `φ p / p ≤ 1`. -/
private theorem abs_bTilde_prime_le (S : SieveDatum) (p : Nat.Primes) :
    |S.bTilde (p : ℕ)| ≤ 2 * S.A₃ / S.A₁ * (1 / ((p : ℕ) : ℝ) ^ 2) := by
  have hp : (p : ℕ).Prime := p.2
  have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.pos
  by_cases hpV : (p : ℕ) ∣ S.V
  · rw [bTilde_prime_dvd_V S hp hpV, abs_zero]
    exact mul_nonneg (div_nonneg (by linarith [S.A₃_nonneg]) S.A₁_pos.le) (by positivity)
  · have hfrac_le : ((p : ℕ).totient : ℝ) / ((p : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hpR]; exact_mod_cast (p : ℕ).totient_le
    rw [show S.bTilde (p : ℕ) = S.bDefect (p : ℕ) * ((p : ℕ).totient : ℝ) / ((p : ℕ) : ℝ) from rfl,
      mul_div_assoc, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((p : ℕ).totient : ℝ) / ((p : ℕ) : ℝ))]
    calc |S.bDefect (p : ℕ)| * (((p : ℕ).totient : ℝ) / ((p : ℕ) : ℝ))
        ≤ |S.bDefect (p : ℕ)| * 1 := mul_le_mul_of_nonneg_left hfrac_le (abs_nonneg _)
      _ ≤ 2 * S.A₃ / S.A₁ * (1 / ((p : ℕ) : ℝ) ^ 2) := by
          rw [mul_one]; exact S.bDefect_bound (p : ℕ) hp hpV

/-- Uniform (`A₁,A₃`-only) bound on `∑'_e |bTilde e|`.
Route: `∑'_e |bTilde e| = ∏'_p (1 + |bTilde p|) ≤ exp(∑'_p |bTilde p|) ≤ exp(2A₃/A₁·1)`,
using `|bTilde p| ≤ |bDefect p| ≤ 2A₃/A₁·(1/p²)` and `∑'_p 1/p² ≤ 1` (`primes_recip_sq_le`).
`K A₁ A₃ = Real.exp (2·A₃/A₁·1) + 1` (positive for all reals since exp > 0). -/
theorem bTilde_abs_tsum_uniform : ∃ K : ℝ → ℝ → ℝ, (∀ A₁ A₃ : ℝ, 0 < K A₁ A₃) ∧
      ∀ S : SieveDatum, (∑' e : ℕ, |S.bTilde e|) ≤ K S.A₁ S.A₃ := by
  refine ⟨fun A₁ A₃ ↦ rexp (2 * A₃ / A₁ * 1) + 1, fun A₁ A₃ ↦ by positivity, fun S ↦ ?_⟩
  change (∑' e : ℕ, |S.bTilde e|) ≤ rexp (2 * S.A₃ / S.A₁ * 1) + 1
  have hcnn : (0 : ℝ) ≤ 2 * S.A₃ / S.A₁ :=
    div_nonneg (by linarith [S.A₃_nonneg]) S.A₁_pos.le
  have hsumb : Summable (fun p : Nat.Primes ↦ |S.bTilde (p : ℕ)|) :=
    (absBTilde_summable S).comp_injective Subtype.val_injective
  have hsumsq : Summable (fun p : Nat.Primes ↦ 1 / ((p : ℕ) : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      Subtype.val_injective
  have hpos : ∀ p : Nat.Primes, 0 < 1 + |S.bTilde (p : ℕ)| := fun p ↦ by positivity
  have hlogsum : Summable (fun p : Nat.Primes ↦ Real.log (1 + |S.bTilde (p : ℕ)|)) :=
    Real.summable_log_one_add_of_summable hsumb
  rw [absBTilde_euler S, ← Real.rexp_tsum_eq_tprod hpos hlogsum]
  have hle : (∑' p : Nat.Primes, Real.log (1 + |S.bTilde (p : ℕ)|)) ≤ 2 * S.A₃ / S.A₁ * 1 := by
    refine (Summable.tsum_le_tsum (fun p ↦ by
      linarith [Real.log_le_sub_one_of_pos (hpos p)]) hlogsum hsumb).trans ?_
    refine (Summable.tsum_le_tsum (fun p ↦ abs_bTilde_prime_le S p) hsumb
      (hsumsq.mul_left _)).trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left primes_recip_sq_le hcnn
  linarith [Real.exp_le_exp.mpr hle]

/-- Uniform (`A₁,A₃`-only) bound on the `bDefect`-weighted `τ√` sum that governs the
density error after termwise substitution.
NOTE `bDefect e = bTilde e · e/φ(e)`; `e/φ(e) = O(log log e)`. Multiplicative Euler bound
from `bDefect_bound` directly on `|bDefect e|·τ(e)·√e` (multiplicative, per-prime factor
`(1 + |bDefect p|·2·(1+√p))` summable since `|bDefect p| ≤ 2A₃/A₁/p²`, so `·√p ~ 1/p^{3/2}`
summable). -/
theorem bDefect_tau_sqrt_tsum_uniform : ∃ K : ℝ → ℝ → ℝ, (∀ A₁ A₃ : ℝ, 0 < K A₁ A₃) ∧
      ∀ S : SieveDatum,
        (∑' e : ℕ, |S.bDefect e| * (#e.divisors : ℝ) * √e) ≤ K S.A₁ S.A₃ := by
  classical
  refine ⟨fun A₁ A₃ ↦
    rexp (4 * A₃ / A₁ * (∑' p : Nat.Primes, 1 / ((p : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) + 1,
    fun A₁ A₃ ↦ by positivity, fun S ↦ ?_⟩
  set w : ℕ → ℝ := fun e ↦ |S.bDefect e| * (#e.divisors : ℝ) * √e with hwdef
  change (∑' e : ℕ, w e) ≤ rexp (4 * S.A₃ / S.A₁ *
          (∑' p : Nat.Primes, 1 / ((p : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) + 1
  have hw_nonneg : ∀ e, 0 ≤ w e := fun e ↦ bDefect_tau_sqrt_nonneg S e
  have hw1 : w 1 = 1 := bDefect_tau_sqrt_one S
  have hsupp : ∀ n, ¬ Squarefree n → w n = 0 :=
    fun _ hn ↦ bDefect_tau_sqrt_eq_zero_of_not_squarefree S hn
  have hwp_bound : ∀ p : Nat.Primes,
      w (p : ℕ) ≤ 4 * S.A₃ / S.A₁ * (1 / ((p : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := fun p ↦
    bDefect_tau_sqrt_prime_le S p
  have hsumRp : Summable
      (fun p : Nat.Primes ↦ 4 * S.A₃ / S.A₁ * (1 / ((p : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) :=
    summable_one_div_prime_rpow_three_halves.mul_left _
  have hsumwp : Summable (fun p : Nat.Primes ↦ w (p : ℕ)) :=
    Summable.of_nonneg_of_le (fun p ↦ hw_nonneg _) hwp_bound hsumRp
  have hposf : ∀ p : Nat.Primes, 0 < 1 + w (p : ℕ) := fun p ↦ by
    linarith [hw_nonneg (p : ℕ)]
  have hlogsum : Summable (fun p : Nat.Primes ↦ Real.log (1 + w (p : ℕ))) :=
    Real.summable_log_one_add_of_summable hsumwp
  have heuler : (∑' e : ℕ, w e) = ∏' p : Nat.Primes, (1 + w (p : ℕ)) := by
    rw [← EulerProduct.eulerProduct_tprod (f := w) hw1
      (fun {m n} hmn ↦ bDefect_tau_sqrt_mul_of_coprime S hmn)
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hw_nonneg _)] using
        bDefect_tau_sqrt_summable S) (bDefect_tau_sqrt_zero S)]
    refine tprod_congr fun p ↦ ?_
    rw [tsum_eq_sum (s := Finset.range 2) fun k hk ↦ hsupp _ fun hsq ↦ by
        rw [Finset.mem_range, Nat.not_lt] at hk
        have := (Nat.squarefree_pow_iff p.2.ne_one (by omega)).mp hsq
        omega,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [hw1]
  rw [heuler, ← Real.rexp_tsum_eq_tprod hposf hlogsum]
  have hle : (∑' p : Nat.Primes, Real.log (1 + w (p : ℕ))) ≤
      4 * S.A₃ / S.A₁ * (∑' p : Nat.Primes, 1 / ((p : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := by
    refine (Summable.tsum_le_tsum (fun p ↦ by
      linarith [Real.log_le_sub_one_of_pos (hposf p)]) hlogsum hsumwp).trans ?_
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hwp_bound hsumwp hsumRp
  linarith [Real.exp_le_exp.mpr hle]

/-- `∑' e, |S.bTilde e| * (1 + log e) ≤ K S.A₁ S.A₃`, uniformly over sieve data. -/
theorem bTilde_log_tsum_uniform : ∃ K : ℝ → ℝ → ℝ, (∀ A₁ A₃ : ℝ, 0 < K A₁ A₃) ∧
      ∀ S : SieveDatum, (∑' e : ℕ, |S.bTilde e| * (1 + Real.log e)) ≤ K S.A₁ S.A₃ := by
  obtain ⟨K5, hK5pos, hK5⟩ := bDefect_tau_sqrt_tsum_uniform
  refine ⟨fun A₁ A₃ ↦ 3 * K5 A₁ A₃, fun A₁ A₃ ↦ by have := hK5pos A₁ A₃; positivity, fun S ↦ ?_⟩
  set v : ℕ → ℝ := fun e ↦ |S.bTilde e| * (1 + Real.log e)
  set w : ℕ → ℝ := fun e ↦ |S.bDefect e| * (#e.divisors : ℝ) * √e
  have hterm : ∀ e : ℕ, v e ≤ 3 * w e := fun e ↦ abs_bTilde_mul_log_le S e
  have hsum_3w : Summable (fun e ↦ 3 * w e) := (bDefect_tau_sqrt_summable S).mul_left 3
  have hsum_v : Summable v := Summable.of_nonneg_of_le
    (fun e ↦ mul_nonneg (abs_nonneg _) (by linarith [Real.log_natCast_nonneg e])) hterm hsum_3w
  calc (∑' e : ℕ, v e) ≤ ∑' e : ℕ, 3 * w e := Summable.tsum_le_tsum hterm hsum_v hsum_3w
    _ = 3 * ∑' e : ℕ, w e := tsum_mul_left
    _ ≤ 3 * K5 S.A₁ S.A₃ := mul_le_mul_of_nonneg_left (hK5 S) (by norm_num)

/-- **Prime-local lower bound for the `bTilde` Euler factor.**
`-(2 * S.A₃) * (1 / p ^ 2) ≤ log (1 + S.bTilde p)` at every prime `p`. -/
private theorem neg_le_log_one_add_bTilde_prime (S : SieveDatum) (p : Nat.Primes) :
    -(2 * S.A₃) * (1 / ((p : ℕ) : ℝ) ^ 2) ≤ Real.log (1 + S.bTilde (p : ℕ)) := by
  have hA₃nn : (0 : ℝ) ≤ S.A₃ := S.A₃_nonneg
  have hp : (p : ℕ).Prime := p.2
  have hp2 : (2 : ℕ) ≤ (p : ℕ) := hp.two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp2pos : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 2 := by positivity
  by_cases hpV : (p : ℕ) ∣ S.V
  · rw [bTilde_prime_dvd_V S hp hpV, add_zero, Real.log_one]
    have : (0 : ℝ) ≤ 2 * S.A₃ * (1 / ((p : ℕ) : ℝ) ^ 2) := by positivity
    linarith
  · have h1mγ : 1 - S.γ (p : ℕ) ≤ S.A₃ / (p : ℝ) := by
      have := abs_le.mp (S.γ_approx (p : ℕ) hp hpV); linarith [this.1, this.2]
    have hden : (0 : ℝ) < 1 - S.γ (p : ℕ) / p := by
      rw [sub_pos, div_lt_one hp0]; exact S.γ_lt (p : ℕ) hp
    set K : ℝ := 1 + 2 * S.A₃ / ((p : ℕ) : ℝ) ^ 2 with hK
    have hKpos : (0 : ℝ) < K := by rw [hK]; positivity
    have hge : 1 / K ≤ 1 + S.bTilde (p : ℕ) := by
      rw [bTilde_prime_add_one S hp hpV, div_le_div_iff₀ hKpos hden, hK, ← sub_nonneg,
        show (1 - 1 / (p : ℝ)) * (1 + 2 * S.A₃ / ((p : ℕ) : ℝ) ^ 2) - 1 * (1 - S.γ (p : ℕ) / p) =
            (2 * S.A₃ * ((p : ℝ) - 1) - (p : ℝ) * ((p : ℝ) * (1 - S.γ (p : ℕ)))) / (p : ℝ) ^ 3 by
          field_simp; ring]
      have h1mγ' : (p : ℝ) * (1 - S.γ (p : ℕ)) ≤ S.A₃ := by
        rw [mul_comm]; exact (le_div_iff₀ hp0).mp h1mγ
      have hstep1 := mul_nonneg hp0.le (sub_nonneg.mpr h1mγ')
      have hstep2 := mul_nonneg hA₃nn (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)
      exact div_nonneg (by linarith) (by positivity)
    have hlogmono := Real.log_le_log (one_div_pos.mpr hKpos) hge
    rw [one_div, Real.log_inv] at hlogmono
    have hlogK_le : Real.log K ≤ 2 * S.A₃ / ((p : ℕ) : ℝ) ^ 2 := by
      have := Real.log_le_sub_one_of_pos hKpos
      rw [hK] at this
      linarith
    rw [show - (2 * S.A₃) * (1 / ((p : ℕ) : ℝ) ^ 2) = -(2 * S.A₃ / ((p : ℕ) : ℝ) ^ 2) by ring]
    linarith

/-- `φ S.V / S.V ≤ f S.A₃ * singularSeries S.γ`, uniformly over sieve data, with
`f A₃ = exp (2 * A₃)`. -/
theorem singularSeries_rhoV_uniform_lower : ∃ f : ℝ → ℝ, (∀ A₃ : ℝ, 0 < f A₃) ∧ ∀ S : SieveDatum,
        (S.V.totient : ℝ) / S.V ≤ f S.A₃ * PrimeGaps.singularSeries S.γ := by
  refine ⟨fun A₃ ↦ rexp (2 * A₃), fun A₃ ↦ by positivity, fun S ↦ ?_⟩
  have hpos : ∀ p : Nat.Primes, 0 < 1 + S.bTilde (p : ℕ) := one_add_bTilde_prime_pos S
  have hlog : Summable (fun p : Nat.Primes ↦ Real.log (1 + S.bTilde (p : ℕ))) :=
    Real.summable_log_one_add_of_summable
      (((bTilde_norm_summable S).comp_injective Subtype.val_injective).of_norm)
  have hsumsq : Summable (fun p : Nat.Primes ↦ (1 / ((p : ℕ) : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective Subtype.val_injective
  have hge_neg2A₃ : -(2 * S.A₃) ≤ ∑' p : Nat.Primes, Real.log (1 + S.bTilde (p : ℕ)) := by
    refine le_trans ?_ (Summable.tsum_le_tsum (neg_le_log_one_add_bTilde_prime S)
      (hsumsq.mul_left _) hlog)
    rw [tsum_mul_left]
    have hBnn : (0 : ℝ) ≤ ∑' p : Nat.Primes, (1 / ((p : ℕ) : ℝ) ^ 2) :=
      tsum_nonneg fun p ↦ by positivity
    nlinarith [primes_recip_sq_le, hBnn, S.A₃_nonneg]
  have hprod_ge : rexp (-(2 * S.A₃)) ≤ ∏' p : Nat.Primes, (1 + S.bTilde (p : ℕ)) := by
    rw [← Real.rexp_tsum_eq_tprod hpos hlog]; exact Real.exp_le_exp.mpr hge_neg2A₃
  rw [slem_singularSeries_bTilde_bridge S, bTilde_euler S]
  calc (S.V.totient : ℝ) / S.V
      = (S.V.totient : ℝ) / S.V * (rexp (2 * S.A₃) * rexp (-(2 * S.A₃))) := by
        rw [← Real.exp_add]; simp
    _ ≤ (S.V.totient : ℝ) / S.V *
          (rexp (2 * S.A₃) * ∏' p : Nat.Primes, (1 + S.bTilde (p : ℕ))) := by gcongr
    _ = rexp (2 * S.A₃) *
          ((S.V.totient : ℝ) / S.V * ∏' p : Nat.Primes, (1 + S.bTilde (p : ℕ))) := by ring

end PrimeGaps
