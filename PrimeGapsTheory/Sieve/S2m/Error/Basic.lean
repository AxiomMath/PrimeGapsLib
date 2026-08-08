/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.PrimeIndicator
public import PrimeGapsTheory.Sieve.BombieriVinogradov
public import PrimeGapsTheory.Sieve.S1.CRT
public import PrimeGapsTheory.Sieve.Transforms.YFromLambda

/-!
# Setup for the S2m error term

Divisor-function bounds at prime powers, the sieve-weight structure, the error
contributions, and the collapse to a sum over moduli.

## Main definitions

* `MaynardS2Error.SieveWeights`: a family of sieve weights with permissible support.
* `MaynardS2Error.windowError`: the prime-counting error over the window `(N, 2N]`.
* `MaynardS2Error.totalErrorContribution`, `MaynardS2Error.gatedErrorContribution`: the weighted
  error sums.

## Main results

* `MaynardS2Error.fiber_card_le_tau`: at most `τ (3 * k) q` pairs share a given modulus.
* `MaynardS2Error.collapse_to_modulus_sum`: the error contribution is bounded by a sum over moduli.
-/

@[expose] public section

open Real
open PrimeGaps

open scoped ArithmeticFunction.zeta
open scoped Finset
open scoped Topology

namespace MaynardS2Error

open ArithmeticFunction zeta

theorem zeta_pow_eq_tuple_card (r n : ℕ) (hn : 0 < n) : τ r n =
      #((Fintype.piFinset (fun _ : Fin r ↦ Finset.range (n + 1))).filter
        (fun a : Fin r → ℕ ↦ (∀ i, 1 ≤ a i) ∧ (∏ i, a i) = n)) := by
  have hn0 : n ≠ 0 := hn.ne'
  have hbridge : τ r n = {d : Fin r → ℕ | ∏ i, d i = n}.ncard := by
    rw [ArithmeticFunction.tau_apply_eq_card_finMulAntidiag, ← Set.ncard_coe_finset]
    congr 1
    ext d
    simp [Nat.mem_finMulAntidiag, hn0]
  rw [hbridge, ← Set.ncard_coe_finset]
  congr 1
  ext d
  simp only [Finset.coe_filter, Fintype.mem_piFinset, Finset.mem_range, Set.mem_ofPred_eq]
  refine ⟨fun hprod ↦ ⟨fun i ↦ ?_, fun i ↦ ?_, hprod⟩, fun h ↦ h.2.2⟩
  · have := Nat.le_of_dvd hn (hprod ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    omega
  · exact Nat.pos_of_ne_zero fun hdi ↦ hn0 (hprod ▸ Finset.prod_eq_zero (Finset.mem_univ i) hdi)

/-- `τ r (p ^ a) ≤ (a + 1) ^ r` at a prime power. -/
theorem zeta_pow_ppow_le (r : ℕ) : ∀ (p a : ℕ), p.Prime → τ r (p ^ a) ≤ (a + 1) ^ r := by
  induction r with
  | zero =>
    intro p a hp
    simp only [pow_zero]
    rcases eq_or_ne (p ^ a) 1 with h | h
    · simp [h]
    · rw [ArithmeticFunction.one_apply, if_neg h]; norm_num
  | succ r ih =>
    intro p a hp
    have hpow : (ζ ^ (r + 1)) = τ r * ζ := by ring
    rw [hpow, ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    calc ∑ x ∈ Finset.range (a + 1), τ r (p ^ x) ≤ ∑ _ ∈ Finset.range (a + 1), (a + 1) ^ r :=
          Finset.sum_le_sum fun x hx ↦ (ih p x hp).trans
            (Nat.pow_le_pow_left (Finset.mem_range.mp hx) r)
      _ = (a + 1) ^ (r + 1) := by rw [Finset.sum_const, Finset.card_range]; ring

/-- `(a + 1) ^ r ≤ (2 ^ r) ^ a`. -/
theorem ppow_bound (r a : ℕ) : (a + 1) ^ r ≤ (2 ^ r) ^ a := by
  rw [← pow_mul, mul_comm, pow_mul]
  exact Nat.pow_le_pow_left Nat.lt_two_pow_self r

/-- `τ r (p ^ a) ≤ (2 ^ r) ^ a` at a prime power, the geometric form of `zeta_pow_ppow_le`. -/
theorem zeta_pow_ppow_le' (r p a : ℕ) (hp : p.Prime) : τ r (p ^ a) ≤ (2 ^ r) ^ a :=
  (zeta_pow_ppow_le r p a hp).trans (ppow_bound r a)

/-- A family of sieve weights `λ` with promoted permissible support. -/
structure SieveWeights (k : ℕ) (N θ δ : ℝ) where
  /-- The weight function `λ`, finitely supported on `k`-tuples of naturals. -/
  lam : (Fin k → ℕ) →₀ ℝ
  support : lam.HasPermissibleSupport ⌊N ^ (θ / 2 - δ)⌋₊ (primorial ⌊PrimeGaps.D₀ N⌋₊)

/-- The promoted interval error, adapted to a real window by taking its natural floors. -/
noncomputable def windowError (N : ℝ) (q : ℕ) : ℝ := Nat.primeCountingIocError ⌊N⌋₊ ⌊2 * N⌋₊ q

/-- `Real.primeCountingZMod x q a` as the number of primes `p ≤ x` with `p % q = a % q`. -/
lemma primesInAP_eq_filter (x : ℝ) (q a : ℕ) : Real.primeCountingZMod x q (a : ZMod q) =
      #{p ∈ (Finset.range (⌊x⌋₊ + 1)) | p.Prime ∧ p % q = a % q} := by
  classical
  rw [Real.primeCountingZMod_eq_card_finset_range]
  congr 1
  refine Finset.filter_congr fun p _ ↦ ?_
  rw [ZMod.natCast_eq_natCast_iff]
  rfl

/-- The total error contribution `∑_{d,e: λ_d λ_e ≠ 0} |λ_d| |λ_e| E(N, q(d,e))`. -/
noncomputable def totalErrorContribution {k : ℕ} {N θ δ : ℝ} (w : SieveWeights k N θ δ) : ℝ :=
  ∑' d : Fin k → ℕ, ∑' e : Fin k → ℕ, (if w.lam d * w.lam e ≠ 0 then
      |w.lam d| * |w.lam e| * windowError N (PrimeGaps.qMod (primorial ⌊PrimeGaps.D₀ N⌋₊) d e)
    else 0)

/-- The error contribution at window scale `X` and modulus `W`, restricted to pairs satisfying
`gate`. -/
noncomputable def gatedErrorContribution {k : ℕ} (X : ℝ) (W : ℕ) (lam : (Fin k → ℕ) → ℝ)
    (gate : (Fin k → ℕ) → (Fin k → ℕ) → Prop) [DecidableRel gate] : ℝ :=
  ∑' d : Fin k → ℕ, ∑' e : Fin k → ℕ, if gate d e ∧ lam d * lam e ≠ 0 then
      |lam d| * |lam e| * windowError X (PrimeGaps.qMod W d e)
    else 0

/-- The sieve weight `w.lam` has finite support, being a `Finsupp`. -/
lemma totalErrorContribution_finite_support {k : ℕ} {N θ δ : ℝ} (w : SieveWeights k N θ δ) :
    (Function.support (fun d : Fin k → ℕ ↦ w.lam d)).Finite :=
  w.lam.hasFiniteSupport

/-- `|λ d| ≤ C₁ * Finsupp.maxRealAbs (PrimeGaps.lToY λ) * Real.log N ^ k` for all large `N`, with
`C₁` independent of `N`, of the weight `λ` and of `d`. -/
lemma lambdaMax_bound (k : ℕ) (hk : 2 ≤ k) (θ δ : ℝ) (hδ0 : 0 < δ) (hδθ : δ < θ / 2) (hθ1 : θ < 1) :
    ∃ (C₁ N₁ : ℝ), 0 < C₁ ∧ ∀ (N : ℝ), N₁ ≤ N → ∀ (w : SieveWeights k N θ δ), ∀ (d : Fin k → ℕ),
        |w.lam d| ≤ C₁ * Finsupp.maxRealAbs (PrimeGaps.lToY w.lam) * (Real.log N) ^ k := by
  classical
  set α : ℝ := θ / 2 - δ with hα
  -- `hδθ` gives `0 < α`; `hδ0` and `hθ1` only pin the (unused) upper bound `α < 1/2`.
  have hα0 : 0 < α := by rw [hα]; linarith
  have : α < 1 / 2 := by rw [hα]; linarith
  refine ⟨rexp (1 + 3 * k) * α ^ k, rexp (2 / α), ?_, ?_⟩
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < 2).trans_le hk
    positivity
  intro N hN w d
  have hexp_pos : (0 : ℝ) < rexp (2 / α) := Real.exp_pos _
  have hN0 : (0 : ℝ) < N := hexp_pos.trans_le hN
  have hlogN : 2 / α ≤ Real.log N := by simpa using Real.log_le_log hexp_pos hN
  have hSL : N ^ (θ / 2 - δ) = N ^ α := rfl
  have hlogSL : Real.log (N ^ (θ / 2 - δ)) = α * Real.log N := by
    rw [hSL, Real.log_rpow hN0]
  have hR2 : (2 : ℝ) ≤ N ^ (θ / 2 - δ) := by
    rw [hSL, ← Real.log_le_log_iff (by norm_num) (Real.rpow_pos_of_pos hN0 α), Real.log_rpow hN0]
    calc Real.log 2 ≤ 2 := by
          linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ = α * (2 / α) := by field_simp
      _ ≤ α * Real.log N := by gcongr
  have hRfloor : 2 ≤ ⌊N ^ (θ / 2 - δ)⌋₊ := Nat.le_floor hR2
  have hbound := PrimeGaps.max_yToL_le_const_mul_max_y_mul_log_pow w.support.lToY hRfloor
  have hlogFloor : Real.log (⌊N ^ (θ / 2 - δ)⌋₊ : ℝ) ≤ α * Real.log N := by
    rw [← hlogSL]
    exact Real.log_le_log (by positivity) (Nat.floor_le (Real.rpow_nonneg hN0.le _))
  have hlamRecover : w.lam d = PrimeGaps.yToL (PrimeGaps.lToY w.lam) d := by
    rw [PrimeGaps.yToL_lToY]
    split_ifs with hd
    · rfl
    · by_contra hne
      exact hd (w.support.squarefree_of_ne_zero hne)
  rw [hlamRecover]
  calc
    |PrimeGaps.yToL (PrimeGaps.lToY w.lam) d| ≤
        Finsupp.maxRealAbs (PrimeGaps.yToL (PrimeGaps.lToY w.lam)) :=
      Finsupp.le_maxRealAbs
    _ ≤ rexp (1 + 3 * k) * Finsupp.maxRealAbs (PrimeGaps.lToY w.lam) *
        Real.log ⌊N ^ (θ / 2 - δ)⌋₊ ^ k := hbound
    _ ≤ rexp (1 + 3 * k) * Finsupp.maxRealAbs (PrimeGaps.lToY w.lam) *
        (α * Real.log N) ^ k := by
      gcongr
      exact mul_nonneg (Real.exp_pos _).le Finsupp.maxRealAbs_nonneg
    _ = rexp (1 + 3 * k) * α ^ k *
        Finsupp.maxRealAbs (PrimeGaps.lToY w.lam) * Real.log N ^ k := by rw [mul_pow]; ring

/-- `0 ≤ windowError N q`. -/
lemma windowError_nonneg (N : ℝ) (q : ℕ) : 0 ≤ windowError N q :=
  Nat.primeCountingIocError_nonneg _ _ q

/-- `primorial ⌊D₀ N⌋₊ * (N ^ (θ/2 - δ)) ^ 2 < N ^ θ` for all large `N`: the modulus `W` times the
square of the truncation level stays below the level of distribution `N ^ θ`. -/
lemma primorial_D0_Rsq_lt_Npow {θ δ : ℝ} (hδ0 : 0 < δ) : ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (primorial ⌊PrimeGaps.D₀ N⌋₊ : ℝ) * (N ^ (θ / 2 - δ)) ^ 2 < N ^ θ := by
  have hev : ∀ᶠ N : ℝ in Filter.atTop,
      Real.log (Real.log (Real.log N)) * Real.log 4 < 2 * δ * Real.log N := by
    have hg : Filter.Tendsto (fun t : ℝ ↦ Real.log t / t) Filter.atTop (𝓝 0) := by
      simpa only [pow_one, one_mul, add_zero] using
        Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
    have hcomp : Filter.Tendsto (fun N : ℝ ↦ Real.log (Real.log N) / Real.log N)
        Filter.atTop (𝓝 0) := hg.comp Real.tendsto_log_atTop
    have hbnd : (0 : ℝ) < 2 * δ / Real.log 4 := by
      have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
      positivity
    have hev1 : ∀ᶠ N : ℝ in Filter.atTop, Real.log (Real.log N) / Real.log N < 2 * δ / Real.log 4 :=
      hcomp.eventually (gt_mem_nhds hbnd)
    have hev2 : ∀ᶠ N : ℝ in Filter.atTop, (1 : ℝ) < Real.log N :=
      Real.tendsto_log_atTop.eventually_gt_atTop 1
    have hev3 : ∀ᶠ N : ℝ in Filter.atTop, (1 : ℝ) < Real.log (Real.log N) :=
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 1
    filter_upwards [hev1, hev2, hev3] with N h1 h2 h3
    have hlogN_pos : (0 : ℝ) < Real.log N := by linarith
    have hlog4_pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    have hstep : Real.log (Real.log (Real.log N)) < Real.log (Real.log N) := by
      have := Real.log_lt_sub_one_of_pos (by linarith : (0 : ℝ) < Real.log (Real.log N))
        (by linarith)
      linarith
    rw [div_lt_iff₀ hlogN_pos] at h1
    calc Real.log (Real.log (Real.log N)) * Real.log 4
        < ((2 * δ / Real.log 4) * Real.log N) * Real.log 4 :=
          mul_lt_mul_of_pos_right (by linarith) hlog4_pos
      _ = 2 * δ * Real.log N := by field_simp
  have hevD0 : ∀ᶠ N : ℝ in Filter.atTop, (0 : ℝ) ≤ PrimeGaps.D₀ N := by
    filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
      with N h
    simpa [PrimeGaps.D₀] using Real.log_nonneg h
  have hevN : ∀ᶠ N : ℝ in Filter.atTop, (1 : ℝ) < N := Filter.eventually_gt_atTop 1
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hev.and (hevD0.and hevN))
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨hlog, hD0, hN1⟩ := hN₀ N hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN_pos : (0 : ℝ) < Real.log N := Real.log_pos hN1
  have hW_lt : (primorial ⌊PrimeGaps.D₀ N⌋₊ : ℝ) < N ^ (2 * δ) := by
    refine lt_of_le_of_lt (?_ : _ ≤ (4 : ℝ) ^ (PrimeGaps.D₀ N)) ?_
    · calc (primorial ⌊PrimeGaps.D₀ N⌋₊ : ℝ)
          ≤ ((4 ^ ⌊PrimeGaps.D₀ N⌋₊ : ℕ) : ℝ) := by exact_mod_cast primorial_le_four_pow _
        _ = (4 : ℝ) ^ ((⌊PrimeGaps.D₀ N⌋₊ : ℝ)) := by push_cast; rw [Real.rpow_natCast]
        _ ≤ (4 : ℝ) ^ (PrimeGaps.D₀ N) :=
            (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 4)).mpr (Nat.floor_le hD0)
    · rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_pos_of_pos hN0 _), Real.log_rpow (by norm_num : (0 : ℝ) < 4), Real.log_rpow hN0]
      unfold PrimeGaps.D₀; linarith
  have hSL2 : (N ^ (θ / 2 - δ)) ^ 2 = N ^ (θ - 2 * δ) := by
    rw [← Real.rpow_natCast (N ^ (θ / 2 - δ)) 2, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  calc (primorial ⌊PrimeGaps.D₀ N⌋₊ : ℝ) * (N ^ (θ / 2 - δ)) ^ 2
      < N ^ (2 * δ) * (N ^ (θ / 2 - δ)) ^ 2 :=
        mul_lt_mul_of_pos_right hW_lt (pow_pos (Real.rpow_pos_of_pos hN0 _) 2)
    _ = N ^ θ := by rw [hSL2, ← Real.rpow_add hN0]; ring_nf

/-- `1 ≤ τ r n` for `0 < r` and `0 < n`. -/
lemma tau_pos {r n : ℕ} (hr : 0 < r) (hn : 0 < n) : 1 ≤ τ r n := by
  rw [zeta_pow_eq_tuple_card r n hn, Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
  have hval : ∀ i : Fin r, 1 ≤ (if i = (⟨0, hr⟩ : Fin r) then n else 1) ∧
      (if i = (⟨0, hr⟩ : Fin r) then n else 1) < n + 1 := fun i ↦ by
    by_cases h : i = (⟨0, hr⟩ : Fin r) <;> simp [h] <;> omega
  refine ⟨fun i ↦ if i = (⟨0, hr⟩ : Fin r) then n else 1, Finset.mem_filter.mpr
    ⟨Fintype.mem_piFinset.mpr fun i ↦ Finset.mem_range.mpr (hval i).2, fun i ↦ (hval i).1, ?_⟩⟩
  simp [Finset.prod_ite_eq' Finset.univ (⟨0, hr⟩ : Fin r) (fun _ ↦ n)]

/-- `Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) = Nat.lcm a b` for `0 < a`. -/
lemma gcd_split_eq_lcm {a b : ℕ} (ha : 0 < a) :
    Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) = Nat.lcm a b := by
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left a b),
    ← Nat.mul_div_assoc _ (Nat.gcd_dvd_right a b), ← Nat.gcd_mul_lcm a b,
    Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_left b ha)]

/-- At most `τ (3 * k) q` pairs `(d, e) ∈ S ×ˢ S` share a given modulus `qMod W d e = q`, by
splitting each coordinate as `gcd`, `dᵢ/gcd`, `eᵢ/gcd`. -/
lemma fiber_card_le_tau {k : ℕ} (hk : 0 < k) (W : ℕ) (hWpos : 0 < W) (S : Finset (Fin k → ℕ))
    (hS : ∀ d ∈ S, (∀ i, 0 < d i) ∧ Nat.Coprime (∏ i, d i) W) (q : ℕ) :
    #{p ∈ (S ×ˢ S) | PrimeGaps.qMod W p.1 p.2 = q} ≤
      τ (3 * k) q := by
  classical
  set Fib := {p ∈ (S ×ˢ S) | PrimeGaps.qMod W p.1 p.2 = q} with hFibdef
  rcases Finset.eq_empty_or_nonempty Fib with hemp | ⟨p₀, hp₀⟩
  · simp [hemp]
  have hcoord : ∀ p ∈ Fib, (∀ i, 0 < p.1 i) ∧ (∀ i, 0 < p.2 i) ∧
      (∀ i, Nat.Coprime (p.1 i) W) ∧ (∀ i, Nat.Coprime (p.2 i) W) := by
    intro p hp
    rw [hFibdef, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, _⟩ := hp
    obtain ⟨hd1, hdcop⟩ := hS p.1 hp1
    obtain ⟨he1, hecop⟩ := hS p.2 hp2
    exact ⟨hd1, he1, fun i ↦ hdcop.coprime_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)),
      fun i ↦ hecop.coprime_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))⟩
  have hqOf : ∀ p ∈ Fib, W * ∏ i, Nat.lcm (p.1 i) (p.2 i) = q := by
    intro p hp
    rw [hFibdef, Finset.mem_filter] at hp
    simpa [PrimeGaps.qMod] using hp.2
  obtain ⟨hd0pos, he0pos, hd0cop, he0cop⟩ := hcoord p₀ hp₀
  set m := ∏ i, Nat.lcm (p₀.1 i) (p₀.2 i)
  have hmpos : 0 < m := Finset.prod_pos fun i _ ↦ Nat.lcm_pos (hd0pos i) (he0pos i)
  have hqval : q = W * m := (hqOf p₀ hp₀).symm
  have hWm_cop : Nat.Coprime W m :=
    (Nat.Coprime.prod_left fun i _ ↦ Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _)
      ((hd0cop i).mul_left (he0cop i))).symm
  have h3k : 0 < 3 * k := by omega
  have htau_mono : τ (3 * k) m ≤ τ (3 * k) q := by
    rw [hqval, (ArithmeticFunction.isMultiplicative_zeta.pow (k := 3 * k)).map_mul_of_coprime
      hWm_cop]
    exact Nat.le_mul_of_pos_left _ (tau_pos h3k hWpos)
  refine le_trans ?_ htau_mono
  set T : Finset (Fin (3 * k) → ℕ) :=
    (Fintype.piFinset (fun _ : Fin (3 * k) ↦ Finset.range (m + 1))).filter
      (fun a : Fin (3 * k) → ℕ ↦ (∀ i, 1 ≤ a i) ∧ (∏ i, a i) = m) with hTdef
  rw [zeta_pow_eq_tuple_card (3 * k) m hmpos]
  change #Fib ≤ #T
  set eqv : Fin 3 × Fin k ≃ Fin (3 * k) := finProdFinEquiv
  set slot : Fin 3 → ℕ → ℕ → ℕ := fun s a b ↦
    if s = 0 then Nat.gcd a b else if s = 1 then a / Nat.gcd a b else b / Nat.gcd a b
    with hslot
  set Φ : ((Fin k → ℕ) × (Fin k → ℕ)) → (Fin (3 * k) → ℕ) := fun p j ↦
    slot (eqv.symm j).1 (p.1 (eqv.symm j).2) (p.2 (eqv.symm j).2) with hΦ
  apply Finset.card_le_card_of_injOn Φ
  · intro p hp
    obtain ⟨hp1pos, hp2pos, _, _⟩ := hcoord p hp
    have hpair_prod : (∏ j, Φ p j) = ∏ x : Fin 3 × Fin k, slot x.1 (p.1 x.2) (p.2 x.2) :=
      (Fintype.prod_equiv eqv _ (Φ p) fun x ↦ by simp [hΦ, Equiv.symm_apply_apply]).symm
    have hcoordlcm : ∀ i, slot 0 (p.1 i) (p.2 i) * slot 1 (p.1 i) (p.2 i) *
        slot 2 (p.1 i) (p.2 i) = Nat.lcm (p.1 i) (p.2 i) := fun i ↦ by
      simpa [hslot] using gcd_split_eq_lcm (hp1pos i)
    have hprodm : (∏ j, Φ p j) = ∏ i, Nat.lcm (p.1 i) (p.2 i) := by
      rw [hpair_prod, Fintype.prod_prod_type' (fun a b ↦ slot a (p.1 b) (p.2 b)),
        Finset.prod_comm]
      exact Finset.prod_congr rfl fun i _ ↦ (Fin.prod_univ_three _).trans (hcoordlcm i)
    have hprodq : ∏ i, Nat.lcm (p.1 i) (p.2 i) = m :=
      Nat.eq_of_mul_eq_mul_left hWpos (by rw [hqOf p hp, hqval])
    have hΦprod : (∏ j, Φ p j) = m := by rw [hprodm, hprodq]
    have hslotpos : ∀ j, 1 ≤ Φ p j := by
      intro j
      simp only [hΦ, hslot]
      set i := (eqv.symm j).2
      have hgi : 0 < Nat.gcd (p.1 i) (p.2 i) := Nat.gcd_pos_of_pos_left _ (hp1pos i)
      split_ifs
      · exact hgi
      · exact (Nat.one_le_div_iff hgi).mpr (Nat.le_of_dvd (hp1pos i) (Nat.gcd_dvd_left _ _))
      · exact (Nat.one_le_div_iff hgi).mpr (Nat.le_of_dvd (hp2pos i) (Nat.gcd_dvd_right _ _))
    simp only [hTdef, Finset.coe_filter, Set.mem_ofPred_eq]
    refine ⟨Fintype.mem_piFinset.mpr fun j ↦ Finset.mem_range.mpr ?_, hslotpos, hΦprod⟩
    have hdvd : Φ p j ∣ m := hΦprod ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have := Nat.le_of_dvd hmpos hdvd
    omega
  · intro p hp p' hp' hΦeq
    have hslot_eq : ∀ (s : Fin 3) (i : Fin k),
        slot s (p.1 i) (p.2 i) = slot s (p'.1 i) (p'.2 i) := fun s i ↦ by
      simpa only [hΦ, Equiv.symm_apply_apply] using congrFun hΦeq (eqv (s, i))
    have hcoords : ∀ i, p.1 i = p'.1 i ∧ p.2 i = p'.2 i := by
      intro i
      have hg := hslot_eq 0 i
      have ha := hslot_eq 1 i
      norm_num [hslot] at hg ha
      have hb : p.2 i / Nat.gcd (p.1 i) (p.2 i) = p'.2 i / Nat.gcd (p'.1 i) (p'.2 i) := by
        simpa [hslot, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
          using hslot_eq 2 i
      -- rebuild each coordinate as `gcd * (coordinate / gcd)` and transport along `hg`, `ha`, `hb`
      exact ⟨by rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left (p.1 i) (p.2 i)),
          ← Nat.mul_div_cancel' (Nat.gcd_dvd_left (p'.1 i) (p'.2 i)), ha, hg],
        by rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_right (p.1 i) (p.2 i)),
          ← Nat.mul_div_cancel' (Nat.gcd_dvd_right (p'.1 i) (p'.2 i)), hb, hg]⟩
    ext i
    · exact (hcoords i).1
    · exact (hcoords i).2

/-- Regrouping the double weight sum by the modulus `q = qMod W d e`: the gated error is at most
`C₃ * lamBound ^ 2 * ∑_{1 ≤ q ≤ N ^ θq} τ (3 * k) q ^ 2 * windowError X q`. -/
lemma collapse_to_modulus_sum_of_pair_bound_with_bound {k : ℕ} (hk : 0 < k) (θs δs θq : ℝ) :
    ∃ (C₃ N₃ : ℝ), 0 < C₃ ∧ ∀ (N : ℝ), N₃ ≤ N → ∀ (w : SieveWeights k N θs δs), ∀ lamBound : ℝ,
      (∀ (d : Fin k → ℕ), |w.lam d| ≤ lamBound) →
      ∀ (X : ℝ) (W : ℕ), 0 < W →
      (∀ d, w.lam d ≠ 0 → Nat.Coprime (∏ i, d i) W) →
      ∀ (gate : (Fin k → ℕ) → (Fin k → ℕ) → Prop) [DecidableRel gate],
      (∀ d e, gate d e → w.lam d ≠ 0 → w.lam e ≠ 0 → (PrimeGaps.qMod W d e : ℝ) < N ^ θq) →
      gatedErrorContribution X W w.lam gate ≤ C₃ * lamBound ^ 2 *
          (∑ q ∈ {q ∈ (Finset.range (⌊N ^ θq⌋₊ + 1)) | 1 ≤ q},
            (τ (3 * k) q : ℝ) ^ 2 * windowError X q) := by
  -- Each `q` receives at most `τ_{3k}(q)` pairs; `|λ||λ| ≤ λ_max²`; `E ≥ 1`.
  classical
  refine ⟨1, 1, one_pos, ?_⟩
  intro N _ w lamBound hlam_w X W hWpos hcop gate _inst hmod
  have hlam_nn : 0 ≤ lamBound := (abs_nonneg _).trans (hlam_w fun _ ↦ 1)
  -- The finite support Finset S.
  set S : Finset (Fin k → ℕ) := (totalErrorContribution_finite_support w).toFinset
  have hS_mem : ∀ d, d ∈ S ↔ w.lam d ≠ 0 := fun _ ↦ Set.Finite.mem_toFinset _
  have hS_supp : ∀ d ∈ S, (∀ i, 0 < d i) ∧ Nat.Coprime (∏ i, d i) W := by
    intro d hd
    have hd0 := (hS_mem d).mp hd
    have hdmem := w.support (Finsupp.mem_support_iff.mpr hd0)
    exact ⟨fun i ↦ Nat.pos_of_ne_zero (Finset.squarefree_of_mem_permissibleSupport hdmem i).ne_zero,
      hcop d hd0⟩
  -- Stage 1 (Sub-lemma B): collapse the double tsum to a finite Finset double sum.
  have hstep1 : gatedErrorContribution X W w.lam gate =
      ∑ p ∈ {p ∈ (S ×ˢ S) | gate p.1 p.2},
        |w.lam p.1| * |w.lam p.2| * windowError X (PrimeGaps.qMod W p.1 p.2) := by
    unfold gatedErrorContribution
    rw [Finset.sum_filter, Finset.sum_product' (s := S) (t := S) (f := fun d e ↦ if gate d e then
        |w.lam d| * |w.lam e| * windowError X (PrimeGaps.qMod W d e) else 0)]
    -- Outer tsum over d collapses to a sum over S.
    rw [tsum_eq_sum (s := S) ?_]
    · -- For each d in S, the inner tsum over e collapses to a sum over S too.
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [tsum_eq_sum (s := S) ?_]
      · refine Finset.sum_congr rfl fun e he ↦ ?_
        by_cases hg : gate d e
        · rw [if_pos ⟨hg, mul_ne_zero ((hS_mem d).mp hd) ((hS_mem e).mp he)⟩, if_pos hg]
        · rw [if_neg (fun h ↦ hg h.1), if_neg hg]
      · -- off-S terms vanish for the inner sum
        intro e he
        rw [if_neg (by simp [not_not.mp fun h ↦ he ((hS_mem e).mpr h)])]
    · -- off-S terms vanish for the outer sum
      intro d hd
      simp [not_not.mp fun h ↦ hd ((hS_mem d).mpr h)]
  rw [hstep1]
  -- Stage 2a (Sub-lemma C): every contributing pair has q ∈ filtered range.
  have hstep2 : ∀ p ∈ {p ∈ (S ×ˢ S) | gate p.1 p.2}, PrimeGaps.qMod W p.1 p.2 ∈
        {q ∈ (Finset.range (⌊N ^ θq⌋₊ + 1)) | 1 ≤ q} := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hgate⟩ := hp
    obtain ⟨hd1, _⟩ := hS_supp p.1 hp1
    obtain ⟨he1, _⟩ := hS_supp p.2 hp2
    have hcm_pos : 0 < PrimeGaps.qMod W p.1 p.2 := by
      unfold PrimeGaps.qMod
      exact Nat.mul_pos hWpos (Finset.prod_pos fun i _ ↦ Nat.lcm_pos (hd1 i) (he1 i))
    have hcm_real : (PrimeGaps.qMod W p.1 p.2 : ℝ) < N ^ θq :=
      hmod p.1 p.2 hgate ((hS_mem p.1).mp hp1) ((hS_mem p.2).mp hp2)
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor hcm_real.le), hcm_pos⟩
  -- Stage 2b: regroup by `q = qMod W d e` (fiberwise sum).
  rw [← Finset.sum_fiberwise_of_maps_to hstep2
        (g := fun p : (Fin k → ℕ) × (Fin k → ℕ) ↦ PrimeGaps.qMod W p.1 p.2)]
  -- Stage 2c+2d: bound the fiber sum for each q, then sum over q.
  rw [one_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  set F := {p ∈ {p ∈ (S ×ˢ S) | gate p.1 p.2} | PrimeGaps.qMod W p.1 p.2 = q} with hF
  have hE_nn : 0 ≤ windowError X q := windowError_nonneg X q
  have hconst_nn : 0 ≤ lamBound * lamBound * windowError X q :=
    mul_nonneg (mul_nonneg hlam_nn hlam_nn) hE_nn
  -- Fiber card ≤ τ_{3k}(q) ≤ τ_{3k}(q)² (Sub-lemma E; the square avoids needing τ ≥ 1).
  have hfiber : (#F : ℝ) ≤ (τ (3 * k) q : ℝ) ^ 2 := by
    have hsub : F ⊆ {p ∈ (S ×ˢ S) | PrimeGaps.qMod W p.1 p.2 = q} := by
      rw [hF]
      intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1.1, hp.2⟩
    exact_mod_cast (Finset.card_le_card hsub).trans
      ((fiber_card_le_tau hk W hWpos S hS_supp q).trans (Nat.le_self_pow (by norm_num) _))
  -- On the q-fiber `windowError` is constant, and each weight is at most `lamBound`.
  calc ∑ p ∈ F, |w.lam p.1| * |w.lam p.2| * windowError X (PrimeGaps.qMod W p.1 p.2)
      ≤ ∑ p ∈ F, lamBound * lamBound * windowError X q := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        rw [hF, Finset.mem_filter] at hp
        rw [hp.2]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hlam_w p.1) (hlam_w p.2) (abs_nonneg _) hlam_nn) hE_nn
    _ = (#F : ℝ) * (lamBound * lamBound * windowError X q) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (τ (3 * k) q : ℝ) ^ 2 * (lamBound * lamBound * windowError X q) :=
        mul_le_mul_of_nonneg_right hfiber hconst_nn
    _ = lamBound ^ 2 * ((τ (3 * k) q : ℝ) ^ 2 * windowError X q) := by ring

/-- Compatibility wrapper using the standard `Finsupp.maxRealAbs · log^k` pointwise bound. -/
lemma collapse_to_modulus_sum_of_pair_bound {k : ℕ} (hk : 0 < k) (θs δs θq : ℝ) (C₁ : ℝ) (N₁ : ℝ)
    (hlam : ∀ (N' : ℝ), N₁ ≤ N' → ∀ (w : SieveWeights k N' θs δs), ∀ (d : Fin k → ℕ), |w.lam d| ≤
          C₁ * (PrimeGaps.lToY w.lam).maxRealAbs * (Real.log N') ^ k) :
    ∃ (C₃ N₃ : ℝ), 0 < C₃ ∧ ∀ (N : ℝ), N₃ ≤ N → ∀ (w : SieveWeights k N θs δs),
      ∀ (X : ℝ) (W : ℕ), 0 < W →
      (∀ d, w.lam d ≠ 0 → Nat.Coprime (∏ i, d i) W) →
      ∀ (gate : (Fin k → ℕ) → (Fin k → ℕ) → Prop) [DecidableRel gate],
      (∀ d e, gate d e → w.lam d ≠ 0 → w.lam e ≠ 0 → (PrimeGaps.qMod W d e : ℝ) < N ^ θq) →
      gatedErrorContribution X W w.lam gate ≤ C₃ *
          (C₁ * (PrimeGaps.lToY w.lam).maxRealAbs * (Real.log N) ^ k) ^ 2 *
          (∑ q ∈ {q ∈ (Finset.range (⌊N ^ θq⌋₊ + 1)) | 1 ≤ q},
            (τ (3 * k) q : ℝ) ^ 2 * windowError X q) := by
  obtain ⟨C₃, N₃, hC₃, hc⟩ := collapse_to_modulus_sum_of_pair_bound_with_bound hk θs δs θq
  refine ⟨C₃, max N₃ N₁, hC₃, ?_⟩
  intro N hN w X W hWpos hcop gate _inst hmod
  exact hc N ((le_max_left _ _).trans hN) w
    (C₁ * (PrimeGaps.lToY w.lam).maxRealAbs * Real.log N ^ k)
    (hlam N ((le_max_right _ _).trans hN) w) X W hWpos hcop gate hmod

/-- Compatibility form of the modulus collapse, deriving the pair bound from the
usual common sieve support `R = N^(θ/2-δ)`. -/
lemma collapse_to_modulus_sum {k : ℕ} (hk : 0 < k) (θ δ : ℝ) (hδ0 : 0 < δ) (C₁ : ℝ) (N₁ : ℝ)
    (hlam : ∀ (N' : ℝ), N₁ ≤ N' → ∀ (w : SieveWeights k N' θ δ),
      ∀ d, |w.lam d| ≤ C₁ * (PrimeGaps.lToY w.lam).maxRealAbs * (Real.log N') ^ k) :
    ∃ (C₃ N₃ : ℝ), 0 < C₃ ∧ ∀ (N : ℝ), N₃ ≤ N → ∀ (w : SieveWeights k N θ δ),
      totalErrorContribution w ≤ C₃ *
          (C₁ * (PrimeGaps.lToY w.lam).maxRealAbs * (Real.log N) ^ k) ^ 2 *
          (∑ q ∈ {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q},
            (τ (3 * k) q : ℝ) ^ 2 * windowError N q) := by
  obtain ⟨Nmod, hWR⟩ := primorial_D0_Rsq_lt_Npow (θ := θ) (δ := δ) hδ0
  have hpair : ∀ (N : ℝ), max Nmod 1 ≤ N → ∀ (w : SieveWeights k N θ δ),
      ∀ d e, True → w.lam d ≠ 0 → w.lam e ≠ 0 →
        (PrimeGaps.qMod (primorial ⌊PrimeGaps.D₀ N⌋₊) d e : ℝ) < N ^ θ := by
    intro N hN w d e _ hd he
    have hNmod : Nmod ≤ N := (le_max_left _ _).trans hN
    have hN1 : (1 : ℝ) ≤ N := (le_max_right _ _).trans hN
    have hdmem := w.support (Finsupp.mem_support_iff.mpr hd)
    have hemel := w.support (Finsupp.mem_support_iff.mpr he)
    have hd1 : ∀ i, 1 ≤ d i := fun i ↦ Nat.one_le_iff_ne_zero.mpr
      (Finset.squarefree_of_mem_permissibleSupport hdmem i).ne_zero
    have he1 : ∀ i, 1 ≤ e i := fun i ↦ Nat.one_le_iff_ne_zero.mpr
      (Finset.squarefree_of_mem_permissibleSupport hemel i).ne_zero
    have hdR : ((∏ i, d i : ℕ) : ℝ) ≤ N ^ (θ / 2 - δ) := le_trans
      (by exact_mod_cast (Finset.mem_permissibleSupport_iff.mp hdmem).1)
      (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hN1) _))
    have heR : ((∏ i, e i : ℕ) : ℝ) ≤ N ^ (θ / 2 - δ) := le_trans
      (by exact_mod_cast (Finset.mem_permissibleSupport_iff.mp hemel).1)
      (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hN1) _))
    have hlcm :
        ((∏ i, Nat.lcm (d i) (e i) : ℕ) : ℝ) ≤ ((∏ i, d i : ℕ) : ℝ) * ((∏ i, e i : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, Nat.cast_le, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        fun i _ ↦ Nat.lcm_le_mul (hd1 i) (he1 i)
    have hprod : ((∏ i, d i : ℕ) : ℝ) * ((∏ i, e i : ℕ) : ℝ) ≤ (N ^ (θ / 2 - δ)) ^ 2 := by
      rw [pow_two]
      exact mul_le_mul hdR heR (by positivity) (Real.rpow_nonneg (by linarith) _)
    unfold PrimeGaps.qMod
    rw [Nat.cast_mul]
    calc (primorial ⌊PrimeGaps.D₀ N⌋₊ : ℝ) * ((∏ i, Nat.lcm (d i) (e i) : ℕ) : ℝ)
        ≤ (primorial ⌊PrimeGaps.D₀ N⌋₊ : ℝ) * (N ^ (θ / 2 - δ)) ^ 2 := by
          gcongr
          exact hlcm.trans hprod
      _ < N ^ θ := hWR N hNmod
  obtain ⟨C₃, N₃, hC₃, hb⟩ := collapse_to_modulus_sum_of_pair_bound hk θ δ θ C₁ N₁ hlam
  refine ⟨C₃, max N₃ (max Nmod 1), hC₃, fun N hN w ↦ ?_⟩
  have hN3 : N₃ ≤ N := (le_max_left _ _).trans hN
  have hNm : max Nmod 1 ≤ N := (le_max_right _ _).trans hN
  have hcop : ∀ d, w.lam d ≠ 0 → Nat.Coprime (∏ i, d i) (primorial ⌊PrimeGaps.D₀ N⌋₊) :=
    fun d hd ↦ (Finset.mem_permissibleSupport_iff.mp
      (w.support (Finsupp.mem_support_iff.mpr hd))).2.1
  simpa [gatedErrorContribution, totalErrorContribution] using
    hb N hN3 w N (primorial ⌊PrimeGaps.D₀ N⌋₊) (primorial_pos _) hcop
      (fun _ _ ↦ True) (hpair N hNm w)

end MaynardS2Error
