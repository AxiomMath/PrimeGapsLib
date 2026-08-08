/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.SijD0.FirstMoment
public import PrimeGapsTheory.Sieve.S1.SijOne

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The first moment in transformed weights

Transfers the first-moment estimate from the primed sum to the transformed weight sum.

## Main results

* `lem_S1_from_y`: Approximates the first moment by the transformed weight sum.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

open GPYSieveS1 PrimeGaps.LemS1RestrictSij

namespace PrimeGaps

/-- If `lam` is supported on tuples with product `≤ R` (coprime, squarefree, positive) and `r` has
product exceeding `R`, then `PrimeGaps.lToY lam r = 0`, because the inner sum ranges over `d` with
`rᵢ ∣ dᵢ` and `∏ dᵢ ≤ R`, which is empty.
-/
lemma yWeight_eq_zero_of_prod_gt {k : ℕ} {R : ℝ} {W : ℕ} {lam : (Fin k → ℕ) →₀ ℝ}
    (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W) {r : Fin k → ℕ}
    (hR : R < ∏ i, (r i : ℝ)) : PrimeGaps.lToY lam r = 0 := by
  by_contra hne
  have hsY := hlam.lToY
  have hprod := hsY.prod_lt_R_of_ne_zero hne
  have hfloorle : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le (Nat.pos_of_floor_pos (lt_of_lt_of_le
    (Finset.prod_pos fun i _ ↦ Nat.pos_of_ne_zero (hsY.ne_zero_of_ne_zero hne i)) hprod)).le
  have hprod' : (∏ i, (r i : ℝ)) ≤ (⌊R⌋₊ : ℝ) := by
    rw [← Nat.cast_prod]; exact_mod_cast hprod
  exact absurd hR (not_lt_of_ge (hprod'.trans hfloorle))

/-- For fixed `u` (all entries `≥ 1`) and `s` with off-diagonal entries `≥ 1`, if
`PrimeGaps.lToY lam (boldA u s) ≠
  0` then every off-diagonal `s i j` is bounded by `⌊R⌋₊` and every `u i`
is bounded by `⌊R⌋₊`.
-/
lemma bound_of_yWeightA_ne {k : ℕ} {R : ℝ} {W : ℕ} {lam : (Fin k → ℕ) →₀ ℝ}
    (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W) {u : Fin k → ℕ} {s : Fin k → Fin k → ℕ}
    (hu : ∀ i, 1 ≤ u i) (hs : ∀ i j, i ≠ j → 1 ≤ s i j)
    (hne : PrimeGaps.lToY lam (boldA u s) ≠ 0) :
    (∀ i, u i ≤ ⌊R⌋₊) ∧ (∀ i j, i ≠ j → s i j ≤ ⌊R⌋₊) := by
  have hbA1 : ∀ j, 1 ≤ boldA u s j := fun j ↦ by
    unfold boldA
    have hp : 1 ≤ ∏ i ∈ Finset.univ.erase j, s j i :=
      Finset.one_le_prod' fun i hi ↦ hs j i fun h ↦ (Finset.mem_erase.mp hi).1 h.symm
    simpa using Nat.mul_le_mul (hu j) hp
  have hprodle : (∏ j, (boldA u s j : ℝ)) ≤ R :=
    not_lt.mp fun hgt ↦ hne (yWeight_eq_zero_of_prod_gt hlam hgt)
  have hbAle : ∀ j, (boldA u s j : ℝ) ≤ R := fun j ↦ by
    have hj : boldA u s j ≤ ∏ i, boldA u s i :=
      Finset.single_le_prod' (f := fun i ↦ boldA u s i) (fun i _ ↦ hbA1 i) (Finset.mem_univ j)
    exact le_trans (by exact_mod_cast hj) hprodle
  refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · exact Nat.le_floor
      (le_trans (by exact_mod_cast Nat.le_of_dvd (hbA1 i) ⟨_, rfl⟩) (hbAle i))
  · have hdvd : s i j ∣ boldA u s i := by
      unfold boldA
      exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (f := fun a ↦ s i a)
        (Finset.mem_erase.mpr ⟨fun h ↦ hij h.symm, Finset.mem_univ j⟩)) _
    exact Nat.le_floor (le_trans (by exact_mod_cast Nat.le_of_dvd (hbA1 i) hdvd) (hbAle i))

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- **The `D₀`-truncated double sum collapses to the diagonal.**  If every off-diagonal `s i j` is
at most `⌊D₀ N⌋₊` and both `y` -weights `lToY lam (boldA u s)`, `lToY lam (boldB u s)` are nonzero,
then `lem_S1_sij_dichotomy` forces `s i j = 1`; so only the term `s ≡ 1` survives, and it is exactly
the diagonal summand. -/
private theorem tsum_truncated_eq_diag {k : ℕ} (θ δ : ℝ) (N : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hlam : lam.HasPermissibleSupport ⌊R⌋₊ (W N))
    (D0 : (Fin k → ℕ) × (Fin k → Fin k → ℕ) → ℝ)
    (hD0 : ∀ p, D0 p = if ((∀ i, 1 ≤ p.1 i) ∧ (∀ i, p.2 i i = 1) ∧
              (∀ i j, i ≠ j → 1 ≤ p.2 i j) ∧ RestrictedCoprime p.1 p.2) ∧
            ¬ (∃ i j, i ≠ j ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < p.2 i j) then
          ((∏ i, (μ (p.1 i) : ℝ) ^ 2 / (p.1 i).totient) *
              ∏ q ∈ Finset.univ.offDiag,
                (μ (p.2 q.1 q.2) : ℝ) / (p.2 q.1 q.2).totient ^ 2) *
            PrimeGaps.lToY lam (boldA p.1 p.2) * PrimeGaps.lToY lam (boldB p.1 p.2)
        else 0)
    (hD0summ : Summable D0) (hD0floor : 1 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊) :
    (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) then
        (∏ i, (μ (u i) : ℝ) ^ 2 / (u i).totient) *
          PrimeGaps.lToY lam u * PrimeGaps.lToY lam u else 0) = ∑' p, D0 p := by
  classical
  have hbAone : ∀ u : Fin k → ℕ, boldA u (fun _ _ ↦ 1) = u := by
    intro u; unfold boldA; funext j; simp
  have hbBone : ∀ u : Fin k → ℕ, boldB u (fun _ _ ↦ 1) = u := by
    intro u; unfold boldB; funext j; simp
  have hprodone : (∏ p ∈ (Finset.univ : Finset (Fin k)).offDiag,
      (μ ((fun _ _ ↦ 1 : Fin k → Fin k → ℕ) p.1 p.2) : ℝ) /
        ((fun _ _ ↦ 1 : Fin k → Fin k → ℕ) p.1 p.2).totient ^ 2) = 1 := by
    simp
  rw [hD0summ.tsum_prod]
  refine tsum_congr fun u ↦ ?_
  rw [tsum_eq_single (fun _ _ ↦ 1) ?_]
  · rw [hD0]
    simp only
    split_ifs with h1 h2 h2
    · rw [hbAone u, hbBone u, hprodone]; ring
    · refine absurd ?_ h2
      refine ⟨⟨h1.1, by simp, by simp, h1.2⟩, ?_⟩
      rintro ⟨i, j, -, hlt⟩
      omega
    · exact absurd ⟨h2.1.1, h2.1.2.2.2⟩ h1
    · rfl
  · intro s hs
    rw [hD0]
    simp only
    by_cases hguard : ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
        RestrictedCoprime u s) ∧
        ¬ (∃ i j, i ≠ j ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s i j)
    · rw [if_pos hguard]
      obtain ⟨⟨-, hdiags, hposs, -⟩, hnPs⟩ := hguard
      by_contra hFne
      have hboth : PrimeGaps.lToY lam (boldA u s) ≠ 0 ∧ PrimeGaps.lToY lam (boldB u s) ≠ 0 :=
        ⟨fun hz ↦ hFne (by rw [hz]; ring), fun hz ↦ hFne (by rw [hz]; ring)⟩
      apply hs
      funext i j
      by_cases hij : i = j
      · subst hij; exact hdiags i
      · rcases lem_S1_sij_dichotomy N R (W N) PrimeGaps.W_eq_primorial_D₀ lam hlam
            u s hboth i j hij with hsij1 | hprimes
        · exact hsij1
        · have h1le : 1 ≤ s i j := hposs i j hij
          rcases Nat.lt_or_ge 1 (s i j) with hgt | hle
          · obtain ⟨q, hq, hqdvd⟩ := (s i j).exists_prime_and_dvd (by omega)
            have hqbig : ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < q := hprimes q hq hqdvd
            have hqle : q ≤ s i j := Nat.le_of_dvd (by omega) hqdvd
            exact absurd ⟨i, j, hij, by omega⟩ hnPs
          · omega
    · rw [if_neg hguard]

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Maynard Lemma 5.1: the sieve sum `S₁ h lam N W v0` equals the diagonal main term
`(N/W) · ∑ᵤ PrimeGaps.lToY lam u ² /
  ∏ᵢ φ(uᵢ)` (over restricted-coprime diagonal tuples) up to an error
bounded by `C · Finsupp.maxRealAbs (PrimeGaps.lToY lam) ² · φ(W)^k · N · (log R)^k /
  (W^{k+1} · D₀)`, for all sufficiently large
`N`.
-/
@[pg_tag "bg246" "lem_S1_from_y"]
theorem lem_S1_from_y {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h) :
    ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    ∀ lam : (Fin k → ℕ) →₀ ℝ, lam.HasPermissibleSupport ⌊R⌋₊ (W N) →
    ∀ v0 : ℕ, V0Valid h (W N) v0 →
      |S1 h lam N (W N) v0 - (N / (W N : ℝ)) *
        (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) then
                  PrimeGaps.lToY lam u ^ 2 / (∏ i, (Nat.totient (u i) : ℝ)) else 0)| ≤
        C * (Finsupp.maxRealAbs (PrimeGaps.lToY lam)) ^ 2 * (Nat.totient (W N) : ℝ) ^ k * N *
          (Real.log (R)) ^ k /
            ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  intro θ δ hθ hδ
  obtain ⟨C₁, hC₁, N₁, H₁⟩ := lem_S1_substitute_y hk h hadm θ δ hθ hδ
  obtain ⟨C₂, hC₂, N₂, H₂⟩ := PrimeGaps.lem_S1_sij_D0 hk θ δ hθ hδ
  obtain ⟨N₃, HN₃⟩ : ∃ N₃ : ℝ, ∀ N : ℕ, N₃ ≤ (N : ℝ) → 1 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ := by
    obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp PrimeGaps.D0_tendsto_atTop 1
    exact ⟨M, fun N hN ↦ Nat.le_floor (by exact_mod_cast hM _ hN)⟩
  refine ⟨C₁ + C₂, by positivity, max (max N₁ N₂) N₃, fun N hN lam hlam v0 hv0 ↦ ?_⟩
  have hN₁ : N₁ ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂ : N₂ ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₃ : N₃ ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  have hD0floor : 1 ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ := HN₃ N hN₃
  have E1 := H₁ N hN₁ lam hlam v0 hv0
  have E2 := H₂ N hN₂ lam hlam
  set Wt := W N with hW
  set MT : ℝ := ∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) then
        PrimeGaps.lToY lam u ^ 2 / (∏ i, (Nat.totient (u i) : ℝ)) else 0
  set OFF : ℝ := ∑' (u : Fin k → ℕ) (s : Fin k → Fin k → ℕ), if (∀ (i : Fin k), 1 ≤ u i) ∧
          (∀ (i : Fin k), s i i = 1) ∧ (∀ (i j : Fin k), i ≠ j → 1 ≤ s i j) ∧
              RestrictedCoprime u s ∧ ∃ i j, i ≠ j ∧ ⌊PrimeGaps.D₀ ↑N⌋₊ < s i j then
        ((∏ i, (μ (u i) : ℝ) ^ 2 / (u i).totient) *
              ∏ p ∈ Finset.univ.offDiag,
                (μ (s p.1 p.2) : ℝ) / (s p.1 p.2).totient ^ 2) *
            PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s) else 0 with hOFF
  set DIAG : ℝ := ∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) then
        (∏ i, (μ (u i) : ℝ) ^ 2 / (u i).totient) *
          PrimeGaps.lToY lam u * PrimeGaps.lToY lam u else 0 with hDIAG
  have hsijone : (N : ℝ) / Wt * DIAG = (N : ℝ) / Wt * MT := lem_S1_sij_one N Wt lam
  set G : (Fin k → ℕ) → (Fin k → Fin k → ℕ) → Prop :=
    fun u s ↦ (∀ (i : Fin k), 1 ≤ u i) ∧ (∀ (i : Fin k), s i i = 1) ∧
      (∀ (i j : Fin k), i ≠ j → 1 ≤ s i j) ∧ RestrictedCoprime u s with hG
  set P : (Fin k → ℕ) → (Fin k → Fin k → ℕ) → Prop :=
    fun u s ↦ ∃ i j, i ≠ j ∧ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ < s i j with hP
  set Fexpr : (Fin k → ℕ) → (Fin k → Fin k → ℕ) → ℝ :=
    fun u s ↦ ((∏ i, (μ (u i) : ℝ) ^ 2 / (u i).totient) *
        ∏ p ∈ Finset.univ.offDiag,
          (μ (s p.1 p.2) : ℝ) / (s p.1 p.2).totient ^ 2) *
      PrimeGaps.lToY lam (boldA u s) * PrimeGaps.lToY lam (boldB u s) with hFexpr
  set F0 : (Fin k → ℕ) × (Fin k → Fin k → ℕ) → ℝ :=
    fun p ↦ if G p.1 p.2 then Fexpr p.1 p.2 else 0 with hF0
  set D0 : (Fin k → ℕ) × (Fin k → Fin k → ℕ) → ℝ :=
    fun p ↦ if G p.1 p.2 ∧ ¬ P p.1 p.2 then Fexpr p.1 p.2 else 0 with hD0
  set O0 : (Fin k → ℕ) × (Fin k → Fin k → ℕ) → ℝ :=
    fun p ↦ if G p.1 p.2 ∧ P p.1 p.2 then Fexpr p.1 p.2 else 0 with hO0
  let B := ⌊R⌋₊
  let box : Finset ((Fin k → ℕ) × (Fin k → Fin k → ℕ)) :=
    (Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B)) ×ˢ
      (Fintype.piFinset (fun _ : Fin k ↦ Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 0 B)))
  have hsuppF0 : ∀ p, F0 p ≠ 0 → (∀ i, p.1 i ≤ B) ∧ (∀ i j, i ≠ j → p.2 i j ≤ B) := by
    intro p hp0
    rw [hF0] at hp0
    simp only at hp0
    by_cases hGp : G p.1 p.2
    · rw [if_pos hGp] at hp0
      obtain ⟨hu, -, hspos, -⟩ := hGp
      exact bound_of_yWeightA_ne hlam hu hspos fun hz ↦ hp0 (by
        rw [hFexpr]; simp only; rw [hz]; ring)
    · rw [if_neg hGp] at hp0; exact absurd rfl hp0
  have hF0summ : Summable F0 := by
    refine summable_of_ne_finset_zero (s := box) fun p hp ↦ ?_
    by_contra hne
    apply hp
    obtain ⟨hb1, hb2⟩ := hsuppF0 p hne
    have hGp : G p.1 p.2 := by
      by_contra hG'
      exact hne (by rw [hF0]; simp only; rw [if_neg hG'])
    obtain ⟨hu1, hdiag, -, -⟩ := hGp
    have hB1 : 1 ≤ B := le_trans (hu1 ⟨0, by omega⟩) (hb1 ⟨0, by omega⟩)
    refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦
      Finset.mem_Icc.mpr ⟨hu1 i, hb1 i⟩, Fintype.mem_piFinset.mpr fun i ↦
        Fintype.mem_piFinset.mpr fun j ↦ Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩⟩
    by_cases hij : i = j
    · subst hij; rw [hdiag i]; exact hB1
    · exact hb2 i j hij
  have hD0summ : Summable D0 := by
    refine Summable.of_norm_bounded (g := fun p ↦ |F0 p|) hF0summ.abs fun p ↦ ?_
    rw [Real.norm_eq_abs, hF0, hD0]
    simp only
    by_cases hGp : G p.1 p.2
    · by_cases hPp : P p.1 p.2
      · rw [if_neg fun h ↦ h.2 hPp, if_pos hGp]; simp
      · rw [if_pos ⟨hGp, hPp⟩, if_pos hGp]
    · rw [if_neg fun h ↦ hGp h.1, if_neg hGp]
  have hO0summ : Summable O0 := by
    refine Summable.of_norm_bounded (g := fun p ↦ |F0 p|) hF0summ.abs fun p ↦ ?_
    rw [Real.norm_eq_abs, hF0, hO0]
    simp only
    by_cases hGp : G p.1 p.2
    · by_cases hPp : P p.1 p.2
      · rw [if_pos ⟨hGp, hPp⟩, if_pos hGp]
      · rw [if_neg fun h ↦ hPp h.2, if_pos hGp]; simp
    · rw [if_neg fun h ↦ hGp h.1, if_neg hGp]
  have hyw : yWeightedSum lam = ∑' p, F0 p := by rw [hF0summ.tsum_prod]; rfl
  have hptwise : ∀ p, F0 p = D0 p + O0 p := fun p ↦ by
    rw [hF0, hD0, hO0]
    simp only
    by_cases hGp : G p.1 p.2
    · by_cases hPp : P p.1 p.2
      · rw [if_pos hGp, if_neg fun h ↦ h.2 hPp, if_pos ⟨hGp, hPp⟩]; ring
      · rw [if_pos hGp, if_pos ⟨hGp, hPp⟩, if_neg fun h ↦ hPp h.2]; ring
    · rw [if_neg hGp, if_neg fun h ↦ hGp h.1, if_neg fun h ↦ hGp h.1]; ring
  have hOFF' : OFF = ∑' p, O0 p := by
    rw [hOFF, hO0summ.tsum_prod]
    refine tsum_congr fun u ↦ tsum_congr fun s ↦ ?_
    simp only [hO0, hG, hP, hFexpr]
    refine if_congr ?_ rfl rfl
    constructor <;> intro h <;> tauto
  have hDIAG' : DIAG = ∑' p, D0 p := by
    rw [hDIAG]
    exact tsum_truncated_eq_diag θ δ N lam (hW ▸ hlam) D0 (fun p ↦ rfl) hD0summ hD0floor
  have hsplit : yWeightedSum lam = DIAG + OFF := by
    rw [hyw]
    calc ∑' p, F0 p = ∑' p, (D0 p + O0 p) := tsum_congr hptwise
      _ = (∑' p, D0 p) + (∑' p, O0 p) := hD0summ.tsum_add hO0summ
      _ = DIAG + OFF := by rw [← hDIAG', ← hOFF']
  have key : (N : ℝ) / Wt * yWeightedSum lam - (N : ℝ) / Wt * MT = (N : ℝ) / Wt * OFF := by
    rw [hsplit, mul_add, ← hsijone]; ring
  have hOFFbound : |(N : ℝ) / Wt * yWeightedSum lam - (N : ℝ) / Wt * MT| ≤
      C₂ * Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 * (Nat.totient Wt : ℝ) ^ k * N *
        Real.log R ^ k / ((Wt : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
    rw [key, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) / Wt)]
    exact E2
  calc |S1 h lam N Wt v0 - (N : ℝ) / Wt * MT|
      = |(S1 h lam N Wt v0 - (N : ℝ) / Wt * yWeightedSum lam) +
          ((N : ℝ) / Wt * yWeightedSum lam - (N : ℝ) / Wt * MT)| := by ring_nf
    _ ≤ |S1 h lam N Wt v0 - (N : ℝ) / Wt * yWeightedSum lam| +
          |(N : ℝ) / Wt * yWeightedSum lam - (N : ℝ) / Wt * MT| := abs_add_le _ _
    _ ≤ (C₁ * Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 * (Nat.totient Wt : ℝ) ^ k * N *
          Real.log R ^ k / ((Wt : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ))) +
        (C₂ * Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 * (Nat.totient Wt : ℝ) ^ k * N *
          Real.log R ^ k / ((Wt : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ))) := add_le_add E1 hOFFbound
    _ = (C₁ + C₂) * Finsupp.maxRealAbs (PrimeGaps.lToY lam) ^ 2 * (Nat.totient Wt : ℝ) ^ k * N *
          Real.log R ^ k / ((Wt : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by ring

end PrimeGaps
