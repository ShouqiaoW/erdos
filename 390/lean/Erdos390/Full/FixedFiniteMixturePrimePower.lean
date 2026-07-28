import Erdos390.Full.FiniteProbabilityMixture
import Erdos390.Full.PaperPrimePowerPointwise

/-!
# Prime-power estimates for a fixed finite mixture

A covariance of a mixture is not the mixture of the covariances.  The
theorems in this file instead average the common one- and two-divisor
profiles first and only then form the covariance.  Consequently the
between-cell covariance is included exactly.
-/

namespace Erdos390.Full.FixedFiniteMixturePrimePower

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open FullTiltPrimePowerCovariance FullTiltPrimePowerActualChamber
open FullTiltPrimePowerFallback
open OmittedTiltPairChamber
open PaperPrimePowerChamberError PaperPrimePowerPointwise
open PaperPrimePowerRow

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
  {M : ℕ}

/-- A common marked divisibility profile gives the sharp covariance bound
for the tagged finite mixture.  In particular, no covariance is averaged
across cells. -/
theorem abs_sigmaMixture_primePower_covariance_le_of_common_profile
    {C_K E : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |DickmanFourMarkProductKernel.fourMarkProfile (x + z) -
          DickmanFourMarkProductKernel.fourMarkProfile x *
            DickmanFourMarkProductKernel.fourMarkProfile z| ≤ C_K * x * z)
    (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W p q r s : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W)
    (hqErase : q ∈ (primeBand n W).erase p)
    (hD4 : pairPower p q r s ≤ yNat n ^ 4)
    (hprofile : ∀ c u v,
      pairPower p q u v ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q u v) ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n
          (pairPower p q u v)| ≤ E * pairWeight p q u v) :
    let mix := sigmaMixture weight law
    |mix.probability.covariance (mix.Ip p r) (mix.Ip q s)| ≤
      C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s) +
        pairCovarianceScale E * pairWeight p q r s := by
  dsimp only
  let mix := sigmaMixture weight law
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hqErase).1.symm
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hDpos : 0 < pairPower p q r s := pairPower_pos hp hq
  have hdivP : pairPower p q r 0 ∣ pairPower p q r s := by
    refine ⟨q ^ s, ?_⟩
    simp only [pairPower, pow_zero, mul_one]
  have hdivQ : pairPower p q 0 s ∣ pairPower p q r s := by
    refine ⟨p ^ r, ?_⟩
    simp only [pairPower, pow_zero, one_mul]
    exact (mul_comm (q ^ s) (p ^ r)).symm
  have hD4P : pairPower p q r 0 ≤ yNat n ^ 4 :=
    (Nat.le_of_dvd hDpos hdivP).trans hD4
  have hD4Q : pairPower p q 0 s ≤ yNat n ^ 4 :=
    (Nat.le_of_dvd hDpos hdivQ).trans hD4
  let Mrs := PaperScaleMarkedCell.paperDivisibilityMain n
    (pairPower p q r s)
  let Mr := PaperScaleMarkedCell.paperDivisibilityMain n
    (pairPower p q r 0)
  let Ms := PaperScaleMarkedCell.paperDivisibilityMain n
    (pairPower p q 0 s)
  let Ers := E * pairWeight p q r s
  let Er := E * singleWeight p r
  let Es := E * singleWeight q s
  have hpair : |mix.probability.expect
        (fun omega ↦ divInd (pairPower p q r s) (mix.value omega)) - Mrs| ≤
      Ers := by
    exact abs_sigmaMixture_expect_divInd_sub_common_le weight law
      (pairPower p q r s) Mrs Ers (fun c ↦ hprofile c r s hD4)
  have hpr : |mix.probability.expect
        (fun omega ↦ divInd (p ^ r) (mix.value omega)) - Mr| ≤ Er := by
    have hraw := abs_sigmaMixture_expect_divInd_sub_common_le weight law
      (pairPower p q r 0) Mr (E * pairWeight p q r 0)
      (fun c ↦ hprofile c r 0 hD4P)
    simpa only [pairPower, pow_zero, mul_one, pairWeight_eq_single_mul,
      singleWeight, Nat.cast_zero, zero_add, div_one, mul_one] using hraw
  have hqs : |mix.probability.expect
        (fun omega ↦ divInd (q ^ s) (mix.value omega)) - Ms| ≤ Es := by
    have hraw := abs_sigmaMixture_expect_divInd_sub_common_le weight law
      (pairPower p q 0 s) Ms (E * pairWeight p q 0 s)
      (fun c ↦ hprofile c 0 s hD4Q)
    simpa only [pairPower, pow_zero, one_mul, pairWeight_eq_single_mul,
      singleWeight, Nat.cast_zero, zero_add, div_one, one_mul] using hraw
  have hEr : 0 ≤ Er := mul_nonneg hE (singleWeight_nonneg p r)
  have hprob := abs_primePower_covariance_sub_mainCov_le
    mix.probability mix.value hpq hp hq hEr
    (Mrs := Mrs) (Mr := Mr) (Ms := Ms)
    (by simpa only [mix, BoundedValuationLaw.Ip] using hpair)
    (by simpa only [mix, BoundedValuationLaw.Ip] using hpr)
    (by simpa only [mix, BoundedValuationLaw.Ip] using hqs)
  have hMr : |Mr| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r := by
    simpa only [Mr, pairPower, pow_zero, mul_one] using
      abs_paperDivisibilityMain_pow_le_singleWeight hn hp
        (by simpa only [pairPower, pow_zero, mul_one] using hD4P)
  have hMs : |Ms| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight q s := by
    simpa only [Ms, pairPower, pow_zero, one_mul] using
      abs_paperDivisibilityMain_pow_le_singleWeight hn hq
        (by simpa only [pairPower, pow_zero, one_mul] using hD4Q)
  have herr : Ers + Er * |Ms| + Es * |Mr| + Er * Es ≤
      pairCovarianceScale E * pairWeight p q r s := by
    have halg := covariance_error_algebra hE
      (singleWeight_nonneg p r) (singleWeight_nonneg q s)
      (mul_nonneg hE (singleWeight_nonneg q s))
      (show Ers ≤ E * (singleWeight p r * singleWeight q s) by
        simp only [Ers, pairWeight_eq_single_mul]
        exact le_rfl)
      (show Er ≤ E * singleWeight p r by rfl)
      (show Es ≤ E * singleWeight q s by rfl) hMr hMs
    simpa only [pairCovarianceScale, pairWeight_eq_single_mul, Ers, Er, Es]
      using halg
  have hmain := abs_paperMainCovariance_le_of_le hkernel hn hpBand hqBand hD4
  have htriangle :
      |mix.probability.covariance (mix.Ip p r) (mix.Ip q s)| ≤
        |mix.probability.covariance (mix.Ip p r) (mix.Ip q s) -
          (Mrs - Mr * Ms)| + |Mrs - Mr * Ms| := by
    have h := abs_add_le
      (mix.probability.covariance (mix.Ip p r) (mix.Ip q s) -
        (Mrs - Mr * Ms)) (Mrs - Mr * Ms)
    simpa only [sub_add_cancel] using h
  exact htriangle.trans (by
    have hsum := add_le_add (hprob.trans herr) hmain
    simpa only [Mrs, Mr, Ms, add_comm, add_left_comm, add_assoc] using hsum)

/-- Chamber/fallback splice for a tagged finite mixture. -/
theorem sigmaMixture_primePower_covariance_le_chamber_add_tail
    {C_K E Gf : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |DickmanFourMarkProductKernel.fourMarkProfile (x + z) -
          DickmanFourMarkProductKernel.fourMarkProfile x *
            DickmanFourMarkProductKernel.fourMarkProfile z| ≤ C_K * x * z)
    (hCK : 0 ≤ C_K) (hE : 0 ≤ E) (hGf : 0 ≤ Gf)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W p q r s : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W)
    (hqErase : q ∈ (primeBand n W).erase p)
    (hprofile : ∀ c u v,
      pairPower p q u v ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q u v) ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n
          (pairPower p q u v)| ≤ E * pairWeight p q u v)
    (hfallback : ∀ c D, 0 < D →
      (law c).probability.expect
        (fun omega ↦ divInd D ((law c).value omega)) ≤ Gf / (D : ℝ)) :
    let mix := sigmaMixture weight law
    |mix.probability.covariance (mix.Ip p r) (mix.Ip q s)| ≤
      (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) *
          pairWeight p q r s + covarianceTail Gf n p q r s := by
  dsimp only
  let mix := sigmaMixture weight law
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hqErase).1.symm
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have htp := tPrime_nonneg_of_mem_primeBand hn hpBand
  have htq := tPrime_nonneg_of_mem_primeBand hn hqBand
  apply covariance_le_chamber_add_tail hCK
    (pairCovarianceScale_nonneg hE) htp htq
  · intro hD4
    exact abs_sigmaMixture_primePower_covariance_le_of_common_profile
      hkernel hE weight law hn hpBand hqErase hD4 hprofile
  · intro hD4
    exact le_rfl
  · apply abs_primePower_covariance_le_reciprocal
      mix.probability mix.value hpq hp hq hGf
    · have h := sigmaMixture_expect_divInd_le_common weight law
        (pairPower p q r s)
        (Gf / (pairPower p q r s : ℝ))
        (fun c ↦ hfallback c (pairPower p q r s) (pairPower_pos hp hq))
      simpa only [pairPower, Nat.cast_mul, Nat.cast_pow] using h
    · have h := sigmaMixture_expect_divInd_le_common weight law (p ^ r)
        (Gf / ((p ^ r : ℕ) : ℝ))
        (fun c ↦ hfallback c (p ^ r) (Nat.pow_pos hp.pos))
      simpa only [Nat.cast_pow] using h
    · have h := sigmaMixture_expect_divInd_le_common weight law (q ^ s)
        (Gf / ((q ^ s : ℕ) : ℝ))
        (fun c ↦ hfallback c (q ^ s) (Nat.pow_pos hq.pos))
      simpa only [Nat.cast_pow] using h

/-- The matching one-prime probability splice for a tagged mixture. -/
theorem sigmaMixture_primePower_probability_le_chamber_add_tail
    {E Gf : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W p r : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W)
    (hprofile : ∀ c,
      p ^ r ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (p ^ r) ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r)| ≤
          E * singleWeight p r)
    (hfallback : ∀ c D, 0 < D →
      (law c).probability.expect
        (fun omega ↦ divInd D ((law c).value omega)) ≤ Gf / (D : ℝ)) :
    let mix := sigmaMixture weight law
    mix.probability.expect (mix.Ip p r) ≤
      ((1 / DickmanBasic.rho DickmanBasic.U) + E) * singleWeight p r +
        probabilityTail Gf n p r := by
  dsimp only
  let mix := sigmaMixture weight law
  have hp := prime_of_mem_primeBand hpBand
  apply probability_le_chamber_add_tail
    (chamberError := E * singleWeight p r)
    (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le) hE
  · intro hD4
    have hmix := abs_sigmaMixture_expect_divInd_sub_common_le weight law
      (p ^ r) (PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r))
      (E * singleWeight p r) (fun c ↦ hprofile c hD4)
    have hmain := abs_paperDivisibilityMain_pow_le_singleWeight hn hp hD4
    have htriangle : mix.probability.expect (mix.Ip p r) ≤
        |mix.probability.expect (mix.Ip p r) -
            PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r)| +
          |PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r)| := by
      have habs := abs_add_le
        (mix.probability.expect (mix.Ip p r) -
          PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r))
        (PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r))
      exact (le_abs_self _).trans (by simpa only [sub_add_cancel] using habs)
    have hsum := htriangle.trans (add_le_add
      (by simpa only [mix, BoundedValuationLaw.Ip] using hmix) hmain)
    simpa only [add_comm] using hsum
  · intro hD4
    exact le_rfl
  · have h := sigmaMixture_expect_divInd_le_common weight law (p ^ r)
      (Gf / ((p ^ r : ℕ) : ℝ))
      (fun c ↦ hfallback c (p ^ r) (Nat.pow_pos hp.pos))
    simpa only [mix, BoundedValuationLaw.Ip, Nat.cast_pow] using h

end

end Erdos390.Full.FixedFiniteMixturePrimePower
