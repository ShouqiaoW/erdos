import Erdos390.Full.FixedFiniteMixturePrimePower
import Erdos390.Full.ConditionedPoissonLimit
import Erdos390.Full.ArithmeticBandGeometry

/-!
# Signed squarefree covariance transfer to the Dickman kernel

The prime-power ledger only needs an absolute upper bound.  Lemma 8.4 needs
the stronger *signed* comparison between the genuine divisor-indicator
covariance and the arithmetic Poisson--Dickman matrix.  This file derives
that comparison from the same common one- and two-divisor profiles, before
any band averaging.  In particular, the between-cell covariance of the
tagged mixture is retained exactly.
-/

namespace Erdos390.Full.SquarefreeCovarianceReference

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber
open PaperScaleMarkedCell PaperPrimePowerChamberError
open FullTiltPrimePowerCovariance
open FixedFiniteMixturePrimePower
open DickmanFourMarkProductKernel ConditionedPoissonLimit

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
  {M : ℕ}

/-- The signed off-diagonal entry of the arithmetic Dickman matrix. -/
def squarefreeKernelEntry (n p q : ℕ) : ℝ :=
  covarianceKernel (tPrime n p) (tPrime n q) /
    ((p : ℝ) * (q : ℝ))

/-- The diagonal multiplier together with the diagonal term inserted by the
double-prime kernel sum.  This is exactly the diagonal entry represented by
`arithmeticDiagonal + arithmeticKernel`. -/
def squarefreeReferenceEntry (n p q : ℕ) : ℝ :=
  if p = q then
    DickmanBasic.F (tPrime n p) / (p : ℝ) +
      squarefreeKernelEntry n p p
  else squarefreeKernelEntry n p q

theorem paperDivisibilityMain_prime_eq
    {n p : ℕ} (hn : 1 < n) (hp : p.Prime) :
    paperDivisibilityMain n p =
      DickmanBasic.F (tPrime n p) / (p : ℝ) := by
  have h := paperDivisibilityMain_pairPower_eq_profile
    (n := n) (p := p) (q := p) (r := 1) (s := 0) hn hp hp
  simpa only [pairPower, pow_one, pow_zero, mul_one,
    Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero,
    DickmanFourMarkProductKernel.fourMarkProfile_eq_F] using h

/-- The three common marked profiles imply a signed covariance comparison
for two distinct moving primes.  The error is still at product-reciprocal
scale. -/
theorem abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
    {E : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W p q : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W)
    (hqErase : q ∈ (primeBand n W).erase p)
    (hpairProfile : ∀ c,
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1) ((law c).value omega)) -
        paperDivisibilityMain n (pairPower p q 1 1)| ≤
          E * pairWeight p q 1 1)
    (hpProfile : ∀ c,
      |(law c).probability.expect
          (fun omega ↦ divInd p ((law c).value omega)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1)
    (hqProfile : ∀ c,
      |(law c).probability.expect
          (fun omega ↦ divInd q ((law c).value omega)) -
        paperDivisibilityMain n q| ≤ E * singleWeight q 1) :
    let mix := sigmaMixture weight law
    |mix.covII p q - squarefreeKernelEntry n p q| ≤
      pairCovarianceScale E * pairWeight p q 1 1 := by
  dsimp only
  let mix := sigmaMixture weight law
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hqErase).1.symm
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hpPos : 0 < p := hp.pos
  have hqPos : 0 < q := hq.pos
  have hD4 : pairPower p q 1 1 ≤ yNat n ^ 4 := by
    have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
    have hqY : q ≤ yNat n := le_yNat_of_mem_primeBand hqBand
    unfold pairPower
    simp only [pow_one]
    calc
      p * q ≤ yNat n * yNat n := Nat.mul_le_mul hpY hqY
      _ ≤ yNat n ^ 4 := by
        have hy : 1 ≤ yNat n := hpPos.trans_le hpY
        nlinarith [sq_nonneg ((yNat n : ℤ) ^ 2 - 1)]
  have hD4P : pairPower p q 1 0 ≤ yNat n ^ 4 := by
    have hdiv : pairPower p q 1 0 ∣ pairPower p q 1 1 := by
      refine ⟨q, ?_⟩
      simp [pairPower]
    exact (Nat.le_of_dvd (pairPower_pos hp hq) hdiv).trans hD4
  have hD4Q : pairPower p q 0 1 ≤ yNat n ^ 4 := by
    have hdiv : pairPower p q 0 1 ∣ pairPower p q 1 1 := by
      refine ⟨p, ?_⟩
      simp [pairPower, Nat.mul_comm]
    exact (Nat.le_of_dvd (pairPower_pos hp hq) hdiv).trans hD4
  let Mrs := paperDivisibilityMain n (pairPower p q 1 1)
  let Mr := paperDivisibilityMain n (pairPower p q 1 0)
  let Ms := paperDivisibilityMain n (pairPower p q 0 1)
  let Ers := E * pairWeight p q 1 1
  let Er := E * singleWeight p 1
  let Es := E * singleWeight q 1
  have hpair : |mix.probability.expect
        (fun omega ↦ divInd (pairPower p q 1 1) (mix.value omega)) - Mrs| ≤
      Ers := by
    exact abs_sigmaMixture_expect_divInd_sub_common_le weight law
      (pairPower p q 1 1) Mrs Ers hpairProfile
  have hpr : |mix.probability.expect
        (fun omega ↦ divInd (p ^ 1) (mix.value omega)) - Mr| ≤ Er := by
    have hraw := abs_sigmaMixture_expect_divInd_sub_common_le weight law
      p (paperDivisibilityMain n p) (E * singleWeight p 1) hpProfile
    simpa only [Er, Mr, pairPower, pow_zero, pow_one, mul_one] using hraw
  have hqs : |mix.probability.expect
        (fun omega ↦ divInd (q ^ 1) (mix.value omega)) - Ms| ≤ Es := by
    have hraw := abs_sigmaMixture_expect_divInd_sub_common_le weight law
      q (paperDivisibilityMain n q) (E * singleWeight q 1) hqProfile
    simpa only [Es, Ms, pairPower, pow_zero, pow_one, one_mul] using hraw
  have hEr : 0 ≤ Er := mul_nonneg hE (singleWeight_nonneg p 1)
  have hprob := abs_primePower_covariance_sub_mainCov_le
    mix.probability mix.value hpq hp hq hEr hpair hpr hqs
  have hMr : |Mr| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p 1 := by
    simpa only [Mr, pairPower, pow_zero, mul_one] using
      abs_paperDivisibilityMain_pow_le_singleWeight hn hp
        (by simpa only [pairPower, pow_zero, mul_one] using hD4P)
  have hMs : |Ms| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight q 1 := by
    simpa only [Ms, pairPower, pow_zero, one_mul] using
      abs_paperDivisibilityMain_pow_le_singleWeight hn hq
        (by simpa only [pairPower, pow_zero, one_mul] using hD4Q)
  have herr : Ers + Er * |Ms| + Es * |Mr| + Er * Es ≤
      pairCovarianceScale E * pairWeight p q 1 1 := by
    have halg := covariance_error_algebra hE
      (singleWeight_nonneg p 1) (singleWeight_nonneg q 1)
      (mul_nonneg hE (singleWeight_nonneg q 1))
      (show Ers ≤ E * (singleWeight p 1 * singleWeight q 1) by
        rw [show Ers = E * pairWeight p q 1 1 by rfl,
          pairWeight_eq_single_mul])
      (show Er ≤ E * singleWeight p 1 by rfl)
      (show Es ≤ E * singleWeight q 1 by rfl) hMr hMs
    simpa only [pairCovarianceScale, pairWeight_eq_single_mul, Ers, Er, Es]
      using halg
  have hmain := paperMainCovariance_eq_profileKernel
    (r := 1) (s := 1) hn hp hq
  have hmain' : Mrs - Mr * Ms = squarefreeKernelEntry n p q := by
    rw [hmain]
    unfold squarefreeKernelEntry covarianceKernel
    simp only [Nat.cast_one, one_mul, pow_one,
      DickmanFourMarkProductKernel.fourMarkProfile_eq_F]
  change |mix.probability.covariance (mix.I p) (mix.I q) -
      squarefreeKernelEntry n p q| ≤ _
  have hprob' :
      |mix.probability.covariance (mix.I p) (mix.I q) - (Mrs - Mr * Ms)| ≤
        Ers + Er * |Ms| + Es * |Mr| + Er * Es := by
    simpa only [BoundedValuationLaw.Ip, pow_one] using hprob
  rw [hmain'] at hprob'
  exact hprob'.trans herr

/-- Backwards-compatible four-mark formulation.  Only the three squarefree
instances `(1,1)`, `(1,0)`, and `(0,1)` are used by the signed covariance
comparison. -/
theorem abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le
    {E : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W p q : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W)
    (hqErase : q ∈ (primeBand n W).erase p)
    (hprofile : ∀ c u v,
      pairPower p q u v ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q u v) ((law c).value omega)) -
        paperDivisibilityMain n (pairPower p q u v)| ≤
          E * pairWeight p q u v) :
    let mix := sigmaMixture weight law
    |mix.covII p q - squarefreeKernelEntry n p q| ≤
      pairCovarianceScale E * pairWeight p q 1 1 := by
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have h11 := pairPower_le_yNat_pow_four hpBand hqBand (by omega : 1 + 1 ≤ 4)
  have h10 := pairPower_le_yNat_pow_four hpBand hqBand (by omega : 1 + 0 ≤ 4)
  have h01 := pairPower_le_yNat_pow_four hpBand hqBand (by omega : 0 + 1 ≤ 4)
  apply abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
    hE weight law hn hpBand hqErase
  · exact fun c ↦ hprofile c 1 1 h11
  · intro c
    simpa only [pairPower, pow_one, pow_zero, mul_one,
      pairWeight_eq_single_mul, singleWeight, Nat.cast_zero,
      zero_add, div_one, mul_one] using hprofile c 1 0 h10
  · intro c
    simpa only [pairPower, pow_one, pow_zero, one_mul,
      pairWeight_eq_single_mul, singleWeight, Nat.cast_zero,
      zero_add, div_one, one_mul] using hprofile c 0 1 h01

/-- Signed diagonal comparison.  The first summand is the marked
one-divisor error.  The second is the genuine Bernoulli correction together
with the diagonal kernel term inserted by the double-prime reference sum. -/
theorem abs_sigmaMixture_covII_diagonal_sub_reference_le
    {E CKernel : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W p : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W)
    (hsingle : ∀ c,
      |(law c).probability.expect
          (fun omega ↦ divInd p ((law c).value omega)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1)
    (hKernel :
      |covarianceKernel (tPrime n p) (tPrime n p)| ≤ CKernel) :
    let mix := sigmaMixture weight law
    |mix.covII p p - squarefreeReferenceEntry n p p| ≤
      2 * E / (p : ℝ) +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 + CKernel) /
          (p : ℝ) ^ 2 := by
  dsimp only
  let mix := sigmaMixture weight law
  let P : ℝ := mix.probability.expect (mix.I p)
  let Main : ℝ := paperDivisibilityMain n p
  have hpPrime := prime_of_mem_primeBand hpBand
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hprofileRaw := abs_sigmaMixture_expect_divInd_sub_common_le
    weight law p Main (E * singleWeight p 1) hsingle
  have hprofile : |P - Main| ≤ 2 * E / (p : ℝ) := by
    simpa only [P, Main, mix, BoundedValuationLaw.I] using
      (show |(sigmaMixture weight law).probability.expect
          ((sigmaMixture weight law).I p) - Main| ≤
          2 * E / (p : ℝ) by
        calc
          _ ≤ E * singleWeight p 1 := hprofileRaw
          _ = 2 * E / (p : ℝ) := by
            unfold singleWeight
            norm_num
            ring)
  have hMainEq : Main = DickmanBasic.F (tPrime n p) / (p : ℝ) :=
    paperDivisibilityMain_prime_eq hn hpPrime
  have hMainNonneg : 0 ≤ Main := by
    have hmainBound := paperDivisibilityMain_nonneg_le hn hpPrime.pos
      (by
        have hpY := le_yNat_of_mem_primeBand hpBand
        have hy : 1 ≤ yNat n := hpPrime.pos.trans_le hpY
        calc
          p ≤ yNat n := hpY
          _ ≤ yNat n ^ 4 := by nlinarith [sq_nonneg ((yNat n : ℤ) ^ 2 - 1)])
    exact hmainBound.1
  have hMainUpper : Main ≤
      (1 / DickmanBasic.rho DickmanBasic.U) / (p : ℝ) := by
    have hmainBound := paperDivisibilityMain_nonneg_le hn hpPrime.pos
      (by
        have hpY := le_yNat_of_mem_primeBand hpBand
        have hy : 1 ≤ yNat n := hpPrime.pos.trans_le hpY
        calc
          p ≤ yNat n := hpY
          _ ≤ yNat n ^ 4 := by nlinarith [sq_nonneg ((yNat n : ℤ) ^ 2 - 1)])
    change paperDivisibilityMain n p ≤ _
    convert hmainBound.2 using 1
    field_simp [DickmanBasic.rho_U_ne_zero, hpPos.ne']
  have hPNonneg : 0 ≤ P := by
    unfold P
    exact FiniteProbability.expect_nonneg mix.probability (mix.I p)
      (fun omega ↦ divInd_nonneg p (mix.value omega))
  have hPUpper : P ≤
      (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) / (p : ℝ) := by
    have hdiff : P - Main ≤ 2 * E / (p : ℝ) :=
      (le_abs_self (P - Main)).trans hprofile
    calc
      P ≤ Main + 2 * E / (p : ℝ) := by linarith
      _ ≤ (1 / DickmanBasic.rho DickmanBasic.U) / (p : ℝ) +
          2 * E / (p : ℝ) := add_le_add hMainUpper le_rfl
      _ = (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) / (p : ℝ) := by
        ring
  have hCoeffNonneg :
      0 ≤ 1 / DickmanBasic.rho DickmanBasic.U + 2 * E := by
    exact add_nonneg
      (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)
      (mul_nonneg (by norm_num) hE)
  have hPsq : P ^ 2 ≤
      (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 /
        (p : ℝ) ^ 2 := by
    have hupperNonneg : 0 ≤
        (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) / (p : ℝ) :=
      div_nonneg hCoeffNonneg hpPos.le
    have hsquare := (sq_le_sq₀ hPNonneg hupperNonneg).2 hPUpper
    calc
      P ^ 2 ≤ ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) /
          (p : ℝ)) ^ 2 := hsquare
      _ = (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 /
          (p : ℝ) ^ 2 := by ring
  have hCov : mix.covII p p = P - P ^ 2 := by
    unfold BoundedValuationLaw.covII FiniteProbability.covariance P
    have hsquare : (fun omega ↦ mix.I p omega * mix.I p omega) =
        mix.I p := by
      funext omega
      change divInd p (mix.value omega) * divInd p (mix.value omega) =
        divInd p (mix.value omega)
      nlinarith [divInd_sq p (mix.value omega)]
    rw [hsquare]
    ring
  have hKernelScaled :
      |squarefreeKernelEntry n p p| ≤ CKernel / (p : ℝ) ^ 2 := by
    unfold squarefreeKernelEntry
    have hden : 0 < (p : ℝ) * (p : ℝ) := mul_pos hpPos hpPos
    calc
      |covarianceKernel (tPrime n p) (tPrime n p) /
          ((p : ℝ) * (p : ℝ))| =
          |covarianceKernel (tPrime n p) (tPrime n p)| /
            ((p : ℝ) * (p : ℝ)) := by
        rw [abs_div, abs_of_pos hden]
      _ ≤ CKernel / ((p : ℝ) * (p : ℝ)) :=
        div_le_div_of_nonneg_right hKernel hden.le
      _ = CKernel / (p : ℝ) ^ 2 := by ring
  rw [squarefreeReferenceEntry, if_pos rfl, hCov]
  rw [← hMainEq]
  have htriangle :
      |(P - P ^ 2) - (Main + squarefreeKernelEntry n p p)| ≤
        |P - Main| + P ^ 2 + |squarefreeKernelEntry n p p| := by
    calc
      |(P - P ^ 2) - (Main + squarefreeKernelEntry n p p)| =
          |(P - Main) + (-P ^ 2 - squarefreeKernelEntry n p p)| := by
        apply congrArg abs
        ring
      _ ≤ |P - Main| + |-P ^ 2 - squarefreeKernelEntry n p p| :=
        abs_add_le _ _
      _ ≤ |P - Main| + (P ^ 2 + |squarefreeKernelEntry n p p|) := by
        gcongr
        calc
          |-P ^ 2 - squarefreeKernelEntry n p p| ≤
              |-P ^ 2| + |squarefreeKernelEntry n p p| := abs_sub _ _
          _ = P ^ 2 + |squarefreeKernelEntry n p p| := by
            rw [abs_neg, abs_of_nonneg (sq_nonneg P)]
      _ = |P - Main| + P ^ 2 + |squarefreeKernelEntry n p p| := by ring
  calc
    |(P - P ^ 2) - (Main + squarefreeKernelEntry n p p)| ≤
        |P - Main| + P ^ 2 + |squarefreeKernelEntry n p p| := htriangle
    _ ≤ 2 * E / (p : ℝ) +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 /
          (p : ℝ) ^ 2) + CKernel / (p : ℝ) ^ 2 := by
      gcongr
    _ = 2 * E / (p : ℝ) +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 + CKernel) /
          (p : ℝ) ^ 2 := by ring

/-- The signed one- and two-divisor comparisons assembled into the single
entrywise estimate consumed by the sharp band-row theorem. -/
theorem sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
    {E CKernel : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W : ℕ} (hn : 1 < n)
    (hpair : ∀ c p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1) ((law c).value omega)) -
        paperDivisibilityMain n (pairPower p q 1 1)| ≤
          E * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand n W →
      |(law c).probability.expect
          (fun omega ↦ divInd p ((law c).value omega)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand n W,
      |covarianceKernel (tPrime n p) (tPrime n p)| ≤ CKernel) :
    let mix := sigmaMixture weight law
    ∀ p q : ArithmeticBandGeometry.BandPrime n W,
      |mix.covII p.1 q.1 - squarefreeReferenceEntry n p.1 q.1| ≤
        (4 * pairCovarianceScale E) /
            ((p.1 : ℝ) * (q.1 : ℝ)) +
          (if p = q then
            (2 * E) / (p.1 : ℝ) +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 +
                CKernel) / (p.1 : ℝ) ^ 2
          else 0) := by
  dsimp only
  let mix := sigmaMixture weight law
  intro p q
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl]
    have hdiag := abs_sigmaMixture_covII_diagonal_sub_reference_le
      hE weight law hn p.2 (fun c ↦ hsingle c p.1 p.2)
      (hKernel p.1 p.2)
    have hcovNonneg : 0 ≤ pairCovarianceScale E :=
      pairCovarianceScale_nonneg hE
    have hpPos : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hextra : 0 ≤
        (4 * pairCovarianceScale E) / ((p.1 : ℝ) * (p.1 : ℝ)) :=
      div_nonneg (mul_nonneg (by norm_num) hcovNonneg)
        (mul_nonneg hpPos.le hpPos.le)
    exact hdiag.trans (by
      have htwo : 2 * E / (p.1 : ℝ) = (2 * E) / (p.1 : ℝ) := rfl
      rw [htwo]
      linarith)
  · rw [if_neg hpq]
    have hqErase : q.1 ∈ (primeBand n W).erase p.1 :=
      Finset.mem_erase.mpr ⟨fun h ↦ hpq (Subtype.ext h.symm), q.2⟩
    have hoff :=
      abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
      hE weight law hn p.2 hqErase
      (fun c ↦ hpair c p.1 p.2 q.1 hqErase)
      (fun c ↦ hsingle c p.1 p.2)
      (fun c ↦ hsingle c q.1 q.2)
    have href : squarefreeReferenceEntry n p.1 q.1 =
        squarefreeKernelEntry n p.1 q.1 := by
      rw [squarefreeReferenceEntry, if_neg (by
        intro h
        exact hpq (Subtype.ext h))]
    rw [href]
    have hrewrite :
        pairCovarianceScale E * pairWeight p.1 q.1 1 1 =
          (4 * pairCovarianceScale E) /
            ((p.1 : ℝ) * (q.1 : ℝ)) := by
      unfold pairWeight
      norm_num
      ring
    simpa only [mix, hrewrite, add_zero] using hoff

/-- Four-mark wrapper for the entrywise signed reference theorem. -/
theorem sigmaMixture_squarefree_reference_entry_bound
    {E CKernel : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W : ℕ} (hn : 1 < n)
    (hpair : ∀ c p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p → ∀ u v,
      pairPower p q u v ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q u v) ((law c).value omega)) -
        paperDivisibilityMain n (pairPower p q u v)| ≤
          E * pairWeight p q u v)
    (hsingle : ∀ c p, p ∈ primeBand n W →
      |(law c).probability.expect
          (fun omega ↦ divInd p ((law c).value omega)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand n W,
      |covarianceKernel (tPrime n p) (tPrime n p)| ≤ CKernel) :
    let mix := sigmaMixture weight law
    ∀ p q : ArithmeticBandGeometry.BandPrime n W,
      |mix.covII p.1 q.1 - squarefreeReferenceEntry n p.1 q.1| ≤
        (4 * pairCovarianceScale E) /
            ((p.1 : ℝ) * (q.1 : ℝ)) +
          (if p = q then
            (2 * E) / (p.1 : ℝ) +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 +
                CKernel) / (p.1 : ℝ) ^ 2
          else 0) := by
  apply sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
    hE weight law hn
  · intro c p hp q hq
    exact hpair c p hp q hq 1 1
      (pairPower_le_yNat_pow_four hp (Finset.mem_erase.mp hq).2
        (by omega : 1 + 1 ≤ 4))
  · exact hsingle
  · exact hKernel

end

end Erdos390.Full.SquarefreeCovarianceReference
