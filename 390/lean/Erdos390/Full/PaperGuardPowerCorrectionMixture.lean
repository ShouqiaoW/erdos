import Erdos390.Full.FiniteProbabilityMixturePerturbation
import Erdos390.Full.PaperGuardDeletionRows

/-!
# Guard deletion for the global prime-power correction row

The useful object in Lemma 7.5 is not the full valuation covariance by
itself, but its difference from the squarefree covariance.  This file applies
the family-summed tagged-mixture perturbation theorem separately to the `VV`
and `II` rows and then subtracts them.  The estimate is global: arbitrary
common component weights and every between-cell covariance term are included.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel ArithmeticBandGeometry FiniteProbability PaperBridgeFit

noncomputable section

/-- The prime-power correction covariance of a finite integer-valued law. -/
def powerCorrectionCovariance
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (p q : ℕ) : ℝ :=
  mu.covariance (fun x ↦ valuation p (value x))
      (fun x ↦ valuation q (value x)) -
    mu.covariance (fun x ↦ divInd p (value x))
      (fun x ↦ divInd q (value x))

/-- Explicit global error produced by deleting the concrete guards from both
the full-valuation and squarefree rows. -/
def guardPowerCorrectionRowError (K d : ℝ) : ℝ :=
  (3 * K * K * d +
      2 * ((K + K * d) * (K * d) + K * (K * d))) +
    (3 * K * d +
      2 * (((1 : ℝ) + d) * (K * d) + K * d))

theorem guardPowerCorrectionRowError_nonneg {K d : ℝ}
    (hK : 0 ≤ K) (hd : 0 ≤ d) :
    0 ≤ guardPowerCorrectionRowError K d := by
  unfold guardPowerCorrectionRowError
  positivity

variable {Head : Type*} [Fintype Head]

/-- Deleting guards componentwise perturbs the global `VV-II` row by the
displayed family error.  The hypothesis `hperturb` is a bound for the exact
conditional-normalization factor, not a total-variation proxy. -/
theorem sum_abs_guardDeleted_powerCorrectionRow_sub_le
    (P : Head → HeadPattern.Pattern) (Iphys : PhysicalIntervals)
    {n W : ℕ} (hW : 1 < W)
    (guardsNat : Finset ℕ)
    (hS : ∀ c : Cell Head, (rawCell P Iphys n c).Nonempty)
    (score : ∀ c : Cell Head, rawCell P Iphys n c → ℝ)
    (weight : FiniteProbability (Cell Head))
    (p : BandPrime n W)
    {K d : ℝ} (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hEnvelope : ∀ c : Cell Head,
      valuationEnvelope Iphys n W c ≤ K)
    (hsmall : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P Iphys n c) (hS c)).exponentialTilt
          (score c)).guardMass
        (GuardedUniformCell.guardSubtype
          (rawCell P Iphys n c) guardsNat) < 1))
    (hperturb : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P Iphys n c) (hS c)).exponentialTilt
          (score c)).guardPerturbation
        (GuardedUniformCell.guardSubtype
          (rawCell P Iphys n c) guardsNat) ≤ d)) :
    let S := fun c : Cell Head ↦ rawCell P Iphys n c
    let mu : ∀ c, FiniteProbability (S c) := fun c ↦
      (uniformOnFinset (S c) (hS c)).exponentialTilt (score c)
    let Gsub : ∀ c, Finset (S c) := fun c ↦
      GuardedUniformCell.guardSubtype (S c) guardsNat
    let nu : ∀ c, FiniteProbability (S c) := fun c ↦
      (mu c).deleteGuards (Gsub c) (hsmall c)
    let value : (Sigma fun c : Cell Head ↦ S c) → ℕ :=
      fun x ↦ (x.2 : ℕ)
    ∑ q : BandPrime n W,
      |powerCorrectionCovariance (sigmaMixture weight nu) value p.1 q.1 -
        powerCorrectionCovariance (sigmaMixture weight mu) value p.1 q.1| ≤
      guardPowerCorrectionRowError K d := by
  dsimp only
  let S := fun c : Cell Head ↦ rawCell P Iphys n c
  let mu : ∀ c, FiniteProbability (S c) := fun c ↦
    (uniformOnFinset (S c) (hS c)).exponentialTilt (score c)
  let Gsub : ∀ c, Finset (S c) := fun c ↦
    GuardedUniformCell.guardSubtype (S c) guardsNat
  let nu : ∀ c, FiniteProbability (S c) := fun c ↦
    (mu c).deleteGuards (Gsub c) (hsmall c)
  let Fv : ∀ c, S c → ℝ := fun _ m ↦ valuation p.1 (m : ℕ)
  let Hv : ∀ c, BandPrime n W → S c → ℝ :=
    fun _ q m ↦ valuation q.1 (m : ℕ)
  let Fi : ∀ c, S c → ℝ := fun _ m ↦ divInd p.1 (m : ℕ)
  let Hi : ∀ c, BandPrime n W → S c → ℝ :=
    fun _ q m ↦ divInd q.1 (m : ℕ)
  have htotal (c : Cell Head) (m : S c) :
      ∑ q : BandPrime n W, valuation q.1 (m : ℕ) ≤ K :=
    (rawCell_totalBandValuation_le P Iphys hW c m).trans (hEnvelope c)
  have hFv (c : Cell Head) (m : S c) : |Fv c m| ≤ K := by
    rw [abs_of_nonneg (valuation_nonneg p.1 (m : ℕ))]
    exact (rawCell_valuation_le_total P Iphys p c m).trans (htotal c m)
  have hHv (c : Cell Head) (m : S c) :
      ∑ q : BandPrime n W, |Hv c q m| ≤ K := by
    simpa only [Hv, abs_of_nonneg (valuation_nonneg _ _)] using htotal c m
  have hFi (c : Cell Head) (m : S c) : |Fi c m| ≤ (1 : ℝ) := by
    dsimp only [Fi]
    rw [abs_of_nonneg (divInd_nonneg p.1 (m : ℕ))]
    exact divInd_le_one p.1 (m : ℕ)
  have hHi (c : Cell Head) (m : S c) :
      ∑ q : BandPrime n W, |Hi c q m| ≤ K := by
    calc
      ∑ q : BandPrime n W, |Hi c q m| ≤
          ∑ q : BandPrime n W, valuation q.1 (m : ℕ) := by
        apply Finset.sum_le_sum
        intro q hq
        dsimp only [Hi]
        rw [abs_of_nonneg (divInd_nonneg q.1 (m : ℕ))]
        have hmpos : 0 < (m : ℕ) :=
          StructuredCells.pos_of_mem_smoothInterval
            (StructuredCells.mem_structuredCell.mp m.2).1
        have hhigher := higherValuation_nonneg
          (prime_of_mem_primeBand q.2) hmpos
        unfold higherValuation at hhigher
        linarith
      _ ≤ K := htotal c m
  have hsmall' (c : Cell Head) : (mu c).guardMass (Gsub c) < 1 := by
    simpa only [mu, Gsub, S] using hsmall c
  have hperturb' (c : Cell Head) :
      (mu c).guardPerturbation (Gsub c) ≤ d := by
    simpa only [mu, Gsub, S] using hperturb c
  have hfull := sum_abs_sigmaMixture_deleteGuards_covariance_sub_le
    weight mu Gsub hsmall' Fv Hv hK hK hd hFv hHv hperturb'
  have hsquare := sum_abs_sigmaMixture_deleteGuards_covariance_sub_le
    weight mu Gsub hsmall' Fi Hi (by norm_num) hK hd hFi hHi hperturb'
  have hpoint (q : BandPrime n W) :
      |powerCorrectionCovariance (sigmaMixture weight nu)
          (fun x : (Sigma fun c : Cell Head ↦ S c) ↦ (x.2 : ℕ)) p.1 q.1 -
        powerCorrectionCovariance (sigmaMixture weight mu)
          (fun x : (Sigma fun c : Cell Head ↦ S c) ↦ (x.2 : ℕ)) p.1 q.1| ≤
        |(sigmaMixture weight nu).covariance
            (fun x ↦ valuation p.1 (x.2 : ℕ))
            (fun x ↦ valuation q.1 (x.2 : ℕ)) -
          (sigmaMixture weight mu).covariance
            (fun x ↦ valuation p.1 (x.2 : ℕ))
            (fun x ↦ valuation q.1 (x.2 : ℕ))| +
        |(sigmaMixture weight nu).covariance
            (fun x ↦ divInd p.1 (x.2 : ℕ))
            (fun x ↦ divInd q.1 (x.2 : ℕ)) -
          (sigmaMixture weight mu).covariance
            (fun x ↦ divInd p.1 (x.2 : ℕ))
            (fun x ↦ divInd q.1 (x.2 : ℕ))| := by
    unfold powerCorrectionCovariance
    rw [show
      ((sigmaMixture weight nu).covariance
          (fun x ↦ valuation p.1 (x.2 : ℕ))
          (fun x ↦ valuation q.1 (x.2 : ℕ)) -
        (sigmaMixture weight nu).covariance
          (fun x ↦ divInd p.1 (x.2 : ℕ))
          (fun x ↦ divInd q.1 (x.2 : ℕ))) -
      ((sigmaMixture weight mu).covariance
          (fun x ↦ valuation p.1 (x.2 : ℕ))
          (fun x ↦ valuation q.1 (x.2 : ℕ)) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ divInd p.1 (x.2 : ℕ))
          (fun x ↦ divInd q.1 (x.2 : ℕ))) =
      ((sigmaMixture weight nu).covariance
          (fun x ↦ valuation p.1 (x.2 : ℕ))
          (fun x ↦ valuation q.1 (x.2 : ℕ)) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ valuation p.1 (x.2 : ℕ))
          (fun x ↦ valuation q.1 (x.2 : ℕ))) -
      ((sigmaMixture weight nu).covariance
          (fun x ↦ divInd p.1 (x.2 : ℕ))
          (fun x ↦ divInd q.1 (x.2 : ℕ)) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ divInd p.1 (x.2 : ℕ))
          (fun x ↦ divInd q.1 (x.2 : ℕ))) by ring]
    exact abs_sub _ _
  calc
    ∑ q : BandPrime n W,
      |powerCorrectionCovariance (sigmaMixture weight nu)
          (fun x : (Sigma fun c : Cell Head ↦ S c) ↦ (x.2 : ℕ)) p.1 q.1 -
        powerCorrectionCovariance (sigmaMixture weight mu)
          (fun x : (Sigma fun c : Cell Head ↦ S c) ↦ (x.2 : ℕ)) p.1 q.1| ≤
      ∑ q : BandPrime n W,
        (|(sigmaMixture weight nu).covariance
              (fun x ↦ valuation p.1 (x.2 : ℕ))
              (fun x ↦ valuation q.1 (x.2 : ℕ)) -
            (sigmaMixture weight mu).covariance
              (fun x ↦ valuation p.1 (x.2 : ℕ))
              (fun x ↦ valuation q.1 (x.2 : ℕ))| +
          |(sigmaMixture weight nu).covariance
              (fun x ↦ divInd p.1 (x.2 : ℕ))
              (fun x ↦ divInd q.1 (x.2 : ℕ)) -
            (sigmaMixture weight mu).covariance
              (fun x ↦ divInd p.1 (x.2 : ℕ))
              (fun x ↦ divInd q.1 (x.2 : ℕ))|) :=
      Finset.sum_le_sum fun q hq ↦ hpoint q
    _ = (∑ q : BandPrime n W,
          |(sigmaMixture weight nu).covariance
              (fun x ↦ valuation p.1 (x.2 : ℕ))
              (fun x ↦ valuation q.1 (x.2 : ℕ)) -
            (sigmaMixture weight mu).covariance
              (fun x ↦ valuation p.1 (x.2 : ℕ))
              (fun x ↦ valuation q.1 (x.2 : ℕ))|) +
        ∑ q : BandPrime n W,
          |(sigmaMixture weight nu).covariance
              (fun x ↦ divInd p.1 (x.2 : ℕ))
              (fun x ↦ divInd q.1 (x.2 : ℕ)) -
            (sigmaMixture weight mu).covariance
              (fun x ↦ divInd p.1 (x.2 : ℕ))
              (fun x ↦ divInd q.1 (x.2 : ℕ))| := by
      rw [Finset.sum_add_distrib]
    _ ≤ (3 * K * K * d +
          2 * ((K + K * d) * (K * d) + K * (K * d))) +
        (3 * 1 * K * d +
          2 * ((1 + 1 * d) * (K * d) + K * (1 * d))) :=
      add_le_add (by simpa only [nu, Fv, Hv] using hfull)
        (by simpa only [nu, Fi, Hi] using hsquare)
    _ = guardPowerCorrectionRowError K d := by
      unfold guardPowerCorrectionRowError
      ring

end

end Erdos390.Full.PaperGuardCensus
