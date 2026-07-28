import Erdos390.Full.PaperCanonicalActualFullQuotientNullIdentification

/-!
# Expanded statement audit for the actual full quotient gap

These wrappers deliberately repeat every quantifier, hypothesis, coefficient,
and conclusion.  They therefore fail to typecheck if the production theorem
is silently weakened, restricted to the raw gauge, or detached from the
literal actual nuisance-Schur variance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperCanonicalActualFullQuotientExpandedStatementAudit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperCanonicalSlowKappa
open PaperCanonicalActualBandQuadraticTransfer
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open OmittedTiltPairChamber

namespace BridgeData

open PaperBridgeFit

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : PaperBridgeFit.BridgeData Head Band)

/-- Expanded audit of the exact finite null relation.  Both `b` and the two
physical subtraction parameters are arbitrary. -/
theorem expanded_nuisanceResidualVariance_residual_independent_mu
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (b : Band → ℝ) (mu nu : ℝ) :
    (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b nu)))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b nu))) =
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b mu)))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b mu))) := by
  exact B.nuisanceResidualVariance_residual_independent_mu
    xi hgamma hgap hhead b mu nu

/-- Fully expanded audit of the strongest arbitrary-band, arbitrary-physical
parameter, fixed-canonical-kappa actual nuisance-Schur quotient gap. -/
theorem expanded_actualResidualSchur_fullQuotient_Dgap_canonicalKappa_independent_mu
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ}
    (hgamma : 0 < gamma) (hCmarked : 0 ≤ Cmarked)
    (hgapNuisance : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Set.Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (hsmall : rowError +
          ((4 * pairCovarianceScale Eprofile) * totalWeight +
            2 * Eprofile +
            ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
              CKernel) * invW) +
          R +
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2 * totalWeight / gamma) ≤
        (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor) :
    ∀ (b : Band → ℝ) (mu : ℝ),
      let c := B.partition.data.residual b mu
      let F := B.primeValuationScore c
      ((canonicalSlowKappa / 2) *
                anchorMass (primeWeight B.sampleData.n) anchor -
              rowError -
              ((4 * pairCovarianceScale Eprofile) * totalWeight +
                2 * Eprofile +
                ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                  CKernel) * invW) -
              R -
              ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
                Cmarked ^ 2 * totalWeight / gamma)) *
            B.partition.data.bandNormSq (B.partition.data.gaugePart b) ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgapNuisance F)
          (B.nuisanceResidualScore xi hgamma hgapNuisance F) := by
  exact B.actualResidualSchur_fullQuotient_Dgap_canonicalKappa_independent_mu
    xi hgamma hCmarked hgapNuisance hhead anchor hinterior hmass
      hEprofile hCKernel hW hTotal hInvW hrowReference hpair hsingle
      hKernel hrowPower hmarked hsmall

end BridgeData

end

end Erdos390.Full.PaperCanonicalActualFullQuotientExpandedStatementAudit
