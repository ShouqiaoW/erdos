import Erdos390.Full.PaperActualSlowRightRowFinite
import Erdos390.Full.PaperActualSlowRightRowTriangle

/-!
# Finite analytic assembly of the actual slow right column

The reference moving-low estimate and the exact actual-law/nuisance triangle
are combined here.  The conclusion is already the literal right column used
by Lemma 8.6; no substitute score or auxiliary Schur map remains.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerSharpBandTransfer SquarefreeSharpBandTransfer
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open ConditionedPoissonLimit DickmanBasic

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Fully finite slow-right-row estimate after inserting the exact
moving-low Dickman reference bound. -/
theorem abs_actualSlowRightRow_le_of_profiles
    [Nonempty Head]
    (xi : B.ParamSpace)
    {gamma Cmarked Efull Esquare rowError w CF CKernel : ℝ}
    (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (hw : 0 ≤ w) (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hrowResidual : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) -
          F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p|)
    (hKernelProduct : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n q.1)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (hfull : ∀ i : Band,
      |fullSharpRow (B.actualValuationLaw xi) B.partition
          (fun _ ↦ (1 : ℝ)) i -
        squarefreeSharpRow (B.actualValuationLaw xi) B.partition
          (fun _ ↦ (1 : ℝ)) i| ≤ Efull)
    (hsquare : ∀ i : Band,
      |squarefreeSharpRow (B.actualValuationLaw xi) B.partition
          (fun _ ↦ (1 : ℝ)) i -
        referenceSharpRow B.partition (fun _ ↦ (1 : ℝ)) i| ≤
          Esquare)
    (i : Band) :
    |B.normalizedBandCovarianceRow xi
        (B.nuisanceResidualScore xi hgamma hgap B.slowScore) i| ≤
      (Efull + Esquare +
          (rowError + (2 * CF + 7 * CKernel) * w)) *
          B.bandCenter i +
        ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            (Cmarked *
              (∑ j : Band, B.harmonicMass j * B.bandCenter j))) /
          gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked) := by
  have href := B.referenceBandRow_bandCenter_le_of_rowResidual
    hw hCF hCKernel hrowResidual hFdiff hKernelProduct hdevSup hdevL1 i
  exact B.abs_normalizedBandCovarianceRow_nuisanceResidual_slow_le_of_sharpRows
    xi hgamma hgap hhead hCmarked hmarked i (hfull i) (hsquare i) href

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
