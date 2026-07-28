import Erdos390.Full.PaperNonstepPowerCorrectionLedger

/-!
Expanded statement audit for the exact non-step power-correction ledger.
The displayed hypothesis is the reciprocal weighted covariance-row bound,
and the displayed conclusion contains the literal arithmetic deviations.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

example
    {Omega₁ Omega₂ : Type*} [Fintype Omega₁] [Fintype Omega₂]
    {M₁ M₂ : ℕ}
    (law₁ : BoundedValuationLaw Omega₁ M₁)
    (law₂ : BoundedValuationLaw Omega₂ M₂)
    {rho w : ℝ} (hw : 0 ≤ w)
    (hdevSup : ∀ q : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation q| ≤ w)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |(law₁.covVV p.1 q.1 - law₁.covII p.1 q.1) -
            (law₂.covVV p.1 q.1 - law₂.covII p.1 q.1)| ≤ rho)
    (i : Band) :
    |(((1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₁.covVV p.1 q.1) -
        ((1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₁.covII p.1 q.1)) -
      (((1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₂.covVV p.1 q.1) -
        ((1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₂.covII p.1 q.1))| ≤ rho * w := by
  simpa only [nonstepFullCoefficientRow,
    nonstepSquarefreeCoefficientRow] using
      B.abs_nonstepPowerCorrectionRow_sub_le
        law₁ law₂ hw hdevSup hrow i

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

#print Erdos390.Full.PaperBridgeFit.BridgeData.abs_nonstepPowerCorrectionRow_sub_le
