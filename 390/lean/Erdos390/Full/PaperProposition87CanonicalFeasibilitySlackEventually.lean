import Erdos390.Full.PaperCanonicalNuisanceUniformFloor
import Erdos390.Full.PaperProposition87SpeedRadius

/-!
# Canonical eventual feasibility slack for Proposition 8.7

The finite ODE assembly asks for an exponential feasibility inequality whose
nuisance coefficient is attached to the current canonical bridge data.  The
coefficient is uniformly bounded by the head-cardinality ceiling.  Therefore,
after `W`, the head type, and the effective ball have been fixed, the required
inequality follows from `L(n) -> infinity`; it is not an analytic hypothesis
at the final Proposition 8.7 call site.
-/

open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Uniform eventual form of the literal feasibility slack used by the
canonical ODE assembly. -/
theorem eventually_canonical_exponential_slack_le_L
    (U : ℝ) (hU : 1 ≤ U) (W : ℕ) (a : NNReal)
    (Cfixed Cactive : ℝ) (hCactive : 0 ≤ Cactive) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        Cfixed +
            Real.exp (2 *
              ((PaperStatisticNorm.valuationLogCoefficient
                    U B.sampleData.W +
                  B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) *
              Cactive ≤ B.L := by
  let Kceiling : ℝ :=
    2 * ((PaperStatisticNorm.valuationLogCoefficient U W +
      nuisanceStatisticCoefficientCeiling Head U) * (3 * (a : ℝ)))
  have hlarge := eventually_fixed_exponential_slack_le_L
    Cfixed Kceiling Cactive
  filter_upwards [hlarge] with n hlargeN
  intro B hBn hBW
  have hcoeff :
      PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
          B.nuisanceStatisticCoefficient U ≤
        PaperStatisticNorm.valuationLogCoefficient U W +
          nuisanceStatisticCoefficientCeiling Head U := by
    rw [hBW]
    linarith [B.nuisanceStatisticCoefficient_le_ceiling hU]
  have hscaleNonneg : 0 ≤ 3 * (a : ℝ) := by positivity
  have hexponent :
      2 * ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
            B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ))) ≤
        Kceiling := by
    dsimp only [Kceiling]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hscaleNonneg]
  have hexp :
      Real.exp (2 *
          ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
            B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) ≤
        Real.exp Kceiling := Real.exp_le_exp.mpr hexponent
  have hscaled := mul_le_mul_of_nonneg_right hexp hCactive
  calc
    Cfixed +
          Real.exp (2 *
            ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
              B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) *
            Cactive ≤
        Cfixed + Real.exp Kceiling * Cactive :=
      by linarith
    _ ≤ B.L := by
      change Cfixed + Real.exp Kceiling * Cactive ≤
        Scale.L B.sampleData.n
      rw [hBn]
      exact hlargeN

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
