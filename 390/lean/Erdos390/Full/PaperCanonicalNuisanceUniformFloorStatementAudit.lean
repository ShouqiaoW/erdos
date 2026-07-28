import Erdos390.Full.PaperCanonicalNuisanceUniformFloor

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

example (B : BridgeData Head Band) :
    Fintype.card (NuisanceCoord B.HeadIndex) ≤ Fintype.card Head + 1 := by
  exact B.nuisanceCoord_card_le_head_add_one

example (B : BridgeData Head Band) :
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
      nuisanceDimensionCeiling Head := by
  exact B.sqrt_nuisanceCoord_card_le_ceiling

example (B : BridgeData Head Band) {U : ℝ} (hU : 1 ≤ U) :
    B.nuisanceStatisticCoefficient U ≤
      nuisanceStatisticCoefficientCeiling Head U := by
  exact B.nuisanceStatisticCoefficient_le_ceiling hU

example (B : BridgeData Head Band) (sep R : ℝ) :
    B.nuisanceGeometryConstant sep R ≤
      nuisanceGeometryCeiling Head sep R := by
  exact B.nuisanceGeometryConstant_le_ceiling sep R

example (I : PhysicalIntervals) {U a marginFloor : ℝ} {W : ℕ}
    (hmargin : 0 < marginFloor) :
    0 < canonicalEffectiveNuisanceGammaFloor
      Head I U a W marginFloor := by
  exact canonicalEffectiveNuisanceGammaFloor_pos
    (Head := Head) I hmargin

example (B : BridgeData Head Band) [Nonempty Head]
    (I : PhysicalIntervals) {U a marginFloor : ℝ}
    (hU : 1 ≤ U) (ha : 0 ≤ a) (hmargin : 0 < marginFloor)
    (T : BarycentricTarget B.sampleData)
    (hTmargin : marginFloor ≤ T.cellMassMargin) :
    canonicalEffectiveNuisanceGammaFloor
        Head I U a B.sampleData.W marginFloor ≤
      B.canonicalEffectiveNuisanceGamma I U a T := by
  exact B.canonicalEffectiveNuisanceGammaFloor_le I hU ha hmargin
    T hTmargin

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
