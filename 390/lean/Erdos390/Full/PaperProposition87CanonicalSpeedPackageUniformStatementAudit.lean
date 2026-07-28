import Erdos390.Full.PaperProposition87CanonicalSpeedPackage

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

example {CinvOrd Tband Creg Tslow K gammaSlow Ccoef : ℝ}
    (hTband : 0 ≤ Tband)
    (hCreg : 0 ≤ Creg) (hTslow : 0 ≤ Tslow)
    (hK : 0 ≤ K) (hgammaSlow : 0 < gammaSlow)
    (hCcoef : 0 ≤ Ccoef) :
    let A := K * Creg * Tband + Tslow
    ∃ speed a : NNReal,
      1 ≤ (speed : ℝ) ∧ speed ≤ a ∧
      (a : ℝ) = 4 * (speed : ℝ) ∧
      ∀ {Head Band : Type*} [Fintype Head] [DecidableEq Head]
        [Fintype Band] [DecidableEq Band],
      ∀ (B : BridgeData Head Band),
        (∑ j : Band, B.harmonicMass j * B.bandCenter j) ≤ K →
        CinvOrd * Tband +
            (B.twoStageCompensatedTargetBoundOrdinaryFast
                Creg Tband Tslow / (gammaSlow * B.w ^ 2)) *
              (Ccoef * B.w) ≤ (speed : ℝ) ∧
          (1 / 2 : ℝ) +
              (B.twoStageCompensatedTargetBoundOrdinaryFast
                Creg Tband Tslow / (gammaSlow * B.w ^ 2)) *
                (gammaSlow * B.w / (2 * (1 + A))) ≤
            (speed : ℝ) ∧
          B.w *
              (B.twoStageCompensatedTargetBoundOrdinaryFast
                Creg Tband Tslow / (gammaSlow * B.w ^ 2)) ≤
            (speed : ℝ) := by
  exact exists_speed_radius_with_canonicalTwoStage_bounds_uniformTypes
    hTband hCreg hTslow hK hgammaSlow hCcoef

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
