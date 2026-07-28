import Erdos390.Full.PaperProposition87CanonicalTargetPackage

/-!
# Non-circular speed package for Proposition 8.7

All constants entering the fast and slow velocities are fixed before the
effective box.  The speed is the maximum of the two structural bounds and
one unit reserved for the nuisance velocity; the radius is four times that
speed.  The exact finite inequalities are then consequences for every
positive paper scale `B.w`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Radius selection and all three speed inequalities in the exact form
consumed by `exists_physicallyCenteredFixedPartitionFit_of_canonicalTwoStageOutputs`.
The compensated prime coefficient is `Ccoef * B.w`, and the two nuisance
reserves are `1/2` and `gammaSlow*B.w/(2(1+A))`. -/
theorem exists_speed_radius_with_canonicalTwoStage_bounds
    {CinvOrd Tband Creg Tslow K gammaSlow Ccoef : ℝ}
    (hTband : 0 ≤ Tband)
    (hCreg : 0 ≤ Creg) (hTslow : 0 ≤ Tslow)
    (hK : 0 ≤ K) (hgammaSlow : 0 < gammaSlow)
    (hCcoef : 0 ≤ Ccoef) :
    let A := K * Creg * Tband + Tslow
    ∃ speed a : NNReal,
      1 ≤ (speed : ℝ) ∧ speed ≤ a ∧
      (a : ℝ) = 4 * (speed : ℝ) ∧
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
  dsimp only
  let A : ℝ := K * Creg * Tband + Tslow
  let primeBound : ℝ :=
    CinvOrd * Tband + (A / gammaSlow) * Ccoef
  let slowBound : ℝ := A / gammaSlow
  obtain ⟨speed, a, hspeedOne, hprimeSpeed, hslowSpeed,
      hmargin, hradius⟩ :=
    exists_speed_radius_before_vanishing_nuisance primeBound slowBound
  refine ⟨speed, a, hspeedOne, hmargin, hradius, ?_⟩
  intro B hmoment
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  obtain ⟨hprime, _hnuisanceScaled, hslow⟩ :=
    B.twoStage_uniform_speed_bounds_of_scaled_rows
      (Creg := Creg) (Tband := Tband) (Tslow := Tslow) (K := K)
      (gamma := gammaSlow) (Cc := Ccoef) (Cz := 0)
      (Cord := CinvOrd) (Cfast := 0)
      hCreg hTband hgammaSlow hCcoef (by norm_num) hmoment
  have hstage :=
    B.twoStageCompensatedTargetBoundOrdinaryFast_le_w_mul
      (Creg := Creg) (Tband := Tband) (Tslow := Tslow)
      hCreg hTband hmoment
  have hnuisance :=
    B.twoStage_nuisance_speed_le_one_of_half_reserves
      hA hgammaSlow hstage
  refine ⟨?_, ?_, ?_⟩
  · exact hprime.trans (by simpa only [primeBound, A] using hprimeSpeed)
  · exact hnuisance.trans hspeedOne
  · exact hslow.trans (by simpa only [slowBound, A] using hslowSpeed)

/-- Type- and mesh-uniform form of the same radius choice.  The witnesses
`speed` and `a` are selected before the head type and the regular partition;
all subsequent finite band types use those identical witnesses.  This is the
quantifier order consumed by the paper-level eventual Proposition 8.7. -/
theorem exists_speed_radius_with_canonicalTwoStage_bounds_uniformTypes
    {CinvOrd Tband Creg Tslow K gammaSlow Ccoef : ℝ}
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
  dsimp only
  let A : ℝ := K * Creg * Tband + Tslow
  let primeBound : ℝ :=
    CinvOrd * Tband + (A / gammaSlow) * Ccoef
  let slowBound : ℝ := A / gammaSlow
  obtain ⟨speed, a, hspeedOne, hprimeSpeed, hslowSpeed,
      hmargin, hradius⟩ :=
    exists_speed_radius_before_vanishing_nuisance primeBound slowBound
  refine ⟨speed, a, hspeedOne, hmargin, hradius, ?_⟩
  intro Head Band _instHeadFintype _instHeadDecidable
    _instBandFintype _instBandDecidable B hmoment
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  obtain ⟨hprime, _hnuisanceScaled, hslow⟩ :=
    B.twoStage_uniform_speed_bounds_of_scaled_rows
      (Creg := Creg) (Tband := Tband) (Tslow := Tslow) (K := K)
      (gamma := gammaSlow) (Cc := Ccoef) (Cz := 0)
      (Cord := CinvOrd) (Cfast := 0)
      hCreg hTband hgammaSlow hCcoef (by norm_num) hmoment
  have hstage :=
    B.twoStageCompensatedTargetBoundOrdinaryFast_le_w_mul
      (Creg := Creg) (Tband := Tband) (Tslow := Tslow)
      hCreg hTband hmoment
  have hnuisance :=
    B.twoStage_nuisance_speed_le_one_of_half_reserves
      hA hgammaSlow hstage
  refine ⟨?_, ?_, ?_⟩
  · exact hprime.trans (by simpa only [primeBound, A] using hprimeSpeed)
  · exact hnuisance.trans hspeedOne
  · exact hslow.trans (by simpa only [slowBound, A] using hslowSpeed)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
