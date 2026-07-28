import Erdos390.WholePaper.RoughSaiasRiemannAbsorption

namespace Erdos390.WholePaper

noncomputable section

#check exists_roughSaiasRiemannAbsorptionCutoff
#check roughSaiasRiemannAbsorptionCutoff
#check roughSaiasRiemannAbsorptionCutoff_spec
#check roughSaiasDickmanRiemannEnvelope_le_invLogSq
#check roughSaiasDickmanBuchstabBlockRemainder_abs_le_invLogSq
#check roughSaiasReverseNormalFormDefect_self_abs_le_closed_add_obstruction

example {y : ℕ} (hY : roughSaiasRiemannAbsorptionCutoff ≤ y) :
    2 * (6 + 40 * Real.log (y : ℝ)) * Real.log (y : ℝ) ^ 2 ≤
      (y : ℝ) :=
  roughSaiasRiemannAbsorptionCutoff_spec hY

example {X y : ℕ} (hY : roughSaiasRiemannAbsorptionCutoff ≤ y)
    (hy2 : 2 ≤ y)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) ≤
      (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
  roughSaiasDickmanRiemannEnvelope_le_invLogSq hY hy2 hu5

example {X y : ℕ} (hy2 : 2 ≤ y) (hyX : y < X)
    (hYtheta : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hYriemann : roughSaiasRiemannAbsorptionCutoff ≤ y)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      (4 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
      |roughSaiasCanonicalCorrectionObstruction X y| :=
  roughSaiasReverseNormalFormDefect_self_abs_le_closed_add_obstruction
    hy2 hyX hYtheta hYriemann hu5

end

end Erdos390.WholePaper
