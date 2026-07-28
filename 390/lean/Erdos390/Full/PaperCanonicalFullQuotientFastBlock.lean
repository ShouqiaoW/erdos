import Erdos390.Full.PaperCanonicalFullQuotientEventually

/-!
# Specializing the canonical full quotient to the actual fast main block

The eventual quotient theorem is deliberately stated for every arithmetic
band vector `b` and every physical coefficient `mu`.  Proposition 8.7 uses
the special vector represented by an actual main parameter.  The following
finite identity performs that specialization without a change of norm or a
limiting argument.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The all-`b,mu` literal quotient gap implies the corresponding gap for
the exact main score.  Both rewrites are pointwise identities: the gauge
part of `mainBandVector` is the raw gauge, and its residual valuation score
is the actual exponential-family main score. -/
theorem actualFullQuotient_mainScore_of_all_residuals
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma kappa : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
      inner ℝ v (B.nuisanceCovarianceOperator xi v))
    (hquot : ∀ (b : Band → ℝ) (mu : ℝ),
      kappa * B.partition.data.bandNormSq
          (B.partition.data.gaugePart b) ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.primeValuationScore
              (B.partition.data.residual b mu)))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.primeValuationScore
              (B.partition.data.residual b mu)))) :
    ∀ u : B.MainSpace,
      kappa * B.partition.data.bandNormSq (B.rawGaugeOfMain u).1 ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (fun m => B.vectorFamily.scalarFamily.score m
              (B.mainEmbed u)))
          (B.nuisanceResidualScore xi hgamma hgap
            (fun m => B.vectorFamily.scalarFamily.score m
              (B.mainEmbed u))) := by
  intro u
  have h := hquot (B.mainBandVector u) (u MainCoord.slow / B.w)
  rw [B.gaugePart_mainBandVector_eq_rawGauge] at h
  rw [B.primeValuationScore_mainBandVector_residual_eq_mainScore] at h
  exact h

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
