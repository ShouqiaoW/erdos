import Erdos390.Full.PaperBridgeFit
import Erdos390.Full.PositiveCellTransfer

/-!
# Positive-cell quadrature inside the paper bridge

This module specializes the unconditional endpoint estimates to the actual
`BridgeData` quantities denoted by `H_j` and `alpha_j` in Section 8.4.  The
only finite combinatorial input is an `IntervalCertificate` saying that a
band really is the prime interval `(A_j,Y_j]`.  The two identities below then
identify the bridge quantities with the prime sums exactly; the asymptotic
bounds are consequences of the proved PNT quadrature, not structure fields of
`BridgeData`.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open PositiveCellTransfer
open PrimeSums PrimeBandQuadrature

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Endpoint certificate for the actual prime partition carried by `B`. -/
abbrev PositiveCellCertificate :=
  PositiveCellTransfer.IntervalCertificate B.partition

/-- Exact identification of the paper's `H_j` with the reciprocal-prime sum
over its certified arithmetic interval. -/
theorem harmonicMass_eq_fullReciprocalSum_sub
    (E : B.PositiveCellCertificate) (j : Band) :
    B.harmonicMass j =
      fullReciprocalSum (E.upper j) - fullReciprocalSum (E.lower j) := by
  exact E.mass_eq_fullReciprocalSum_sub j

/-- Exact identification of `H_j alpha_j` with the normalized first
logarithmic moment.  In particular, the center on the left is the arithmetic
center, so no continuum-centering identity is being assumed. -/
theorem harmonicMass_mul_bandCenter_eq_fullLogReciprocalSum_sub
    (E : B.PositiveCellCertificate) (j : Band) :
    B.harmonicMass j * B.bandCenter j =
      (fullLogReciprocalSum (E.upper j) -
        fullLogReciprocalSum (E.lower j)) /
          Real.log (ArithmeticModel.y B.sampleData.n) := by
  exact E.mass_mul_center_eq_fullLogReciprocalSum_sub j

/-- The ratio step in the actual bridge notation.  Separate estimates for
`H_j` and `H_j alpha_j` imply a quantitative estimate for the arithmetic
center itself. -/
theorem bandCenter_error_le_of_mass_moment_errors
    (E : B.PositiveCellCertificate) (j : Band) {eMass eMoment : ℝ}
    (hMass : |B.harmonicMass j - E.continuumMass j| ≤ eMass)
    (hMoment :
      |B.harmonicMass j * B.bandCenter j - E.continuumMoment j| ≤
        eMoment)
    (hContinuumMass : E.continuumMass j ≠ 0) :
    |B.bandCenter j - E.continuumCenter j| ≤
      eMoment / B.harmonicMass j +
        |E.continuumMoment j| * eMass /
          (B.harmonicMass j * |E.continuumMass j|) := by
  exact E.center_error_le_of_mass_moment_errors j
    hMass hMoment hContinuumMass

/-- Relative harmonic-mass transfer, including the moving-low regime where
absolute mass convergence is neither asserted nor needed. -/
theorem harmonicMass_ratio_error_le
    (E : B.PositiveCellCertificate) (j : Band) {eMass : ℝ}
    (hMass : |B.harmonicMass j - E.continuumMass j| ≤ eMass)
    (hContinuumMass : E.continuumMass j ≠ 0) :
    |B.harmonicMass j / E.continuumMass j - 1| ≤
      eMass / |E.continuumMass j| := by
  exact E.mass_ratio_error_le j hMass hContinuumMass

/-- Unconditional moving-endpoint quadrature for the actual bridge mass
`H_j`, uniform over all certified positive cells. -/
theorem exists_harmonicMass_quadrature_bound
    (E : B.PositiveCellCertificate) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ j : Band,
      X₀ ≤ E.lower j →
      |B.harmonicMass j -
        (Real.log (Real.log (E.upper j : ℝ)) -
          Real.log (Real.log (E.lower j : ℝ)))| ≤
        5 * C / Real.log (E.lower j : ℝ) ^ 3 := by
  exact E.exists_mass_quadrature_bound

/-- Unconditional moving-endpoint quadrature for the actual bridge moment
`H_j alpha_j`.  The error retains the exact arithmetic divisor `log y`. -/
theorem exists_harmonicMass_mul_bandCenter_quadrature_bound
    (E : B.PositiveCellCertificate) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ j : Band,
      X₀ ≤ E.lower j →
      |B.harmonicMass j * B.bandCenter j -
        (Real.log (E.upper j : ℝ) -
          Real.log (E.lower j : ℝ)) /
            Real.log (ArithmeticModel.y B.sampleData.n)| ≤
        (C * (2 + (Real.log (E.upper j : ℝ) -
          Real.log (E.lower j : ℝ))) /
            Real.log (E.lower j : ℝ) ^ 3) /
          |Real.log (ArithmeticModel.y B.sampleData.n)| := by
  exact E.exists_mass_mul_center_quadrature_bound B.n_gt_one

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
