import Erdos390.Full.PaperProposition87ActiveMassTransport

/-! Statement audit for fixed and varying active-mass Proposition 8.7 transport. -/

namespace Erdos390.Full.PaperBridgeFit

open Filter Metric Set PaperGuardCensus

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band] [Nonempty Head]
  (B : BridgeData Head Band)

/-- Audit the central law, moment, covariance, and ODE homogeneity package. -/
example
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (Delta : Band -> Real) (F G : B.sampleData.Sample -> Real)
    (xi : B.ParamSpace) :
    B.vectorFamily.scalarFamily.covariance F G xi =
        (B.normalizedLawCompanion T).vectorFamily.scalarFamily.covariance
          F G xi ∧
      B.paperMoment F xi =
        q * (B.normalizedLawCompanion T).paperMoment F xi ∧
      B.covarianceOperator xi =
        (B.normalizedLawCompanion T).covarianceOperator xi ∧
      B.vectorFamily.vectorField (B.targetVector Delta) xi =
        (B.normalizedLawCompanion T).vectorFamily.vectorField
          ((B.normalizedLawCompanion T).targetVector
            (fun j => Delta j / q)) xi := by
  exact ⟨B.covariance_eq_normalizedLawCompanion T q hq hbaseline F G xi,
    B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline F xi,
    B.covarianceOperator_eq_normalizedLawCompanion
      T q hq hbaseline xi,
    B.vectorField_eq_normalizedLawCompanion
      T q hq hbaseline Delta xi⟩

/-- Audit the assumption-free fixed-positive-mass canonical terminal. -/
example
    (q : Real) (hq : 0 < q) (cMesh : Real)
    (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank) :
    CanonicalProposition87ActiveMassLiteralBalanceStatement
      q hq cMesh I U Cprom Cbank ledger := by
  exact canonical_proposition87_activeMassLiteralBandBalance
    q hq cMesh I U Cprom Cbank ledger

/-- Audit the paper-facing terminal where the literal active mass varies with
`n`; eventual `1 <= q_n` is the only uniformity hypothesis. -/
example
    (qMass : Nat -> Real)
    (hqOne : ∀ᶠ n : Nat in atTop, 1 <= qMass n)
    (cMesh : Real) (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank) :
    CanonicalProposition87VaryingActiveMassLiteralBalanceStatement
      qMass cMesh I U Cprom Cbank ledger := by
  exact canonical_proposition87_varyingActiveMassLiteralBandBalance
    qMass hqOne cMesh I U Cprom Cbank ledger

#check normalizedLawCompanion
#check normalizedLawCompanion_sampleData
#check normalizedLawCompanion_baseline
#check normalizedLawCompanion_partition
#check normalizedLawCompanion_lowBand
#check normalizedLawCompanion_referenceHead
#check normalizedLawCompanion_w
#check normalizedLawCompanion_L
#check normalizedLawCompanion_q
#check baseWeight_eq_activeMass_mul_normalizedLawCompanion
#check headBaselineMass_eq_normalizedLawCompanion
#check statistic_eq_normalizedLawCompanion
#check unnormalizedWeight_eq_activeMass_mul_normalizedLawCompanion
#check partition_eq_activeMass_mul_normalizedLawCompanion
#check probabilityMass_eq_normalizedLawCompanion
#check covariance_eq_normalizedLawCompanion
#check activeWeight_eq_activeMass_mul_normalizedLawCompanion
#check paperMoment_eq_activeMass_mul_normalizedLawCompanion
#check vectorMoment_eq_activeMass_smul_normalizedLawCompanion
#check jacobian_eq_activeMass_smul_normalizedLawCompanion
#check jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
#check covarianceOperator_eq_normalizedLawCompanion
#check targetVector_eq_activeMass_smul_normalizedLawCompanion
#check normalizedTarget_eq_normalizedLawCompanion
#check hasTargetEnvelopes_normalizedLawCompanion
#check normalizedLawCompanion_baseWeight_le_div_log
#check normalizedLawCompanion_q_le_of_activeMass_bound
#check normalizedLawCompanion_initialMarkedRate
#check jacobian_isInvertible_iff_normalizedLawCompanion
#check vectorField_eq_normalizedLawCompanion
#check markedBandResidual_eq_activeMass_mul_normalizedLawCompanion
#check hasPaperProposition87Conclusion_of_normalizedLawCompanion
#check canonical_activeMass_proposition87_of_normalizedLawCompanion
#check CanonicalProposition87ActiveMassLiteralBalanceStatement
#check canonical_proposition87_activeMassLiteralBandBalance
#check CanonicalProposition87VaryingActiveMassLiteralBalanceStatement
#check canonical_proposition87_varyingActiveMassLiteralBandBalance

end BridgeData

end


end Erdos390.Full.PaperBridgeFit
