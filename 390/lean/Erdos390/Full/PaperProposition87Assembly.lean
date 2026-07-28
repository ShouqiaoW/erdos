import Erdos390.Full.PaperEffectiveScoreBound
import Erdos390.Full.PaperBridgePrimewiseRate
import Erdos390.Full.PaperVectorFieldEffectiveBound

/-!
# Finite assembly layer for Proposition 8.7

This file assembles the already proved finite exponential-family, ODE,
endpoint, marked-row, and feasibility statements in the literal effective
norm used in the paper.  It deliberately does not assert the analytic
estimates of Lemmas 8.4 and 8.6: the three hypotheses `hgap`, `hvelocity`,
and `hmarkedRow` are exactly the uniform analytic outputs which those lemmas
must supply on the effective box chosen before the path.

The conclusion is not packaged as an abstract contract.  It exhibits the
actual bridge path and states the individual band, physical, head,
logarithmic, marked-prime, natural-coordinate feasibility, frozen-coordinate,
mass, and integer-quota conclusions directly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The literal frozen weight at a natural-number coordinate.  Several
tagged frozen summands are allowed to occupy the same coordinate, as happens
for a protected contribution superposed on a clean active coordinate. -/
def frozenAmbientWeight {Fixed : Type*} [Fintype Fixed]
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ) (x : ℕ) : ℝ :=
  ∑ f : Fixed, if fixedValue f = x then fixedWeight f else 0

/-- The unnormalized ordinary logarithm whose moment the construction keeps
exact.  `physicalScore` differs from it only by the constant `log n`. -/
def ordinaryLogScore (m : B.sampleData.Sample) : ℝ :=
  Real.log (B.sampleData.value m : ℝ)

theorem endpoint_preserves_ordinaryLog [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (hendpoint : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta) :
    B.paperMoment B.ordinaryLogScore xi1 =
      B.paperMoment B.ordinaryLogScore xi0 := by
  have hpoint (m : B.sampleData.Sample) :
      B.ordinaryLogScore m =
        B.physicalScore m + Real.log (B.sampleData.n : ℝ) := by
    have hm : (B.sampleData.value m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (B.sampleData.value_pos m)
    have hn : (B.sampleData.n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt B.n_gt_one)
    rw [ordinaryLogScore, physicalScore, Real.log_div hm hn]
    ring
  have hexpand (xi : B.ParamSpace) :
      B.paperMoment B.ordinaryLogScore xi =
        B.paperMoment B.physicalScore xi +
          B.q * Real.log (B.sampleData.n : ℝ) := by
    calc
      B.paperMoment B.ordinaryLogScore xi =
          B.paperMoment (fun m =>
            B.physicalScore m + Real.log (B.sampleData.n : ℝ)) xi := by
        congr 1
        funext m
        exact hpoint m
      _ = B.paperMoment B.physicalScore xi +
          B.paperMoment (fun _ => Real.log (B.sampleData.n : ℝ)) xi :=
        B.paperMoment_add _ _ xi
      _ = B.paperMoment B.physicalScore xi +
          B.q * Real.log (B.sampleData.n : ℝ) := by
        rw [B.paperMoment_const]
  rw [hexpand, hexpand,
    B.endpoint_preserves_physical Delta xi0 xi1 hendpoint]

/--
Finite, statement-level assembly of the physically centered
fixed-partition fit.

The analytic input is limited to a covariance gap, a dimension-free inverse
velocity estimate, and the marked covariance row, all uniform on the same
preselected effective ball.  The target and baseline ledger hypotheses are
the data entering Proposition 8.7 before the nonlinear fit.  In particular,
the theorem neither assumes a path nor assumes any endpoint, feasibility,
support, or quota conclusion.
-/
theorem exists_physicallyCenteredFixedPartitionFit_of_analyticOutputs
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ)
    (a speed : NNReal) {gamma : ℝ}
    (hgamma : 0 < gamma)
    (hgap : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gamma (B.effectiveParamEquiv z))
    (hvelocity : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      ‖B.effectiveParamEquiv.symm
        (B.vectorFamily.vectorField (B.targetVector Delta)
          (B.effectiveParamEquiv z))‖ ≤ (speed : ℝ))
    (hmargin : speed ≤ a)
    (monitoredPrimes : Finset ℕ)
    (Crow : ℝ) (hCrow : 0 ≤ Crow)
    (hmarkedRow : ∀ p ∈ monitoredPrimes,
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
            (B.markedValuation p)
            (fun m => B.vectorFamily.scalarFamily.score m
              (B.vectorFamily.vectorField (B.targetVector Delta)
                (B.effectiveParamEquiv z)))
            (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ))
    (markedTarget : ℕ → ℝ)
    (N Cinitial Cmass : ℝ)
    (hprimePos : ∀ p ∈ monitoredPrimes, 0 < p)
    (hqMass : B.q ≤ Cmass * N)
    (hinitialMarked : ∀ p ∈ monitoredPrimes,
      |markedTarget p - B.paperMoment (B.markedValuation p) 0| ≤
        Cinitial * N / ((p : ℝ) * B.L))
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ)
    (hquota : (quota : ℝ) = (∑ f, fixedWeight f) + B.q)
    {C Cfixed Cactive : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      ArithmeticModel.physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hfrozenFeasible : ∀ x,
      frozenAmbientWeight fixedValue fixedWeight x ∈ Set.Icc (0 : ℝ) 1)
    (hfrozenLedger : ∀ m : B.sampleData.Sample,
      frozenAmbientWeight fixedValue fixedWeight
        (B.sampleData.value m) ≤ Cfixed / B.L)
    (hactiveLedger : ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L)
    (hlarge : Cfixed +
      Real.exp (2 *
        ((PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * (3 * (a : ℝ)))) *
            Cactive ≤ B.L) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.effectiveParamEquiv.symm (path t) ∈
          closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      (∀ j : Band,
        B.paperMoment (B.bandScore j) (path 1) =
          B.paperMoment (B.bandScore j) 0 + Delta j) ∧
      B.paperMoment B.physicalScore (path 1) =
        B.paperMoment B.physicalScore 0 ∧
      B.paperMoment B.ordinaryLogScore (path 1) =
        B.paperMoment B.ordinaryLogScore 0 ∧
      (∀ h : B.HeadIndex,
        B.paperMoment (B.headIndicator h.1) (path 1) =
          B.paperMoment (B.headIndicator h.1) 0) ∧
      B.paperMoment B.primeLogScore (path 1) =
        B.paperMoment B.primeLogScore 0 ∧
      (∀ p ∈ monitoredPrimes,
        |markedTarget p - B.paperMoment (B.markedValuation p) (path 1)| ≤
          (Cinitial + Cmass * Crow) * N / ((p : ℝ) * B.L)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
        B.ambientCombinedWeight
            (frozenAmbientWeight fixedValue fixedWeight) (path t) x ∈
          Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
        B.combinedWeight fixedWeight (path t) (Sum.inl f) =
          B.combinedWeight fixedWeight 0 (Sum.inl f)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ m : B.sampleData.Sample,
          B.activeCoordinateWeight (path t) m) = B.q) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ x : Fixed ⊕ B.sampleData.Sample,
          B.combinedWeight fixedWeight (path t) x) = (quota : ℝ)) := by
  obtain ⟨path, hpathZero, hball, hsize, hderiv, hraw⟩ :=
    B.exists_paperFit_on_preselectedEffectiveBall Delta a speed hgamma
      hgap hvelocity hmargin
  have hendpoint : B.vectorFamily.vectorMoment (path 1) =
      B.vectorFamily.vectorMoment 0 + B.targetVector Delta :=
    (B.endpoint_iff_paperMoments Delta 0 (path 1)).mpr hraw
  have hbands : ∀ j : Band,
      B.paperMoment (B.bandScore j) (path 1) =
        B.paperMoment (B.bandScore j) 0 + Delta j :=
    B.endpoint_recovers_all_bandMoments_of_compatibility
      hcompat Delta 0 (path 1) hendpoint
  have hphysical : B.paperMoment B.physicalScore (path 1) =
      B.paperMoment B.physicalScore 0 :=
    B.endpoint_preserves_physical Delta 0 (path 1) hendpoint
  have hordinaryLog : B.paperMoment B.ordinaryLogScore (path 1) =
      B.paperMoment B.ordinaryLogScore 0 :=
    B.endpoint_preserves_ordinaryLog Delta 0 (path 1) hendpoint
  have hheads : ∀ h : B.HeadIndex,
      B.paperMoment (B.headIndicator h.1) (path 1) =
        B.paperMoment (B.headIndicator h.1) 0 :=
    fun h => B.endpoint_preserves_headIndicator Delta 0 (path 1) hendpoint h
  have hlog : B.paperMoment B.primeLogScore (path 1) =
      B.paperMoment B.primeLogScore 0 :=
    B.endpoint_preserves_primeLogScore_of_compatibility
      hcompat Delta 0 (path 1) hendpoint
  have hmarked : ∀ p ∈ monitoredPrimes,
      |markedTarget p - B.paperMoment (B.markedValuation p) (path 1)| ≤
        (Cinitial + Cmass * Crow) * N / ((p : ℝ) * B.L) := by
    intro p hp
    apply B.abs_target_sub_markedMoment_one_le_of_initial_rate
      p (hprimePos p hp) path
      (fun t => B.vectorFamily.vectorField (B.targetVector Delta) (path t))
      (markedTarget p) N Cinitial Cmass Crow hCrow hqMass hderiv
    · intro t ht
      let z : B.EffectiveParamSpace := B.effectiveParamEquiv.symm (path t)
      have hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) :=
        hball t ht
      have hpathEq : B.effectiveParamEquiv z = path t :=
        B.effectiveParamEquiv.apply_symm_apply (path t)
      rw [← hpathEq]
      exact hmarkedRow p hp z hz
    · simpa only [hpathZero] using hinitialMarked p hp
  have hfeasible : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
      B.ambientCombinedWeight
          (frozenAmbientWeight fixedValue fixedWeight) (path t) x ∈
        Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact B.ambientCombinedWeight_mem_Icc_of_paperEffectiveSize
      hC hW hhi hsep
      (frozenAmbientWeight fixedValue fixedWeight)
      hfrozenFeasible (path t) (hsize t ht)
      hfrozenLedger hactiveLedger hlarge
  have hfixed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
      B.combinedWeight fixedWeight (path t) (Sum.inl f) =
        B.combinedWeight fixedWeight 0 (Sum.inl f) := by
    intro t ht f
    exact B.combinedWeight_fixed_unchanged fixedWeight (path t) 0 f
  have hmass : ∀ t ∈ Icc (0 : ℝ) 1,
      (∑ m : B.sampleData.Sample,
        B.activeCoordinateWeight (path t) m) = B.q := by
    intro t ht
    exact B.sum_activeCoordinateWeight (path t)
  have hquotaPath : ∀ t ∈ Icc (0 : ℝ) 1,
      (∑ x : Fixed ⊕ B.sampleData.Sample,
        B.combinedWeight fixedWeight (path t) x) = (quota : ℝ) := by
    intro t ht
    exact B.sum_combinedWeight_eq_integerQuota
      fixedWeight quota hquota (path t)
  exact ⟨path, hpathZero, hball, hsize, hderiv, hbands, hphysical,
    hordinaryLog, hheads, hlog, hmarked, hfeasible, hfixed, hmass,
    hquotaPath⟩

/--
Proposition 8.7 with the full covariance-gap input eliminated in favor of
the two literal analytic Schur blocks.  The nuisance hypothesis is the
finite covariance coercivity of the actual head/physical statistics, and
the main hypothesis is the coercivity of the actual exact-regression Schur
residual.  The full Jacobian gap used by the ODE is a conclusion, with one
constant valid on the whole preselected effective ball.

The effective-velocity estimate is no longer assumed as a conclusion about
the assembled vector field.  Instead the theorem receives the three literal
component bounds for every solution of the actual Schur equation (effective
prime fugacity, nuisance coefficient, and stored slow coordinate) and proves
the velocity bound from the exact block identity.  The marked row remains an
explicit quantitative Lemma 8.6 output used for the post-bridge primewise
rate.
-/
theorem exists_physicallyCenteredFixedPartitionFit_of_exactSchurOutputs
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ)
    (a speed : NNReal) (gammaMain gammaNuisance : ℝ)
    (hgammaMain : 0 < gammaMain)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      ∀ v, gammaNuisance * ‖v‖ ^ 2 ≤
        inner ℝ v (B.nuisanceCovarianceOperator
          (B.effectiveParamEquiv z) v))
    (hSchur : ∀ z (hz : z ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.exactNuisanceRegression (B.effectiveParamEquiv z)
              hgammaNuisance (hGamma z hz)) u)
          (B.covarianceOperator (B.effectiveParamEquiv z)
            (B.schurResidual
              (B.exactNuisanceRegression (B.effectiveParamEquiv z)
                hgammaNuisance (hGamma z hz)) u)))
    (hprime : ∀ z (hz : z ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
        ‖fun p : ArithmeticBandGeometry.BandPrime
              B.sampleData.n B.sampleData.W ↦
            (B.rawGaugeOfMain u).1 (B.partition.band p) +
              (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
          (speed : ℝ))
    (hnuisance : ∀ z (hz : z ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
        ‖B.exactNuisanceRegression (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u‖ ≤ (speed : ℝ))
    (hslow : ∀ z (hz : z ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
        |u MainCoord.slow| ≤ (speed : ℝ))
    (hmargin : speed ≤ a)
    (monitoredPrimes : Finset ℕ)
    (Crow : ℝ) (hCrow : 0 ≤ Crow)
    (hmarkedRow : ∀ p ∈ monitoredPrimes,
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
            (B.markedValuation p)
            (fun m => B.vectorFamily.scalarFamily.score m
              (B.vectorFamily.vectorField (B.targetVector Delta)
                (B.effectiveParamEquiv z)))
            (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ))
    (markedTarget : ℕ → ℝ)
    (N Cinitial Cmass : ℝ)
    (hprimePos : ∀ p ∈ monitoredPrimes, 0 < p)
    (hqMass : B.q ≤ Cmass * N)
    (hinitialMarked : ∀ p ∈ monitoredPrimes,
      |markedTarget p - B.paperMoment (B.markedValuation p) 0| ≤
        Cinitial * N / ((p : ℝ) * B.L))
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ)
    (hquota : (quota : ℝ) = (∑ f, fixedWeight f) + B.q)
    {C Cfixed Cactive : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      ArithmeticModel.physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hfrozenFeasible : ∀ x,
      frozenAmbientWeight fixedValue fixedWeight x ∈ Set.Icc (0 : ℝ) 1)
    (hfrozenLedger : ∀ m : B.sampleData.Sample,
      frozenAmbientWeight fixedValue fixedWeight
        (B.sampleData.value m) ≤ Cfixed / B.L)
    (hactiveLedger : ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L)
    (hlarge : Cfixed +
      Real.exp (2 *
        ((PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * (3 * (a : ℝ)))) *
            Cactive ≤ B.L) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.effectiveParamEquiv.symm (path t) ∈
          closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      (∀ j : Band,
        B.paperMoment (B.bandScore j) (path 1) =
          B.paperMoment (B.bandScore j) 0 + Delta j) ∧
      B.paperMoment B.physicalScore (path 1) =
        B.paperMoment B.physicalScore 0 ∧
      B.paperMoment B.ordinaryLogScore (path 1) =
        B.paperMoment B.ordinaryLogScore 0 ∧
      (∀ h : B.HeadIndex,
        B.paperMoment (B.headIndicator h.1) (path 1) =
          B.paperMoment (B.headIndicator h.1) 0) ∧
      B.paperMoment B.primeLogScore (path 1) =
        B.paperMoment B.primeLogScore 0 ∧
      (∀ p ∈ monitoredPrimes,
        |markedTarget p - B.paperMoment (B.markedValuation p) (path 1)| ≤
          (Cinitial + Cmass * Crow) * N / ((p : ℝ) * B.L)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
        B.ambientCombinedWeight
            (frozenAmbientWeight fixedValue fixedWeight) (path t) x ∈
          Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
        B.combinedWeight fixedWeight (path t) (Sum.inl f) =
          B.combinedWeight fixedWeight 0 (Sum.inl f)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ m : B.sampleData.Sample,
          B.activeCoordinateWeight (path t) m) = B.q) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ x : Fixed ⊕ B.sampleData.Sample,
          B.combinedWeight fixedWeight (path t) x) = (quota : ℝ)) := by
  let gammaFull := min gammaMain gammaNuisance /
    (3 + 2 * (B.canonicalCrossBound / gammaNuisance) ^ 2)
  have hden : 0 < 3 + 2 *
      (B.canonicalCrossBound / gammaNuisance) ^ 2 := by positivity
  have hgammaFull : 0 < gammaFull := by
    exact div_pos (lt_min hgammaMain hgammaNuisance) hden
  have hfull : ∀ z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gammaFull
        (B.effectiveParamEquiv z) := by
    intro z hz
    exact B.hasCovarianceGap_of_uniform_exactSchur
      (B.effectiveParamEquiv z) gammaMain gammaNuisance
      hgammaMain hgammaNuisance (hGamma z hz) (hSchur z hz)
  have hvelocity : ∀ z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      ‖B.effectiveParamEquiv.symm
        (B.vectorFamily.vectorField (B.targetVector Delta)
          (B.effectiveParamEquiv z))‖ ≤ (speed : ℝ) := by
    intro z hz
    exact B.effectiveVelocity_le_of_exactSchur_solution_component_bounds
      (B.effectiveParamEquiv z) Delta hgammaFull (hfull z hz)
      hgammaNuisance (hGamma z hz)
      (hprime z hz) (hnuisance z hz) (hslow z hz)
  exact B.exists_physicallyCenteredFixedPartitionFit_of_analyticOutputs
    hcompat Delta a speed hgammaFull hfull hvelocity hmargin
    monitoredPrimes Crow hCrow hmarkedRow markedTarget
    N Cinitial Cmass hprimePos hqMass hinitialMarked
    fixedValue fixedWeight quota hquota hC hW hhi hsep
    hfrozenFeasible hfrozenLedger hactiveLedger hlarge

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
