import Erdos390.Full.PaperProposition87CanonicalEventually

/-!
# Literal residual-balance form of paper Proposition 8.7

The generalized Proposition 8.7 engine takes a prescribed vector of band
moment increments.  In the paper that vector is not arbitrary: its `j`th
coordinate is the initial sum of the marked residuals in the `j`th prime
band.  This file records that specialization and derives the displayed
post-fit identity `sum_{p in P_j} r_p = 0` exactly at finite `n`.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The active marked residual summed over one actual arithmetic prime band. -/
def markedBandResidual [Nonempty Head]
    (markedTarget : ℕ → ℝ) (xi : B.ParamSpace) (j : Band) : ℝ :=
  ∑ p ∈ B.partition.data.fiber j,
    (markedTarget p.1 - B.paperMoment (B.markedValuation p.1) xi)

/-- A band-score moment is exactly the sum of its marked valuation moments.
This is a finite identity, with no asymptotic or squarefree replacement. -/
theorem paperMoment_bandScore_eq_sum_markedValuation [Nonempty Head]
    (xi : B.ParamSpace) (j : Band) :
    B.paperMoment (B.bandScore j) xi =
      ∑ p ∈ B.partition.data.fiber j,
        B.paperMoment (B.markedValuation p.1) xi := by
  simp only [paperMoment, bandScore, markedValuation,
    FiniteExponentialFamily.moment, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- If `Delta` is the initial band-residual vector and the endpoint changes
each band moment by `Delta`, then every endpoint band residual is exactly
zero. -/
theorem markedBandResidual_eq_zero_of_bandMoment_increment
    [Nonempty Head]
    (Delta : Band → ℝ) (markedTarget : ℕ → ℝ)
    (xi0 xi1 : B.ParamSpace)
    (hDelta : ∀ j, Delta j = B.markedBandResidual markedTarget xi0 j)
    (hbands : ∀ j,
      B.paperMoment (B.bandScore j) xi1 =
        B.paperMoment (B.bandScore j) xi0 + Delta j) :
    ∀ j, B.markedBandResidual markedTarget xi1 j = 0 := by
  intro j
  rw [markedBandResidual, Finset.sum_sub_distrib,
    ← B.paperMoment_bandScore_eq_sum_markedValuation xi1 j,
    hbands j, hDelta j, markedBandResidual,
    Finset.sum_sub_distrib,
    ← B.paperMoment_bandScore_eq_sum_markedValuation xi0 j]
  ring

/-- The path-level output of the generalized finite fit, with the monitored
set specialized to every actual medium prime. -/
def IsPaperProposition87Path
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (Delta : Band → ℝ) (a : NNReal)
    (markedTarget : ℕ → ℝ) (N Cpost : ℝ)
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ) (path : ℝ → B.ParamSpace) : Prop :=
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
    (∀ p : ℕ, p.Prime → p ≤ B.sampleData.W →
      B.paperMoment (B.markedValuation p) (path 1) =
        B.paperMoment (B.markedValuation p) 0) ∧
    B.paperMoment B.primeLogScore (path 1) =
      B.paperMoment B.primeLogScore 0 ∧
    (∀ p ∈ ArithmeticModel.primeBand
        B.sampleData.n B.sampleData.W,
      |markedTarget p -
          B.paperMoment (B.markedValuation p) (path 1)| ≤
        Cpost * N / ((p : ℝ) * B.L)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
      B.ambientCombinedWeight
          (frozenAmbientWeight fixedValue fixedWeight)
          (path t) x ∈ Icc (0 : ℝ) 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
      B.combinedWeight fixedWeight (path t) (Sum.inl f) =
        B.combinedWeight fixedWeight 0 (Sum.inl f)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      (∑ m : B.sampleData.Sample,
        B.activeCoordinateWeight (path t) m) = B.q) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      (∑ x : Fixed ⊕ B.sampleData.Sample,
        B.combinedWeight fixedWeight (path t) x) = (quota : ℝ)

/-- The literal conclusion displayed in paper Proposition 8.7.  In addition
to all finite-fit outputs, it states the exact residual cancellation in every
actual prime band and the pointwise rate for every `W < p ≤ y`. -/
def HasPaperProposition87Conclusion
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (Delta : Band → ℝ) (a : NNReal)
    (markedTarget : ℕ → ℝ) (N Cpost : ℝ)
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ) : Prop :=
  ∃ path : ℝ → B.ParamSpace,
    B.IsPaperProposition87Path Delta a markedTarget N Cpost
      fixedValue fixedWeight quota path ∧
    ∀ j : Band, B.markedBandResidual markedTarget (path 1) j = 0

/-- Upgrade the generalized finite-fit endpoint to the literal residual form
used in the paper. -/
theorem hasPaperProposition87Conclusion_of_fit
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (Delta : Band → ℝ) (a : NNReal)
    (markedTarget : ℕ → ℝ) (N Cpost : ℝ)
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ)
    (hDelta : ∀ j,
      Delta j = B.markedBandResidual markedTarget 0 j)
    (hfit : B.HasPhysicallyCenteredFixedPartitionFit Delta a
      (ArithmeticModel.primeBand B.sampleData.n B.sampleData.W)
      markedTarget N Cpost fixedValue fixedWeight quota) :
    B.HasPaperProposition87Conclusion Delta a markedTarget N Cpost
      fixedValue fixedWeight quota := by
  unfold HasPhysicallyCenteredFixedPartitionFit at hfit
  obtain ⟨path, hpath⟩ := hfit
  refine ⟨path, ?_, ?_⟩
  · exact hpath
  · exact B.markedBandResidual_eq_zero_of_bandMoment_increment
      Delta markedTarget 0 (path 1) hDelta hpath.2.2.2.2.1

end BridgeData

open ArithmeticModel PaperGuardCensus PaperPermittedRegularMesh
open RegularMeshPrimeCutoffs

/-- Paper-order, literal-residual statement of Proposition 8.7. -/
def CanonicalProposition87LiteralBalanceStatement
    (cMesh : ℝ)
    (I : PhysicalIntervals) (U : ℝ)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank) : Prop :=
  0 < cMesh →
  1 ≤ U →
  (∀ sigma, 1 ≤ I.lower sigma) →
  (∀ sigma, I.upper sigma ≤ U) →
  ∃ meshTol : ℝ, 0 < meshTol ∧
  ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
    ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
      (Phead : Head → HeadPattern.Pattern),
    (∀ h : Head, ∀ p : ℕ,
      p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
    ∀ (Ctarget Cinitial Cmass Cfixed Cactive marginFloor : ℝ),
      0 ≤ Ctarget → 0 ≤ Cinitial → 0 ≤ Cmass →
      0 ≤ Cfixed → 0 ≤ Cactive → 0 < marginFloor →
    ∃ a : NNReal, 0 < (a : ℝ) ∧
    ∃ Cpost : ℝ, 0 ≤ Cpost ∧
    ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
      (hdelta : 0 < delta)
      (_hPermitted : IsPermitted (cMesh := cMesh) M),
      delta + eta ≤ meshTol →
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            (hscale : B.w = delta + eta) →
            ∀ (T : BarycentricTarget B.sampleData),
              marginFloor ≤ T.cellMassMargin →
              B.baseline = T.baseline →
            ∀ (Delta : Fin (M.cellCount + 1) → ℝ),
              B.HasTargetEnvelopes Ctarget Delta →
            ∀ (markedTarget : ℕ → ℝ) (N : ℝ),
              0 ≤ N →
              B.q ≤ Cmass * N →
              (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
                |markedTarget p - B.paperMoment (B.markedValuation p) 0| ≤
                  Cinitial * N / ((p : ℝ) * B.L)) →
              (∀ j, Delta j = B.markedBandResidual markedTarget 0 j) →
            ∀ {Fixed : Type*} [Fintype Fixed]
              (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
              (quota : ℤ),
              (quota : ℝ) = (∑ f, fixedWeight f) + B.q →
              B.sampleData.HeadPatternsSeparated →
              (∀ x,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
                  Icc (0 : ℝ) 1) →
              (∀ m : B.sampleData.Sample,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (B.sampleData.value m) ≤ Cfixed / B.L) →
              (∀ m : B.sampleData.Sample,
                B.baseline.baseWeight m ≤ Cactive / B.L) →
              B.HasPaperProposition87Conclusion Delta a markedTarget N Cpost
                fixedValue fixedWeight quota

namespace BridgeData

/-- Assumption-free literal paper terminal.  It specializes the generalized
engine to the full arithmetic prime band and closes the displayed exact
band-residual equations. -/
theorem canonical_proposition87_literalBandBalance
    (cMesh : ℝ)
    (I : PhysicalIntervals) (U : ℝ)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank) :
    CanonicalProposition87LiteralBalanceStatement
      cMesh I U Cprom Cbank ledger := by
  have hgeneral := canonical_proposition87 cMesh I U Cprom Cbank ledger
  unfold CanonicalProposition87Statement at hgeneral
  unfold CanonicalProposition87LiteralBalanceStatement
  intro hcMesh hU hlowerOne hupperU
  obtain ⟨meshTol, hmeshTol, W₀, hWgeneral⟩ :=
    hgeneral hcMesh hU hlowerOne hupperU
  refine ⟨meshTol, hmeshTol, W₀, ?_⟩
  intro W hW Head _instHeadFintype _instHeadDecidable _instHeadNonempty
    Phead hPhead Ctarget Cinitial Cmass Cfixed Cactive marginFloor
    hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  obtain ⟨a, ha, Cpost, hCpost, hMeshGeneral⟩ :=
    hWgeneral W hW Phead hPhead Ctarget Cinitial Cmass Cfixed Cactive
      marginFloor hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  refine ⟨a, ha, Cpost, hCpost, ?_⟩
  intro delta eta M hdelta hPermitted hfine
  have hEventual := hMeshGeneral M hdelta hPermitted hfine
  filter_upwards [hEventual] with n hn
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline Delta henv markedTarget N hN hqMass
    hinitialMarked hDelta Fixed _instFixedFintype fixedValue fixedWeight
    quota hquota hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
  have hfit := hn B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline Delta henv
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p hp ↦ prime_of_mem_primeBand hp)
    (fun p hp ↦ le_yNat_of_mem_primeBand hp)
    markedTarget N hN hqMass hinitialMarked fixedValue fixedWeight quota
    hquota hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
  exact B.hasPaperProposition87Conclusion_of_fit Delta a markedTarget N Cpost
    fixedValue fixedWeight quota hDelta hfit

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
