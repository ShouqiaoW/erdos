import Erdos390.Full.PaperProposition87CanonicalConclusion
import Erdos390.Full.PaperPermittedRegularMesh
import Erdos390.Full.PaperGuardCensus

/-!
# Paper-order canonical statement of Proposition 8.7

This file fixes the public statement before the analytic orchestration is
attached.  Its order is the one needed in the paper: choose `W`, then the
effective box and the mesh-independent residual constant, then an arbitrary
sufficiently fine permitted partition, and only last the ambient integer
`n`.  All rough-stage and feasibility data occur as their literal finite
envelopes or ledgers.  No covariance gap, inverse, target estimate, nuisance
row, marked row, speed inequality, or exponential-slack inequality occurs in
the statement.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus PaperPermittedRegularMesh
open RegularMeshPrimeCutoffs

/-- The exact canonical, eventual form of the physically centered
fixed-partition proposition. -/
def CanonicalProposition87Statement
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
            ∀ (monitoredPrimes : Finset ℕ),
              (∀ p ∈ monitoredPrimes, p.Prime) →
              (∀ p ∈ monitoredPrimes, p ≤ yNat B.sampleData.n) →
            ∀ (markedTarget : ℕ → ℝ) (N : ℝ),
              0 ≤ N →
              B.q ≤ Cmass * N →
              (∀ p ∈ monitoredPrimes,
                |markedTarget p - B.paperMoment (B.markedValuation p) 0| ≤
                  Cinitial * N / ((p : ℝ) * B.L)) →
            ∀ {Fixed : Type*} [Fintype Fixed]
              (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
              (quota : ℤ),
              (quota : ℝ) = (∑ f, fixedWeight f) + B.q →
              B.sampleData.HeadPatternsSeparated →
              (∀ x,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
                  Set.Icc (0 : ℝ) 1) →
              (∀ m : B.sampleData.Sample,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (B.sampleData.value m) ≤ Cfixed / B.L) →
              (∀ m : B.sampleData.Sample,
                B.baseline.baseWeight m ≤ Cactive / B.L) →
              B.HasPhysicallyCenteredFixedPartitionFit Delta a
                monitoredPrimes markedTarget N Cpost
                fixedValue fixedWeight quota

end

end Erdos390.Full.PaperBridgeFit
