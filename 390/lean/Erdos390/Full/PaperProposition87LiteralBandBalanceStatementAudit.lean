import Erdos390.Full.PaperProposition87LiteralBandBalance

/-!
# Expanded statement audit for literal paper Proposition 8.7

This audit expands the public statement and conclusion abbreviations.  It
therefore checks that the terminal covers every prime in the actual interval
`W < p ≤ y`, identifies `Delta` with the initial residual sums, and concludes
the exact finite residual balance in every arithmetic band.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus PaperPermittedRegularMesh
open RegularMeshPrimeCutoffs

namespace BridgeData

example
    (cMesh : ℝ)
    (I : PhysicalIntervals) (U : ℝ)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank) :
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
                  |markedTarget p -
                      B.paperMoment (B.markedValuation p) 0| ≤
                    Cinitial * N / ((p : ℝ) * B.L)) →
                (∀ j,
                  Delta j =
                    ∑ p ∈ B.partition.data.fiber j,
                      (markedTarget p.1 -
                        B.paperMoment (B.markedValuation p.1) 0)) →
              ∀ {Fixed : Type*} [Fintype Fixed]
                (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
                (quota : ℤ),
                (quota : ℝ) = (∑ f, fixedWeight f) + B.q →
                B.sampleData.HeadPatternsSeparated →
                (∀ x,
                  frozenAmbientWeight fixedValue fixedWeight x ∈
                    Icc (0 : ℝ) 1) →
                (∀ m : B.sampleData.Sample,
                  frozenAmbientWeight fixedValue fixedWeight
                    (B.sampleData.value m) ≤ Cfixed / B.L) →
                (∀ m : B.sampleData.Sample,
                  B.baseline.baseWeight m ≤ Cactive / B.L) →
                ∃ path : ℝ → B.ParamSpace,
                  (path 0 = 0 ∧
                    (∀ t ∈ Icc (0 : ℝ) 1,
                      B.effectiveParamEquiv.symm (path t) ∈
                        closedBall
                          (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
                    (∀ t ∈ Icc (0 : ℝ) 1,
                      B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
                    (∀ t ∈ Icc (0 : ℝ) 1,
                      HasDerivWithinAt path
                        (B.vectorFamily.vectorField
                          (B.targetVector Delta) (path t))
                        (Icc (0 : ℝ) 1) t) ∧
                    (∀ j : Fin (M.cellCount + 1),
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
                    (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
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
                        B.combinedWeight fixedWeight (path t) x) =
                          (quota : ℝ)) ∧
                  ∀ j : Fin (M.cellCount + 1),
                    (∑ p ∈ B.partition.data.fiber j,
                      (markedTarget p.1 -
                        B.paperMoment (B.markedValuation p.1) (path 1))) =
                      0 := by
  simpa only [CanonicalProposition87LiteralBalanceStatement,
    HasPaperProposition87Conclusion, IsPaperProposition87Path,
    markedBandResidual] using
      canonical_proposition87_literalBandBalance
        cMesh I U Cprom Cbank ledger

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
