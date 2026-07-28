import Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureBroad
import Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureMixture

/-!
# Full sharp smooth-source valuation lift

This file combines the two separately proved common-profile estimates:

* every canonical guarded active cell; and
* the canonical guarded label-one broad pool.

The only remaining step is the exact barycentric algebra.  In particular,
the theorem below does not assume a cell-versus-pool valuation comparison.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PrimePowerCovariance
open Erdos390.Full.FiniteProbability

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-- The unrounded scaled active valuation moment and the constant guarded
smooth-base valuation moment differ by the sharp paper rate.  All analytic
inputs are discharged by the fixed-cell, moving-prefix, prime-power-tail,
guard-census, and barycentric theorems proved earlier in this closure chain.
-/
theorem
    exists_uniform_scaledActive_sub_guardedSmoothBase_valuationMoment_paperRate
    (Phead : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag Phead → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W K depth : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W)
    {c : Real} (hc : 0 < c) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData (PaperHeadSimplex.Tag Phead) Band)
        (R : BankPaperRealization B.sampleData.n
          (upperEndpoint B.sampleData.n
            (upperTailLength c B.sampleData.n)))
        (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (T : BarycentricTarget B.sampleData)
        (deltaStar betaAct q : Real),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
            (rawCell Patterns I B.sampleData.n cell \
              (G B.sampleData.n).guards).Nonempty),
          B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Patterns I (G B.sampleData.n)
                hsep hremaining →
          q = bankPaperCanonicalGuardedSmoothBaseMass R certificate
              deltaStar B.sampleData.W K betaAct →
          ∀ _hpool :
            (R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1).Nonempty,
          ∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |bankPaperCanonicalScaledActiveValuationMoment T q p.1 -
                bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
                  B R certificate deltaStar betaAct p.1| ≤
              |q| * (Cval / ((p.1 : Real) * B.L)) := by
  obtain ⟨Ccell, hCcell, Ncell, hcellRate⟩ :=
    exists_uniform_bridge_guardedCell_valuation_mean_profiles_paperRate
      Patterns I Cprom Cbank G W hW hHeadLe
  obtain ⟨Cpool, hCpool, Npool, hpoolRate⟩ :=
    exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate
      W K depth hW hc
  let Cval : Real := Ccell + Cpool
  have hCval : 0 < Cval := by
    dsimp only [Cval]
    positivity
  refine ⟨Cval, hCval, max 2 (max Ncell Npool), ?_⟩
  intro Band _instBand _instBandDec B R certificate T
    deltaStar betaAct q hN hBW hsep hremaining hcanonical hq hpool p
  subst W
  have hn : 1 < B.sampleData.n := by omega
  have hNcell : Ncell ≤ B.sampleData.n := by omega
  have hNpool : Npool ≤ B.sampleData.n := by omega
  have hpBandW : p.1 ∈
      primeBand B.sampleData.n B.sampleData.W := p.2
  have hcell :=
    hcellRate B hNcell rfl hsep hremaining hcanonical p
  have hpoolProfile :=
    hpoolRate R certificate deltaStar hNpool hpBandW
      hpool
  let Kcut := Nat.log p.1 (yNat B.sampleData.n ^ 4)
  let mainSum := ∑ j ∈ positiveExponents Kcut,
    paperDivisibilityMain B.sampleData.n (p.1 ^ j)
  have hcell' :
      ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
        |(B.guardedCellProbability cell).expect
              (fun m ↦ valuation p.1 (m : Nat)) - mainSum| ≤
          Ccell / ((p.1 : Real) * B.L) := by
    intro cell
    simpa only [Kcut, mainSum] using hcell cell
  have hpool' :
      |(uniformOnFinset
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) hpool).expect
          (fun a ↦ valuation p.1 (a : Nat)) - mainSum| ≤
        Cpool / ((p.1 : Real) * B.L) := by
    simpa only [Kcut, mainSum, BridgeData.L,
      Erdos390.Full.Scale.L] using hpoolProfile
  have hpPrime := prime_of_mem_primeBand p.2
  have hpPos : 0 < p.1 := hpPrime.pos
  have hL : 0 < B.L := by
    simpa only [BridgeData.L] using L_pos hn
  have hfinal :=
    abs_bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_le_of_commonProfile
      B R certificate T deltaStar betaAct q mainSum Ccell Cpool p.1
      hq hpool hpPos hL hCcell.le hCpool.le hcell' hpool'
  simpa only [Cval] using hfinal

end BankPaperRealization

end

end Erdos390.WholePaper
