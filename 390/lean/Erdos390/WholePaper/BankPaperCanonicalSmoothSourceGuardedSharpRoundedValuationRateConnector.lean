import Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureFinal

/-!
# Rounded smooth-source to guarded valuation rate

The sharp common-profile closure controls the unrounded barycentric active
moment against the constant guarded label-one broad layer.  The exact
frozen-top decomposition has one additional term: the same nearest-integer
mass is inserted in each physical copy of the zero head cell.

This file bounds that literal correction directly.  Its cell mass is at most
`1 / 4`, by the universal half-unit nearest-integer error, and reciprocal
zero-cell valuation means then put it on the same
`secondOrderScale / (p * L)` scale.
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
open Erdos390.Full.FiniteProbability

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## The synchronized guarded active mass -/

/-- The guarded label-one active mass has its pointwise paper-scale upper
bound without an additional analytic hypothesis.  Indeed, its support is
contained in the raw label-one smooth pool, which in turn lies in an
interval of cardinality at most `n`. -/
theorem
    abs_bankPaperCanonicalGuardedSmoothBaseMass_le_abs_mul_secondOrderScale
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) (betaAct : Real)
    (hn : 1 < n) :
    |bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar W K betaAct| ≤
      |betaAct| * secondOrderScale n := by
  have hL : 0 < L n := L_pos hn
  have hguardedSubset :
      R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1 ⊆
        bankPaperCanonicalRawSmoothBasePool W n h K := by
    simpa only [bankPaperCanonicalRawSmoothBasePool] using
      R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
        certificate deltaStar W K 1
  have hrawSubset :
      bankPaperCanonicalRawSmoothBasePool W n h K ⊆
        roughBroadLowerBlock n h K := by
    intro a ha
    change a ∈ roughCanonicalBroadCorrectionPool W n h K (yNat n) 1 at ha
    have haRow := mem_completeRoughRowFiber.mp ha
    exact (mem_roughHeadFree.mp haRow.1).1
  have hcardNat :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K 1).card ≤ n := by
    calc
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card ≤
          (bankPaperCanonicalRawSmoothBasePool W n h K).card :=
        Finset.card_le_card hguardedSubset
      _ ≤ (roughBroadLowerBlock n h K).card :=
        Finset.card_le_card hrawSubset
      _ ≤ n := by
        simp only [roughBroadLowerBlock, Nat.card_Ioc]
        omega
  have hcard :
      ((R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K 1).card : Real) ≤ (n : Real) := by
    exact_mod_cast hcardNat
  have hcardNonneg :
      (0 : Real) ≤
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card : Real) :=
    Nat.cast_nonneg _
  unfold bankPaperCanonicalGuardedSmoothBaseMass
  rw [abs_mul, abs_div, abs_of_pos hL, abs_of_nonneg hcardNonneg]
  rw [secondOrderScale]
  calc
    |betaAct| / L n *
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card : Real) ≤
        |betaAct| / L n * (n : Real) :=
      mul_le_mul_of_nonneg_left hcard
        (div_nonneg (abs_nonneg _) hL.le)
    _ = |betaAct| * ((n : Real) / L n) := by ring

/-! ## The literal nearest-integer correction -/

/-- Each of the two zero-head cells receives half of a row-mass rounding
error of absolute size at most `1 / 2`. -/
theorem
    abs_bankPaperCanonicalTopFrozenNearestIntegerCellMass_le_quarter
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha qTilde : Real) :
    |bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
        B R certificate deltaStar betaProt alpha qTilde| ≤
      (1 : Real) / 4 := by
  let mFrozen :=
    bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
      B R certificate deltaStar betaProt alpha
  have hround :=
    bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
      mFrozen qTilde
  unfold bankPaperCanonicalTopFrozenNearestIntegerCellMass
  unfold bankPaperCanonicalTopFrozenRoundedActiveMass
  change
    |(bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde -
        qTilde) / 2| ≤ (1 : Real) / 4
  rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
  linarith

/-- Reciprocal valuation means in the two physical zero-head cells give a
literal reciprocal-prime bound for the nearest-integer valuation moment. -/
theorem
    abs_bankPaperCanonicalTopFrozenNearestIntegerValuationMoment_le
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha qTilde Azero : Real) (p : Nat)
    (hp : p.Prime) (hAzero : 0 ≤ Azero)
    (hmean : ∀ sigma : PhysicalSign,
      (B.guardedCellProbability (none, sigma)).expect
          (fun m ↦ valuation p (m : Nat)) ≤ Azero / (p : Real)) :
    |bankPaperCanonicalTopFrozenNearestIntegerValuationMoment (K := K)
        B R certificate deltaStar betaProt alpha qTilde p| ≤
      Azero / (2 * (p : Real)) := by
  let cellMass :=
    bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
      B R certificate deltaStar betaProt alpha qTilde
  let meanMinus :=
    (B.guardedCellProbability (none, .minus)).expect
      (fun m ↦ valuation p (m : Nat))
  let meanPlus :=
    (B.guardedCellProbability (none, .plus)).expect
      (fun m ↦ valuation p (m : Nat))
  have hmass : |cellMass| ≤ (1 : Real) / 4 := by
    simpa only [cellMass] using
      abs_bankPaperCanonicalTopFrozenNearestIntegerCellMass_le_quarter
        (K := K) B R certificate deltaStar betaProt alpha qTilde
  have hminus0 : 0 ≤ meanMinus :=
    (B.guardedCellProbability (none, .minus)).expect_nonneg _
      (fun m ↦ valuation_nonneg p (m : Nat))
  have hplus0 : 0 ≤ meanPlus :=
    (B.guardedCellProbability (none, .plus)).expect_nonneg _
      (fun m ↦ valuation_nonneg p (m : Nat))
  have hminus : meanMinus ≤ Azero / (p : Real) := by
    simpa only [meanMinus] using hmean .minus
  have hplus : meanPlus ≤ Azero / (p : Real) := by
    simpa only [meanPlus] using hmean .plus
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hrate0 : 0 ≤ Azero / (p : Real) :=
    div_nonneg hAzero hpR.le
  unfold bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
  change |cellMass * meanMinus + cellMass * meanPlus| ≤ _
  calc
    |cellMass * meanMinus + cellMass * meanPlus| ≤
        |cellMass * meanMinus| + |cellMass * meanPlus| :=
      abs_add_le _ _
    _ = |cellMass| * meanMinus + |cellMass| * meanPlus := by
      rw [abs_mul, abs_mul, abs_of_nonneg hminus0,
        abs_of_nonneg hplus0]
    _ ≤ ((1 : Real) / 4) * (Azero / (p : Real)) +
        ((1 : Real) / 4) * (Azero / (p : Real)) := by
      exact add_le_add
        (mul_le_mul hmass hminus hminus0 (by norm_num))
        (mul_le_mul hmass hplus hplus0 (by norm_num))
    _ = Azero / (2 * (p : Real)) := by
      field_simp [hpR.ne']
      ring

/-! ## Sharp rounded finite-rate connector -/

/-- The complete rounded label-one source-to-guarded defect has the paper
rate.  The hypotheses retained at the call site are the honest construction
interfaces not determined by the valuation analysis itself:

* literal identification with the canonical guarded sample;
* synchronization of `qTilde` with the guarded smooth-base mass;
* membership of the structured active values in the guarded smooth row; and
* reciprocal valuation means in the two zero-head cells.

The active coefficient `betaAct` is fixed outside the uniform quantifiers,
so the resulting constant may honestly depend on its absolute value.
-/
theorem
    exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate
    (Phead : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag Phead → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W K0 depth : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W)
    {c : Real} (hc : 0 < c)
    (betaAct Azero : Real) (hAzero : 0 ≤ Azero) :
    ∃ Csource : Real, 0 < Csource ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData (PaperHeadSimplex.Tag Phead) Band)
        (R : BankPaperRealization B.sampleData.n
          (upperEndpoint B.sampleData.n
            (upperTailLength c B.sampleData.n)))
          (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (T : BarycentricTarget B.sampleData)
        (deltaStar betaProt qTilde : Real),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
            (rawCell Patterns I B.sampleData.n cell \
              (G B.sampleData.n).guards).Nonempty),
          B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Patterns I (G B.sampleData.n)
                hsep hremaining →
          qTilde = bankPaperCanonicalGuardedSmoothBaseMass R certificate
              deltaStar B.sampleData.W (K0 + 1) betaAct →
          deltaStar ≤ 1 →
          (∀ m : B.sampleData.Sample,
            B.sampleData.value m ∈
              R.roughCanonicalGuardedRow certificate deltaStar
                (K0 + 1) 1) →
          ∀ _hpool :
            (R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W (K0 + 1) 1).Nonempty,
          ∀ p : BandPrime B.sampleData.n B.sampleData.W,
            (∀ sigma : PhysicalSign,
              (B.guardedCellProbability (none, sigma)).expect
                  (fun m ↦ valuation p.1 (m : Nat)) ≤
                Azero / (p.1 : Real)) →
            RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
              B K0 R certificate T deltaStar betaProt betaAct qTilde p.1
              (Csource *
                (secondOrderScale B.sampleData.n /
                  ((p.1 : Real) * B.L))) := by
  obtain ⟨Csharp, hCsharp, Nsharp, hsharp⟩ :=
    exists_uniform_scaledActive_sub_guardedSmoothBase_valuationMoment_paperRate
      Phead Patterns I Cprom Cbank G W (K0 + 1) depth hW hHeadLe hc
  have hscaleEvent : ∀ᶠ n : Nat in atTop,
      1 ≤ secondOrderScale n / L n :=
    secondOrderScale_div_L_tendsto_atTop.eventually
      (eventually_ge_atTop 1)
  obtain ⟨Nscale, hNscale⟩ := Filter.eventually_atTop.mp hscaleEvent
  let Csource : Real := |betaAct| * Csharp + Azero / 2 + 1
  have hCsource : 0 < Csource := by
    dsimp only [Csource]
    positivity
  refine ⟨Csource, hCsource, max 2 (max Nsharp Nscale), ?_⟩
  intro Band _instBand _instBandDec B R certificate T
    deltaStar betaProt qTilde hN hBW hsep hremaining
    hcanonical hmassSync hdeltaUpper hvalues _hpool p hmean
  have hn : 1 < B.sampleData.n := by omega
  have hNsharp : Nsharp ≤ B.sampleData.n := by omega
  have hNscaleBound : Nscale ≤ B.sampleData.n := by omega
  have hp := prime_of_mem_primeBand p.2
  have hpR : (0 : Real) < p.1 := by exact_mod_cast hp.pos
  have hL : 0 < B.L := B.L_pos
  let scale : Real :=
    secondOrderScale B.sampleData.n / ((p.1 : Real) * B.L)
  have hscale0 : 0 ≤ scale := by
    dsimp only [scale]
    exact
      div_nonneg (secondOrderScale_pos (by omega)).le
        (mul_nonneg hpR.le hL.le)
  have hscaleOne :
      1 ≤ secondOrderScale B.sampleData.n / B.L := by
    simpa only [BridgeData.L] using
      hNscale B.sampleData.n hNscaleBound
  have hqBound :
      |qTilde| ≤ |betaAct| * secondOrderScale B.sampleData.n := by
    rw [hmassSync]
    exact
      abs_bankPaperCanonicalGuardedSmoothBaseMass_le_abs_mul_secondOrderScale
        R certificate deltaStar B.sampleData.W (K0 + 1) betaAct hn
  have hsharpBound :=
    hsharp B R certificate T deltaStar betaAct qTilde
      hNsharp hBW hsep hremaining hcanonical hmassSync _hpool p
  have hprincipal :
      |bankPaperCanonicalScaledActiveValuationMoment T qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1| ≤
        (|betaAct| * Csharp) * scale := by
    calc
      |bankPaperCanonicalScaledActiveValuationMoment T qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1| ≤
        |qTilde| * (Csharp / ((p.1 : Real) * B.L)) :=
          hsharpBound
      _ ≤ (|betaAct| * secondOrderScale B.sampleData.n) *
          (Csharp / ((p.1 : Real) * B.L)) := by
        exact mul_le_mul_of_nonneg_right hqBound
          (div_nonneg hCsharp.le (mul_nonneg hpR.le hL.le))
      _ = (|betaAct| * Csharp) * scale := by
        dsimp only [scale]
        ring
  have hnearestRaw :=
    abs_bankPaperCanonicalTopFrozenNearestIntegerValuationMoment_le
      (K := K0 + 1) B R certificate deltaStar betaProt
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      qTilde Azero p.1 hp hAzero hmean
  have hnearest :
      |bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p.1| ≤
        (Azero / 2) * scale := by
    calc
      |bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p.1| ≤
        Azero / (2 * (p.1 : Real)) := hnearestRaw
      _ = (Azero / (2 * (p.1 : Real))) * 1 := by ring
      _ ≤ (Azero / (2 * (p.1 : Real))) *
          (secondOrderScale B.sampleData.n / B.L) := by
        exact mul_le_mul_of_nonneg_left hscaleOne
          (div_nonneg hAzero
            (mul_nonneg (by norm_num) hpR.le))
      _ = (Azero / 2) * scale := by
        dsimp only [scale]
        field_simp [hpR.ne', hL.ne']
  have hdecomp :=
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_scaled_sub_guardedBase_add_nearestInteger
      B K0 R certificate T deltaStar betaProt betaAct qTilde p.1
      (by omega : 1 ≤ B.sampleData.n) hdeltaUpper hvalues
  unfold RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
  rw [hdecomp]
  calc
    |bankPaperCanonicalScaledActiveValuationMoment T qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1 +
        bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p.1| ≤
      |bankPaperCanonicalScaledActiveValuationMoment T qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1| +
        |bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p.1| :=
      abs_add_le _ _
    _ ≤ (|betaAct| * Csharp) * scale + (Azero / 2) * scale :=
      add_le_add hprincipal hnearest
    _ = (|betaAct| * Csharp + Azero / 2) * scale := by ring
    _ ≤ Csource * scale := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp only [Csource]; linarith) hscale0
    _ = Csource *
        (secondOrderScale B.sampleData.n /
          ((p.1 : Real) * B.L)) := by
      rfl

end BankPaperRealization

end

end Erdos390.WholePaper
