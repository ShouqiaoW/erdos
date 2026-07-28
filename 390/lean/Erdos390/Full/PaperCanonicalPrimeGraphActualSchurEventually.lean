import Erdos390.Full.PaperCanonicalPrimeGraphReferenceEventually
import Erdos390.Full.PaperActualFullProjectedInverseEventually
import Erdos390.Full.PaperActualFullEffectiveBall
import Erdos390.Full.PaperCanonicalMarkedNuisanceRows
import Erdos390.Full.PaperSelectedMeshSchurEventually
import Erdos390.Full.RegularRelativeMeshInteriorAnchors

/-!
# Canonical prime-graph inverse through the literal nuisance Schur complement

This is the paper-order, assumption-free closure of the sharp arithmetic
reference argument.  The structural cutoff is chosen before the regular
mesh, the finite head family, and the effective tilt ball.  After those data
are fixed, all squarefree-profile, full-valuation, moving-low, marked-row,
and nuisance-Schur smallness estimates are constructed internally.

The final equivalence is not an abstract comparison map: it is pointwise
equal to the literal finite arithmetic map `actualBandSchurLinearMap`.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimeSums PaperWeightedInverseExport MovingLowGaugeTransfer
open OmittedTiltPairChamber PaperPrimePowerChamberError
open PaperGuardCensus RegularMeshPrimeCutoffs

namespace BridgeData

set_option maxHeartbeats 4000000 in
/-- Exact paper-order terminal for the literal actual nuisance-Schur band
operator.  There are no profile, row-error, inverse, convergence, or
smallness assumptions in the statement.  In particular, `W` is fixed before
`delta`, the mesh, the head family, and the effective ball. -/
theorem exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cschur : ℝ, 0 < Cschur ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + M.ratio ≤ meshTol →
        ∀ (anchors : Finset (Fin M.cellCount)), anchors.Nonempty →
          (∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k) →
          (∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ)) →
          ((1 / 8 : ℝ) ≤ (∑ k ∈ anchors, M.width k) / 2) →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            ∀ (T : BarycentricTarget B.sampleData)
              (_hTmargin : marginFloor ≤ T.cellMassMargin)
              (hbaseline : B.baseline = T.baseline),
              ∃ e : ∀ (z : B.EffectiveParamSpace),
                  z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                    B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                (∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                  e z hz q =
                    B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by
                          intro sigma
                          rw [hcanonical]
                          rfl)
                        (by
                          intro sigma
                          rw [hcanonical]
                          rfl)
                        T hbaseline hBWlarge z hz) q) ∧
                ∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                  paperSharpNorm B.harmonicMass B.bandCenter
                      (B.partition.center_ne_zero B.n_gt_one)
                      ((e z hz).symm v) ≤
                    Cschur *
                      paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one) v := by
  obtain ⟨meshTol, hmeshTol, Cref, hCref, Wref, hreferenceEvent⟩ :=
    @exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  let r : ℝ := canonicalProjectedPerturbationRadius Cref
  let Cfull : ℝ := 2 * Cref
  let Cschur : ℝ := 2 * Cfull
  have hr : 0 < r := by
    dsimp only [r]
    exact canonicalProjectedPerturbationRadius_pos hCref
  have hCfull : 0 < Cfull := by
    dsimp only [Cfull]
    positivity
  have hCschur : 0 < Cschur := by
    dsimp only [Cschur]
    positivity
  let K : ℝ := 2 * Real.log 4
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hInvNat : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ))
      atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp
      tendsto_natCast_atTop_atTop :
        Tendsto (fun W : ℕ ↦ ((W : ℝ))⁻¹) atTop (nhds 0))
    simpa only [one_div] using h
  let squareTailConstant : ℝ :=
    (1 / DickmanBasic.rho DickmanBasic.U) ^ 2 + CKernel
  have hSquareTail : Tendsto (fun W : ℕ ↦
      squareTailConstant * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ squareTailConstant * (1 / (W : ℝ)))
          atTop (nhds (squareTailConstant * 0)))
  let fullTailConstant : ℝ := 3 * Cpow * (K + 1)
  have hFullTail : Tendsto (fun W : ℕ ↦
      fullTailConstant * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ fullTailConstant * (1 / (W : ℝ)))
          atTop (nhds (fullTailConstant * 0)))
  obtain ⟨Wsquare, hWsquare⟩ := eventually_atTop.1
    (hSquareTail.eventually (eventually_lt_nhds hr))
  obtain ⟨Wfull, hWfull⟩ := eventually_atTop.1
    (hFullTail.eventually (eventually_lt_nhds hr))
  let W₀ : ℕ := max Wref
    (max RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff
      (max Wsquare (max Wfull 2)))
  refine ⟨meshTol, hmeshTol, Cschur, hCschur, W₀, ?_⟩
  intro W hWcutoff delta eta M hdelta hmesh anchors hAnchors
    hIdealLower hIdealUpper hIdealMass Head _instFintype _instDecidable
    _instNonempty Phead hhead I U hU hlowerOne hupperU Cprom Cbank
    ledger a marginFloor hmarginFloor
  have hWref : Wref ≤ W :=
    (le_max_left _ _).trans hWcutoff
  have hWcenter :
      RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff ≤ W :=
    ((le_max_left _ (max Wsquare (max Wfull 2))).trans
      (le_max_right Wref _)).trans hWcutoff
  have hWsquare' : Wsquare ≤ W :=
    ((le_max_left Wsquare (max Wfull 2)).trans
      (le_max_right
        RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff _)).trans
      ((le_max_right Wref _).trans hWcutoff)
  have hWfull' : Wfull ≤ W :=
    ((le_max_left Wfull 2).trans
      (le_max_right Wsquare _)).trans
      ((le_max_right
        RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff _).trans
        ((le_max_right Wref _).trans hWcutoff))
  have hWtwo : 2 ≤ W :=
    ((le_max_right Wfull 2).trans
      (le_max_right Wsquare _)).trans
      ((le_max_right
        RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff _).trans
        ((le_max_right Wref _).trans hWcutoff))
  have hWone : 1 < W := by omega
  have hSquareTailLt :
      squareTailConstant * (1 / (W : ℝ)) < r :=
    hWsquare W hWsquare'
  have hFullTailLt :
      fullTailConstant * (1 / (W : ℝ)) < r :=
    hWfull W hWfull'
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hhead h p).mp hp |>.2
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I U hlowerOne hupperU Cprom Cbank ledger W hWone hHeadLe
        Acoef Aphys hAcoef hAphys
  obtain ⟨_hCpowTerminal, hfullTerminal⟩ :=
    boxIndependent_canonicalRaw_fullSharp
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, hepsilon75Rate,
      hcombinedRateRaw, Nfull, hfullRaw⟩ :=
    hfullTerminal W hWone hHeadLe Acoef hAcoef Aphys hAphys
  obtain ⟨markedError, hmarked0, hmarkedRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger W hWone
        hHeadLe a
  let Calpha : ℝ :=
    RegularMeshPrimeCutoffs.canonicalCenterEnvelopeConstant delta
  let centerScale : ℝ := 1 / Calpha
  have hCalpha : 0 < Calpha := by
    dsimp only [Calpha]
    exact RegularMeshPrimeCutoffs.canonicalCenterEnvelopeConstant_pos hdelta
  have hcenterScale : 0 < centerScale := by
    dsimp only [centerScale]
    exact one_div_pos.mpr hCalpha
  let combined : ℕ → ℝ := fun n ↦
    canonicalCombinedPowerCorrection
      Phead I U Cprom Cbank W Acoef Aphys n
  have hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    simpa only [combined, canonicalCombinedPowerCorrection] using
      hcombinedRateRaw
  have hSquareRemainderT := tendsto_squarefreeSharpProfileRemainder
    profileError Calpha K CKernel W hprofileT hprofileRate
  have hSquareSmall : ∀ᶠ n : ℕ in atTop,
      squarefreeSharpProfileRemainder
        profileError Calpha K CKernel W n < r :=
    hSquareRemainderT.eventually (eventually_lt_nhds (by
      simpa only [squareTailConstant] using hSquareTailLt))
  have hFullRemainderT := tendsto_canonicalFullSharpRemainder
    epsilon75 combined Cpow Calpha K W
      hepsilon75T hepsilon75Rate hcombinedRate
  have hFullSmall : ∀ᶠ n : ℕ in atTop,
      canonicalFullSharpRemainder
        epsilon75 combined Cpow Calpha K W n < r :=
    hFullRemainderT.eventually (eventually_lt_nhds (by
      simpa only [fullTailConstant] using hFullTailLt))
  have hReference := hreferenceEvent W hWref Head M hdelta hmesh anchors hAnchors
      hIdealLower hIdealUpper hIdealMass
  have hCenterInverse :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_inverse
      M hdelta W hWcenter
  have hCenterLower :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_lower
      M hdelta W hWcenter
  have hBandT := eventually_bandTReciprocalSum_le W
  have hSchurConnector :=
    eventually_exists_uniform_actualBandSchurEquiv_and_quadratic
      (Head := Head) (Band := Fin (M.cellCount + 1))
      I hU hlowerOne hupperU W hWone a marginFloor centerScale Cfull
        hmarginFloor hcenterScale hCfull markedError hmarked0 hmarkedRate
  filter_upwards [hReference, hCenterInverse, hCenterLower, hBandT,
      hSquareSmall, hFullSmall, hSchurConnector,
      eventually_ge_atTop Nprofile, eventually_ge_atTop Nfull,
      eventually_ge_atTop Nmarked] with
      n hReferenceN hCenterInverseN hCenterLowerN hBandTN
      hSquareN hFullN hSchurN hnProfile hnFull hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition T hTmargin
    hbaseline
  subst n
  subst W
  obtain ⟨cert, referenceEquiv, hreference, hinvReference⟩ :=
    hReferenceN B rfl rfl hpartition
  obtain ⟨hWne, S, hpartitionCanonical⟩ := hpartition
  have hPattern : B.sampleData.pattern = Phead := by
    rw [hcanonical]
    rfl
  have hLo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hHi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hGuards : B.sampleData.guards =
      (ledger B.sampleData.n).guards := by
    rw [hcanonical]
    rfl
  have hCenterInvActual : ∀ i : Fin (M.cellCount + 1),
      1 / B.partition.center i ≤
        Calpha * Real.log (Scale.L B.sampleData.n) := by
    intro i
    rw [hpartitionCanonical]
    simpa only [Calpha] using
      hCenterInverseN B.n_gt_one hWne S i
  have hCenterLowerActual : ∀ i : Fin (M.cellCount + 1),
      centerScale / Real.log (Scale.L B.sampleData.n) ≤
        B.partition.center i := by
    intro i
    rw [hpartitionCanonical]
    simpa only [centerScale, Calpha] using
      hCenterLowerN B.n_gt_one hWne S i
  have hKernel : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
        CKernel := by
    intro p hp
    have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one hp
    have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one hp
    calc
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
          CKernel * tPrime B.sampleData.n p :=
        hKernelBound _ ⟨ht0, ht1⟩ _ ⟨ht0, ht1⟩
      _ ≤ CKernel := by
        exact (mul_le_mul_of_nonneg_left ht1 hCKernel).trans_eq
          (mul_one CKernel)
  have hUstrict : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hpoint : ∀ (xi : B.ParamSpace),
      (∀ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
      |xi MomentCoord.physical| ≤ Aphys →
      ∃ actualEquiv :
          SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
            SharpGaugeSpace B.partition.mass B.partition.center,
        (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
        ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖ := by
    intro xi heta hphys
    obtain ⟨hpair, hsingle⟩ := hprofile B xi hnProfile
      hPattern hLo hHi hGuards heta hphys rfl
    have hSquareRow : ∀ q : Fin (M.cellCount + 1) → ℝ,
        (∀ j, |q j| ≤ 1) → ∀ i : Fin (M.cellCount + 1),
        |SquarefreeSharpBandTransfer.squarefreeSharpRow
            (B.actualValuationLaw xi) B.partition q i -
          CompressedArithmeticOperator.arithmeticSharpOperator
            (y B.sampleData.n) cert.lower cert.upper
              B.partition.center q i| ≤ r := by
      intro q hq i
      exact (B.abs_actual_squarefreeSharpRow_sub_arithmetic_le_profileRemainder
        xi cert (hprofile0 B.sampleData.n) (by omega) hpair hsingle
        hKernel hBandTN hCenterInvActual q hq i).trans hSquareN.le
    have hcombined0 : 0 ≤ combined B.sampleData.n := by
      dsimp only [combined]
      exact canonicalCombinedPowerCorrection_nonneg
        Phead I hUstrict.le hAphys (by omega) B.n_gt_one
    have hrawFull := hfullRaw B xi hnFull rfl hsep hremaining
      hcanonical heta hphys
    have hFullRow : ∀ q : Fin (M.cellCount + 1) → ℝ,
        (∀ j, |q j| ≤ 1) → ∀ i : Fin (M.cellCount + 1),
        |PrimePowerSharpBandTransfer.fullSharpRow
            (B.actualValuationLaw xi) B.partition q i -
          SquarefreeSharpBandTransfer.squarefreeSharpRow
            (B.actualValuationLaw xi) B.partition q i| ≤ r := by
      intro q hq i
      have hraw := hrawFull q hq i
      have hbounded := B.fullSharpRow_le_canonicalFullSharpRemainder
        xi epsilon75 combined
          FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos.le
          (hepsilon750 B.sampleData.n) hcombined0 (by omega)
          hBandTN hCenterInvActual q i
          (by
            simpa only [Cpow, combined,
              canonicalCombinedPowerCorrection] using hraw)
      exact hbounded.trans hFullN.le
    obtain ⟨actualEquiv, hactual, hinvActual⟩ :=
      B.exists_actualFullProjectedEquiv_of_reference_of_unitSharpRows
        xi cert referenceEquiv hreference hCref.le hr.le hr.le
          hinvReference
          (canonicalProjectedPerturbationRadius_first_small hCref)
          hSquareRow
          (canonicalProjectedPerturbationRadius_second_small hCref)
          hFullRow
    refine ⟨actualEquiv, hactual, ?_⟩
    intro v
    have hbound := hinvActual v
    rw [canonicalProjectedPerturbation_finalConstant hCref] at hbound
    simpa only [Cfull] using hbound
  obtain ⟨fullEquiv, hfull, hinvFull⟩ :=
    B.exists_actualFullProjectedEquiv_on_closedBall_of_box a
      (by simpa only [Acoef, Aphys] using hpoint)
  have hmarkedRows : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro z hz c p
    exact hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  have hterminal := hSchurN B rfl rfl T hTmargin hbaseline hLo hHi
    fullEquiv hfull hinvFull hCenterLowerActual hmarkedRows
  dsimp only at hterminal
  obtain ⟨e, he, hinvSchur, hlocalConstant, _hquadratic⟩ := hterminal
  refine ⟨e, ?_, ?_⟩
  · simpa only using he
  · intro z hz v
    exact (hinvSchur z hz v).trans
      (mul_le_mul_of_nonneg_right
        (by simpa only [Cschur, Cfull] using hlocalConstant)
        (norm_nonneg _))

set_option maxHeartbeats 1000000 in
/-- Final fine-mesh form.  The anchor block is no longer data supplied by a
caller: it is constructed uniformly from the regular mesh itself.  Thus the
only mesh premise is the paper's single quantitative fineness condition. -/
theorem exists_fineMesh_cutoff_eventually_actualBandSchur_primeGraph_inverse :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cschur : ℝ, 0 < Cschur ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + M.ratio ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            ∀ (T : BarycentricTarget B.sampleData)
              (_hTmargin : marginFloor ≤ T.cellMassMargin)
              (hbaseline : B.baseline = T.baseline),
              ∃ e : ∀ (z : B.EffectiveParamSpace),
                  z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                    B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                (∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                  e z hz q =
                    B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by intro sigma; rw [hcanonical]; rfl)
                        (by intro sigma; rw [hcanonical]; rfl)
                        T hbaseline hBWlarge z hz) q) ∧
                ∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                  paperSharpNorm B.harmonicMass B.bandCenter
                      (B.partition.center_ne_zero B.n_gt_one)
                      ((e z hz).symm v) ≤
                    Cschur *
                      paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one) v := by
  obtain ⟨meshTol, hmeshTol, Cschur, hCschur, W₀, hmain⟩ :=
    @exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse
  let fineTol : ℝ := min meshTol (1 / 16)
  have hfineTol : 0 < fineTol := by
    dsimp only [fineTol]
    exact lt_min hmeshTol (by norm_num)
  refine ⟨fineTol, hfineTol, Cschur, hCschur, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
  have hmesh : delta + M.ratio ≤ meshTol :=
    hfine.trans (min_le_left _ _)
  have hsumSmall : delta + M.ratio ≤ (1 / 16 : ℝ) :=
    hfine.trans (min_le_right _ _)
  have hdeltaSmall : delta < (1 / 16 : ℝ) := by
    linarith [M.ratio_pos]
  have hratioSmall : M.ratio < (1 / 16 : ℝ) := by
    linarith
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 / 16 : ℝ) := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  obtain ⟨anchors, anchor, hanchor, hLower, hUpper, hMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hanchor⟩
  exact hmain W hW M hdelta hmesh anchors hAnchors
    hLower hUpper hMass

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
