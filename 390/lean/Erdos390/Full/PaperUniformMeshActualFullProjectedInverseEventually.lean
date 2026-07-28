import Erdos390.Full.PaperSelectedMeshActualFullProjectedInverseEventually
import Erdos390.Full.RegularRelativeMeshInteriorAnchors

/-!
# Uniform actual-full inverse for every permitted anchored mesh

The selected-dyadic wrapper is sufficient for one implementation of the
upper construction, but the statement of the moving-low arithmetic quotient
lemma is uniform over every fixed permitted mesh.  This file keeps the mesh
universally quantified.  A fixed interior anchor block of positive total
width supplies a reference inverse constant independent of all individual
cell widths; only the final ambient threshold is allowed to depend on the
particular mesh.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError
open RegularRelativeMesh

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

set_option maxHeartbeats 2400000 in
/-- Uniform actual-full projected inverse on an arbitrary fixed mesh carrying
an interior anchor block of fixed total width.  The constants `kappa`,
`meshTol`, and `Cfull` are chosen before the mesh, the prime cutoff, and the
coefficient box. -/
theorem exists_uniformMultiAnchor_eventually_actualFullProjected_inverse
    [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals) (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cfull : ℝ, 0 < Cfull ∧
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta)
        (anchors : Finset (Fin M.cellCount)) (anchor : Fin M.cellCount),
      anchors.Nonempty →
      anchor ∈ anchors →
      (∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k) →
      (∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ)) →
      ((1 / 8 : ℝ) ≤ (∑ k ∈ anchors, M.width k) / 2) →
      (delta < meshTol ∧ ∀ k : Fin M.cellCount, M.width k < meshTol) →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        (∀ h, (Phead h).modulus ≤ W) →
        ∀ Acoef Aphys : ℝ, 0 ≤ Acoef → 0 ≤ Aphys →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1)))
            (xi : B.ParamSpace),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (PaperGuardCensus.rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              B.sampleData = PaperGuardCensus.canonicalSampleData
                  (W := B.sampleData.W) Phead I
                    (ledger B.sampleData.n) hsep hremaining →
              (∃ (hWne : B.sampleData.W ≠ 0)
                  (S : RegularMeshPrimeCutoffs.ScaleSeparation
                    M B.sampleData.n B.sampleData.W),
                B.partition =
                  RegularMeshPrimeCutoffs.Mesh.canonicalPartition M
                    hdelta B.n_gt_one hWne S) →
              (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
              |xi MomentCoord.physical| ≤ Aphys →
              ∃ actualEquiv :
                SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
                  SharpGaugeSpace B.partition.mass B.partition.center,
                (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
                ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖ := by
  obtain ⟨kappa, hkappa, meshTol, hmeshTol, hcanonicalInverse⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_meshTolerance_cutoff_eventually_multiAnchor_projected_inverse
      (epsilon := (1 / 8 : ℝ)) (anchorFloor := (1 / 8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hCpow, hfullRowTerminal⟩ :=
    boxIndependent_canonicalRaw_fullSharp
      Phead I Cmax hlowerOne hupperMax Cprom Cbank ledger
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  let Cref : ℝ := multiAnchorReferenceInverseConstant kappa (1 / 8)
  let r : ℝ := canonicalProjectedPerturbationRadius Cref
  let Cfull : ℝ := 2 * Cref
  have hCref : 0 < Cref := by
    dsimp only [Cref]
    exact multiAnchorReferenceInverseConstant_pos hkappa (by norm_num)
  have hr : 0 < r := by
    dsimp only [r]
    exact canonicalProjectedPerturbationRadius_pos hCref
  have hCfull : 0 < Cfull := by
    dsimp only [Cfull]
    positivity
  refine ⟨kappa, hkappa, meshTol, hmeshTol, Cfull, hCfull, ?_⟩
  intro delta eta M hdelta anchors anchor hAnchors hAnchor
    hIdealLower hIdealUpper hIdealAnchorMass hmesh
  obtain ⟨_CRow, _hCRow, Winverse, hinverseEvent⟩ :=
    hcanonicalInverse M hdelta anchors hAnchors anchor hAnchor
      hIdealLower hIdealUpper hIdealAnchorMass hmesh
  obtain ⟨Calpha, hCalpha, Wcenter, hcenterEvent⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_cutoff_eventually_canonical_center_inverse_logL
      M hdelta
  let Kbound : ℝ := 2 * Real.log 4
  have hKbound : 0 ≤ Kbound := by
    dsimp only [Kbound]
    positivity
  have hInvNat : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ))
      atTop (nhds 0) := by
    have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have h := hinv.comp tendsto_natCast_atTop_atTop
    simpa only [one_div] using h
  let squareTailConstant : ℝ :=
    (1 / DickmanBasic.rho DickmanBasic.U) ^ 2 + CKernel
  have hSquareTail : Tendsto (fun W : ℕ ↦
      squareTailConstant * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ squareTailConstant * (1 / (W : ℝ)))
          atTop (nhds (squareTailConstant * 0)))
  let fullTailConstant : ℝ := 3 * Cpow * (Kbound + 1)
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
  let W₀ := max 2 (max Winverse (max Wcenter (max Wsquare Wfull)))
  refine ⟨W₀, ?_⟩
  intro W hWcutoff hmod
  have hWtwo : 2 ≤ W := (le_max_left 2 _).trans hWcutoff
  have hWone : 1 < W := by omega
  have hWne : W ≠ 0 := by omega
  have hWinverse : Winverse ≤ W := by
    exact ((le_max_left Winverse _).trans (le_max_right 2 _)).trans hWcutoff
  have hWcenter : Wcenter ≤ W := by
    exact ((le_max_left Wcenter (max Wsquare Wfull)).trans
      (le_max_right Winverse _)).trans ((le_max_right 2 _).trans hWcutoff)
  have hWsquare' : Wsquare ≤ W := by
    exact ((le_max_left Wsquare Wfull).trans
      (le_max_right Wcenter _)).trans
        ((le_max_right Winverse _).trans ((le_max_right 2 _).trans hWcutoff))
  have hWfull' : Wfull ≤ W := by
    exact ((le_max_right Wsquare Wfull).trans
      (le_max_right Wcenter _)).trans
        ((le_max_right Winverse _).trans ((le_max_right 2 _).trans hWcutoff))
  have hSquareTailLt :
      squareTailConstant * (1 / (W : ℝ)) < r := hWsquare W hWsquare'
  have hFullTailLt :
      fullTailConstant * (1 / (W : ℝ)) < r := hWfull W hWfull'
  intro Acoef Aphys hAcoef hAphys
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I Cmax hlowerOne hupperMax Cprom Cbank ledger
        W hWone
          (fun h p hp ↦
            PaperPrimePowerAuxiliaryPrime.headPrime_le_cutoff_of_modulus_le
              (Phead h) (hmod h) p hp)
          Acoef Aphys hAcoef hAphys
  obtain ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
      hcombinedRateRaw, Nfull, hfullRaw⟩ :=
    hfullRowTerminal W hWone
      (fun h p hp ↦
        PaperPrimePowerAuxiliaryPrime.headPrime_le_cutoff_of_modulus_le
          (Phead h) (hmod h) p hp)
      Acoef hAcoef Aphys hAphys
  let combined : ℕ → ℝ := fun n ↦
    canonicalCombinedPowerCorrection
      Phead I Cmax Cprom Cbank W Acoef Aphys n
  have hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    simpa only [combined, canonicalCombinedPowerCorrection] using
      hcombinedRateRaw
  have hSquareRemainderT := tendsto_squarefreeSharpProfileRemainder
    profileError Calpha Kbound CKernel W hprofileT hprofileRate
  have hSquareSmall : ∀ᶠ n : ℕ in atTop,
      squarefreeSharpProfileRemainder
        profileError Calpha Kbound CKernel W n < r :=
    hSquareRemainderT.eventually (eventually_lt_nhds (by
      simpa only [squareTailConstant] using hSquareTailLt))
  have hFullRemainderT := tendsto_canonicalFullSharpRemainder
    epsilon75 combined Cpow Calpha Kbound W
      hepsilonT hepsilonRate hcombinedRate
  have hFullSmall : ∀ᶠ n : ℕ in atTop,
      canonicalFullSharpRemainder
        epsilon75 combined Cpow Calpha Kbound W n < r :=
    hFullRemainderT.eventually (eventually_lt_nhds (by
      simpa only [fullTailConstant] using hFullTailLt))
  have hInverse := hinverseEvent W hWinverse
  have hCenter := hcenterEvent W hWcenter
  have hCoverage :=
    RegularMeshPrimeCutoffs.Mesh.eventually_canonical_anchorBlock_coverage
      M hdelta hWne hWtwo anchors hAnchors hIdealLower hIdealUpper
        hIdealAnchorMass
  have hBandT := eventually_bandTReciprocalSum_le W
  filter_upwards [hInverse, hCenter, hCoverage, hBandT,
    hSquareSmall, hFullSmall, eventually_ge_atTop Nprofile,
    eventually_ge_atTop Nfull] with n hInverseN hCenterN hCoverageN
      hBandTN hSquareN hFullN hnProfile hnFull
  intro B xi hBn hBW hsep hremaining hcanonical hpartition heta hphys
  subst n
  subst W
  obtain ⟨hWactual, hWTwoActual, hnInverse, SInverse,
      hInteriorLower, hInteriorUpper, referenceEquiv,
      hreference, hinvVarying⟩ := hInverseN
  obtain ⟨hnCoverage, hCoverageAll⟩ := hCoverageN
  obtain ⟨hWpartition, SPartition, hPartitionUser⟩ := hpartition
  let Pcanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hnInverse hWactual SInverse
  let Ecanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hnInverse hWactual SInverse
  let IM := RegularMeshPrimeCutoffs.Mesh.canonicalIntervalMeshOfAnchors
    M hdelta hnInverse hWactual hWTwoActual SInverse
      (1 / 8) anchors hAnchors hInteriorLower hInteriorUpper
  have hPartitionCanonical : B.partition = Pcanonical := by
    exact hPartitionUser.trans (by rfl)
  obtain ⟨_hCoverageLower, _hCoverageUpper, hAnchorMassRaw⟩ :=
    hCoverageAll SInverse
  have hAnchorMass : (1 / 8 : ℝ) ≤ ∑ j, IM.anchor j := by
    simpa only [IM, Subsingleton.elim hnCoverage hnInverse,
      Subsingleton.elim hWTwoActual hWtwo] using hAnchorMassRaw
  let Cvary : ℝ :=
    (4 / (kappa * ∑ j, IM.anchor j)) /
      (1 - (4 / (kappa * ∑ j, IM.anchor j)) *
        (2 * (kappa * ((1 : ℝ) / 8) / 16)))
  have hCvary : Cvary ≤ Cref := by
    dsimp only [Cvary, Cref]
    exact multiAnchor_varyingInverseConstant_le hkappa (by norm_num)
      hAnchorMass
  have hinvReference : ∀ v, ‖referenceEquiv.symm v‖ ≤ Cref * ‖v‖ := by
    intro v
    exact (hinvVarying v).trans
      (mul_le_mul_of_nonneg_right hCvary (norm_nonneg v))
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
  have hGuards : B.sampleData.guards = (ledger B.sampleData.n).guards := by
    rw [hcanonical]
    rfl
  obtain ⟨hpair, hsingle⟩ := hprofile B xi hnProfile
    hPattern hLo hHi hGuards heta hphys rfl
  have hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
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
  have hCenterCanonical : ∀ i : Fin (M.cellCount + 1),
      1 / Pcanonical.center i ≤
        Calpha * Real.log (Scale.L B.sampleData.n) := by
    intro i
    exact hCenterN hnInverse hWactual SInverse i
  have hSquareRow : ∀ q : Fin (M.cellCount + 1) → ℝ,
      (∀ j, |q j| ≤ 1) → ∀ i : Fin (M.cellCount + 1),
      |SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        CompressedArithmeticOperator.arithmeticSharpOperator
          (y B.sampleData.n) Ecanonical.lower Ecanonical.upper
            Pcanonical.center q i| ≤ r := by
    intro q hq i
    exact (B.abs_actual_squarefreeSharpRow_sub_equalPartitionArithmetic_le
      xi hPartitionCanonical Ecanonical
      (hprofile0 B.sampleData.n) (by omega) hpair hsingle hKernel
      hBandTN hCenterCanonical q hq i).trans hSquareN.le
  have hCenterActual : ∀ i : Fin (M.cellCount + 1),
      1 / B.partition.center i ≤
        Calpha * Real.log (Scale.L B.sampleData.n) := by
    intro i
    rw [hPartitionCanonical]
    exact hCenterCanonical i
  have hCmax : 1 ≤ Cmax :=
    (hlowerOne .minus).trans
      ((I.lower_lt_upper .minus).le.trans (hupperMax .minus))
  have hcombined0 : 0 ≤ combined B.sampleData.n := by
    dsimp only [combined]
    exact canonicalCombinedPowerCorrection_nonneg
      Phead I hCmax hAphys (by omega) B.n_gt_one
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
      xi epsilon75 combined hCpow.le (hepsilon0 B.sampleData.n)
        hcombined0 (by omega) hBandTN hCenterActual q i
        (by simpa only [combined, canonicalCombinedPowerCorrection] using hraw)
    exact hbounded.trans hFullN.le
  obtain ⟨actualEquiv, hactual, hinvActual⟩ :=
    B.exists_actualFullProjectedEquiv_of_equal_referencePartition
      xi hPartitionCanonical Ecanonical referenceEquiv hreference
      hCref.le hr.le hr.le hinvReference
      (canonicalProjectedPerturbationRadius_first_small hCref)
      hSquareRow
      (canonicalProjectedPerturbationRadius_second_small hCref)
      hFullRow
  refine ⟨actualEquiv, hactual, ?_⟩
  intro v
  have hbound := hinvActual v
  rw [canonicalProjectedPerturbation_finalConstant hCref] at hbound
  simpa only [Cfull] using hbound

set_option maxHeartbeats 1200000 in
/-- Exact every-permitted-mesh version: the interior anchor block is now a
conclusion of mesh fineness rather than an input.  Only the final ambient
threshold may depend on the particular fixed mesh. -/
theorem exists_uniformPermittedMesh_eventually_actualFullProjected_inverse
    [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals) (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cfull : ℝ, 0 < Cfull ∧
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
      (delta < meshTol ∧ ∀ k : Fin M.cellCount, M.width k < meshTol) →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        (∀ h, (Phead h).modulus ≤ W) →
        ∀ Acoef Aphys : ℝ, 0 ≤ Acoef → 0 ≤ Aphys →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1)))
            (xi : B.ParamSpace),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (PaperGuardCensus.rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              B.sampleData = PaperGuardCensus.canonicalSampleData
                  (W := B.sampleData.W) Phead I
                    (ledger B.sampleData.n) hsep hremaining →
              (∃ (hWne : B.sampleData.W ≠ 0)
                  (S : RegularMeshPrimeCutoffs.ScaleSeparation
                    M B.sampleData.n B.sampleData.W),
                B.partition =
                  RegularMeshPrimeCutoffs.Mesh.canonicalPartition M
                    hdelta B.n_gt_one hWne S) →
              (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
              |xi MomentCoord.physical| ≤ Aphys →
              ∃ actualEquiv :
                SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
                  SharpGaugeSpace B.partition.mass B.partition.center,
                (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
                ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖ := by
  obtain ⟨kappa, hkappa, meshTol, hmeshTol, Cfull, hCfull, hmain⟩ :=
    exists_uniformMultiAnchor_eventually_actualFullProjected_inverse
      Phead I Cmax hlowerOne hupperMax Cprom Cbank ledger
  let meshTol' : ℝ := min meshTol (1 / 16)
  have hmeshTol' : 0 < meshTol' := by
    dsimp only [meshTol']
    exact lt_min hmeshTol (by norm_num)
  refine ⟨kappa, hkappa, meshTol', hmeshTol', Cfull, hCfull, ?_⟩
  intro delta eta M hdelta hfine
  have hdeltaSmall : delta < 1 / 16 :=
    hfine.1.trans_le (min_le_right _ _)
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 / 16 : ℝ) := by
    intro k
    exact (hfine.2 k).trans_le (min_le_right _ _)
  obtain ⟨anchors, anchor, hanchor, hLower, hUpper, hMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hanchor⟩
  apply hmain M hdelta anchors anchor hAnchors hanchor hLower hUpper hMass
  exact ⟨hfine.1.trans_le (min_le_left _ _), fun k ↦
    (hfine.2 k).trans_le (min_le_left _ _)⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
