import Erdos390.Full.PaperActualFullProjectedInverseEventually
import Erdos390.Full.PaperSelectedMeshProjectedInverseEventually

/-!
# Actual full projected inverse on an explicitly selected regular mesh

This closes the mesh-selection wrapper missing from the fixed-mesh terminal.
The continuum tolerance is selected before the explicit dyadic mesh.  A
fixed positive-mass anchor block then supplies inverse constants independent
of the individual cell widths, and the already proved squarefree and
prime-power transfers give the literal actual full operator.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError
open SelectedDyadicRegularMesh

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- Reference inverse constant from a lower bound for the *total* anchor
mass. -/
def multiAnchorReferenceInverseConstant (kappa anchorFloor : ℝ) : ℝ :=
  8 / (kappa * anchorFloor)

theorem multiAnchorReferenceInverseConstant_pos
    {kappa anchorFloor : ℝ} (hkappa : 0 < kappa)
    (hAnchorFloor : 0 < anchorFloor) :
    0 < multiAnchorReferenceInverseConstant kappa anchorFloor := by
  exact div_pos (by norm_num) (mul_pos hkappa hAnchorFloor)

theorem multiAnchor_varyingInverseConstant_le
    {kappa anchorFloor anchorMass : ℝ}
    (hkappa : 0 < kappa) (hAnchorFloor : 0 < anchorFloor)
    (hAnchor : anchorFloor ≤ anchorMass) :
    (4 / (kappa * anchorMass)) /
        (1 - (4 / (kappa * anchorMass)) *
          (2 * (kappa * anchorFloor / 16))) ≤
      multiAnchorReferenceInverseConstant kappa anchorFloor := by
  have hAnchorPos : 0 < anchorMass := hAnchorFloor.trans_le hAnchor
  have hkAnchor : 0 < kappa * anchorMass := mul_pos hkappa hAnchorPos
  have hkFloor : 0 < kappa * anchorFloor :=
    mul_pos hkappa hAnchorFloor
  let base : ℝ := 4 / (kappa * anchorMass)
  let loss : ℝ := base * (2 * (kappa * anchorFloor / 16))
  have hbasePos : 0 < base := div_pos (by norm_num) hkAnchor
  have hlossId : loss = anchorFloor / (2 * anchorMass) := by
    dsimp only [loss, base]
    field_simp [ne_of_gt hkappa, ne_of_gt hAnchorPos]
    ring
  have hlossLe : loss ≤ 1 / 2 := by
    rw [hlossId]
    apply (div_le_iff₀ (mul_pos (by norm_num) hAnchorPos)).2
    nlinarith
  have hdenHalf : 1 / 2 ≤ 1 - loss := by linarith
  have hbaseBound : base ≤ 4 / (kappa * anchorFloor) := by
    dsimp only [base]
    apply (div_le_div_iff₀ hkAnchor hkFloor).2
    nlinarith [mul_le_mul_of_nonneg_left hAnchor hkappa.le]
  change base / (1 - loss) ≤
    multiAnchorReferenceInverseConstant kappa anchorFloor
  calc
    base / (1 - loss) ≤ base / (1 / 2) :=
      div_le_div_of_nonneg_left hbasePos.le (by norm_num) hdenHalf
    _ = 2 * base := by ring
    _ ≤ 2 * (4 / (kappa * anchorFloor)) :=
      mul_le_mul_of_nonneg_left hbaseBound (by norm_num)
    _ = multiAnchorReferenceInverseConstant kappa anchorFloor := by
      unfold multiAnchorReferenceInverseConstant
      ring

set_option maxHeartbeats 1800000 in
/-- End-to-end actual-full projected inverse after a literal, nonvacuous
dyadic mesh has been selected.

The quantifiers record the dependency order used in the paper: the
continuum gap, mesh tolerance, and structural full-inverse constant are
chosen first; the finite mesh and its positive-mass anchor block are then
fixed explicitly; the prime cutoff is chosen only afterwards; coefficient
boxes precede the eventual ambient threshold. -/
theorem exists_selectedDyadicMesh_eventually_actualFullProjected_inverse
    [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals) (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cfull : ℝ, 0 < Cfull ∧
      ∃ K N : ℕ, ∃ hK : 3 ≤ K, ∃ hN : 0 < N,
        let M := mesh K N (lt_of_lt_of_le (by decide : 0 < 3) hK) hN
        let anchors := SelectedDyadicRegularMesh.anchors hK hN
        ∃ anchor : Fin M.cellCount, anchor ∈ anchors ∧
          delta K < meshTol ∧
          (∀ k : Fin M.cellCount, M.width k < meshTol) ∧
          ∃ W₀ : ℕ,
            ∀ W : ℕ, W₀ ≤ W →
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
                          (by
                            unfold SelectedDyadicRegularMesh.delta
                            positivity)
                          B.n_gt_one hWne S) →
                    (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                      |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
                    |xi MomentCoord.physical| ≤ Aphys →
                    ∃ actualEquiv :
                      SharpGaugeSpace B.partition.mass B.partition.center
                          ≃L[ℝ]
                        SharpGaugeSpace B.partition.mass B.partition.center,
                      (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
                      ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖ := by
  obtain ⟨kappa, hkappa, meshTol, hmeshTol, hcanonicalInverse⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_meshTolerance_cutoff_eventually_multiAnchor_projected_inverse
        (epsilon := (1 / 8 : ℝ)) (anchorFloor := (1 / 8 : ℝ))
        (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨K, N, hK, hN, hdeltaFine, _hratioFine, hwidthFine⟩ :=
    exists_fine_mesh meshTol hmeshTol
  let M := mesh K N (lt_of_lt_of_le (by decide : 0 < 3) hK) hN
  let anchors := SelectedDyadicRegularMesh.anchors hK hN
  have hAnchors : anchors.Nonempty :=
    SelectedDyadicRegularMesh.anchors_nonempty hK hN
  let anchor : Fin M.cellCount := hAnchors.choose
  have hAnchor : anchor ∈ anchors := hAnchors.choose_spec
  have hdelta : 0 < delta K := by
    unfold SelectedDyadicRegularMesh.delta
    positivity
  have hIdealLower : ∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k := by
    intro k hk
    exact (SelectedDyadicRegularMesh.anchors_ideal_interior hK hN hk).1
  have hIdealUpper : ∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ) := by
    intro k hk
    exact (SelectedDyadicRegularMesh.anchors_ideal_interior hK hN hk).2
  have hIdealMass : (1 / 8 : ℝ) ≤
      (∑ k ∈ anchors, M.width k) / 2 := by
    rw [show (∑ k ∈ anchors, M.width k) = (1 / 4 : ℝ) by
      simpa only [M, anchors] using
        SelectedDyadicRegularMesh.sum_anchor_widths hK hN]
    norm_num
  obtain ⟨_CRow, _hCRow, Winverse, hinverseEvent⟩ :=
    hcanonicalInverse M hdelta anchors hAnchors anchor hAnchor
      hIdealLower hIdealUpper hIdealMass ⟨hdeltaFine, hwidthFine⟩
  obtain ⟨Calpha, hCalpha, Wcenter, hcenterEvent⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_cutoff_eventually_canonical_center_inverse_logL
      M hdelta
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
  refine ⟨kappa, hkappa, meshTol, hmeshTol, Cfull, hCfull,
    K, N, hK, hN, anchor, hAnchor, hdeltaFine, hwidthFine, ?_⟩
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
      M hdelta hWne hWtwo anchors hAnchors hIdealLower hIdealUpper hIdealMass
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

end BridgeData
end
end Erdos390.Full.PaperBridgeFit
