import Erdos390.Full.PaperCanonicalActualFullQuotientNullIdentification
import Erdos390.Full.PaperLemma84StructuralCutoff
import Erdos390.Full.PaperActualSquarefreeReference
import Erdos390.Full.PaperCanonicalActualPrimePowerWeightedRowEventually
import Erdos390.Full.PaperCanonicalMarkedNuisanceRows
import Erdos390.Full.PaperCanonicalNuisanceUniformFloor
import Erdos390.Full.PaperCanonicalNuisanceEffectiveBall

/-!
# The canonical actual-full arithmetic quotient gap

This file discharges every analytic input of the finite full-valuation
quotient theorem.  The structural cutoff is selected before the mesh, the
head patterns, and the effective tilt ball.  Once those later data are fixed,
only the ambient threshold is allowed to depend on them.

The conclusion is the actual nuisance-Schur covariance of the literal
full-valuation score.  No projected inverse, profile estimate, prime-power
row, nuisance gap, or convergence statement is accepted as a hypothesis.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus PrimeSums
open RegularMeshPrimeCutoffs
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open PaperCanonicalSlowKappa
open PaperLemma84StructuralCutoff
open SquarefreeSharpBandTransfer PrimePowerSharpBandTransfer
open PaperPrimePowerChamberError

namespace BridgeData

/-- A product-log rate and pointwise nonnegativity imply ordinary
convergence to zero. -/
private theorem tendsto_zero_of_nonneg_mul_logL_zero
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 ≤ epsilon n)
    (hrate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    Tendsto epsilon atTop (nhds 0) := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (Scale.L n) :=
    (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hupper : ∀ᶠ n : ℕ in atTop,
      epsilon n ≤ epsilon n * Real.log (Scale.L n) := by
    filter_upwards [hlogOne] with n hn
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (hepsilon n)
  exact squeeze_zero' (Filter.Eventually.of_forall hepsilon) hupper hrate

set_option maxHeartbeats 4000000 in
/-- Exact paper-order eventual form of the full arithmetic quotient gap.

The exact head condition is deliberately placed after `W`; it both supplies
the finite logarithmic null relation and implies the support condition used
by all marked asymptotics. -/
theorem exists_structural_cutoff_eventually_canonical_actualFullQuotient :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
      ∀ (anchors : Finset (Fin M.cellCount))
        (_hAnchors : anchors.Nonempty)
        (_hIdealLower : ∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k)
        (_hIdealUpper : ∀ k ∈ anchors,
          M.upper k ≤ 1 - (1 / 8 : ℝ))
        (_hIdealMass : (1 : ℝ) / 8 ≤
          (∑ k ∈ anchors, M.width k) / 2),
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ (Phead : Head → HeadPattern.Pattern)
        (_hhead : ∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W),
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
        (hupperU : ∀ sigma, I.upper sigma ≤ U),
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (a : NNReal) (marginFloor : ℝ) (_hmarginFloor : 0 < marginFloor),
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1)))
          (_hBn : B.sampleData.n = n) (_hBW : B.sampleData.W = W)
          (hBWlarge : 1 < B.sampleData.W),
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
          ∀ (T : BarycentricTarget B.sampleData)
            (_hTmargin : marginFloor ≤ T.cellMassMargin)
            (hbaseline : B.baseline = T.baseline),
          ∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
          let xi : B.ParamSpace := B.effectiveParamEquiv z
          let gamma : ℝ :=
            B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
          let hgamma : 0 < gamma :=
            B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
          let hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
              inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
            intro v
            simpa only [gamma, xi] using
              B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                hlowerOne hupperU
                (by intro sigma; rw [hcanonical]; rfl)
                (by intro sigma; rw [hcanonical]; rfl)
                T hbaseline hBWlarge z hz v
          ∀ (b : Fin (M.cellCount + 1) → ℝ) (mu : ℝ),
            kappa * B.partition.data.bandNormSq
                (B.partition.data.gaugePart b) ≤
              (B.tiltedLaw xi).covariance
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu)))
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu))) := by
  obtain ⟨CKernel, hCKernel, hKernelStructural,
      Wstruct, hstruct⟩ := PaperLemma84StructuralCutoff.exists_structural_cutoff
  refine ⟨quotientKappa, quotientKappa_pos, Wstruct, ?_⟩
  intro W hWstruct delta eta M hdelta anchors hAnchors
    hIdealLower hIdealUpper hIdealMass Head _instFintype
    _instDecidable _instNonempty Phead hhead I U hU hlowerOne hupperU
    Cprom Cbank ledger a marginFloor hmarginFloor
  obtain ⟨hW2, hWanchor, hrowEvent, hstructSmall⟩ := hstruct W hWstruct
  have hWone : 1 < W := by omega
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
  obtain ⟨_hCpow, hpowerTerminal⟩ :=
    boxIndependent_canonicalRaw_actualWeightedRow
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, _hepsilon75Rate,
      hcombinedRateRaw, Npower, hpower⟩ :=
    hpowerTerminal W hWone hHeadLe Acoef hAcoef Aphys hAphys
  obtain ⟨markedError, hmarked0, hmarkedRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger W hWone
        hHeadLe a
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  let combined : ℕ → ℝ := fun n ↦
    canonicalCombinedPowerCorrection
      Phead I U Cprom Cbank W Acoef Aphys n
  have hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    simpa only [combined, canonicalCombinedPowerCorrection] using
      hcombinedRateRaw
  have hUstrict : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hcombinedNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ combined n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact canonicalCombinedPowerCorrection_nonneg
      Phead I hUstrict.le hAphys hWone hn
  have hcombinedT : Tendsto combined atTop (nhds 0) := by
    have hLTop : Tendsto Scale.L atTop atTop := by
      simpa only [Scale.L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlogOne : ∀ᶠ n : ℕ in atTop,
        1 ≤ Real.log (Scale.L n) :=
      (Real.tendsto_log_atTop.comp hLTop).eventually
        (eventually_ge_atTop (1 : ℝ))
    have hupper : ∀ᶠ n : ℕ in atTop,
        combined n ≤ combined n * Real.log (Scale.L n) := by
      filter_upwards [hcombinedNonneg, hlogOne] with n hn hlog
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hn
    exact squeeze_zero' hcombinedNonneg hupper hcombinedRate
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero markedError hmarked0 hmarkedRate
  let H : ℕ → ℝ := fun n ↦ 12 * Real.log (Scale.L n)
  let K : ℝ := 2 * Real.log 4
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hprofileH : Tendsto (fun n : ℕ ↦ profileError n * H n)
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ (12 : ℝ))
        atTop (nhds 12) := tendsto_const_nhds
    have h := hconst.mul hprofileRate
    simpa only [H, mul_zero, zero_mul, mul_assoc, mul_left_comm, mul_comm]
      using h
  have hpairH : Tendsto
      (fun n : ℕ ↦ pairCovarianceScale (profileError n) * H n)
        atTop (nhds 0) := by
    have hlinear : Tendsto (fun n : ℕ ↦
        (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) *
          (profileError n * H n)) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hprofileH
    have hsquare : Tendsto (fun n : ℕ ↦
        profileError n * (profileError n * H n)) atTop (nhds 0) := by
      simpa only [mul_zero] using hprofileT.mul hprofileH
    have hsum := hlinear.add hsquare
    have hsum0 : Tendsto (fun n : ℕ ↦
        (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) *
            (profileError n * H n) +
          profileError n * (profileError n * H n))
        atTop (nhds 0) := by simpa only [zero_add] using hsum
    apply hsum0.congr'
    filter_upwards with n
    unfold pairCovarianceScale
    ring
  have hsignedT : Tendsto
      (fun n : ℕ ↦ signedSecondConstant (profileError n) CKernel)
        atTop (nhds (signedSecondConstant 0 CKernel)) := by
    have hcont : Continuous
        (fun x : ℝ ↦ signedSecondConstant x CKernel) := by
      unfold signedSecondConstant
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprofileT
  have hmarkedH : Tendsto (fun n : ℕ ↦ markedError n ^ 2 * H n)
      atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ ↦
        markedError n * (markedError n * Real.log (Scale.L n)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using hmarkedT.mul hmarkedRate
    have hconst : Tendsto (fun _n : ℕ ↦ (12 : ℝ))
        atTop (nhds 12) := tendsto_const_nhds
    have h := hconst.mul hbase
    simpa only [H, mul_zero, zero_mul, pow_two, mul_assoc, mul_left_comm,
      mul_comm]
      using h
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmarginFloor
  let dcard : ℝ := (Fintype.card Head + 1 : ℕ)
  have hdcard : 0 ≤ dcard := by dsimp only [dcard]; positivity
  let R : ℕ → ℝ := fun n ↦
    Cpow * (1 / (W : ℝ)) + epsilon75 n + combined n
  have hRT : Tendsto R atTop
      (nhds (Cpow * (1 / (W : ℝ)))) := by
    simpa only [R, add_zero] using
      (tendsto_const_nhds.add hepsilon75T).add hcombinedT
  let nuisanceMajorant : ℕ → ℝ := fun n ↦
    dcard * markedError n ^ 2 * H n / gammaFloor
  have hnuisanceT : Tendsto nuisanceMajorant atTop (nhds 0) := by
    have hnum : Tendsto (fun n : ℕ ↦
        dcard * (markedError n ^ 2 * H n)) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hmarkedH
    have hdiv := hnum.div
      (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ gammaFloor)
        atTop (nhds gammaFloor)) hgammaFloor.ne'
    simpa only [nuisanceMajorant, zero_div, mul_assoc] using hdiv
  let loss : ℕ → ℝ := fun n ↦
    quotientRowTarget +
      ((4 * pairCovarianceScale (profileError n)) * H n +
        2 * profileError n +
        signedSecondConstant (profileError n) CKernel *
          (1 / (W : ℝ))) +
      R n + nuisanceMajorant n
  let limitLoss : ℝ :=
    quotientRowTarget +
      signedSecondConstant 0 CKernel * (1 / (W : ℝ)) +
      Cpow * (1 / (W : ℝ))
  have hlossT : Tendsto loss atTop (nhds limitLoss) := by
    have hoff : Tendsto (fun n : ℕ ↦
        (4 * pairCovarianceScale (profileError n)) * H n)
        atTop (nhds 0) := by
      have h := (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ (4 : ℝ))
        atTop (nhds 4)).mul hpairH
      simpa only [mul_zero, mul_assoc] using h
    have hdiag : Tendsto (fun n : ℕ ↦ 2 * profileError n)
        atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hprofileT
    have hsecond : Tendsto (fun n : ℕ ↦
        signedSecondConstant (profileError n) CKernel *
          (1 / (W : ℝ)))
        atTop (nhds (signedSecondConstant 0 CKernel *
          (1 / (W : ℝ)))) := hsignedT.mul tendsto_const_nhds
    have hrow : Tendsto (fun _n : ℕ ↦ quotientRowTarget)
        atTop (nhds quotientRowTarget) := tendsto_const_nhds
    simpa only [loss, limitLoss, add_zero, zero_add] using
      (((hrow.add ((hoff.add hdiag).add hsecond)).add hRT).add hnuisanceT)
  have hlimitSmall : limitLoss < quotientMain / 4 := by
    simpa only [limitLoss, Cpow] using hstructSmall
  have hlossSmall : ∀ᶠ n : ℕ in atTop, loss n < quotientMain / 2 :=
    hlossT.eventually (eventually_lt_nhds (by
      linarith [quotientMain_pos]))
  have hAnchorEvent :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff_eventually
      M hdelta W hWanchor anchors hAnchors hIdealLower hIdealUpper hIdealMass
  have hReciprocal := PrimeSums.eventually_bandReciprocalSum_le_logL W
  have hLogL : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (Scale.L n) := by
    have hLTop : Tendsto Scale.L atTop atTop := by
      simpa only [Scale.L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_ge_atTop 0)
  filter_upwards [hlossSmall, hAnchorEvent, hrowEvent, hReciprocal,
      hLogL, hcombinedNonneg, eventually_ge_atTop Nprofile,
      eventually_ge_atTop Npower, eventually_ge_atTop Nmarked] with
      n hlossN hAnchorN hRowN hReciprocalN hLogLN hcombinedN
      hnProfile hnPower hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline z hz
  subst n
  subst W
  obtain ⟨hWneAnchor, hnAnchor, hAnchorAll⟩ := hAnchorN
  obtain ⟨hWneUser, S, hpartitionUser⟩ := hpartition
  let Pcanonical := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hnAnchor hWneAnchor S
  let anchor := RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorSet
    M Pcanonical anchors
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by dsimp only [Pcanonical])
  obtain ⟨hinterior, hAnchorMass⟩ := hAnchorAll S
  have hinterior' : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8) := by
    simpa only [anchor, Pcanonical] using hinterior
  have hAnchorMass' : (1 / 8 : ℝ) ≤
      anchorMass (primeWeight B.sampleData.n) anchor := by
    simpa only [anchor, Pcanonical] using hAnchorMass
  have hmass : 0 < anchorMass (primeWeight B.sampleData.n)
      anchor := (by norm_num : (0 : ℝ) < 1 / 8).trans_le hAnchorMass'
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
  let xi : B.ParamSpace := B.effectiveParamEquiv z
  have hznorm : ‖z‖ ≤ (a : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hsize : B.paperEffectiveSize xi ≤ Acoef := by
    dsimp only [xi, Acoef]
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hznorm (by norm_num))
  have heffective := B.effective_bounds_of_paperEffectiveSize xi hsize
  have heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ Acoef := heffective.1
  have hnuisance : ‖B.nuisanceParameter xi‖ ≤ Acoef := heffective.2
  have hphys : |xi MomentCoord.physical| ≤ Aphys := by
    calc
      |xi MomentCoord.physical| =
          ‖B.nuisanceParameter xi NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter xi‖ :=
        PiLp.norm_apply_le (B.nuisanceParameter xi) NuisanceCoord.physical
      _ ≤ Aphys := by simpa only [Aphys, Acoef] using hnuisance
  obtain ⟨hpair, hsingle⟩ :=
    hprofile B xi hnProfile hPattern hLo hHi hGuards heta hphys rfl
  have hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R B.sampleData.n := by
    intro p
    have hraw := hpower B xi hnPower rfl hsep hremaining hcanonical
      heta hphys p
    simpa only [R, combined, canonicalCombinedPowerCorrection] using hraw
  have hmarkedRows : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro c p
    exact hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  have hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        quotientRowTarget * tPrime B.sampleData.n p.1 := hRowN
  have hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel := by
    intro p hp
    have ht : tPrime B.sampleData.n p ∈ Icc (0 : ℝ) 1 := by
      exact ⟨PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand B.n_gt_one hp,
        PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one hp⟩
    calc
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
          CKernel * tPrime B.sampleData.n p :=
        hKernelStructural _ ht _ ht
      _ ≤ CKernel * 1 :=
        mul_le_mul_of_nonneg_left ht.2 hCKernel
      _ = CKernel := by ring
  have hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
      reciprocalWeight p) ≤ H B.sampleData.n := by
    have hattach :
        (∑ p : BandPrime B.sampleData.n B.sampleData.W,
            1 / (p.1 : ℝ)) =
          ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
            1 / (p : ℝ) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach (primeBand B.sampleData.n B.sampleData.W)
          (fun p ↦ 1 / (p : ℝ)))
    unfold reciprocalWeight
    rw [hattach]
    simpa only [PrimeSums.bandReciprocalSum, H] using hReciprocalN
  have hInvW : (1 / (B.sampleData.W : ℝ)) ≤
      (1 / (B.sampleData.W : ℝ)) := le_rfl
  let gamma := B.canonicalEffectiveNuisanceGamma
    I U (3 * (a : ℝ)) T
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
      inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
    intro v
    simpa only [gamma, xi] using
      B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU hLo hHi T hbaseline hBWlarge z hz v
  have hgammaFloorLe : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
  have hcard : (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ dcard := by
    dsimp only [dcard]
    exact_mod_cast B.nuisanceCoord_card_le_head_add_one
  have hH0 : 0 ≤ H B.sampleData.n := by
    dsimp only [H]
    positivity
  have hnuisanceCompare :
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            markedError B.sampleData.n ^ 2 * H B.sampleData.n / gamma ≤
        nuisanceMajorant B.sampleData.n := by
    have hnum :
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              markedError B.sampleData.n ^ 2 * H B.sampleData.n ≤
          dcard * markedError B.sampleData.n ^ 2 * H B.sampleData.n := by
      gcongr
    exact (div_le_div₀
      (mul_nonneg (mul_nonneg hdcard (sq_nonneg _)) hH0)
      hnum hgammaFloor hgammaFloorLe : _)
  have hlossActual :
      quotientRowTarget +
          ((4 * pairCovarianceScale (profileError B.sampleData.n)) *
              H B.sampleData.n +
            2 * profileError B.sampleData.n +
            ((1 / DickmanBasic.rho DickmanBasic.U +
                2 * profileError B.sampleData.n) ^ 2 + CKernel) *
              (1 / (B.sampleData.W : ℝ))) +
          R B.sampleData.n +
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            markedError B.sampleData.n ^ 2 * H B.sampleData.n / gamma) ≤
        quotientMain / 2 := by
    have hsigned :
        ((1 / DickmanBasic.rho DickmanBasic.U +
              2 * profileError B.sampleData.n) ^ 2 + CKernel) =
          signedSecondConstant (profileError B.sampleData.n) CKernel := by
      rfl
    rw [hsigned]
    have hle :
        quotientRowTarget +
            ((4 * pairCovarianceScale (profileError B.sampleData.n)) *
                H B.sampleData.n +
              2 * profileError B.sampleData.n +
              signedSecondConstant (profileError B.sampleData.n) CKernel *
                (1 / (B.sampleData.W : ℝ))) +
            R B.sampleData.n +
            ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              markedError B.sampleData.n ^ 2 * H B.sampleData.n / gamma) ≤
          loss B.sampleData.n := by
      dsimp only [loss]
      linarith
    exact hle.trans hlossN.le
  have hsmall :
      quotientRowTarget +
          ((4 * pairCovarianceScale (profileError B.sampleData.n)) *
              H B.sampleData.n +
            2 * profileError B.sampleData.n +
            ((1 / DickmanBasic.rho DickmanBasic.U +
                2 * profileError B.sampleData.n) ^ 2 + CKernel) *
              (1 / (B.sampleData.W : ℝ))) +
          R B.sampleData.n +
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            markedError B.sampleData.n ^ 2 * H B.sampleData.n / gamma) ≤
        (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor := by
    calc
      _ ≤ quotientMain / 2 := hlossActual
      _ ≤ quotientMain := by linarith [quotientMain_pos]
      _ = (canonicalSlowKappa / 2) * (1 / 8 : ℝ) := by
        unfold quotientMain
        ring
      _ ≤ (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor :=
        mul_le_mul_of_nonneg_left hAnchorMass'
          (div_nonneg canonicalSlowKappa_pos.le (by norm_num))
  have hheadActual : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W := by
    intro h p
    rw [hPattern]
    exact hhead h p
  have hbase :=
    B.actualResidualSchur_fullQuotient_Dgap_canonicalKappa_independent_mu
      xi hgamma (hmarked0 B.sampleData.n) hgap hheadActual anchor hinterior'
      hmass
      (hprofile0 B.sampleData.n) hCKernel
      (by exact_mod_cast (show 0 < B.sampleData.W by omega))
      hTotal hInvW hrowReference hpair hsingle hKernel hrowPower
      hmarkedRows hsmall
  dsimp only
  intro b mu
  have hraw := hbase b mu
  dsimp only at hraw ⊢
  have hcoefficient : quotientKappa ≤
      (canonicalSlowKappa / 2) *
            anchorMass (primeWeight B.sampleData.n) anchor -
          quotientRowTarget -
          ((4 * pairCovarianceScale (profileError B.sampleData.n)) *
              H B.sampleData.n +
            2 * profileError B.sampleData.n +
            ((1 / DickmanBasic.rho DickmanBasic.U +
                2 * profileError B.sampleData.n) ^ 2 + CKernel) *
              (1 / (B.sampleData.W : ℝ))) -
          R B.sampleData.n -
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            markedError B.sampleData.n ^ 2 * H B.sampleData.n / gamma) := by
    have hmainLower : quotientMain ≤
        (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor := by
      calc
        quotientMain = (canonicalSlowKappa / 2) * (1 / 8 : ℝ) := by
          unfold quotientMain
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hAnchorMass'
          (div_nonneg canonicalSlowKappa_pos.le (by norm_num))
    dsimp only [quotientKappa]
    linarith
  have hnorm0 : 0 ≤ B.partition.data.bandNormSq
      (B.partition.data.gaugePart b) := B.partition.data.bandNormSq_nonneg _
  exact (mul_le_mul_of_nonneg_right hcoefficient hnorm0).trans hraw

end BridgeData
end
end Erdos390.Full.PaperBridgeFit
