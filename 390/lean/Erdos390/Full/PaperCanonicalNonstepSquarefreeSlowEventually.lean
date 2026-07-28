import Erdos390.Full.PaperNonstepSquarefreeSlowLedger
import Erdos390.Full.PaperActualSquarefreeReference
import Erdos390.Full.PaperCanonicalNonstepLocalDiagonalEventually
import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually
import Erdos390.Full.CanonicalEndpointCenterEnvelopeEventually
import Erdos390.Full.PoissonDickmanKernelBounds

/-!
# Canonical squarefree non-step slow row

This file performs the sharp moving-low conversion for the literal
coefficient `g_p = alpha_{j(p)} - t_p`.  The off-diagonal profile remainder
is divided by the output centre only after inserting the canonical estimate
`1/alpha_i = O_delta(log L)`.  The diagonal `p^{-2}` remainder is never
replaced by a global `O(1/W)` term: it is retained until the canonical local
diagonal theorem makes it `o(w alpha_i)`.

The structural cutoff is chosen before `delta`, the mesh, the head data, the
tilt box, and the requested accuracy.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus RegularMeshPrimeCutoffs
open PrimeSquarefreeDirichletGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open SquarefreeCovarianceReference
open PaperPrimePowerChamberError
open PoissonDickmanKernelBounds
open FiniteProbability

namespace BridgeData

set_option maxHeartbeats 2000000

/-- Global-order, profile-free squarefree/reference slow-row terminal.  All
profile, rate, moving-low centre, first-moment, and local-diagonal estimates
are derived internally. -/
theorem exists_global_cutoff_eventually_canonical_squarefreeSlowRow_sub_reference
    : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (hdelta : 0 < delta)
        (M : RegularRelativeMesh.Mesh delta eta),
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
        (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ (I : PhysicalIntervals) (Cmax : ℝ),
        (∀ sigma, 1 ≤ I.lower sigma) →
        (∀ sigma, I.upper sigma ≤ Cmax) →
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (Acoef Aphys : ℝ), 0 ≤ Acoef → 0 ≤ Aphys →
      ∀ r : ℝ, 0 < r →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              B.sampleData = canonicalSampleData
                (W := B.sampleData.W) Phead I
                  (ledger B.sampleData.n) hsep hremaining →
            (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            B.w = delta + eta →
            ∀ (xi : B.ParamSpace),
              (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
              |xi MomentCoord.physical| ≤ Aphys →
              ∀ i : Fin (M.cellCount + 1),
                |B.normalizedSquarefreeBandCovarianceRow
                    xi B.slowSquarefreeScore i -
                  B.referenceSlowRow i| ≤
                    r * B.w * B.bandCenter i := by
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    exists_covarianceKernel_abs_le_second
  let W₀ : ℕ := max 2
    (max RegularMeshPrimeCutoffs.canonicalActualMomentCutoff
      (max RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff
        RegularMeshPrimeCutoffs.canonicalNonstepLocalDiagonalCutoff))
  refine ⟨W₀, ?_⟩
  intro W hW delta eta hdelta M Head _instFintype _instDecidable
    _instNonempty Phead hhead I Cmax hlowerOne hupperMax
    Cprom Cbank ledger Acoef Aphys hAcoef hAphys r hr
  have hWone : 1 < W := by
    dsimp only [W₀] at hW
    omega
  have hWmoment :
      RegularMeshPrimeCutoffs.canonicalActualMomentCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWcenter :
      RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWlocal :
      RegularMeshPrimeCutoffs.canonicalNonstepLocalDiagonalCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hhead h p).mp hp |>.2
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I Cmax hlowerOne hupperMax Cprom Cbank ledger
        W hWone hHeadLe Acoef Aphys hAcoef hAphys
  let Calpha : ℝ :=
    RegularMeshPrimeCutoffs.canonicalCenterEnvelopeConstant delta
  let Ctail : ℝ :=
    (1 / DickmanBasic.rho DickmanBasic.U + 2) ^ 2 + CKernel + 1
  have hCtail : 0 < Ctail := by
    dsimp only [Ctail]
    have hrho : 0 < 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_pos.mpr DickmanBasic.rho_U_pos
    positivity
  let localRequest : ℝ := r / (3 * Ctail)
  have hlocalRequest : 0 < localRequest := by
    dsimp only [localRequest]
    positivity
  have hCovRate :=
    tendsto_pairCovarianceScale_mul_logL_zero
      profileError hprofileT hprofileRate
  have hOffRate : Tendsto
      (fun n : ℕ ↦
        28 * pairCovarianceScale (profileError n) * Calpha *
          Real.log (Scale.L n)) atTop (nhds 0) := by
    have hraw := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ 28 * Calpha) atTop (nhds (28 * Calpha))).mul
        hCovRate
    convert hraw using 1
    · funext n
      ring
    · ring
  have hDiagRate : Tendsto (fun n : ℕ ↦ 4 * profileError n)
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hprofileT : Tendsto
        (fun n : ℕ ↦ (4 : ℝ) * profileError n) atTop (nhds (4 * 0)))
  have hOffSmall : ∀ᶠ n : ℕ in atTop,
      28 * pairCovarianceScale (profileError n) * Calpha *
          Real.log (Scale.L n) < r / 3 :=
    hOffRate.eventually (eventually_lt_nhds (by positivity))
  have hDiagSmall : ∀ᶠ n : ℕ in atTop,
      4 * profileError n < r * delta / 3 :=
    hDiagRate.eventually (eventually_lt_nhds (by positivity))
  have hProfileOne : ∀ᶠ n : ℕ in atTop, profileError n < 1 :=
    hprofileT.eventually (eventually_lt_nhds (by norm_num))
  have hMoment :=
    RegularMeshPrimeCutoffs.Mesh.canonicalActualFirstMomentCutoff_eventually
      M hdelta W hWmoment
  have hCenter :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_inverse
      M hdelta W hWcenter
  have hLocal :=
    RegularMeshPrimeCutoffs.Mesh.canonicalNonstepLocalDiagonalCutoff_eventually
      M hdelta W hWlocal hlocalRequest
  filter_upwards [hOffSmall, hDiagSmall, hProfileOne, hMoment,
    hCenter, hLocal, eventually_ge_atTop Nprofile] with
      n hOffN hDiagN hProfileOneN hMomentN hCenterN hLocalN hnProfile
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    xi hetaCoeff hphysical i
  subst n
  subst W
  obtain ⟨_hWmoment, _hnMoment, hMomentAll⟩ := hMomentN
  obtain ⟨hWne, S, hpartitionUser⟩ := hpartition
  let Pcanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
      B.n_gt_one hWne S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨_devSupRaw, hdevL1Raw⟩ := hMomentAll S
  have hdevL1 : B.primeDeviationL1 ≤ 7 * B.w := by
    change B.partition.totalL1 ≤ 7 * B.w
    rw [hpartitionCanonical]
    calc
      Pcanonical.totalL1 ≤ 7 * (delta + M.ratio) := by
        simpa only [Pcanonical] using hdevL1Raw
      _ ≤ 7 * B.w := by
        rw [hscale]
        nlinarith [M.ratio_le_eta]
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
  obtain ⟨hpair, hsingle⟩ := hprofile B xi hnProfile
    hPattern hLo hHi hGuards hetaCoeff hphysical rfl
  have hKernel : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
        (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
          CKernel := by
    intro p hp
    let p' : PrimeIndex B.sampleData.n B.sampleData.W := ⟨p, hp⟩
    have ht := tPrime_mem_unit B.n_gt_one p'
    calc
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
        CKernel * tPrime B.sampleData.n p :=
          hKernelBound _ ht _ ht
      _ ≤ CKernel := by
        exact mul_le_of_le_one_right hCKernel ht.2
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hentryMix :=
    sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
      (hprofile0 B.sampleData.n) weight
      (B.actualComponentValuationLaw xi) B.n_gt_one
      hpair hsingle hKernel
  have hlaw :=
    B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hentryMix hlaw
  rw [hlaw] at hentryMix
  let E : ℝ := profileError B.sampleData.n
  let eOff : ℝ := 4 * pairCovarianceScale E
  let eDiag : ℝ := 2 * E
  let cDiag : ℝ :=
    (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 + CKernel
  have hE : 0 ≤ E := by
    simpa only [E] using hprofile0 B.sampleData.n
  have heOff : 0 ≤ eOff := by
    dsimp only [eOff]
    exact mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hE)
  have heDiag : 0 ≤ eDiag := by
    dsimp only [eDiag]
    positivity
  have hentry : ∀ p q :
      BandPrime B.sampleData.n B.sampleData.W,
      |(B.actualValuationLaw xi).covII p.1 q.1 -
          squarefreeReferenceEntry B.sampleData.n p.1 q.1| ≤
        eOff / ((p.1 : ℝ) * (q.1 : ℝ)) +
          (if p = q then
            eDiag / (p.1 : ℝ) + cDiag / (p.1 : ℝ) ^ 2
          else 0) := by
    simpa only [E, eOff, eDiag, cDiag] using hentryMix
  have hraw :=
    B.abs_squarefreeSlowRow_sub_referenceSlowRow_le
      xi heOff heDiag hentry hdevL1 i
  have hcenterInv : 1 / B.bandCenter i ≤
      Calpha * Real.log (Scale.L B.sampleData.n) := by
    change 1 / B.partition.center i ≤ _
    rw [hpartitionUser]
    simpa only [Calpha] using hCenterN B.n_gt_one hWne S i
  have hcenter : 0 < B.bandCenter i := B.bandCenter_pos i
  have hw : 0 < B.w := by
    rw [hscale]
    exact add_pos hdelta (lt_of_lt_of_le M.ratio_pos M.ratio_le_eta)
  have hdeltaW : delta ≤ B.w := by
    rw [hscale]
    linarith [M.ratio_pos, M.ratio_le_eta]
  have hunit : 1 ≤
      (Calpha * Real.log (Scale.L B.sampleData.n)) *
        B.bandCenter i := by
    exact (div_le_iff₀ hcenter).mp hcenterInv
  have hOffTerm : 7 * eOff * B.w ≤
      (r / 3) * B.w * B.bandCenter i := by
    have hcoeff : 0 ≤ 28 * pairCovarianceScale E * B.w := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hE)) hw.le
    calc
      7 * eOff * B.w =
          (28 * pairCovarianceScale E * B.w) * 1 := by
        dsimp only [eOff]
        ring
      _ ≤ (28 * pairCovarianceScale E * B.w) *
          ((Calpha * Real.log (Scale.L B.sampleData.n)) *
            B.bandCenter i) :=
        mul_le_mul_of_nonneg_left hunit hcoeff
      _ = (28 * pairCovarianceScale E * Calpha *
          Real.log (Scale.L B.sampleData.n)) * B.w *
            B.bandCenter i := by ring
      _ ≤ (r / 3) * B.w * B.bandCenter i := by
        have hOffN' :
            28 * pairCovarianceScale E * Calpha *
                Real.log (Scale.L B.sampleData.n) ≤ r / 3 := by
          simpa only [E] using hOffN.le
        have hmul := mul_le_mul_of_nonneg_right hOffN'
          (mul_nonneg hw.le hcenter.le)
        simpa only [mul_assoc] using hmul
  have hDiagTerm : 2 * eDiag * B.bandCenter i ≤
      (r / 3) * B.w * B.bandCenter i := by
    have hcoef : 4 * E ≤ (r / 3) * B.w := by
      calc
        4 * E ≤ r * delta / 3 := hDiagN.le
        _ ≤ (r / 3) * B.w := by
          nlinarith
    have hcoef' : 2 * eDiag ≤ (r / 3) * B.w := by
      dsimp only [eDiag]
      nlinarith
    exact mul_le_mul_of_nonneg_right hcoef' hcenter.le
  have hEOne : E ≤ 1 := by
    simpa only [E] using hProfileOneN.le
  have hcDiagLe : cDiag ≤ Ctail := by
    have hrho : 0 < 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_pos.mpr DickmanBasic.rho_U_pos
    have hbase :
        1 / DickmanBasic.rho DickmanBasic.U + 2 * E ≤
          1 / DickmanBasic.rho DickmanBasic.U + 2 := by
      nlinarith
    have hbase0 : 0 ≤
        1 / DickmanBasic.rho DickmanBasic.U + 2 * E := by
      positivity
    have htop0 : 0 ≤
        1 / DickmanBasic.rho DickmanBasic.U + 2 := by
      positivity
    have hsq := (sq_le_sq₀ hbase0 htop0).2 hbase
    dsimp only [cDiag, Ctail]
    nlinarith
  have hD : B.bandDeviationReciprocalSquare i ≤
      localRequest * B.w * B.bandCenter i := by
    change B.partition.normalizedDeviationReciprocalSquare i ≤
      localRequest * B.w * B.partition.center i
    rw [hpartitionUser]
    have hactual := hLocalN B.n_gt_one hWne S i
    calc
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
          B.n_gt_one hWne S).normalizedDeviationReciprocalSquare i ≤
          localRequest * (delta + M.ratio) *
            (RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
              B.n_gt_one hWne S).center i := hactual
      _ ≤ localRequest * B.w *
            (RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
              B.n_gt_one hWne S).center i := by
        have hscale' : delta + M.ratio ≤ B.w := by
          rw [hscale]
          linarith [M.ratio_le_eta]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hscale' hlocalRequest.le)
          ((RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
            B.n_gt_one hWne S).center_pos B.n_gt_one i).le
  have hD0 : 0 ≤ B.bandDeviationReciprocalSquare i := by
    unfold bandDeviationReciprocalSquare
    apply mul_nonneg
    · exact one_div_nonneg.mpr (B.harmonicMass_pos i).le
    · exact Finset.sum_nonneg fun p _hp ↦
        mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hLocalTerm : cDiag * B.bandDeviationReciprocalSquare i ≤
      (r / 3) * B.w * B.bandCenter i := by
    calc
      cDiag * B.bandDeviationReciprocalSquare i ≤
          Ctail * B.bandDeviationReciprocalSquare i :=
        mul_le_mul_of_nonneg_right hcDiagLe hD0
      _ ≤ Ctail * (localRequest * B.w * B.bandCenter i) :=
        mul_le_mul_of_nonneg_left hD hCtail.le
      _ = (r / 3) * B.w * B.bandCenter i := by
        dsimp only [localRequest]
        field_simp [hCtail.ne']
  exact hraw.trans (by
    have := add_le_add (add_le_add hOffTerm hDiagTerm) hLocalTerm
    nlinarith)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
