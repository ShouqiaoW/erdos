import Erdos390.Full.PaperCanonicalNonstepSquarefreeSlowEventually
import Erdos390.Full.PaperCanonicalNonstepPowerInputsEventually
import Erdos390.Full.PaperNonstepPowerCorrectionLedger

/-!
# Canonical full-valuation non-step slow row

This file joins four independently auditable estimates without replacing
the primewise coefficient `alpha_{j(p)} - t_p` by a step function:

1. Lemma 7.5 for the raw canonical reference law;
2. the actual/raw power-correction row;
3. the literal moving-low reciprocal-square diagonal; and
4. the squarefree/reference signed-profile comparison.

For every requested relative accuracy, `W` is selected before `delta`,
`eta`, the mesh, all head data, and the tilt box.  Every remaining error is
then `o(w alpha_i)`, including the lowest band where `alpha_0 -> 0`.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperGuardCensus RegularMeshPrimeCutoffs

namespace BridgeData

set_option maxHeartbeats 3000000

/-- Fully discharged canonical full-valuation/reference slow-row terminal.
The outer order `r, W₀, W, delta, eta, mesh, ...` makes the cutoff choice
non-circular and independent of every later moving-low or tilt parameter. -/
theorem forall_accuracy_exists_cutoff_eventually_canonical_fullSlowRow_sub_reference
    : ∀ r : ℝ, 0 < r →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
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
              B.partition = Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            B.w = delta + eta →
            ∀ (xi : B.ParamSpace),
              (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
              |xi MomentCoord.physical| ≤ Aphys →
              ∀ i : Fin (M.cellCount + 1),
                |B.normalizedBandCovarianceRow xi B.slowScore i -
                    B.referenceSlowRow i| ≤
                  r * B.w * B.bandCenter i := by
  intro r hr
  let share : ℝ := r / 5
  have hshare : 0 < share := by dsimp only [share]; positivity
  obtain ⟨Wsquare, hSquareMain⟩ :=
    exists_global_cutoff_eventually_canonical_squarefreeSlowRow_sub_reference
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  have hInvNat : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ))
      atTop (nhds 0) := by
    have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    simpa only [one_div] using
      hinv.comp tendsto_natCast_atTop_atTop
  have hStructT : Tendsto
      (fun W : ℕ ↦ 21 * Cpow * (1 / (W : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ (21 * Cpow) * (1 / (W : ℝ)))
          atTop (nhds ((21 * Cpow) * 0)))
  obtain ⟨Wstruct, hWstruct⟩ := eventually_atTop.1
    (hStructT.eventually (eventually_lt_nhds hshare))
  let W₀ : ℕ := max 2
    (max Wsquare
      (max canonicalActualMomentCutoff
        (max canonicalCenterEnvelopeCutoff
          (max canonicalNonstepLocalDiagonalCutoff Wstruct))))
  refine ⟨W₀, ?_⟩
  intro W hW delta eta hdelta M Head _instFintype _instDecidable
    _instNonempty Phead hhead I Cmax hlowerOne hupperMax
    Cprom Cbank ledger Acoef Aphys hAcoef hAphys
  have hWone : 1 < W := by
    dsimp only [W₀] at hW
    omega
  have hWsquare : Wsquare ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWmoment : canonicalActualMomentCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWcenter : canonicalCenterEnvelopeCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWlocal : canonicalNonstepLocalDiagonalCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWstruct' : Wstruct ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hStructSmall : 21 * Cpow * (1 / (W : ℝ)) < share :=
    hWstruct W hWstruct'
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hhead h p).mp hp |>.2
  obtain ⟨_hCpowInput, hInputMain⟩ :=
    boxIndependent_canonicalRaw_nonstepPower_inputs
      Phead I Cmax hlowerOne hupperMax Cprom Cbank ledger
  obtain ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
      hcombinedRate, Ninput, hInput⟩ :=
    hInputMain W hWone hHeadLe Acoef hAcoef Aphys hAphys
  let combined : ℕ → ℝ := fun n ↦
    canonicalNonstepPowerCorrection
      Phead I Cmax Cprom Cbank W Acoef Aphys n
  let Calpha : ℝ := canonicalCenterEnvelopeConstant delta
  have hEpsilonScaled : Tendsto
      (fun n : ℕ ↦
        21 * epsilon75 n * (1 / (W : ℝ)) * Calpha *
          Real.log (Scale.L n)) atTop (nhds 0) := by
    have hraw := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ 21 * (1 / (W : ℝ)) * Calpha)
        atTop (nhds (21 * (1 / (W : ℝ)) * Calpha))).mul
          hepsilonRate
    convert hraw using 1
    · funext n
      ring
    · ring
  have hCombinedScaled : Tendsto
      (fun n : ℕ ↦ combined n * Calpha * Real.log (Scale.L n))
      atTop (nhds 0) := by
    have hraw := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ Calpha) atTop (nhds Calpha)).mul hcombinedRate
    convert hraw using 1
    · funext n
      dsimp only [combined]
      ring
    · ring
  have hEpsilonSmall : ∀ᶠ n : ℕ in atTop,
      21 * epsilon75 n * (1 / (W : ℝ)) * Calpha *
          Real.log (Scale.L n) < share :=
    hEpsilonScaled.eventually (eventually_lt_nhds hshare)
  have hCombinedSmall : ∀ᶠ n : ℕ in atTop,
      combined n * Calpha * Real.log (Scale.L n) < share :=
    hCombinedScaled.eventually (eventually_lt_nhds hshare)
  have hEpsilonOne : ∀ᶠ n : ℕ in atTop, epsilon75 n < 1 :=
    hepsilonT.eventually (eventually_lt_nhds (by norm_num))
  let localRequest : ℝ := share / (3 * (Cpow + 1))
  have hlocalRequest : 0 < localRequest := by
    dsimp only [localRequest]
    positivity
  have hMoment :=
    Mesh.canonicalActualFirstMomentCutoff_eventually
      M hdelta W hWmoment
  have hCenter :=
    Mesh.canonicalCenterEnvelopeCutoff_eventually_inverse
      M hdelta W hWcenter
  have hLocal :=
    Mesh.canonicalNonstepLocalDiagonalCutoff_eventually
      M hdelta W hWlocal hlocalRequest
  have hSquare := hSquareMain W hWsquare hdelta M Phead hhead
    I Cmax hlowerOne hupperMax Cprom Cbank ledger
      Acoef Aphys hAcoef hAphys share hshare
  filter_upwards [hEpsilonSmall, hCombinedSmall, hEpsilonOne,
    hMoment, hCenter, hLocal, hSquare, eventually_ge_atTop Ninput] with
      n hEpsilonSmallN hCombinedSmallN hEpsilonOneN hMomentN
      hCenterN hLocalN hSquareN hnInput
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    xi heta hphys i
  subst n
  subst W
  obtain ⟨_hWneMoment, _hnMoment, hMomentAll⟩ := hMomentN
  obtain ⟨hWne, S, hpartitionUser⟩ := hpartition
  let Pcanonical := Mesh.canonicalPartition M hdelta B.n_gt_one hWne S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨hdevSupRaw, hdevL1Raw⟩ := hMomentAll S
  have hactualScale : delta + M.ratio ≤ B.w := by
    rw [hscale]
    linarith [M.ratio_le_eta]
  have hw : 0 < B.w := by
    exact (add_pos hdelta M.ratio_pos).trans_le hactualScale
  have hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ B.w := by
    intro p
    change |B.partition.deviation p| ≤ B.w
    rw [hpartitionCanonical]
    exact (hdevSupRaw p).trans hactualScale
  have hdevL1 : B.primeDeviationL1 ≤ 7 * B.w := by
    change B.partition.totalL1 ≤ 7 * B.w
    rw [hpartitionCanonical]
    exact hdevL1Raw.trans
      (mul_le_mul_of_nonneg_left hactualScale (by norm_num))
  have hcenterInv : 1 / B.bandCenter i ≤
      Calpha * Real.log (Scale.L B.sampleData.n) := by
    change 1 / B.partition.center i ≤ _
    rw [hpartitionUser]
    simpa only [Calpha] using hCenterN B.n_gt_one hWne S i
  have hcenter : 0 < B.bandCenter i := B.bandCenter_pos i
  have hunit : 1 ≤
      (Calpha * Real.log (Scale.L B.sampleData.n)) *
        B.bandCenter i :=
    (div_le_iff₀ hcenter).mp hcenterInv
  have hD : B.bandDeviationReciprocalSquare i ≤
      localRequest * B.w * B.bandCenter i := by
    change B.partition.normalizedDeviationReciprocalSquare i ≤
      localRequest * B.w * B.partition.center i
    rw [hpartitionUser]
    have hactual := hLocalN B.n_gt_one hWne S i
    exact hactual.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hactualScale hlocalRequest.le)
      ((Mesh.canonicalPartition M hdelta B.n_gt_one hWne S).center_pos
        B.n_gt_one i).le)
  obtain ⟨h75, hpowerRow⟩ :=
    hInput B xi hnInput rfl hsep hremaining hcanonical heta hphys
  let hS : ∀ c : Cell Head,
      (rawCell Phead I B.sampleData.n c).Nonempty :=
    fun c ↦ (hremaining c).mono Finset.sdiff_subset
  let referenceLaw :=
    B.canonicalRawMediumReferenceLaw
      Phead I Cmax xi hupperMax hS
  have h75' : PaperPrimePowerLemma75.PrimePowerTransferBounds
      referenceLaw B.sampleData.n B.sampleData.W Cpow
        (epsilon75 B.sampleData.n) := by
    simpa only [referenceLaw, hS, Cpow] using h75
  have hpowerRow' : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)| ≤
        combined B.sampleData.n := by
    simpa only [referenceLaw, hS, combined] using hpowerRow
  have hrawLedger :=
    B.abs_nonstepFullCoefficientRow_sub_squarefree_le_nonstepBudget
      referenceLaw hCpow.le (hepsilon0 B.sampleData.n) hw.le
        (by simpa only using hWone) h75' hdevL1 i
  have hcorrection :=
    B.abs_nonstepPowerCorrectionRow_sub_le
      (B.actualValuationLaw xi) referenceLaw hw.le hdevSup hpowerRow' i
  have hcombined0 : 0 ≤ combined B.sampleData.n := by
    dsimp only [combined]
    have hupperOne : ∀ sigma, 1 ≤ I.upper sigma := fun sigma ↦
      (hlowerOne sigma).trans (I.lower_lt_upper sigma).le
    exact canonicalNonstepPowerCorrection_nonneg Phead I
      ((hupperOne .minus).trans (hupperMax .minus)) hAphys
      (by simpa only using hWone) B.n_gt_one
  have hStructTerm :
      (21 * Cpow * (1 / (B.sampleData.W : ℝ))) *
          (B.w * B.bandCenter i) ≤
        share * B.w * B.bandCenter i := by
    have hcoef : 21 * Cpow * (1 / (B.sampleData.W : ℝ)) ≤ share := by
      simpa only using hStructSmall.le
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hcoef
        (mul_nonneg hw.le hcenter.le)
  have hEpsilonTerm :
      (21 * epsilon75 B.sampleData.n *
          (1 / (B.sampleData.W : ℝ))) * B.w ≤
        share * B.w * B.bandCenter i := by
    have hcoef0 : 0 ≤ 21 * epsilon75 B.sampleData.n *
        (1 / (B.sampleData.W : ℝ)) * B.w := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (hepsilon0 _))
          (one_div_nonneg.mpr (Nat.cast_nonneg _))) hw.le
    calc
      (21 * epsilon75 B.sampleData.n *
          (1 / (B.sampleData.W : ℝ))) * B.w =
          (21 * epsilon75 B.sampleData.n *
            (1 / (B.sampleData.W : ℝ)) * B.w) * 1 := by ring
      _ ≤ (21 * epsilon75 B.sampleData.n *
            (1 / (B.sampleData.W : ℝ)) * B.w) *
          ((Calpha * Real.log (Scale.L B.sampleData.n)) *
            B.bandCenter i) :=
        mul_le_mul_of_nonneg_left hunit hcoef0
      _ = (21 * epsilon75 B.sampleData.n *
            (1 / (B.sampleData.W : ℝ)) * Calpha *
              Real.log (Scale.L B.sampleData.n)) *
          B.w * B.bandCenter i := by ring
      _ ≤ share * B.w * B.bandCenter i := by
        have hsmall :
            21 * epsilon75 B.sampleData.n *
                (1 / (B.sampleData.W : ℝ)) * Calpha *
                  Real.log (Scale.L B.sampleData.n) ≤ share :=
          hEpsilonSmallN.le
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hsmall
            (mul_nonneg hw.le hcenter.le)
  have hLocalTerm :
      3 * (Cpow + epsilon75 B.sampleData.n) *
          B.bandDeviationReciprocalSquare i ≤
        share * B.w * B.bandCenter i := by
    have hepsOne : epsilon75 B.sampleData.n ≤ 1 := hEpsilonOneN.le
    have hcoef : 3 * (Cpow + epsilon75 B.sampleData.n) ≤
        3 * (Cpow + 1) := by nlinarith
    have hD0 : 0 ≤ B.bandDeviationReciprocalSquare i := by
      unfold bandDeviationReciprocalSquare
      apply mul_nonneg
      · exact one_div_nonneg.mpr (B.harmonicMass_pos i).le
      · exact Finset.sum_nonneg fun p _hp ↦
          mul_nonneg (abs_nonneg _) (sq_nonneg _)
    calc
      3 * (Cpow + epsilon75 B.sampleData.n) *
          B.bandDeviationReciprocalSquare i ≤
        (3 * (Cpow + 1)) * B.bandDeviationReciprocalSquare i :=
          mul_le_mul_of_nonneg_right hcoef hD0
      _ ≤ (3 * (Cpow + 1)) *
          (localRequest * B.w * B.bandCenter i) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      _ = share * B.w * B.bandCenter i := by
        dsimp only [localRequest]
        have hden : Cpow + 1 ≠ 0 := by positivity
        field_simp [hden]
  have hCorrectionTerm : combined B.sampleData.n * B.w ≤
      share * B.w * B.bandCenter i := by
    have hcoef0 : 0 ≤ combined B.sampleData.n * B.w :=
      mul_nonneg hcombined0 hw.le
    calc
      combined B.sampleData.n * B.w =
          (combined B.sampleData.n * B.w) * 1 := by ring
      _ ≤ (combined B.sampleData.n * B.w) *
          ((Calpha * Real.log (Scale.L B.sampleData.n)) *
            B.bandCenter i) :=
        mul_le_mul_of_nonneg_left hunit hcoef0
      _ = (combined B.sampleData.n * Calpha *
            Real.log (Scale.L B.sampleData.n)) *
          B.w * B.bandCenter i := by ring
      _ ≤ share * B.w * B.bandCenter i := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hCombinedSmallN.le
            (mul_nonneg hw.le hcenter.le)
  have hrawTerms :
      nonstepPrimePowerRowBudget Cpow
          (epsilon75 B.sampleData.n) B.w
          (B.sampleData.W : ℝ) (B.bandCenter i)
          (B.bandDeviationReciprocalSquare i) ≤
        3 * share * B.w * B.bandCenter i := by
    unfold nonstepPrimePowerRowBudget
    linarith
  have hfullSquarefree :
      |B.nonstepFullCoefficientRow (B.actualValuationLaw xi) i -
          B.nonstepSquarefreeCoefficientRow (B.actualValuationLaw xi) i| ≤
        4 * share * B.w * B.bandCenter i := by
    let A := B.nonstepFullCoefficientRow (B.actualValuationLaw xi) i -
      B.nonstepSquarefreeCoefficientRow (B.actualValuationLaw xi) i
    let R := B.nonstepFullCoefficientRow referenceLaw i -
      B.nonstepSquarefreeCoefficientRow referenceLaw i
    have htriangle : |A| ≤ |A - R| + |R| := by
      calc
        |A| = |(A - R) + R| := by
          congr 1
          ring
        _ ≤ |A - R| + |R| := abs_add_le _ _
    calc
      |B.nonstepFullCoefficientRow (B.actualValuationLaw xi) i -
          B.nonstepSquarefreeCoefficientRow (B.actualValuationLaw xi) i| =
          |A| := by rfl
      _ ≤ |A - R| + |R| := htriangle
      _ ≤ combined B.sampleData.n * B.w +
          nonstepPrimePowerRowBudget Cpow
            (epsilon75 B.sampleData.n) B.w
            (B.sampleData.W : ℝ) (B.bandCenter i)
            (B.bandDeviationReciprocalSquare i) :=
        add_le_add hcorrection hrawLedger
      _ ≤ 4 * share * B.w * B.bandCenter i := by
        linarith
  have hrows := B.normalizedSlowRows_eq_fullSquarefreeCoefficientRows xi i
  have hSquareBound := hSquareN B rfl rfl hsep hremaining hcanonical
    ⟨hWne, S, hpartitionUser⟩ hscale xi heta hphys i
  rw [hrows.2] at hSquareBound
  change |B.nonstepSquarefreeCoefficientRow (B.actualValuationLaw xi) i -
      B.referenceSlowRow i| ≤ share * B.w * B.bandCenter i at hSquareBound
  rw [hrows.1]
  change |B.nonstepFullCoefficientRow (B.actualValuationLaw xi) i -
      B.referenceSlowRow i| ≤ r * B.w * B.bandCenter i
  have htriangle :
      |B.nonstepFullCoefficientRow (B.actualValuationLaw xi) i -
          B.referenceSlowRow i| ≤
        |B.nonstepFullCoefficientRow (B.actualValuationLaw xi) i -
          B.nonstepSquarefreeCoefficientRow (B.actualValuationLaw xi) i| +
        |B.nonstepSquarefreeCoefficientRow (B.actualValuationLaw xi) i -
          B.referenceSlowRow i| := by
    rw [show
      B.nonstepFullCoefficientRow (B.actualValuationLaw xi) i -
          B.referenceSlowRow i =
        (B.nonstepFullCoefficientRow (B.actualValuationLaw xi) i -
          B.nonstepSquarefreeCoefficientRow (B.actualValuationLaw xi) i) +
        (B.nonstepSquarefreeCoefficientRow (B.actualValuationLaw xi) i -
          B.referenceSlowRow i) by ring]
    exact abs_add_le _ _
  calc
    |B.nonstepFullCoefficientRow (B.actualValuationLaw xi) i -
        B.referenceSlowRow i| ≤
      |B.nonstepFullCoefficientRow (B.actualValuationLaw xi) i -
          B.nonstepSquarefreeCoefficientRow (B.actualValuationLaw xi) i| +
        |B.nonstepSquarefreeCoefficientRow (B.actualValuationLaw xi) i -
          B.referenceSlowRow i| := htriangle
    _ ≤ 4 * share * B.w * B.bandCenter i +
        share * B.w * B.bandCenter i :=
      add_le_add hfullSquarefree (by
        exact hSquareBound)
    _ = r * B.w * B.bandCenter i := by
      dsimp only [share]
      ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
