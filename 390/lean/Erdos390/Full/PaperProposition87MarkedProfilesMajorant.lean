import Erdos390.Full.PaperProposition87UniformMarkedProfiles
import Erdos390.Full.PaperCanonicalNuisanceUniformFloor

/-!
# An ambient-independent majorant for the Proposition 8.7 marked row

The signed-profile and nuisance errors are `o(1 / log L)`, while the total
harmonic mass is `O(log L)`.  This file records the exact finite inequality
which converts those rates into one constant independent of the ambient
integer.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

set_option maxHeartbeats 1200000

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Explicit fixed majorant after the two products with the harmonic mass
have each been made at most one. -/
def vectorFieldProfilesMarkedMajorant
    (K CF Cprod CKernel Rmax gammaFloor CinvOrd Tband Tslow Vlower Creg : ℝ) : ℝ :=
  let d := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let A := 1 / DickmanBasic.rho DickmanBasic.U
  let fast :=
    Cprod * K + CF +
      4 * (2 + 2 * A) + 2 + ((A + 2) ^ 2 + Cprod) + Rmax +
      d ^ 2 / gammaFloor
  let slow :=
    CKernel * (7 + Creg * K) + CF * (1 + Creg) +
      4 * (2 + 2 * A) * (7 + Creg * K) +
      2 * (1 + Creg) +
      ((A + 2) ^ 2 + CKernel) * (1 + Creg) +
      (1 + Creg) * Rmax + d ^ 2 * (7 + Creg * K) / gammaFloor
  fast * (CinvOrd * Tband) +
    (Tslow / Vlower) * (slow * B.w)

/-- Deterministic majorization.  No limit, filter, or unspecified `O(1)`
constant occurs in this statement. -/
theorem vectorFieldProfilesMarkedConstant_le_majorant
    {H K Eprofile CF Cprod CKernel R Rmax Cmarked gammaNuisance
      gammaFloor CinvOrd Tband Tslow Vlower Creg : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hE : 0 ≤ Eprofile) (hEone : Eprofile ≤ 1)
    (hEH : Eprofile * H ≤ 1)
    (hCF : 0 ≤ CF) (hCprod : 0 ≤ Cprod)
    (hCKernel : 0 ≤ CKernel)
    (hR : 0 ≤ R) (hRRmax : R ≤ Rmax)
    (hM : 0 ≤ Cmarked) (hMone : Cmarked ≤ 1)
    (hMH : Cmarked * H ≤ 1)
    (hgammaFloor : 0 < gammaFloor)
    (hgamma : 0 < gammaNuisance)
    (hgammaCompare : gammaFloor ≤ gammaNuisance)
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hTslow : 0 ≤ Tslow) (hVlower : 0 < Vlower)
    (hCreg : 0 ≤ Creg) (hW : 1 < B.sampleData.W) :
    B.vectorFieldProfilesMarkedConstant H K Eprofile CF Cprod CKernel R
        Cmarked gammaNuisance CinvOrd Tband Tslow Vlower Creg ≤
      B.vectorFieldProfilesMarkedMajorant K CF Cprod CKernel Rmax
        gammaFloor CinvOrd Tband Tslow Vlower Creg := by
  let A : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  let d : ℝ :=
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let S : ℝ := 7 + Creg * K
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hRmax : 0 ≤ Rmax := hR.trans hRRmax
  have hWinv0 : 0 ≤ 1 / (B.sampleData.W : ℝ) := by positivity
  have hWinv1 : 1 / (B.sampleData.W : ℝ) ≤ 1 := by
    have hcast : (1 : ℝ) ≤ B.sampleData.W := by
      exact_mod_cast hW.le
    simpa only [one_div_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hcast
  have hInvGamma : 1 / gammaNuisance ≤ 1 / gammaFloor :=
    one_div_le_one_div_of_le hgammaFloor hgammaCompare
  have hE2 : Eprofile ^ 2 ≤ Eprofile := by
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hEone)]
  have hM2 : Cmarked ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hM (sub_nonneg.mpr hMone)]
  have hpairOne :
      PaperPrimePowerChamberError.pairCovarianceScale Eprofile ≤
        2 + 2 * A := by
    unfold PaperPrimePowerChamberError.pairCovarianceScale
    dsimp only [A]
    have hcoef : 0 ≤
        1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U) := by positivity
    calc
      Eprofile * (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) +
          Eprofile ^ 2 ≤
        1 * (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) + 1 :=
          add_le_add (mul_le_mul_of_nonneg_right hEone hcoef)
            (hE2.trans hEone)
      _ = 2 + 2 * A := by dsimp only [A]; ring
  have hpairH :
      PaperPrimePowerChamberError.pairCovarianceScale Eprofile * H ≤
        2 + 2 * A := by
    unfold PaperPrimePowerChamberError.pairCovarianceScale
    dsimp only [A]
    have hcoef : 0 ≤
        1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U) := by positivity
    calc
      (Eprofile * (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) +
          Eprofile ^ 2) * H =
        (Eprofile * H) *
            (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) +
          Eprofile * (Eprofile * H) := by ring
      _ ≤ 1 * (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) +
          1 * 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hEH hcoef)
          (mul_le_mul hEone hEH (mul_nonneg hE hH) (by norm_num))
      _ = 2 + 2 * A := by dsimp only [A]; ring
  have hSquare :
      (A + 2 * Eprofile) ^ 2 ≤ (A + 2) ^ 2 := by
    have hbase : A + 2 * Eprofile ≤ A + 2 := by linarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hbase
  have hTailFast :
      ((A + 2 * Eprofile) ^ 2 + Cprod) *
          (1 / (B.sampleData.W : ℝ)) ≤
        (A + 2) ^ 2 + Cprod := by
    calc
      ((A + 2 * Eprofile) ^ 2 + Cprod) *
          (1 / (B.sampleData.W : ℝ)) ≤
        ((A + 2) ^ 2 + Cprod) * 1 := by
          exact mul_le_mul (add_le_add hSquare le_rfl) hWinv1
            hWinv0 (add_nonneg (sq_nonneg _) hCprod)
      _ = _ := by ring
  have hTailSlow :
      (((A + 2 * Eprofile) ^ 2 + CKernel) * (1 + Creg)) *
          (1 / (B.sampleData.W : ℝ)) ≤
        ((A + 2) ^ 2 + CKernel) * (1 + Creg) := by
    have hbase :
        ((A + 2 * Eprofile) ^ 2 + CKernel) * (1 + Creg) ≤
          ((A + 2) ^ 2 + CKernel) * (1 + Creg) :=
      mul_le_mul_of_nonneg_right (add_le_add hSquare le_rfl)
        (by positivity)
    calc
      (((A + 2 * Eprofile) ^ 2 + CKernel) * (1 + Creg)) *
          (1 / (B.sampleData.W : ℝ)) ≤
        (((A + 2) ^ 2 + CKernel) * (1 + Creg)) * 1 := by
          exact mul_le_mul hbase hWinv1 hWinv0 (by positivity)
      _ = _ := by ring
  have hFastNuisance :
      ((d * (Cmarked * H)) / gammaNuisance) * (d * Cmarked) ≤
        d ^ 2 / gammaFloor := by
    have hMH_M : (Cmarked * H) * Cmarked ≤ 1 := by
      exact (mul_le_mul hMH hMone hM (by norm_num)).trans_eq
        (one_mul 1)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      (d * (Cmarked * H) * gammaNuisance⁻¹) * (d * Cmarked) =
          d ^ 2 * ((Cmarked * H) * Cmarked) * gammaNuisance⁻¹ := by ring
      _ ≤ d ^ 2 * 1 * gammaFloor⁻¹ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hMH_M (sq_nonneg d))
          (by simpa only [one_div] using hInvGamma)
          (inv_nonneg.mpr hgamma.le) (mul_nonneg (sq_nonneg d) (by norm_num))
      _ = d ^ 2 * gammaFloor⁻¹ := by ring
  have hSlowNuisance :
      ((d * (Cmarked * S)) / gammaNuisance) * (d * Cmarked) ≤
        d ^ 2 * S / gammaFloor := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      (d * (Cmarked * S) * gammaNuisance⁻¹) * (d * Cmarked) =
          (d ^ 2 * S) * (Cmarked ^ 2) * gammaNuisance⁻¹ := by ring
      _ ≤ (d ^ 2 * S) * 1 * gammaFloor⁻¹ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hM2
            (mul_nonneg (sq_nonneg d) hS))
          (by simpa only [one_div] using hInvGamma)
          (inv_nonneg.mpr hgamma.le)
          (mul_nonneg (mul_nonneg (sq_nonneg d) hS) (by norm_num))
      _ = d ^ 2 * S * gammaFloor⁻¹ := by ring
  let fastActual := fastProfilesMarkedConstant d H K Eprofile CF Cprod R
    Cmarked gammaNuisance (1 / (B.sampleData.W : ℝ))
  let fastBound := Cprod * K + CF + 4 * (2 + 2 * A) + 2 +
    ((A + 2) ^ 2 + Cprod) + Rmax + d ^ 2 / gammaFloor
  have hfast : fastActual ≤ fastBound := by
    dsimp only [fastActual, fastBound, fastProfilesMarkedConstant]
    dsimp only [A, d] at hpairH hTailFast hFastNuisance ⊢
    nlinarith
  let slowActual := slowProfilesMarkedConstant d Creg K R Eprofile CF
    CKernel Cmarked gammaNuisance (1 / (B.sampleData.W : ℝ))
  let slowBound := CKernel * S + CF * (1 + Creg) +
    4 * (2 + 2 * A) * S + 2 * (1 + Creg) +
    ((A + 2) ^ 2 + CKernel) * (1 + Creg) +
    (1 + Creg) * Rmax + d ^ 2 * S / gammaFloor
  have hslow : slowActual ≤ slowBound := by
    dsimp only [slowActual, slowBound, slowProfilesMarkedConstant,
      actualSquarefreeMarkedConstant]
    dsimp only [S, A, d] at hpairOne hTailSlow hSlowNuisance ⊢
    have hpairScaled := mul_le_mul_of_nonneg_right hpairOne
      (by positivity : 0 ≤ 7 + Creg * K)
    have hRscaled := mul_le_mul_of_nonneg_left hRRmax (by positivity)
    nlinarith
  have hfast0 : 0 ≤ fastActual := by
    dsimp only [fastActual, fastProfilesMarkedConstant]
    have hpair0 :=
      PaperPrimePowerChamberError.pairCovarianceScale_nonneg hE
    positivity
  have hslow0 : 0 ≤ slowActual := by
    dsimp only [slowActual, slowProfilesMarkedConstant,
      actualSquarefreeMarkedConstant]
    have hpair0 :=
      PaperPrimePowerChamberError.pairCovarianceScale_nonneg hE
    positivity
  unfold vectorFieldProfilesMarkedConstant
    vectorFieldProfilesMarkedMajorant
  dsimp only [A, d, S, fastActual, fastBound, slowActual, slowBound]
  exact add_le_add
    (mul_le_mul_of_nonneg_right hfast (mul_nonneg hCinvOrd hTband))
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hslow B.w_pos.le)
      (div_nonneg hTslow hVlower.le))

/-- Mesh-independent form of the same majorant.  The actual compensated
target is bounded by `targetScale * w` and the slow variance by
`gammaSlow * w^2`; the two powers of the moving mesh scale cancel exactly. -/
def vectorFieldProfilesMarkedScaledMajorant
    (K CF Cprod CKernel Rmax gammaFloor CinvOrd Tband
      targetScale gammaSlow Creg : ℝ) : ℝ :=
  let d := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let A := 1 / DickmanBasic.rho DickmanBasic.U
  let fast :=
    Cprod * K + CF +
      4 * (2 + 2 * A) + 2 + ((A + 2) ^ 2 + Cprod) + Rmax +
      d ^ 2 / gammaFloor
  let slow :=
    CKernel * (7 + Creg * K) + CF * (1 + Creg) +
      4 * (2 + 2 * A) * (7 + Creg * K) +
      2 * (1 + Creg) +
      ((A + 2) ^ 2 + CKernel) * (1 + Creg) +
      (1 + Creg) * Rmax +
      d ^ 2 * (7 + Creg * K) / gammaFloor
  fast * (CinvOrd * Tband) + (targetScale / gammaSlow) * slow

/-- Exact cancellation lemma used by the paper-order Proposition 8.7
terminal.  Its right side contains no occurrence of `B.w`. -/
theorem vectorFieldProfilesMarkedConstant_le_scaledMajorant
    {H K Eprofile CF Cprod CKernel R Rmax Cmarked gammaNuisance
      gammaFloor CinvOrd Tband targetScale gammaSlow Creg : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hE : 0 ≤ Eprofile) (hEone : Eprofile ≤ 1)
    (hEH : Eprofile * H ≤ 1)
    (hCF : 0 ≤ CF) (hCprod : 0 ≤ Cprod)
    (hCKernel : 0 ≤ CKernel)
    (hR : 0 ≤ R) (hRRmax : R ≤ Rmax)
    (hM : 0 ≤ Cmarked) (hMone : Cmarked ≤ 1)
    (hMH : Cmarked * H ≤ 1)
    (hgammaFloor : 0 < gammaFloor)
    (hgamma : 0 < gammaNuisance)
    (hgammaCompare : gammaFloor ≤ gammaNuisance)
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hTargetScale : 0 ≤ targetScale) (hgammaSlow : 0 < gammaSlow)
    (hCreg : 0 ≤ Creg) (hW : 1 < B.sampleData.W) :
    B.vectorFieldProfilesMarkedConstant H K Eprofile CF Cprod CKernel R
        Cmarked gammaNuisance CinvOrd Tband (B.w * targetScale)
          (gammaSlow * B.w ^ 2) Creg ≤
      B.vectorFieldProfilesMarkedScaledMajorant K CF Cprod CKernel Rmax
        gammaFloor CinvOrd Tband targetScale gammaSlow Creg := by
  have hraw := B.vectorFieldProfilesMarkedConstant_le_majorant
    hH hK hE hEone hEH hCF hCprod hCKernel hR hRRmax hM hMone hMH
      hgammaFloor hgamma hgammaCompare hCinvOrd hTband
      (mul_nonneg B.w_pos.le hTargetScale)
      (mul_pos hgammaSlow (sq_pos_of_pos B.w_pos)) hCreg hW
  calc
    _ ≤ B.vectorFieldProfilesMarkedMajorant K CF Cprod CKernel Rmax
          gammaFloor CinvOrd Tband (B.w * targetScale)
            (gammaSlow * B.w ^ 2) Creg := hraw
    _ = B.vectorFieldProfilesMarkedScaledMajorant K CF Cprod CKernel Rmax
          gammaFloor CinvOrd Tband targetScale gammaSlow Creg := by
      unfold vectorFieldProfilesMarkedMajorant
        vectorFieldProfilesMarkedScaledMajorant
      field_simp [B.w_pos.ne', hgammaSlow.ne']

/-- A version of the scaled majorant which is defined before a particular
bridge datum exists.  The nuisance dimension is replaced by the uniform
head-cardinality ceiling.  Consequently this constant can be quantified
before the ambient integer and before the canonical sample is constructed. -/
def vectorFieldProfilesMarkedScaledHeadMajorant
    (Head : Type*) [Fintype Head]
    (K CF Cprod CKernel Rmax gammaFloor CinvOrd Tband
      targetScale gammaSlow Creg : ℝ) : ℝ :=
  let D2 := (Fintype.card Head + 1 : ℝ)
  let A := 1 / DickmanBasic.rho DickmanBasic.U
  let fast :=
    Cprod * K + CF +
      4 * (2 + 2 * A) + 2 + ((A + 2) ^ 2 + Cprod) + Rmax +
      D2 / gammaFloor
  let slow :=
    CKernel * (7 + Creg * K) + CF * (1 + Creg) +
      4 * (2 + 2 * A) * (7 + Creg * K) +
      2 * (1 + Creg) +
      ((A + 2) ^ 2 + CKernel) * (1 + Creg) +
      (1 + Creg) * Rmax +
      D2 * (7 + Creg * K) / gammaFloor
  fast * (CinvOrd * Tband) + (targetScale / gammaSlow) * slow

/-- The datum-dependent scaled majorant is bounded by the single constant
chosen from the finite head type.  This is the formal uniformity statement
needed to move `∃ Crow` outside the eventual ambient quantifier. -/
theorem vectorFieldProfilesMarkedScaledMajorant_le_headMajorant
    {K CF Cprod CKernel Rmax gammaFloor CinvOrd Tband
      targetScale gammaSlow Creg : ℝ}
    (hK : 0 ≤ K)
    (hgammaFloor : 0 < gammaFloor)
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hTargetScale : 0 ≤ targetScale) (hgammaSlow : 0 < gammaSlow)
    (hCreg : 0 ≤ Creg) :
    B.vectorFieldProfilesMarkedScaledMajorant K CF Cprod CKernel Rmax
        gammaFloor CinvOrd Tband targetScale gammaSlow Creg ≤
      vectorFieldProfilesMarkedScaledHeadMajorant Head K CF Cprod CKernel
        Rmax gammaFloor CinvOrd Tband targetScale gammaSlow Creg := by
  let d2 : ℝ :=
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let D2 : ℝ := (Fintype.card Head + 1 : ℝ)
  have hd2 : 0 ≤ d2 := by dsimp only [d2]; positivity
  have hD2 : 0 ≤ D2 := by dsimp only [D2]; positivity
  have hdim : d2 ≤ D2 := by
    dsimp only [d2, D2]
    exact_mod_cast B.nuisanceCoord_card_le_head_add_one
  have hsqrt :
      (Real.sqrt
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)) ^ 2 = d2 := by
    dsimp only [d2]
    exact Real.sq_sqrt (by positivity)
  have hdiv : d2 / gammaFloor ≤ D2 / gammaFloor :=
    div_le_div_of_nonneg_right hdim hgammaFloor.le
  have hS : 0 ≤ 7 + Creg * K := by positivity
  have hdivS : d2 * (7 + Creg * K) / gammaFloor ≤
      D2 * (7 + Creg * K) / gammaFloor := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hdim hS) hgammaFloor.le
  have hfastMul : 0 ≤ CinvOrd * Tband :=
    mul_nonneg hCinvOrd hTband
  have hslowMul : 0 ≤ targetScale / gammaSlow :=
    div_nonneg hTargetScale hgammaSlow.le
  unfold vectorFieldProfilesMarkedScaledMajorant
    vectorFieldProfilesMarkedScaledHeadMajorant
  dsimp only [D2]
  rw [hsqrt]
  exact add_le_add
    (mul_le_mul_of_nonneg_right
      (add_le_add_right hdiv _) hfastMul)
    (mul_le_mul_of_nonneg_left
      (add_le_add_right hdivS _) hslowMul)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
