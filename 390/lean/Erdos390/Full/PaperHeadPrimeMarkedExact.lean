import Erdos390.Full.PaperProposition87Assembly

/-!
# Exact fixed-head-prime rows

For `p ≤ W`, the canonical head pattern fixes the full `p`-adic valuation
pointwise on every structured cell.  Thus the marked valuation is literally
a function of the finite head tag.  The ODE endpoint preserves its moment
exactly; no moving-prime `C / p` estimate or limiting argument is needed.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- A fixed head-prime valuation is exactly the head-tag function carrying
the prescribed exponent. -/
theorem markedValuation_eq_headFunctionScore_of_exactHeadPrimes
    (hhead : ∀ h : Head, ∀ r : ℕ,
      r ∈ (B.sampleData.pattern h).primes ↔
        r.Prime ∧ r ≤ B.sampleData.W)
    {p : ℕ} (hp : p.Prime) (hpW : p ≤ B.sampleData.W)
    (m : B.sampleData.Sample) :
    B.markedValuation p m =
      B.headFunctionScore
        (fun h ↦ ((B.sampleData.pattern h).exponent p : ℝ)) m := by
  have hmem : p ∈
      (B.sampleData.pattern (B.sampleData.cellOf m).1).primes :=
    (hhead (B.sampleData.cellOf m).1 p).2 ⟨hp, hpW⟩
  have hmatch := B.sampleData.value_matches_head m p hmem
  unfold markedValuation headFunctionScore ArithmeticModel.valuation
  simpa only using congrArg (fun k : ℕ ↦ (k : ℝ)) hmatch

/-- The nonlinear bridge preserves every fixed head-prime valuation moment
exactly because all head-tag moments are frozen coordinates. -/
theorem endpoint_preserves_headPrimeMarkedValuation
    [Nonempty Head]
    (hhead : ∀ h : Head, ∀ r : ℕ,
      r ∈ (B.sampleData.pattern h).primes ↔
        r.Prime ∧ r ≤ B.sampleData.W)
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (hendpoint : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta)
    {p : ℕ} (hp : p.Prime) (hpW : p ≤ B.sampleData.W) :
    B.paperMoment (B.markedValuation p) xi1 =
      B.paperMoment (B.markedValuation p) xi0 := by
  let phi : Head → ℝ := fun h ↦
    ((B.sampleData.pattern h).exponent p : ℝ)
  have hpoint : B.markedValuation p = B.headFunctionScore phi := by
    funext m
    exact B.markedValuation_eq_headFunctionScore_of_exactHeadPrimes
      hhead hp hpW m
  rw [hpoint]
  exact B.endpoint_preserves_headFunction Delta xi0 xi1 hendpoint phi

/-- Endpoint preservation can also be read directly from the individual
head-indicator moment equations emitted by the Proposition 8.7 assembly. -/
theorem paperMoment_headFunction_eq_of_headIndicatorMoments
    [Nonempty Head]
    (phi : Head → ℝ) (xi0 xi1 : B.ParamSpace)
    (hheads : ∀ h : B.HeadIndex,
      B.paperMoment (B.headIndicator h.1) xi1 =
        B.paperMoment (B.headIndicator h.1) xi0) :
    B.paperMoment (B.headFunctionScore phi) xi1 =
      B.paperMoment (B.headFunctionScore phi) xi0 := by
  have hexpand (xi : B.ParamSpace) :
      B.paperMoment (B.headFunctionScore phi) xi =
        B.q * phi B.referenceHead +
          ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) *
              B.paperMoment (B.headIndicator h.1) xi := by
    calc
      B.paperMoment (B.headFunctionScore phi) xi =
          B.paperMoment (fun m ↦ phi B.referenceHead +
            ∑ h : B.HeadIndex,
              (phi h.1 - phi B.referenceHead) *
                B.headIndicator h.1 m) xi := by
            congr 1
            funext m
            exact B.headFunctionScore_decomposition phi m
      _ = B.paperMoment (fun _ ↦ phi B.referenceHead) xi +
          B.paperMoment (fun m ↦ ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) *
              B.headIndicator h.1 m) xi := by
            unfold paperMoment FiniteExponentialFamily.moment
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro m hm
            ring
      _ = B.q * phi B.referenceHead +
          ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) *
              B.paperMoment (B.headIndicator h.1) xi := by
            rw [B.paperMoment_const, B.paperMoment_fintype_sum]
            apply congrArg₂ (· + ·) rfl
            apply Finset.sum_congr rfl
            intro h hh
            exact B.paperMoment_const_mul
              (phi h.1 - phi B.referenceHead)
              (B.headIndicator h.1) xi
  rw [hexpand, hexpand]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro h hh
  rw [hheads h]

/-- The fixed-head valuation conclusion can therefore be appended to the
literal path conclusion of the finite ODE assembly without reconstructing
the hidden vector-moment endpoint. -/
theorem headPrimeMarkedMoment_eq_of_headIndicatorMoments
    [Nonempty Head]
    (hhead : ∀ h : Head, ∀ r : ℕ,
      r ∈ (B.sampleData.pattern h).primes ↔
        r.Prime ∧ r ≤ B.sampleData.W)
    (xi0 xi1 : B.ParamSpace)
    (hheads : ∀ h : B.HeadIndex,
      B.paperMoment (B.headIndicator h.1) xi1 =
        B.paperMoment (B.headIndicator h.1) xi0)
    {p : ℕ} (hp : p.Prime) (hpW : p ≤ B.sampleData.W) :
    B.paperMoment (B.markedValuation p) xi1 =
      B.paperMoment (B.markedValuation p) xi0 := by
  let phi : Head → ℝ := fun h ↦
    ((B.sampleData.pattern h).exponent p : ℝ)
  have hpoint : B.markedValuation p = B.headFunctionScore phi := by
    funext m
    exact B.markedValuation_eq_headFunctionScore_of_exactHeadPrimes
      hhead hp hpW m
  rw [hpoint]
  exact B.paperMoment_headFunction_eq_of_headIndicatorMoments
    phi xi0 xi1 hheads

/-- Each nonreference centered head coordinate has zero covariance with the
exact inverse-Jacobian vector field, since the paper target has zero head
coordinates. -/
theorem covariance_centeredHeadScore_vectorField_eq_zero
    [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : B.vectorFamily.HasCovarianceGap gamma xi)
    (h : B.HeadIndex) :
    B.vectorFamily.scalarFamily.covariance
        (B.centeredHeadScore h)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta) xi)) xi = 0 := by
  let x : B.ParamSpace :=
    EuclideanSpace.single (MomentCoord.head h) (1 : ℝ)
  have hi := B.inner_covarianceOperator xi x
    (B.vectorFamily.vectorField (B.targetVector Delta) xi)
  rw [B.covarianceOperator_vectorField xi Delta hgamma hgap] at hi
  simpa only [x, EuclideanSpace.inner_single_left,
    B.normalizedTarget_apply, unscaledTarget, coordScale, div_one,
    zero_mul, mul_zero, B.statistic_apply, rawStatistic,
    FiniteExponentialFamily.score,
    VectorExponentialFamily.scalarFamily,
    innerSL_apply_apply, map_one, one_mul, real_inner_comm] using hi.symm

/-- Consequently every fixed head-prime marked row is identically zero on
the whole covariance-gap box.  This is stronger than a `C / p` bound. -/
theorem covariance_headPrimeMarkedValuation_vectorField_eq_zero
    [Nonempty Head]
    (hhead : ∀ h : Head, ∀ r : ℕ,
      r ∈ (B.sampleData.pattern h).primes ↔
        r.Prime ∧ r ≤ B.sampleData.W)
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : B.vectorFamily.HasCovarianceGap gamma xi)
    {p : ℕ} (hp : p.Prime) (hpW : p ≤ B.sampleData.W) :
    B.vectorFamily.scalarFamily.covariance
        (B.markedValuation p)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta) xi)) xi = 0 := by
  let phi : Head → ℝ := fun h ↦
    ((B.sampleData.pattern h).exponent p : ℝ)
  let Y : B.sampleData.Sample → ℝ := fun m ↦
    B.vectorFamily.scalarFamily.score m
      (B.vectorFamily.vectorField (B.targetVector Delta) xi)
  let cphi : ℝ := phi B.referenceHead +
    ∑ h : B.HeadIndex,
      (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1
  have hpoint : B.markedValuation p = B.headFunctionScore phi := by
    funext m
    exact B.markedValuation_eq_headFunctionScore_of_exactHeadPrimes
      hhead hp hpW m
  rw [hpoint]
  have hdecomp : B.headFunctionScore phi = fun m ↦
      cphi +
        ∑ h : B.HeadIndex,
          (phi h.1 - phi B.referenceHead) *
            B.centeredHeadScore h m := by
    funext m
    rw [B.headFunctionScore_decomposition phi m]
    dsimp only [cphi]
    rw [add_assoc]
    apply congrArg (fun r : ℝ ↦ phi B.referenceHead + r)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    unfold centeredHeadScore
    ring
  rw [hdecomp]
  let mu : FiniteProbability B.sampleData.Sample := B.tiltedLaw xi
  change mu.covariance
      (fun m ↦ cphi +
        ∑ h : B.HeadIndex,
          (phi h.1 - phi B.referenceHead) *
            B.centeredHeadScore h m) Y = 0
  rw [mu.covariance_add_left]
  have hconst : mu.covariance (fun _ ↦ cphi) Y = 0 := by
    unfold FiniteProbability.covariance
    have hexpect : mu.expect (fun _ ↦ cphi) = cphi := by
      unfold FiniteProbability.expect
      rw [← Finset.sum_mul, mu.mass_sum]
      ring
    rw [show (fun omega ↦ cphi * Y omega) =
        (fun omega ↦ cphi * Y omega) by rfl,
      mu.expect_smul, hexpect]
    ring
  rw [hconst, zero_add]
  rw [mu.covariance_sum_left]
  apply Finset.sum_eq_zero
  intro h hh
  rw [mu.covariance_smul_left]
  have hz := B.covariance_centeredHeadScore_vectorField_eq_zero
    xi Delta hgamma hgap h
  simpa only [Y, mul_zero] using congrArg
    (fun r : ℝ ↦ (phi h.1 - phi B.referenceHead) * r) hz


end BridgeData

end

end Erdos390.Full.PaperBridgeFit
