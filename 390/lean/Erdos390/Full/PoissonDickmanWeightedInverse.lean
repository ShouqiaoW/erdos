import Erdos390.Full.PoissonDickmanDirichlet

/-!
# A deterministic weighted `L∞` quotient inverse

After writing the Poisson--Dickman test as `f(t)=t q(t)`, the covariance
operator is a nonlocal graph Laplacian with continuous edge kernel
`-K(s,t)/s`.  Strict Dickman log-concavity makes this edge kernel uniformly
positive when the second endpoint ranges in one fixed interior interval,
including at the removable axis `s=0`.  A maximum/minimum argument then
controls the oscillation of `q` directly.  This gives the weighted quotient
inverse without assuming Fredholm theory or an inverse theorem.
-/

open Set

noncomputable section

set_option maxHeartbeats 800000

namespace Erdos390.Full.PoissonDickmanWeightedInverse

open MeasureTheory
open DickmanBasic ConditionedPoissonLimit PoissonDickmanDirichlet

lemma FdifferenceQuotient_zero_right {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) :
    FdifferenceQuotient a 0 = deriv F a := by
  unfold FdifferenceQuotient
  have ha2 : a ∈ Icc (0 : ℝ) 2 := ⟨ha.1, ha.2.trans (by norm_num)⟩
  simp only [mul_zero, add_zero]
  rw [derivFExtension_eq_deriv_of_mem ha2]
  simp

/-- The derivative of the normalized Dickman translate is its value times
the Dickman logarithmic slope. -/
lemma deriv_F_eq_mul_dickmanLogSlope {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv F x = F x * dickmanLogSlope (U - x) := by
  have hu1 : 1 < U - x := by norm_num [U] at hx ⊢; linarith [hx.2]
  have hu6 : U - x ≤ 6 := by norm_num [U] at hx ⊢; linarith [hx.1]
  have hinner : HasDerivAt (fun z : ℝ => U - z) (-1) x := by
    simpa using (hasDerivAt_const x U).sub (hasDerivAt_id x)
  have hcomp := (hasDerivAt_rho hu1 hu6).comp x hinner
  have hdiv := hcomp.div_const (rho U)
  have hU : rho U ≠ 0 := ne_of_gt rho_U_pos
  have hFderiv : HasDerivAt F
      (-rho (U - x - 1) / (U - x) * -1 / rho U) x := by
    simpa [F, Function.comp_def] using hdiv
  rw [hFderiv.deriv]
  unfold F dickmanLogSlope
  have hUx0 : 0 < U - x := by linarith
  have hUx5 : U - x < 5 := by
    norm_num [U] at hx ⊢
    linarith [hx.1]
  have hRho : rho (U - x) ≠ 0 :=
    ne_of_gt (rho_pos_on_zero_five hUx0.le hUx5.le)
  field_simp [hU, ne_of_gt hUx0, hRho]

lemma covarianceKernelQuotient_axis_formula {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    covarianceKernelQuotient t 0 =
      F t * (dickmanLogSlope (U - t) - dickmanLogSlope U) := by
  unfold covarianceKernelQuotient
  rw [FdifferenceQuotient_zero_right ht,
    FdifferenceQuotient_zero_right (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num),
    deriv_F_eq_mul_dickmanLogSlope ht,
    deriv_F_eq_mul_dickmanLogSlope
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)]
  simp only [F_zero, one_mul]
  ring

/-- Strict negativity survives at the removable `s=0` axis. -/
theorem covarianceKernelQuotient_axis_neg {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    covarianceKernelQuotient t 0 < 0 := by
  have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  rw [covarianceKernelQuotient_axis_formula htcc]
  have hUt : U - t ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    norm_num [U] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hU : U ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by norm_num [U]
  have hslope : dickmanLogSlope (U - t) < dickmanLogSlope U :=
    strictMonoOn_dickmanLogSlope_one_nine_halves hUt hU (by linarith [ht.1])
  exact mul_neg_of_pos_of_neg
    (F_pos ⟨htcc.1, htcc.2.trans (by norm_num)⟩)
    (sub_neg.mpr hslope)

/-! The strict four-point inequality with one endpoint allowed to equal one.
The proof repeats the already audited shifted-slope integral argument, but
uses only positivity (not strict upper bounds) for the endpoints. -/

private lemma slopeIntegral_shift_lt_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x in (U - s - t)..(U - s), dickmanLogSlope x) <
      ∫ x in (U - t)..U, dickmanLogSlope x := by
  have hab : U - s - t < U - s := by linarith [ht.1]
  have hxmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.2, ht.2, hx.1]
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.1, hx.2]
  have hxsmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x + s ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [ht.2, hx.1]
    · norm_num [U] at hs hx ⊢
      linarith [hs.2, hx.2]
  have hcont₁ : ContinuousOn dickmanLogSlope (Icc (U - s - t) (U - s)) :=
    continuousOn_dickmanLogSlope_one_to_nine_halves.mono hxmem
  have hcont₂ : ContinuousOn (fun x : ℝ => dickmanLogSlope (x + s))
      (Icc (U - s - t) (U - s)) := by
    apply continuousOn_dickmanLogSlope_one_to_nine_halves.comp
      (continuous_id.add continuous_const).continuousOn
    exact hxsmem
  have hle : ∀ x ∈ Ioc (U - s - t) (U - s),
      dickmanLogSlope x ≤ dickmanLogSlope (x + s) := by
    intro x hx
    apply strictMonoOn_dickmanLogSlope_one_nine_halves.monotoneOn
    · exact hxmem x ⟨hx.1.le, hx.2⟩
    · exact hxsmem x ⟨hx.1.le, hx.2⟩
    · linarith [hs.1]
  have hexists : ∃ c ∈ Icc (U - s - t) (U - s),
      dickmanLogSlope c < dickmanLogSlope (c + s) := by
    refine ⟨U - s - t, left_mem_Icc.mpr hab.le, ?_⟩
    apply strictMonoOn_dickmanLogSlope_one_nine_halves
    · exact hxmem _ (left_mem_Icc.mpr hab.le)
    · exact hxsmem _ (left_mem_Icc.mpr hab.le)
    · linarith [hs.1]
  have hint := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab hcont₁ hcont₂ hle hexists
  rw [intervalIntegral.integral_comp_add_right] at hint
  convert hint using 1
  all_goals ring

lemma log_rho_four_point_lt_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Real.log (rho (U - s - t)) + Real.log (rho U) <
      Real.log (rho (U - s)) + Real.log (rho (U - t)) := by
  have h₁ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - s - t) (b := U - s)
    (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
    (by linarith [ht.1])
    (by norm_num [U] at hs ⊢; linarith [hs.1])
  have h₂ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - t) (b := U)
    (by norm_num [U] at ht ⊢; linarith [ht.2])
    (by linarith [ht.1]) (by norm_num [U])
  have hint := slopeIntegral_shift_lt_closed hs ht
  linarith

lemma rho_four_point_lt_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    rho (U - s - t) * rho U < rho (U - s) * rho (U - t) := by
  have ha : 0 < rho (U - s - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
      (by norm_num [U] at hs ht ⊢; linarith [hs.1, ht.1])
  have hb : 0 < rho U := rho_U_pos
  have hc : 0 < rho (U - s) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ⊢; linarith [hs.2])
      (by norm_num [U] at hs ⊢; linarith [hs.1])
  have hd : 0 < rho (U - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at ht ⊢; linarith [ht.2])
      (by norm_num [U] at ht ⊢; linarith [ht.1])
  have h := Real.exp_lt_exp.mpr (log_rho_four_point_lt_closed hs ht)
  rw [Real.exp_add, Real.exp_add, Real.exp_log ha, Real.exp_log hb,
    Real.exp_log hc, Real.exp_log hd] at h
  exact h

theorem covarianceKernel_neg_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    covarianceKernel s t < 0 := by
  have hprod := rho_four_point_lt_closed hs ht
  have hU : 0 < rho U := rho_U_pos
  have hden : 0 < rho U * rho U := mul_pos hU hU
  have hscaled := (div_lt_div_iff_of_pos_right hden).2 hprod
  unfold covarianceKernel F
  apply sub_neg.mpr
  calc
    rho (U - (s + t)) / rho U =
        (rho (U - s - t) * rho U) / (rho U * rho U) := by
      rw [show U - (s + t) = U - s - t by ring]
      field_simp [ne_of_gt hU]
    _ < (rho (U - s) * rho (U - t)) / (rho U * rho U) := hscaled
    _ = rho (U - s) / rho U * (rho (U - t) / rho U) := by
      field_simp [ne_of_gt hU]

/-- The transposed removable quotient is strictly negative for every first
coordinate, including both boundary points, once the second coordinate is
interior. -/
theorem covarianceKernelQuotient_transpose_neg {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    covarianceKernelQuotient t s < 0 := by
  by_cases hs0 : s = 0
  · subst s
    exact covarianceKernelQuotient_axis_neg ht
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hkernel : covarianceKernel t s < 0 :=
      covarianceKernel_neg_closed
        ⟨ht.1, ht.2.le⟩ ⟨hspos, hs.2⟩
    have hmul := mul_covarianceKernelQuotient_eq_kernel
      (s := t) (t := s) ⟨ht.1.le, ht.2.le⟩ hs
    nlinarith

/-- Compactness upgrades strict negativity to one uniform edge-weight lower
bound.  The first coordinate includes the moving-low axis. -/
theorem exists_transposeQuotient_uniform_gap {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s := by
  let S : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) 1 ×ˢ Icc epsilon (1 - epsilon)
  have hnonempty : S.Nonempty := by
    exact ⟨(0, epsilon), by constructor <;> constructor <;> linarith⟩
  have hcompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun z : ℝ × ℝ => -covarianceKernelQuotient z.2 z.1) S :=
    (continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)).neg.continuousOn
  obtain ⟨z, hzS, hzmin⟩ := hcompact.exists_isMinOn hnonempty hcont
  let kappa := -covarianceKernelQuotient z.2 z.1
  have hzt : z.2 ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨hepsilon.trans_le hzS.2.1, by linarith [hzS.2.2, hepsilon]⟩
  have hkappa : 0 < kappa := by
    dsimp only [kappa]
    exact neg_pos.mpr (covarianceKernelQuotient_transpose_neg hzS.1 hzt)
  refine ⟨kappa, hkappa, ?_⟩
  intro s hs t ht
  change -covarianceKernelQuotient z.2 z.1 ≤
    -covarianceKernelQuotient t s
  exact hzmin (show (s, t) ∈ S by exact ⟨hs, ht⟩)

/-! ## The weighted operator as a graph Laplacian -/

/-- The covariance operator after the isometry `f(t)=t q(t)`, divided by
the output coordinate. -/
def weightedCovarianceOperator (q : ℝ → ℝ) (s : ℝ) : ℝ :=
  F s * q s +
    ∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s * q t

private lemma continuous_weightedKernelIntegral (q : ℝ → ℝ)
    (hq : Continuous q) :
    Continuous (fun s : ℝ =>
      ∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s * q t) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := (0 : ℝ)) (b₀ := 1)
  exact (continuous_uncurry_covarianceKernelQuotient.comp
    (continuous_snd.prodMk continuous_fst)).mul (hq.comp continuous_snd)

theorem continuous_weightedCovarianceOperator (q : ℝ → ℝ)
    (hq : Continuous q) :
    Continuous (weightedCovarianceOperator q) := by
  unfold weightedCovarianceOperator
  exact (continuous_F.mul hq).add (continuous_weightedKernelIntegral q hq)

theorem covarianceKernelQuotient_transpose_nonpos {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    covarianceKernelQuotient t s ≤ 0 := by
  by_cases hs0 : s = 0
  · subst s
    rw [covarianceKernelQuotient_axis_formula ht]
    have hUt : U - t ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
      norm_num [U] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have hU : U ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by norm_num [U]
    have hslope : dickmanLogSlope (U - t) ≤ dickmanLogSlope U :=
      strictMonoOn_dickmanLogSlope_one_nine_halves.monotoneOn
        hUt hU (by linarith [ht.1])
    exact mul_nonpos_of_nonneg_of_nonpos
      (F_pos ⟨ht.1, ht.2.trans (by norm_num)⟩).le
      (sub_nonpos.mpr hslope)
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hkernel : covarianceKernel t s ≤ 0 :=
      covarianceKernel_nonpos ht hs
    have hmul := mul_covarianceKernelQuotient_eq_kernel
      (s := t) (t := s) ht hs
    nlinarith

/-- The removable row-sum identity, including the axis by continuity. -/
theorem weightedKernel_rowSum (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    F s + (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s) = 0 := by
  let R : ℝ → ℝ := fun u =>
    F u + ∫ t in (0 : ℝ)..1, covarianceKernelQuotient t u
  have hRcont : Continuous R := by
    dsimp only [R]
    apply continuous_F.add
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
    exact continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)
  have hzero : Ioc (0 : ℝ) 1 ⊆ R ⁻¹' ({0} : Set ℝ) := by
    intro u hu
    have hucc : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
    have hu0 : u ≠ 0 := ne_of_gt hu.1
    change R u = 0
    dsimp only [R]
    have hInt :
        (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t u) =
          (∫ t in (0 : ℝ)..1, covarianceKernel u t) / u := by
      calc
        (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t u) =
            ∫ t in (0 : ℝ)..1, covarianceKernel u t / u := by
          apply intervalIntegral.integral_congr
          intro t ht
          have htcc : t ∈ Icc (0 : ℝ) 1 := by
            simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
          change covarianceKernelQuotient t u = covarianceKernel u t / u
          rw [covarianceKernelQuotient_eq_div htcc hucc hu0,
            covarianceKernel_comm]
        _ = (∫ t in (0 : ℝ)..1, covarianceKernel u t) / u := by
          rw [intervalIntegral.integral_div]
    rw [hInt, integral_covarianceKernel u hucc]
    field_simp [hu0]
    ring
  have hclosed : IsClosed (R ⁻¹' ({0} : Set ℝ)) :=
    isClosed_singleton.preimage hRcont
  have hclosure := closure_minimal hzero hclosed
  rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)] at hclosure
  exact hclosure hs

/-- Exact graph-Laplacian representation. -/
theorem weightedCovarianceOperator_eq_edgeIntegral
    (q : ℝ → ℝ) (hq : Continuous q)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    weightedCovarianceOperator q s =
      ∫ t in (0 : ℝ)..1,
        (-covarianceKernelQuotient t s) * (q s - q t) := by
  have hrow := weightedKernel_rowSum s hs
  have hFrow : F s =
      -(∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s) := by
    linarith
  unfold weightedCovarianceOperator
  calc
    F s * q s +
        (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s * q t) =
      q s * (-(∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s)) +
        (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s * q t) := by
      rw [hFrow]
      ring
    _ = (∫ t in (0 : ℝ)..1,
        (-covarianceKernelQuotient t s) * q s) +
        (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s * q t) := by
      congr 1
      calc
        q s * (-(∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s)) =
            (-q s) * (∫ t in (0 : ℝ)..1,
              covarianceKernelQuotient t s) := by ring
        _ = ∫ t in (0 : ℝ)..1,
            (-q s) * covarianceKernelQuotient t s := by
          rw [← intervalIntegral.integral_const_mul]
        _ = ∫ t in (0 : ℝ)..1,
            (-covarianceKernelQuotient t s) * q s := by
          apply intervalIntegral.integral_congr
          intro t ht
          ring
    _ = ∫ t in (0 : ℝ)..1,
        ((-covarianceKernelQuotient t s) * q s +
          covarianceKernelQuotient t s * q t) := by
      rw [intervalIntegral.integral_add]
      · exact (continuous_uncurry_covarianceKernelQuotient.comp
          (continuous_id.prodMk continuous_const)).neg.mul continuous_const
          |>.intervalIntegrable 0 1
      · exact (continuous_uncurry_covarianceKernelQuotient.comp
          (continuous_id.prodMk continuous_const)).mul
            hq |>.intervalIntegrable 0 1
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      ring

theorem weightedCovarianceOperator_neg (q : ℝ → ℝ) (s : ℝ) :
    weightedCovarianceOperator (fun t => -q t) s =
      -weightedCovarianceOperator q s := by
  unfold weightedCovarianceOperator
  have hintegrand :
      (fun t : ℝ => covarianceKernelQuotient t s * (-q t)) =
        fun t : ℝ => -(covarianceKernelQuotient t s * q t) := by
    funext t
    ring
  rw [hintegrand]
  rw [intervalIntegral.integral_neg]
  ring

/-- At a global maximum, the operator dominates the edge energy from any
fixed interior interval. -/
lemma interiorEdgeIntegral_le_operator_at_max
    {epsilon kappa : ℝ}
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc epsilon (1 - epsilon),
      kappa ≤ -covarianceKernelQuotient t s)
    (q : ℝ → ℝ) (hq : Continuous q)
    {smax : ℝ} (hsmax : smax ∈ Icc (0 : ℝ) 1)
    (hmax : ∀ t ∈ Icc (0 : ℝ) 1, q t ≤ q smax) :
    kappa * (∫ t in epsilon..(1 - epsilon), q smax - q t) ≤
      weightedCovarianceOperator q smax := by
  let a : ℝ := epsilon
  let b : ℝ := 1 - epsilon
  let G : ℝ → ℝ := fun t =>
    (-covarianceKernelQuotient t smax) * (q smax - q t)
  have h0a : 0 ≤ a := hepsilon.le
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hdiffCont : Continuous (fun t : ℝ => q smax - q t) :=
    continuous_const.sub hq
  have hGcont : Continuous G := by
    dsimp only [G]
    exact (continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_id.prodMk continuous_const)).neg.mul hdiffCont
  have hlocal :
      kappa * (∫ t in a..b, q smax - q t) ≤ ∫ t in a..b, G t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
      ((continuous_const.mul hdiffCont).intervalIntegrable a b)
      (hGcont.intervalIntegrable a b)
    intro t ht
    have hdiff : 0 ≤ q smax - q t := by
      apply sub_nonneg.mpr
      exact hmax t ⟨h0a.trans ht.1, ht.2.trans hb1⟩
    exact mul_le_mul_of_nonneg_right
      (hgap smax hsmax t (by simpa [a, b] using ht)) hdiff
  have hGnonneg :
      0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    exact mul_nonneg
      (neg_nonneg.mpr
        (covarianceKernelQuotient_transpose_nonpos hsmax htcc))
      (sub_nonneg.mpr (hmax t htcc))
  have hlocalFull : (∫ t in a..b, G t) ≤ ∫ t in (0 : ℝ)..1, G t :=
    intervalIntegral.integral_mono_interval h0a hab hb1 hGnonneg
      (hGcont.intervalIntegrable 0 1)
  rw [weightedCovarianceOperator_eq_edgeIntegral q hq smax hsmax]
  exact hlocal.trans hlocalFull

/-- The deterministic weighted `L∞` quotient inverse.  The constant is
selected solely from the Dickman kernel and the fixed interior interval;
no inverse, gap, mesh, or arithmetic hypothesis is supplied. -/
theorem exists_weighted_Linfty_quotient_bound {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ → ℝ, Continuous q →
      ∀ G : ℝ, 0 ≤ G →
      (∀ s ∈ Icc (0 : ℝ) 1,
        |weightedCovarianceOperator q s| ≤ G) →
      ∃ mu : ℝ, ∀ s ∈ Icc (0 : ℝ) 1,
        |q s - mu| ≤ C * G := by
  obtain ⟨kappa, hkappa, hgap⟩ :=
    exists_transposeQuotient_uniform_gap hepsilon hhalf
  let ell : ℝ := 1 - 2 * epsilon
  have hell : 0 < ell := by dsimp [ell]; linarith
  refine ⟨1 / (kappa * ell), by positivity, ?_⟩
  intro q hq G hG hbound
  obtain ⟨smax, hsmax, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (show (0 : ℝ) ≤ 1 by norm_num)) hq.continuousOn
  obtain ⟨smin, hsmin, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (show (0 : ℝ) ≤ 1 by norm_num)) hq.continuousOn
  have hmaxEdge := interiorEdgeIntegral_le_operator_at_max
    hepsilon hhalf hgap q hq hsmax hmax
  have hnegContinuous : Continuous (fun t => -q t) := hq.neg
  have hminAsMax : ∀ t ∈ Icc (0 : ℝ) 1, -q t ≤ -q smin := by
    intro t ht
    exact neg_le_neg (hmin ht)
  have hminEdgeRaw := interiorEdgeIntegral_le_operator_at_max
    hepsilon hhalf hgap (fun t => -q t) hnegContinuous hsmin hminAsMax
  rw [weightedCovarianceOperator_neg] at hminEdgeRaw
  have hminEdge :
      kappa * (∫ t in epsilon..(1 - epsilon), q t - q smin) ≤
        -weightedCovarianceOperator q smin := by
    convert hminEdgeRaw using 1
    apply congrArg (fun x : ℝ => kappa * x)
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hfirstInt : IntervalIntegrable (fun t : ℝ => q smax - q t)
      volume epsilon (1 - epsilon) :=
    (continuous_const.sub hq).intervalIntegrable _ _
  have hsecondInt : IntervalIntegrable (fun t : ℝ => q t - q smin)
      volume epsilon (1 - epsilon) :=
    (hq.sub continuous_const).intervalIntegrable _ _
  have hsumInt :
      (∫ t in epsilon..(1 - epsilon), q smax - q t) +
        (∫ t in epsilon..(1 - epsilon), q t - q smin) =
          ell * (q smax - q smin) := by
    rw [← intervalIntegral.integral_add hfirstInt hsecondInt]
    calc
      (∫ t in epsilon..(1 - epsilon),
          (q smax - q t) + (q t - q smin)) =
        ∫ t in epsilon..(1 - epsilon), q smax - q smin := by
          apply intervalIntegral.integral_congr
          intro t ht
          ring
      _ = ell * (q smax - q smin) := by
        simp [ell]
        ring
  have hoperatorSum :
      weightedCovarianceOperator q smax +
          (-weightedCovarianceOperator q smin) ≤ 2 * G := by
    have hmaxBound := hbound smax hsmax
    have hminBound := hbound smin hsmin
    have hmaxUpper : weightedCovarianceOperator q smax ≤ G :=
      (le_abs_self _).trans hmaxBound
    have hminUpper : -weightedCovarianceOperator q smin ≤ G :=
      (neg_le_abs _).trans hminBound
    linarith
  have hoscScaled :
      kappa * (ell * (q smax - q smin)) ≤ 2 * G := by
    calc
      kappa * (ell * (q smax - q smin)) =
          kappa * (∫ t in epsilon..(1 - epsilon), q smax - q t) +
            kappa * (∫ t in epsilon..(1 - epsilon), q t - q smin) := by
        rw [← hsumInt]
        ring
      _ ≤ weightedCovarianceOperator q smax +
          (-weightedCovarianceOperator q smin) :=
        add_le_add hmaxEdge hminEdge
      _ ≤ 2 * G := hoperatorSum
  have hden : 0 < kappa * ell := mul_pos hkappa hell
  have hosc : q smax - q smin ≤ 2 * G / (kappa * ell) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  refine ⟨(q smax + q smin) / 2, ?_⟩
  intro s hs
  have hsUpper := hmax hs
  have hsLower := hmin hs
  change q s ≤ q smax at hsUpper
  change q smin ≤ q s at hsLower
  have hCmul : (1 / (kappa * ell)) * G = G / (kappa * ell) := by
    rw [one_div, div_eq_mul_inv]
    ring
  rw [abs_le]
  rw [hCmul]
  constructor
  · have : -(G / (kappa * ell)) ≤
        q s - (q smax + q smin) / 2 := by
      have hhalfOsc : (q smax - q smin) / 2 ≤
          G / (kappa * ell) := by
        calc
          (q smax - q smin) / 2 ≤
              (2 * G / (kappa * ell)) / 2 := by linarith
          _ = G / (kappa * ell) := by ring
      linarith
    exact this
  · have : q s - (q smax + q smin) / 2 ≤
        G / (kappa * ell) := by
      have hhalfOsc : (q smax - q smin) / 2 ≤
          G / (kappa * ell) := by
        calc
          (q smax - q smin) / 2 ≤
              (2 * G / (kappa * ell)) / 2 := by linarith
          _ = G / (kappa * ell) := by ring
      linarith
    exact this

end Erdos390.Full.PoissonDickmanWeightedInverse
