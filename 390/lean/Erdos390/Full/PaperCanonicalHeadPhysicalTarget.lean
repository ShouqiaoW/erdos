import Erdos390.Full.PaperCanonicalBaselineBridge
import Erdos390.Full.PaperHeadSimplex

/-!
# The paper's explicit head simplex and physical interpolation

The head barycenter is not supplied as an arbitrary probability vector in
the paper.  Its nonzero-vertex coefficients are exactly `A_p / (E*q)` and
the zero-vertex coefficient is the remaining mass.  This file constructs
that literal vector from the finite reserve ledger and combines it with the
two fixed physical intervals around `mu`.
-/

open scoped BigOperators

namespace Erdos390.Full

open PaperGuardCensus PaperBridgeFit PaperHeadSimplex ArithmeticModel

noncomputable section

namespace PaperGuardCensus

/-- Explicit finite head-reserve data from the paper's simplex
`{0, E e_p : p in P}`.  The two margin fields are precisely the
coordinatewise reserve inequalities; no probability vector is stored. -/
structure HeadSimplexReserve (P : Finset ℕ) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  activeMass : ℝ
  activeMass_pos : 0 < activeMass
  target : {p : ℕ // p ∈ P} → ℝ
  margin : ℝ
  margin_pos : 0 < margin
  vertex_margin : ∀ p,
    margin ≤ target p / ((exponent : ℝ) * activeMass)
  zero_margin :
    margin ≤ 1 - ∑ p : {p : ℕ // p ∈ P},
      target p / ((exponent : ℝ) * activeMass)

namespace HeadSimplexReserve

variable {P : Finset ℕ} (R : HeadSimplexReserve P)

/-- Coefficient of the zero head vertex. -/
def zeroCoefficient : ℝ :=
  1 - ∑ p : {p : ℕ // p ∈ P},
    R.target p / ((R.exponent : ℝ) * R.activeMass)

/-- Literal barycentric coefficients on `0` and `E e_p`. -/
def beta : PaperHeadSimplex.Tag P → ℝ
  | none => R.zeroCoefficient
  | some p => R.target p / ((R.exponent : ℝ) * R.activeMass)

theorem zeroCoefficient_margin : R.margin ≤ R.zeroCoefficient := by
  exact R.zero_margin

theorem beta_margin (h : PaperHeadSimplex.Tag P) :
    R.margin ≤ R.beta h := by
  cases h with
  | none => exact R.zeroCoefficient_margin
  | some p => exact R.vertex_margin p

theorem beta_pos (h : PaperHeadSimplex.Tag P) : 0 < R.beta h :=
  R.margin_pos.trans_le (R.beta_margin h)

theorem beta_sum : ∑ h : PaperHeadSimplex.Tag P, R.beta h = 1 := by
  rw [Fintype.sum_option]
  simp only [beta, zeroCoefficient]
  ring

theorem exponent_cast_pos : 0 < (R.exponent : ℝ) := by
  exact_mod_cast R.exponent_pos

theorem exponent_activeMass_ne :
    (R.exponent : ℝ) * R.activeMass ≠ 0 :=
  ne_of_gt (mul_pos R.exponent_cast_pos R.activeMass_pos)

/-- The displayed barycenter has exactly the normalized target valuation at
each head prime. -/
theorem beta_exponent_moment (p : {p : ℕ // p ∈ P}) :
    ∑ h : PaperHeadSimplex.Tag P,
        R.beta h * (PaperHeadSimplex.exponent P R.exponent h p.1 : ℝ) =
      R.target p / R.activeMass := by
  rw [Fintype.sum_option]
  simp only [beta, PaperHeadSimplex.exponent_none, Nat.cast_zero,
    mul_zero, zero_add]
  rw [Finset.sum_eq_single p]
  · simp only [PaperHeadSimplex.exponent_some_self]
    field_simp [ne_of_gt R.exponent_cast_pos,
      ne_of_gt R.activeMass_pos]
  · intro q hq hqp
    have hval : p.1 ≠ q.1 := by
      intro h
      exact hqp (Subtype.ext h.symm)
    rw [PaperHeadSimplex.exponent_some_ne P R.exponent q p.1 hval]
    simp
  · intro hp
    exact (hp (Finset.mem_univ p)).elim

end HeadSimplexReserve

/-- The fixed interval inequalities used by the paper's two-pool
interpolation.  They state that the entire minus interval lies below
`mu-eta` and the entire plus interval lies above `mu+eta`. -/
structure PhysicalInterpolationTarget (I : PhysicalIntervals) where
  mu : ℝ
  eta : ℝ
  eta_pos : 0 < eta
  minus_below : Real.log (I.upper .minus) ≤ mu - eta
  plus_above : mu + eta ≤ Real.log (I.lower .plus)

namespace PhysicalInterpolationTarget

variable {I : PhysicalIntervals}

/-- A fixed upper bound for the difference of any two physical means in
the selected pools. -/
def physicalSpan (I : PhysicalIntervals) : ℝ :=
  Real.log (I.upper .plus) - Real.log (I.lower .minus)

theorem lower_minus_lt_upper_plus : I.lower .minus < I.upper .plus :=
  (I.lower_lt_upper .minus).trans
    (I.separated.trans (I.lower_lt_upper .plus))

theorem physicalSpan_pos : 0 < physicalSpan I := by
  unfold physicalSpan
  apply sub_pos.mpr
  exact Real.strictMonoOn_log (I.lower_pos .minus)
    ((I.lower_pos .plus).trans (I.lower_lt_upper .plus))
    lower_minus_lt_upper_plus

/-- Uniform physical splitting margin obtained only from the fixed endpoint
gap around `mu`. -/
def tau (K : PhysicalInterpolationTarget I) : ℝ :=
  K.eta / physicalSpan I

theorem tau_pos (K : PhysicalInterpolationTarget I) : 0 < K.tau :=
  div_pos K.eta_pos physicalSpan_pos

end PhysicalInterpolationTarget

end PaperGuardCensus

namespace PaperBridgeFit.BridgeData

variable {P : Finset ℕ} {Band : Type*}
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData (PaperHeadSimplex.Tag P) Band)

private theorem cellLogMean_le_log_upper
    (I : PhysicalIntervals)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (c : Cell (PaperHeadSimplex.Tag P)) :
    cellLogMean B.sampleData c ≤ Real.log (I.upper c.2) := by
  rw [← B.cellPhysicalMean_eq_cellLogMean c]
  apply B.cellPhysicalMean_le_of_cellwise c _
  intro m hm
  exact (B.physicalScore_le_log_upper I hhi m).trans_eq (by
    congr 1
    exact congrArg I.upper (congrArg Prod.snd hm))

private theorem log_lower_le_cellLogMean
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (c : Cell (PaperHeadSimplex.Tag P)) :
    Real.log (I.lower c.2) ≤ cellLogMean B.sampleData c := by
  rw [← B.cellPhysicalMean_eq_cellLogMean c]
  apply B.le_cellPhysicalMean_of_cellwise c _
  intro m hm
  exact (B.log_lower_lt_physicalScore I hlo m).le.trans_eq' (by
    congr 1
    exact congrArg I.lower (congrArg Prod.snd hm))

private theorem poolLogMean_le_log_upper
    (I : PhysicalIntervals)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (R : HeadSimplexReserve P) (sigma : PhysicalSign) :
    poolLogMean B.sampleData R.beta sigma ≤ Real.log (I.upper sigma) := by
  unfold poolLogMean
  calc
    (∑ h : PaperHeadSimplex.Tag P,
        R.beta h * cellLogMean B.sampleData (h, sigma)) ≤
        ∑ h : PaperHeadSimplex.Tag P,
          R.beta h * Real.log (I.upper sigma) := by
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_left
        (B.cellLogMean_le_log_upper I hhi (h, sigma))
        (R.beta_pos h).le
    _ = Real.log (I.upper sigma) := by
      rw [← Finset.sum_mul, R.beta_sum, one_mul]

private theorem log_lower_le_poolLogMean
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (R : HeadSimplexReserve P) (sigma : PhysicalSign) :
    Real.log (I.lower sigma) ≤
      poolLogMean B.sampleData R.beta sigma := by
  unfold poolLogMean
  calc
    Real.log (I.lower sigma) =
        ∑ h : PaperHeadSimplex.Tag P,
          R.beta h * Real.log (I.lower sigma) := by
      rw [← Finset.sum_mul, R.beta_sum, one_mul]
    _ ≤ ∑ h : PaperHeadSimplex.Tag P,
        R.beta h * cellLogMean B.sampleData (h, sigma) := by
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_left
        (B.log_lower_le_cellLogMean I hlo (h, sigma))
        (R.beta_pos h).le

/-- The exact `BarycentricTarget` derived from the paper's displayed head
coefficients and fixed two-pool endpoint inequalities. -/
def barycentricTargetOfPaperData
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (R : HeadSimplexReserve P)
    (K : PhysicalInterpolationTarget I) :
    BarycentricTarget B.sampleData where
  beta := R.beta
  beta_pos := R.beta_pos
  beta_sum := R.beta_sum
  betaFloor := R.margin
  betaFloor_pos := R.margin_pos
  betaFloor_le := R.beta_margin
  mu := K.mu
  tau := K.tau
  tau_pos := K.tau_pos
  pool_separated := by
    have hm := B.poolLogMean_le_log_upper I hhi R .minus
    have hp := B.log_lower_le_poolLogMean I hlo R .plus
    linarith [K.minus_below, K.plus_above, K.eta_pos]
  left_interior := by
    have hmUpper := B.poolLogMean_le_log_upper I hhi R .minus
    have hpUpper := B.poolLogMean_le_log_upper I hhi R .plus
    have hmLower := B.log_lower_le_poolLogMean I hlo R .minus
    have hspan :
        poolLogMean B.sampleData R.beta .plus -
            poolLogMean B.sampleData R.beta .minus ≤
              PhysicalInterpolationTarget.physicalSpan I := by
      unfold PhysicalInterpolationTarget.physicalSpan
      linarith
    have hscaled : K.tau *
        (poolLogMean B.sampleData R.beta .plus -
          poolLogMean B.sampleData R.beta .minus) ≤ K.eta := by
      unfold PhysicalInterpolationTarget.tau
      rw [div_mul_eq_mul_div,
        div_le_iff₀ PhysicalInterpolationTarget.physicalSpan_pos]
      nlinarith [K.eta_pos.le]
    exact hscaled.trans (by linarith [K.minus_below])
  right_interior := by
    have hpUpper := B.poolLogMean_le_log_upper I hhi R .plus
    have hmLower := B.log_lower_le_poolLogMean I hlo R .minus
    have hpLower := B.log_lower_le_poolLogMean I hlo R .plus
    have hspan :
        poolLogMean B.sampleData R.beta .plus -
            poolLogMean B.sampleData R.beta .minus ≤
              PhysicalInterpolationTarget.physicalSpan I := by
      unfold PhysicalInterpolationTarget.physicalSpan
      linarith
    have hscaled : K.tau *
        (poolLogMean B.sampleData R.beta .plus -
          poolLogMean B.sampleData R.beta .minus) ≤ K.eta := by
      unfold PhysicalInterpolationTarget.tau
      rw [div_mul_eq_mul_div,
        div_le_iff₀ PhysicalInterpolationTarget.physicalSpan_pos]
      nlinarith [K.eta_pos.le]
    exact hscaled.trans (by linarith [K.plus_above])

/-- The canonical baseline obtained from the paper data realizes every
displayed normalized head valuation exactly. -/
theorem barycentricTargetOfPaperData_headExponentMoment
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (R : HeadSimplexReserve P)
    (K : PhysicalInterpolationTarget I)
    (p : {p : ℕ // p ∈ P}) :
    let T := B.barycentricTargetOfPaperData I hlo hhi R K
    ∑ c : Cell (PaperHeadSimplex.Tag P),
        T.baseline.normalizedCellMass c *
          (PaperHeadSimplex.exponent P R.exponent c.1 p.1 : ℝ) =
      R.target p / R.activeMass := by
  dsimp only
  let T := B.barycentricTargetOfPaperData I hlo hhi R K
  calc
    (∑ c : Cell (PaperHeadSimplex.Tag P),
        T.baseline.normalizedCellMass c *
          (PaperHeadSimplex.exponent P R.exponent c.1 p.1 : ℝ)) =
        ∑ h : PaperHeadSimplex.Tag P, T.beta h *
          (PaperHeadSimplex.exponent P R.exponent h p.1 : ℝ) :=
      T.headMoment (fun h : PaperHeadSimplex.Tag P ↦
        (PaperHeadSimplex.exponent P R.exponent h p.1 : ℝ))
    _ = R.target p / R.activeMass := by
      change (∑ h : PaperHeadSimplex.Tag P, R.beta h *
        (PaperHeadSimplex.exponent P R.exponent h p.1 : ℝ)) = _
      exact R.beta_exponent_moment p

/-- The common normalized cell-mass margin is the product of the explicit
head-reserve margin and the fixed physical interpolation margin. -/
theorem barycentricTargetOfPaperData_cellMassMargin
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (R : HeadSimplexReserve P)
    (K : PhysicalInterpolationTarget I) :
    (B.barycentricTargetOfPaperData I hlo hhi R K).cellMassMargin =
      R.margin * K.tau := rfl

/-- After installing the explicitly constructed baseline in `BridgeData`,
the actual finite bridge moment at zero equals the paper's chosen `mu`. -/
theorem paperMoment_physicalScore_zero_eq_mu_ofPaperData
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (R : HeadSimplexReserve P)
    (K : PhysicalInterpolationTarget I)
    (hbaseline : B.baseline =
      (B.barycentricTargetOfPaperData I hlo hhi R K).baseline) :
    B.paperMoment B.physicalScore 0 = K.mu := by
  exact B.paperMoment_physicalScore_zero_eq_mu
    (B.barycentricTargetOfPaperData I hlo hhi R K) hbaseline

end PaperBridgeFit.BridgeData

end

end Erdos390.Full
