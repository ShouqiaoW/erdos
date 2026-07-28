import Erdos390.Full.PaperProposition87LiteralBandBalance
import Erdos390.Full.PaperCanonicalActiveMassBaseline

/-!
# Homogeneous active-mass transport for Proposition 8.7

The canonical covariance argument is an argument about the normalized cell
law.  The literal bridge, however, has total active mass `q_n`, not one.
This file makes the homogeneity exact without changing any of the existing
Proposition 8.7 interfaces.

For a bridge whose baseline is `T.activeMassBaseline q hq`, we form the
mass-one companion with the same sample, partition, gauge, reference head,
and scale, and with baseline `T.baseline`.  We prove that

* the two tilted probability laws and normalized covariances agree;
* every active weight and raw paper moment for the literal bridge is `q`
  times its companion value;
* after dividing the requested raw moment increment by `q`, the two ODE
  vector fields agree exactly, including at points where the globally
  defined inverse is the zero fallback; and
* a companion Proposition 8.7 path therefore transports to a literal
  `q`-mass path.  Feasibility is proved afresh with the literal frozen and
  active ledgers, so protected frozen mass may overlap an active coordinate.

No equality between the literal baseline and the old mass-one baseline is
assumed.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The mass-one companion of a literal active-mass bridge.  All arithmetic,
gauge, and scale data are retained definitionally; only the baseline is
replaced by the canonical probability allocation. -/
def normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) : BridgeData Head Band where
  sampleData := B.sampleData
  baseline := T.baseline
  partition := B.partition
  lowBand := B.lowBand
  referenceHead := B.referenceHead
  w := B.w
  w_pos := B.w_pos
  n_gt_one := B.n_gt_one

@[simp] theorem normalizedLawCompanion_sampleData
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).sampleData = B.sampleData :=
  rfl

@[simp] theorem normalizedLawCompanion_baseline
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).baseline = T.baseline :=
  rfl

@[simp] theorem normalizedLawCompanion_partition
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).partition = B.partition :=
  rfl

@[simp] theorem normalizedLawCompanion_lowBand
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).lowBand = B.lowBand :=
  rfl

@[simp] theorem normalizedLawCompanion_referenceHead
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).referenceHead = B.referenceHead :=
  rfl

@[simp] theorem normalizedLawCompanion_w
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).w = B.w :=
  rfl

@[simp] theorem normalizedLawCompanion_L
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).L = B.L :=
  rfl

@[simp] theorem normalizedLawCompanion_q [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).q = 1 := by
  exact T.baseline_totalMass

/-- Literal coordinate weights are exactly `q` times the mass-one companion
weights. -/
theorem baseWeight_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (m : B.sampleData.Sample) :
    B.baseline.baseWeight m =
      q * (B.normalizedLawCompanion T).baseline.baseWeight m := by
  rw [hbaseline, T.activeMassBaseline_baseWeight q hq]
  rfl

/-- The centered head statistics agree because scaling does not change the
normalized cell law. -/
theorem headBaselineMass_eq_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq) (h : Head) :
    B.headBaselineMass h =
      (B.normalizedLawCompanion T).headBaselineMass h := by
  unfold headBaselineMass normalizedLawCompanion
  rw [hbaseline]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [T.activeMassBaseline_normalizedCellMass q hq,
    T.baseline_normalizedCellMass]

/-- The full statistic vector is unchanged by active-mass scaling. -/
theorem statistic_eq_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (m : B.sampleData.Sample) :
    B.statistic m = (B.normalizedLawCompanion T).statistic m := by
  apply (EuclideanSpace.equiv B.Coord Real).injective
  funext c
  change B.statistic m c = (B.normalizedLawCompanion T).statistic m c
  rw [B.statistic_apply,
    (B.normalizedLawCompanion T).statistic_apply]
  cases c with
  | gauge j => rfl
  | physical => rfl
  | head h =>
      change
        (B.headIndicator h.1 m - B.headBaselineMass h.1) / 1 =
          (B.headIndicator h.1 m -
            (B.normalizedLawCompanion T).headBaselineMass h.1) / 1
      rw [B.headBaselineMass_eq_normalizedLawCompanion
        T q hq hbaseline h.1]
  | slow => rfl

/-- Unnormalized tilted weights scale by `q`. -/
theorem unnormalizedWeight_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.unnormalizedWeight xi m =
      q * (B.normalizedLawCompanion T).vectorFamily.scalarFamily.unnormalizedWeight
        xi m := by
  have hbase :
      B.vectorFamily.scalarFamily.baseWeight m =
        q * (B.normalizedLawCompanion T).vectorFamily.scalarFamily.baseWeight m := by
    change B.baseline.baseWeight m =
      q * (B.normalizedLawCompanion T).baseline.baseWeight m
    exact B.baseWeight_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline m
  have hscore :
      B.vectorFamily.scalarFamily.score m xi =
        (B.normalizedLawCompanion T).vectorFamily.scalarFamily.score m xi := by
    change (innerSL ℝ) (B.statistic m) xi =
      (innerSL ℝ) ((B.normalizedLawCompanion T).statistic m) xi
    rw [B.statistic_eq_normalizedLawCompanion T q hq hbaseline m]
    rfl
  have hscale :
      B.vectorFamily.scalarFamily.scale =
        (B.normalizedLawCompanion T).vectorFamily.scalarFamily.scale := by
    change B.L = (B.normalizedLawCompanion T).L
    exact (B.normalizedLawCompanion_L T).symm
  unfold FiniteExponentialFamily.unnormalizedWeight
  rw [hbase, hscore, hscale]
  ring

/-- Partition functions scale by `q`. -/
theorem partition_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) :
    B.vectorFamily.scalarFamily.partition xi =
      q * (B.normalizedLawCompanion T).vectorFamily.scalarFamily.partition xi := by
  unfold FiniteExponentialFamily.partition
  simp_rw [B.unnormalizedWeight_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline xi]
  rw [Finset.mul_sum]
  rfl

/-- The tilted probability mass is independent of the literal active mass. -/
theorem probabilityMass_eq_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.probabilityMass xi m =
      (B.normalizedLawCompanion T).vectorFamily.scalarFamily.probabilityMass
        xi m := by
  have hpartition :
      (B.normalizedLawCompanion T).vectorFamily.scalarFamily.partition xi ≠ 0 :=
    (B.normalizedLawCompanion T).vectorFamily.scalarFamily.partition_ne_zero xi
  unfold FiniteExponentialFamily.probabilityMass
  rw [B.unnormalizedWeight_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline xi m,
    B.partition_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline xi]
  field_simp [ne_of_gt hq, hpartition]

/-- Normalized scalar covariance is unchanged by active-mass scaling. -/
theorem covariance_eq_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (F G : B.sampleData.Sample -> Real) (xi : B.ParamSpace) :
    B.vectorFamily.scalarFamily.covariance F G xi =
      (B.normalizedLawCompanion T).vectorFamily.scalarFamily.covariance
        F G xi := by
  unfold FiniteExponentialFamily.covariance
    FiniteExponentialFamily.tiltedProbability FiniteProbability.covariance
    FiniteProbability.expect
  simp_rw [B.probabilityMass_eq_normalizedLawCompanion
    T q hq hbaseline xi]
  rfl

/-- Active tilted coordinate weights scale by `q`. -/
theorem activeWeight_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.activeWeight xi m =
      q * (B.normalizedLawCompanion T).vectorFamily.scalarFamily.activeWeight
        xi m := by
  unfold FiniteExponentialFamily.activeWeight
  change
    B.vectorFamily.baseMass *
        B.vectorFamily.scalarFamily.probabilityMass xi m =
      q * ((B.normalizedLawCompanion T).vectorFamily.baseMass *
        (B.normalizedLawCompanion T).vectorFamily.scalarFamily.probabilityMass
          xi m)
  rw [B.vectorFamily_baseMass,
    B.q_eq_of_baseline_eq_activeMassBaseline T q hq hbaseline,
    (B.normalizedLawCompanion T).vectorFamily_baseMass,
    B.normalizedLawCompanion_q T,
    B.probabilityMass_eq_normalizedLawCompanion T q hq hbaseline xi m]
  ring

/-- Every raw paper moment scales by the literal active mass. -/
theorem paperMoment_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (F : B.sampleData.Sample -> Real) (xi : B.ParamSpace) :
    B.paperMoment F xi =
      q * (B.normalizedLawCompanion T).paperMoment F xi := by
  unfold paperMoment FiniteExponentialFamily.moment
  simp_rw [B.activeWeight_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline xi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The vector moment map scales by `q`. -/
theorem vectorMoment_eq_activeMass_smul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) :
    B.vectorFamily.vectorMoment xi =
      q • (B.normalizedLawCompanion T).vectorFamily.vectorMoment xi := by
  unfold VectorExponentialFamily.vectorMoment
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [B.activeWeight_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline xi m]
  have hstatistic :
      B.vectorFamily.statistic m =
        (B.normalizedLawCompanion T).vectorFamily.statistic m := by
    change B.statistic m = (B.normalizedLawCompanion T).statistic m
    exact B.statistic_eq_normalizedLawCompanion T q hq hbaseline m
  rw [hstatistic]
  rw [mul_smul]

/-- Consequently the raw Jacobian scales by `q`. -/
theorem jacobian_eq_activeMass_smul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) :
    B.vectorFamily.jacobian xi =
      q • (B.normalizedLawCompanion T).vectorFamily.jacobian xi := by
  have hbase :=
    (B.normalizedLawCompanion T).vectorFamily.hasFDerivAt_vectorMoment xi
  have hscaled := hbase.const_smul q
  have hfun :
      (fun eta : B.ParamSpace =>
        q • (B.normalizedLawCompanion T).vectorFamily.vectorMoment eta) =
        B.vectorFamily.vectorMoment := by
    funext eta
    exact (B.vectorMoment_eq_activeMass_smul_normalizedLawCompanion
      T q hq hbaseline eta).symm
  exact B.vectorFamily.hasFDerivAt_vectorMoment xi |>.unique (hfun ▸ hscaled)

/-- Applying the raw Jacobian exhibits the same scale factor. -/
theorem jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi v : B.ParamSpace) :
    B.vectorFamily.jacobian xi v =
      q • (B.normalizedLawCompanion T).vectorFamily.jacobian xi v := by
  rw [B.jacobian_eq_activeMass_smul_normalizedLawCompanion
    T q hq hbaseline xi]
  rfl

/-- Normalized covariance operators agree literally. -/
theorem covarianceOperator_eq_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) :
    B.covarianceOperator xi =
      (B.normalizedLawCompanion T).covarianceOperator xi := by
  unfold covarianceOperator
  rw [B.q_eq_of_baseline_eq_activeMassBaseline T q hq hbaseline,
    B.normalizedLawCompanion_q T,
    B.normalizedLawCompanion_L,
    B.jacobian_eq_activeMass_smul_normalizedLawCompanion
      T q hq hbaseline xi]
  ext v
  simp only [smul_smul, div_one]
  field_simp [ne_of_gt hq]

/-- Dividing the raw band request by `q` makes the target vectors differ by
the same factor `q` as the Jacobians. -/
theorem targetVector_eq_activeMass_smul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (Delta : Band -> Real) :
    B.targetVector Delta = q •
      (B.normalizedLawCompanion T).targetVector
        (fun j => Delta j / q) := by
  apply (EuclideanSpace.equiv B.Coord Real).injective
  funext c
  change B.targetVector Delta c = q *
    (B.normalizedLawCompanion T).targetVector
      (fun j => Delta j / q) c
  rw [B.targetVector_apply,
    (B.normalizedLawCompanion T).targetVector_apply]
  cases c with
  | gauge j =>
      change
        (Delta j.1 - B.lowRatio j * Delta B.lowBand) / 1 =
          q * ((Delta j.1 / q -
            B.lowRatio j * (Delta B.lowBand / q)) / 1)
      field_simp [ne_of_gt hq]
  | physical => simp [unscaledTarget, coordScale]
  | head h => simp [unscaledTarget, coordScale]
  | slow =>
      change
        (∑ j : Band, B.bandCenter j * Delta j) / B.w =
          q * ((∑ j : Band, B.bandCenter j * (Delta j / q)) / B.w)
      have hsum :
          (∑ j : Band, B.bandCenter j * (Delta j / q)) =
            (∑ j : Band, B.bandCenter j * Delta j) / q := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hsum]
      field_simp [ne_of_gt hq, ne_of_gt B.w_pos]

/-- The normalized endpoint target is literally the same for the physical
bridge and its mass-one companion. -/
theorem normalizedTarget_eq_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (Delta : Band -> Real) :
    B.normalizedTarget Delta =
      (B.normalizedLawCompanion T).normalizedTarget
        (fun j => Delta j / q) := by
  unfold normalizedTarget
  rw [B.q_eq_of_baseline_eq_activeMassBaseline T q hq hbaseline,
    B.normalizedLawCompanion_q T, B.normalizedLawCompanion_L,
    B.targetVector_eq_activeMass_smul_normalizedLawCompanion T q hq Delta]
  simp only [smul_smul, div_one]
  congr 1
  field_simp [ne_of_gt hq]

/-- The two exact canonical target-envelope hypotheses are invariant under
the same normalization of the raw requested increments. -/
theorem hasTargetEnvelopes_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    {C : Real} (Delta : Band -> Real)
    (henv : B.HasTargetEnvelopes C Delta) :
    (B.normalizedLawCompanion T).HasTargetEnvelopes C
      (fun j => Delta j / q) := by
  rcases henv with ⟨hband, hslow⟩
  constructor
  · intro j
    have hj := hband j
    rw [B.q_eq_of_baseline_eq_activeMassBaseline T q hq hbaseline] at hj
    rw [abs_div, abs_of_pos hq,
      B.normalizedLawCompanion_q, B.normalizedLawCompanion_L]
    apply (div_le_iff₀ hq).2
    calc
      abs (Delta j) <=
          (q / B.L) * C * abs (B.harmonicMass j) := hj
      _ = ((1 / B.L) * C * abs (B.harmonicMass j)) * q := by ring
  · have hs := hslow
    rw [B.q_eq_of_baseline_eq_activeMassBaseline T q hq hbaseline] at hs
    rw [B.normalizedLawCompanion_q, B.normalizedLawCompanion_L,
      B.normalizedLawCompanion_w]
    have hcenter : ∀ j : Band,
        (B.normalizedLawCompanion T).bandCenter j = B.bandCenter j := by
      intro j
      rfl
    simp_rw [hcenter]
    have hsum :
        (∑ j : Band, B.bandCenter j * (Delta j / q)) =
          (∑ j : Band, B.bandCenter j * Delta j) / q := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum, abs_div, abs_of_pos hq]
    apply (div_le_iff₀ hq).2
    calc
      abs (∑ j : Band, B.bandCenter j * Delta j) <=
          (q / B.L) * C * B.w := hs
      _ = ((1 / B.L) * C * B.w) * q := by ring

/-- A literal `Cactive/L` coordinate ledger becomes the corresponding
mass-one `(Cactive/q)/L` ledger.  This is a consequence, not an additional
input. -/
theorem normalizedLawCompanion_baseWeight_le_div_log
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    {Cactive : Real}
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L) :
    forall m : B.sampleData.Sample,
      (B.normalizedLawCompanion T).baseline.baseWeight m <=
        (Cactive / q) / (B.normalizedLawCompanion T).L := by
  intro m
  have hm := hactive m
  rw [B.baseWeight_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline m] at hm
  rw [B.normalizedLawCompanion_L]
  calc
    (B.normalizedLawCompanion T).baseline.baseWeight m <=
        (Cactive / B.L) / q := by
      apply (le_div_iff₀ hq).2
      simpa only [mul_comm] using hm
    _ = (Cactive / q) / B.L := by ring

/-- The usual active-mass majorant becomes the mass-one majorant after
normalizing `N` by the same factor. -/
theorem normalizedLawCompanion_q_le_of_activeMass_bound
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    {Cmass N : Real}
    (hqMass : q <= Cmass * N) :
    (B.normalizedLawCompanion T).q <= Cmass * (N / q) := by
  rw [B.normalizedLawCompanion_q]
  calc
    (1 : Real) <= (Cmass * N) / q :=
      (le_div_iff₀ hq).2 (by simpa only [one_mul] using hqMass)
    _ = Cmass * (N / q) := by ring

/-- The initial marked-prime rate is homogeneous under simultaneous
normalization of the marked target, moment, and ambient scale `N`. -/
theorem normalizedLawCompanion_initialMarkedRate
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (markedTarget : Nat -> Real) (N Cinitial : Real)
    (primes : Finset Nat)
    (hinitial : ∀ p ∈ primes,
      abs (markedTarget p - B.paperMoment (B.markedValuation p) 0) <=
        Cinitial * N / ((p : Real) * B.L)) :
    ∀ p ∈ primes,
      abs (markedTarget p / q -
          (B.normalizedLawCompanion T).paperMoment
            ((B.normalizedLawCompanion T).markedValuation p) 0) <=
        Cinitial * (N / q) /
          ((p : Real) * (B.normalizedLawCompanion T).L) := by
  intro p hp
  have hpRaw := hinitial p hp
  rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline] at hpRaw
  have hidentity : markedTarget p / q -
        (B.normalizedLawCompanion T).paperMoment
          ((B.normalizedLawCompanion T).markedValuation p) 0 =
      (markedTarget p - q *
        (B.normalizedLawCompanion T).paperMoment
          ((B.normalizedLawCompanion T).markedValuation p) 0) / q := by
    field_simp [ne_of_gt hq]
  rw [hidentity, abs_div, abs_of_pos hq,
    B.normalizedLawCompanion_L]
  apply (div_le_iff₀ hq).2
  calc
    abs (markedTarget p - q *
        (B.normalizedLawCompanion T).paperMoment
          ((B.normalizedLawCompanion T).markedValuation p) 0) <=
      Cinitial * N / ((p : Real) * B.L) := hpRaw
    _ = (Cinitial * (N / q) / ((p : Real) * B.L)) * q := by
      have hcancel : q * (N / q) = N := by
        field_simp [ne_of_gt hq]
      rw [show (Cinitial * (N / q) / ((p : Real) * B.L)) * q =
          (q * (N / q)) *
            (Cinitial / ((p : Real) * B.L)) by ring,
        hcancel]
      ring

/-- Raw Jacobian invertibility is invariant under positive active-mass
scaling.  This is used to handle the globally defined inverse even outside
the covariance box, where its documented fallback is zero. -/
theorem jacobian_isInvertible_iff_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) :
    (B.vectorFamily.jacobian xi).IsInvertible <->
      ((B.normalizedLawCompanion T).vectorFamily.jacobian xi).IsInvertible := by
  constructor
  · intro hB
    have hinj : Function.Injective
        ((B.normalizedLawCompanion T).vectorFamily.jacobian xi) := by
      intro x y hxy
      apply hB.injective
      rw [B.jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
          T q hq hbaseline xi,
        B.jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
          T q hq hbaseline xi,
        hxy]
    have hsurj : Function.Surjective
        ((B.normalizedLawCompanion T).vectorFamily.jacobian xi) :=
      LinearMap.surjective_of_injective hinj
    exact ⟨ContinuousLinearEquiv.ofBijective
      ((B.normalizedLawCompanion T).vectorFamily.jacobian xi)
      (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj), rfl⟩
  · intro hN
    have hinj : Function.Injective (B.vectorFamily.jacobian xi) := by
      intro x y hxy
      apply hN.injective
      have hscaled := hxy
      rw [B.jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
          T q hq hbaseline xi,
        B.jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
          T q hq hbaseline xi] at hscaled
      exact smul_right_injective B.ParamSpace (ne_of_gt hq) hscaled
    have hsurj : Function.Surjective (B.vectorFamily.jacobian xi) :=
      LinearMap.surjective_of_injective hinj
    exact ⟨ContinuousLinearEquiv.ofBijective
      (B.vectorFamily.jacobian xi)
      (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj), rfl⟩

/-- The straight-target ODE is exactly homogeneous: scaling the baseline
and the raw requested increments by the same positive factor does not alter
the parameter-space vector field. -/
theorem vectorField_eq_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (Delta : Band -> Real) (xi : B.ParamSpace) :
    B.vectorFamily.vectorField (B.targetVector Delta) xi =
      (B.normalizedLawCompanion T).vectorFamily.vectorField
        ((B.normalizedLawCompanion T).targetVector
          (fun j => Delta j / q)) xi := by
  let N : BridgeData Head Band := B.normalizedLawCompanion T
  by_cases hN : (N.vectorFamily.jacobian xi).IsInvertible
  · have hB : (B.vectorFamily.jacobian xi).IsInvertible :=
      (B.jacobian_isInvertible_iff_normalizedLawCompanion
        T q hq hbaseline xi).mpr hN
    apply hB.injective
    change B.vectorFamily.jacobian xi
        ((B.vectorFamily.jacobian xi).inverse (B.targetVector Delta)) =
      B.vectorFamily.jacobian xi
        ((N.vectorFamily.jacobian xi).inverse
          (N.targetVector (fun j => Delta j / q)))
    rw [hB.self_apply_inverse]
    rw [B.jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
      T q hq hbaseline xi]
    rw [hN.self_apply_inverse]
    exact B.targetVector_eq_activeMass_smul_normalizedLawCompanion
      T q hq Delta
  · have hB : ¬ (B.vectorFamily.jacobian xi).IsInvertible := by
      intro h
      exact hN ((B.jacobian_isInvertible_iff_normalizedLawCompanion
        T q hq hbaseline xi).mp h)
    unfold VectorExponentialFamily.vectorField
    rw [ContinuousLinearMap.inverse_of_not_isInvertible hB,
      ContinuousLinearMap.inverse_of_not_isInvertible hN]
    change (0 : B.ParamSpace) = (0 : B.ParamSpace)
    rfl

/-- The marked residual itself scales by `q` when both the baseline and the
marked target are scaled. -/
theorem markedBandResidual_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (markedTarget : Nat -> Real) (xi : B.ParamSpace) (j : Band) :
    B.markedBandResidual markedTarget xi j = q *
      (B.normalizedLawCompanion T).markedBandResidual
        (fun p => markedTarget p / q) xi j := by
  unfold markedBandResidual
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hvaluation :
      B.markedValuation (p : Nat) =
        (B.normalizedLawCompanion T).markedValuation (p : Nat) := by
    rfl
  rw [hvaluation]
  rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline]
  field_simp [ne_of_gt hq]

set_option maxHeartbeats 4000000 in
/--
Transport a certified mass-one canonical Proposition 8.7 path to the
literal active mass.  The auxiliary frozen layer used to obtain the
mass-one path is deliberately independent of the literal frozen layer and
is discarded.  Literal feasibility, frozen invariance, mass, and quota are
then re-established directly from the ordinary Proposition 8.7 ledger
hypotheses.  This avoids any false requirement that `q - 1` be an integer
or that the protected layer be disjoint from the active support.
-/
theorem hasPaperProposition87Conclusion_of_normalizedLawCompanion
    [Nonempty Head]
    {Aux Fixed : Type*} [Fintype Aux] [Fintype Fixed]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (Delta : Band -> Real) (a : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (auxValue : Aux -> Nat) (auxWeight : Aux -> Real) (auxQuota : Int)
    (Hnormalized : (B.normalizedLawCompanion T).HasPaperProposition87Conclusion
        (fun j => Delta j / q) a (fun p => markedTarget p / q)
        (N / q) Cpost auxValue auxWeight auxQuota)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int)
    (hquota : (quota : Real) = (∑ f, fixedWeight f) + B.q)
    {C Cfixed Cactive : Real}
    (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sigma, B.sampleData.hi sigma <=
      ArithmeticModel.physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hfrozenFeasible : forall x,
      frozenAmbientWeight fixedValue fixedWeight x ∈ Icc (0 : Real) 1)
    (hfrozenLedger : forall m : B.sampleData.Sample,
      frozenAmbientWeight fixedValue fixedWeight (B.sampleData.value m) <=
        Cfixed / B.L)
    (hactiveLedger : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hlarge : Cfixed +
      Real.exp (2 *
        ((PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * (3 * (a : Real)))) *
            Cactive <= B.L) :
    B.HasPaperProposition87Conclusion Delta a markedTarget N Cpost
      fixedValue fixedWeight quota := by
  let B0 : BridgeData Head Band := B.normalizedLawCompanion T
  obtain ⟨path, hpath0, hbands0⟩ := Hnormalized
  rcases hpath0 with
    ⟨hzero0, hball0, _hsize0, hderiv0, hbandMoments0, hphysical0,
      hordinaryLog0, hheads0, hsmall0, hprimeLog0, hmarked0,
      _hfeasible0, _hfixed0, _hmass0, _hquota0⟩
  have hzero : path 0 = 0 := hzero0
  have hball : ∀ t ∈ Icc (0 : Real) 1,
      B.effectiveParamEquiv.symm (path t) ∈
        closedBall (0 : B.EffectiveParamSpace) (a : Real) := by
    intro t ht
    have ht0 := hball0 t ht
    rw [mem_closedBall, dist_zero_right,
      B0.norm_effectiveParamEquiv_symm] at ht0
    rw [mem_closedBall, dist_zero_right,
      B.norm_effectiveParamEquiv_symm]
    have hnorm :
        ‖B.effectiveCoordinateCLM (path t)‖ =
          ‖B0.effectiveCoordinateCLM (path t)‖ := by
      rw [B.norm_effectiveCoordinateCLM_eq,
        B0.norm_effectiveCoordinateCLM_eq]
      unfold effectivePrimeCoefficient bandParameter nuisanceParameter
        HeadIndex lowRatio harmonicMass primeDeviation bandCenter
      simp only [B0, B.normalizedLawCompanion_sampleData T,
        B.normalizedLawCompanion_partition T,
        B.normalizedLawCompanion_lowBand T,
        B.normalizedLawCompanion_referenceHead T,
        B.normalizedLawCompanion_w T]
      congr 1
      congr 1
      congr 1
      apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) Real).injective
      funext c
      cases c <;> rfl
    rw [hnorm]
    exact ht0
  have hsize : ∀ t ∈ Icc (0 : Real) 1,
      B.paperEffectiveSize (path t) <= 3 * (a : Real) := by
    intro t ht
    let z : B.EffectiveParamSpace := B.effectiveParamEquiv.symm (path t)
    have hzBall : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : Real) :=
      hball t ht
    have hzNorm : ‖z‖ <= (a : Real) := by
      simpa only [mem_closedBall, dist_zero_right] using hzBall
    have hpath : B.effectiveParamEquiv z = path t :=
      B.effectiveParamEquiv.apply_symm_apply (path t)
    rw [← hpath]
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hzNorm (by norm_num))
  have hderiv : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt path
        (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
        (Icc (0 : Real) 1) t := by
    intro t ht
    rw [B.vectorField_eq_normalizedLawCompanion
      T q hq hbaseline Delta (path t)]
    exact hderiv0 t ht
  have hbandMoments : forall j : Band,
      B.paperMoment (B.bandScore j) (path 1) =
        B.paperMoment (B.bandScore j) 0 + Delta j := by
    intro j
    have hj := hbandMoments0 j
    have hj' :
        B0.paperMoment (B.bandScore j) (path 1) =
          B0.paperMoment (B.bandScore j) 0 + Delta j / q := by
      simpa only [B0, normalizedLawCompanion] using hj
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    rw [hj']
    field_simp [ne_of_gt hq]; ring
  have hphysical : B.paperMoment B.physicalScore (path 1) =
      B.paperMoment B.physicalScore 0 := by
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    exact congrArg (fun x : Real => q * x) (by
      simpa only [B0, normalizedLawCompanion] using hphysical0)
  have hordinaryLog : B.paperMoment B.ordinaryLogScore (path 1) =
      B.paperMoment B.ordinaryLogScore 0 := by
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    exact congrArg (fun x : Real => q * x) (by
      simpa only [B0, normalizedLawCompanion] using hordinaryLog0)
  have hheads : forall h : B.HeadIndex,
      B.paperMoment (B.headIndicator h.1) (path 1) =
        B.paperMoment (B.headIndicator h.1) 0 := by
    intro h
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    exact congrArg (fun x : Real => q * x) (by
      simpa only [B0, normalizedLawCompanion] using hheads0 h)
  have hsmall : forall p : Nat, p.Prime -> p <= B.sampleData.W ->
      B.paperMoment (B.markedValuation p) (path 1) =
        B.paperMoment (B.markedValuation p) 0 := by
    intro p hp hple
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    exact congrArg (fun x : Real => q * x) (by
      simpa only [B0, normalizedLawCompanion] using hsmall0 p hp hple)
  have hprimeLog : B.paperMoment B.primeLogScore (path 1) =
      B.paperMoment B.primeLogScore 0 := by
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    exact congrArg (fun x : Real => q * x) (by
      simpa only [B0, normalizedLawCompanion] using hprimeLog0)
  have hmarked : ∀ p ∈ ArithmeticModel.primeBand
      B.sampleData.n B.sampleData.W,
      abs (markedTarget p -
          B.paperMoment (B.markedValuation p) (path 1)) <=
        Cpost * N / ((p : Real) * B.L) := by
    intro p hp
    have hp0 := hmarked0 p (by
      simpa only [B0, normalizedLawCompanion] using hp)
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline]
    have hidentity : markedTarget p - q *
          B0.paperMoment (B.markedValuation p) (path 1) =
        q * (markedTarget p / q -
          B0.paperMoment (B.markedValuation p) (path 1)) := by
      field_simp [ne_of_gt hq]
    rw [hidentity, abs_mul, abs_of_pos hq]
    have hscaled := mul_le_mul_of_nonneg_left hp0 hq.le
    have hcancel : q * (N / q) = N := by
      field_simp [ne_of_gt hq]
    calc
      q * abs (markedTarget p / q -
          B0.paperMoment (B.markedValuation p) (path 1))
          <= q * (Cpost * (N / q) / ((p : Real) * B.L)) := hscaled
      _ = (q * (N / q)) *
          (Cpost / ((p : Real) * B.L)) := by ring
      _ = N * (Cpost / ((p : Real) * B.L)) := by rw [hcancel]
      _ = Cpost * N / ((p : Real) * B.L) := by ring
  have hfeasible : ∀ t ∈ Icc (0 : Real) 1, forall x : Nat,
      B.ambientCombinedWeight
          (frozenAmbientWeight fixedValue fixedWeight) (path t) x ∈
        Icc (0 : Real) 1 := by
    intro t ht
    exact B.ambientCombinedWeight_mem_Icc_of_paperEffectiveSize
      hC hW hhi hsep
      (frozenAmbientWeight fixedValue fixedWeight) hfrozenFeasible
      (path t) (hsize t ht) hfrozenLedger hactiveLedger hlarge
  have hfixed : ∀ t ∈ Icc (0 : Real) 1, forall f : Fixed,
      B.combinedWeight fixedWeight (path t) (Sum.inl f) =
        B.combinedWeight fixedWeight 0 (Sum.inl f) := by
    intro t ht f
    exact B.combinedWeight_fixed_unchanged fixedWeight (path t) 0 f
  have hmass : ∀ t ∈ Icc (0 : Real) 1,
      (∑ m : B.sampleData.Sample,
        B.activeCoordinateWeight (path t) m) = B.q := by
    intro t ht
    exact B.sum_activeCoordinateWeight (path t)
  have hquotaPath : ∀ t ∈ Icc (0 : Real) 1,
      (∑ x : Fixed ⊕ B.sampleData.Sample,
        B.combinedWeight fixedWeight (path t) x) = (quota : Real) := by
    intro t ht
    exact B.sum_combinedWeight_eq_integerQuota
      fixedWeight quota hquota (path t)
  have hpath : B.IsPaperProposition87Path Delta a markedTarget N Cpost
      fixedValue fixedWeight quota path :=
    ⟨hzero, hball, hsize, hderiv, hbandMoments, hphysical,
      hordinaryLog, hheads, hsmall, hprimeLog, hmarked, hfeasible,
      hfixed, hmass, hquotaPath⟩
  refine ⟨path, hpath, ?_⟩
  intro j
  rw [B.markedBandResidual_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline markedTarget (path 1) j]
  have hj := hbands0 j
  change q * B0.markedBandResidual
      (fun p => markedTarget p / q) (path 1) j = 0
  rw [hj, mul_zero]

/-- Canonically named public endpoint of the homogeneous transport.  Its
type is exactly the preceding theorem: normalized-law canonical P87 data
produce the literal active-mass P87 conclusion with the physical frozen
layer and integer quota. -/
alias canonical_activeMass_proposition87_of_normalizedLawCompanion :=
  hasPaperProposition87Conclusion_of_normalizedLawCompanion

end BridgeData

open ArithmeticModel PaperGuardCensus PaperPermittedRegularMesh
open RegularMeshPrimeCutoffs

/-- Fixed-positive-mass, paper-order canonical Proposition 8.7 statement.
It is the literal residual-balance statement with the sole baseline change
`T.baseline` to `T.activeMassBaseline q hq`. -/
def CanonicalProposition87ActiveMassLiteralBalanceStatement
    (q : Real) (hq : 0 < q)
    (cMesh : Real)
    (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank) : Prop :=
  0 < cMesh ->
  1 <= U ->
  (forall sigma, 1 <= I.lower sigma) ->
  (forall sigma, I.upper sigma <= U) ->
  ∃ meshTol : Real, 0 < meshTol ∧
  ∃ W0 : Nat, forall W : Nat, W0 <= W ->
    forall {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
      (Phead : Head -> HeadPattern.Pattern),
    (forall h : Head, forall p : Nat,
      p ∈ (Phead h).primes <-> p.Prime ∧ p <= W) ->
    forall (Ctarget Cinitial Cmass Cfixed Cactive marginFloor : Real),
      0 <= Ctarget -> 0 <= Cinitial -> 0 <= Cmass ->
      0 <= Cfixed -> 0 <= Cactive -> 0 < marginFloor ->
    ∃ a : NNReal, 0 < (a : Real) ∧
    ∃ Cpost : Real, 0 <= Cpost ∧
    forall {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
      (hdelta : 0 < delta)
      (_hPermitted : IsPermitted (cMesh := cMesh) M),
      delta + eta <= meshTol ->
      ∀ᶠ n : Nat in atTop,
        forall (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n -> B.sampleData.W = W ->
          forall (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : forall c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) ->
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) ->
            (hscale : B.w = delta + eta) ->
            forall (T : BarycentricTarget B.sampleData),
              marginFloor <= T.cellMassMargin ->
              B.baseline = T.activeMassBaseline q hq ->
            forall (Delta : Fin (M.cellCount + 1) -> Real),
              B.HasTargetEnvelopes Ctarget Delta ->
            forall (markedTarget : Nat -> Real) (N : Real),
              0 <= N ->
              B.q <= Cmass * N ->
              (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
                abs (markedTarget p -
                  B.paperMoment (B.markedValuation p) 0) <=
                    Cinitial * N / ((p : Real) * B.L)) ->
              (forall j,
                Delta j = B.markedBandResidual markedTarget 0 j) ->
            forall {Fixed : Type*} [Fintype Fixed]
              (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
              (quota : Int),
              (quota : Real) = (∑ f, fixedWeight f) + B.q ->
              B.sampleData.HeadPatternsSeparated ->
              (forall x,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
                  Icc (0 : Real) 1) ->
              (forall m : B.sampleData.Sample,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (B.sampleData.value m) <= Cfixed / B.L) ->
              (forall m : B.sampleData.Sample,
                B.baseline.baseWeight m <= Cactive / B.L) ->
              B.HasPaperProposition87Conclusion Delta a markedTarget N Cpost
                fixedValue fixedWeight quota

namespace BridgeData

set_option maxHeartbeats 4000000 in
/-- Canonical Proposition 8.7 for an arbitrary fixed positive literal active
mass.  The mass-one canonical theorem is applied only to the normalized-law
companion; the preceding homogeneous theorem transports its actual path and
then re-establishes the physical frozen-plus-active feasibility and quota. -/
theorem canonical_proposition87_activeMassLiteralBandBalance
    (q : Real) (hq : 0 < q)
    (cMesh : Real)
    (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank) :
    CanonicalProposition87ActiveMassLiteralBalanceStatement
      q hq cMesh I U Cprom Cbank ledger := by
  have hold := canonical_proposition87_literalBandBalance
    cMesh I U Cprom Cbank ledger
  unfold CanonicalProposition87LiteralBalanceStatement at hold
  unfold CanonicalProposition87ActiveMassLiteralBalanceStatement
  intro hcMesh hU hlowerOne hupperU
  obtain ⟨meshTol, hmeshTol, W0, hWold⟩ :=
    hold hcMesh hU hlowerOne hupperU
  let Wactive : Nat := max W0 2
  refine ⟨meshTol, hmeshTol, Wactive, ?_⟩
  intro W hW Head _instHeadFintype _instHeadDecidable _instHeadNonempty
    Phead hPhead Ctarget Cinitial Cmass Cfixed Cactive marginFloor
    hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  let Cactive0 : Real := max Cactive (Cactive / q)
  have hCactive0 : 0 <= Cactive0 := by
    exact hCactive.trans (le_max_left _ _)
  have hWoldLe : W0 <= W := by
    exact (le_max_left W0 2).trans hW
  obtain ⟨a, ha, Cpost, hCpost, hMeshOld⟩ :=
    hWold W hWoldLe Phead hPhead Ctarget Cinitial Cmass Cfixed Cactive0
      marginFloor hCtarget hCinitial hCmass hCfixed hCactive0 hmarginFloor
  refine ⟨a, ha, Cpost, hCpost, ?_⟩
  intro delta eta M hdelta hPermitted hfine
  have hOldN := hMeshOld M hdelta hPermitted hfine
  have hSlackN := eventually_canonical_exponential_slack_le_L
    (Head := Head) (Band := Fin (M.cellCount + 1))
    U hU W a Cfixed Cactive hCactive
  filter_upwards [hOldN, hSlackN] with n hnOld hslack
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline Delta henv markedTarget N hN hqMass
    hinitial hDelta Fixed _instFixedFintype fixedValue fixedWeight
    quota hquota hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
  let B0 := B.normalizedLawCompanion T
  have hBWlarge : 1 < B.sampleData.W := by
    have hWlarge : 1 < W := by
      have hWtwo : 2 <= W := by
        exact (le_max_right W0 2).trans hW
      omega
    simpa only [hBW] using hWlarge
  have hhiIntervals : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhiU : forall sigma, B.sampleData.hi sigma <=
      physicalBound U B.sampleData.n := by
    intro sigma
    rw [hhiIntervals]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperU sigma) B.sampleData.n
  have henv0 := B.hasTargetEnvelopes_normalizedLawCompanion
    T q hq hbaseline Delta henv
  have hN0 : 0 <= N / q := div_nonneg hN hq.le
  have hqRaw : q <= Cmass * N := by
    rw [← B.q_eq_of_baseline_eq_activeMassBaseline T q hq hbaseline]
    exact hqMass
  have hqMass0 : B0.q <= Cmass * (N / q) := by
    exact B.normalizedLawCompanion_q_le_of_activeMass_bound
      T q hq hqRaw
  have hinitial0 := B.normalizedLawCompanion_initialMarkedRate
    T q hq hbaseline markedTarget N Cinitial
      (primeBand B.sampleData.n B.sampleData.W) hinitial
  have hDelta0 : forall j,
      Delta j / q = B0.markedBandResidual
        (fun p => markedTarget p / q) 0 j := by
    intro j
    have hres := B.markedBandResidual_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline markedTarget 0 j
    rw [hDelta j, hres]
    field_simp [ne_of_gt hq]; ring
  have hactive0Raw := B.normalizedLawCompanion_baseWeight_le_div_log
    T q hq hbaseline hactiveLedger
  have hactive0 : forall m : B0.sampleData.Sample,
      B0.baseline.baseWeight m <= Cactive0 / B0.L := by
    intro m
    exact (hactive0Raw m).trans (div_le_div_of_nonneg_right
      (le_max_right Cactive (Cactive / q)) B.L_pos.le)
  have hfrozen0 : forall x : Nat,
      frozenAmbientWeight (fun e : Fin 0 => Fin.elim0 e)
        (fun e : Fin 0 => Fin.elim0 e) x ∈ Icc (0 : Real) 1 := by
    intro x
    simp [frozenAmbientWeight]
  have hfrozenLedger0 : forall m : B0.sampleData.Sample,
      frozenAmbientWeight (fun e : Fin 0 => Fin.elim0 e)
        (fun e : Fin 0 => Fin.elim0 e) (B0.sampleData.value m) <=
          Cfixed / B0.L := by
    intro m
    simp only [frozenAmbientWeight, Finset.univ_eq_empty, Finset.sum_empty]
    exact div_nonneg hCfixed B0.L_pos.le
  have hquota0 : ((1 : Int) : Real) =
      (∑ e : Fin 0, (Fin.elim0 e : Real)) + B0.q := by
    simp [B0, B.normalizedLawCompanion_q]
  have Hnormalized : B0.HasPaperProposition87Conclusion
      (fun j => Delta j / q) a (fun p => markedTarget p / q)
      (N / q) Cpost (fun e : Fin 0 => Fin.elim0 e)
      (fun e : Fin 0 => Fin.elim0 e) 1 := by
    exact hnOld B0 hBn hBW hsep hremaining
      (by simpa only [B0, normalizedLawCompanion] using hcanonical)
      (by simpa only [B0, normalizedLawCompanion] using hpartition)
      (by simpa only [B0, normalizedLawCompanion] using hscale)
      T hTmargin rfl (fun j => Delta j / q) henv0
      (fun p => markedTarget p / q) (N / q) hN0 hqMass0
      (by simpa only [B0, normalizedLawCompanion] using hinitial0)
      hDelta0 (fun e : Fin 0 => Fin.elim0 e)
      (fun e : Fin 0 => Fin.elim0 e) 1 hquota0
      (by simpa only [B0, normalizedLawCompanion] using hheadSeparated)
      hfrozen0 hfrozenLedger0 hactive0
  exact B.canonical_activeMass_proposition87_of_normalizedLawCompanion
    T q hq hbaseline Delta a markedTarget N Cpost
    (fun e : Fin 0 => Fin.elim0 e) (fun e : Fin 0 => Fin.elim0 e) 1
    Hnormalized fixedValue fixedWeight quota hquota hU hBWlarge hhiU
    hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
    (hslack B hBn hBW)

end BridgeData

/-!
## Varying paper mass

The paper uses `q_n`, not a fixed `q`.  Uniformity is retained once
`1 <= q_n`: the normalized companion ledger is bounded by
`(Cactive / q_n) / L <= Cactive / L`, so no ODE radius, mesh constant, or
eventual threshold needs to depend on `q_n`.
-/

/-- Paper-order canonical Proposition 8.7 with an active mass which may vary
with `n`.  Positivity is supplied at the actual finite bridge, while the
uniform theorem below needs only the paper-valid eventual lower bound
`1 <= q_n`. -/
def CanonicalProposition87VaryingActiveMassLiteralBalanceStatement
    (qMass : Nat -> Real)
    (cMesh : Real)
    (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank) : Prop :=
  0 < cMesh ->
  1 <= U ->
  (forall sigma, 1 <= I.lower sigma) ->
  (forall sigma, I.upper sigma <= U) ->
  ∃ meshTol : Real, 0 < meshTol ∧
  ∃ W0 : Nat, forall W : Nat, W0 <= W ->
    forall {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
      (Phead : Head -> HeadPattern.Pattern),
    (forall h : Head, forall p : Nat,
      p ∈ (Phead h).primes <-> p.Prime ∧ p <= W) ->
    forall (Ctarget Cinitial Cmass Cfixed Cactive marginFloor : Real),
      0 <= Ctarget -> 0 <= Cinitial -> 0 <= Cmass ->
      0 <= Cfixed -> 0 <= Cactive -> 0 < marginFloor ->
    ∃ a : NNReal, 0 < (a : Real) ∧
    ∃ Cpost : Real, 0 <= Cpost ∧
    forall {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
      (hdelta : 0 < delta)
      (_hPermitted : IsPermitted (cMesh := cMesh) M),
      delta + eta <= meshTol ->
      ∀ᶠ n : Nat in atTop,
        forall (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n -> B.sampleData.W = W ->
          forall (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : forall c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) ->
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) ->
            (hscale : B.w = delta + eta) ->
            forall (T : BarycentricTarget B.sampleData)
              (hq : 0 < qMass B.sampleData.n),
              marginFloor <= T.cellMassMargin ->
              B.baseline = T.activeMassBaseline
                (qMass B.sampleData.n) hq ->
            forall (Delta : Fin (M.cellCount + 1) -> Real),
              B.HasTargetEnvelopes Ctarget Delta ->
            forall (markedTarget : Nat -> Real) (N : Real),
              0 <= N ->
              B.q <= Cmass * N ->
              (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
                abs (markedTarget p -
                  B.paperMoment (B.markedValuation p) 0) <=
                    Cinitial * N / ((p : Real) * B.L)) ->
              (forall j,
                Delta j = B.markedBandResidual markedTarget 0 j) ->
            forall {Fixed : Type*} [Fintype Fixed]
              (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
              (quota : Int),
              (quota : Real) = (∑ f, fixedWeight f) + B.q ->
              B.sampleData.HeadPatternsSeparated ->
              (forall x,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
                  Icc (0 : Real) 1) ->
              (forall m : B.sampleData.Sample,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (B.sampleData.value m) <= Cfixed / B.L) ->
              (forall m : B.sampleData.Sample,
                B.baseline.baseWeight m <= Cactive / B.L) ->
              B.HasPaperProposition87Conclusion Delta a markedTarget N Cpost
                fixedValue fixedWeight quota

namespace BridgeData

set_option maxHeartbeats 4000000 in
/-- Uniform varying-mass canonical Proposition 8.7.  The sole mass-uniformity
input is `1 <= q_n` eventually.  This is exactly what makes normalization
improve the active coordinate ledger and hence keeps every old canonical
constant and threshold independent of the later value of `q_n`. -/
theorem canonical_proposition87_varyingActiveMassLiteralBandBalance
    (qMass : Nat -> Real)
    (hqOne : ∀ᶠ n : Nat in atTop, 1 <= qMass n)
    (cMesh : Real)
    (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank) :
    CanonicalProposition87VaryingActiveMassLiteralBalanceStatement
      qMass cMesh I U Cprom Cbank ledger := by
  have hold := canonical_proposition87_literalBandBalance
    cMesh I U Cprom Cbank ledger
  unfold CanonicalProposition87LiteralBalanceStatement at hold
  unfold CanonicalProposition87VaryingActiveMassLiteralBalanceStatement
  intro hcMesh hU hlowerOne hupperU
  obtain ⟨meshTol, hmeshTol, Wold, hWold⟩ :=
    hold hcMesh hU hlowerOne hupperU
  let W0 : Nat := max Wold 2
  refine ⟨meshTol, hmeshTol, W0, ?_⟩
  intro W hW Head _instHeadFintype _instHeadDecidable _instHeadNonempty
    Phead hPhead Ctarget Cinitial Cmass Cfixed Cactive marginFloor
    hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  have hWoldLe : Wold <= W := (le_max_left Wold 2).trans hW
  have hWtwo : 2 <= W := (le_max_right Wold 2).trans hW
  obtain ⟨a, ha, Cpost, hCpost, hMeshOld⟩ :=
    hWold W hWoldLe Phead hPhead Ctarget Cinitial Cmass Cfixed Cactive
      marginFloor hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  refine ⟨a, ha, Cpost, hCpost, ?_⟩
  intro delta eta M hdelta hPermitted hfine
  have hOldN := hMeshOld M hdelta hPermitted hfine
  have hSlackN := eventually_canonical_exponential_slack_le_L
    (Head := Head) (Band := Fin (M.cellCount + 1))
    U hU W a Cfixed Cactive hCactive
  filter_upwards [hOldN, hSlackN, hqOne] with n hnOld hslack hqOneN
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hq hTmargin hbaseline Delta henv markedTarget N hN hMassBound
    hinitial hDelta Fixed _instFixedFintype fixedValue fixedWeight
    quota hquota hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
  let q : Real := qMass B.sampleData.n
  let B0 := B.normalizedLawCompanion T
  have hqOneB : 1 <= q := by
    dsimp only [q]
    rw [hBn]
    exact hqOneN
  have hqPos : 0 < q := lt_of_lt_of_le zero_lt_one hqOneB
  have hqProof : hq = hqPos := Subsingleton.elim _ _
  have hbaseline' : B.baseline = T.activeMassBaseline q hqPos := by
    simpa only [q, hqProof] using hbaseline
  have hBWlarge : 1 < B.sampleData.W := by
    rw [hBW]
    omega
  have hhiIntervals : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhiU : forall sigma, B.sampleData.hi sigma <=
      physicalBound U B.sampleData.n := by
    intro sigma
    rw [hhiIntervals]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperU sigma) B.sampleData.n
  have henv0 := B.hasTargetEnvelopes_normalizedLawCompanion
    T q hqPos hbaseline' Delta henv
  have hN0 : 0 <= N / q := div_nonneg hN hqPos.le
  have hqRaw : q <= Cmass * N := by
    rw [← B.q_eq_of_baseline_eq_activeMassBaseline T q hqPos hbaseline']
    exact hMassBound
  have hqMass0 : B0.q <= Cmass * (N / q) := by
    exact B.normalizedLawCompanion_q_le_of_activeMass_bound
      T q hqPos hqRaw
  have hinitial0 := B.normalizedLawCompanion_initialMarkedRate
    T q hqPos hbaseline' markedTarget N Cinitial
      (primeBand B.sampleData.n B.sampleData.W) hinitial
  have hDelta0 : forall j,
      Delta j / q = B0.markedBandResidual
        (fun p => markedTarget p / q) 0 j := by
    intro j
    have hres := B.markedBandResidual_eq_activeMass_mul_normalizedLawCompanion
      T q hqPos hbaseline' markedTarget 0 j
    rw [hDelta j, hres]
    field_simp [ne_of_gt hqPos]; ring
  have hactive0Raw := B.normalizedLawCompanion_baseWeight_le_div_log
    T q hqPos hbaseline' hactiveLedger
  have hCdiv : Cactive / q <= Cactive := div_le_self hCactive hqOneB
  have hactive0 : forall m : B0.sampleData.Sample,
      B0.baseline.baseWeight m <= Cactive / B0.L := by
    intro m
    exact (hactive0Raw m).trans (div_le_div_of_nonneg_right
      hCdiv B.L_pos.le)
  have hfrozen0 : forall x : Nat,
      frozenAmbientWeight (fun e : Fin 0 => Fin.elim0 e)
        (fun e : Fin 0 => Fin.elim0 e) x ∈ Icc (0 : Real) 1 := by
    intro x
    simp [frozenAmbientWeight]
  have hfrozenLedger0 : forall m : B0.sampleData.Sample,
      frozenAmbientWeight (fun e : Fin 0 => Fin.elim0 e)
        (fun e : Fin 0 => Fin.elim0 e) (B0.sampleData.value m) <=
          Cfixed / B0.L := by
    intro m
    simp only [frozenAmbientWeight, Finset.univ_eq_empty, Finset.sum_empty]
    exact div_nonneg hCfixed B0.L_pos.le
  have hquota0 : ((1 : Int) : Real) =
      (∑ e : Fin 0, (Fin.elim0 e : Real)) + B0.q := by
    simp [B0, B.normalizedLawCompanion_q]
  have Hnormalized : B0.HasPaperProposition87Conclusion
      (fun j => Delta j / q) a (fun p => markedTarget p / q)
      (N / q) Cpost (fun e : Fin 0 => Fin.elim0 e)
      (fun e : Fin 0 => Fin.elim0 e) 1 := by
    exact hnOld B0 hBn hBW hsep hremaining
      (by simpa only [B0, normalizedLawCompanion] using hcanonical)
      (by simpa only [B0, normalizedLawCompanion] using hpartition)
      (by simpa only [B0, normalizedLawCompanion] using hscale)
      T hTmargin rfl (fun j => Delta j / q) henv0
      (fun p => markedTarget p / q) (N / q) hN0 hqMass0
      (by simpa only [B0, normalizedLawCompanion] using hinitial0)
      hDelta0 (fun e : Fin 0 => Fin.elim0 e)
      (fun e : Fin 0 => Fin.elim0 e) 1 hquota0
      (by simpa only [B0, normalizedLawCompanion] using hheadSeparated)
      hfrozen0 hfrozenLedger0 hactive0
  exact B.canonical_activeMass_proposition87_of_normalizedLawCompanion
    T q hqPos hbaseline' Delta a markedTarget N Cpost
    (fun e : Fin 0 => Fin.elim0 e) (fun e : Fin 0 => Fin.elim0 e) 1
    Hnormalized fixedValue fixedWeight quota hquota hU hBWlarge hhiU
    hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
    (hslack B hBn hBW)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
