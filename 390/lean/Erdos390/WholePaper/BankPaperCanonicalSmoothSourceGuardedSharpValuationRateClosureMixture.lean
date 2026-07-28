import Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosure

/-!
# Barycentric mixture algebra for the sharp smooth-source rate

The analytic marked-cell estimates compare every cell and the moving broad
pool to one common truncated prime-power profile.  This file performs the
remaining finite convex-mixture algebra exactly.

No cell-versus-broad rate is assumed.  The quantitative transfer theorem
takes two separate common-profile bounds, which are the outputs supplied by
the fixed-cell and moving-prefix analyses.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.FiniteProbability

noncomputable section

namespace BankPaperRealization

/-! ## Exact convex-mixture identities -/

/-- The scaled active valuation moment is the active mass times the
barycentric convex combination of the literal guarded-cell valuation
means. -/
theorem
    bankPaperCanonicalScaledActiveValuationMoment_eq_q_mul_cellMeans
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head}
    (T : BarycentricTarget D) (q : Real) (p : Nat) :
    bankPaperCanonicalScaledActiveValuationMoment T q p =
      q * ∑ c : Cell Head,
        T.cellProbability c *
          (uniformOnFinset (D.cellFinset c) (D.cell_nonempty c)).expect
            (fun m ↦ valuation p (m : Nat)) := by
  classical
  unfold bankPaperCanonicalScaledActiveValuationMoment
  unfold bankPaperCanonicalScaledActiveSeed
  rw [Fintype.sum_sigma]
  calc
    (∑ c : Cell Head, ∑ m : D.SampleAt c,
        q * T.baseline.baseWeight ⟨c, m⟩ *
          valuation p (D.value ⟨c, m⟩)) =
      ∑ c : Cell Head,
        q * T.cellProbability c *
          (uniformOnFinset (D.cellFinset c) (D.cell_nonempty c)).expect
            (fun m ↦ valuation p (m : Nat)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [FiniteProbability.uniformOnFinset_expect_eq]
      simp only [BaselineAllocation.baseWeight,
        StructuredSampleData.cellOf, StructuredSampleData.value,
        Fintype.card_coe]
      unfold BarycentricTarget.baseline
      rw [← Finset.mul_sum]
      ring
    _ = q * ∑ c : Cell Head,
        T.cellProbability c *
          (uniformOnFinset (D.cellFinset c) (D.cell_nonempty c)).expect
            (fun m ↦ valuation p (m : Nat)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _hc
      ring

/-- The constant guarded smooth-base moment is its literal mass times the
uniform valuation mean of the guarded broad pool. -/
theorem
    bankPaperCanonicalGuardedSmoothBaseValuationMoment_eq_mass_mul_poolMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaAct : Real) (p : Nat)
    (hpool :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).Nonempty) :
    bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
        B R certificate deltaStar betaAct p =
      bankPaperCanonicalGuardedSmoothBaseMass R certificate
          deltaStar B.sampleData.W K betaAct *
        (uniformOnFinset
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) hpool).expect
          (fun a ↦ valuation p (a : Nat)) := by
  unfold bankPaperCanonicalGuardedSmoothBaseValuationMoment
  unfold bankPaperCanonicalGuardedSmoothBaseMass
  rw [FiniteProbability.uniformOnFinset_expect_ambient_eq]
  unfold BridgeData.L Erdos390.Full.Scale.L
  have hcard :
      ((R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).card : Real) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hpool
  field_simp [hcard]

/-- After synchronizing `q` with the literal guarded smooth mass, the
unrounded active-versus-base moment is exactly mass times a difference of
probability means. -/
theorem
    bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_eq_mass_mul_meanDefect
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaAct q : Real) (p : Nat)
    (hq : q =
      bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar B.sampleData.W K betaAct)
    (hpool :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).Nonempty) :
    bankPaperCanonicalScaledActiveValuationMoment T q p -
        bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
          B R certificate deltaStar betaAct p =
      q *
        ((∑ cell : Cell (PaperHeadSimplex.Tag P),
            T.cellProbability cell *
              (B.guardedCellProbability cell).expect
                (fun m ↦ valuation p (m : Nat))) -
          (uniformOnFinset
            (R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1) hpool).expect
                (fun a ↦ valuation p (a : Nat))) := by
  rw [
    bankPaperCanonicalScaledActiveValuationMoment_eq_q_mul_cellMeans,
    bankPaperCanonicalGuardedSmoothBaseValuationMoment_eq_mass_mul_poolMean
      B R certificate deltaStar betaAct p hpool,
    ← hq]
  unfold BridgeData.guardedCellProbability
  ring

/-! ## Common-profile quantitative transfer -/

/-- A convex combination and one broad-pool law inherit their difference
bound from separate estimates against the same common profile. -/
theorem
    abs_bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_le_of_commonProfile
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaAct q main Ccell Cpool : Real) (p : Nat)
    (hq : q =
      bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar B.sampleData.W K betaAct)
    (hpool :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).Nonempty)
    (_hp : 0 < p) (_hL : 0 < B.L)
    (_hCcell : 0 ≤ Ccell) (_hCpool : 0 ≤ Cpool)
    (hcell : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      |(B.guardedCellProbability cell).expect
          (fun m ↦ valuation p (m : Nat)) - main| ≤
        Ccell / ((p : Real) * B.L))
    (hpoolProfile :
      |(uniformOnFinset
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) hpool).expect
          (fun a ↦ valuation p (a : Nat)) - main| ≤
        Cpool / ((p : Real) * B.L)) :
    |bankPaperCanonicalScaledActiveValuationMoment T q p -
        bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
          B R certificate deltaStar betaAct p| ≤
      |q| * ((Ccell + Cpool) / ((p : Real) * B.L)) := by
  let cellMean : Cell (PaperHeadSimplex.Tag P) → Real := fun cell ↦
    (B.guardedCellProbability cell).expect
      (fun m ↦ valuation p (m : Nat))
  let poolMean : Real :=
    (uniformOnFinset
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1) hpool).expect
      (fun a ↦ valuation p (a : Nat))
  have hmixIdentity :
      (∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main =
        ∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * (cellMean cell - main) := by
    calc
      (∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main =
        (∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) -
          (∑ cell : Cell (PaperHeadSimplex.Tag P),
            T.cellProbability cell) * main := by
          rw [T.sum_cellProbability, one_mul]
      _ = _ := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro cell _hcell
        ring
  have hmix :
      |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main| ≤
        Ccell / ((p : Real) * B.L) := by
    rw [hmixIdentity]
    calc
      |∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * (cellMean cell - main)| ≤
        ∑ cell : Cell (PaperHeadSimplex.Tag P),
          |T.cellProbability cell * (cellMean cell - main)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * |cellMean cell - main| := by
        apply Finset.sum_congr rfl
        intro cell _hcell
        rw [abs_mul, abs_of_nonneg (T.cellProbability_pos cell).le]
      _ ≤ ∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell *
            (Ccell / ((p : Real) * B.L)) := by
        apply Finset.sum_le_sum
        intro cell _hcell
        exact mul_le_mul_of_nonneg_left
          (by simpa only [cellMean] using hcell cell)
          (T.cellProbability_pos cell).le
      _ = Ccell / ((p : Real) * B.L) := by
        rw [← Finset.sum_mul, T.sum_cellProbability, one_mul]
  have hmeanPair :
      |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - poolMean| ≤
        (Ccell + Cpool) / ((p : Real) * B.L) := by
    calc
      |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - poolMean| ≤
        |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main| +
          |poolMean - main| := by
            have htri := abs_add_le
              ((∑ cell : Cell (PaperHeadSimplex.Tag P),
                T.cellProbability cell * cellMean cell) - main)
              (main - poolMean)
            simpa only [sub_add_sub_cancel, abs_sub_comm] using htri
      _ ≤ Ccell / ((p : Real) * B.L) +
          Cpool / ((p : Real) * B.L) :=
        add_le_add hmix
          (by simpa only [poolMean] using hpoolProfile)
      _ = (Ccell + Cpool) / ((p : Real) * B.L) := by ring
  rw [
    bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_eq_mass_mul_meanDefect
      B R certificate T deltaStar betaAct q p hq hpool,
    abs_mul]
  exact mul_le_mul_of_nonneg_left hmeanPair (abs_nonneg q)

end BankPaperRealization

end

end Erdos390.WholePaper
