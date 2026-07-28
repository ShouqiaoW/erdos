import Erdos390.Full.PaperNonstepSlowRightLedger

/-!
# Exact non-step aggregation of a power-correction row

The guard/physical comparison is naturally stated as
`p * sum_q |Delta_{pq}| <= rho`.  Contracting it against the literal
primewise coefficient `g_q` costs only `sup |g_q|`; averaging over the
output fiber then uses its exact harmonic mass.  No output centre is divided
out in this finite lemma.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

set_option maxHeartbeats 1000000

/-- A reciprocal weighted covariance-row comparison contracts against the
literal non-step coefficient with the exact bound `rho * w`. -/
theorem abs_nonstepPowerCorrectionRow_sub_le
    {Omega₁ Omega₂ : Type*} [Fintype Omega₁] [Fintype Omega₂]
    {M₁ M₂ : ℕ}
    (law₁ : BoundedValuationLaw Omega₁ M₁)
    (law₂ : BoundedValuationLaw Omega₂ M₂)
    {rho w : ℝ} (hw : 0 ≤ w)
    (hdevSup : ∀ q : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation q| ≤ w)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |(law₁.covVV p.1 q.1 - law₁.covII p.1 q.1) -
            (law₂.covVV p.1 q.1 - law₂.covII p.1 q.1)| ≤ rho)
    (i : Band) :
    |(B.nonstepFullCoefficientRow law₁ i -
          B.nonstepSquarefreeCoefficientRow law₁ i) -
        (B.nonstepFullCoefficientRow law₂ i -
          B.nonstepSquarefreeCoefficientRow law₂ i)| ≤
      rho * w := by
  let H : ℝ := B.harmonicMass i
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have hpPos (p : BandPrime B.sampleData.n B.sampleData.W) :
      (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  let D := fun (p q : BandPrime B.sampleData.n B.sampleData.W) ↦
    (law₁.covVV p.1 q.1 - law₁.covII p.1 q.1) -
      (law₂.covVV p.1 q.1 - law₂.covII p.1 q.1)
  have hrho : 0 ≤ rho := by
    obtain ⟨p, hp⟩ := B.partition.fiber_nonempty i
    let p' : BandPrime B.sampleData.n B.sampleData.W := p
    have hnonneg : 0 ≤ (p'.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W, |D p' q| := by
      exact mul_nonneg (hpPos p').le (Finset.sum_nonneg fun q _hq ↦ abs_nonneg _)
    exact hnonneg.trans (by simpa only [D] using hrow p')
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W) :
      |∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q * D p q| ≤
        (rho * w) * (1 / (p.1 : ℝ)) := by
    have hsum :
        ∑ q : BandPrime B.sampleData.n B.sampleData.W, |D p q| ≤
          rho / (p.1 : ℝ) := by
      exact (le_div_iff₀ (hpPos p)).2 (by
        simpa only [D, mul_comm] using hrow p)
    calc
      |∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q * D p q| ≤
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |B.primeDeviation q * D p q| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |B.primeDeviation q| * |D p q| := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [abs_mul]
      _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          w * |D p q| := by
        apply Finset.sum_le_sum
        intro q _hq
        exact mul_le_mul_of_nonneg_right (hdevSup q) (abs_nonneg _)
      _ = w * ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |D p q| := by rw [Finset.mul_sum]
      _ ≤ w * (rho / (p.1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hw
      _ = (rho * w) * (1 / (p.1 : ℝ)) := by ring
  have hmass : (1 / H) *
      ∑ p ∈ B.partition.data.fiber i, (1 / (p.1 : ℝ)) = 1 := by
    change (1 / H) * H = 1
    field_simp [hH.ne']
  unfold nonstepFullCoefficientRow nonstepSquarefreeCoefficientRow
  have hrewrite :
      (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            (((∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law₁.covVV p.1 q.1) -
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law₁.covII p.1 q.1) -
            ((∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law₂.covVV p.1 q.1) -
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law₂.covII p.1 q.1)) =
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * D p q := by
    congr 1
    apply Finset.sum_congr rfl
    intro p _hp
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    dsimp only [D]
    ring
  have hrowRewrite :
      ((1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₁.covVV p.1 q.1 -
        (1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₁.covII p.1 q.1) -
      ((1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₂.covVV p.1 q.1 -
        (1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₂.covII p.1 q.1) =
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * D p q := by
    rw [← hrewrite]
    dsimp only [H]
    simp_rw [Finset.sum_sub_distrib]
    ring
  rw [hrowRewrite]
  calc
    |(1 / H) *
        ∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * D p q| ≤
      (1 / H) *
        ∑ p ∈ B.partition.data.fiber i,
          |∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * D p q| := by
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hH)]
      exact mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / H) *
        ∑ p ∈ B.partition.data.fiber i,
          (rho * w) * (1 / (p.1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun p _hp ↦ hinner p
    _ = rho * w := by
      rw [← Finset.mul_sum]
      calc
        (1 / H) * ((rho * w) *
            ∑ p ∈ B.partition.data.fiber i,
              (1 / (p.1 : ℝ))) =
          (rho * w) * ((1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              (1 / (p.1 : ℝ))) := by ring
        _ = rho * w := by rw [hmass, mul_one]

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
