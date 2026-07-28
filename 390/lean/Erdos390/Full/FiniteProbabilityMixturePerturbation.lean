import Erdos390.Full.FiniteProbabilityMixture
import Erdos390.Full.GuardDeletionFamilyRows

/-!
# Family-summed perturbations of finite tagged mixtures

The covariance of a tagged mixture contains a between-component term.  Thus
componentwise covariance estimates alone cannot be averaged.  This file
works one level lower: component first moments and mixed moments are compared,
then the exact sigma-mixture expectation formula is used before covariance is
formed.  The resulting theorem keeps an entire finite covariance row under a
single family envelope and includes the between-component contribution.
-/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbability

noncomputable section

variable {Cell I : Type*} [Fintype Cell] [Fintype I]
  {Omega Theta : Cell → Type*}
  [∀ c, Fintype (Omega c)] [∀ c, Fintype (Theta c)]

/-- A uniform componentwise expectation perturbation survives an arbitrary
common convex mixture.  The two component sample types may be different. -/
theorem abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Fmu : ∀ c, Omega c → ℝ) (Fnu : ∀ c, Theta c → ℝ)
    {d : ℝ}
    (hcell : ∀ c, |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| ≤ d) :
    |(sigmaMixture weight nu).expect (fun x ↦ Fnu x.1 x.2) -
        (sigmaMixture weight mu).expect (fun x ↦ Fmu x.1 x.2)| ≤ d := by
  rw [sigmaMixture_expect, sigmaMixture_expect]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ c, (weight.mass c * (nu c).expect (Fnu c) -
        weight.mass c * (mu c).expect (Fmu c))| ≤
        ∑ c, |weight.mass c * (nu c).expect (Fnu c) -
          weight.mass c * (mu c).expect (Fmu c)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, weight.mass c *
        |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← mul_sub, abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
    _ ≤ ∑ c, weight.mass c * d := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = d := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]

/-- A componentwise `l¹` family of expectation perturbations also survives
mixing without a factor equal to the number of components or row indices. -/
theorem sum_abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Hmu : ∀ c, I → Omega c → ℝ)
    (Hnu : ∀ c, I → Theta c → ℝ)
    {d : ℝ}
    (hcell : ∀ c, ∑ i,
      |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| ≤ d) :
    ∑ i, |(sigmaMixture weight nu).expect
          (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).expect
          (fun x ↦ Hmu x.1 i x.2)| ≤ d := by
  have hpoint (i : I) :
      |(sigmaMixture weight nu).expect (fun x ↦ Hnu x.1 i x.2) -
          (sigmaMixture weight mu).expect (fun x ↦ Hmu x.1 i x.2)| ≤
        ∑ c, weight.mass c *
          |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| := by
    rw [sigmaMixture_expect, sigmaMixture_expect,
      ← Finset.sum_sub_distrib]
    calc
      |∑ c, (weight.mass c * (nu c).expect (Hnu c i) -
          weight.mass c * (mu c).expect (Hmu c i))| ≤
          ∑ c, |weight.mass c * (nu c).expect (Hnu c i) -
            weight.mass c * (mu c).expect (Hmu c i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [← mul_sub, abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
  calc
    ∑ i, |(sigmaMixture weight nu).expect
          (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).expect
          (fun x ↦ Hmu x.1 i x.2)| ≤
        ∑ i, ∑ c, weight.mass c *
          |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = ∑ c, weight.mass c * ∑ i,
        |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ ≤ ∑ c, weight.mass c * d := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = d := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]

/-- A componentwise `l¹` expectation envelope passes to the tagged mixture.
This is the family analogue of `sigmaMixture_expect_le_common`. -/
theorem sum_abs_sigmaMixture_expect_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (H : ∀ c, I → Omega c → ℝ)
    {A : ℝ}
    (hcell : ∀ c, ∑ i, |(mu c).expect (H c i)| ≤ A) :
    ∑ i, |(sigmaMixture weight mu).expect
      (fun x ↦ H x.1 i x.2)| ≤ A := by
  have hpoint (i : I) :
      |(sigmaMixture weight mu).expect (fun x ↦ H x.1 i x.2)| ≤
        ∑ c, weight.mass c * |(mu c).expect (H c i)| := by
    rw [sigmaMixture_expect]
    calc
      |∑ c, weight.mass c * (mu c).expect (H c i)| ≤
          ∑ c, |weight.mass c * (mu c).expect (H c i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
  calc
    ∑ i, |(sigmaMixture weight mu).expect
        (fun x ↦ H x.1 i x.2)| ≤
        ∑ i, ∑ c, weight.mass c * |(mu c).expect (H c i)| :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = ∑ c, weight.mass c * ∑ i, |(mu c).expect (H c i)| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ ≤ ∑ c, weight.mass c * A := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = A := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]

/-- Family-summed covariance stability for two tagged mixtures with the same
component weights.  The hypotheses compare component first moments and mixed
moments, not component covariances, so the conclusion includes the complete
between-component covariance term. -/
theorem sum_abs_sigmaMixture_covariance_sub_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Fmu : ∀ c, Omega c → ℝ) (Fnu : ∀ c, Theta c → ℝ)
    (Hmu : ∀ c, I → Omega c → ℝ)
    (Hnu : ∀ c, I → Theta c → ℝ)
    {AF AH dF dH dFH : ℝ}
    (hAF : 0 ≤ AF) (hAH : 0 ≤ AH)
    (hdF : 0 ≤ dF)
    (hFbase : ∀ c, |(mu c).expect (Fmu c)| ≤ AF)
    (hHbase : ∀ c, ∑ i, |(mu c).expect (Hmu c i)| ≤ AH)
    (hFdiff : ∀ c,
      |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| ≤ dF)
    (hHdiff : ∀ c, ∑ i,
      |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| ≤ dH)
    (hFHdiff : ∀ c, ∑ i,
      |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
        (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤ dFH) :
    ∑ i, |(sigmaMixture weight nu).covariance
          (fun x ↦ Fnu x.1 x.2) (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ Fmu x.1 x.2) (fun x ↦ Hmu x.1 i x.2)| ≤
      dFH + (AF + dF) * dH + AH * dF := by
  let Mu := sigmaMixture weight mu
  let Nu := sigmaMixture weight nu
  let FMu : Sigma Omega → ℝ := fun x ↦ Fmu x.1 x.2
  let FNu : Sigma Theta → ℝ := fun x ↦ Fnu x.1 x.2
  let HMU : I → Sigma Omega → ℝ := fun i x ↦ Hmu x.1 i x.2
  let HNU : I → Sigma Theta → ℝ := fun i x ↦ Hnu x.1 i x.2
  have hFbaseGlobal : |Mu.expect FMu| ≤ AF := by
    rw [sigmaMixture_expect]
    calc
      |∑ c, weight.mass c * (mu c).expect (Fmu c)| ≤
          ∑ c, weight.mass c * |(mu c).expect (Fmu c)| := by
        calc
          _ ≤ ∑ c, |weight.mass c * (mu c).expect (Fmu c)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
      _ ≤ ∑ c, weight.mass c * AF := by
        apply Finset.sum_le_sum
        intro c hc
        exact mul_le_mul_of_nonneg_left (hFbase c) (weight.mass_nonneg c)
      _ = AF := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]
  have hHbaseGlobal : ∑ i, |Mu.expect (HMU i)| ≤ AH := by
    simpa only [Mu, HMU] using
      sum_abs_sigmaMixture_expect_le weight mu Hmu hHbase
  have hFdiffGlobal : |Nu.expect FNu - Mu.expect FMu| ≤ dF := by
    simpa only [Nu, Mu, FNu, FMu] using
      abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
        weight mu nu Fmu Fnu hFdiff
  have hHdiffGlobal : ∑ i, |Nu.expect (HNU i) - Mu.expect (HMU i)| ≤ dH := by
    simpa only [Nu, Mu, HNU, HMU] using
      sum_abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
        weight mu nu Hmu Hnu hHdiff
  have hFHdiffGlobal : ∑ i,
      |Nu.expect (fun x ↦ FNu x * HNU i x) -
        Mu.expect (fun x ↦ FMu x * HMU i x)| ≤ dFH := by
    let PHmu : ∀ c, I → Omega c → ℝ :=
      fun c i x ↦ Fmu c x * Hmu c i x
    let PHnu : ∀ c, I → Theta c → ℝ :=
      fun c i x ↦ Fnu c x * Hnu c i x
    have hraw := sum_abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
      weight mu nu PHmu PHnu hFHdiff
    simpa only [Nu, Mu, FNu, FMu, HNU, HMU, PHmu, PHnu] using hraw
  have hFnu : |Nu.expect FNu| ≤ AF + dF := by
    calc
      |Nu.expect FNu| = |(Nu.expect FNu - Mu.expect FMu) + Mu.expect FMu| := by
        congr 1
        ring
      _ ≤ |Nu.expect FNu - Mu.expect FMu| + |Mu.expect FMu| :=
        abs_add_le _ _
      _ ≤ dF + AF := add_le_add hFdiffGlobal hFbaseGlobal
      _ = AF + dF := add_comm _ _
  have hpoint (i : I) :
      |Nu.covariance FNu (HNU i) - Mu.covariance FMu (HMU i)| ≤
        |Nu.expect (fun x ↦ FNu x * HNU i x) -
            Mu.expect (fun x ↦ FMu x * HMU i x)| +
          |Nu.expect FNu| * |Nu.expect (HNU i) - Mu.expect (HMU i)| +
          |Mu.expect (HMU i)| * |Nu.expect FNu - Mu.expect FMu| := by
    unfold covariance
    have hprod :
        Nu.expect FNu * Nu.expect (HNU i) -
            Mu.expect FMu * Mu.expect (HMU i) =
          Nu.expect FNu * (Nu.expect (HNU i) - Mu.expect (HMU i)) +
            Mu.expect (HMU i) * (Nu.expect FNu - Mu.expect FMu) := by ring
    rw [show
      (Nu.expect (fun x ↦ FNu x * HNU i x) -
          Nu.expect FNu * Nu.expect (HNU i)) -
        (Mu.expect (fun x ↦ FMu x * HMU i x) -
          Mu.expect FMu * Mu.expect (HMU i)) =
        (Nu.expect (fun x ↦ FNu x * HNU i x) -
          Mu.expect (fun x ↦ FMu x * HMU i x)) -
        (Nu.expect FNu * Nu.expect (HNU i) -
          Mu.expect FMu * Mu.expect (HMU i)) by ring,
      hprod]
    let X := Nu.expect (fun x ↦ FNu x * HNU i x) -
      Mu.expect (fun x ↦ FMu x * HMU i x)
    let Y := Nu.expect FNu * (Nu.expect (HNU i) - Mu.expect (HMU i))
    let Z := Mu.expect (HMU i) * (Nu.expect FNu - Mu.expect FMu)
    change |X - (Y + Z)| ≤ _
    calc
      |X - (Y + Z)| ≤ |X| + |Y + Z| := abs_sub _ _
      _ ≤ |X| + (|Y| + |Z|) :=
        add_le_add (le_refl |X|) (abs_add_le Y Z)
      _ = _ := by
        dsimp only [X, Y, Z]
        simp only [abs_mul]
        ring
  calc
    ∑ i, |Nu.covariance FNu (HNU i) -
        Mu.covariance FMu (HMU i)| ≤
      ∑ i, (|Nu.expect (fun x ↦ FNu x * HNU i x) -
          Mu.expect (fun x ↦ FMu x * HMU i x)| +
        |Nu.expect FNu| * |Nu.expect (HNU i) - Mu.expect (HMU i)| +
        |Mu.expect (HMU i)| * |Nu.expect FNu - Mu.expect FMu|) :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = (∑ i, |Nu.expect (fun x ↦ FNu x * HNU i x) -
          Mu.expect (fun x ↦ FMu x * HMU i x)|) +
        |Nu.expect FNu| *
          (∑ i, |Nu.expect (HNU i) - Mu.expect (HMU i)|) +
        (∑ i, |Mu.expect (HMU i)|) *
          |Nu.expect FNu - Mu.expect FMu| := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_mul]
    _ ≤ dFH + (AF + dF) * dH + AH * dF := by
      exact add_le_add
        (add_le_add hFHdiffGlobal
          (mul_le_mul hFnu hHdiffGlobal (by positivity)
            (add_nonneg hAF hdF)))
        (mul_le_mul hHbaseGlobal hFdiffGlobal (by positivity) hAH)

/-- Variant with component covariance-row perturbations as input.  The two
copies of the mean-product loss are deliberate: one converts component
covariances back to mixed moments, and the other is the between-component
covariance of the tagged mixture. -/
theorem sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Fmu : ∀ c, Omega c → ℝ) (Fnu : ∀ c, Theta c → ℝ)
    (Hmu : ∀ c, I → Omega c → ℝ)
    (Hnu : ∀ c, I → Theta c → ℝ)
    {AF AH dF dH dCov : ℝ}
    (hAF : 0 ≤ AF) (hAH : 0 ≤ AH)
    (hdF : 0 ≤ dF)
    (hFbase : ∀ c, |(mu c).expect (Fmu c)| ≤ AF)
    (hHbase : ∀ c, ∑ i, |(mu c).expect (Hmu c i)| ≤ AH)
    (hFdiff : ∀ c,
      |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| ≤ dF)
    (hHdiff : ∀ c, ∑ i,
      |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| ≤ dH)
    (hCovdiff : ∀ c, ∑ i,
      |(nu c).covariance (Fnu c) (Hnu c i) -
        (mu c).covariance (Fmu c) (Hmu c i)| ≤ dCov) :
    ∑ i, |(sigmaMixture weight nu).covariance
          (fun x ↦ Fnu x.1 x.2) (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ Fmu x.1 x.2) (fun x ↦ Hmu x.1 i x.2)| ≤
      dCov + 2 * ((AF + dF) * dH + AH * dF) := by
  have hFnu (c : Cell) : |(nu c).expect (Fnu c)| ≤ AF + dF := by
    calc
      |(nu c).expect (Fnu c)| =
          |((nu c).expect (Fnu c) - (mu c).expect (Fmu c)) +
            (mu c).expect (Fmu c)| := by
        congr 1
        ring
      _ ≤ |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| +
          |(mu c).expect (Fmu c)| := abs_add_le _ _
      _ ≤ dF + AF := add_le_add (hFdiff c) (hFbase c)
      _ = AF + dF := add_comm _ _
  have hprodPoint (c : Cell) (i : I) :
      |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| ≤
        |(nu c).expect (Fnu c)| *
            |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| +
          |(mu c).expect (Hmu c i)| *
            |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| := by
    rw [show
      (nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i) =
        (nu c).expect (Fnu c) *
            ((nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)) +
          (mu c).expect (Hmu c i) *
            ((nu c).expect (Fnu c) - (mu c).expect (Fmu c)) by ring]
    simpa only [abs_mul] using abs_add_le
      ((nu c).expect (Fnu c) *
        ((nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)))
      ((mu c).expect (Hmu c i) *
        ((nu c).expect (Fnu c) - (mu c).expect (Fmu c)))
  have hprod (c : Cell) :
      ∑ i, |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| ≤
        (AF + dF) * dH + AH * dF := by
    calc
      ∑ i, |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| ≤
        ∑ i, (|(nu c).expect (Fnu c)| *
            |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| +
          |(mu c).expect (Hmu c i)| *
            |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)|) :=
        Finset.sum_le_sum fun i hi ↦ hprodPoint c i
      _ = |(nu c).expect (Fnu c)| *
            (∑ i, |(nu c).expect (Hnu c i) -
              (mu c).expect (Hmu c i)|) +
          (∑ i, |(mu c).expect (Hmu c i)|) *
            |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      _ ≤ (AF + dF) * dH + AH * dF := by
        exact add_le_add
          (mul_le_mul (hFnu c) (hHdiff c) (by positivity)
            (add_nonneg hAF hdF))
          (mul_le_mul (hHbase c) (hFdiff c) (by positivity) hAH)
  have hFHdiff (c : Cell) : ∑ i,
      |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
        (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤
      dCov + ((AF + dF) * dH + AH * dF) := by
    have hpoint (i : I) :
        |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
            (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤
          |(nu c).covariance (Fnu c) (Hnu c i) -
            (mu c).covariance (Fmu c) (Hmu c i)| +
          |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| := by
      unfold covariance
      rw [show
        (nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
            (mu c).expect (fun x ↦ Fmu c x * Hmu c i x) =
          ((nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
              (nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            ((mu c).expect (fun x ↦ Fmu c x * Hmu c i x) -
              (mu c).expect (Fmu c) * (mu c).expect (Hmu c i))) +
          ((nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)) by ring]
      exact abs_add_le _ _
    calc
      ∑ i, |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
          (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤
        ∑ i, (|(nu c).covariance (Fnu c) (Hnu c i) -
            (mu c).covariance (Fmu c) (Hmu c i)| +
          |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)|) :=
        Finset.sum_le_sum fun i hi ↦ hpoint i
      _ = (∑ i, |(nu c).covariance (Fnu c) (Hnu c i) -
            (mu c).covariance (Fmu c) (Hmu c i)|) +
          ∑ i, |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| := by
        rw [Finset.sum_add_distrib]
      _ ≤ dCov + ((AF + dF) * dH + AH * dF) :=
        add_le_add (hCovdiff c) (hprod c)
  have hmain := sum_abs_sigmaMixture_covariance_sub_le
    weight mu nu Fmu Fnu Hmu Hnu hAF hAH hdF
      hFbase hHbase hFdiff hHdiff hFHdiff
  calc
    ∑ i, |(sigmaMixture weight nu).covariance
          (fun x ↦ Fnu x.1 x.2) (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ Fmu x.1 x.2) (fun x ↦ Hmu x.1 i x.2)| ≤
      (dCov + ((AF + dF) * dH + AH * dF)) +
        (AF + dF) * dH + AH * dF := hmain
    _ = dCov + 2 * ((AF + dF) * dH + AH * dF) := by ring

/-- Concrete specialization to deleting guards independently in every
component while keeping the same tagged mixture weights.  The bound is
family-summed before mixing, so neither the number of components nor the
number of row indices appears. -/
theorem sum_abs_sigmaMixture_deleteGuards_covariance_sub_le
    [∀ c, DecidableEq (Omega c)]
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (guards : ∀ c, Finset (Omega c))
    (hsmall : ∀ c, (mu c).guardMass (guards c) < 1)
    (F : ∀ c, Omega c → ℝ) (H : ∀ c, I → Omega c → ℝ)
    {KF KH d : ℝ}
    (hKF : 0 ≤ KF) (hKH : 0 ≤ KH) (hd : 0 ≤ d)
    (hF : ∀ c x, |F c x| ≤ KF)
    (hH : ∀ c x, ∑ i, |H c i x| ≤ KH)
    (hperturb : ∀ c, (mu c).guardPerturbation (guards c) ≤ d) :
    ∑ i, |(sigmaMixture weight
          (fun c ↦ (mu c).deleteGuards (guards c) (hsmall c))).covariance
          (fun x ↦ F x.1 x.2) (fun x ↦ H x.1 i x.2) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ F x.1 x.2) (fun x ↦ H x.1 i x.2)| ≤
      3 * KF * KH * d +
        2 * ((KF + KF * d) * (KH * d) + KH * (KF * d)) := by
  let nu : ∀ c, FiniteProbability (Omega c) :=
    fun c ↦ (mu c).deleteGuards (guards c) (hsmall c)
  have hFbase (c : Cell) : |(mu c).expect (F c)| ≤ KF :=
    (mu c).abs_expect_le_of_abs_le (F c) hKF (hF c)
  have hHbase (c : Cell) : ∑ i, |(mu c).expect (H c i)| ≤ KH :=
    (mu c).sum_abs_expect_le_familyEnvelope (H c) (hH c)
  have hFdiff (c : Cell) :
      |(nu c).expect (F c) - (mu c).expect (F c)| ≤ KF * d := by
    have hraw := (mu c).abs_deleteGuards_expect_sub_le
      (guards c) (hsmall c) (F c) hKF (hF c)
    exact hraw.trans (mul_le_mul_of_nonneg_left (hperturb c) hKF)
  have hHdiff (c : Cell) : ∑ i,
      |(nu c).expect (H c i) - (mu c).expect (H c i)| ≤ KH * d := by
    have hraw := (mu c).sum_abs_deleteGuards_expect_sub_le
      (guards c) (hsmall c) (H c) (hH c)
    exact hraw.trans (mul_le_mul_of_nonneg_left (hperturb c) hKH)
  have hCovdiff (c : Cell) : ∑ i,
      |(nu c).covariance (F c) (H c i) -
        (mu c).covariance (F c) (H c i)| ≤ 3 * KF * KH * d := by
    have hraw := (mu c).sum_abs_deleteGuards_covariance_sub_le
      (guards c) (hsmall c) (F c) (H c) hKF (hF c) (hH c)
    have hcoef : 0 ≤ 3 * KF * KH := by positivity
    exact hraw.trans (mul_le_mul_of_nonneg_left (hperturb c) hcoef)
  have hmain := sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    weight mu nu F F H H hKF hKH (mul_nonneg hKF hd)
      hFbase hHbase hFdiff hHdiff hCovdiff
  simpa only [nu] using hmain

end

end Erdos390.Full.FiniteProbability
