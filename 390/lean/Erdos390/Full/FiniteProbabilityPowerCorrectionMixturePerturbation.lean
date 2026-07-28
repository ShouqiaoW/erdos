import Erdos390.Full.FiniteProbabilityMixturePerturbation

/-!
# Prime-power correction perturbations for tagged mixtures

The full-minus-squarefree covariance is the sum of the `JI`, `IJ`, and
`JJ` orientations.  This file packages only that exact covariance algebra.
All component first-moment and covariance-row losses remain explicit, so a
later arithmetic specialization can retain the extra reciprocal power.
-/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbability

noncomputable section

variable {Cell I : Type*} [Fintype Cell] [Fintype I]
  {Omega Theta : Cell → Type*}
  [∀ c, Fintype (Omega c)] [∀ c, Fintype (Theta c)]

/-- Componentwise perturbation budgets for the three prime-power
orientations pass through an arbitrary common tagged mixture, including all
between-component covariance terms. -/
theorem sum_abs_sigmaMixture_powerCorrectionOrientations_sub_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (IpMu JpMu : ∀ c, Omega c → ℝ)
    (IpNu JpNu : ∀ c, Theta c → ℝ)
    (IqMu JqMu : ∀ c, I → Omega c → ℝ)
    (IqNu JqNu : ∀ c, I → Theta c → ℝ)
    {AIp AJp AIrow AJrow dIp dJp dIrow dJrow dJI dIJ dJJ : ℝ}
    (hAIp : 0 ≤ AIp) (hAJp : 0 ≤ AJp)
    (hAIrow : 0 ≤ AIrow) (hAJrow : 0 ≤ AJrow)
    (hdIp : 0 ≤ dIp) (hdJp : 0 ≤ dJp)
    (hIpBase : ∀ c, |(mu c).expect (IpMu c)| ≤ AIp)
    (hJpBase : ∀ c, |(mu c).expect (JpMu c)| ≤ AJp)
    (hIqBase : ∀ c, ∑ i, |(mu c).expect (IqMu c i)| ≤ AIrow)
    (hJqBase : ∀ c, ∑ i, |(mu c).expect (JqMu c i)| ≤ AJrow)
    (hIpDiff : ∀ c,
      |(nu c).expect (IpNu c) - (mu c).expect (IpMu c)| ≤ dIp)
    (hJpDiff : ∀ c,
      |(nu c).expect (JpNu c) - (mu c).expect (JpMu c)| ≤ dJp)
    (hIqDiff : ∀ c, ∑ i,
      |(nu c).expect (IqNu c i) - (mu c).expect (IqMu c i)| ≤ dIrow)
    (hJqDiff : ∀ c, ∑ i,
      |(nu c).expect (JqNu c i) - (mu c).expect (JqMu c i)| ≤ dJrow)
    (hJICovDiff : ∀ c, ∑ i,
      |(nu c).covariance (JpNu c) (IqNu c i) -
        (mu c).covariance (JpMu c) (IqMu c i)| ≤ dJI)
    (hIJCovDiff : ∀ c, ∑ i,
      |(nu c).covariance (IpNu c) (JqNu c i) -
        (mu c).covariance (IpMu c) (JqMu c i)| ≤ dIJ)
    (hJJCovDiff : ∀ c, ∑ i,
      |(nu c).covariance (JpNu c) (JqNu c i) -
        (mu c).covariance (JpMu c) (JqMu c i)| ≤ dJJ) :
    let Mu := sigmaMixture weight mu
    let Nu := sigmaMixture weight nu
    let IpM : Sigma Omega → ℝ := fun x ↦ IpMu x.1 x.2
    let JpM : Sigma Omega → ℝ := fun x ↦ JpMu x.1 x.2
    let IqM : I → Sigma Omega → ℝ := fun i x ↦ IqMu x.1 i x.2
    let JqM : I → Sigma Omega → ℝ := fun i x ↦ JqMu x.1 i x.2
    let IpN : Sigma Theta → ℝ := fun x ↦ IpNu x.1 x.2
    let JpN : Sigma Theta → ℝ := fun x ↦ JpNu x.1 x.2
    let IqN : I → Sigma Theta → ℝ := fun i x ↦ IqNu x.1 i x.2
    let JqN : I → Sigma Theta → ℝ := fun i x ↦ JqNu x.1 i x.2
    ∑ i,
      |((Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)))| ≤
      (dJI + 2 * ((AJp + dJp) * dIrow + AIrow * dJp)) +
      (dIJ + 2 * ((AIp + dIp) * dJrow + AJrow * dIp)) +
      (dJJ + 2 * ((AJp + dJp) * dJrow + AJrow * dJp)) := by
  dsimp only
  let Mu := sigmaMixture weight mu
  let Nu := sigmaMixture weight nu
  let IpM : Sigma Omega → ℝ := fun x ↦ IpMu x.1 x.2
  let JpM : Sigma Omega → ℝ := fun x ↦ JpMu x.1 x.2
  let IqM : I → Sigma Omega → ℝ := fun i x ↦ IqMu x.1 i x.2
  let JqM : I → Sigma Omega → ℝ := fun i x ↦ JqMu x.1 i x.2
  let IpN : Sigma Theta → ℝ := fun x ↦ IpNu x.1 x.2
  let JpN : Sigma Theta → ℝ := fun x ↦ JpNu x.1 x.2
  let IqN : I → Sigma Theta → ℝ := fun i x ↦ IqNu x.1 i x.2
  let JqN : I → Sigma Theta → ℝ := fun i x ↦ JqNu x.1 i x.2
  have hJI := sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    weight mu nu JpMu JpNu IqMu IqNu hAJp hAIrow hdJp
    hJpBase hIqBase hJpDiff hIqDiff hJICovDiff
  have hIJ := sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    weight mu nu IpMu IpNu JqMu JqNu hAIp hAJrow hdIp
    hIpBase hJqBase hIpDiff hJqDiff hIJCovDiff
  have hJJ := sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    weight mu nu JpMu JpNu JqMu JqNu hAJp hAJrow hdJp
    hJpBase hJqBase hJpDiff hJqDiff hJJCovDiff
  have hpoint (i : I) :
      |((Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)))| ≤
        |Nu.covariance JpN (IqN i) - Mu.covariance JpM (IqM i)| +
        |Nu.covariance IpN (JqN i) - Mu.covariance IpM (JqM i)| +
        |Nu.covariance JpN (JqN i) - Mu.covariance JpM (JqM i)| := by
    let x := Nu.covariance JpN (IqN i) - Mu.covariance JpM (IqM i)
    let y := Nu.covariance IpN (JqN i) - Mu.covariance IpM (JqM i)
    let z := Nu.covariance JpN (JqN i) - Mu.covariance JpM (JqM i)
    have heq :
        (Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)) = x + y + z := by
      dsimp only [x, y, z]
      ring
    rw [heq]
    exact (abs_add_le (x + y) z).trans
      (add_le_add (abs_add_le x y) (le_refl _))
  calc
    ∑ i,
      |((Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)))| ≤
        ∑ i, (|Nu.covariance JpN (IqN i) -
              Mu.covariance JpM (IqM i)| +
            |Nu.covariance IpN (JqN i) -
              Mu.covariance IpM (JqM i)| +
            |Nu.covariance JpN (JqN i) -
              Mu.covariance JpM (JqM i)|) :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = (∑ i, |Nu.covariance JpN (IqN i) -
            Mu.covariance JpM (IqM i)|) +
        (∑ i, |Nu.covariance IpN (JqN i) -
            Mu.covariance IpM (JqM i)|) +
        (∑ i, |Nu.covariance JpN (JqN i) -
            Mu.covariance JpM (JqM i)|) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add (add_le_add hJI hIJ) hJJ

open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw

/-- Bounded-valuation-law specialization of the preceding tagged-mixture
identity.  The conclusion is stated directly for the literal
`(covVV-covII)` rows, so no orientation algebra is left to an application. -/
theorem sum_abs_boundedValuationSigmaMixture_powerCorrection_sub_le
    {M : ℕ}
    (weight : FiniteProbability Cell)
    (lawMu : ∀ c, BoundedValuationLaw (Omega c) M)
    (lawNu : ∀ c, BoundedValuationLaw (Theta c) M)
    (p : ℕ) (q : I → ℕ)
    {AIp AJp AIrow AJrow dIp dJp dIrow dJrow dJI dIJ dJJ : ℝ}
    (hAIp : 0 ≤ AIp) (hAJp : 0 ≤ AJp)
    (hAIrow : 0 ≤ AIrow) (hAJrow : 0 ≤ AJrow)
    (hdIp : 0 ≤ dIp) (hdJp : 0 ≤ dJp)
    (hIpBase : ∀ c,
      |(lawMu c).probability.expect ((lawMu c).I p)| ≤ AIp)
    (hJpBase : ∀ c,
      |(lawMu c).probability.expect ((lawMu c).J p)| ≤ AJp)
    (hIqBase : ∀ c, ∑ i,
      |(lawMu c).probability.expect ((lawMu c).I (q i))| ≤ AIrow)
    (hJqBase : ∀ c, ∑ i,
      |(lawMu c).probability.expect ((lawMu c).J (q i))| ≤ AJrow)
    (hIpDiff : ∀ c,
      |(lawNu c).probability.expect ((lawNu c).I p) -
        (lawMu c).probability.expect ((lawMu c).I p)| ≤ dIp)
    (hJpDiff : ∀ c,
      |(lawNu c).probability.expect ((lawNu c).J p) -
        (lawMu c).probability.expect ((lawMu c).J p)| ≤ dJp)
    (hIqDiff : ∀ c, ∑ i,
      |(lawNu c).probability.expect ((lawNu c).I (q i)) -
        (lawMu c).probability.expect ((lawMu c).I (q i))| ≤ dIrow)
    (hJqDiff : ∀ c, ∑ i,
      |(lawNu c).probability.expect ((lawNu c).J (q i)) -
        (lawMu c).probability.expect ((lawMu c).J (q i))| ≤ dJrow)
    (hJICovDiff : ∀ c, ∑ i,
      |(lawNu c).probability.covariance
          ((lawNu c).J p) ((lawNu c).I (q i)) -
        (lawMu c).probability.covariance
          ((lawMu c).J p) ((lawMu c).I (q i))| ≤ dJI)
    (hIJCovDiff : ∀ c, ∑ i,
      |(lawNu c).probability.covariance
          ((lawNu c).I p) ((lawNu c).J (q i)) -
        (lawMu c).probability.covariance
          ((lawMu c).I p) ((lawMu c).J (q i))| ≤ dIJ)
    (hJJCovDiff : ∀ c, ∑ i,
      |(lawNu c).probability.covariance
          ((lawNu c).J p) ((lawNu c).J (q i)) -
        (lawMu c).probability.covariance
          ((lawMu c).J p) ((lawMu c).J (q i))| ≤ dJJ) :
    let Mu := BoundedValuationLaw.sigmaMixture weight lawMu
    let Nu := BoundedValuationLaw.sigmaMixture weight lawNu
    ∑ i, |(Nu.covVV p (q i) - Nu.covII p (q i)) -
        (Mu.covVV p (q i) - Mu.covII p (q i))| ≤
      (dJI + 2 * ((AJp + dJp) * dIrow + AIrow * dJp)) +
      (dIJ + 2 * ((AIp + dIp) * dJrow + AJrow * dIp)) +
      (dJJ + 2 * ((AJp + dJp) * dJrow + AJrow * dJp)) := by
  dsimp only
  let Mu := BoundedValuationLaw.sigmaMixture weight lawMu
  let Nu := BoundedValuationLaw.sigmaMixture weight lawNu
  have hraw := sum_abs_sigmaMixture_powerCorrectionOrientations_sub_le
    weight (fun c ↦ (lawMu c).probability)
      (fun c ↦ (lawNu c).probability)
      (fun c ↦ (lawMu c).I p) (fun c ↦ (lawMu c).J p)
      (fun c ↦ (lawNu c).I p) (fun c ↦ (lawNu c).J p)
      (fun c i ↦ (lawMu c).I (q i))
      (fun c i ↦ (lawMu c).J (q i))
      (fun c i ↦ (lawNu c).I (q i))
      (fun c i ↦ (lawNu c).J (q i))
      hAIp hAJp hAIrow hAJrow hdIp hdJp
      hIpBase hJpBase hIqBase hJqBase hIpDiff hJpDiff
      hIqDiff hJqDiff hJICovDiff hIJCovDiff hJJCovDiff
  have hNu (i : I) :
      Nu.covVV p (q i) - Nu.covII p (q i) =
        Nu.covJI p (q i) + Nu.covIJ p (q i) + Nu.covJJ p (q i) :=
    Nu.covVV_sub_covII p (q i)
  have hMu (i : I) :
      Mu.covVV p (q i) - Mu.covII p (q i) =
        Mu.covJI p (q i) + Mu.covIJ p (q i) + Mu.covJJ p (q i) :=
    Mu.covVV_sub_covII p (q i)
  simpa only [Mu, Nu, hNu, hMu] using hraw

end

end Erdos390.Full.FiniteProbability
