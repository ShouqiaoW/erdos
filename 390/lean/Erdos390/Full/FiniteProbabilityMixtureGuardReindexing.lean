import Erdos390.Full.FiniteProbabilityMixture
import Erdos390.Full.GuardDeletionReindexing

/-!
# Exact guard reindexing for tagged mixtures

Guard perturbation estimates are most naturally stated on the original cell,
where deleted points have mass zero.  The bridge is carried by the literal
difference-finset subtype.  This file lifts the exact component reindexing to
an arbitrary tagged mixture, including its between-component covariance.
-/

namespace Erdos390.Full.GuardedUniformCell

open FiniteProbability

noncomputable section

variable {Cell Alpha : Type*} [Fintype Cell] [DecidableEq Alpha]

/-- Exact expectation reindexing after componentwise guard deletion and
arbitrary common mixing. -/
theorem sigmaMixture_deleteGuards_expect_remaining_eq
    (S G : Cell → Finset Alpha)
    (hS : ∀ c, (S c).Nonempty) (hR : ∀ c, (S c \ G c).Nonempty)
    (score : ∀ c, S c → ℝ)
    (hsmall : ∀ c,
      ((uniformOnFinset (S c) (hS c)).exponentialTilt (score c)).guardMass
        (guardSubtype (S c) (G c)) < 1)
    (weight : FiniteProbability Cell)
    (F : ∀ c, S c → ℝ) :
    let raw : ∀ c, FiniteProbability (S c) := fun c ↦
      (uniformOnFinset (S c) (hS c)).exponentialTilt (score c)
    let deleted : ∀ c, FiniteProbability (S c) := fun c ↦
      (raw c).deleteGuards (guardSubtype (S c) (G c)) (hsmall c)
    let remaining : ∀ c, FiniteProbability ↑(S c \ G c) := fun c ↦
      (uniformOnFinset (S c \ G c) (hR c)).exponentialTilt
        (fun z ↦ score c (remainingEmbedding (S c) (G c) z))
    (sigmaMixture weight deleted).expect (fun x ↦ F x.1 x.2) =
      (sigmaMixture weight remaining).expect
        (fun x ↦ F x.1 (remainingEmbedding (S x.1) (G x.1) x.2)) := by
  dsimp only
  rw [sigmaMixture_expect, sigmaMixture_expect]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  exact deleteGuards_tilted_uniform_expect_remaining_eq
    (S c) (G c) (hS c) (hR c) (score c) (hsmall c) (F c)

/-- Exact covariance reindexing for the complete tagged mixture. -/
theorem sigmaMixture_deleteGuards_covariance_remaining_eq
    (S G : Cell → Finset Alpha)
    (hS : ∀ c, (S c).Nonempty) (hR : ∀ c, (S c \ G c).Nonempty)
    (score : ∀ c, S c → ℝ)
    (hsmall : ∀ c,
      ((uniformOnFinset (S c) (hS c)).exponentialTilt (score c)).guardMass
        (guardSubtype (S c) (G c)) < 1)
    (weight : FiniteProbability Cell)
    (F H : ∀ c, S c → ℝ) :
    let raw : ∀ c, FiniteProbability (S c) := fun c ↦
      (uniformOnFinset (S c) (hS c)).exponentialTilt (score c)
    let deleted : ∀ c, FiniteProbability (S c) := fun c ↦
      (raw c).deleteGuards (guardSubtype (S c) (G c)) (hsmall c)
    let remaining : ∀ c, FiniteProbability ↑(S c \ G c) := fun c ↦
      (uniformOnFinset (S c \ G c) (hR c)).exponentialTilt
        (fun z ↦ score c (remainingEmbedding (S c) (G c) z))
    (sigmaMixture weight deleted).covariance
        (fun x ↦ F x.1 x.2) (fun x ↦ H x.1 x.2) =
      (sigmaMixture weight remaining).covariance
        (fun x ↦ F x.1 (remainingEmbedding (S x.1) (G x.1) x.2))
        (fun x ↦ H x.1 (remainingEmbedding (S x.1) (G x.1) x.2)) := by
  dsimp only
  unfold FiniteProbability.covariance
  rw [sigmaMixture_deleteGuards_expect_remaining_eq
      S G hS hR score hsmall weight F,
    sigmaMixture_deleteGuards_expect_remaining_eq
      S G hS hR score hsmall weight H]
  let FH : ∀ c, S c → ℝ := fun c x ↦ F c x * H c x
  have hFH := sigmaMixture_deleteGuards_expect_remaining_eq
    S G hS hR score hsmall weight FH
  dsimp only [FH] at hFH
  rw [hFH]

end

end Erdos390.Full.GuardedUniformCell
