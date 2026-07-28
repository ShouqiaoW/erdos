import Erdos390.Full.GuardDeletionReindexing
import Erdos390.Full.SquarefreeCovarianceReference

/-!
# Reciprocal signed profiles after guard deletion

For the signed squarefree comparison only divisors `p` and `pq` occur.
Although deleting guards first gives an additive probability error, the
paper census is much smaller than `1/y²`; multiplying by the explicit
`y²` factor therefore restores the required reciprocal scale.  This file
records the exact finite step, including renormalization.
-/

namespace Erdos390.Full.GuardDeletionSquarefreeProfiles

open ArithmeticModel Scale FiniteProbability GuardedUniformCell
open OmittedTiltPairChamber PaperPrimePowerChamberError
open PaperScaleMarkedCell

noncomputable section

/-- The explicit reciprocal-profile cost of deleting guards from one cell. -/
def guardSquarefreeError
    (S G : Finset ℕ) (scoreBound : ℝ) (n : ℕ) : ℝ :=
  2 * (Real.exp (2 * scoreBound) * (G.card : ℝ) / (S.card : ℝ)) *
    (yNat n : ℝ) ^ 2

theorem guardSquarefreeError_nonneg
    (S G : Finset ℕ) (scoreBound : ℝ) (n : ℕ) :
    0 ≤ guardSquarefreeError S G scoreBound n := by
  unfold guardSquarefreeError
  positivity

/-- A common signed squarefree profile survives literal conditional guard
deletion.  The proof constructs the conditional law and includes the two
mean-renormalization losses through `abs_deleteGuards_expect_sub_le`; no
total-variation assertion is assumed. -/
theorem exists_deleteGuards_squarefree_profiles
    (S G : Finset ℕ) (hS : S.Nonempty)
    (score : S → ℝ) (K : ℝ) (hscore : ∀ x, |score x| ≤ K)
    {n W : ℕ} {E : ℝ}
    (hsmallCensus :
      Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ) ≤ (1 : ℝ) / 2)
    (hpair : ∀ p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p →
      |((uniformOnFinset S hS).exponentialTilt score).expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q 1 1)| ≤
          E * pairWeight p q 1 1)
    (hsingle : ∀ p, p ∈ primeBand n W →
      |((uniformOnFinset S hS).exponentialTilt score).expect
          (fun m ↦ divInd p (m : ℕ)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1) :
    ∃ hsmall :
        ((uniformOnFinset S hS).exponentialTilt score).guardMass
          (guardSubtype S G) < 1,
      let deleted :=
        ((uniformOnFinset S hS).exponentialTilt score).deleteGuards
          (guardSubtype S G) hsmall
      (∀ p, p ∈ primeBand n W →
        ∀ q, q ∈ (primeBand n W).erase p →
        |deleted.expect
            (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
          paperDivisibilityMain n (pairPower p q 1 1)| ≤
            (E + guardSquarefreeError S G K n) * pairWeight p q 1 1) ∧
      (∀ p, p ∈ primeBand n W →
        |deleted.expect (fun m ↦ divInd p (m : ℕ)) -
          paperDivisibilityMain n p| ≤
            (E + guardSquarefreeError S G K n) * singleWeight p 1) := by
  let mu := (uniformOnFinset S hS).exponentialTilt score
  let guards := guardSubtype S G
  let delta := Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ)
  have hmass : mu.guardMass guards ≤ delta := by
    simpa only [mu, guards, delta] using
      tilted_uniform_guardMass_le S G hS score K hscore
  have hhalf : mu.guardMass guards ≤ (1 : ℝ) / 2 :=
    hmass.trans hsmallCensus
  have hsmall : mu.guardMass guards < 1 := by linarith
  refine ⟨hsmall, ?_, ?_⟩
  · intro p hp q hq
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hq).2
    have hpPrime := prime_of_mem_primeBand hp
    have hqPrime := prime_of_mem_primeBand hqBand
    have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hp
    have hqY : q ≤ yNat n := le_yNat_of_mem_primeBand hqBand
    have hpPosR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hqPosR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqPrime.pos
    have hpqPosR : (0 : ℝ) < (p : ℝ) * (q : ℝ) :=
      mul_pos hpPosR hqPosR
    have hpqY : (p : ℝ) * (q : ℝ) ≤ (yNat n : ℝ) ^ 2 := by
      have hnat : p * q ≤ yNat n * yNat n := Nat.mul_le_mul hpY hqY
      exact_mod_cast (by simpa only [pow_two] using hnat)
    have hdelta0 : 0 ≤ delta := by
      dsimp only [delta]
      positivity
    have hdiff :
        |(mu.deleteGuards guards hsmall).expect
              (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
            mu.expect (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))| ≤
          4 * delta := by
      have hraw := mu.abs_deleteGuards_expect_sub_le guards hsmall
        (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))
        (show 0 ≤ (1 : ℝ) by norm_num)
        (fun m ↦ by
          rw [abs_of_nonneg (divInd_nonneg _ _)]
          exact divInd_le_one _ _)
      have hperturb := mu.guardPerturbation_le_four_mul_guardMass
        guards hhalf
      exact hraw.trans ((mul_le_mul_of_nonneg_left
        (hperturb.trans (mul_le_mul_of_nonneg_left hmass (by norm_num)))
        (by norm_num)).trans_eq (by ring))
    have habsorb : 4 * delta ≤
        guardSquarefreeError S G K n * pairWeight p q 1 1 := by
      have hmul : 4 * delta * ((p : ℝ) * (q : ℝ)) ≤
          (2 * delta * (yNat n : ℝ) ^ 2) * 4 := by
        have hleft : 4 * delta * ((p : ℝ) * (q : ℝ)) ≤
            4 * delta * (yNat n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hpqY
            (mul_nonneg (by norm_num) hdelta0)
        nlinarith
      unfold guardSquarefreeError pairWeight
      norm_num
      change 4 * delta ≤
        (2 * delta * (yNat n : ℝ) ^ 2) *
          (4 / ((p : ℝ) * (q : ℝ)))
      rw [show (2 * delta * (yNat n : ℝ) ^ 2) *
          (4 / ((p : ℝ) * (q : ℝ))) =
        ((2 * delta * (yNat n : ℝ) ^ 2) * 4) /
          ((p : ℝ) * (q : ℝ)) by ring]
      exact (le_div_iff₀ hpqPosR).2 hmul
    calc
      |(mu.deleteGuards guards hsmall).expect
            (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
          paperDivisibilityMain n (pairPower p q 1 1)| ≤
        |(mu.deleteGuards guards hsmall).expect
              (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
            mu.expect (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))| +
          |mu.expect (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
            paperDivisibilityMain n (pairPower p q 1 1)| := by
          calc
            _ = |((mu.deleteGuards guards hsmall).expect
                    (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
                  mu.expect (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))) +
                (mu.expect (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
                  paperDivisibilityMain n (pairPower p q 1 1))| := by ring_nf
            _ ≤ _ := abs_add_le _ _
      _ ≤ guardSquarefreeError S G K n * pairWeight p q 1 1 +
          E * pairWeight p q 1 1 := add_le_add (hdiff.trans habsorb) (hpair p hp q hq)
      _ = (E + guardSquarefreeError S G K n) * pairWeight p q 1 1 := by ring
  · intro p hp
    have hpPrime := prime_of_mem_primeBand hp
    have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hp
    have hyPos : 0 < yNat n := hpPrime.pos.trans_le hpY
    have hpPosR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hpYsq : (p : ℝ) ≤ (yNat n : ℝ) ^ 2 := by
      exact_mod_cast (calc
        p ≤ yNat n := hpY
        _ ≤ yNat n ^ 2 := by nlinarith)
    have hdelta0 : 0 ≤ delta := by
      dsimp only [delta]
      positivity
    have hdiff :
        |(mu.deleteGuards guards hsmall).expect
              (fun m ↦ divInd p (m : ℕ)) -
            mu.expect (fun m ↦ divInd p (m : ℕ))| ≤ 4 * delta := by
      have hraw := mu.abs_deleteGuards_expect_sub_le guards hsmall
        (fun m ↦ divInd p (m : ℕ))
        (show 0 ≤ (1 : ℝ) by norm_num)
        (fun m ↦ by
          rw [abs_of_nonneg (divInd_nonneg _ _)]
          exact divInd_le_one _ _)
      have hperturb := mu.guardPerturbation_le_four_mul_guardMass guards hhalf
      exact hraw.trans ((mul_le_mul_of_nonneg_left
        (hperturb.trans (mul_le_mul_of_nonneg_left hmass (by norm_num)))
        (by norm_num)).trans_eq (by ring))
    have habsorb : 4 * delta ≤
        guardSquarefreeError S G K n * singleWeight p 1 := by
      have hmul : 4 * delta * (p : ℝ) ≤
          (2 * delta * (yNat n : ℝ) ^ 2) * 2 := by
        have hleft : 4 * delta * (p : ℝ) ≤
            4 * delta * (yNat n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hpYsq
            (mul_nonneg (by norm_num) hdelta0)
        nlinarith
      unfold guardSquarefreeError singleWeight
      norm_num
      change 4 * delta ≤
        (2 * delta * (yNat n : ℝ) ^ 2) * (2 / (p : ℝ))
      rw [show (2 * delta * (yNat n : ℝ) ^ 2) * (2 / (p : ℝ)) =
        ((2 * delta * (yNat n : ℝ) ^ 2) * 2) / (p : ℝ) by ring]
      exact (le_div_iff₀ hpPosR).2 hmul
    calc
      |(mu.deleteGuards guards hsmall).expect (fun m ↦ divInd p (m : ℕ)) -
          paperDivisibilityMain n p| ≤
        |(mu.deleteGuards guards hsmall).expect (fun m ↦ divInd p (m : ℕ)) -
            mu.expect (fun m ↦ divInd p (m : ℕ))| +
          |mu.expect (fun m ↦ divInd p (m : ℕ)) -
            paperDivisibilityMain n p| := by
          calc
            _ = |((mu.deleteGuards guards hsmall).expect
                    (fun m ↦ divInd p (m : ℕ)) -
                  mu.expect (fun m ↦ divInd p (m : ℕ))) +
                (mu.expect (fun m ↦ divInd p (m : ℕ)) -
                  paperDivisibilityMain n p)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
      _ ≤ guardSquarefreeError S G K n * singleWeight p 1 +
          E * singleWeight p 1 := add_le_add (hdiff.trans habsorb) (hsingle p hp)
      _ = (E + guardSquarefreeError S G K n) * singleWeight p 1 := by ring

/-- Reindex the preceding result to the literal subtype of the difference
finset used by the bridge sample. -/
theorem remaining_tilt_squarefree_profiles
    (S G : Finset ℕ) (hS : S.Nonempty) (hR : (S \ G).Nonempty)
    (score : S → ℝ) (K : ℝ) (hscore : ∀ x, |score x| ≤ K)
    {n W : ℕ} {E : ℝ}
    (hsmallCensus :
      Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ) ≤ (1 : ℝ) / 2)
    (hpair : ∀ p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p →
      |((uniformOnFinset S hS).exponentialTilt score).expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q 1 1)| ≤
          E * pairWeight p q 1 1)
    (hsingle : ∀ p, p ∈ primeBand n W →
      |((uniformOnFinset S hS).exponentialTilt score).expect
          (fun m ↦ divInd p (m : ℕ)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1) :
    let remaining := (uniformOnFinset (S \ G) hR).exponentialTilt
      (fun z ↦ score (remainingEmbedding S G z))
    (∀ p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p →
      |remaining.expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q 1 1)| ≤
          (E + guardSquarefreeError S G K n) * pairWeight p q 1 1) ∧
    (∀ p, p ∈ primeBand n W →
      |remaining.expect (fun m ↦ divInd p (m : ℕ)) -
        paperDivisibilityMain n p| ≤
          (E + guardSquarefreeError S G K n) * singleWeight p 1) := by
  dsimp only
  obtain ⟨hsmall, hpairDeleted, hsingleDeleted⟩ :=
    exists_deleteGuards_squarefree_profiles S G hS score K hscore
      hsmallCensus hpair hsingle
  constructor
  · intro p hp q hq
    have hreindex := deleteGuards_tilted_uniform_expect_remaining_eq
      S G hS hR score hsmall
      (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))
    have hdel := hpairDeleted p hp q hq
    rw [hreindex] at hdel
    simpa only [remainingEmbedding_value] using hdel
  · intro p hp
    have hreindex := deleteGuards_tilted_uniform_expect_remaining_eq
      S G hS hR score hsmall (fun m ↦ divInd p (m : ℕ))
    have hdel := hsingleDeleted p hp
    rw [hreindex] at hdel
    simpa only [remainingEmbedding_value] using hdel

end

end Erdos390.Full.GuardDeletionSquarefreeProfiles
