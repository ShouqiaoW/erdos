import Erdos390.Full.PrimePowerCovariance
import Erdos390.Lemma75

/-!
# Actual finite-law row contraction for prime powers

The original finite contraction theorem in `Erdos390.Lemma75` is pure
finite-sum algebra, but it was stated for the audit companion's duplicate
probability structure.  This file transports that theorem definitionally to
the genuine `Full.FiniteProbability` and then specializes it to the actual
valuation columns of `BoundedValuationLaw`.

No analytic covariance estimate is asserted here.  The point is that once the
actual `JI`, `IJ`, `JJ`, diagonal, prime-sum, and endpoint bounds are proved,
their contraction to the paper's full-valuation row norm is now a theorem
about the same probability law and the same valuation functions.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerRowTransfer

noncomputable section

open Erdos390.Full
open Erdos390.Full.PrimePowerCovariance

variable {Omega Iota : Type*} [Fintype Omega]

set_option maxHeartbeats 800000

/-- The duplicate audit probability structure has exactly the same data as
the full finite probability structure. -/
def toLegacyProbability (mu : Erdos390.Full.FiniteProbability Omega) :
    Erdos390.Lemma75.FiniteProbability Omega where
  mass := mu.mass
  mass_nonneg := mu.mass_nonneg
  mass_sum := mu.mass_sum

@[simp] theorem toLegacyProbability_expect
    (mu : Erdos390.Full.FiniteProbability Omega) (F : Omega -> Real) :
    (toLegacyProbability mu).expect F = mu.expect F := rfl

@[simp] theorem toLegacyProbability_covariance
    (mu : Erdos390.Full.FiniteProbability Omega) (F G : Omega -> Real) :
    (toLegacyProbability mu).covariance F G = mu.covariance F G := rfl

/-- The finite row contraction, now stated for the probability type used by
all actual structured-cell and exponential-tilt modules. -/
theorem row_primePower_transfer
    [DecidableEq Iota]
    (mu : Erdos390.Full.FiniteProbability Omega) (P : Finset Iota)
    (I J : Iota -> Omega -> Real) (t u rowScale : Iota -> Real)
    (C epsilon invW HT H1 H2 remRow : Real)
    (rJI rIJ rJJ : Iota -> Iota -> Real) (rD : Iota -> Real)
    (hC : 0 <= C) (hepsilon : 0 <= epsilon)
    (hinv0 : 0 <= invW) (hinv1 : invW <= 1)
    (ht0 : ∀ i ∈ P, 0 <= t i) (ht1 : ∀ i ∈ P, t i <= 1)
    (hu0 : ∀ i ∈ P, 0 <= u i) (huW : ∀ i ∈ P, u i <= invW)
    (hscale0 : ∀ i ∈ P, 0 <= rowScale i)
    (hscale : ∀ i ∈ P, rowScale i * u i = 1)
    (hI0 : ∀ i ∈ P, ∀ omega, 0 <= I i omega)
    (hI1 : ∀ i ∈ P, ∀ omega, I i omega <= 1)
    (hJ0 : ∀ i ∈ P, ∀ omega, 0 <= J i omega)
    (hJsq : ∀ i ∈ P, ∀ omega, J i omega <= J i omega ^ 2)
    (hIJpoint : ∀ i ∈ P, ∀ omega, I i omega * J i omega = J i omega)
    (hJI : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |mu.covariance (J i) (I j)| <=
        C * t i * t j * u i ^ 2 * u j +
          epsilon * u i ^ 2 * u j + rJI i j)
    (hIJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |mu.covariance (I i) (J j)| <=
        C * t i * t j * u i * u j ^ 2 +
          epsilon * u i * u j ^ 2 + rIJ i j)
    (hJJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |mu.covariance (J i) (J j)| <=
        C * t i * t j * u i ^ 2 * u j ^ 2 +
          epsilon * u i ^ 2 * u j ^ 2 + rJJ i j)
    (hMoment : ∀ i ∈ P,
      mu.expect (fun omega => J i omega ^ 2) <=
        (C + epsilon) * u i ^ 2 + rD i)
    (hTsum : (∑ j ∈ P, t j * u j) <= HT)
    (hUsum : (∑ j ∈ P, u j) <= H1)
    (hU2sum : (∑ j ∈ P, u j ^ 2) <= H2 * invW)
    (hRowRem : ∀ i ∈ P,
      rowScale i *
        ((∑ j ∈ P.erase i, (rJI i j + rIJ i j + rJJ i j)) +
          3 * rD i) <= remRow) :
    ∀ i ∈ P,
      rowScale i * ∑ j ∈ P,
        |mu.covariance (fun omega => I i omega + J i omega)
            (fun omega => I j omega + J j omega) -
          mu.covariance (I i) (I j)| <=
      C * (HT + 2 * H2 + 3) * invW +
        epsilon * (H1 + 2 * H2 + 3) * invW + remRow := by
  let muLegacy := toLegacyProbability mu
  have hJI' : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |muLegacy.covariance (J i) (I j)| <=
        C * t i * t j * u i ^ 2 * u j +
          epsilon * u i ^ 2 * u j + rJI i j := by
    simpa only [muLegacy, toLegacyProbability_covariance] using hJI
  have hIJ' : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |muLegacy.covariance (I i) (J j)| <=
        C * t i * t j * u i * u j ^ 2 +
          epsilon * u i * u j ^ 2 + rIJ i j := by
    simpa only [muLegacy, toLegacyProbability_covariance] using hIJ
  have hJJ' : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |muLegacy.covariance (J i) (J j)| <=
        C * t i * t j * u i ^ 2 * u j ^ 2 +
          epsilon * u i ^ 2 * u j ^ 2 + rJJ i j := by
    simpa only [muLegacy, toLegacyProbability_covariance] using hJJ
  have hMoment' : ∀ i ∈ P,
      muLegacy.expect (fun omega => J i omega ^ 2) <=
        (C + epsilon) * u i ^ 2 + rD i := by
    simpa only [muLegacy, toLegacyProbability_expect] using hMoment
  simpa only [muLegacy, toLegacyProbability_covariance] using
    (Erdos390.Lemma75.row_primePower_transfer
      muLegacy P I J t u rowScale C epsilon invW HT H1 H2 remRow
      rJI rIJ rJJ rD hC hepsilon hinv0 hinv1 ht0 ht1 hu0 huW
      hscale0 hscale hI0 hI1 hJ0 hJsq hIJpoint hJI' hIJ' hJJ'
      hMoment' hTsum hUsum hU2sum hRowRem)

namespace BoundedValuationLaw

variable {M : Nat} (law : BoundedValuationLaw Omega M)

/-- Specialization of the row contraction to the literal columns
`V_p = v_p(m)`, `I_p = 1_{p|m}`, and `J_p = V_p-I_p` of the actual bounded
integer-valued law. -/
theorem covVV_sub_covII_row_le
    (P : Finset Nat) (t u rowScale : Nat -> Real)
    (C epsilon invW HT H1 H2 remRow : Real)
    (rJI rIJ rJJ : Nat -> Nat -> Real) (rD : Nat -> Real)
    (hPrime : ∀ p ∈ P, p.Prime)
    (hC : 0 <= C) (hepsilon : 0 <= epsilon)
    (hinv0 : 0 <= invW) (hinv1 : invW <= 1)
    (ht0 : ∀ p ∈ P, 0 <= t p) (ht1 : ∀ p ∈ P, t p <= 1)
    (hu0 : ∀ p ∈ P, 0 <= u p) (huW : ∀ p ∈ P, u p <= invW)
    (hscale0 : ∀ p ∈ P, 0 <= rowScale p)
    (hscale : ∀ p ∈ P, rowScale p * u p = 1)
    (hJI : ∀ p ∈ P, ∀ q ∈ P.erase p,
      |law.covJI p q| <=
        C * t p * t q * u p ^ 2 * u q +
          epsilon * u p ^ 2 * u q + rJI p q)
    (hIJ : ∀ p ∈ P, ∀ q ∈ P.erase p,
      |law.covIJ p q| <=
        C * t p * t q * u p * u q ^ 2 +
          epsilon * u p * u q ^ 2 + rIJ p q)
    (hJJ : ∀ p ∈ P, ∀ q ∈ P.erase p,
      |law.covJJ p q| <=
        C * t p * t q * u p ^ 2 * u q ^ 2 +
          epsilon * u p ^ 2 * u q ^ 2 + rJJ p q)
    (hMoment : ∀ p ∈ P,
      law.probability.expect (fun omega => law.J p omega ^ 2) <=
        (C + epsilon) * u p ^ 2 + rD p)
    (hTsum : (∑ q ∈ P, t q * u q) <= HT)
    (hUsum : (∑ q ∈ P, u q) <= H1)
    (hU2sum : (∑ q ∈ P, u q ^ 2) <= H2 * invW)
    (hRowRem : ∀ p ∈ P,
      rowScale p *
        ((∑ q ∈ P.erase p, (rJI p q + rIJ p q + rJJ p q)) +
          3 * rD p) <= remRow) :
    ∀ p ∈ P,
      rowScale p * ∑ q ∈ P,
        |law.covVV p q - law.covII p q| <=
      C * (HT + 2 * H2 + 3) * invW +
        epsilon * (H1 + 2 * H2 + 3) * invW + remRow := by
  have hrow := row_primePower_transfer law.probability P law.I law.J
    t u rowScale C epsilon invW HT H1 H2 remRow rJI rIJ rJJ rD
    hC hepsilon hinv0 hinv1 ht0 ht1 hu0 huW hscale0 hscale
    (fun p hp omega => law.I_nonneg p omega)
    (fun p hp omega => law.I_le_one p omega)
    (fun p hp omega => law.J_nonneg (hPrime p hp) omega)
    (fun p hp omega => law.J_le_sq (hPrime p hp) omega)
    (fun p hp omega => law.I_mul_J p omega)
    (by simpa only [BoundedValuationLaw.covJI] using hJI)
    (by simpa only [BoundedValuationLaw.covIJ] using hIJ)
    (by simpa only [BoundedValuationLaw.covJJ] using hJJ)
    hMoment hTsum hUsum hU2sum hRowRem
  intro p hp
  have hpRow := hrow p hp
  have hfull (a b : Nat) :
      law.probability.covariance
          (fun omega => law.I a omega + law.J a omega)
          (fun omega => law.I b omega + law.J b omega) =
        law.covVV a b := by
    rw [← law.V_eq_I_add_J a, ← law.V_eq_I_add_J b]
    rfl
  simpa only [hfull, BoundedValuationLaw.covII] using hpRow

end BoundedValuationLaw

end

end Erdos390.Full.PrimePowerRowTransfer
