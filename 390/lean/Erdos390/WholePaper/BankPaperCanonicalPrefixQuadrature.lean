import Erdos390.WholePaper.BankPaperCanonicalPrefixAdapter
import Erdos390.Full.PrimeBandQuadrature

/-!
# Harmonic-prime majorants for the canonical prefix adapter

The prefix adapter reduces a signed ratio-cell prefix to the strict tail of
the declared pointwise residual bound.  In the paper that bound is a fixed
nonnegative scale times `1 / p`.  This file performs the remaining analytic
step from literal finite tails to the verified uniform Mertens estimate.

No distribution assertion about the ratio cells is built into the result.
The only geometric input says that every prime in a declared strict tail
lies in an explicit numerical interval `(A,Y]`.  The tail can be an arbitrary
subset of that interval; positivity then permits comparison with the full
prime harmonic sum.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

noncomputable section

/-- The paper pointwise shape after collecting all factors independent of
the prime label into one nonnegative scale.  It includes the specialization
`scale = C_tan * N / L`. -/
def bankPaperCanonicalHarmonicPointwiseUpper
    {n W : Nat} (scale : Real)
    (p : BankPaperCanonicalTangentPrime n W) : Real :=
  scale / (bankPaperCanonicalTangentPrimeLabel p : Real)

/-- Multiplying the paper pointwise majorant by its literal prime label
recovers the prime-independent scale exactly. -/
theorem bankPaperCanonicalTangentPrimeLabel_mul_harmonicPointwiseUpper
    {n W : Nat} (scale : Real)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        bankPaperCanonicalHarmonicPointwiseUpper scale p = scale := by
  have hp : (bankPaperCanonicalTangentPrimeLabel p : Real) ≠ 0 := by
    exact_mod_cast
      (bankPaperCanonicalTangentPrimeLabel_prime p).pos.ne'
  unfold bankPaperCanonicalHarmonicPointwiseUpper
  field_simp [hp]

/-- The unconditional endpoint majorant obtained from the uniform
reciprocal-prime quadrature theorem. -/
def bankPaperCanonicalHarmonicTailMajorant
    (scale : Real) (A Y : Nat) : Real :=
  scale *
    (Real.log (Real.log (Y : Real)) -
        Real.log (Real.log (A : Real)) +
      5 * fullReciprocalSumUniformConstant /
        Real.log (A : Real) ^ 3)

-- `WholePaper` also has a distinct presentation of `primesUpTo`; the
-- qualification here keeps this set definitionally aligned with
-- `Full.PrimeSums.fullReciprocalSum`.
private theorem bankPaperCanonical_primesUpTo_mono
    {A Y : Nat} (hAY : A <= Y) :
    Erdos390.Full.PrimeSums.primesUpTo A ⊆
      Erdos390.Full.PrimeSums.primesUpTo Y := by
  intro p hp
  simp only [Erdos390.Full.PrimeSums.primesUpTo,
    Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

private theorem bankPaperCanonical_reciprocalPrimeInterval_eq_sub
    {A Y : Nat} (hAY : A <= Y) :
    (∑ p ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
        Erdos390.Full.PrimeSums.primesUpTo A, 1 / (p : Real)) =
      fullReciprocalSum Y - fullReciprocalSum A := by
  have hsub := bankPaperCanonical_primesUpTo_mono hAY
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : Nat => 1 / (p : Real))
  unfold fullReciprocalSum
  exact (eq_sub_iff_add_eq).2 hsum

/-- An arbitrary strict ratio-cell tail with pointwise bound `scale / p` is
bounded by the full harmonic prime mass of any numerical interval containing
that tail.

The interval condition is deliberately one-sided: it does not assert that
the ratio-cell tail contains every prime in `(A,Y]`. -/
theorem tangentRatioCellTail_harmonicPointwiseUpper_le_fullReciprocalSum_sub
    {n W : Nat} {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (scale : Real) (hscale : 0 <= scale)
    (band : Band) (cut A Y : Nat) (hAY : A <= Y)
    (hgeometry : forall p : BankPaperCanonicalTangentPrime n W,
      bandOf p = band -> cut < cellIndex p ->
        A < bankPaperCanonicalTangentPrimeLabel p ∧
          bankPaperCanonicalTangentPrimeLabel p <= Y) :
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut <=
      scale * (fullReciprocalSum Y - fullReciprocalSum A) := by
  let tail : Finset (BankPaperCanonicalTangentPrime n W) :=
    Finset.univ.filter
      (fun p => bandOf p = band ∧ cut < cellIndex p)
  let labelEmbedding : BankPaperCanonicalTangentPrime n W ↪ Nat :=
    ⟨bankPaperCanonicalTangentPrimeLabel,
      bankPaperCanonicalTangentPrimeLabel_injective⟩
  let labels : Finset Nat := tail.map labelEmbedding
  have hlabels : labels ⊆
      Erdos390.Full.PrimeSums.primesUpTo Y \
        Erdos390.Full.PrimeSums.primesUpTo A := by
    intro q hq
    have hq' : q ∈ tail.map labelEmbedding := by
      simpa only [labels] using hq
    obtain ⟨p, hpTail, hpq⟩ := Finset.mem_map.mp hq'
    subst q
    have hpCondition : bandOf p = band ∧ cut < cellIndex p :=
      (Finset.mem_filter.mp hpTail).2
    have hpInterval := hgeometry p hpCondition.1 hpCondition.2
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simp only [Erdos390.Full.PrimeSums.primesUpTo,
        Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.zero_le _, hpInterval.2⟩,
        bankPaperCanonicalTangentPrimeLabel_prime p⟩
    · intro hpA
      simp only [Erdos390.Full.PrimeSums.primesUpTo,
        Finset.mem_filter, Finset.mem_Icc] at hpA
      exact (Nat.not_lt_of_ge hpA.1.2) hpInterval.1
  have htail :
      tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalHarmonicPointwiseUpper scale)
          bandOf cellIndex band cut =
        ∑ p ∈ tail,
          scale / (bankPaperCanonicalTangentPrimeLabel p : Real) := by
    simp only [tangentRatioCellTailPointwiseUpper,
      bankPaperCanonicalHarmonicPointwiseUpper, tail, Finset.sum_filter]
  have hmap :
      (∑ p ∈ tail,
          scale / (bankPaperCanonicalTangentPrimeLabel p : Real)) =
        ∑ q ∈ labels, scale / (q : Real) := by
    simp only [labels, Finset.sum_map]
    rfl
  have hsum :
      (∑ q ∈ labels, scale / (q : Real)) <=
        ∑ q ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
            Erdos390.Full.PrimeSums.primesUpTo A,
          scale / (q : Real) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hlabels
      (fun q _hq _hnot => div_nonneg hscale (Nat.cast_nonneg q))
  calc
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut =
      ∑ p ∈ tail,
        scale / (bankPaperCanonicalTangentPrimeLabel p : Real) := htail
    _ = ∑ q ∈ labels, scale / (q : Real) := hmap
    _ <= ∑ q ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
          Erdos390.Full.PrimeSums.primesUpTo A,
        scale / (q : Real) := hsum
    _ = scale *
        (∑ q ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
            Erdos390.Full.PrimeSums.primesUpTo A,
          1 / (q : Real)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring
    _ = scale * (fullReciprocalSum Y - fullReciprocalSum A) := by
      rw [bankPaperCanonical_reciprocalPrimeInterval_eq_sub hAY]

/-- Uniform log-log majorant for a literal canonical strict tail.  The same
global constant and cutoff work for every band, cut, and moving endpoint
pair satisfying the displayed geometry. -/
theorem tangentRatioCellTail_harmonicPointwiseUpper_le_uniformMajorant
    {n W : Nat} {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (scale : Real) (hscale : 0 <= scale)
    (band : Band) (cut A Y : Nat)
    (hA : fullReciprocalSumUniformCutoff <= A) (hAY : A <= Y)
    (hgeometry : forall p : BankPaperCanonicalTangentPrime n W,
      bandOf p = band -> cut < cellIndex p ->
        A < bankPaperCanonicalTangentPrimeLabel p ∧
          bankPaperCanonicalTangentPrimeLabel p <= Y) :
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut <=
      bankPaperCanonicalHarmonicTailMajorant scale A Y := by
  have hquadrature := fullReciprocalSumUniform_bound A Y hA hAY
  have hupper :
      fullReciprocalSum Y - fullReciprocalSum A <=
        Real.log (Real.log (Y : Real)) -
            Real.log (Real.log (A : Real)) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 3 := by
    have hdeviation :
        fullReciprocalSum Y - fullReciprocalSum A -
            (Real.log (Real.log (Y : Real)) -
              Real.log (Real.log (A : Real))) <=
          |fullReciprocalSum Y - fullReciprocalSum A -
            (Real.log (Real.log (Y : Real)) -
              Real.log (Real.log (A : Real)))| :=
      le_abs_self _
    linarith
  calc
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut <=
      scale * (fullReciprocalSum Y - fullReciprocalSum A) :=
        tangentRatioCellTail_harmonicPointwiseUpper_le_fullReciprocalSum_sub
          bandOf cellIndex scale hscale band cut A Y hAY hgeometry
    _ <= scale *
        (Real.log (Real.log (Y : Real)) -
            Real.log (Real.log (A : Real)) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 3) :=
      mul_le_mul_of_nonneg_left hupper hscale
    _ = bankPaperCanonicalHarmonicTailMajorant scale A Y := rfl

/-- Direct specialization of the prefix adapter.  Exact band balance and
the paper-shaped pointwise estimate now suffice once each strict tail has
certified numerical endpoints beyond the uniform quadrature cutoff. -/
theorem bankPaperCanonicalRoundedSelectorTangentInput_of_harmonicTailGeometry
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (tailLower tailUpper : Band -> Nat -> Nat)
    (scale : Real) (selector : Nat -> Real)
    (hscale : 0 <= scale)
    (hselector : ∀ a ∈ candidates,
      0 <= selector a ∧ selector a <= 1)
    (hrowIntegral : BankPaperCanonicalSelectorRowIntegral
      n candidates selector)
    (hprimeBandBalance :
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed candidates selector)
    (hdeficitSupport :
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed candidates selector)
    (hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| <=
        bankPaperCanonicalHarmonicPointwiseUpper scale p)
    (hlowerCutoff : forall band cut,
      fullReciprocalSumUniformCutoff <= tailLower band cut)
    (hendpoints : forall band cut,
      tailLower band cut <= tailUpper band cut)
    (hgeometry : forall band cut
        (p : BankPaperCanonicalTangentPrime n W),
      bandOf p = band -> cut < cellIndex p ->
        tailLower band cut < bankPaperCanonicalTangentPrimeLabel p ∧
          bankPaperCanonicalTangentPrimeLabel p <= tailUpper band cut) :
    BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        (fun band cut => bankPaperCanonicalHarmonicTailMajorant scale
          (tailLower band cut) (tailUpper band cut)) selector := by
  apply bankPaperCanonicalRoundedSelectorTangentInput_of_tailPointwiseMajorant
    R certificate fixed candidates bandOf cellIndex
      (bankPaperCanonicalHarmonicPointwiseUpper scale)
      (fun band cut => bankPaperCanonicalHarmonicTailMajorant scale
        (tailLower band cut) (tailUpper band cut))
      selector hselector hrowIntegral hprimeBandBalance hdeficitSupport
      hbalance hpointwise
  intro band cut
  exact tangentRatioCellTail_harmonicPointwiseUpper_le_uniformMajorant
    bandOf cellIndex scale hscale band cut
      (tailLower band cut) (tailUpper band cut)
      (hlowerCutoff band cut) (hendpoints band cut)
      (fun p hpBand hpCut => hgeometry band cut p hpBand hpCut)

end

end Erdos390.WholePaper
