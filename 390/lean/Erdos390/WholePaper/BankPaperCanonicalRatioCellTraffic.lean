import Erdos390.WholePaper.BankPaperCanonicalRatioCellOccupancy
import Erdos390.WholePaper.BankPaperCanonicalPrefixQuadrature
import Erdos390.WholePaper.SafeShortIntervalPrimeCounting
import Erdos390.WholePaper.TangentRatioCellEarthmover

/-!
# Analytic envelopes for the canonical ratio cells

This file is the first analytic layer after the concrete ratio-cell
geometry.  It makes three facts explicit.

* A strict tail after cell `cut` lies between the next multiplicative
  cutoff and the upper endpoint of its canonical exponent band.  Capping
  the lower endpoint by the band upper endpoint makes the statement valid
  for every natural `cut`, including vacuous cuts beyond the last cell.
* Every full raw interval contained in a merged cell injects into the
  actual finite cell.  The fixed-ratio PNT therefore gives a quantitative
  lower bound for the literal denominator used by the distributed port.
* Uniform Mertens and the PNT denominator combine into finite cut-traffic
  and pointwise-port envelopes.  No mesh sum is estimated here: the final
  Riemann-sum collapse is deliberately left as a separate analytic step.

There are no new distribution hypotheses.  The only asymptotic inputs are
the audited safe PNT and uniform reciprocal-prime estimate already present
in the repository.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Concrete endpoints for strict cell tails -/

/-- The next raw multiplicative cutoff, capped by the exponent-band upper
endpoint.  The cap makes this a valid endpoint even for a vacuous cut past
the last canonical cell. -/
def bankPaperCanonicalRatioCellTailLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho : Real)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) : Nat :=
  min
    (tangentMultiplicativeRatioCutoff
      (bankPaperCanonicalExponentBandLower M n W band) rho (cut + 1))
    (bankPaperCanonicalExponentBandUpper M n W band)

/-- The upper endpoint of a canonical ratio-cell strict tail. -/
def bankPaperCanonicalRatioCellTailUpper
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (band : BankPaperCanonicalExponentBand M) : Nat :=
  bankPaperCanonicalExponentBandUpper M n W band

theorem bankPaperCanonicalRatioCellTailLower_le_upper
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho : Real)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    bankPaperCanonicalRatioCellTailLower M n W rho band cut <=
      bankPaperCanonicalRatioCellTailUpper M n W band := by
  exact Nat.min_le_right _ _

/-- The fixed cutoff lies below every canonical exponent-band lower
endpoint. -/
theorem bankPaperCanonical_fixedCutoff_le_exponentBandLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (band : BankPaperCanonicalExponentBand M) :
    W <= bankPaperCanonicalExponentBandLower M n W band := by
  have hcut :=
    (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hn hW S).cutoff_le_lower band
  simpa only [bankPaperCanonicalExponentBandLower,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using hcut

/-- Both branches in the capped lower endpoint remain above the fixed
cutoff. -/
theorem bankPaperCanonical_fixedCutoff_le_ratioCellTailLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    W <= bankPaperCanonicalRatioCellTailLower M n W rho band cut := by
  have hWLower := bankPaperCanonical_fixedCutoff_le_exponentBandLower
    M hdelta hn hW S band
  have hcutMono := tangentMultiplicativeRatioCutoff_mono
    (lower := bankPaperCanonicalExponentBandLower M n W band)
    (rho := rho) hrho.le
  have hWNext : W <= tangentMultiplicativeRatioCutoff
      (bankPaperCanonicalExponentBandLower M n W band) rho (cut + 1) := by
    exact hWLower.trans (by
      simpa only [tangentMultiplicativeRatioCutoff_zero] using
        hcutMono (Nat.zero_le (cut + 1)))
  have hWUpper : W <= bankPaperCanonicalExponentBandUpper M n W band := by
    obtain ⟨p, hp⟩ :=
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn hW S).fiber_nonempty band
    have hpInterval :=
      ((RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
        M hdelta hn hW S).band_eq_iff p band).mp hp
    exact hWLower.trans (hpInterval.1.le.trans hpInterval.2)
  exact le_min hWNext hWUpper

/-- Every prime in a declared strict merged-cell tail lies in the concrete
numerical interval used by the Mertens estimate. -/
theorem bankPaperCanonical_ratioCellTail_mem_interval
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat)
    (p : BankPaperCanonicalTangentPrime n W)
    (hpBand : bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band)
    (hpCut : cut <
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p) :
    bankPaperCanonicalRatioCellTailLower M n W rho band cut <
        bankPaperCanonicalTangentPrimeLabel p ∧
      bankPaperCanonicalTangentPrimeLabel p <=
        bankPaperCanonicalRatioCellTailUpper M n W band := by
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let raw := bankPaperCanonicalRawRatioCellIndex
    M hdelta hn hW S rho p
  have hlower : 0 < lower := by
    exact bankPaperCanonicalExponentBandLower_pos
      M hdelta hn hW S band
  have hpLower : lower < p.1 := by
    have hp :=
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S p).1
    simpa only [lower, hpBand] using hp
  have hpUpper : p.1 <= bankPaperCanonicalExponentBandUpper M n W band := by
    have hp :=
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S p).2
    simpa only [hpBand] using hp
  have hmergedLeRaw :
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <= raw := by
    unfold bankPaperCanonicalRatioCellIndex
    exact tangentMergedRatioCellIndex_le_raw _ _
  have hcutRaw : cut + 1 <= raw := by omega
  have hrawLower : tangentMultiplicativeRatioCutoff lower rho raw < p.1 := by
    have h := tangentMultiplicativeRatioCutoff_rawCell_lt_label
      hlower hrho hpLower
    simpa only [raw, lower, bankPaperCanonicalRawRatioCellIndex, hpBand] using h
  have hnextLower :
      tangentMultiplicativeRatioCutoff lower rho (cut + 1) < p.1 := by
    exact (tangentMultiplicativeRatioCutoff_mono
      (lower := lower) (rho := rho) hrho.le hcutRaw).trans_lt hrawLower
  constructor
  · exact (Nat.min_le_left _ _).trans_lt (by
      simpa only [bankPaperCanonicalRatioCellTailLower, lower] using hnextLower)
  · simpa only [bankPaperCanonicalTangentPrimeLabel,
      bankPaperCanonicalRatioCellTailUpper] using hpUpper

/-! ## Uniform Mertens envelope on the concrete tails -/

/-- The explicit Mertens majorant attached to one canonical strict tail. -/
def bankPaperCanonicalRatioCellTailMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho scale : Real)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) : Real :=
  bankPaperCanonicalHarmonicTailMajorant scale
    (bankPaperCanonicalRatioCellTailLower M n W rho band cut)
    (bankPaperCanonicalRatioCellTailUpper M n W band)

/-- Uniform Mertens bounds the literal harmonic mass of every concrete
strict cell tail. -/
theorem bankPaperCanonical_ratioCellTail_harmonic_le_majorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band cut <=
      bankPaperCanonicalRatioCellTailMajorant
        M n W rho scale band cut := by
  apply tangentRatioCellTail_harmonicPointwiseUpper_le_uniformMajorant
    (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
    scale hscale band cut
    (bankPaperCanonicalRatioCellTailLower M n W rho band cut)
    (bankPaperCanonicalRatioCellTailUpper M n W band)
  · exact hMertens.trans
      (bankPaperCanonical_fixedCutoff_le_ratioCellTailLower
        M hdelta hn hW S hrho band cut)
  · exact bankPaperCanonicalRatioCellTailLower_le_upper
      M n W rho band cut
  · intro p hpBand hpCut
    exact bankPaperCanonical_ratioCellTail_mem_interval
      M hdelta hn hW S hrho band cut p hpBand hpCut

/-- The explicit tail majorant is nonnegative.  This is deduced from the
nonnegative literal harmonic tail rather than by separately manipulating
the log-log formula. -/
theorem bankPaperCanonicalRatioCellTailMajorant_nonneg
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    0 <= bankPaperCanonicalRatioCellTailMajorant
      M n W rho scale band cut := by
  have htailNonneg : 0 <=
      tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band cut := by
    unfold tangentRatioCellTailPointwiseUpper
    apply Finset.sum_nonneg
    intro p _hp
    by_cases htail :
        bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band ∧
          cut < bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p
    · simp only [if_pos htail]
      exact div_nonneg hscale (Nat.cast_nonneg _)
    · simp [htail]
  exact htailNonneg.trans
    (bankPaperCanonical_ratioCellTail_harmonic_le_majorant
      M hdelta hn hW S hrho hscale hMertens band cut)

/-! ## Quantitative PNT denominator inside an actual cell -/

/-- Uniform quantitative fixed-ratio prime counting above one cutoff. -/
def TangentFixedRatioPrimeCountLower
    (W : Nat) (rho : Real) : Prop :=
  forall A : Nat, W <= A ->
    ((rho - 1) / 2) * ((A : Real) / Real.log (A : Real)) <=
      (Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
        Nat.primeCounting A : Nat)

/-- The safe PNT supplies a single cutoff for the quantitative fixed-ratio
lower bound. -/
theorem exists_fixedRatioPrimeCountLower_cutoff
    {rho : Real} (hrho : 1 < rho) :
    exists W : Nat, 2 <= W ∧ TangentFixedRatioPrimeCountLower W rho := by
  obtain ⟨W0, hW0⟩ :=
    eventually_atTop.1 (eventually_fixedRatio_primeCounting_lower hrho)
  let W := max 2 W0
  exact ⟨W, le_max_left _ _, by
    intro A hWA
    exact hW0 A ((le_max_right 2 W0).trans hWA)⟩

/-- One fixed cutoff simultaneously supports the quantitative PNT cell
lower bound and the uniform Mertens tail estimate. -/
theorem exists_fixedRatioPrimeCountLower_and_Mertens_cutoff
    {rho : Real} (hrho : 1 < rho) :
    exists W : Nat,
      2 <= W ∧ fullReciprocalSumUniformCutoff <= W ∧
        TangentFixedRatioPrimeCountLower W rho := by
  obtain ⟨W0, hW0two, hW0PNT⟩ :=
    exists_fixedRatioPrimeCountLower_cutoff hrho
  let W := max W0 fullReciprocalSumUniformCutoff
  exact ⟨W, hW0two.trans (le_max_left _ _), le_max_right _ _, by
    intro A hWA
    exact hW0PNT A ((le_max_left W0 fullReciprocalSumUniformCutoff).trans hWA)⟩

/-- The last raw cutoff is strictly below the exponent-band upper endpoint.
This is the finite fact that keeps every earlier full raw interval inside
the canonical prime band. -/
theorem bankPaperCanonical_lastRawRatioCutoff_lt_bandUpper
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (band : BankPaperCanonicalExponentBand M) :
    tangentMultiplicativeRatioCutoff
        (bankPaperCanonicalExponentBandLower M n W band) rho
        (bankPaperCanonicalLastRawRatioCell M
          (n := n) (W := W) rho band) <
      bankPaperCanonicalExponentBandUpper M n W band := by
  obtain ⟨p, hp⟩ :=
    (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S).fiber_nonempty band
  have hpInterval :=
    ((RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hn hW S).band_eq_iff p band).mp hp
  have hstrict : bankPaperCanonicalExponentBandLower M n W band <
      bankPaperCanonicalExponentBandUpper M n W band :=
    hpInterval.1.trans_le hpInterval.2
  simpa only [bankPaperCanonicalLastRawRatioCell] using
    tangentMultiplicativeRatioCutoff_rawCell_lt_label
      (bankPaperCanonicalExponentBandLower_pos M hdelta hn hW S band)
      hrho hstrict

/-- The primes in the full raw interval beginning at a merged cell inject
into the literal finite cell.  The final raw fragment may also be present
in the target cell, so the result is an inequality rather than an equality. -/
theorem bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (band : BankPaperCanonicalExponentBand M) (cell : Nat)
    (hcell : cell < bankPaperCanonicalLastRawRatioCell M
      (n := n) (W := W) rho band) :
    Nat.primeCounting
          ⌊rho * (tangentMultiplicativeRatioCutoff
            (bankPaperCanonicalExponentBandLower M n W band)
            rho cell : Real)⌋₊ -
        Nat.primeCounting
          (tangentMultiplicativeRatioCutoff
            (bankPaperCanonicalExponentBandLower M n W band) rho cell) <=
      tangentRatioCellCard
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band cell := by
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let lastRaw := bankPaperCanonicalLastRawRatioCell M
    (n := n) (W := W) rho band
  let A := tangentMultiplicativeRatioCutoff lower rho cell
  let B := ⌊rho * (A : Real)⌋₊
  let source : Finset Nat := (Finset.Ioc A B).filter Nat.Prime
  let target : Finset (BankPaperCanonicalTangentPrime n W) :=
    Finset.univ.filter (fun p =>
      bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band ∧
        bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = cell)
  let labelEmbedding : BankPaperCanonicalTangentPrime n W ↪ Nat :=
    ⟨bankPaperCanonicalTangentPrimeLabel,
      bankPaperCanonicalTangentPrimeLabel_injective⟩
  let targetLabels : Finset Nat := target.map labelEmbedding
  have hlower : 0 < lower :=
    bankPaperCanonicalExponentBandLower_pos M hdelta hn hW S band
  have hALower : lower <= A := by
    have hmono := tangentMultiplicativeRatioCutoff_mono
      (lower := lower) (rho := rho) hrho.le (Nat.zero_le cell)
    simpa only [A, tangentMultiplicativeRatioCutoff_zero] using hmono
  have hAB : A <= B := by
    apply Nat.le_floor
    have hrhoNonneg : 0 <= rho := by linarith
    calc
      (A : Real) = 1 * (A : Real) := by ring
      _ <= rho * (A : Real) :=
        mul_le_mul_of_nonneg_right hrho.le (Nat.cast_nonneg A)
  have hsubset : source ⊆ targetLabels := by
    intro p hpSource
    have hpFilter := Finset.mem_filter.mp hpSource
    have hpIoc := Finset.mem_Ioc.mp hpFilter.1
    have hpPrime : p.Prime := hpFilter.2
    have hAReal : (A : Real) <= (lower : Real) * rho ^ cell := by
      exact Nat.floor_le
        (mul_nonneg (Nat.cast_nonneg lower) (pow_nonneg (by linarith) _))
    have hnextReal : rho * (A : Real) <=
        (lower : Real) * rho ^ (cell + 1) := by
      calc
        rho * (A : Real) <= rho * ((lower : Real) * rho ^ cell) :=
          mul_le_mul_of_nonneg_left hAReal (by linarith)
        _ = (lower : Real) * rho ^ (cell + 1) := by
          rw [pow_succ]
          ring
    have hpNext : p <= tangentMultiplicativeRatioCutoff
        lower rho (cell + 1) := by
      exact hpIoc.2.trans (Nat.floor_mono hnextReal)
    have hnextLast : tangentMultiplicativeRatioCutoff lower rho (cell + 1) <=
        tangentMultiplicativeRatioCutoff lower rho lastRaw := by
      exact tangentMultiplicativeRatioCutoff_mono
        (lower := lower) (rho := rho) hrho.le (by omega)
    have hpUpperBand : p <=
        bankPaperCanonicalExponentBandUpper M n W band := by
      exact hpNext.trans (hnextLast.trans
        (by simpa only [lower, lastRaw] using
          (bankPaperCanonical_lastRawRatioCutoff_lt_bandUpper
            M hdelta hn hW S hrho band).le))
    have hWLower := bankPaperCanonical_fixedCutoff_le_exponentBandLower
      M hdelta hn hW S band
    have hpBandNat : p ∈ primeBand n W := by
      apply mem_primeBand.mpr
      exact ⟨hpPrime, (hWLower.trans hALower).trans_lt hpIoc.1,
        hpUpperBand.trans (by
          simpa only [bankPaperCanonicalExponentBandUpper,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using
              (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
                M hdelta hn hW S).upper_le_yNat band)⟩
    let q : BankPaperCanonicalTangentPrime n W := ⟨p, hpBandNat⟩
    have hqBand :
        bankPaperCanonicalExponentBandOf M hdelta hn hW S q = band := by
      have hinterval :
          (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
              M hdelta hn hW S).lower band < q.1 ∧
            q.1 <=
              (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
                M hdelta hn hW S).upper band := by
        constructor
        · have : lower < p := hALower.trans_lt hpIoc.1
          simpa only [lower,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using this
        · simpa only [bankPaperCanonicalExponentBandUpper,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using
              hpUpperBand
      have hband :=
        ((RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
          M hdelta hn hW S).band_eq_iff q band).mpr hinterval
      simpa only [bankPaperCanonicalExponentBandOf] using hband
    have hqRaw : bankPaperCanonicalRawRatioCellIndex
        M hdelta hn hW S rho q = cell := by
      unfold bankPaperCanonicalRawRatioCellIndex
      rw [hqBand]
      exact tangentMultiplicativeRawCellIndex_eq_of_mem
        hlower hrho hpIoc.1 hpNext
    have hqCell : bankPaperCanonicalRatioCellIndex
        M hdelta hn hW S rho q = cell := by
      unfold bankPaperCanonicalRatioCellIndex
      rw [hqBand, hqRaw]
      exact tangentMergedRatioCellIndex_eq_self (by
        unfold tangentMergedRatioLastCell
        simpa only [lastRaw] using (show cell <= lastRaw - 1 by omega))
    apply Finset.mem_map.mpr
    exact ⟨q, by
      simp only [target, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hqBand, hqCell⟩, rfl⟩
  have hcard : source.card <= targetLabels.card :=
    Finset.card_le_card hsubset
  have hsource : source.card =
      Nat.primeCounting B - Nat.primeCounting A := by
    simpa only [source] using
      SafePrimeCounting.prime_Ioc_card_eq_primeCounting_sub hAB
  have htarget : targetLabels.card = target.card := by
    exact Finset.card_map labelEmbedding
  rw [hsource, htarget] at hcard
  simpa only [target, A, B, lower, tangentRatioCellCard] using hcard

/-- Quantitative PNT lower bound for the actual denominator of every merged
cell containing a full raw interval. -/
theorem bankPaperCanonical_ratioCellCard_PNT_lower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (band : BankPaperCanonicalExponentBand M) (cell : Nat)
    (hcell : cell < bankPaperCanonicalLastRawRatioCell M
      (n := n) (W := W) rho band) :
    ((rho - 1) / 2) *
        ((tangentMultiplicativeRatioCutoff
            (bankPaperCanonicalExponentBandLower M n W band)
            rho cell : Real) /
          Real.log (tangentMultiplicativeRatioCutoff
            (bankPaperCanonicalExponentBandLower M n W band)
            rho cell : Real)) <=
      (tangentRatioCellCard
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band cell : Real) := by
  let A := tangentMultiplicativeRatioCutoff
    (bankPaperCanonicalExponentBandLower M n W band) rho cell
  have hWA : W <= A := by
    exact (bankPaperCanonical_fixedCutoff_le_exponentBandLower
      M hdelta hn hW S band).trans (by
        have hmono := tangentMultiplicativeRatioCutoff_mono
          (lower := bankPaperCanonicalExponentBandLower M n W band)
          (rho := rho) hrho.le (Nat.zero_le cell)
        simpa only [A, tangentMultiplicativeRatioCutoff_zero] using hmono)
  exact (hPNT A hWA).trans (by
    exact_mod_cast
      (bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard
        M hdelta hn hW S hrho band cell hcell))

/-! ## Finite traffic envelopes before the final mesh sum -/

/-- Sum of the concrete Mertens majorants over the nonterminal canonical
cell cuts.  This is the exact finite expression to be collapsed by the
later mesh/Riemann-sum argument. -/
def bankPaperCanonicalRatioCellCutEnvelope
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho scale : Real) : Real :=
  ∑ band : BankPaperCanonicalExponentBand M,
    ∑ cut ∈ Finset.range
        (bankPaperCanonicalLastRatioCell M
          (n := n) (W := W) rho band),
      bankPaperCanonicalRatioCellTailMajorant
        M n W rho scale band cut

/-- Literal harmonic envelope for the residual `ell^1` mass. -/
def bankPaperCanonicalHarmonicResidualL1Envelope
    (n W : Nat) (scale : Real) : Real :=
  ∑ p : BankPaperCanonicalTangentPrime n W,
    bankPaperCanonicalHarmonicPointwiseUpper scale p

/-- Uniform Mertens endpoint majorant for the complete harmonic residual
mass on `W < p <= yNat n`. -/
def bankPaperCanonicalHarmonicResidualL1Majorant
    (n W : Nat) (scale : Real) : Real :=
  bankPaperCanonicalHarmonicTailMajorant scale W (yNat n)

/-- Complete finite total-traffic envelope: half of the harmonic residual
mass plus twice the Mertens cut envelope. -/
def bankPaperCanonicalRatioCellTotalTrafficEnvelope
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho scale : Real) : Real :=
  bankPaperCanonicalHarmonicResidualL1Envelope n W scale / 2 +
    2 * bankPaperCanonicalRatioCellCutEnvelope M n W rho scale

/-- Endpoint form of the complete traffic envelope, after applying Mertens
also to the global residual `ell^1` mass. -/
def bankPaperCanonicalRatioCellTotalTrafficMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho scale : Real) : Real :=
  bankPaperCanonicalHarmonicResidualL1Majorant n W scale / 2 +
    2 * bankPaperCanonicalRatioCellCutEnvelope M n W rho scale

/-- The harmonic pointwise estimate immediately supplies the exact
weighted-residual budget `weightedResidual = scale`. -/
theorem bankPaperCanonical_weightedResidual_le_harmonicScale
    {n W : Nat} {scale : Real}
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |residual p| <= bankPaperCanonicalHarmonicPointwiseUpper scale p)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| <=
      scale := by
  calc
    (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| <=
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
          bankPaperCanonicalHarmonicPointwiseUpper scale p :=
      mul_le_mul_of_nonneg_left (hpointwise p) (Nat.cast_nonneg _)
    _ = scale :=
      bankPaperCanonicalTangentPrimeLabel_mul_harmonicPointwiseUpper scale p

/-- Uniform Mertens bounds the complete harmonic residual envelope on the
literal canonical prime band. -/
theorem bankPaperCanonicalHarmonicResidualL1Envelope_le_majorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {scale : Real} (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W) :
    bankPaperCanonicalHarmonicResidualL1Envelope n W scale <=
      bankPaperCanonicalHarmonicResidualL1Majorant n W scale := by
  let bandOf : BankPaperCanonicalTangentPrime n W -> Unit := fun _ => ()
  let cellIndex : BankPaperCanonicalTangentPrime n W -> Nat := fun _ => 1
  have hWY : W <= yNat n := by
    let band : BankPaperCanonicalExponentBand M := ⟨0, by omega⟩
    let E := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hn hW S
    exact (E.cutoff_le_lower band).trans
      ((E.lower_le_upper band).trans (E.upper_le_yNat band))
  have htail :=
    tangentRatioCellTail_harmonicPointwiseUpper_le_uniformMajorant
      bandOf cellIndex scale hscale () 0 W (yNat n)
      hMertens hWY (by
        intro p _hpBand _hpCut
        exact ⟨cutoff_lt_of_mem_primeBand p.2,
          le_yNat_of_mem_primeBand p.2⟩)
  simpa [bankPaperCanonicalHarmonicResidualL1Envelope,
    bankPaperCanonicalHarmonicResidualL1Majorant,
    tangentRatioCellTailPointwiseUpper, bandOf, cellIndex,
    bankPaperCanonicalTangentPrimeLabel] using htail

/-- Exact band balance and the harmonic residual bound reduce the complete
canonical cut ledger to the explicit finite Mertens envelope. -/
theorem bankPaperCanonical_ratioCellCutTraffic_le_envelope
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band then
          residual p else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |residual p| <= bankPaperCanonicalHarmonicPointwiseUpper scale p) :
    tangentRatioCellCanonicalCutTraffic
        (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
        residual
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) <=
      bankPaperCanonicalRatioCellCutEnvelope M n W rho scale := by
  unfold bankPaperCanonicalRatioCellCutEnvelope
  apply tangentRatioCellCanonicalCutTraffic_le_prefixUpper
  intro band cut
  exact (abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
      residual (bankPaperCanonicalHarmonicPointwiseUpper scale)
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
      hbalance hpointwise band cut).trans
    (bankPaperCanonical_ratioCellTail_harmonic_le_majorant
      M hdelta hn hW S hrho hscale hMertens band cut)

/-- The literal distributed total-traffic ledger is bounded by the complete
finite harmonic/Mertens envelope. -/
theorem bankPaperCanonical_ratioCellTotalTraffic_le_envelope
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band then
          residual p else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |residual p| <= bankPaperCanonicalHarmonicPointwiseUpper scale p) :
    tangentDistributedTotalTrafficLedger residual
        (tangentRatioCellCanonicalCutTraffic
          (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
          residual
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)) <=
      bankPaperCanonicalRatioCellTotalTrafficEnvelope
        M n W rho scale := by
  have hresidualSum :
      (∑ p : BankPaperCanonicalTangentPrime n W, |residual p|) <=
        bankPaperCanonicalHarmonicResidualL1Envelope n W scale := by
    unfold bankPaperCanonicalHarmonicResidualL1Envelope
    exact Finset.sum_le_sum (fun p _hp => hpointwise p)
  have hcut := bankPaperCanonical_ratioCellCutTraffic_le_envelope
    M hdelta hn hW S hrho hscale hMertens residual hbalance hpointwise
  unfold tangentDistributedTotalTrafficLedger
    bankPaperCanonicalRatioCellTotalTrafficEnvelope
  exact add_le_add
    (div_le_div_of_nonneg_right hresidualSum (by norm_num))
    (mul_le_mul_of_nonneg_left hcut (by norm_num))

/-- Fully endpoint-reduced total-traffic bound.  The only unevaluated term
is the explicit finite sum of cell-tail Mertens majorants. -/
theorem bankPaperCanonical_ratioCellTotalTraffic_le_majorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band then
          residual p else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |residual p| <= bankPaperCanonicalHarmonicPointwiseUpper scale p) :
    tangentDistributedTotalTrafficLedger residual
        (tangentRatioCellCanonicalCutTraffic
          (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
          residual
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)) <=
      bankPaperCanonicalRatioCellTotalTrafficMajorant
        M n W rho scale := by
  have htotal := bankPaperCanonical_ratioCellTotalTraffic_le_envelope
    M hdelta hn hW S hrho hscale hMertens residual hbalance hpointwise
  have hresidual := bankPaperCanonicalHarmonicResidualL1Envelope_le_majorant
    M hdelta hn hW S hscale hMertens
  exact htotal.trans (by
    unfold bankPaperCanonicalRatioCellTotalTrafficEnvelope
      bankPaperCanonicalRatioCellTotalTrafficMajorant
    exact add_le_add
      (div_le_div_of_nonneg_right hresidual (by norm_num)) le_rfl)

/-- The two Mertens tails incident to a vertex's cell. -/
def bankPaperCanonicalRatioCellPortNumeratorEnvelope
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho scale : Real) (p : BankPaperCanonicalTangentPrime n W) : Real :=
  (if bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = 0 then 0
    else bankPaperCanonicalRatioCellTailMajorant M n W rho scale
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p - 1)) +
    bankPaperCanonicalRatioCellTailMajorant M n W rho scale
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p)

/-- If an exponent band has no full raw interval, terminal merging puts all
of its vertices in cell zero, so the strict tail after cell zero is empty. -/
theorem bankPaperCanonical_ratioCellTail_eq_zero_of_lastRaw_eq_zero
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (band : BankPaperCanonicalExponentBand M)
    (hlast : bankPaperCanonicalLastRawRatioCell M
      (n := n) (W := W) rho band = 0) :
    tangentRatioCellTailPointwiseUpper pointwiseUpper
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band 0 = 0 := by
  unfold tangentRatioCellTailPointwiseUpper
  apply Finset.sum_eq_zero
  intro p _hp
  by_cases hpBand :
      bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band
  · have hpIndex := bankPaperCanonicalRatioCellIndex_le_lastCell
      M hdelta hn hW S rho p
    have hpIndexLe :
        bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <= 0 := by
      simpa only [hpBand, bankPaperCanonicalLastRatioCell,
        tangentMergedRatioLastCell, hlast] using hpIndex
    have hpIndexZero :
        bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = 0 :=
      Nat.eq_zero_of_le_zero hpIndexLe
    simp [hpBand, hpIndexZero]
  · simp [hpBand]

/-- Correspondingly, the literal two-sided pointwise port majorant is zero
in a band with no full raw interval. -/
theorem bankPaperCanonical_ratioCellPointwisePortUpper_eq_zero_of_lastRaw_eq_zero
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (p : BankPaperCanonicalTangentPrime n W)
    (hlast : bankPaperCanonicalLastRawRatioCell M
      (n := n) (W := W) rho
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) = 0) :
    tangentRatioCellPointwisePortUpper pointwiseUpper
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) p = 0 := by
  have hpIndex := bankPaperCanonicalRatioCellIndex_le_lastCell
    M hdelta hn hW S rho p
  have hpIndexLe :
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <= 0 := by
    simpa only [bankPaperCanonicalLastRatioCell,
      tangentMergedRatioLastCell, hlast] using hpIndex
  have hpIndexZero :
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = 0 :=
    Nat.eq_zero_of_le_zero hpIndexLe
  have htail := bankPaperCanonical_ratioCellTail_eq_zero_of_lastRaw_eq_zero
    M hdelta hn hW S rho pointwiseUpper
    (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) hlast
  unfold tangentRatioCellPointwisePortUpper
  rw [if_pos hpIndexZero, hpIndexZero, htail]
  simp

/-- Mertens bounds the numerator in the literal pointwise-port quotient. -/
theorem bankPaperCanonical_ratioCellPointwisePortUpper_le_envelope_div_card
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (p : BankPaperCanonicalTangentPrime n W) :
    tangentRatioCellPointwisePortUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) p <=
      bankPaperCanonicalRatioCellPortNumeratorEnvelope
          M hdelta hn hW S rho scale p /
        tangentRatioCellCard
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p) := by
  unfold tangentRatioCellPointwisePortUpper
    bankPaperCanonicalRatioCellPortNumeratorEnvelope
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  by_cases hcell :
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = 0
  · simpa only [if_pos hcell, zero_add] using
      (bankPaperCanonical_ratioCellTail_harmonic_le_majorant
        M hdelta hn hW S hrho hscale hMertens
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p))
  · simpa only [if_neg hcell] using
      (add_le_add
        (bankPaperCanonical_ratioCellTail_harmonic_le_majorant
          M hdelta hn hW S hrho hscale hMertens
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p - 1))
        (bankPaperCanonical_ratioCellTail_harmonic_le_majorant
          M hdelta hn hW S hrho hscale hMertens
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p)))

/-- PNT main term used as the analytic lower denominator at a vertex. -/
def bankPaperCanonicalRatioCellPNTDenominator
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) : Real :=
  let A := tangentMultiplicativeRatioCutoff
    (bankPaperCanonicalExponentBandLower M n W
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)) rho
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p)
  ((rho - 1) / 2) * ((A : Real) / Real.log (A : Real))

/-- The PNT denominator is positive once the fixed cutoff is at least two. -/
theorem bankPaperCanonicalRatioCellPNTDenominator_pos
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    0 < bankPaperCanonicalRatioCellPNTDenominator
      M hdelta hn (by omega) S rho p := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn
    (by omega : W ≠ 0) S p
  let cell := bankPaperCanonicalRatioCellIndex M hdelta hn
    (by omega : W ≠ 0) S rho p
  let A := tangentMultiplicativeRatioCutoff
    (bankPaperCanonicalExponentBandLower M n W band) rho cell
  have hWA : W <= A :=
    (bankPaperCanonical_fixedCutoff_le_exponentBandLower
      M hdelta hn (by omega) S band).trans (by
        have hmono := tangentMultiplicativeRatioCutoff_mono
          (lower := bankPaperCanonicalExponentBandLower M n W band)
          (rho := rho) hrho.le (Nat.zero_le cell)
        simpa only [A, tangentMultiplicativeRatioCutoff_zero] using hmono)
  have hAone : 1 < A := by omega
  have hApos : (0 : Real) < A := by exact_mod_cast (Nat.zero_lt_of_lt hAone)
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast hAone)
  simpa only [bankPaperCanonicalRatioCellPNTDenominator, A, band, cell] using
    mul_pos (div_pos (sub_pos.mpr hrho) (by norm_num))
      (div_pos hApos hlogA)

/-- The quantitative PNT and Mertens estimates give a completely explicit
weighted pointwise-port bound.  Bands with a full raw interval use the PNT
denominator; in a degenerate one-cell band the literal port load is zero. -/
theorem bankPaperCanonical_weightedRatioCellPointwisePortUpper_le_PNTEnvelope
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        tangentRatioCellPointwisePortUpper
          (bankPaperCanonicalHarmonicPointwiseUpper scale)
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho) p <=
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
        (bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p /
          bankPaperCanonicalRatioCellPNTDenominator
            M hdelta hn (by omega) S rho p) := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn
    (by omega : W ≠ 0) S p
  let cell := bankPaperCanonicalRatioCellIndex M hdelta hn
    (by omega : W ≠ 0) S rho p
  have hnumNonneg : 0 <= bankPaperCanonicalRatioCellPortNumeratorEnvelope
      M hdelta hn (by omega) S rho scale p := by
    unfold bankPaperCanonicalRatioCellPortNumeratorEnvelope
    change 0 <=
      (if cell = 0 then 0
        else bankPaperCanonicalRatioCellTailMajorant
          M n W rho scale band (cell - 1)) +
        bankPaperCanonicalRatioCellTailMajorant
          M n W rho scale band cell
    by_cases hcellZero : cell = 0
    · simpa only [if_pos hcellZero, zero_add] using
        (bankPaperCanonicalRatioCellTailMajorant_nonneg
          M hdelta hn (by omega) S hrho hscale hMertens band cell)
    · simpa only [if_neg hcellZero] using
        (add_nonneg
          (bankPaperCanonicalRatioCellTailMajorant_nonneg
            M hdelta hn (by omega) S hrho hscale hMertens band (cell - 1))
          (bankPaperCanonicalRatioCellTailMajorant_nonneg
            M hdelta hn (by omega) S hrho hscale hMertens band cell))
  have hport :=
    bankPaperCanonical_ratioCellPointwisePortUpper_le_envelope_div_card
      M hdelta hn (by omega) S hrho hscale hMertens p
  have hdenPos := bankPaperCanonicalRatioCellPNTDenominator_pos
    M hdelta hn hWtwo S hrho p
  by_cases hlastZero : bankPaperCanonicalLastRawRatioCell M
      (n := n) (W := W) rho band = 0
  · have hportZero :=
      bankPaperCanonical_ratioCellPointwisePortUpper_eq_zero_of_lastRaw_eq_zero
        M hdelta hn (by omega) S rho
        (bankPaperCanonicalHarmonicPointwiseUpper scale) p (by
          simpa only [band] using hlastZero)
    rw [hportZero, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg hnumNonneg hdenPos.le)
  · have hlast : 0 < bankPaperCanonicalLastRawRatioCell M
        (n := n) (W := W) rho band := Nat.pos_of_ne_zero hlastZero
    have hcell : cell < bankPaperCanonicalLastRawRatioCell M
        (n := n) (W := W) rho band := by
      have hindex : cell <=
          bankPaperCanonicalLastRawRatioCell M
            (n := n) (W := W) rho band - 1 := by
        simpa only [cell, band, bankPaperCanonicalLastRatioCell,
          tangentMergedRatioLastCell] using
            (bankPaperCanonicalRatioCellIndex_le_lastCell
              M hdelta hn (by omega) S rho p)
      omega
    have hdenLower : bankPaperCanonicalRatioCellPNTDenominator
        M hdelta hn (by omega) S rho p <=
        (tangentRatioCellCard
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho)
          band cell : Real) := by
      simpa only [bankPaperCanonicalRatioCellPNTDenominator, band, cell] using
        bankPaperCanonical_ratioCellCard_PNT_lower
          M hdelta hn (by omega) S hrho hPNT band cell hcell
    have hratio :
        bankPaperCanonicalRatioCellPortNumeratorEnvelope
              M hdelta hn (by omega) S rho scale p /
            (tangentRatioCellCard
              (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
              (bankPaperCanonicalRatioCellIndex
                M hdelta hn (by omega) S rho)
              (bankPaperCanonicalExponentBandOf
                M hdelta hn (by omega) S p)
              (bankPaperCanonicalRatioCellIndex
                M hdelta hn (by omega) S rho p) : Real) <=
          bankPaperCanonicalRatioCellPortNumeratorEnvelope
              M hdelta hn (by omega) S rho scale p /
            bankPaperCanonicalRatioCellPNTDenominator
              M hdelta hn (by omega) S rho p := by
      exact div_le_div_of_nonneg_left hnumNonneg hdenPos
        (by simpa only [band, cell] using hdenLower)
    exact mul_le_mul_of_nonneg_left
      (hport.trans hratio) (Nat.cast_nonneg _)

/-- Direct assembly-facing form: exact band balance and the harmonic
pointwise residual bound first control the literal uniform port, after
which the concrete Mertens/PNT envelope supplies its weighted bound. -/
theorem bankPaperCanonical_weightedRatioCellUniformPortLoad_le_PNTEnvelope
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ q : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S q =
            band then residual q else 0) = 0)
    (hpointwise : forall q : BankPaperCanonicalTangentPrime n W,
      |residual q| <= bankPaperCanonicalHarmonicPointwiseUpper scale q)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        tangentRatioCellUniformPortLoad residual
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho) p <=
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
        (bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p /
          bankPaperCanonicalRatioCellPNTDenominator
            M hdelta hn (by omega) S rho p) := by
  calc
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
          tangentRatioCellUniformPortLoad residual
            (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
            (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho) p <=
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
          tangentRatioCellPointwisePortUpper
            (bankPaperCanonicalHarmonicPointwiseUpper scale)
            (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
            (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho) p :=
      mul_le_mul_of_nonneg_left
        (tangentRatioCellUniformPortLoad_le_pointwisePortUpper
          residual (bankPaperCanonicalHarmonicPointwiseUpper scale)
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho)
          hbalance hpointwise p)
        (Nat.cast_nonneg _)
    _ <= (bankPaperCanonicalTangentPrimeLabel p : Real) *
        (bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p /
          bankPaperCanonicalRatioCellPNTDenominator
            M hdelta hn (by omega) S rho p) :=
      bankPaperCanonical_weightedRatioCellPointwisePortUpper_le_PNTEnvelope
        M hdelta hn hWtwo S hrho hscale hMertens hPNT p

end

end Erdos390.WholePaper
