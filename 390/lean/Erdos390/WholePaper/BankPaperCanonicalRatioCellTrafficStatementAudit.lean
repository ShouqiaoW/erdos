import Erdos390.WholePaper.BankPaperCanonicalRatioCellTraffic

/-!
# Expanded statement audit for canonical ratio-cell traffic envelopes

The declaration census covers every public definition and theorem.  The
expanded examples pin down the quantitative PNT cell denominator, the
finite Mertens cut envelope, and the weighted pointwise-port terminal.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

#check bankPaperCanonicalRatioCellTailLower
#check bankPaperCanonicalRatioCellTailUpper
#check bankPaperCanonicalRatioCellTailLower_le_upper
#check bankPaperCanonical_fixedCutoff_le_exponentBandLower
#check bankPaperCanonical_fixedCutoff_le_ratioCellTailLower
#check bankPaperCanonical_ratioCellTail_mem_interval
#check bankPaperCanonicalRatioCellTailMajorant
#check bankPaperCanonical_ratioCellTail_harmonic_le_majorant
#check bankPaperCanonicalRatioCellTailMajorant_nonneg
#check TangentFixedRatioPrimeCountLower
#check exists_fixedRatioPrimeCountLower_cutoff
#check exists_fixedRatioPrimeCountLower_and_Mertens_cutoff
#check bankPaperCanonical_lastRawRatioCutoff_lt_bandUpper
#check bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard
#check bankPaperCanonical_ratioCellCard_PNT_lower
#check bankPaperCanonicalRatioCellCutEnvelope
#check bankPaperCanonicalHarmonicResidualL1Envelope
#check bankPaperCanonicalHarmonicResidualL1Majorant
#check bankPaperCanonicalRatioCellTotalTrafficEnvelope
#check bankPaperCanonicalRatioCellTotalTrafficMajorant
#check bankPaperCanonical_weightedResidual_le_harmonicScale
#check bankPaperCanonicalHarmonicResidualL1Envelope_le_majorant
#check bankPaperCanonical_ratioCellCutTraffic_le_envelope
#check bankPaperCanonical_ratioCellTotalTraffic_le_envelope
#check bankPaperCanonical_ratioCellTotalTraffic_le_majorant
#check bankPaperCanonicalRatioCellPortNumeratorEnvelope
#check bankPaperCanonical_ratioCellTail_eq_zero_of_lastRaw_eq_zero
#check bankPaperCanonical_ratioCellPointwisePortUpper_eq_zero_of_lastRaw_eq_zero
#check bankPaperCanonical_ratioCellPointwisePortUpper_le_envelope_div_card
#check bankPaperCanonicalRatioCellPNTDenominator
#check bankPaperCanonicalRatioCellPNTDenominator_pos
#check bankPaperCanonical_weightedRatioCellPointwisePortUpper_le_PNTEnvelope
#check bankPaperCanonical_weightedRatioCellUniformPortLoad_le_PNTEnvelope

example {rho : Real} (hrho : 1 < rho) :
    ∃ W : Nat, 2 ≤ W ∧
      ∀ A : Nat, W ≤ A →
        ((rho - 1) / 2) * ((A : Real) / Real.log (A : Real)) ≤
          (Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
            Nat.primeCounting A : Nat) :=
  exists_fixedRatioPrimeCountLower_cutoff hrho

example {rho : Real} (hrho : 1 < rho) :
    ∃ W : Nat,
      2 ≤ W ∧ fullReciprocalSumUniformCutoff ≤ W ∧
        TangentFixedRatioPrimeCountLower W rho :=
  exists_fixedRatioPrimeCountLower_and_Mertens_cutoff hrho

example
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
            rho cell : Real)) ≤
      (tangentRatioCellCard
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band cell : Real) :=
  bankPaperCanonical_ratioCellCard_PNT_lower
    M hdelta hn hW S hrho hPNT band cell hcell

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 ≤ scale)
    (hMertens : fullReciprocalSumUniformCutoff ≤ W)
    (residual : BankPaperCanonicalTangentPrime n W → Real)
    (hbalance : ∀ band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band then
          residual p else 0) = 0)
    (hpointwise : ∀ p : BankPaperCanonicalTangentPrime n W,
      |residual p| ≤ bankPaperCanonicalHarmonicPointwiseUpper scale p) :
    tangentRatioCellCanonicalCutTraffic
        (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
        residual
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) ≤
      bankPaperCanonicalRatioCellCutEnvelope M n W rho scale :=
  bankPaperCanonical_ratioCellCutTraffic_le_envelope
    M hdelta hn hW S hrho hscale hMertens residual hbalance hpointwise

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 ≤ scale)
    (hMertens : fullReciprocalSumUniformCutoff ≤ W)
    (residual : BankPaperCanonicalTangentPrime n W → Real)
    (hbalance : ∀ band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band then
          residual p else 0) = 0)
    (hpointwise : ∀ p : BankPaperCanonicalTangentPrime n W,
      |residual p| ≤ bankPaperCanonicalHarmonicPointwiseUpper scale p) :
    tangentDistributedTotalTrafficLedger residual
        (tangentRatioCellCanonicalCutTraffic
          (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
          residual
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)) ≤
      bankPaperCanonicalRatioCellTotalTrafficEnvelope M n W rho scale :=
  bankPaperCanonical_ratioCellTotalTraffic_le_envelope
    M hdelta hn hW S hrho hscale hMertens residual hbalance hpointwise

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 ≤ W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 ≤ scale)
    (hMertens : fullReciprocalSumUniformCutoff ≤ W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        tangentRatioCellPointwisePortUpper
          (bankPaperCanonicalHarmonicPointwiseUpper scale)
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn (by omega) S rho) p ≤
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
        (bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p /
          bankPaperCanonicalRatioCellPNTDenominator
            M hdelta hn (by omega) S rho p) :=
  bankPaperCanonical_weightedRatioCellPointwisePortUpper_le_PNTEnvelope
    M hdelta hn hWtwo S hrho hscale hMertens hPNT p

end

end Erdos390.WholePaper
