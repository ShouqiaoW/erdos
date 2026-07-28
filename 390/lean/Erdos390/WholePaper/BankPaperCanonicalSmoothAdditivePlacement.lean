import Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureAdditiveRefinement
import Erdos390.WholePaper.BankPaperCanonicalSmoothAdditiveRefinementTangentTransport

/-!
# Paper-faithful placement boundary for the guarded smooth refinement

The smooth bridge in the paper does not preserve the medium-prime moments
of an earlier provisional selector.  It freezes the protected layer,
redistributes the active mass while preserving the smooth-row ledger and
the moments outside the tangent band, and then fits the medium-prime band
moments.  Proposition 8.7 supplies that latter fit.

Accordingly, the pre-selector part of the actual endpoint theorem needs
only complete-row integrality and deficit support outside the medium-prime
band.  Its older statement accepted a full rounded-selector tangent input,
although the proof used only those two fields.  This file records the
weaker exact theorem, constructs the minimized ledger from the paper's two
literal zero-head cells, and proves the exact scaled structured head-cell
moments.  It then resolves the support boundary--the nonzero head cells lie
in the smooth row, not in its head-free correction subpool--by transporting
a signed ledger over the whole smooth row for the corrected selector.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-- The minimized ledger needed before the smooth P87 fit.  The local row
mass may change, but only by an integer, and only the fixed head-prime
moments must be preserved.  Moments above `y` vanish automatically because
the replacement is supported in the smooth row; medium-prime moments are
allowed to change and are fitted by P87. -/
def BankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) : Prop :=
  (∃ rowChange : Int,
    (∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      (betaProt / B.L +
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a -
          baseSelector a)) = (rowChange : Real)) ∧
    ∀ q : Nat, q.Prime -> q <= B.sampleData.W ->
      bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q = 0

/-! ## Exact finite algebra for the two zero-head pools -/

/-- A mass increment spread uniformly over one literal structured cell.
The cell is nonempty by `StructuredSampleData.cell_nonempty`, so its
cardinality denominator is nonzero. -/
def bankPaperCanonicalUniformCellIncrement
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (cell : Cell Head)
    (mass : Real) (m : D.Sample) : Real := by
  classical
  exact
    if D.cellOf m = cell then
      mass / Fintype.card (D.SampleAt cell)
    else 0

/-- Uniform spreading realizes the requested cell mass exactly. -/
theorem sum_bankPaperCanonicalUniformCellIncrement
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (cell : Cell Head)
    (mass : Real) :
    (∑ m : D.Sample,
      bankPaperCanonicalUniformCellIncrement D cell mass m) = mass := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single cell]
  · simp only [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, if_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (D.SampleAt cell) : Real) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (D.sampleAt_card_pos cell)
    field_simp [hcard]
  · intro other _hother hne
    apply Finset.sum_eq_zero
    intro m _hm
    simp [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, hne]
  · intro hnot
    exact (hnot (Finset.mem_univ cell)).elim

/-- The paper's two mass changes are made in the two physical copies of
the zero head vertex.  This definition changes no nonzero head cell. -/
def bankPaperCanonicalTwoZeroHeadCellRebalance
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (seed : D.Sample -> Real) (minusMass plusMass : Real)
    (m : D.Sample) : Real :=
  seed m +
    bankPaperCanonicalUniformCellIncrement D (none, .minus) minusMass m +
    bankPaperCanonicalUniformCellIncrement D (none, .plus) plusMass m

/-- The two zero-head pool changes alter the tagged active mass by exactly
the sum of their two requested masses. -/
theorem sum_bankPaperCanonicalTwoZeroHeadCellRebalance_sub
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (seed : D.Sample -> Real) (minusMass plusMass : Real) :
    (∑ m : D.Sample,
        (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass m - seed m)) = minusMass + plusMass := by
  calc
    (∑ m : D.Sample,
        (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass m - seed m)) =
        (∑ m : D.Sample,
          bankPaperCanonicalUniformCellIncrement
            D (none, .minus) minusMass m) +
        ∑ m : D.Sample,
          bankPaperCanonicalUniformCellIncrement
            D (none, .plus) plusMass m := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalTwoZeroHeadCellRebalance
      ring
    _ = minusMass + plusMass := by
      rw [sum_bankPaperCanonicalUniformCellIncrement,
        sum_bankPaperCanonicalUniformCellIncrement]

/-- Literal active mass after the two pool changes. -/
theorem bankPaperCanonicalLiteralActiveMass_twoZeroHeadCellRebalance
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (seed : D.Sample -> Real) (minusMass plusMass : Real) :
    bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
          minusMass plusMass) =
      bankPaperCanonicalLiteralActiveMass D seed +
        minusMass + plusMass := by
  unfold bankPaperCanonicalLiteralActiveMass
  have hchange := sum_bankPaperCanonicalTwoZeroHeadCellRebalance_sub
    D seed minusMass plusMass
  rw [add_assoc, ← hchange]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- For a canonical scaled seed, the preceding identity reads
`q + deltaMinus + deltaPlus` with no normalization surrogate. -/
theorem bankPaperCanonicalLiteralActiveMass_rebalancedScaledActiveSeed
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (q minusMass plusMass : Real) :
    bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalTwoZeroHeadCellRebalance D
          (bankPaperCanonicalScaledActiveSeed T q)
          minusMass plusMass) = q + minusMass + plusMass := by
  rw [bankPaperCanonicalLiteralActiveMass_twoZeroHeadCellRebalance,
    bankPaperCanonicalLiteralActiveMass_scaledActiveSeed]

/-- Ambient push-forward is linear with respect to subtraction of tagged
seed weights. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_sub
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    (seed₁ seed₀ : D.Sample -> Real) (a : Nat) :
    bankPaperCanonicalActiveSeedAmbientWeight D seed₁ a -
        bankPaperCanonicalActiveSeedAmbientWeight D seed₀ a =
      bankPaperCanonicalActiveSeedAmbientWeight D
        (fun m => seed₁ m - seed₀ m) a := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hvalue : D.value m = a <;> simp [hvalue]

/-- A tagged signed seed sums correctly over any ambient support containing
every coordinate on which that signed seed is nonzero. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_of_changeSupport
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (change : D.Sample -> Real)
    (support : Finset Nat)
    (hchange : forall m : D.Sample,
      change m ≠ 0 -> D.value m ∈ support) :
    (∑ a ∈ support,
      bankPaperCanonicalActiveSeedAmbientWeight D change a) =
        ∑ m : D.Sample, change m := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hm : change m = 0
  · simp [hm]
  · rw [Finset.sum_eq_single (D.value m)]
    · simp
    · intro a _ha hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (hchange m hm)).elim

/-- A two-zero-head-cell change is supported on those two cells and nowhere
else.  Thus it is carried by any ambient pool containing both literal cell
images. -/
theorem bankPaperCanonicalTwoZeroHeadCellRebalance_changeSupport
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (seed : D.Sample -> Real) (minusMass plusMass : Real)
    (support : Finset Nat)
    (hminus : forall m : D.Sample,
      D.cellOf m = (none, .minus) -> D.value m ∈ support)
    (hplus : forall m : D.Sample,
      D.cellOf m = (none, .plus) -> D.value m ∈ support) :
    forall m : D.Sample,
      bankPaperCanonicalTwoZeroHeadCellRebalance D seed
          minusMass plusMass m - seed m ≠ 0 ->
        D.value m ∈ support := by
  intro m hm
  by_cases hmMinus : D.cellOf m = (none, .minus)
  · exact hminus m hmMinus
  · by_cases hmPlus : D.cellOf m = (none, .plus)
    · exact hplus m hmPlus
    · exfalso
      apply hm
      simp [bankPaperCanonicalTwoZeroHeadCellRebalance,
        bankPaperCanonicalUniformCellIncrement, hmMinus, hmPlus]

/-- On an ambient pool containing the two zero-head cells, their pushed
forward mass change is exactly the requested signed total. -/
theorem sum_bankPaperCanonicalTwoZeroHeadCellRebalance_ambient_sub
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (seed : D.Sample -> Real) (minusMass plusMass : Real)
    (support : Finset Nat)
    (hminus : forall m : D.Sample,
      D.cellOf m = (none, .minus) -> D.value m ∈ support)
    (hplus : forall m : D.Sample,
      D.cellOf m = (none, .plus) -> D.value m ∈ support) :
    (∑ a ∈ support,
        (bankPaperCanonicalActiveSeedAmbientWeight D
              (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
                minusMass plusMass) a -
          bankPaperCanonicalActiveSeedAmbientWeight D seed a)) =
      minusMass + plusMass := by
  calc
    (∑ a ∈ support,
        (bankPaperCanonicalActiveSeedAmbientWeight D
              (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
                minusMass plusMass) a -
          bankPaperCanonicalActiveSeedAmbientWeight D seed a)) =
        ∑ a ∈ support,
          bankPaperCanonicalActiveSeedAmbientWeight D
            (fun m =>
              bankPaperCanonicalTwoZeroHeadCellRebalance D seed
                  minusMass plusMass m - seed m) a := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact bankPaperCanonicalActiveSeedAmbientWeight_sub D _ _ a
    _ = ∑ m : D.Sample,
        (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass m - seed m) := by
      exact sum_bankPaperCanonicalActiveSeedAmbientWeight_of_changeSupport
        D _ support
          (bankPaperCanonicalTwoZeroHeadCellRebalance_changeSupport
            D seed minusMass plusMass support hminus hplus)
    _ = minusMass + plusMass :=
      sum_bankPaperCanonicalTwoZeroHeadCellRebalance_sub
        D seed minusMass plusMass

/-! ## The head-free correction-pool ledger -/

/-- Every coordinate in the guarded broad correction pool has zero
valuation at every head prime.  This is the exact finite reason why either
of the paper's zero-head pool mass changes is invisible to the head ledger. -/
theorem factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar : Real} {q a : Nat}
    (hqPrime : q.Prime) (hqW : q <= B.sampleData.W)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    a.factorization q = 0 := by
  have haRaw :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
      certificate deltaStar B.sampleData.W K 1 ha
  have haData := mem_completeRoughRowFiber.mp haRaw
  have haHeadFree := mem_roughHeadFree.mp haData.1
  have hqHead : q ∈ primesUpTo B.sampleData.W :=
    mem_primesUpTo.mpr ⟨hqPrime, hqW⟩
  have hqDvd : q ∣ roughHeadModulus B.sampleData.W := by
    unfold roughHeadModulus
    exact Finset.dvd_prod_of_mem (fun r : Nat => r) hqHead
  have hcop : Nat.Coprime a q :=
    Nat.Coprime.of_dvd_right hqDvd haHeadFree.2
  exact Nat.factorization_eq_zero_of_not_dvd
    (hqPrime.coprime_iff_not_dvd.mp hcop.symm)

/-- Consequently the local additive replacement has zero head-prime
valuation moment independently of the actual weights placed in that
head-free correction pool. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment_eq_zero_of_headPrime
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {q : Nat} (hqPrime : q.Prime) (hqW : q <= B.sampleData.W) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
      B R certificate deltaStar betaProt baseSelector activeSeed q = 0 := by
  unfold bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment
  apply Finset.sum_eq_zero
  intro a ha
  rw [factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime
    B R certificate hqPrime hqW ha]
  simp

/-- Since the head part of the minimized ledger is automatic on the
head-free pool, an explicit integer local mass change constructs the whole
prebridge ledger. -/
theorem bankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger_of_rowChange
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (rowChange : Int)
    (hrowChange :
      (∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        (betaProt / B.L +
              bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData activeSeed a -
            baseSelector a)) = (rowChange : Real)) :
    BankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger (K := K)
      B R certificate deltaStar betaProt baseSelector activeSeed := by
  refine ⟨⟨rowChange, hrowChange⟩, ?_⟩
  intro q hqPrime hqW
  exact
    bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment_eq_zero_of_headPrime
      B R certificate baseSelector activeSeed hqPrime hqW

/-- The selector immediately before the two-pool adjustment.  On the
head-free correction pool it consists of the frozen protected layer plus
the old structured active seed; all other coordinates are retained from an
arbitrary already-fixed selector. -/
def bankPaperCanonicalTwoZeroHeadCellSourceSelector
    {P : Finset Nat} {GeoBand : Type*}
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData (PaperHeadSimplex.Tag P) GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (outsideSelector : Nat -> Real) (a : Nat) : Real :=
  if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 then
    betaProt / B.L +
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a
  else outsideSelector a

/-- The paper's two literal zero-head cells construct the minimized
prebridge ledger.  The only numerical datum is their combined signed mass,
which must be the desired integer row change.  No head-moment hypothesis is
needed: it follows from head freedom of the correction pool. -/
theorem bankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger_twoZeroHeadCells
    {P : Finset Nat} {GeoBand : Type*}
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData (PaperHeadSimplex.Tag P) GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (outsideSelector : Nat -> Real)
    (minusMass plusMass : Real) (rowChange : Int)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hmass : minusMass + plusMass = (rowChange : Real)) :
    BankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger (K := K)
      B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K) B R certificate
          deltaStar betaProt oldSeed outsideSelector)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          minusMass plusMass) := by
  apply bankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger_of_rowChange
    B R certificate
      (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K) B R certificate
        deltaStar betaProt oldSeed outsideSelector)
      (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
        minusMass plusMass) rowChange
  calc
    (∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      (betaProt / B.L +
            bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                oldSeed minusMass plusMass) a -
          bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K) B R certificate
            deltaStar betaProt oldSeed outsideSelector a)) =
      ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        (bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                oldSeed minusMass plusMass) a -
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a) := by
      apply Finset.sum_congr rfl
      intro a ha
      unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
      rw [if_pos ha]
      ring
    _ = minusMass + plusMass := by
      exact sum_bankPaperCanonicalTwoZeroHeadCellRebalance_ambient_sub
        B.sampleData oldSeed minusMass plusMass
        (R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1) hminus hplus
    _ = (rowChange : Real) := hmass

/-! ## Structured head-cell realization -/

/-- Summing a uniform baseline coordinate statistic which depends only on
the structured cell recovers the corresponding cell-mass sum. -/
theorem sum_baselineBaseWeight_mul_cellFunction
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head}
    (A : BaselineAllocation D) (f : Cell Head -> Real) :
    (∑ m : D.Sample, A.baseWeight m * f (D.cellOf m)) =
      ∑ cell : Cell Head, A.cellMass cell * f cell := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro cell _hcell
  simp only [BaselineAllocation.baseWeight, StructuredSampleData.cellOf]
  have hcard : (Fintype.card (D.SampleAt cell) : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.sampleAt_card_pos cell)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

/-- The canonical scaled seed realizes every prescribed head-tag linear
moment with the literal active-mass factor in front. -/
theorem sum_bankPaperCanonicalScaledActiveSeed_mul_headFunction
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    (q : Real) (phi : Head -> Real) :
    (∑ m : D.Sample,
        bankPaperCanonicalScaledActiveSeed T q m *
          phi (D.cellOf m).1) =
      q * ∑ h : Head, T.beta h * phi h := by
  calc
    (∑ m : D.Sample,
        bankPaperCanonicalScaledActiveSeed T q m *
          phi (D.cellOf m).1) =
      q * ∑ m : D.Sample,
        T.baseline.baseWeight m * phi (D.cellOf m).1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalScaledActiveSeed
      ring
    _ = q * ∑ cell : Cell Head,
        T.baseline.cellMass cell * phi cell.1 := by
      apply congrArg (q * ·)
      simpa using
        (sum_baselineBaseWeight_mul_cellFunction
          T.baseline (fun cell => phi cell.1))
    _ = q * ∑ cell : Cell Head,
        T.baseline.normalizedCellMass cell * phi cell.1 := by
      apply congrArg (q * ·)
      apply Finset.sum_congr rfl
      intro cell _hcell
      unfold BaselineAllocation.normalizedCellMass
      rw [T.baseline_totalMass, div_one]
    _ = q * ∑ h : Head, T.beta h * phi h := by
      rw [T.headMoment phi]

/-- Weighted ambient push-forward over a support containing all structured
values is exactly the corresponding tagged weighted sum. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (seed : D.Sample -> Real)
    (support : Finset Nat)
    (hvalues : forall m : D.Sample, D.value m ∈ support)
    (p : Nat) :
    (∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight D seed a *
          valuation p a) =
      ∑ m : D.Sample, seed m * valuation p (D.value m) := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalues m)).elim

/-- The scaled structured head-simplex seed has exactly the unnormalized
head-prime moment stored in `HeadSimplexReserve`.  This is the finite
coordinate version of the paper's head-cell realization. -/
theorem sum_bankPaperCanonicalScaledActiveSeed_mul_paperHeadValuation
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    (p : {p : Nat // p ∈ P}) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T Rhead.activeMass m *
          valuation p.1 (B.sampleData.value m)) = Rhead.target p := by
  dsimp only
  let T := B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical
  have hvaluation : forall m : B.sampleData.Sample,
      valuation p.1 (B.sampleData.value m) =
        (PaperHeadSimplex.exponent P Rhead.exponent
          (B.sampleData.cellOf m).1 p.1 : Real) := by
    intro m
    have hpMem : p.1 ∈
        (B.sampleData.pattern (B.sampleData.cellOf m).1).primes := by
      rw [hpattern]
      exact p.2
    have hm := B.sampleData.value_matches_head m p.1 hpMem
    simpa [valuation, hpattern, PaperHeadSimplex.pattern] using
      congrArg (fun k : Nat => (k : Real)) hm
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T Rhead.activeMass m *
          valuation p.1 (B.sampleData.value m)) =
      ∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T Rhead.activeMass m *
          (PaperHeadSimplex.exponent P Rhead.exponent
            (B.sampleData.cellOf m).1 p.1 : Real) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [hvaluation m]
    _ = Rhead.activeMass *
        ∑ h : PaperHeadSimplex.Tag P,
          T.beta h *
            (PaperHeadSimplex.exponent P Rhead.exponent h p.1 : Real) :=
      sum_bankPaperCanonicalScaledActiveSeed_mul_headFunction
        T Rhead.activeMass
          (fun h =>
            (PaperHeadSimplex.exponent P Rhead.exponent h p.1 : Real))
    _ = Rhead.activeMass * (Rhead.target p / Rhead.activeMass) := by
      apply congrArg (Rhead.activeMass * ·)
      change (∑ h : PaperHeadSimplex.Tag P,
        Rhead.beta h *
          (PaperHeadSimplex.exponent P Rhead.exponent h p.1 : Real)) = _
      exact Rhead.beta_exponent_moment p
    _ = Rhead.target p := by
      field_simp [ne_of_gt Rhead.activeMass_pos]

/-- Ambient form of the same exact structured head-cell realization. -/
theorem sum_bankPaperCanonicalScaledActiveSeedAmbient_mul_paperHeadValuation
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    (support : Finset Nat)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ support)
    (p : {p : Nat // p ∈ P}) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    (∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass) a *
          valuation p.1 a) = Rhead.target p := by
  dsimp only
  rw [sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
    B.sampleData _ support hvalues p.1]
  exact sum_bankPaperCanonicalScaledActiveSeed_mul_paperHeadValuation
    B hprime Rhead I hlo hhi Kphysical hpattern p

/-- The smallest exact placement theorem for the structured head cells.
Once their numerical values lie in a supplied finite support, the ambient
scaled seed has exactly the reserve active mass and every prescribed head
moment.  No broad-pool membership, capacity, or feasibility assertion is
folded into this finite identity. -/
theorem bankPaperCanonicalStructuredHeadCellMomentLedger
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    (support : Finset Nat)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ support) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    (∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
          (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass) a) =
        Rhead.activeMass ∧
      forall p : {p : Nat // p ∈ P},
        (∑ a ∈ support,
            bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
                (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass) a *
              valuation p.1 a) = Rhead.target p := by
  dsimp only
  constructor
  · rw [sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
      B.sampleData
        (bankPaperCanonicalScaledActiveSeed
          (B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical)
          Rhead.activeMass)
        support hvalues,
      bankPaperCanonicalLiteralActiveMass_scaledActiveSeed]
  · intro p
    exact
      sum_bankPaperCanonicalScaledActiveSeedAmbient_mul_paperHeadValuation
        B hprime Rhead I hlo hhi Kphysical hpattern support hvalues p

/-- A uniform change in either physical copy of the zero head cell has
literally zero valuation moment at every prime represented in the head
simplex. -/
theorem sum_bankPaperCanonicalUniformZeroHeadCellIncrement_mul_valuation_eq_zero
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : D.pattern = PaperHeadSimplex.pattern P hprime E)
    (sigma : PhysicalSign) (mass : Real)
    (p : {p : Nat // p ∈ P}) :
    (∑ m : D.Sample,
        bankPaperCanonicalUniformCellIncrement D (none, sigma) mass m *
          valuation p.1 (D.value m)) = 0 := by
  apply Finset.sum_eq_zero
  intro m _hm
  by_cases hcell : D.cellOf m = (none, sigma)
  · have hpMem : p.1 ∈ (D.pattern (D.cellOf m).1).primes := by
      rw [hpattern]
      exact p.2
    have hmatch := D.value_matches_head m p.1 hpMem
    have hzero : (D.value m).factorization p.1 = 0 := by
      simpa [hpattern, hcell, PaperHeadSimplex.pattern] using hmatch
    rw [show valuation p.1 (D.value m) = 0 by
      simp [valuation, hzero]]
    ring
  · simp [bankPaperCanonicalUniformCellIncrement, hcell]

/-- Therefore both literal zero-head pool changes preserve every structured
head-prime moment exactly. -/
theorem sum_bankPaperCanonicalTwoZeroHeadCellRebalance_mul_valuation_eq
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : D.pattern = PaperHeadSimplex.pattern P hprime E)
    (seed : D.Sample -> Real) (minusMass plusMass : Real)
    (p : {p : Nat // p ∈ P}) :
    (∑ m : D.Sample,
        bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass m * valuation p.1 (D.value m)) =
      ∑ m : D.Sample, seed m * valuation p.1 (D.value m) := by
  calc
    (∑ m : D.Sample,
        bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass m * valuation p.1 (D.value m)) =
      (∑ m : D.Sample, seed m * valuation p.1 (D.value m)) +
      (∑ m : D.Sample,
        bankPaperCanonicalUniformCellIncrement
            D (none, .minus) minusMass m *
          valuation p.1 (D.value m)) +
      ∑ m : D.Sample,
        bankPaperCanonicalUniformCellIncrement
            D (none, .plus) plusMass m *
          valuation p.1 (D.value m) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalTwoZeroHeadCellRebalance
      ring
    _ = ∑ m : D.Sample, seed m * valuation p.1 (D.value m) := by
      rw [sum_bankPaperCanonicalUniformZeroHeadCellIncrement_mul_valuation_eq_zero
          D hprime E hpattern .minus minusMass p,
        sum_bankPaperCanonicalUniformZeroHeadCellIncrement_mul_valuation_eq_zero
          D hprime E hpattern .plus plusMass p]
      ring

/-- Combining the structured head-cell realization with the two zero-head
pool changes retains the prescribed unnormalized head target exactly. -/
theorem sum_bankPaperCanonicalRebalancedScaledActiveSeed_mul_paperHeadValuation
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    (minusMass plusMass : Real)
    (p : {p : Nat // p ∈ P}) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass)
            minusMass plusMass m *
          valuation p.1 (B.sampleData.value m)) = Rhead.target p := by
  dsimp only
  rw [sum_bankPaperCanonicalTwoZeroHeadCellRebalance_mul_valuation_eq
    B.sampleData hprime Rhead.exponent hpattern
      (bankPaperCanonicalScaledActiveSeed
        (B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical)
        Rhead.activeMass)
      minusMass plusMass p]
  exact sum_bankPaperCanonicalScaledActiveSeed_mul_paperHeadValuation
    B hprime Rhead I hlo hhi Kphysical hpattern p

/-! ## Exact support boundary -/

/-- A genuine nonzero simplex vertex cannot lie in the repository's
`roughHeadFree` correction pool.  Hence the two zero-head cells may be
placed there, but the full structured head realization must only be required
to lie in the surrounding guarded smooth row (or candidate set).  This is
the precise support mismatch left by the current additive-refinement API. -/
theorem not_all_paperHeadSimplex_values_mem_guardedBroadCorrectionPool
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
    (deltaStar : Real)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    (p : {p : Nat // p ∈ P})
    (hpW : p.1 <= B.sampleData.W) :
    ¬ forall m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
  intro hvalues
  let cell : Cell (PaperHeadSimplex.Tag P) := (some p, .minus)
  obtain ⟨a, ha⟩ := B.sampleData.cell_nonempty cell
  let m : B.sampleData.Sample := ⟨cell, ⟨a, ha⟩⟩
  have hmCell : B.sampleData.cellOf m = (some p, .minus) := by
    rfl
  have hpPrime : p.1.Prime := hprime p.1 p.2
  have hzero : (B.sampleData.value m).factorization p.1 = 0 :=
    factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime
      B R certificate hpPrime hpW (hvalues m)
  have hpMem : p.1 ∈
      (B.sampleData.pattern (B.sampleData.cellOf m).1).primes := by
    rw [hpattern]
    exact p.2
  have hmatch := B.sampleData.value_matches_head m p.1 hpMem
  have hvertex :
      (B.sampleData.value m).factorization p.1 = Rhead.exponent := by
    rw [hpattern, hmCell] at hmatch
    simpa [PaperHeadSimplex.pattern] using hmatch
  have hexponentPos := Rhead.exponent_pos
  omega

/-! ## Signed whole-smooth-row placement ledger -/

/-- The signed valuation change of the corrected structured placement on
the complete guarded smooth row.  Unlike the older correction-pool moment,
this sees every structured active coordinate, including the nonzero head
cells which cannot lie in the head-free broad pool. -/
def bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (q : Nat) : Real :=
  ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
    (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed a -
        baseSelector a) * (a.factorization q : Real)

/-- The exact signed ledger needed by the corrected whole-row placement.
It records that the structured image is supported on the guarded smooth
row, that the total smooth-row change is an integer, and that every fixed
head-prime moment is unchanged.  Medium-prime moments are deliberately not
constrained: Proposition 8.7 fits them later. -/
def BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) : Prop :=
  bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 ∧
    (∃ rowChange : Int,
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed a -
          baseSelector a)) = (rowChange : Real)) ∧
    ∀ q : Nat, q.Prime -> q <= B.sampleData.W ->
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q = 0

/-- Every valuation moment of the corrected placement above the smooth
cutoff vanishes.  This uses the complete smooth row itself, so it applies
equally to the old head-free correction pool and to the added structured
head coordinates. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment_eq_zero_of_yNat_lt
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {q : Nat}
    (hqPrime : q.Prime) (hqLarge : yNat B.sampleData.n < q) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
      B R certificate deltaStar betaProt baseSelector activeSeed q = 0 := by
  unfold
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
  apply Finset.sum_eq_zero
  intro a ha
  have haData := mem_completeRoughRowFiber.mp ha
  have haRaw : a ∈ roughRawCandidateSet B.sampleData.n
      (upperTailLength c B.sampleData.n) K :=
    R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
      certificate deltaStar K haData.1
  have haPos : 0 < a := by
    rw [roughRawCandidateSet, Finset.mem_union] at haRaw
    rcases haRaw with haHigh | haBroad
    · rw [roughHighLowerBlock, Finset.mem_Ioc] at haHigh
      omega
    · rw [roughBroadLowerBlock, Finset.mem_Ioc] at haBroad
      omega
  have haSmooth :
      a ∈ Nat.smoothNumbers (yNat B.sampleData.n + 1) :=
    (completeRoughLabel_eq_one_iff_mem_smoothNumbers haPos).mp haData.2
  have hnotDvd : ¬q ∣ a := by
    intro hqa
    have hqSmall :=
      (Nat.mem_smoothNumbers').mp haSmooth q hqPrime hqa
    omega
  rw [Nat.factorization_eq_zero_of_not_dvd hnotDvd]
  simp

/-- The signed smooth-row moment is exactly the change of the weighted
candidate sum.  The corrected placement equals the base selector off the
smooth row once the structured image is known to lie in that row. -/
theorem sum_guardedCandidates_structuredAdditivePlacement_factorization_sub_base_eq_moment
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (q : Nat) :
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed a *
          (a.factorization q : Real)) -
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          baseSelector a * (a.factorization q : Real) =
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q := by
  rw [← Finset.sum_sub_distrib]
  have hsmooth :
      R.roughCanonicalGuardedRow certificate deltaStar K 1 ⊆
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro a ha
    exact (mem_completeRoughRowFiber.mp ha).1
  calc
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed a *
            (a.factorization q : Real) -
          baseSelector a * (a.factorization q : Real))) =
      ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed a *
            (a.factorization q : Real) -
          baseSelector a * (a.factorization q : Real)) := by
      symm
      apply Finset.sum_subset hsmooth
      intro a _haCandidate haNotSmooth
      rw [
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_base_outside_smoothRow
          B R certificate baseSelector activeSeed hactiveSmooth haNotSmooth]
      ring
    _ = bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q := by
      unfold
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
      apply Finset.sum_congr rfl
      intro a _ha
      ring

/-- Exact transport of the literal selector valuation deficit under the
corrected whole-row placement. -/
theorem bankPaperCanonicalSelectorValuationDeficit_structuredAdditivePlacement_eq_sub_moment
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (q : Nat) :
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed) q =
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          baseSelector q -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed q := by
  have hmoment :=
    sum_guardedCandidates_structuredAdditivePlacement_factorization_sub_base_eq_moment
      (betaProt := betaProt)
      B R certificate baseSelector activeSeed hactiveSmooth q
  unfold bankPaperCanonicalSelectorValuationDeficit
  rw [← hmoment]
  ring

/-- An integral signed change on the complete smooth row preserves every
complete-row integer quota for the corrected placement.  Other rows are
unchanged pointwise. -/
theorem bankPaperCanonicalSelectorRowIntegral_structuredAdditivePlacement_of_prebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hbase : BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hledger :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) := by
  intro label hlabelMem
  obtain ⟨quota, hquota⟩ := hbase label hlabelMem
  by_cases hlabel : label = 1
  · subst label
    obtain ⟨rowChange, hrowChange⟩ := hledger.2.1
    refine ⟨quota + rowChange, ?_⟩
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed a) =
        ((quota + rowChange : Int) : Real)
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          baseSelector a) = (quota : Real) at hquota
    have hchange :
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            baseSelector a = (rowChange : Real) := by
      rw [← Finset.sum_sub_distrib]
      exact hrowChange
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed a) =
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          baseSelector a) + (rowChange : Real) := by linarith
      _ = (quota : Real) + (rowChange : Real) := by rw [hquota]
      _ = ((quota + rowChange : Int) : Real) := by norm_num
  · refine ⟨quota, ?_⟩
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed a) =
        (quota : Real)
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          baseSelector a) = (quota : Real) at hquota
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          baseSelector a := by
        apply Finset.sum_congr rfl
        intro a ha
        apply
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_base_outside_smoothRow
            B R certificate baseSelector activeSeed hledger.1
        intro haSmooth
        have hsmoothEq := (mem_completeRoughRowFiber.mp haSmooth).2
        have hlabelEq := (mem_completeRoughRowFiber.mp ha).2
        exact hlabel (hlabelEq.symm.trans hsmoothEq)
      _ = (quota : Real) := hquota

/-- The signed head moments from the ledger, together with automatic
vanishing above `y`, preserve exact selector-target agreement outside the
medium-prime tangent band. -/
theorem bankPaperCanonicalSelectorDeficitSupportedOnPrimeBand_structuredAdditivePlacement_of_prebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hbase : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hledger :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) := by
  intro q hqPrime hqNotBand
  have hmoment :
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q = 0 := by
    by_cases hqHead : q <= B.sampleData.W
    · exact hledger.2.2 q hqPrime hqHead
    · have hWq : B.sampleData.W < q := Nat.lt_of_not_ge hqHead
      have hyq : yNat B.sampleData.n < q := by
        by_contra hnotY
        have hqy : q <= yNat B.sampleData.n := Nat.le_of_not_gt hnotY
        exact hqNotBand (mem_primeBand.mpr ⟨hqPrime, hWq, hqy⟩)
      exact
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment_eq_zero_of_yNat_lt
          B R certificate baseSelector activeSeed hqPrime hyq
  rw [
    bankPaperCanonicalSelectorValuationDeficit_structuredAdditivePlacement_eq_sub_moment
      B R certificate fixed baseSelector activeSeed hledger.1 q,
    hmoment, sub_zero]
  exact hbase q hqPrime hqNotBand

/-- Minimal selector state consumed before Proposition 8.7.

The structured placement needs only candidate feasibility, complete-rough-row
integrality, and exact selector-target agreement outside the medium-prime
band.  Prime-band balance and tangent residual bounds are deliberately absent:
the subsequent Proposition 8.7 endpoint constructs them. -/
structure BankPaperCanonicalSelectorSourceState
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    (selector : Nat -> Real) : Prop where
  feasible : ∀ a ∈ candidates,
    0 <= selector a ∧ selector a <= 1
  rowIntegral :
    BankPaperCanonicalSelectorRowIntegral n candidates selector
  deficitSupportedOnPrimeBand :
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
      R certificate fixed candidates selector

/-- A full rounded-selector tangent input projects to the minimal source
state used before Proposition 8.7. -/
theorem bankPaperCanonicalSelectorSourceState_of_roundedSelectorTangentInput
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
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector) :
    BankPaperCanonicalSelectorSourceState (W := W)
      R certificate fixed candidates selector := by
  have hstate :=
    bankPaperCanonicalRoundedSelectorTangentInput_selectorState S
  exact
    { feasible := hstate.1
      rowIntegral := hstate.2.1
      deficitSupportedOnPrimeBand := hstate.2.2.2 }

/-- The corrected whole-row prebridge placement statement: feasibility,
integer complete-row quotas, and exact agreement outside the tangent band.
It contains no medium-prime balance or prefix bound, since those are
produced by Proposition 8.7. -/
def BankPaperCanonicalGuardedStructuredAdditivePlacement
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) : Prop :=
  let placed :=
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
      B R certificate deltaStar betaProt baseSelector activeSeed
  (∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= placed a ∧ placed a <= 1) ∧
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      placed ∧
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      placed

/-- Feasibility of the corrected selector and the signed whole-row ledger
give the corrected additive placement predicate exactly. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacement_of_prebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hfeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed a ∧
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed a <= 1)
    (hbaseRow : BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hbaseSupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hledger :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector activeSeed := by
  unfold BankPaperCanonicalGuardedStructuredAdditivePlacement
  refine ⟨hfeasible, ?_, ?_⟩
  · exact
      bankPaperCanonicalSelectorRowIntegral_structuredAdditivePlacement_of_prebridgeMomentLedger
        B R certificate baseSelector activeSeed hbaseRow hledger
  · exact
      bankPaperCanonicalSelectorDeficitSupportedOnPrimeBand_structuredAdditivePlacement_of_prebridgeMomentLedger
        B R certificate fixed baseSelector activeSeed hbaseSupport hledger

/-- The exact pre-bridge placement statement still required of the
protected-plus-active smooth refinement.  It contains feasibility, the
integer complete-row ledger, and exact prime agreement outside the tangent
band.  It deliberately contains no medium-prime band balance, pointwise
bound, or prefix bound: those are produced by the subsequent P87 fit. -/
def BankPaperCanonicalGuardedSmoothAdditivePlacement
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) : Prop :=
  let refined :=
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
      deltaStar betaProt baseSelector activeSeed
  (∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= refined a ∧ refined a <= 1) ∧
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      refined ∧
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      refined

/-- An integral local smooth-row change preserves complete-row
integrality.  Nonsmooth rows are unchanged pointwise. -/
theorem bankPaperCanonicalSelectorRowIntegral_additiveRefinement_of_prebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hbase : BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hledger :
      BankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
        deltaStar betaProt baseSelector activeSeed) := by
  intro label hlabelMem
  obtain ⟨quota, hquota⟩ := hbase label hlabelMem
  by_cases hlabel : label = 1
  · subst label
    obtain ⟨rowChange, hrowChange⟩ := hledger.1
    refine ⟨quota + rowChange, ?_⟩
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
            deltaStar betaProt baseSelector activeSeed a) =
        ((quota + rowChange : Int) : Real)
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          baseSelector a) = (quota : Real) at hquota
    have hchange :
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            baseSelector a = (rowChange : Real) :=
      (sum_guardedSmoothRow_additiveRefinement_sub_base_eq_pool
        B R certificate baseSelector activeSeed).trans hrowChange
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
            deltaStar betaProt baseSelector activeSeed a) =
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          baseSelector a) + (rowChange : Real) := by linarith
      _ = (quota : Real) + (rowChange : Real) := by rw [hquota]
      _ = ((quota + rowChange : Int) : Real) := by norm_num
  · refine ⟨quota, ?_⟩
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
            deltaStar betaProt baseSelector activeSeed a) = (quota : Real)
    change
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          baseSelector a) = (quota : Real) at hquota
    rw [sum_guardedRow_additiveRefinement_eq_base_of_label_ne_one
      B R certificate baseSelector activeSeed hlabel]
    exact hquota

/-- Head-prime zero moments and smooth support preserve exact target
agreement outside the tangent band.  No medium-prime equality is needed. -/
theorem bankPaperCanonicalSelectorDeficitSupportedOnPrimeBand_additiveRefinement_of_prebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hbase : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hledger :
      BankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
        deltaStar betaProt baseSelector activeSeed) := by
  intro q hqPrime hqNotBand
  have hmoment :
      bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q = 0 := by
    by_cases hqHead : q <= B.sampleData.W
    · exact hledger.2 q hqPrime hqHead
    · have hWq : B.sampleData.W < q := Nat.lt_of_not_ge hqHead
      have hyq : yNat B.sampleData.n < q := by
        by_contra hnotY
        have hqy : q <= yNat B.sampleData.n := Nat.le_of_not_gt hnotY
        exact hqNotBand (mem_primeBand.mpr ⟨hqPrime, hWq, hqy⟩)
      exact
        bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment_eq_zero_of_yNat_lt
          B R certificate baseSelector activeSeed hqPrime hyq
  rw [
    bankPaperCanonicalSelectorValuationDeficit_additiveRefinement_eq_sub_moment
      B R certificate fixed baseSelector activeSeed q,
    hmoment, sub_zero]
  exact hbase q hqPrime hqNotBand

/-- The minimized prebridge ledger, base selector state, and feasibility
on the replaced pool give exactly the additive placement predicate. -/
theorem bankPaperCanonicalGuardedSmoothAdditivePlacement_of_prebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hbaseFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= baseSelector a ∧ baseSelector a <= 1)
    (hbaseRow : BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hbaseSupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hpoolFeasible : ∀ a ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      0 <= bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
          deltaStar betaProt baseSelector activeSeed a ∧
        bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
          deltaStar betaProt baseSelector activeSeed a <= 1)
    (hledger :
      BankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalGuardedSmoothAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector activeSeed := by
  unfold BankPaperCanonicalGuardedSmoothAdditivePlacement
  refine ⟨?_, ?_, ?_⟩
  · intro a haCandidate
    by_cases haPool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · exact hpoolFeasible a haPool
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
        B R certificate baseSelector activeSeed haPool]
      exact hbaseFeasible a haCandidate
  · exact
      bankPaperCanonicalSelectorRowIntegral_additiveRefinement_of_prebridgeMomentLedger
        B R certificate baseSelector activeSeed hbaseRow hledger
  · exact
      bankPaperCanonicalSelectorDeficitSupportedOnPrimeBand_additiveRefinement_of_prebridgeMomentLedger
        B R certificate fixed baseSelector activeSeed hbaseSupport hledger

/-- A rounded continuation selector supplies all base-state hypotheses for
the minimized prebridge ledger adapter.  Its medium-prime fields are not
used. -/
theorem bankPaperCanonicalGuardedSmoothAdditivePlacement_of_roundedSelector_prebridgeMomentLedger
    {Head GeoBand TangentBand : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    [DecidableEq TangentBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (bandOf : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> TangentBand)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prefixUpper : TangentBand -> Nat -> Real)
    (Sbase : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      bandOf cellIndex pointwiseUpper prefixUpper baseSelector)
    (hpoolFeasible : ∀ a ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      0 <= bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
          deltaStar betaProt baseSelector activeSeed a ∧
        bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
          deltaStar betaProt baseSelector activeSeed a <= 1)
    (hledger :
      BankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalGuardedSmoothAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector activeSeed := by
  have hstate :=
    bankPaperCanonicalRoundedSelectorTangentInput_selectorState Sbase
  exact
    bankPaperCanonicalGuardedSmoothAdditivePlacement_of_prebridgeMomentLedger
      B R certificate fixed baseSelector activeSeed hstate.1 hstate.2.1
      hstate.2.2.2 hpoolFeasible hledger

/-- The stronger zero-moment transport criterion supplies the paper-faithful
pre-bridge placement state.  This is a sufficient adapter, not a claim that
the paper's nonlinear active placement has zero medium-prime change. -/
theorem bankPaperCanonicalGuardedSmoothAdditivePlacement_of_zeroMomentLedger
    {Head GeoBand TangentBand : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    [DecidableEq TangentBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (bandOf : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> TangentBand)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prefixUpper : TangentBand -> Nat -> Real)
    (Sbase : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      bandOf cellIndex pointwiseUpper prefixUpper baseSelector)
    (hpoolFeasible : ∀ a ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      0 <= bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
          deltaStar betaProt baseSelector activeSeed a ∧
        bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
          deltaStar betaProt baseSelector activeSeed a <= 1)
    (hledger :
      BankPaperCanonicalGuardedSmoothAdditiveRefinementZeroMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalGuardedSmoothAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector activeSeed := by
  have Srefined :=
    bankPaperCanonicalRoundedSelectorTangentInput_additiveRefinement_of_zeroMomentLedger
      B R certificate fixed baseSelector activeSeed bandOf cellIndex
      pointwiseUpper prefixUpper Sbase hpoolFeasible hledger
  have hstate :=
    bankPaperCanonicalRoundedSelectorTangentInput_selectorState Srefined
  unfold BankPaperCanonicalGuardedSmoothAdditivePlacement
  exact ⟨hstate.1, hstate.2.1, hstate.2.2.2⟩

end BankPaperRealization

/-! ## Weaker actual-endpoint preselector interface -/

/-- The actual Proposition 8.7 endpoint needs only row integrality and
outside-band deficit support from its pre-selector.  Exact endpoint band
balance, pointwise control, and the deterministic prefix bounds all come
from the P87 path and its existing prefix adapter. -/
theorem exists_bankPaperCanonicalActualP87EndpointSelector_of_rowIntegral_deficitSupported
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (hpreRow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates preSelector)
    (hpreSupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates preSelector)
    (Delta : Band -> Real) (radius : NNReal) (N Cpost : Real)
    (quota : Int)
    (Hfit : B.HasPaperProposition87Conclusion Delta radius
      (bankPaperCanonicalActualActiveMarkedTarget B R certificate
        fixed candidates preSelector activeSeed)
      N Cpost
      (bankPaperCanonicalActualFrozenValue (candidates := candidates))
      (bankPaperCanonicalActualFrozenWeight
        B.sampleData candidates preSelector activeSeed)
      quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat) :
    ∃ path : Real -> B.ParamSpace, ∃ endpoint : Nat -> Real,
      B.IsPaperProposition87Path Delta radius
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed)
        N Cpost
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed)
        quota path ∧
      endpoint = bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path ∧
      bankPaperProposition87SelectorSupport B
        (bankPaperCanonicalActualFrozenValue (candidates := candidates)) =
          candidates ∧
      (forall p : Nat,
        bankPaperProposition87FullMarkedTarget
            (bankPaperCanonicalActualFrozenValue (candidates := candidates))
            (bankPaperCanonicalActualFrozenWeight
              B.sampleData candidates preSelector activeSeed)
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate
              fixed candidates preSelector activeSeed) p =
          ((certificate.selectorTailTarget R fixed).factorization p : Real)) ∧
      (forall x, x ∉ candidates -> endpoint x = 0) ∧
      BankPaperCanonicalRoundedSelectorTangentInput
        R certificate fixed candidates B.partition.band cellIndex
        (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
          B.partition.band cellIndex)
        endpoint := by
  obtain ⟨path, hpath, hbands⟩ := Hfit
  let endpoint := bankPaperCanonicalActualP87EndpointSelector
    B candidates preSelector activeSeed path
  have hpathData := hpath
  rcases hpathData with
    ⟨_hzero, _hball, _hsize, _hderiv, _hbandMoments, _hphysical,
      _hlog, _hheads, hsmall, _hprimeLog, hmarked, hfeasible,
      _hfixed, _hmass, _hquota⟩
  have hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates :=
    fun m => bankPaperCanonicalActiveSeed_value_mem_candidates Hmeasure m
  have hselector : ∀ x ∈ candidates,
      0 <= endpoint x ∧ endpoint x <= 1 := by
    intro x _hx
    exact hfeasible 1 (by simp) x
  have hrow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates endpoint := by
    exact bankPaperCanonicalActualP87EndpointSelector_rowIntegral
      B candidates preSelector activeSeed Hmeasure hseed path hpreRow
  have hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates endpoint := by
    exact
      bankPaperCanonicalActualP87EndpointSelector_deficitSupportedOnPrimeBand
        B R certificate fixed candidates preSelector activeSeed Hmeasure hseed
        path hpreSupport hsmall
  have hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if B.partition.band p = band then
          bankPaperCanonicalTangentResidual R certificate fixed candidates
            endpoint p
        else 0) = 0 := by
    exact bankPaperCanonicalActualP87EndpointSelector_bandBalance
      B R certificate fixed candidates preSelector activeSeed hvalues path
        hbands
  have hprimeBandBalance : BankPaperCanonicalPostRoundingPrimeBandBalance
      (W := B.sampleData.W) R certificate fixed candidates endpoint := by
    exact bankPaperCanonicalActualP87EndpointSelector_primeBandBalance
      B R certificate fixed candidates preSelector activeSeed path hbalance
  have hpointwise : forall p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalTangentResidual R certificate fixed candidates
        endpoint p) <= bankPaperCanonicalActualP87PointwiseUpper B N Cpost p := by
    exact bankPaperCanonicalActualP87EndpointSelector_pointwise
      B R certificate fixed candidates preSelector activeSeed hvalues path
        N Cpost hmarked
  have Sendpoint : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates B.partition.band cellIndex
      (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
      (tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
        B.partition.band cellIndex)
      endpoint := by
    exact bankPaperCanonicalRoundedSelectorTangentInput_of_balance_pointwise
      R certificate fixed candidates B.partition.band cellIndex
      (bankPaperCanonicalActualP87PointwiseUpper B N Cpost) endpoint
      hselector hrow hprimeBandBalance hsupport hbalance hpointwise
  refine ⟨path, endpoint, hpath, rfl, ?_, ?_, ?_, Sendpoint⟩
  · exact bankPaperCanonicalActualP87SelectorSupport_eq_candidates
      B candidates hvalues
  · intro p
    exact bankPaperCanonicalActualFullMarkedTarget_eq_selectorTailTarget
      B R certificate fixed candidates preSelector activeSeed p
  · intro x hx
    exact bankPaperCanonicalActualP87EndpointSelector_eq_zero_of_not_mem
      B candidates preSelector activeSeed hvalues path hx

namespace BankPaperRealization

/-- End-to-end exact quota transport through the actual P87 endpoint.  The
literal additive replacement installs `targetQuota` by a specified integer
row change, and Proposition 8.7 preserves that exact smooth-row sum.  No
asymptotic premise occurs in this connector. -/
theorem bankPaperCanonicalGuardedSmoothFlexibleQuota_actualP87Endpoint_of_additiveRowChange
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {T : BarycentricTarget B.sampleData}
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed)
        activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace) (baseQuota targetQuota : Int)
    (hbase : BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K baseSelector baseQuota)
    (hrowChange :
      (∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        (betaProt / B.L +
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a -
          baseSelector a)) = ((targetQuota - baseQuota : Int) : Real)) :
    BankPaperCanonicalGuardedSmoothFlexibleQuota R certificate deltaStar K
      (bankPaperCanonicalActualP87EndpointSelector B
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed)
        activeSeed path) targetQuota := by
  apply bankPaperCanonicalGuardedSmoothFlexibleQuota_actualP87Endpoint
    B R certificate deltaStar
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed)
      activeSeed Hmeasure hseed path targetQuota
  exact
    bankPaperCanonicalGuardedSmoothFlexibleQuota_additiveRefinement_of_rowChange
      B R certificate baseSelector activeSeed baseQuota targetQuota hbase
        hrowChange

/-- Once the paper's additive placement lemma and the actual active-measure
constructor are supplied, Proposition 8.7 produces the complete rounded
selector tangent input.  No zero medium-prime transport premise occurs. -/
theorem exists_bankPaperCanonicalActualP87EndpointSelector_of_additivePlacement
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
        deltaStar betaProt baseSelector activeSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Hplacement : BankPaperCanonicalGuardedSmoothAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector activeSeed)
    (Delta : Band -> Real) (radius : NNReal) (N Cpost : Real)
    (quota : Int)
    (Hfit : B.HasPaperProposition87Conclusion Delta radius
      (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
          deltaStar betaProt baseSelector activeSeed)
        activeSeed)
      N Cpost
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet certificate
          deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
          deltaStar betaProt baseSelector activeSeed)
        activeSeed)
      quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat) :
    ∃ path : Real -> B.ParamSpace, ∃ endpoint : Nat -> Real,
      B.IsPaperProposition87Path Delta radius
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
            deltaStar betaProt baseSelector activeSeed)
          activeSeed)
        N Cpost
        (bankPaperCanonicalActualFrozenValue
          (candidates := R.roughCanonicalGuardedCandidateSet certificate
            deltaStar K))
        (bankPaperCanonicalActualFrozenWeight B.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
            deltaStar betaProt baseSelector activeSeed)
          activeSeed)
        quota path ∧
      endpoint = bankPaperCanonicalActualP87EndpointSelector B
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
          deltaStar betaProt baseSelector activeSeed)
        activeSeed path ∧
      bankPaperProposition87SelectorSupport B
        (bankPaperCanonicalActualFrozenValue
          (candidates := R.roughCanonicalGuardedCandidateSet certificate
            deltaStar K)) =
          R.roughCanonicalGuardedCandidateSet certificate deltaStar K ∧
      (forall p : Nat,
        bankPaperProposition87FullMarkedTarget
            (bankPaperCanonicalActualFrozenValue
              (candidates := R.roughCanonicalGuardedCandidateSet certificate
                deltaStar K))
            (bankPaperCanonicalActualFrozenWeight B.sampleData
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
                B R certificate deltaStar betaProt baseSelector activeSeed)
              activeSeed)
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
                B R certificate deltaStar betaProt baseSelector activeSeed)
              activeSeed) p =
          ((certificate.selectorTailTarget R fixed).factorization p : Real)) ∧
      (forall x,
        x ∉ R.roughCanonicalGuardedCandidateSet certificate deltaStar K ->
          endpoint x = 0) ∧
      BankPaperCanonicalRoundedSelectorTangentInput R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        B.partition.band cellIndex
        (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
          B.partition.band cellIndex)
        endpoint := by
  have hplacement := Hplacement
  unfold BankPaperCanonicalGuardedSmoothAdditivePlacement at hplacement
  exact
    exists_bankPaperCanonicalActualP87EndpointSelector_of_rowIntegral_deficitSupported
      B R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
        deltaStar betaProt baseSelector activeSeed)
      activeSeed Hmeasure hseed hplacement.2.1 hplacement.2.2
      Delta radius N Cpost quota Hfit cellIndex

/-- The corrected whole-smooth-row placement feeds the same actual
Proposition 8.7 endpoint interface.  This is the first downstream consumer
of the signed structured placement ledger: its row-integrality and
outside-band support fields are precisely the two preselector invariants
required by the generic endpoint theorem. -/
theorem exists_bankPaperCanonicalActualP87EndpointSelector_of_structuredAdditivePlacement
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Hplacement : BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector activeSeed)
    (Delta : Band -> Real) (radius : NNReal) (N Cpost : Real)
    (quota : Int)
    (Hfit : B.HasPaperProposition87Conclusion Delta radius
      (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed)
        activeSeed)
      N Cpost
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet certificate
          deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed)
        activeSeed)
      quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat) :
    ∃ path : Real -> B.ParamSpace, ∃ endpoint : Nat -> Real,
      B.IsPaperProposition87Path Delta radius
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed)
          activeSeed)
        N Cpost
        (bankPaperCanonicalActualFrozenValue
          (candidates := R.roughCanonicalGuardedCandidateSet certificate
            deltaStar K))
        (bankPaperCanonicalActualFrozenWeight B.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed)
          activeSeed)
        quota path ∧
      endpoint = bankPaperCanonicalActualP87EndpointSelector B
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed)
        activeSeed path ∧
      bankPaperProposition87SelectorSupport B
        (bankPaperCanonicalActualFrozenValue
          (candidates := R.roughCanonicalGuardedCandidateSet certificate
            deltaStar K)) =
          R.roughCanonicalGuardedCandidateSet certificate deltaStar K ∧
      (forall p : Nat,
        bankPaperProposition87FullMarkedTarget
            (bankPaperCanonicalActualFrozenValue
              (candidates := R.roughCanonicalGuardedCandidateSet certificate
                deltaStar K))
            (bankPaperCanonicalActualFrozenWeight B.sampleData
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                B R certificate deltaStar betaProt baseSelector activeSeed)
              activeSeed)
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                B R certificate deltaStar betaProt baseSelector activeSeed)
              activeSeed) p =
          ((certificate.selectorTailTarget R fixed).factorization p : Real)) ∧
      (forall x,
        x ∉ R.roughCanonicalGuardedCandidateSet certificate deltaStar K ->
          endpoint x = 0) ∧
      BankPaperCanonicalRoundedSelectorTangentInput R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        B.partition.band cellIndex
        (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
          B.partition.band cellIndex)
        endpoint := by
  have hplacement := Hplacement
  unfold BankPaperCanonicalGuardedStructuredAdditivePlacement at hplacement
  exact
    exists_bankPaperCanonicalActualP87EndpointSelector_of_rowIntegral_deficitSupported
      B R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed)
      activeSeed Hmeasure hseed hplacement.2.1 hplacement.2.2
      Delta radius N Cpost quota Hfit cellIndex

end BankPaperRealization

end

end Erdos390.WholePaper
