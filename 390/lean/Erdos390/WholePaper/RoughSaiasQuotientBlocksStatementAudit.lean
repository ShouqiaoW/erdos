import Erdos390.WholePaper.RoughSaiasQuotientBlocks

namespace Erdos390.WholePaper

open Erdos390.Full

#check roughSaiasQuotientBlock
#check roughSaiasQuotientValues
#check natDiv_eq_iff_mul_bounds
#check natDiv_eq_iff_mem_hyperbolaIoc
#check mem_roughSaiasQuotientBlock
#check natDiv_eq_of_between
#check roughSaiasQuotientBlock_eq_hyperbola_filter
#check roughSaiasQuotientBlock_subset_hyperbolaIoc
#check roughSaiasQuotientBlock_card_le
#check roughSaiasQuotientValues_subset_Iic
#check roughSaiasQuotientValues_card_le
#check roughSaiasDualQuotientInterval
#check mem_roughSaiasDualQuotientInterval
#check card_roughSaiasDualQuotientInterval
#check natDiv_succ_lt_of_le_sqrt
#check roughSaiasDualQuotientInterval_nonempty_of_le_sqrt
#check le_of_mem_roughSaiasDualQuotientInterval_of_le_sqrt
#check mem_div_Ioc_iff_exists_mem_roughSaiasDualQuotientInterval
#check natDiv_le_self_of_mem_div_Ioc_of_le_sqrt_succ
#check sum_Ico_sum_roughSaiasDualQuotientInterval
#check sum_Ico_sum_roughSaiasDualQuotientInterval_involution
#check sum_Ioc_eq_sum_roughSaiasQuotientBlocks
#check roughSaiasNaturalQuotientThetaWeight_diff_eq_on_quotientBlock
#check roughSaiasStableQuotientEdges
#check roughSaiasJumpQuotientEdges
#check roughSaiasStableQuotientValues
#check roughSaiasStableQuotientEdgeBlock
#check mem_roughSaiasStableQuotientEdges
#check mem_roughSaiasJumpQuotientEdges
#check mem_roughSaiasStableQuotientEdgeBlock
#check mem_roughSaiasStableQuotientEdgeBlock_iff_pair_mem
#check sum_Ioc_eq_sum_stableQuotientEdges_add_jumpEdges
#check roughSaiasStableQuotientEdges_eq_empty_of_le_sqrt_succ
#check roughSaiasJumpQuotientEdges_eq_Ioc_of_le_sqrt_succ
#check sum_roughSaiasStableQuotientEdges_eq_sum_edgeBlocks
#check sum_stableNaturalThetaWeight_diff_mul_eq_baseFree_edgeBlocks
#check sum_Ioc_naturalThetaWeight_diff_mul_eq_edgeBlocks_add_jumps
#check sum_jumpQuotientEdges_succ_sub_eq_endpoints_sub_stable
#check sum_jumpQuotientEdges_weighted_succ_sub_eq_endpoints_sub_residual_sub_stable
#check roughSaiasPrimeLogError_succ_sub
#check sum_jumpNaturalThetaWeight_diff_mul_primeLogError_eq_endpoints_sub_residual_sub_stable
#check roughSaiasNaturalThetaErrorTransfer_eq_localPrimeErrorResidual

example {X m q : ℕ} (hm : 0 < m) :
    X / m = q ↔ q * m ≤ X ∧ X < (q + 1) * m :=
  natDiv_eq_iff_mul_bounds hm

example {X q y Z : ℕ} (hq : 0 < q) :
    (roughSaiasQuotientBlock X q y Z).card ≤
      X / q - X / (q + 1) :=
  roughSaiasQuotientBlock_card_le hq

example (X y Z : ℕ) :
    (roughSaiasQuotientValues X y Z).card ≤ X / (y + 1) + 1 :=
  roughSaiasQuotientValues_card_le X y Z

example {X m q : ℕ} (hm : 0 < m) (hq : 0 < q) :
    q ∈ roughSaiasDualQuotientInterval X m ↔ X / q = m :=
  mem_roughSaiasDualQuotientInterval hm hq

example (X m : ℕ) :
    (roughSaiasDualQuotientInterval X m).card =
      X / m - X / (m + 1) :=
  card_roughSaiasDualQuotientInterval X m

example {X m : ℕ} (hm : 0 < m) (hmsqrt : m ≤ Nat.sqrt X) :
    X / (m + 1) < X / m :=
  natDiv_succ_lt_of_le_sqrt hm hmsqrt

example {X y M q : ℕ} (hy : 0 < y) (hyM : y ≤ M) :
    q ∈ Finset.Ioc (X / M) (X / y) ↔
      ∃ m ∈ Finset.Ico y M,
        q ∈ roughSaiasDualQuotientInterval X m :=
  mem_div_Ioc_iff_exists_mem_roughSaiasDualQuotientInterval hy hyM

example {X y M q : ℕ} (hy : 0 < y) (hyM : y ≤ M)
    (hM : M ≤ Nat.sqrt X + 1)
    (hq : q ∈ Finset.Ioc (X / M) (X / y)) :
    X / q ≤ q :=
  natDiv_le_self_of_mem_div_Ioc_of_le_sqrt_succ hy hyM hM hq

example {A : Type*} [AddCommMonoid A] (f : ℕ → ℕ → A) (X : ℕ)
    {y M : ℕ} (hy : 0 < y) (hyM : y ≤ M) :
    (∑ m ∈ Finset.Ico y M,
        ∑ q ∈ roughSaiasDualQuotientInterval X m, f m q) =
      ∑ q ∈ Finset.Ioc (X / M) (X / y), f (X / q) q :=
  sum_Ico_sum_roughSaiasDualQuotientInterval_involution f X hy hyM

example {M : Type*} [AddCommMonoid M] (f : ℕ → M) (X y Z : ℕ) :
    (∑ m ∈ Finset.Ioc y Z, f m) =
      ∑ q ∈ roughSaiasQuotientValues X y Z,
        ∑ m ∈ roughSaiasQuotientBlock X q y Z, f m :=
  sum_Ioc_eq_sum_roughSaiasQuotientBlocks f X y Z

example {X y Z m : ℕ} :
    m ∈ roughSaiasStableQuotientEdges X y Z ↔
      y < m ∧ m ≤ Z - 1 ∧ X / (m + 1) = X / m :=
  mem_roughSaiasStableQuotientEdges

example {X y Z m : ℕ} :
    m ∈ roughSaiasJumpQuotientEdges X y Z ↔
      y < m ∧ m ≤ Z - 1 ∧ X / (m + 1) ≠ X / m :=
  mem_roughSaiasJumpQuotientEdges

example {X q y Z m : ℕ} :
    m ∈ roughSaiasStableQuotientEdgeBlock X q y Z ↔
      y < m ∧ m ≤ Z - 1 ∧ X / m = q ∧ X / (m + 1) = q :=
  mem_roughSaiasStableQuotientEdgeBlock

example {X q y Z m : ℕ} :
    m ∈ roughSaiasStableQuotientEdgeBlock X q y Z ↔
      m ∈ roughSaiasQuotientBlock X q y Z ∧
        m + 1 ∈ roughSaiasQuotientBlock X q y Z :=
  mem_roughSaiasStableQuotientEdgeBlock_iff_pair_mem

example {M : Type*} [AddCommMonoid M] (f : ℕ → M) (X y Z : ℕ) :
    (∑ m ∈ Finset.Ioc y (Z - 1), f m) =
      (∑ m ∈ roughSaiasStableQuotientEdges X y Z, f m) +
        ∑ m ∈ roughSaiasJumpQuotientEdges X y Z, f m :=
  sum_Ioc_eq_sum_stableQuotientEdges_add_jumpEdges f X y Z

example {X y Z : ℕ} (hZ : Z ≤ Nat.sqrt X + 1) :
    roughSaiasStableQuotientEdges X y Z = ∅ :=
  roughSaiasStableQuotientEdges_eq_empty_of_le_sqrt_succ hZ

example {X y Z : ℕ} (hZ : Z ≤ Nat.sqrt X + 1) :
    roughSaiasJumpQuotientEdges X y Z = Finset.Ioc y (Z - 1) :=
  roughSaiasJumpQuotientEdges_eq_Ioc_of_le_sqrt_succ hZ

example {M : Type*} [AddCommMonoid M] (f : ℕ → M) (X y Z : ℕ) :
    (∑ m ∈ roughSaiasStableQuotientEdges X y Z, f m) =
      ∑ q ∈ roughSaiasStableQuotientValues X y Z,
        ∑ m ∈ roughSaiasStableQuotientEdgeBlock X q y Z, f m :=
  sum_roughSaiasStableQuotientEdges_eq_sum_edgeBlocks f X y Z

example (a : ℕ → ℝ) {X y Z : ℕ} (hy2 : 2 ≤ y) :
    (∑ m ∈ roughSaiasStableQuotientEdges X y Z,
        (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m) * a m) =
      ∑ q ∈ roughSaiasStableQuotientValues X y Z,
        ∑ m ∈ roughSaiasStableQuotientEdgeBlock X q y Z,
          (roughSaiasBaseFreeNaturalThetaWeight q (m + 1) -
            roughSaiasBaseFreeNaturalThetaWeight q m) * a m :=
  sum_stableNaturalThetaWeight_diff_mul_eq_baseFree_edgeBlocks a hy2

example (a : ℕ → ℝ) {X y Z : ℕ} (hy2 : 2 ≤ y) :
    (∑ m ∈ Finset.Ioc y (Z - 1),
        (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m) * a m) =
      (∑ q ∈ roughSaiasStableQuotientValues X y Z,
        ∑ m ∈ roughSaiasStableQuotientEdgeBlock X q y Z,
          (roughSaiasBaseFreeNaturalThetaWeight q (m + 1) -
            roughSaiasBaseFreeNaturalThetaWeight q m) * a m) +
        ∑ m ∈ roughSaiasJumpQuotientEdges X y Z,
          (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
            roughSaiasNaturalQuotientThetaWeight X m) * a m :=
  sum_Ioc_naturalThetaWeight_diff_mul_eq_edgeBlocks_add_jumps a hy2

example (w : ℕ → ℝ) {X y Z : ℕ} (hyZ : y < Z) :
    (∑ m ∈ roughSaiasJumpQuotientEdges X y Z,
        (w (m + 1) - w m)) =
      w Z - w (y + 1) -
        ∑ m ∈ roughSaiasStableQuotientEdges X y Z,
          (w (m + 1) - w m) :=
  sum_jumpQuotientEdges_succ_sub_eq_endpoints_sub_stable w hyZ

example (w a : ℕ → ℝ) {X y Z : ℕ} (hyZ : y < Z) :
    (∑ m ∈ roughSaiasJumpQuotientEdges X y Z,
        (w (m + 1) - w m) * a m) =
      w Z * a Z - w (y + 1) * a (y + 1) -
        (∑ m ∈ Finset.Ioc y (Z - 1),
          w (m + 1) * (a (m + 1) - a m)) -
        ∑ m ∈ roughSaiasStableQuotientEdges X y Z,
          (w (m + 1) - w m) * a m :=
  sum_jumpQuotientEdges_weighted_succ_sub_eq_endpoints_sub_residual_sub_stable
    w a hyZ

example (m : ℕ) :
    (FriableAsymptotic.primeLogSumUpTo (m + 1) - ((m + 1 : ℕ) : ℝ)) -
        (FriableAsymptotic.primeLogSumUpTo m - (m : ℝ)) =
      FriableAsymptotic.primeLogIncrement (m + 1) - 1 :=
  roughSaiasPrimeLogError_succ_sub m

example {X y Z : ℕ} (hyZ : y < Z) :
    (∑ m ∈ roughSaiasJumpQuotientEdges X y Z,
        (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m) *
            (FriableAsymptotic.primeLogSumUpTo m - (m : ℝ))) =
      roughSaiasNaturalQuotientThetaWeight X Z *
          (FriableAsymptotic.primeLogSumUpTo Z - (Z : ℝ)) -
        roughSaiasNaturalQuotientThetaWeight X (y + 1) *
          (FriableAsymptotic.primeLogSumUpTo (y + 1) -
            ((y + 1 : ℕ) : ℝ)) -
        (∑ m ∈ Finset.Ioc y (Z - 1),
          roughSaiasNaturalQuotientThetaWeight X (m + 1) *
            (FriableAsymptotic.primeLogIncrement (m + 1) - 1)) -
        ∑ m ∈ roughSaiasStableQuotientEdges X y Z,
          (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
            roughSaiasNaturalQuotientThetaWeight X m) *
              (FriableAsymptotic.primeLogSumUpTo m - (m : ℝ)) :=
  sum_jumpNaturalThetaWeight_diff_mul_primeLogError_eq_endpoints_sub_residual_sub_stable
    hyZ

example {X y Z : ℕ} (hyZ : y < Z) :
    roughSaiasNaturalThetaErrorTransfer X y Z =
      ∑ m ∈ Finset.Ioc y Z,
        roughSaiasNaturalQuotientThetaWeight X m *
          (FriableAsymptotic.primeLogIncrement m - 1) :=
  roughSaiasNaturalThetaErrorTransfer_eq_localPrimeErrorResidual hyZ

end Erdos390.WholePaper
