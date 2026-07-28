import Erdos390.WholePaper.TangentBalancedProductFlow

/-! # Expanded statement audit for the balanced product transport -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Complete public declaration census -/

#check tangentPositiveMass
#check tangentNegativeMass
#check tangentBalancedProductFlow
#check tangentPositiveMass_nonneg
#check tangentNegativeMass_nonneg
#check tangentPositiveMass_eq_negativeMass
#check tangentPositiveMass_add_negativeMass
#check tangentBalancedProductFlow_nonneg
#check tangentBalancedProductFlow_eq_zero_of_positiveMass_eq_zero
#check tangentBalancedProductFlow_self
#check tangentBalanced_eq_zero_of_positiveMass_eq_zero
#check sum_tangentBalancedProductFlow_out
#check sum_tangentBalancedProductFlow_in
#check tangentBalancedProductFlow_divergence_eq
#check tangentBalancedProductFlow_traffic_eq_positiveMass
#check tangentBalancedProductFlow_traffic_eq_half_sum_abs
#check tangentBalancedProductFlow_incident_eq_abs
#check tangentBalancedProductFlow_positive_endpoints_ne

example {V : Type*} [Fintype V] (q : V -> Real)
    (source target : V) :
    tangentBalancedProductFlow q source target =
      max (q source) 0 * max (-q target) 0 /
        (∑ v : V, max (q v) 0) := by
  rfl

example {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) (v : V) :
    tangentFlowDivergence (tangentBalancedProductFlow q) v = q v :=
  tangentBalancedProductFlow_divergence_eq q hsum v

example {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) :
    tangentFlowTraffic (tangentBalancedProductFlow q) =
      (∑ v : V, |q v|) / 2 :=
  tangentBalancedProductFlow_traffic_eq_half_sum_abs q hsum

example {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) (v : V) :
    (∑ w : V, tangentBalancedProductFlow q v w) +
        (∑ w : V, tangentBalancedProductFlow q w v) = |q v| :=
  tangentBalancedProductFlow_incident_eq_abs q hsum v

end

end Erdos390.WholePaper
