import Erdos390.WholePaper.VariablePrimeCounting

open Filter Topology

namespace Erdos390.WholePaper.SafePrimeCounting

example {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦
        (Nat.primeCounting (m n) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds a) :=
  primeCounting_movingEndpoint_normalized_tendsto ha hm

end Erdos390.WholePaper.SafePrimeCounting
