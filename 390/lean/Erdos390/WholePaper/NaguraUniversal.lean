import Erdos390.WholePaper.NaguraAnalyticTail
import Erdos390.WholePaper.NaguraPrimeChainTo16000000

/-! # Nagura's theorem for every natural endpoint -/

namespace Erdos390.WholePaper

/-- For every `n ≥ 25`, there is a prime strictly between `n` and `6n/5`.
This is the public universal Nagura API used by the allocation argument. -/
theorem exists_prime_nagura {n : ℕ} (hn : 25 ≤ n) :
    HasNaguraPrime n := by
  by_cases hSmall : n < 91639
  · exact exists_prime_nagura_below_91639 hn hSmall
  by_cases hFinite : n < 16000000
  · exact exists_prime_nagura_91639_to_16000000 (by omega) hFinite
  · exact exists_prime_nagura_analytic_tail (by omega)

end Erdos390.WholePaper
