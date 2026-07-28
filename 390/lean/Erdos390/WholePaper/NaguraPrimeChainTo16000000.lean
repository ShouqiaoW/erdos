import Erdos390.WholePaper.NaguraPrimeChainTo1482617
import Erdos390.WholePaper.NaguraPrimeChain1482617To3538187
import Erdos390.WholePaper.NaguraPrimeChain3538187To8443433
import Erdos390.WholePaper.NaguraPrimeChain8443433To16000000

/-! # Aggregated finite Nagura prime chain to `16000000` -/

namespace Erdos390.WholePaper

theorem exists_prime_nagura_1482617_to_16000000 {n : ℕ}
    (hnLower : 1482617 ≤ n) (hnUpper : n < 16000000) :
    HasNaguraPrime n := by
  by_cases h1 : n < 3538187
  · exact exists_prime_nagura_1482617_to_3538187 hnLower h1
  by_cases h2 : n < 8443433
  · exact exists_prime_nagura_3538187_to_8443433 (by omega) h2
  · exact exists_prime_nagura_8443433_to_16000000 (by omega) hnUpper

theorem exists_prime_nagura_91639_to_16000000 {n : ℕ}
    (hnLower : 91639 ≤ n) (hnUpper : n < 16000000) :
    HasNaguraPrime n := by
  by_cases h : n < 1482617
  · exact exists_prime_nagura_to_1482617 hnLower h
  · exact exists_prime_nagura_1482617_to_16000000 (by omega) hnUpper

end Erdos390.WholePaper
