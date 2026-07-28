import Erdos390.WholePaper.NaguraPrimeChain91639To218737
import Erdos390.WholePaper.NaguraPrimeChain218737To522059
import Erdos390.WholePaper.NaguraPrimeChain522059To1046959
import Erdos390.WholePaper.NaguraPrimeChain1046959To1482617

/-! # Aggregated finite Nagura prime chain to `1482617` -/

namespace Erdos390.WholePaper

theorem exists_prime_nagura_to_1482617 {n : ℕ}
    (hnLower : 91639 ≤ n) (hnUpper : n < 1482617) : HasNaguraPrime n := by
  by_cases h1 : n < 218737
  · exact exists_prime_nagura_91639_to_218737 hnLower h1
  by_cases h2 : n < 522059
  · exact exists_prime_nagura_218737_to_522059 (by omega) h2
  by_cases h3 : n < 1046959
  · exact exists_prime_nagura_522059_to_1046959 (by omega) h3
  · exact exists_prime_nagura_1046959_to_1482617 (by omega) hnUpper

end Erdos390.WholePaper
