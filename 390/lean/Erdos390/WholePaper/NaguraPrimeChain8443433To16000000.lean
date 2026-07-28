import Erdos390.WholePaper.Nagura

namespace Erdos390.WholePaper

theorem exists_prime_nagura_8443433_to_16000000 {n : ℕ}
    (hnLower : 8443433 ≤ n) (hnUpper : n < 16000000) : HasNaguraPrime n := by
  by_cases h10047703 : n < 10047703
  · exact ⟨10047703, by norm_num, h10047703, by omega⟩
  by_cases h11956801 : n < 11956801
  · exact ⟨11956801, by norm_num, h11956801, by omega⟩
  by_cases h14228623 : n < 14228623
  · exact ⟨14228623, by norm_num, h14228623, by omega⟩
  exact ⟨16932073, by norm_num, by omega, by omega⟩

end Erdos390.WholePaper
