import Mathlib

/-!
# The explicit finite allocation certificate

This file is deliberately only data.  It is the 211-entry rational array from
`reference/numerical_verifier.py`, transcribed literally so that the Lean
kernel, rather than the Python program, can check every calculation used by
the finite allocation lemma.
-/

namespace Erdos390.WholePaper

/-- One nonzero coordinate of the finite allocation certificate. -/
structure AllocationEntry where
  row : ℕ
  cofactor : ℕ
  numerator : ℕ
  denominator : ℕ
deriving DecidableEq, Repr

namespace AllocationEntry

/-- Constructor used to keep the literal array compact and readable. -/
def entry (row cofactor numerator denominator : ℕ) : AllocationEntry :=
  ⟨row, cofactor, numerator, denominator⟩

/-- The rational value represented by a certificate entry. -/
def value (e : AllocationEntry) : ℚ :=
  (e.numerator : ℚ) / (max 1 e.denominator : ℕ)

/-- The coordinate occupied by an entry. -/
def coordinate (e : AllocationEntry) : ℕ × ℕ :=
  (e.row, e.cofactor)

end AllocationEntry

open AllocationEntry

/-- The explicit nonzero entries in a single row. -/
def finiteAllocationRowEntries : ℕ → List AllocationEntry
  | 1 => [entry 1 2 4029639598 25970038185, entry 1 3 597400199 51940076370]
  | 2 => [entry 2 3 3432239399 51940076370, entry 2 5 30432359 51940076370]
  | 3 => [entry 3 5 177892183 11130016365, entry 3 7 6149035241 311640458220]
  | 4 => [entry 4 5 1 45]
  | 5 => [entry 5 7 5536939 903305676, entry 5 11 29881539 3312120812]
  | 6 => [entry 6 11 37106416381 5713408400700, entry 6 13 25678291319 5713408400700]
  | 7 => [entry 7 13 1 120]
  | 8 => [entry 8 17 1 153]
  | 9 => [entry 9 13 3520187831 34280450404200, entry 9 17 1970727917 623280916440, entry 9 19 34256599957 17140225202100]
  | 10 => [entry 10 19 1 231]
  | 11 => [entry 11 19 117890228609 51420675606300, entry 11 23 34208283533 25710337803150]
  | 12 => [entry 12 23 1 325]
  | 13 => [entry 13 23 1 378]
  | 14 => [entry 14 29 1 435]
  | 15 => [entry 15 29 1 496]
  | 16 => [entry 16 29 213831204731 174324746984752, entry 16 31 3197967125333 5752716650496816]
  | 17 => [entry 17 31 1 630]
  | 18 => [entry 18 31 142776482538959 143817916262420400, entry 18 37 2286634159870117 5321262901709554800]
  | 19 => [entry 19 31 1 780]
  | 20 => [entry 20 41 1 861]
  | 21 => [entry 21 43 1 946]
  | 22 => [entry 22 41 1 1035]
  | 23 => [entry 23 43 1 1128]
  | 24 => [entry 24 37 10658441105846658564953 17935134484658062065193800, entry 24 43 796497000815658011939 3587026896931612413038760]
  | 25 => [entry 25 31 1 1326]
  | 26 => [entry 26 43 1 1431]
  | 27 => [entry 27 47 1 1540]
  | 28 => [entry 28 53 1 1653]
  | 29 => [entry 29 47 1 1770]
  | 30 => [entry 30 43 1 1891]
  | 31 => [entry 31 61 1 2016]
  | 32 => [entry 32 41 1 2145]
  | 33 => [entry 33 41 1 2278]
  | 34 => [entry 34 61 1 2415]
  | 35 => [entry 35 47 1 2556]
  | 36 => [entry 36 47 1 2701]
  | 37 => [entry 37 41 1 2850]
  | 38 => [entry 38 73 1 3003]
  | 39 => [entry 39 79 1 3160]
  | 40 => [entry 40 43 1 3321]
  | 41 => [entry 41 47 1 3486]
  | 42 => [entry 42 61 1 3655]
  | 43 => [entry 43 47 1 3828]
  | 44 => [entry 44 71 1 4005]
  | 45 => [entry 45 83 1 4186]
  | 46 => [entry 46 73 1 4371]
  | 47 => [entry 47 67 1 4560]
  | 48 => [entry 48 61 1 4753]
  | 49 => [entry 49 53 1 4950]
  | 50 => [entry 50 53 1 5151]
  | 51 => [entry 51 67 1 5356]
  | 52 => [entry 52 59 1 5565]
  | 53 => [entry 53 103 1 5778]
  | 54 => [entry 54 107 1 5995]
  | 55 => [entry 55 103 1 6216]
  | 56 => [entry 56 109 1 6441]
  | 57 => [entry 57 113 1 6670]
  | 58 => [entry 58 79 1 6903]
  | 59 => [entry 59 103 1 7140]
  | 60 => [entry 60 103 1 7381]
  | 61 => [entry 61 107 1 7626]
  | 62 => [entry 62 83 1 7875]
  | 63 => [entry 63 67 1 8128]
  | 64 => [entry 64 83 1 8385]
  | 65 => [entry 65 67 1 8646]
  | 66 => [entry 66 113 1 8911]
  | 67 => [entry 67 83 1 9180]
  | 68 => [entry 68 79 1 9453]
  | 69 => [entry 69 71 1 9730]
  | 70 => [entry 70 73 1 10011]
  | 71 => [entry 71 103 1 10296]
  | 72 => [entry 72 89 1 10585]
  | 73 => [entry 73 103 1 10878]
  | 74 => [entry 74 101 1 11175]
  | 75 => [entry 75 79 1 11476]
  | 76 => [entry 76 101 1 11781]
  | 77 => [entry 77 107 1 12090]
  | 78 => [entry 78 97 1 12403]
  | 79 => [entry 79 83 1 12720]
  | 80 => [entry 80 101 1 13041]
  | 81 => [entry 81 101 1 13366]
  | 82 => [entry 82 103 1 13695]
  | 83 => [entry 83 89 1 14028]
  | 84 => [entry 84 103 1 14365]
  | 85 => [entry 85 101 1 14706]
  | 86 => [entry 86 89 1 15051]
  | 87 => [entry 87 89 1 15400]
  | 88 => [entry 88 101 1 15753]
  | 89 => [entry 89 97 1 16110]
  | 90 => [entry 90 97 1 16471]
  | 91 => [entry 91 97 1 16836]
  | 92 => [entry 92 97 1 17205]
  | 93 => [entry 93 97 1 17578]
  | 94 => [entry 94 97 1 17955]
  | 95 => [entry 95 97 1 18336]
  | 96 => [entry 96 97 1 18721]
  | 97 => [entry 97 191 1 19110]
  | 98 => [entry 98 197 1 19503]
  | 99 => [entry 99 163 1 19900]
  | 100 => [entry 100 191 1 20301]
  | 101 => [entry 101 109 1 20706]
  | 102 => [entry 102 131 1 21115]
  | 103 => [entry 103 199 1 21528]
  | 104 => [entry 104 179 1 21945]
  | 105 => [entry 105 173 1 22366]
  | 106 => [entry 106 199 1 22791]
  | 107 => [entry 107 127 1 23220]
  | 108 => [entry 108 199 1 23653]
  | 109 => [entry 109 151 1 24090]
  | 110 => [entry 110 211 1 24531]
  | 111 => [entry 111 193 1 24976]
  | 112 => [entry 112 193 1 25425]
  | 113 => [entry 113 197 1 25878]
  | 114 => [entry 114 181 1 26335]
  | 115 => [entry 115 167 1 26796]
  | 116 => [entry 116 197 1 27261]
  | 117 => [entry 117 173 1 27730]
  | 118 => [entry 118 193 1 28203]
  | 119 => [entry 119 179 1 28680]
  | 120 => [entry 120 173 1 29161]
  | 121 => [entry 121 163 1 29646]
  | 122 => [entry 122 137 1 30135]
  | 123 => [entry 123 137 1 30628]
  | 124 => [entry 124 167 1 31125]
  | 125 => [entry 125 197 1 31626]
  | 126 => [entry 126 197 1 32131]
  | 127 => [entry 127 157 1 32640]
  | 128 => [entry 128 157 1 33153]
  | 129 => [entry 129 149 1 33670]
  | 130 => [entry 130 131 1 34191]
  | 131 => [entry 131 163 1 34716]
  | 132 => [entry 132 199 1 35245]
  | 133 => [entry 133 211 1 35778]
  | 134 => [entry 134 151 1 36315]
  | 135 => [entry 135 151 1 36856]
  | 136 => [entry 136 149 1 37401]
  | 137 => [entry 137 193 1 37950]
  | 138 => [entry 138 199 1 38503]
  | 139 => [entry 139 197 1 39060]
  | 140 => [entry 140 197 1 39621]
  | 141 => [entry 141 173 1 40186]
  | 142 => [entry 142 149 1 40755]
  | 143 => [entry 143 173 1 41328]
  | 144 => [entry 144 199 1 41905]
  | 145 => [entry 145 167 1 42486]
  | 146 => [entry 146 163 1 43071]
  | 147 => [entry 147 163 1 43660]
  | 148 => [entry 148 173 1 44253]
  | 149 => [entry 149 173 1 44850]
  | 150 => [entry 150 157 1 45451]
  | 151 => [entry 151 163 1 46056]
  | 152 => [entry 152 191 1 46665]
  | 153 => [entry 153 199 1 47278]
  | 154 => [entry 154 193 1 47895]
  | 155 => [entry 155 163 1 48516]
  | 156 => [entry 156 173 1 49141]
  | 157 => [entry 157 197 1 49770]
  | 158 => [entry 158 179 1 50403]
  | 159 => [entry 159 167 1 51040]
  | 160 => [entry 160 181 1 51681]
  | 161 => [entry 161 163 1 52326]
  | 162 => [entry 162 199 1 52975]
  | 163 => [entry 163 193 1 53628]
  | 164 => [entry 164 197 1 54285]
  | 165 => [entry 165 167 1 54946]
  | 166 => [entry 166 181 1 55611]
  | 167 => [entry 167 191 1 56280]
  | 168 => [entry 168 199 1 56953]
  | 169 => [entry 169 173 1 57630]
  | 170 => [entry 170 193 1 58311]
  | 171 => [entry 171 181 1 58996]
  | 172 => [entry 172 193 1 59685]
  | 173 => [entry 173 191 1 60378]
  | 174 => [entry 174 197 1 61075]
  | 175 => [entry 175 179 1 61776]
  | 176 => [entry 176 191 1 62481]
  | 177 => [entry 177 197 1 63190]
  | 178 => [entry 178 191 1 63903]
  | 179 => [entry 179 199 1 64620]
  | 180 => [entry 180 191 1 65341]
  | 181 => [entry 181 197 1 66066]
  | 182 => [entry 182 199 1 66795]
  | 183 => [entry 183 197 1 67528]
  | 184 => [entry 184 197 1 68265]
  | 185 => [entry 185 199 1 69006]
  | 186 => [entry 186 193 1 69751]
  | 187 => [entry 187 193 1 70500]
  | 188 => [entry 188 191 1 71253]
  | 189 => [entry 189 199 1 72010]
  | 190 => [entry 190 197 1 72771]
  | 191 => [entry 191 197 1 73536]
  | 192 => [entry 192 197 1 74305]
  | 193 => [entry 193 199 1 75078]
  | 194 => [entry 194 197 1 75855]
  | 195 => [entry 195 197 1 76636]
  | 196 => [entry 196 199 1 77421]
  | 197 => [entry 197 199 1 78210]
  | 198 => [entry 198 199 1 79003]
  | 199 => [entry 199 347 1 79800]
  | 200 => [entry 200 241 1 80601]
  | _ => []

/-- The twenty-row view of the authoritative row slices. -/
def finiteAllocationRowBlockEntries (b : ℕ) : List AllocationEntry :=
  (List.range' (20 * b + 1) 20).flatMap finiteAllocationRowEntries

/-- The authoritative flat array: the explicit row slices concatenated in
row order. -/
def finiteAllocationEntries : List AllocationEntry :=
  finiteAllocationRowBlockEntries 0 ++ finiteAllocationRowBlockEntries 1 ++
  finiteAllocationRowBlockEntries 2 ++ finiteAllocationRowBlockEntries 3 ++
  finiteAllocationRowBlockEntries 4 ++ finiteAllocationRowBlockEntries 5 ++
  finiteAllocationRowBlockEntries 6 ++ finiteAllocationRowBlockEntries 7 ++
  finiteAllocationRowBlockEntries 8 ++ finiteAllocationRowBlockEntries 9

/-- The cofactor keys occurring in each twenty-row block.  Entry payloads
are not duplicated: prime buckets below filter the authoritative row data. -/
def finiteAllocationPrimeBlockKeys : ℕ → List ℕ
  | 0 => [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
  | 1 => [31, 37, 41, 43, 47, 53, 61, 73, 79]
  | 2 => [47, 53, 59, 61, 67, 71, 73, 79, 83, 103, 107, 109, 113]
  | 3 => [67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 113]
  | 4 => [89, 97, 101, 103, 163, 191, 197]
  | 5 => [109, 127, 131, 151, 167, 173, 179, 181, 193, 197, 199, 211]
  | 6 => [131, 137, 149, 151, 157, 163, 167, 193, 197, 199, 211]
  | 7 => [149, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199]
  | 8 => [163, 167, 173, 179, 181, 191, 193, 197, 199]
  | 9 => [191, 193, 197, 199, 241, 347]
  | _ => []

/-- The entries in one row block having cofactor `p`. -/
def finiteAllocationEntriesForCofactor
    (p : ℕ) (entries : List AllocationEntry) : List AllocationEntry :=
  entries.filter fun e => e.cofactor = p

/-- Within each twenty-row block, a derived regrouping by prime cofactor. -/
def finiteAllocationPrimeBlockBuckets
    (b : ℕ) : List (ℕ × List AllocationEntry) :=
  (finiteAllocationPrimeBlockKeys b).map fun p =>
    (p, finiteAllocationEntriesForCofactor p
      (finiteAllocationRowBlockEntries b))

/-- Select a prime bucket without traversing the entry payloads of rejected
buckets. -/
def selectPrimeEntries (p : ℕ) :
    List (ℕ × List AllocationEntry) → List AllocationEntry
  | [] => []
  | (q, entries) :: buckets =>
      if q = p then entries ++ selectPrimeEntries p buckets
      else selectPrimeEntries p buckets

/-- The twenty explicitly indexed row slices in block `b`. -/
def finiteAllocationRowBlockBuckets (b : ℕ) :
    List (ℕ × List AllocationEntry) :=
  (List.range' (20 * b + 1) 20).map fun r =>
    (r, finiteAllocationRowEntries r)

/-- Selecting row `r` from all ten row blocks. -/
def finiteAllocationSelectedRowEntries (r : ℕ) : List AllocationEntry :=
  selectPrimeEntries r
    ((List.range' 1 200).map fun s => (s, finiteAllocationRowEntries s))

/-- The preaggregated entries contributing to the load at `p`. -/
def finiteAllocationPrimeEntries (p : ℕ) : List AllocationEntry :=
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 0) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 1) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 2) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 3) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 4) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 5) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 6) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 7) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 8) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 9)

end Erdos390.WholePaper
