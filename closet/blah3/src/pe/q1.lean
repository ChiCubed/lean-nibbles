import data.finset.basic
import algebra.big_operators.basic

open finset
open_locale big_operators

#eval ∑ i in (range 1000).filter (λ i, 3 ∣ i ∨ 5 ∣ i), i