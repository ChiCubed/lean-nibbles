import Mathlib

open PNat

example
  (f : ℕ+ → ℕ+)
  (h : ∀ i j, i ≠ j → gcd (f i) (f j) = gcd i j) :
    f = id :=
  have h₁ (i : ℕ+) : gcd i (f i) = i := gcd_eq_left $ by
    convert h i (2 * i) (by simp) ▸ gcd_dvd_left ..
    simp [gcd_eq_left]
  funext fun i => by_contra fun c => c $ by
    simpa [h₁] using h _ _ (Ne.symm c)
