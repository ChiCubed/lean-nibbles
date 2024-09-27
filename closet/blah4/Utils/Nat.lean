import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain

section

open UniqueFactorizationMonoid

theorem induction_on_prime_powers {P : ℕ → Prop} (h₀ : P 0) (h₁ : P 1)
  (hps : {p : ℕ} → (k : ℕ) → p.Prime → P (p ^ k) → P (p ^ (k + 1)))
  (hcp : {m n : ℕ} → m.coprime n → P m → P n → P (m * n)) (n : ℕ) : P n := by
  apply induction_on_coprime <;> simp_rw [Nat.isUnit_iff, ← Nat.prime_iff]
  . exact h₀
  . rintro x rfl
    exact h₁
  . intro p i hp
    induction i with
    | zero => simpa
    | succ i ih => apply hps; assumption'
  . intro x y hxy hx hy
    apply hcp; assumption'
    apply hxy
    . apply Nat.gcd_dvd_left
    . apply Nat.gcd_dvd_right

end