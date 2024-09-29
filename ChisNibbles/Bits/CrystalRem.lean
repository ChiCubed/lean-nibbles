import Mathlib

/-
For n : ℕ, floor(sqrt n)^2 + 2 does not divide n^2 + 1.

i have no idea why this is called `crystalrem`
-/

theorem crystalrem (n : ℕ) : ¬ n.sqrt ^ 2 + 2 ∣ n ^ 2 + 1 := by
  obtain rfl | n_pos := n.eq_zero_or_pos
  . decide
  have s_pos := Nat.sqrt_pos.mpr n_pos
  intro h
  zify at h
  let k : ℤ := n - n.sqrt ^ 2
  replace h : (n.sqrt ^ 2 + 2 : ℤ) ∣ (k - 2) ^ 2 + 1
  . convert h.sub <| dvd_mul_left _ (n + k - 2) using 1; ring
  obtain hk | hk := lt_or_le k 2
  . have k_nn : 0 ≤ k := sub_nonneg.mpr <| by exact_mod_cast n.sqrt_le'
    interval_cases k <;> norm_num at h <;> norm_cast at h <;>
      rw [Nat.dvd_prime (by norm_num)] at h
    . replace h : n.sqrt ^ 2 = 3 := by simpa using h
      absurd isSquare_of_exists_sq _ ⟨_, h.symm⟩
      -- wtf, apparently in current Lean "decide" can't prove ¬ IsSquare 3.
      -- I think it gets stuck on computing Nat.sqrt 3? anyway, :(
      simp_rw [IsSquare, eq_comm, Nat.exists_mul_self]
      convert_to ¬ 1 * 1 = 3
      decide
    . absurd s_pos.ne'
      simpa using h
  rcases h with ⟨m, h⟩
  obtain ⟨hm₁, hm₂⟩ : 0 < m ∧ m < 4
  . have k_ub : k ≤ 2 * n.sqrt
    . dsimp only [k]; linarith only [n.sqrt_le_add]
    constructor <;> nlinarith
  interval_cases m <;> clear m hm₁ hm₂
  . replace h : (k - 2 - n.sqrt) * (k - 2 + n.sqrt) = 1
    . rw [← sub_eq_zero] at h ⊢; rw [← h]; ring
    linarith only [Int.eq_of_mul_eq_one h, s_pos]
  . replace h : (k - 2) ^ 2 - 2 * n.sqrt ^ 2 = 3
    . rw [← sub_eq_zero] at h ⊢; rw [← h]; ring
    apply congrArg (Int.cast (R := ZMod 8)) at h
    have : ∀ a b : ZMod 8, a ^ 2 - 2 * b ^ 2 ≠ 3 := by decide
    absurd this (k - 2 : ℤ) (n.sqrt : ℤ)
    exact_mod_cast h
  . replace h : (k - 2) ^ 2 - 3 * n.sqrt ^ 2 = 5
    . rw [← sub_eq_zero] at h ⊢; rw [← h]; ring
    apply congrArg (Int.cast (R := ZMod 3)) at h
    have : ∀ a b : ZMod 3, a ^ 2 - 3 * b ^ 2 ≠ 5 := by decide
    absurd this (k - 2 : ℤ) (n.sqrt : ℤ)
    exact_mod_cast h
