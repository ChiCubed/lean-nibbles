import Mathlib

/-
a is a sequence of naturals satisfying a 0 = 0 and |a (i+1)| = |a i + 1|.
Show that the cumulative averages of a are all at least -1/2.

this problem is definitely from *somewhere*...
-/

open Finset

theorem thingy
  (a : ℕ → ℤ)
  (h₀ : a 0 = 0)
  (h₁ : ∀ i, a (i + 1) = a i + 1 ∨ a (i + 1) = -a i - 1)
  (n : ℕ) (hn : 0 < n) :
    (-1 / 2 : ℚ) ≤ 1 / n * ∑ i in range n, a i := by
  rcases Nat.exists_eq_add_of_lt hn with ⟨n, rfl⟩
  clear hn; rw [zero_add]
  suffices (a n + 1) ^ 2 - (n + 1) ≤ 2 * ∑ i in range (n + 1), a i by
    replace : -(n + 1 : ℤ) ≤ _ * 2 := le_trans (by nlinarith) <|
      this.trans_eq <| mul_comm _ _
    qify at this
    field_simp
    simpa (discharger := positivity) [div_le_div_iff]
  induction n with
  | zero =>
    simp [h₀]
  | succ n ih =>
    rw [range_add_one, sum_insert not_mem_range_self]
    cases h₁ n with | _ h => rw [h]; push_cast; linarith
