import Mathlib

/-
If n is a natural greater than 4 then n ^ n < (n - 1) ^ (n + 1).
To show this it's basically strong enough to prove that e < 3.

Now that I look at this again it occurs to me that there's
a much easier proof by induction, so I wrote that for fun.
-/

example (n : ℕ) (hn : 5 ≤ n) :
    n ^ n < (n - 1) ^ (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [add_tsub_cancel_right,
      ← Nat.mul_lt_mul_left (a := n ^ n) (by positivity), ← pow_add,
      show n + (n + 1 + 1) = 2 * (n + 1) by ring, pow_mul]
    apply mul_lt_mul_of_pos_right ih (by positivity) |>.trans_le
    rw [← mul_pow, mul_comm, ← Nat.sq_sub_sq]
    gcongr
    apply tsub_le_self

/-
here's the old proof.
-/

lemma geo_two_lt {n : ℕ} : ∑ k in Finset.range n, (1 / 2 ^ k : ℚ) < 2 := by
  simp_rw [← one_div_pow]
  rw [geom_sum_eq, div_lt_iff_of_neg, lt_sub_iff_add_lt]
  all_goals { norm_num }

theorem free_e (n : ℕ) : (1 + 1 / n : ℚ) ^ n <3 := by
  obtain rfl | (n_pos : 0 < n) := n.eq_zero_or_pos
  . norm_num
  qify at n_pos
  rw [add_comm, add_pow, Finset.sum_range_succ']
  suffices : ∑ k in Finset.range n, (n.choose (k + 1) / n ^ (k + 1) : ℚ) + 1 < 3
  . norm_num; field_simp; exact this
  apply add_lt_of_lt_sub_right; norm_num1
  suffices _ ≤ ∑ k in Finset.range n, (1 / 2 ^ k : ℚ) from this.trans_lt geo_two_lt
  apply Finset.sum_le_sum
  rintro k -
  rw [div_le_iff₀' (by positivity), mul_one_div]
  apply (Nat.choose_le_pow_div _ _).trans
  gcongr
  norm_cast
  rw [add_comm]
  convert Nat.factorial_mul_pow_le_factorial using 1
  norm_num

example (n : ℕ) (hn : 4 ≤ n) :
    (n + 1) ^ (n + 1) < n ^ (n + 2) := by
  qify
  suffices : (1 + 1 / n : ℚ) ^ n < n ^ 2 / (n + 1)
  . rw [← div_lt_div_right (c := (n ^ n * (n + 1) : ℚ)) (by positivity)]
    convert this using 1 <;> field_simp <;> ring
  have hn' : (n - 1 : ℚ) < n ^ 2 / (n + 1)
  . rw [lt_div_iff (by positivity)]; nlinarith
  apply (free_e n).trans_le ?_ |>.trans hn'
  qify at hn; linarith
