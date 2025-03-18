import Mathlib.Tactic.Rify
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

open Finset

lemma your_name
  (x m : ℕ) (hx : x ≤ m) :
    x = card (filter (· ≤ x) (Icc 1 m)) := by
  rw [← Nat.Ico_succ_right]
  simp_rw [← Nat.lt_succ_iff]
  rw [Ico_filter_lt]
  simp; omega

lemma flippy
  (f : ℕ → ℕ) (s : Finset ℕ)
  (m : ℕ) (hf : ∀ i ∈ s, f i ≤ m) :
    ∑ i ∈ s, f i =
    ∑ j ∈ Icc 1 m, card (s.filter (j ≤ f ·)) := by
  rw [sum_congr rfl fun i hi => your_name _ m (hf i hi)]
  simp_rw [card_filter]
  rw [sum_comm]

-- this is so sloppy but w/e
theorem flippysum (n : ℕ) (hn : n ≥ 2) :
    ∑ k ∈ .Icc 2 n, ⌊Real.logb k n⌋ =
    ∑ k ∈ .Icc 2 n, ⌊(n : ℝ) ^ (1 / k : ℝ)⌋ := by
  conv_lhs =>
    arg 2
    ext k
    rw [Real.floor_logb_natCast n.cast_nonneg, Int.log_natCast]
  norm_cast
  rw [flippy _ _ n ?h_hi]
  case h_hi =>
    intro i hi
    apply Nat.log_le_self
  rw [sum_congr rfl fun j hj => congrArg card <| filter_congr fun x hx =>
    .symm <| Nat.pow_le_iff_le_log (by have := mem_Icc.mp hx; omega) (by omega)]

  have h₀ (j : ℕ) (hj : 1 ≤ j) :
      card (filter (· ^ j ≤ n) (Icc 1 n)) = ⌊(n : ℝ) ^ (1 / j : ℝ)⌋₊ := by
    rw [your_name ⌊(n : ℝ) ^ (1 / j : ℝ)⌋₊ n ?help]
    case help =>
      apply Nat.floor_le_of_le
      conv_rhs => rw [← Real.rpow_one n]
      apply Real.rpow_le_rpow_of_exponent_le
      . norm_cast; omega
      . rw [one_div]
        rw [inv_le_one₀] <;> norm_cast
    congr
    ext x
    rw [Nat.le_floor_iff (by positivity), one_div]
    symm
    rify
    rw [← Real.rpow_natCast]
    apply Real.le_rpow_inv_iff_of_pos <;> norm_cast <;> omega
  have h₁ (j : ℕ) (hj : 1 ≤ j) :
      card (filter (· ^ j ≤ n) (Icc 2 n)) = ⌊(n : ℝ) ^ (1 / j : ℝ)⌋₊ - 1 := by
    rw [← h₀ j hj]
    apply Nat.eq_sub_of_add_eq
    simp_rw [card_filter]
    have : 1 ≤ n := by omega
    nth_rw 2 [← sum_Ioc_add_left (by exact this)]
    congr 1
    simp [this]
  rw [sum_congr rfl fun j hj => h₁ j (by have := mem_Icc.mp hj; omega)]
  clear h₀ h₁

  have h (x : ℕ) : 1 ≤ ⌊(n : ℝ) ^ (1 / x : ℝ)⌋₊ := by
    rw [Nat.one_le_floor_iff]
    apply Real.one_le_rpow
    . norm_cast; linarith
    . positivity
  zify [h]
  simp only [sum_sub_distrib, sum_const, Nat.card_Icc,
    add_tsub_cancel_right, nsmul_eq_mul, mul_one]
  rw [← sum_Ioc_add_left (by omega), ← Nat.Icc_succ_left]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, one_div, Nat.cast_one, ne_eq, one_ne_zero,
    not_false_eq_true, div_self, Real.rpow_one, Nat.floor_natCast, add_sub_cancel_right]
  congr; ext x
  rw [Int.natCast_floor_eq_floor]
  positivity
