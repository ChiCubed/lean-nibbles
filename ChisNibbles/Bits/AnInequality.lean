import Mathlib

/-
If x is a tuple of nonnegative reals then prod (1 + xi) + prod (1 - xi)
is at least 2.

(where is this problem from?)
-/

open Finset

example
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (x : ι → ℝ)
  (hx : ∀ i, 0 ≤ x i) :
    2 ≤ ∏ i, (1 + x i) + ∏ i, (1 - x i) := by
  simp_rw [sub_eq_add_neg, prod_add, ← sum_add_distrib,
    neg_eq_neg_one_mul ∘' x, prod_mul_distrib, prod_const, one_pow, one_mul]
  rw [sum_powerset, sum_range_succ]
  convert le_add_of_nonneg_left (α := ℝ) _
  . rw [powersetCard_self]
    norm_num
  refine sum_nonneg fun _ _ => sum_nonneg fun t _ => ?_
  cases neg_one_pow_eq_or ℝ (univ \ t).card with | _ h => simp [h, prod_nonneg, hx]


-- And an inductive proof, which is probably more like what humans use.

set_option autoImplicit true

theorem Finset.prod_abs
  [LinearOrderedCommRing β] {ι : Type*} (s : Finset ι) (f : ι → β) :
    |∏ i in s, f i| = ∏ i in s, |f i| := by
  induction s using Finset.cons_induction <;> simp [abs_mul, *]

theorem aux
  {ι : Type*} (s : Finset ι)
  (x : ι → ℝ)
  (hx : ∀ i ∈ s, 0 ≤ x i) :
    2 ≤ ∏ i in s, (1 + x i) + ∏ i in s, (1 - x i) := by
  induction s using Finset.cons_induction with
  | empty => norm_num
  | @cons a s ha ih =>
    simp_rw [Finset.mem_cons, forall_eq_or_imp] at hx
    simp_rw [Finset.prod_cons]
    suffices ∏ i in s, (1 - x i) ≤ ∏ i in s, (1 + x i) by
      linarith [mul_le_mul_of_nonneg_left this hx.1, ih hx.2]
    apply le_of_abs_le
    simp_rw [Finset.prod_abs]
    apply Finset.prod_le_prod (by simp)
    intro i hi
    cases abs_cases (1 - x i) <;> linarith [hx.2 i hi]

example
  {ι : Type*} [Fintype ι]
  (x : ι → ℝ)
  (hx : ∀ i, 0 ≤ x i) :
    2 ≤ ∏ i, (1 + x i) + ∏ i, (1 - x i) := by
  apply aux
  simp [hx]
