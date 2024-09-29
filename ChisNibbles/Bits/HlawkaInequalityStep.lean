import Mathlib

/-
A proof of, uh, some complex number equality. Apparently an intermediate
step in a certain proof of Hlawka's inequality.

The proof runs tolerably fast so that's cool; I seem to remember it
being much slower when I first wrote it.
-/

theorem the (a b c : ℂ) :
    (‖a‖ + ‖b‖ + ‖c‖ - ‖b + c‖ - ‖c + a‖ - ‖a + b‖ + ‖a + b + c‖) *
      (‖a‖ + ‖b‖ + ‖c‖ + ‖a + b + c‖)
      =
    (‖b‖ + ‖c‖ - ‖b + c‖) * (‖a‖ - ‖b + c‖ + ‖a + b + c‖) +
    (‖c‖ + ‖a‖ - ‖c + a‖) * (‖b‖ - ‖c + a‖ + ‖a + b + c‖) +
    (‖a‖ + ‖b‖ - ‖a + b‖) * (‖c‖ - ‖a + b‖ + ‖a + b + c‖) := by
  suffices : ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖a + b + c‖^2 = ‖a + b‖ ^ 2 + ‖b + c‖ ^ 2 + ‖c + a‖ ^ 2
  . rw [← sub_eq_zero] at this ⊢
    rw [← this]
    ring
  simp_rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  simp
  ring
