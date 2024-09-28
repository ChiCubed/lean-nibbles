import Mathlib

/-
Consider a Fibonacci-like linear recurrence built from an n-tuple `a`
by starting with `u (-1) = 0`, `u 0 = 1`, and iterating
`u (i + 1) = u i + a i * u (i - 1)`.
Then the value of `u n` stays the same if you reverse `a`.

(where does this problem come from again?)
-/

set_option autoImplicit true

open Matrix List

lemma Matrix.transpose_1x1
  [Unique α] (A : Matrix α α R) :
    Aᵀ = A := by
  ext i j; fin_cases i; fin_cases j; simp

lemma Matrix.conjugate_list_prod
  [CommRing R] [Fintype α] [DecidableEq α]
  (A : Matrix α α R) [Invertible A] (l : List (Matrix α α R)) :
    A⁻¹ * prod l * A = prod (l.map fun B => A⁻¹ * B * A) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [← ih, ← mul_assoc]

lemma rec_matrix_step {x y z c : ℤ} (h : z = y + c * x) :
    !![z, y] = !![y, x] * !![1, 1; c, 0] := by
  simp [h, mul_comm]

lemma rec_matrix {a u : ℕ → ℤ}
  (us : ∀ i, u (i + 1) = u i + a i * u (i - 1))
  (n : ℕ) :
    !![u n, u (n - 1)] = !![u 0, u 0] * prod (range n |>.map fun i => !![1, 1; a i, 0]) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ, ← Matrix.mul_assoc, ← ih,
      ← rec_matrix_step (us n), add_tsub_cancel_right]

lemma aux (n : ℕ) (a u v : ℕ → ℤ)
  (u0 : u 0 = 1) (v0 : v 0 = 1)
  (us : ∀ i, u (i + 1) = u i + a i * u (i - 1))
  (vs : ∀ i, v (i + 1) = v i + a (n - i) * v (i - 1)) :
    u (n + 1) = v (n + 1) := by
  suffices !![u (n + 1), u n] * !![(1 : ℤ); 0] = !![v (n + 1), v n] * !![(1 : ℤ); 0] by
    simpa using congrArg (· 0 0) this
  erw [rec_matrix us, rec_matrix vs, u0, v0]
  let B : Matrix _ _ ℤ := !![1, 1; 1, 0]
  let B' : Matrix _ _ ℤ := !![0, 1; 1, -1]
  let B_inv : Invertible B := B.invertibleOfLeftInverse B' (by decide)
  calc
    _ = _ᵀ                                                     :=
      transpose_1x1 _ |>.symm
    _ = !![(1 : ℤ), 0] * (prod _)ᵀ * !![(1 : ℤ); 1]            := by
      simp_rw [transpose_mul, ← Matrix.mul_assoc]
      congr <;> exact transposeᵣ_eq _ |>.symm
    _ = (!![(1 : ℤ), 1] * ⅟B) * _ * (B * !![(1 : ℤ); 0])       := by
      congr <;> decide
    _ = !![(1 : ℤ), 1] * (⅟B * (prod _)ᵀ * B) * !![(1 : ℤ); 0] := by
      simp [Matrix.mul_assoc]; rfl
    _ = _                                                      := ?_
  congr
  rw [transpose_list_prod, invOf_eq_nonsing_inv, conjugate_list_prod]
  simp only [← map_reverse, List.map_map, range_eq_range', reverse_range']
  congr
  funext i
  dsimp only [Function.comp]
  rw [← transposeᵣ_eq, ← invOf_eq_nonsing_inv B, zero_add, add_tsub_cancel_right]
  change B' * !![1, a (n - i); 1, 0] * B = !![1, 1; a (n - i), 0]
  simp only [B, B']
  norm_num
