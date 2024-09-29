import Mathlib

/-
This is a proof of an "opposite FLT" result: there are no nontrivial solutions to
  2^a = 2^b + 2^c
in integers.

... which isn't hugely impressive. It's more interesting if you observe that it's
also true for a b c : ℚ. I remember having, at one stage, a Lean proof of
  LinearIndependent ℚ fun (i : Set.Ico (α := ℚ) 0 1) => (2 ^ (i : ℝ) : ℝ)
but it seems to be lost to the winds of time.
-/

example (a b c : ℤ) (h : (2 : ℚ) ^ a = 2 ^ b + 2 ^ c) : b = c := by
  have two_nz : (2 : ℚ) ≠ 0 := by norm_num
  have pow_two_mono : StrictMono (fun x : ℤ => (2 : ℚ) ^ x) := zpow_strictMono (by norm_num)
  wlog ha : a = 0 generalizing a b c h
  . replace h : (2 : ℚ) ^ (a - a) = 2 ^ (b - a) + 2 ^ (c - a)
    . simp_rw [zpow_sub₀ two_nz, ← add_div, ← h]
    simpa using this (a - a) (b - a) (c - a) h (sub_self a)
  subst ha
  wlog hbc : b ≤ c generalizing b c h
  . exact symm <| this c b (h.trans <| add_comm _ _) (le_of_not_le hbc)
  have hc₁ : 0 ≤ c + 1
  . rwa [← pow_two_mono.le_iff_le, h, zpow_add₀ two_nz, zpow_one, mul_two,
      add_le_add_iff_right, pow_two_mono.le_iff_le]
  have hc₂ : c < 0
  . rw [← pow_two_mono.lt_iff_lt, h, lt_add_iff_pos_left]; positivity
  obtain rfl : c = -1 := by linarith
  rw [← sub_eq_iff_eq_add] at h
  rw [← pow_two_mono.injective.eq_iff, ← h]
  norm_num



-- Here's an alternative proof using 2-adic valuation:

theorem padicValRat.zpow
  {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0) {k : ℤ} :
    padicValRat p (q ^ k) = k * padicValRat p q := by
  induction k using Int.negInduction with
  | nat k =>
    rw [zpow_natCast]
    apply padicValRat.pow hq
  | neg k ih =>
    simp_rw [zpow_neg, neg_mul, ← ih, zpow_natCast]
    apply padicValRat.inv

theorem padicValRat.self_zpow
  {p : ℕ} [hp : Fact p.Prime] (k : ℤ) :
    padicValRat p (p ^ k) = k := by
  rw [padicValRat.zpow (by exact_mod_cast hp.1.ne_zero),
    padicValRat.self hp.1.one_lt, mul_one]

example (a b c : ℤ) : (2 : ℚ) ^ a + 2 ^ b = 2 ^ c → a = b := by
  intro h₁
  by_contra h
  have : padicValRat 2 (2 ^ a + 2 ^ b) = min a b
  . rw [padicValRat.add_eq_min]
    . congr <;> apply padicValRat.self_zpow
    . positivity
    . positivity
    . positivity
    . convert h <;> apply padicValRat.self_zpow
  erw [h₁, padicValRat.self_zpow] at this
  replace h₁ : (2 : ℚ) ^ a < 2 ^ c
  . simp [← h₁, zpow_pos_of_pos]
  rw [zpow_lt_iff_lt (by trivial)] at h₁
  aesop
