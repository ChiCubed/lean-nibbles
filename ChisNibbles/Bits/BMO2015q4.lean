import Mathlib

/-
A formalisation of (a weakening for some reason of) Balkan MO 2015 Q4.

The proof I formalised is pretty inefficient (proof-ily but also time-ily),
it was basically whatever popped into my head. The original problem used
20 instead of 25, and I think I eventually decided the optimal bound was
15? (don't quote me on that though (unless you convince me to Lean it up))

fun fact: this file was originally named `garbage.lean`,
make of that what you will
-/

open Real

lemma algae {a : ℝ} (ha : 0 ≤ a) {c : ℝ} (h : a * Int.fract a ≤ c) :
    ∃ k : ℕ, k ^ 2 ≤ a ^ 2 ∧ a ^ 2 ≤ k ^ 2 + 2 * c := by
  exists ⌊a⌋₊
  constructor
  . gcongr
    apply Nat.floor_le ha
  . rw [Int.fract] at h
    rw [natCast_floor_eq_intCast_floor ha]
    nlinarith [Int.floor_le a]

lemma idea (x : ℕ)
  (hs : ¬ IsSquare x)
  (hp : ∀ n : ℕ, 0 < n → ∀ c ∈ Set.Icc 1 5, ∀ k : ℕ, n ^ 2 * x ≠ k ^ 2 + c)
  (n : ℕ) (hn : 0 < n) :
    (5 / 2 : ℝ) < n * sqrt x * Int.fract (n * sqrt x) := by
  contrapose! hp with h
  apply algae (by positivity) at h
  rcases h with ⟨k, hk⟩
  replace hk : k ^ 2 ≤ n ^ 2 * x ∧ n ^ 2 * x ≤ k ^ 2 + 5
  . simp only [mul_pow, Nat.cast_nonneg, sq_sqrt] at hk
    norm_num1 at hk
    exact_mod_cast hk
  obtain ⟨c, c_hi, hc⟩ : ∃ c, c ≤ 5 ∧ n ^ 2 * x = k ^ 2 + c
  . use n ^ 2 * x - k ^ 2
    rw [tsub_le_iff_right, add_comm 5]
    simp [hk]
  clear hk
  obtain c_lo | rfl : 1 ≤ c ∨ c = 0 := eq_zero_or_pos c |>.symm
  . use n, hn, c, Set.mem_Icc.mpr ⟨c_lo, c_hi⟩, k
  exfalso
  replace hc : x = (k / n : ℝ) ^ 2
  . rw [div_pow, eq_div_iff (by positivity), mul_comm]
    exact_mod_cast hc
  apply irrational_nrt_of_notint_nrt (x := k / n) 2 x
    (by exact_mod_cast hc.symm) ?_ (by decide) ⟨k / n, by simp⟩
  rintro ⟨y, hy⟩
  apply hs
  apply isSquare_of_exists_sq
  use y.natAbs
  zify
  rw [sq_abs]
  exact_mod_cast hy ▸ hc

lemma oks.gen (n : ℕ) (hs : ¬ IsSquare n)
  (m : ℕ) (hm : 5 < m) (d : ℤ) (hn : (m : ℤ) ∣ n - d)
  (h : ∀ u v : ZMod m, (v ^ 2 * d - u ^ 2).val ∉ Set.Icc 1 5) :
    ∀ k : ℕ, 0 < k → (5 / 2 : ℝ) < k * sqrt n * Int.fract (k * sqrt n) := by
  apply idea n hs
  intro x _ c hc k h'
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub] at hn
  push_cast at hn
  apply (congrArg <| Nat.cast (R := ZMod m)) at h'
  push_cast at h'
  rw [← hn, ← sub_eq_iff_eq_add'] at h'
  apply h k x
  rw [h']
  rw [Set.mem_Icc] at hc
  simp [hc, Nat.mod_eq_of_lt (hc.2.trans_lt hm)]

lemma oks.spec (n : ℕ) (hs : ¬ IsSquare n)
  (m : ℕ) (hm : 5 < m) (hn : m ∣ n)
  (h : ∀ u : ZMod m, (- u ^ 2).val ∉ Set.Icc 1 5) :
    ∀ k : ℕ, 0 < k → (5 / 2 : ℝ) < k * sqrt n * Int.fract (k * sqrt n) :=
  oks.gen n hs m hm 0 (by zify at hn; simpa) (by simpa using h)

set_option maxRecDepth 2000 in
set_option profiler true in
lemma oks.lemma144 (u v : ZMod 144) :
    (v ^ 2 * -1 - u ^ 2).val ∉ Set.Icc 1 5 := by
  -- this proof also works but it's much slower:
  -- revert u v
  -- decide
  let S := Finset.univ.image fun n : ZMod 144 => n ^ 2
  suffices : ∀ a ∈ S, ∀ b ∈ S, (b * -1 - a).val ∉ Set.Icc 1 5
  . apply this (u ^ 2) ?_ (v ^ 2) ?_ <;>
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have : S = {0, 1, 4, 9, 16, 25, 36, 49, 52, 64, 73, 81, 97, 100, 112, 121}
  . dsimp only [S]; decide
  rw [this]; decide

lemma oks (n : ℕ)
  (hs : ¬ IsSquare n)
  (h : 16 ∣ n ∨ 24 ∣ n ∨ 144 ∣ n + 1) :
    ∀ k : ℕ, 0 < k → (5 / 2 : ℝ) < k * sqrt n * Int.fract (k * sqrt n) := by
  obtain h | h | h := h
  . apply oks.spec (m := 16) <;> first | assumption | decide
  . apply oks.spec (m := 24) <;> first | assumption | decide
  . apply oks.gen n hs 144 (by decide) (-1) (by zify at h; simpa)
    exact_mod_cast oks.lemma144

lemma some_kinda_lemma {n : ℕ} (hs : IsSquare n) (hn : 24 ∣ n) :
    144 ∣ n := by
  rcases hs with ⟨k, rfl⟩
  rw [← pow_two] at hn ⊢
  obtain rfl | k_nz : k = 0 ∨ 0 < k := eq_zero_or_pos k
  . norm_num
  replace hn : 2 ^ 3 * 3 ^ 1 ∣ k ^ 2 := by simpa
  suffices 2 ^ 4 * 3 ^ 2 ∣ _ by simpa
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
  . norm_num
  . apply (dvd_mul_right _ _).trans at hn
    rw [padicValNat_dvd_iff, padicValNat.pow] at hn ⊢ <;> omega
  . apply (dvd_mul_left _ _).trans at hn
    rw [padicValNat_dvd_iff, padicValNat.pow] at hn ⊢ <;> omega

example
  (n : ℕ) :
    ∃ i : ℕ, i < 25 ∧
    ∀ k : ℕ, 0 < k → (5 / 2 : ℝ) < k * sqrt (n + i) * Int.fract (k * sqrt (n + i)) := by
  norm_cast
  let i := 23 - (n + 23) % 24
  have hi : i ≤ 23 := Nat.sub_le _ _
  have hn' : 24 ∣ n + i
  . rw [← Nat.add_sub_assoc]
    . apply Nat.dvd_sub_mod
    exact Nat.le_of_lt_succ <| Nat.mod_lt _ <| by decide
  clear_value i
  by_cases hs : IsSquare (n + i)
  case neg =>
    use i, hi.trans_lt (by decide), oks (n + i) hs (.inr <| .inl hn')
  case pos =>
    cases i with
    | zero =>
      rw [Nat.add_zero] at hn' hs
      use 24, by decide, oks (n + 24) ?_ (.inr ∘ .inl <| hn'.add dvd_rfl)
      intro hs'
      have := Nat.dvd_sub (Nat.le_add_right _ _)
        (some_kinda_lemma hs' (by simpa)) (some_kinda_lemma hs hn')
      replace this : 144 ∣ 24 := by simpa
      norm_num at this
    | succ i =>
      use i, Nat.lt_of_succ_le hi |>.trans (by decide), oks (n + i) ?_ <|
        .inr ∘ .inr <| some_kinda_lemma hs hn'
      rcases hs with ⟨x, hx⟩
      rintro ⟨y, hy⟩
      have : x * x - y * y = 1 := by omega
      simp_rw [← pow_two, Nat.sq_sub_sq, mul_eq_one] at this
      obtain rfl : x = 1 := by omega
      rw [hx] at hn'
      norm_num at hn'
