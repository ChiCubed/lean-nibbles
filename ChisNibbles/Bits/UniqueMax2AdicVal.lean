import Mathlib

/-
In a nonempty interval of positive naturals,
there's a unique maximum 2-adic valuation.
-/


open Set

open padicValNat in
theorem padicValNat.val_2_lt_add_of_eq
  (a b : ℕ)
  (ha : 0 < a) (hb : 0 < b)
  (h : padicValNat 2 a = padicValNat 2 b) :
    padicValNat 2 a < padicValNat 2 (a + b) := by
  have hab : 0 < a + b := by positivity
  rw [← PartENat.coe_lt_coe]
  apply congrArg (Nat.cast (R := PartENat)) at h
  simp_all only [add_pos_iff, or_self, padicValNat_eq_maxPowDiv, one_lt_two, ne_eq, ne_of_gt,
    not_false_eq_true, Nat.finiteMultiplicity_iff, and_true, maxPowDiv_eq_multiplicity,
    Nat.cast_inj, Nat.cast_lt]
  set va := multiplicity 2 a
  set vb := multiplicity 2 b
  have v_fin {x} (h : 0 < x) := @Nat.finiteMultiplicity_iff 2 x |>.mpr (by omega)
  have this {x} (h : 0 < x) := (v_fin h).exists_eq_pow_mul_and_not_dvd
  obtain ⟨a', ha₁ : a = 2 ^ va * a', ha'⟩ := this ha
  obtain ⟨b', hb₁ : b = 2 ^ vb * b', hb'⟩ := this hb
  rw [ha₁, hb₁]
  simp_rw [h]
  rw [← mul_add, multiplicity_mul Nat.prime_two.prime (v_fin (by rw [mul_add]; omega)),
    multiplicity_pow_self_of_prime Nat.prime_two.prime]
  rw [lt_add_iff_pos_right]
  apply multiplicity_pos_of_dvd
  omega

example (m n : ℕ) (hm : 0 < m) (ho : m < n) :
  ∃ x ∈ Ico m n, ∀ y ∈ Ico m n,
    padicValNat 2 x ≤ padicValNat 2 y → x = y := by
  by_contra! h
  replace h : ∀ x ∈ Ico m n, ∃ y ∈ Ico m n, padicValNat 2 x < padicValNat 2 y
  . peel h with x hx hy
    rcases hy with ⟨y, hy, hpy, hne⟩
    generalize hd : x.dist y = d
    induction d using Nat.strong_induction_on generalizing y with | h d ih =>
      cases hpy.eq_or_lt with
      | inr hpy => exact ⟨y, hy, hpy⟩
      | inl hpy =>
        simp only [mem_Ico] at *
        let z := (x + y) / 2
        have hpz' := padicValNat.val_2_lt_add_of_eq x y (by omega) (by omega) hpy
        have hdvd : 2 ∣ x + y := dvd_of_one_le_padicValNat (by omega)
        apply ih (Nat.dist x z) ?_ z (by omega) ?_ (by omega) rfl
        . rw [Nat.dist] at hd ⊢
          omega
        . rw [padicValNat.div hdvd]
          exact Nat.le_sub_one_of_lt hpz'
  simp_rw [← Finset.coe_Ico] at h
  contrapose! h
  apply Finset.exists_max_image
  simpa
