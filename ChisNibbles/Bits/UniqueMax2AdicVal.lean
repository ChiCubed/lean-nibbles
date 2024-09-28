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
  simp only [padicValNat_eq_maxPowDiv, maxPowDiv_eq_multiplicity,
    one_lt_two, ha, hb, hab] at h ⊢
  set va := multiplicity 2 a
  set vb := multiplicity 2 b
  have v_fin {x} (h : 0 < x) := multiplicity.finite_nat_iff.mpr ⟨one_lt_two.ne', h⟩
  have this {x} (h : 0 < x) := multiplicity.exists_eq_pow_mul_and_not_dvd <| v_fin h
  obtain ⟨a', ha₁ : a = 2 ^ (va.get _) * a', ha'⟩ := this ha
  obtain ⟨b', hb₁ : b = 2 ^ (vb.get _) * b', hb'⟩ := this hb
  rw [ha₁, hb₁]
  simp_rw [h]
  rw [← mul_add, multiplicity.mul Nat.prime_two.prime,
    multiplicity.multiplicity_pow_self (by norm_num) (by simp)]
  simp only [PartENat.natCast_get, gt_iff_lt]
  rw [PartENat.lt_add_iff_pos_right (multiplicity.ne_top_iff_finite.mpr <| v_fin hb),
    multiplicity.dvd_iff_multiplicity_pos]
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
