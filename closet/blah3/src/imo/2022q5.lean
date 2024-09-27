import number_theory.basic
import data.zmod.basic
import algebra.big_operators
import tactic

open nat finset
open_locale nat big_operators

namespace imo2022q5

@[reducible] def ndvd {α : Type*} [has_dvd α] (a b : α) : Prop := ¬ a ∣ b
infix ` ∤ `:50 := ndvd

def soln_set : set (ℕ × ℕ × ℕ) := {(2, 2, 2), (3, 4, 3)}

-- TODO do this in ℚ instead so it's not sus
-- and/or attempt finset proofs
lemma desc_fac_bound : ∀ (n r : ℕ),
  n.desc_factorial r ≤ (n - (r-1)/2) ^ r
| 0 0         := by simp
| 0 (r+1)     := by simp
| (n+1) 0     := by simp [one_le_pow']
| (n+1) 1     := by norm_num [pow_one]
| (n+1) 2     := by { zify, norm_num [pow_two] }
| (n+1) (r+3) :=
suffices (n + 1) * (n - (r + 1)) ≤ (n - r/2) * (n - r/2),
by simpa [← mul_assoc, pow_succ] using mul_le_mul' this (desc_fac_bound n (r+1)),
begin
  by_cases h : (n - (r + 1) = 0), { simp [h] },
  have : r + 1 ≤ n := le_of_not_le (nat.sub_eq_zero_iff_le.not.mp h),
  have : r / 2 ≤ n := (nat.div_le_self r 2).trans (le_of_succ_le this),
  zify, ring_nf,
  refine int.add_le_add
    (int.mul_le_mul_of_nonneg_right (int.sub_le_sub_left _ _) (by simp))
    _,
  { rw mul_comm, exact int.div_mul_le _ two_ne_zero },
  exact le_trans (by { rw_mod_cast [neg_sub_left, neg_nonpos], simp })
                 (sq_nonneg _),
end

-- aaaa
lemma half_and_half : ∀ (n : ℕ), n = n / 2 + (n + 1) / 2
| 0     := by norm_num
| 1     := by norm_num
| (n+2) :=
begin
  conv_lhs { rw half_and_half n },
  conv_rhs { congr, skip, rw add_assoc,
    conv { congr, congr, skip, rw add_comm }, rw [← add_assoc] },
  simp only [add_div_right _ two_pos, succ_eq_add_one],
  abel,
end

lemma fac_bound (n : ℕ) : n! ≤ (n/2 + 1) ^ n :=
begin
  cases n, { norm_num },
  convert desc_fac_bound (n+1) (n+1), { simp [desc_factorial_eq_div] },

  symmetry,
  rw [add_succ_sub_one, add_zero,
    nat.sub_eq_iff_eq_add ((nat.div_le_self _ _).trans (le_succ _)),
    add_comm, ← add_assoc],
  apply congr_arg,

  exact half_and_half n,
end

lemma weak_fac_bound (n : ℕ) : n! ≤ n ^ n :=
begin
  cases n, { norm_num },
  refine (fac_bound n.succ).trans (nat.pow_le_pow_of_le_left _ _),
  exact succ_le_of_lt (div_lt_self n.succ_pos one_lt_two),
end

-- TODO
lemma pow_add_lt_aux : ∀ a n : ℕ,
  (a+1)^(n+2) + (n+2) < (a+2)^(n+2)
| a 0     := by { ring_nf, exact add_lt_add_of_le_of_lt
                    (nat.mul_le_mul_right _ $ @le.intro _ _ 2 rfl) (lt_succ_self _) }
| a (n+1) :=
begin
  simp_rw [(by abel : n + 1 + 2 = n + 2 + 1)],
  conv_lhs { rw pow_succ }, conv_rhs { rw pow_succ },

  cases a,
  { have := pow_add_lt_aux 0 n,
    simp only [zero_add, one_pow] at ⊢ this,
    ring_nf at ⊢ this,
    refine has_le.le.trans_lt _ ((mul_lt_mul_left two_pos).mpr this),
    linarith },

  calc _ + _ ≤ (a+2) * (a+2)^(n+2) + (a+2) * (n+2) : add_le_add_left _ _
         ... = (a+2) * _                           : (left_distrib _ _ _).symm
         ... < (a+2) * (a+3)^(n+2)                 : (mul_lt_mul_left $ succ_pos _).mpr (pow_add_lt_aux (a+1) n)
         ... ≤ (a+3) * (a+3)^(n+2)                 : (mul_le_mul_right $ pow_pos (succ_pos _) _).mpr (le_succ _),

  ring_nf,
  exact add_le_add (le_mul_of_pos_left $ succ_pos _) (by linarith),
end

-- if < becomes ≤ the hypothesis on n dies yay
lemma pow_add_lt {a b n : ℕ} (a_pos : 0 < a) (n_large : 2 ≤ n) (h : a < b) :
  a^n + n < b^n :=
begin
  suffices : a^n + n < (a+1)^n,
  from this.trans_le (nat.pow_le_pow_of_le_left h.nat_succ_le _),
  convert pow_add_lt_aux (a - 1) (n - 2) using 2; zify,
  { congr, ring1, { zify, ring1 } },
  all_goals { ring1 },
end

lemma prod_dvd_fac_of_le (n : ℕ) (s : finset ℕ) (h : ∀ x ∈ s, 0 < x ∧ x ≤ n) :
  s.prod id ∣ n! :=
finset.prod_Ico_id_eq_factorial n ▸ finset.prod_dvd_prod_of_subset _ _ _ (λ x hx,
  let ⟨l, r⟩ := h x hx in mem_Ico.mpr ⟨l, lt_succ_of_le r⟩)

abbreviation sorted_to_finset (l : list ℕ) (h : l.sorted (<)) : finset ℕ :=
{val := ↑l, nodup := list.sorted.nodup h}

theorem imo2022q5 (a b p : ℕ) :
  0 < a ∧ 0 < b ∧ 0 < p ∧ p.prime ∧ a^p = b! + p ↔
  (a, b, p) ∈ soln_set :=
begin
  split, swap,
  { intro h, simp [soln_set] at h,
    cases h; rcases h with ⟨rfl, rfl, rfl⟩; norm_num [prime_two, prime_three] },

  rintro ⟨a_pos, b_pos, p_pos, p_prime, h⟩,

  have one_lt_a : 1 < a := (nat.one_lt_pow_iff p_pos.ne).mp
    (h.symm ▸ lt_add_of_le_of_pos (succ_le_of_lt $ factorial_pos b) p_pos),

  have not_b_min : b < p → b < a → false,
  { refine λ lt_p lt_a, ne_of_gt _ h,
    calc b! + p ≤ b^b + p : add_le_add_right (weak_fac_bound b) _
            ... ≤ b^p + p : add_le_add_right (pow_le_pow b_pos.nat_succ_le lt_p.le) _
            ... < a^p     : pow_add_lt b_pos p_prime.two_le lt_a },

  have b_lt_ndvd : ∀ {n}, 0 < n → n ∤ b! → b < n :=
  λ n n_pos, lt_of_not_le ∘ mt (dvd_factorial n_pos),

  have p_dvd_a : p ∣ a,
  { by_contra p_ndvd_a,
    refine not_b_min (b_lt_ndvd p_pos _) (b_lt_ndvd a_pos _),
    from (nat.dvd_add_left dvd_rfl).not.mp (h ▸ mt p_prime.dvd_of_dvd_pow p_ndvd_a),

    refine mt nat.dvd_add_right (λ hd, (_ : ¬ a ∣ p) $ hd.mp $
      h ▸ dvd_pow_self _ p_pos.ne'),
    refine (dvd_prime p_prime).not.mpr _,
    rintro (rfl | rfl), from one_lt_a.ne rfl, from p_ndvd_a dvd_rfl },

  -- TODO merge with the above? do i want to not rewrite?
  obtain ⟨m, rfl⟩ := p_dvd_a,

  have b_small : b < 2 * p,
  { suffices : p^2 ∤ b!,
    -- FIXME revise this when you have more factorial divisibiilty machinery
    { contrapose! this with b_large,
      refine dvd_trans _ (factorial_dvd_factorial b_large),
      convert dvd_trans _ (factorial_mul_factorial_dvd_factorial_add p p), ring1,
      from pow_two p! ▸ pow_dvd_pow_of_dvd (dvd_factorial p_pos le_rfl) 2 },

    refine mt nat.dvd_add_right (λ hd, h ▸ absurd _ $ hd.not.mpr $
      show ¬ p^2 ∣ p, by { nth_rewrite 1 ← pow_one p,
        exact (pow_dvd_pow_iff_le_right p_prime.one_lt).not.mpr one_lt_two.not_le }),
    rw mul_pow, exact dvd_mul_of_dvd_left (pow_dvd_pow p p_prime.two_le) _ },

  have m_small : m < p,
  { refine lt_of_mul_lt_mul_left' (lt_of_pow_lt_pow p (p * p).zero_le _),
    rw [← pow_two, ← pow_mul, h],
    calc b! + p ≤ (2*p - 1)! + p  : add_le_add_right (factorial_le $ le_pred_of_lt b_small) _
            ... ≤ p^(2*p - 1) + p : add_le_add_right _ _
            ... < p^(2*p - 1) * 2 : (mul_two $ p^(2*p - 1)).symm ▸ add_lt_add_left _ _
            ... ≤ p^(2*p)         : _,

    { convert fac_bound (2*p - 1),
      cases p, cases p_pos,
      simp [mul_succ, ← bit1_val] },
    { nth_rewrite 0 ← pow_one p,
      rw pow_lt_iff_lt_right p_prime.two_le,
      have := p_prime.two_le, revert this, omega manual },
    { cases p, cases p_pos,
      change (p+1)^(2*p + 1) * 2 ≤ (p+1)^(2*p + 2),
      nth_rewrite 1 pow_succ',
      exact mul_le_mul_left' p_prime.two_le _ } },

  have m_pos : 0 < m :=
  nat.pos_of_ne_zero (not_or_distrib.mp $ zero_eq_mul.not.mp a_pos.ne).2,

  obtain rfl : m = 1 := by
  { suffices : m ≤ 1, { revert m_pos this, omega manual },
    by_contra' one_lt_m,
    suffices : b < p, from not_b_min this (lt_mul_of_lt_of_one_lt' this one_lt_m),
    refine (b_lt_ndvd m_pos _).trans m_small,
    refine mt nat.dvd_add_right (λ hd, absurd (hd.mp _) $
      m_small.ne ∘ (dvd_prime_two_le p_prime one_lt_m.nat_succ_le).mp),
    rw [← h, mul_pow], from dvd_mul_of_dvd_right (dvd_pow_self _ p_pos.ne') _ },

  simp only [mul_one] at *,
  have p_small : p < 4,
  { by_contra' four_le_p,
    obtain ⟨k, hk⟩ := p_prime.eq_two_or_odd'.resolve_left (by linarith),

    have ik : 1 < k := by linarith only [(hk ▸ four_le_p : 4 ≤ 2*k + 1)],

    suffices : b < p + 1,
    { obtain rfl := (symm $ eq_of_lt_succ_of_not_lt this $ λ h, not_b_min h h),
      refine ne_of_gt _ h, rw hk,
      calc (2*k+1)! + (2*k+1) = (2*k+1) * (2*k)! + (2*k+1)
       : by rw factorial_succ
                          ... ≤ (2*k+1) * (2*k)^(2*k) + (2*k+1)
       : add_le_add_right (nat.mul_le_mul_left _ $ weak_fac_bound _) _
                          ... = (2*k+1) * ((2*k)^(2*k) + 1)
       : by ring
                          ... < (2*k+1) * ((2*k)^(2*k) + 2*k)
       : mul_lt_mul_of_pos_left (add_lt_add_left (by linarith) _) succ_pos'
                          ... < (2*k+1) * ((2*k + 1)^(2*k))
       : mul_lt_mul_of_pos_left (pow_add_lt (by linarith) (by linarith) (lt.base _)) succ_pos'
                          ... = (2*k+1) ^ (2*k+1)
       : symm $ pow_succ _ _ },

    zify at h, rw ← sub_eq_iff_eq_add at h,

    have h₁ : ↑p^p - ↑p = ((p+1) * (p * (p-1) * ∑ i in range k, (p^2)^i) : ℤ),
    { nth_rewrite 1 hk,
      rw [pow_succ, pow_mul],
      convert congr_arg (λ x, ↑p * x) (mul_geom_sum (p^2 : ℤ) k).symm using 1; ring },

    have h₂ : ↑(p+1) ∤ (p * (p-1) * ∑ i in range k, (p^2)^i : ℤ),
    { apply (zmod.int_coe_zmod_eq_zero_iff_dvd _ _).not.mp,
      push_cast,
      have : (p : zmod (p+1)) = -1 :=
      @zmod.nat_cast_zmod_val _ ⟨succ_ne_zero p⟩ (-1) ▸ (zmod.val_neg_one p).symm ▸ rfl,
      rw [this, hk], norm_num1,
      simp only [one_pow, sum_const, card_range, smul_one_eq_coe],
      norm_cast,
      rw [← zmod.val_eq_zero, zmod.val_cast_of_lt],
      linarith only [ik], from (lt.base (2*k)).step },

    have h₃ : ↑(p+1)^2 ∤ (b! : ℤ),
    { rw [← h, pow_two, h₁],
      exact (mul_dvd_mul_iff_left $ (int.coe_nat_succ_pos _).ne').not.mpr h₂ },

    contrapose! h₃ with b_large, norm_cast,
    rw hk at ⊢ b_large,
    convert dvd_trans (prod_dvd_fac_of_le (2*k+2) (sorted_to_finset [2, k+1, 2*k+2] _) _)
      (factorial_dvd_factorial b_large),
    { simp, ring },
    { simp, revert ik, omega manual },
    { simp, omega manual }
  },

  zify at h, rw ← sub_eq_iff_eq_add at h,
  interval_cases p; norm_num at h; norm_cast at h,
  simpa [soln_set] using (symm $ (factorial_inj $ show 1 < 2!, by norm_num).mp h),
  simpa [soln_set] using (symm $ (factorial_inj $ show 1 < 4!, by norm_num).mp h),
end

end imo2022q5
