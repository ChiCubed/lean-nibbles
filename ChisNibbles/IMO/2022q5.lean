import Mathlib.NumberTheory.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals

-- This is a port from Lean 3, and man, the current `omega` tactic is *so* convenient.

open Nat Finset
open scoped Nat

namespace IMO.«2022»

namespace q5

-- i had this back in the day,
-- but it's slightly inconvenient to work with
-- abbrev ndvd {α : Type*} [Dvd α] (a b : α) : Prop := ¬ a ∣ b

lemma desc_fac_bound : ∀ n r : ℕ,
    n.descFactorial (r+1) ≤ (n - r/2) ^ (r+1)
  | 0, r => by
    simp
  | n+1, 0 | n+1, 1 => by
    convert descFactorial_le_pow (n + 1) _ using 0
  | n+1, r+2 => by
    rw [succ_descFactorial_succ, descFactorial_succ]
    suffices (n + 1) * (n - (r+1)) ≤ (n - r/2) * (n - r/2) by
      simpa only [← mul_assoc, pow_succ', ofNat_pos, add_div_right, reduceSubDiff]
        using mul_le_mul' this (desc_fac_bound n r)
    by_cases h : n - (r+1) = 0
    case pos => simp [h]
    have h₁ : r + 1 ≤ n := by omega
    have h₂ : r / 2 ≤ n := by omega
    zify [h₁, h₂]
    nlinarith [show ((r / 2) * 2 : ℤ) ≤ r by omega]

-- ...having to add a space between n and ! is less convenient.
-- you win some you lose some i guess.
lemma fac_bound (n : ℕ) : n ! ≤ (n/2 + 1) ^ n := by
  cases' n with n
  case zero => norm_num
  convert desc_fac_bound (n+1) n using 1
  . simp [descFactorial_eq_div]
  . congr; omega

lemma weak_fac_bound (n : ℕ) : n ! ≤ n ^ n := by
  cases' n with n
  case zero => norm_num
  apply fac_bound (n+1) |>.trans
  gcongr; omega

lemma pow_add_lt_aux (a : ℕ) : ∀ n : ℕ,
    (a+1) ^ (n+2) + (n+2) < (a+2) ^ (n+2)
  | 0 => by
    simp only [zero_add]
    linarith [a.zero_le]
  | n+1 => by
    simp_rw [pow_succ _ (n+2)]
    apply mul_lt_mul_of_pos_right (pow_add_lt_aux a n) (show 0 < a + 2 by omega)
      |>.trans_le'
    rw [add_mul]
    nlinarith [(a + 1) ^ (n + 2) |>.zero_le]

-- if < were ≤ we could remove n_large
lemma pow_add_lt {a b n : ℕ} (a_pos : 0 < a) (n_large : 2 ≤ n) (a_lt_b : a < b) :
    a^n + n < b^n := by
  suffices a^n + n < (a+1)^n from this.trans_le $ by gcongr; omega
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_lt a_pos
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le n_large
  convert pow_add_lt_aux a n using 2 <;> ring

lemma prod_dvd_fac_of_le (n : ℕ) (s : Finset ℕ) (h : ∀ x ∈ s, 0 < x ∧ x ≤ n) :
    s.prod id ∣ (n)! :=
  Finset.prod_Ico_id_eq_factorial n ▸ Finset.prod_dvd_prod_of_subset _ _ _ fun x hx =>
    have ⟨l, r⟩ := h x hx; mem_Ico.mpr ⟨l, lt_succ_of_le r⟩

abbrev sorted_to_finset
  {α : Type*} {r : α → α → Prop} [IsIrrefl α r]
  (l : List α) (h : l.Sorted r) :
    Finset α :=
  ⟨l, h.nodup⟩

end q5


def q5.soln_set : Finset (ℕ × ℕ × ℕ) := {(2, 2, 2), (3, 4, 3)}

open q5 in
theorem q5 (a b p : ℕ) :
    0 < a ∧ 0 < b ∧ 0 < p ∧ p.Prime ∧ a^p = b ! + p ↔
    (a, b, p) ∈ soln_set := by
  constructor
  case mpr => intro h; fin_cases h <;> decide

  rintro ⟨a_pos, b_pos, p_pos, hp, h⟩

  have one_lt_a : 1 < a := Nat.one_lt_pow_iff p_pos.ne' |>.mp $
    h ▸ Nat.lt_add_left _ hp.one_lt

  have not_b_min (lt_p : b < p) (lt_a : b < a) : False :=
    flip ne_of_gt h $
    calc
      b ! + p ≤ b^b + p := by gcongr; apply weak_fac_bound
      _       ≤ b^p + p := by gcongr; exact b_pos
      _       < a^p     := pow_add_lt b_pos hp.two_le lt_a

  have b_lt_ndvd {n} (n_pos : 0 < n) : ¬ n ∣ b ! → b < n :=
    lt_of_not_le ∘ mt (dvd_factorial n_pos)

  obtain ⟨m, rfl⟩ : p ∣ a := by
    by_contra p_ndvd_a
    refine not_b_min (b_lt_ndvd p_pos ?p_ndvd_b!) (b_lt_ndvd a_pos ?a_ndvd_b!)
    case p_ndvd_b! =>
      contrapose! p_ndvd_a with p_dvd_b!
      exact hp.dvd_of_dvd_pow $ h ▸ p_dvd_b!.add dvd_rfl
    case a_ndvd_b! =>
      contrapose! p_ndvd_a with a_dvd_b!
      suffices a ∣ p by
        rw [dvd_prime_two_le hp one_lt_a] at this
        rw [this]
      rw [← Nat.dvd_add_right a_dvd_b!, ← h]
      exact dvd_pow_self _ p_pos.ne'
  have m_pos : 0 < m := Nat.pos_of_mul_pos_left a_pos
  have b_lo : p ≤ b := by
    by_contra! h
    exact not_b_min h $ h.trans_le $ Nat.le_mul_of_pos_right _ m_pos
  clear a_pos one_lt_a not_b_min

  have b_hi : b < 2 * p := by
    suffices ¬ p ^ 2 ∣ (b)! by
      contrapose! this with b_large
      refine trans ?_ $ factorial_dvd_factorial b_large
      convert trans ?_ $ factorial_mul_factorial_dvd_factorial_add p p using 2
      . ring
      rw [← pow_two]
      apply pow_dvd_pow_of_dvd
      apply dvd_factorial p_pos le_rfl
    suffices p ^ 2 ∣ (b)! + p by
      have hp : ¬ p^2 ∣ p := by
        nth_rw 2 [← pow_one p]
        rw [pow_dvd_pow_iff_le_right hp.one_lt]
        decide
      contrapose! hp with hb
      rwa [← Nat.dvd_add_right hb]
    rw [← h]
    apply dvd_trans $ pow_dvd_pow_of_dvd (dvd_mul_right p m) _
    exact pow_dvd_pow _ hp.two_le

  have m_small : m < p := by
    refine lt_of_mul_lt_mul_left' $ lt_of_pow_lt_pow_left p (p * p).zero_le ?_
    rw [← pow_two, ← pow_mul, h]
    calc
      b ! + p ≤ (2*p - 1)! + p    := by gcongr; omega
      _       ≤ p ^ (2*p - 1) + p := by gcongr; convert fac_bound (2 * p - 1); omega
      _       < p ^ (2*p - 1) * 2 := ?_
      _       ≤ p ^ (2*p - 1) * p := by gcongr; exact hp.two_le
      _       ≤ p ^ (2*p)         := by rw [← pow_succ]; gcongr <;> omega
    rw [mul_two]
    gcongr
    apply lt_self_pow <;> have := hp.one_lt <;> omega

  obtain rfl : m = 1 := by
    suffices m ≤ 1 by omega
    contrapose! b_lo with one_lt_m
    refine b_lt_ndvd m_pos ?_ |>.trans m_small
    have h₁ : ¬ m ∣ p := by rw [dvd_prime hp]; omega
    contrapose! h₁
    rw [← Nat.dvd_add_right h₁, ← h, mul_pow]
    apply dvd_mul_of_dvd_right
    exact dvd_pow_self _ p_pos.ne'
  clear m_pos m_small b_lt_ndvd
  simp only [mul_one] at *

  obtain p_smol | p_big : (p = 2 ∨ p = 3) ∨ 4 ≤ p := by
    have := hp.two_le; omega
  case inl =>
    rw [← Nat.sub_eq_iff_eq_add (le_self_pow p_pos.ne' _)] at h
    obtain rfl | rfl := p_smol <;>
      norm_num at h <;>
      simp only [soln_set, mem_insert, Prod.mk.injEq, and_true, true_and, mem_singleton,
        reduceEqDiff, and_false, and_self, or_false, false_or]
    . exact symm $ factorial_inj (n := 2) (by decide) |>.mp h
    . exact symm $ factorial_inj (n := 4) (by decide) |>.mp h
  exfalso

  obtain ⟨k, rfl⟩ := hp.eq_two_or_odd'.resolve_left $ by omega
  let o := 2 * k
  set p := o + 1

  have b_ne : p ≠ b := by
    rintro rfl
    clear b_pos b_lo b_hi
    apply flip Nat.ne_of_gt h
    calc
      p ! + p = p * o ! + p       := by rw [factorial_succ]
      _       ≤ p * o ^ o + p     := by gcongr; apply weak_fac_bound
      _       = p * (o ^ o + 1)   := by ring
      _       < p * (o ^ o + 2*k) := by gcongr <;> omega
      _       < p * (p ^ o)       := ?_
      _       = p ^ p             := by rw [← Nat.pow_succ']
    gcongr
    case' bc => apply pow_add_lt
    all_goals omega

  replace b_lo : p < b := by omega
  clear b_ne

  have con₁ : (p + 1) ^ 2 ∣ b ! := by
    refine trans ?_ $ factorial_dvd_factorial (show p + 1 ≤ b by omega)
    convert prod_dvd_fac_of_le (p + 1)
      (sorted_to_finset (r := (· < ·)) [2, k + 1, 2 * k + 2] ?sorted)
      ?prod_eq
    simp; ring
    -- it's also possible to just whack these goals:
    -- case sorted | prod_eq => simp; omega
    case sorted =>
      simp only [List.Sorted, ← List.chain'_iff_pairwise,
        List.chain'_cons, List.chain'_singleton, and_true]
      omega
    case prod_eq =>
      simp only [mem_mk, Multiset.mem_coe, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      omega
  absurd con₁; clear con₁

  replace h : (p ^ p - p : ℤ) = b ! := by rw [sub_eq_iff_eq_add]; exact_mod_cast h

  have : (p ^ p - p : ℤ) = (p + 1) * (p * o * ∑ i in range k, (p ^ 2) ^ i) := by
    rw [pow_succ, pow_mul]
    convert congrArg ((p : ℤ) * ·) (mul_geom_sum (p ^ 2 : ℤ) k).symm using 1
    . ring
    . clear_value o; push_cast; ring
  rw [this] at h; clear this
  norm_cast at h

  have con : ¬ p + 1 ∣ p * o * ∑ i in range k, (p ^ 2) ^ i := by
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    have : (o : ZMod (p + 1)) = -2 := by
      rw [← sub_eq_zero, sub_neg_eq_add]
      norm_cast
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
    push_cast; rw [this]; norm_num1
    simp only [one_pow, sum_const, card_range, smul_one_eq_cast]
    norm_cast
    rw [this, neg_eq_zero, ← ZMod.val_eq_zero]
    erw [ZMod.val_cast_of_lt] <;> linarith only [p_big]

  rwa [pow_two, ← h, mul_dvd_mul_iff_left (by omega)]

end IMO.«2022»
