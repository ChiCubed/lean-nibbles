import Mathlib


/-
For n > m > 1 odd, x^n + x^m + x + 1 is irreducible.
-/


open Polynomial


namespace Polynomial

variable {R : Type*} [Semiring R]

def trunc (n : ℕ) (p : R[X]) : R[X] where
  toFinsupp := p.toFinsupp.filter (· < n)

theorem trunc_coeff_eq_ite (n : ℕ) (p : R[X]) (i : ℕ) :
    (trunc n p).coeff i = if i < n then p.coeff i else 0 := by
  rw [trunc, coeff, coeff, Finsupp.filter_apply]

theorem trunc_coeff_eq_of_lt (n : ℕ) (p : R[X]) {i : ℕ} (hi : i < n) :
    (trunc n p).coeff i = p.coeff i := by
  simp [trunc_coeff_eq_ite, hi]

theorem trunc_coeff_eq_zero (n : ℕ) (p : R[X]) {i : ℕ} (hi : n ≤ i) :
    (trunc n p).coeff i = 0 := by
  simp [trunc_coeff_eq_ite, hi]

theorem trunc_coeff_eq_of_ne_zero {n : ℕ} {p : R[X]} {i : ℕ}
  (h : (trunc n p).coeff i ≠ 0) :
    (trunc n p).coeff i = p.coeff i := by
  rw [trunc_coeff_eq_ite] at h ⊢
  aesop

theorem coeff_eq_of_trunc_coeff_eq_of_ne_zero {n : ℕ} {p : R[X]} {i : ℕ}
  {x : R} (h : (trunc n p).coeff i = x) (hx : x ≠ 0) :
    p.coeff i = x := by
  rwa [trunc_coeff_eq_of_ne_zero (h ▸ hx)] at h

theorem trunc_X_pow_eq_ite (n : ℕ) (k : ℕ) :
    trunc n (X ^ k : R[X]) = if k < n then X ^ k else 0 := by
  ext i
  rw [trunc_coeff_eq_ite, apply_ite (coeff (R := R) · i)]
  simp only [coeff_X_pow, coeff_zero, ← ite_and]
  grind

theorem trunc_X_eq_ite (n : ℕ) :
    trunc n (X : R[X]) = if 1 < n then X else 0 := by
  rw [← pow_one X, trunc_X_pow_eq_ite]

theorem trunc_one_eq_ite (n : ℕ) :
    trunc n (1 : R[X]) = if 0 < n then 1 else 0 := by
  rw [← pow_zero X, trunc_X_pow_eq_ite]

theorem trunc_add (n : ℕ) (p q : R[X]) :
    trunc n p + trunc n q = trunc n (p + q) := by
  ext i
  simp_rw [coeff_add, trunc_coeff_eq_ite]
  split <;> simp

theorem trunc_trunc_mul_trunc (n : ℕ) (p q : R[X]) :
    trunc n (trunc n p * trunc n q) = trunc n (p * q) := by
  ext i
  simp_rw [trunc_coeff_eq_ite]
  split_ifs with hi
  . simp_rw [coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨a, b⟩ h
    simp only [Finset.mem_antidiagonal] at h ⊢
    rw [trunc_coeff_eq_of_lt n _ (i := a) (by omega), trunc_coeff_eq_of_lt n _ (i := b) (by omega)]
  . rfl


lemma sum_X_pow_finset_eq_ofFinsupp_indicator
  (s : Finset ℕ) :
    (∑ i ∈ s, X ^ i : R[X]) = ofFinsupp (.indicator s fun _ _ => 1) := by
  ext; simp


theorem eval₂_mirror_mul_pow
  {S : Type*} [CommSemiring S]
  (i : R →+* S)
  (x : S) [Invertible x]
  (f : R[X]) :
    eval₂ i (⅟x) f.mirror * x ^ (f.natDegree + f.natTrailingDegree) = eval₂ i x f := by
  rw [mirror, eval₂_mul, mul_right_comm, pow_add, ← mul_assoc, eval₂_reverse_mul_pow]
  simp [mul_assoc, ← mul_pow]

theorem eval₂_mirror_eq
  {S : Type*} [CommSemiring S]
  (i : R →+* S)
  (x : S) [Invertible x]
  (f : R[X]) :
    eval₂ i x f.mirror = eval₂ i (⅟x) f * x ^ (f.natDegree + f.natTrailingDegree) := by
  nth_rw 2 [← eval₂_mirror_mul_pow]
  simp [mul_assoc, ← mul_pow]

theorem eval_mirror_eq
  {R : Type*} [CommSemiring R]
  (x : R) [Invertible x]
  (f : R[X]) :
    eval x f.mirror = eval (⅟x) f * x ^ (f.natDegree + f.natTrailingDegree) :=
  eval₂_mirror_eq ..


theorem IsPrimitive.isRelPrime_fraction_map_iff
  {R : Type*} [CommRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]
  {f g : R[X]}
  (hf : f.IsPrimitive)
  (h : IsRelPrime (map (algebraMap R K) f) (map (algebraMap R K) g)) :
    IsRelPrime f g := fun d hdf hdg =>
  isPrimitive_of_dvd hf hdf |>.isUnit_iff_isUnit_map.mpr <|
    h (d := map (algebraMap R K) d) (d.map_dvd _ hdf) (d.map_dvd _ hdg)

end Polynomial


theorem Finsupp.support_indicator_of_ne_zero
  {ι α : Type*} [Zero α] (s : Finset ι)
  (f : (i : ι) → i ∈ s → α)
  (hf : ∀ i (hi : i ∈ s), f i hi ≠ 0) :
    (indicator s f).support = s := by
  classical
  apply_mod_cast antisymm (support_indicator_subset s f)
  intro i hi
  simp [mem_support_iff, indicator_apply, hi, hf]



structure Data where
  (n m : ℕ)
  (n_odd : Odd n) (m_odd : Odd m)
  (h_n_m : n > m) (h_m_1 : m > 1)


namespace Data

variable (d : Data)

noncomputable def p : ℤ[X] := X ^ d.n + X ^ d.m + X + 1

lemma p_ix_nodup : [0, 1, d.m, d.n].Nodup :=
  List.Pairwise.nodup <| List.chain'_iff_pairwise.mp <|
    show List.Chain' (· < ·) _ by simp [d.h_n_m, d.h_m_1]

lemma p_ix_toFinset : [0, 1, d.m, d.n].toFinset = {0, 1, d.m, d.n} := by
  simp

theorem p_eq' : d.p = ofFinsupp (.indicator {0, 1, d.m, d.n} fun _ _ => 1) := by
  rw [p]
  convert_to ([0, 1, d.m, d.n].map (X ^ ·)).sum = (_ : ℤ[X])
  . simp; ring
  rw [← List.sum_toFinset _ d.p_ix_nodup, sum_X_pow_finset_eq_ofFinsupp_indicator, d.p_ix_toFinset]

theorem p_primitive : d.p.IsPrimitive := by
  rw [isPrimitive_iff_content_eq_one]
  suffices d.p.content ∣ 1 from
    Int.eq_one_of_dvd_one (Int.nonneg_of_normalize_eq_self normalize_content) this
  convert d.p.content_dvd_coeff 0
  simp [p_eq']

theorem p_natDeg : d.p.natDegree = d.n := by
  rw [p]
  simp_rw [add_assoc]
  repeat
    rw [natDegree_add_eq_left_of_natDegree_lt]
    . simp [d.h_n_m, d.h_m_1]
    simp

theorem p_natTrailDeg : d.p.natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero]
  right
  rw [p_eq']
  simp

theorem p_natDeg_pos : 0 < d.p.natDegree := by
  rw [p_natDeg]
  cases d; dsimp; omega

theorem mirror_p_eq' : d.p.mirror = ofFinsupp (.indicator {0, d.n - d.m, d.n - 1, d.n} fun _ _ => 1) := by
  rw [mirror, p_natTrailDeg, pow_zero, mul_one, reverse, p_natDeg, p_eq']
  ext i
  simp only [coeff_reflect, coeff_ofFinsupp, Finsupp.indicator_apply]
  congr! 1
  rw [← Finset.mem_map' (revAt d.n), revAt_invol]
  have := d.h_n_m; have := d.h_m_1
  congr! 1
  calc _ = {d.n, d.n - 1, d.n - d.m, 0} := ?_
       _ = [d.n, d.n - 1, d.n - d.m, 0].toFinset := by simp
       _ = [0, d.n - d.m, d.n - 1, d.n].toFinset := List.toFinset_reverse.symm
       _ = _                                     := by simp
  simp_rw [Finset.map_insert, Finset.map_singleton]
  congr <;> rw [revAt_le] <;> omega

theorem mirror_p_eq : d.p.mirror = X ^ d.n + X ^ (d.n - 1) + X ^ (d.n - d.m) + 1 := by
  rw [mirror_p_eq']
  -- i could deduce this from the other stuff but whatever
  have nodup : [0, d.n - d.m, d.n - 1, d.n].Nodup :=
    List.Pairwise.nodup <| List.chain'_iff_pairwise.mp <|
      show List.Chain' (· < ·) _ by have := d.h_n_m; have := d.h_m_1; simp; omega
  have toFinset : [0, d.n - d.m, d.n - 1, d.n].toFinset = {0, d.n - d.m, d.n - 1, d.n} := by
    simp
  rw [← sum_X_pow_finset_eq_ofFinsupp_indicator, ← toFinset, List.sum_toFinset _ nodup]
  simp; ring



lemma n_sub_m_even : Even (d.n - d.m) := by
  cases d
  apply_rules [Nat.Odd.sub_odd]

lemma one_lt_n_sub_m : 1 < d.n - d.m := by
  have := d.h_n_m
  have ⟨k, hk⟩ := d.n_sub_m_even.exists_two_nsmul
  rw [nsmul_eq_mul] at hk
  omega

def k : ℕ := min d.m (d.n - d.m)

lemma one_lt_k : 1 < d.k := by
  have := d.h_m_1
  have := d.one_lt_n_sub_m
  rw [k]; omega

lemma k_le_n : d.k ≤ d.n := by
  rw [k]; omega

lemma p_mul_mirror_low :
    trunc (d.k + 1) (d.p * d.p.mirror) = X ^ d.k + X + 1 := by
  rw [d.mirror_p_eq, p, ← trunc_trunc_mul_trunc]
  have h₀ := d.h_n_m
  have h₁ := d.h_m_1
  obtain ⟨hk, h⟩ | ⟨hk, h⟩ :
      d.k = d.m ∧ d.m ≤ d.n - d.m ∨
      d.k = d.n - d.m ∧ d.n - d.m < d.m :=
    min_cases ..
  all_goals (simp_rw [hk, ← trunc_add, trunc_X_pow_eq_ite, trunc_X_eq_ite, trunc_one_eq_ite]; clear hk)
  . have : d.m ≠ d.n - d.m := by
      intro h
      absurd d.m_odd
      rw [h, Nat.not_odd_iff_even]
      apply d.n_odd.tsub_odd d.m_odd
    have :
      ¬       d.n < d.m + 1 ∧
      ¬   d.n - 1 < d.m + 1 ∧
      ¬ d.n - d.m < d.m + 1 ∧
              d.m < d.m + 1 ∧
                1 < d.m + 1 ∧
                0 < d.m + 1 := by omega
    simp only [reduceIte, this]
    simp_rw [zero_add, mul_one]
    simp only [← trunc_add, trunc_X_pow_eq_ite, trunc_X_eq_ite, trunc_one_eq_ite, reduceIte, this]
  . have :
      ¬       d.n < d.n - d.m + 1 ∧
      ¬   d.n - 1 < d.n - d.m + 1 ∧
      ¬       d.m < d.n - d.m + 1 ∧
        d.n - d.m < d.n - d.m + 1 ∧
                1 < d.n - d.m + 1 ∧
                0 < d.n - d.m + 1 := by omega
    simp only [reduceIte, this]
    simp_rw [zero_add, mul_add, mul_one, add_mul, one_mul, ← add_assoc, ← pow_succ']
    simp only [← trunc_add, trunc_X_pow_eq_ite, trunc_X_eq_ite, trunc_one_eq_ite, reduceIte, this,
      lt_self_iff_false, zero_add]



lemma main₁.aux
  (k : ℕ) (hk : k > 1)
  (f g : ℤ[X])
  (hf : ∀ i, 0 ≤ f.coeff i) (hg : ∀ i, 0 ≤ g.coeff i)
  (h : trunc (k + 1) (f * g) = ofFinsupp (.indicator {0, 1, k} fun _ _ => 1)) :
    ∃ ix ⊆ {1, k},
      trunc (k + 1) f = ofFinsupp (.indicator ({0} ∪ ix) fun _ _ => 1) ∧
      trunc (k + 1) g = ofFinsupp (.indicator ({0} ∪ {1, k} \ ix) fun _ _ => 1) := by
  -- first get f[0] = g[0] = 1
  have ⟨f_0, g_0⟩ : f.coeff 0 = 1 ∧ g.coeff 0 = 1 := by
    suffices f.coeff 0 * g.coeff 0 = 1 by
      rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at this
      apply this.resolve_right
      rintro ⟨h, _⟩
      linarith only [h, hf 0]
    rw [← mul_coeff_zero, ← trunc_coeff_eq_of_lt (k + 1) _ (by omega), h]
    simp
  have h_supp : support (trunc (k + 1) (f * g)) = {0, 1, k} := by
    rw [h]
    ext j
    clear * -; simp; tauto
  -- for each index j > 0, f[j] ≠ 0 or g[j] ≠ 0 would imply
  -- (f*g)[j] ≠ 0. so the only indices that can have anything are k, 1, 0
  have hj_neg : ∀ j < k + 1, j ∉ [0, 1, k] → f.coeff j = 0 ∧ g.coeff j = 0 := by
    intro j hj hj'
    replace hj' : j ∉ support (trunc (k + 1) (f * g)) := by
      simpa [h_supp] using hj'
    rw [mem_support_iff, ne_eq, not_not, trunc_coeff_eq_of_lt _ _ hj, coeff_mul,
      Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by nlinarith only [hf a.1, hg a.2])] at hj'
    constructor
    . specialize hj' (j, 0) (by simp); dsimp at hj'
      rwa [g_0, mul_one] at hj'
    . specialize hj' (0, j) (by simp); dsimp at hj'
      rwa [f_0, one_mul] at hj'
  -- above 0 the only possibilities are (0, 0), (1, 0), (0, 1)
  have hj_pos : ∀ j, j = 1 ∨ j = k → f.coeff j + g.coeff j ≤ 1 := by
    intro j hj
    have hj' : j < k + 1 := by
      clear * - hk hj; omega
    have : (trunc (k + 1) (f * g)).coeff j = 1 := by
      rw [h]
      clear * - hj; aesop
    rw [trunc_coeff_eq_of_lt _ _ hj', coeff_mul] at this
    replace this : ∑ x ∈ {(j, 0), (0, j)}, f.coeff x.1 * g.coeff x.2 ≤ 1 := by
      rw [← this]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      . simp [Finset.insert_subset_iff]
      . intro i _ _
        apply mul_nonneg <;> apply_assumption
    rw [Finset.sum_pair (fun h => absurd (congrArg (·.2) h) (by dsimp; rcases hj <;> linarith))] at this
    simpa [f_0, g_0]
  replace hj_pos : ∀ j, j = 1 ∨ j = k →
      (f.coeff j, g.coeff j) ≠ (0, 0) →
      (f.coeff j, g.coeff j) = (1, 0) ∨ (f.coeff j, g.coeff j) = (0, 1) := by
    peel hj_pos with j hj h
    clear * - h hf hg
    specialize hf j
    specialize hg j
    simp; omega
  -- wlog 1 gets (1, 0)
  wlog h1_eq : f.coeff 1 = 1 ∧ g.coeff 1 = 0 generalizing f g
  . -- 1 can't be (0, 0) because of (f*g)[1]
    have h1_nz : (f.coeff 1, g.coeff 1) ≠ (0, 0) := by
      rw [ne_eq, Prod.mk.injEq]
      rintro ⟨f_1, g_1⟩
      have : (f * g).coeff 1 = 1 := by
        rw [← trunc_coeff_eq_of_lt (k + 1) _ (i := 1) (by omega)]
        simp [h]
      simp [mul_coeff_one, f_1, g_1] at this
    replace h1_nz : (f.coeff 1, g.coeff 1) = (1, 0) ∨ (f.coeff 1, g.coeff 1) = (0, 1) := by
      clear * - hj_pos h1_nz
      specialize hj_pos 1 (.inl rfl)
      tauto
    specialize this g f hg hf
      (mul_comm f g ▸ h) g_0 f_0
      (mul_comm f g ▸ h_supp)
      (fun j hj hj' => hj_neg j hj hj' |>.symm)
      (fun j hj => by have := hj_pos j hj; clear * - this; simp at this ⊢; tauto)
      (by clear * - h1_nz h1_eq; aesop)
    rcases this with ⟨ix, hix, this⟩
    existsi {1, k} \ ix, by simp
    convert this.symm
    simpa using hix
  rcases h1_eq with ⟨f_1, g_1⟩
  -- now we know all coefficients less than k
  have f_lt_k j (hj : j < k) : f.coeff j = if j = 0 ∨ j = 1 then 1 else 0 := by
    split_ifs with h
    . rcases h with rfl | rfl <;> assumption
    . refine' hj_neg .. |>.1
      . omega
      . simp; omega
  have g_lt_k j (hj : j < k) : g.coeff j = if j = 0 then 1 else 0 := by
    split_ifs with h
    . rw [h, g_0]
    . by_cases h' : j = 1
      . rw [h', g_1]
      . refine' hj_neg .. |>.2
        . omega
        . simp; omega
  -- k can't be (0, 0) because expand (f*g)[k].
  have hk_nz : (f.coeff k, g.coeff k) ≠ (0, 0) := by
    rw [ne_eq, Prod.mk.injEq]
    rintro ⟨f_k, g_k⟩
    suffices (f * g).coeff k = 0 by
      rw [← trunc_coeff_eq_of_lt (k + 1) _ (i := k) (by omega)] at this
      simp [h] at this
    rw [coeff_mul, Finset.sum_eq_zero]
    simp only [Finset.mem_antidiagonal, mul_eq_zero, Prod.forall]
    intro a b hab
    by_cases hb : b = 0 ∨ b = k
    . rcases hb with rfl | rfl
      . left
        rw [add_zero] at hab
        rw [hab, f_k]
      . right
        rw [g_k]
    . right
      rw [g_lt_k b (by omega)]
      clear * - hb; simp; aesop
  replace hk_nz := hj_pos k (.inr rfl) hk_nz
  -- and now just finish up
  -- (this code sucks but if it works it works)
  -- TODO: edit
  rcases hk_nz with fg_k | fg_k <;>
      rw [Prod.mk.injEq] at fg_k <;>
      rcases fg_k with ⟨f_k, g_k⟩
  . existsi {1, k}, by simp
    constructor
    . ext i
      obtain hi | hi := lt_or_ge i (k + 1)
      . rw [trunc_coeff_eq_of_lt _ _ hi]
        obtain hi | rfl : i < k ∨ k = i := by clear * - hi; omega
        . rw [f_lt_k i hi]
          simp [hi.ne]
        . simp [f_k]
      . clear * - hi hk
        rw [trunc_coeff_eq_zero _ _ hi]
        simp; omega
    . ext i
      obtain hi | hi := lt_or_ge i (k + 1)
      . rw [trunc_coeff_eq_of_lt _ _ hi]
        obtain hi | rfl : i < k ∨ k = i := by clear * - hi; omega
        . rw [g_lt_k i hi]
          simp
        . simp [g_k, show ¬ k = 0 by omega]
      . clear * - hi hk
        rw [trunc_coeff_eq_zero _ _ hi]
        simp; omega
  . existsi {1}, by simp
    constructor
    . ext i
      obtain hi | hi := lt_or_ge i (k + 1)
      . rw [trunc_coeff_eq_of_lt _ _ hi]
        obtain hi | rfl : i < k ∨ k = i := by clear * - hi; omega
        . rw [f_lt_k i hi]
          simp
        . simp [f_k]; omega
      . clear * - hi hk
        rw [trunc_coeff_eq_zero _ _ hi]
        simp; omega
    . ext i
      obtain hi | hi := lt_or_ge i (k + 1)
      . rw [trunc_coeff_eq_of_lt _ _ hi]
        obtain hi | rfl : i < k ∨ k = i := by clear * - hi; omega
        . rw [g_lt_k i hi]
          simp; split_ifs <;> omega
        . simp; omega
      . clear * - hi hk
        rw [trunc_coeff_eq_zero _ _ hi]
        simp; omega



namespace main₁
  structure SymmFactor where
    q : ℤ[X]
    hq : d.p * d.p.mirror = q * q.mirror

  structure SymmFactor' extends SymmFactor d where
    q_eval_1_nn : 0 ≤ q.eval 1

  structure SymmFactor'' extends SymmFactor' d where
    hq' : ∃ a : ℕ, (a = d.m ∨ a = d.n - d.m) ∧ q = X ^ d.n + X ^ a + X + 1


  namespace SymmFactor
    variable {d} (s : SymmFactor d)

    lemma natDeg : s.q.natDegree = d.n := by
      have := congrArg natDegree s.hq
      simpa [natDegree_mul_mirror, d.p_natDeg] using this.symm

    lemma natTrailDeg : s.q.natTrailingDegree = 0 := by
      have := congrArg natTrailingDegree s.hq
      simpa [natTrailingDegree_mul_mirror, d.p_natTrailDeg] using this.symm

    lemma trunc_mul_mirror :
        trunc (d.k + 1) (s.q * s.q.mirror) = ofFinsupp (.indicator {0, 1, d.k} (fun _ _ => 1)) := by
      rw [← s.hq, p_mul_mirror_low]
      have nodup : [0, 1, d.k].Nodup :=
        List.Pairwise.nodup <| List.chain'_iff_pairwise.mp <|
          show List.Chain' (· < ·) _ by simp [d.one_lt_k]
      have toFinset : [0, 1, d.k].toFinset = {0, 1, d.k} := by
        simp
      convert_to ([0, 1, d.k].map (X ^ ·)).sum = (_ : ℤ[X])
      . simp; ring
      rw [← List.sum_toFinset _ nodup, sum_X_pow_finset_eq_ofFinsupp_indicator, toFinset]

    lemma sq_eval_1 : s.q.eval 1 ^ 2 = 4 ^ 2 := by
      suffices eval 1 (d.p * d.p.mirror) = 4 ^ 2 by
        rwa [s.hq, eval_mul, mirror_eval_one, ← pow_two] at this
      rw [eval_mul, mirror_eval_one, ← pow_two]
      simp [p]

    lemma sum_2 : s.q.sum (fun _ x => x ^ 2) = 4 := by
      rw [← s.q.coeff_mul_mirror, s.natDeg, s.natTrailDeg, ← s.hq,
        ← d.p_natDeg, ← d.p_natTrailDeg, d.p.coeff_mul_mirror]
      rw [p_eq']
      simp only [sum, coeff, Finsupp.indicator_apply]
      rw [support, Finsupp.support_indicator_of_ne_zero _ _ (fun _ _ => one_ne_zero)]
      simp only [dite_eq_ite, apply_ite (· ^ 2), one_pow, zero_pow two_ne_zero]
      rw [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_one]
      norm_cast
      rw [← d.p_ix_toFinset, List.toFinset_card_of_nodup d.p_ix_nodup]
      rfl

    lemma sq_eval_neg1 : s.q.eval (-1) ^ 2 = 4 := by
      let hn1 : Invertible (-1 : ℤ) := ⟨-1, by norm_num, by norm_num⟩
      suffices eval (-1) (d.p * d.p.mirror) = -4 by
        rw [s.hq, eval_mul, eval_mirror_eq, s.natDeg, s.natTrailDeg, add_zero,
          d.n_odd.neg_one_pow] at this
        simp only [hn1] at this
        linarith
      rw [eval_mul, eval_mirror_eq, d.p_natDeg, d.p_natTrailDeg, add_zero,
        d.n_odd.neg_one_pow]
      simp only [hn1]
      suffices eval (-1) d.p ^ 2 = 4 by linear_combination -this
      simp [p, d.n_odd.neg_one_pow, d.m_odd.neg_one_pow]

    theorem step : ∃ s' : SymmFactor' d, s.q = s'.q ∨ s.q = -s'.q :=
      if h : 0 ≤ s.q.eval 1 then
        ⟨{ s with q_eval_1_nn := h }, .inl rfl⟩
      else
        let s' : SymmFactor' d :=
          { q := -s.q,
            hq := by simp [mirror_neg, s.hq],
            q_eval_1_nn := by rw [eval_neg]; linarith }
        ⟨s', .inr (neg_eq_iff_eq_neg.mp rfl)⟩
  end SymmFactor


  namespace SymmFactor'
    variable {d} (s : SymmFactor' d)

    noncomputable def mirror : SymmFactor' d where
      q := s.q.mirror
      hq := by rw [mirror_mirror, mul_comm _ s.q, s.hq]
      q_eval_1_nn := s.q.mirror_eval_one ▸ s.q_eval_1_nn

    lemma sum_1 : s.q.sum (fun _ x => x) = 4 := by
      suffices s.q.eval 1 = 4 by simpa [eval_eq_sum]
      have := s.q_eval_1_nn
      have := eq_or_eq_neg_of_sq_eq_sq _ _ s.sq_eval_1
      omega

    lemma coeff_nn i : 0 ≤ s.q.coeff i := by
      have h₁ := s.sum_1
      have h₂ := s.sum_2
      by_cases h : ∃ k, s.q.coeff k ^ 2 > 1
      . rcases h with ⟨k, hk⟩
        replace hi : s.q.coeff k ^ 2 ≥ 4 := by
          rw [← Int.natAbs_sq] at hk ⊢
          norm_cast at hk ⊢
          rw [Nat.one_lt_pow_iff two_ne_zero] at hk
          erw [Nat.pow_le_pow_iff_left (a := 2) two_ne_zero]
          omega
        rw [sum_eq_of_subset _ (by simp) (s := insert k s.q.support) (by simp)] at h₁ h₂
        rw [← Finset.add_sum_erase _ _ (a := k) (by simp), Finset.erase_insert_eq_erase] at h₁ h₂
        replace h₂ : ∑ j ∈ s.q.support.erase k, s.q.coeff j ^ 2 = 0 := le_antisymm
          (by omega)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at h₂
        simp_rw [pow_eq_zero_iff two_ne_zero] at h₂
        rw [Finset.sum_eq_zero h₂, add_zero] at h₁
        by_cases hi : i = k
        . rw [hi, h₁]; omega
        . simp only [Finset.mem_erase, ne_eq, mem_support_iff, and_imp, not_imp_self] at h₂
          rw [h₂ i hi]
      . push_neg at h
        have h' : ∀ k ∈ s.q.support, s.q.coeff k ^ 2 = 1 := fun k hk => by
          specialize h k
          rw [mem_support_iff, ← pow_ne_zero_iff two_ne_zero] at hk
          have := sq_nonneg (s.q.coeff k); omega
        simp_rw [sum, Finset.sum_congr rfl h'] at h₂
        rw [sum, ← h₂] at h₁
        replace h k : s.q.coeff k ≤ 1 := by nlinarith only [h k]
        rw [Finset.sum_eq_sum_iff_of_le (fun k _ => h k)] at h₁
        by_cases hi : i ∈ s.q.support
        . simp [h₁ i hi]
        . clear * - hi; simp_all

    private theorem step_aux :
        ∃ q, (q = s.q ∨ q = s.q.mirror) ∧
          ∃ a : ℕ, (a = d.m ∨ a = d.n - d.m) ∧
            q = X ^ d.n + X ^ a + X + 1 := by
      have ⟨ix, hix, hq, hqm⟩ :=
        aux d.k d.one_lt_k
          s.q s.q.mirror
          s.coeff_nn (s.q.coeff_mirror · ▸ s.coeff_nn _)
          s.trunc_mul_mirror
      wlog hix' : 1 ∈ ix
      . specialize this s.mirror ({1, d.k} \ ix) (by simp)
          hqm
          (by convert hq <;> simp [mirror, mirror_mirror, hix])
          (by simp [hix'])
        simp only [mirror, mirror_mirror] at this
        convert this using 3
        tauto
      replace hq i (hi : i ∈ {0} ∪ ix) : s.q.coeff i = 1 := by
        apply congrArg (·.coeff i) at hq
        simp only [coeff_ofFinsupp, Finsupp.indicator_apply, hi, reduceDIte] at hq
        apply coeff_eq_of_trunc_coeff_eq_of_ne_zero hq one_ne_zero
      replace hqm i (hi : i ∈ {0} ∪ {1, d.k} \ ix) : s.q.mirror.coeff i = 1 := by
        apply congrArg (·.coeff i) at hqm
        simp only [coeff_ofFinsupp, Finsupp.indicator_apply, hi, reduceDIte] at hqm
        apply coeff_eq_of_trunc_coeff_eq_of_ne_zero hqm one_ne_zero
      simp_rw [coeff_mirror, s.natDeg, s.natTrailDeg, add_zero] at hqm
      existsi s.q, .inl rfl
      let a := if d.k ∈ ix then d.k else d.n - d.k
      have ha : a = d.m ∨ a = d.n - d.m := by
        dsimp [a, k]; have := d.h_n_m; split <;> omega
      have ⟨a_lo, a_hi⟩ : 1 < a ∧ a < d.n := by
        have := d.h_n_m
        have := d.h_m_1
        have := d.one_lt_n_sub_m
        omega
      existsi a, ha
      clear ha
      suffices ∀ i ∈ ({0, 1, a, d.n} : Finset _), s.q.coeff i = 1 by
        clear_value a
        clear * - a_lo a_hi this
        set ix : Finset ℕ := {0, 1, a, d.n}
        have nodup : [0, 1, a, d.n].Nodup :=
          List.Pairwise.nodup <| List.chain'_iff_pairwise.mp <|
            show List.Chain' (· < ·) _ by simp [a_lo, a_hi]
        have finset : [0, 1, a, d.n].toFinset = ix := by
          simp [ix]
        convert_to s.q = ([0, 1, a, d.n].map (X ^ ·)).sum
        . simp; ring
        rw [← List.sum_toFinset _ nodup, finset, sum_X_pow_finset_eq_ofFinsupp_indicator]
        have ix_card : ix.card = 4 :=
          finset ▸ List.toFinset_card_of_nodup nodup
        have ix_supp : ix ⊆ s.q.support := fun i hi =>
          Finsupp.mem_support_iff.mpr <| this i hi |>.trans_ne one_ne_zero
        have this' : ∀ i ∈ s.q.support \ ix, s.q.coeff i = 0 := by
          have h := s.sum_1
          rw [sum, ← Finset.sum_inter_add_sum_diff _ ix,
            Finset.inter_eq_right.mpr ix_supp, Finset.sum_congr rfl this] at h
          rw_mod_cast [← Finset.card_eq_sum_ones, ix_card] at h
          rw [← Finset.sum_eq_zero_iff_of_nonneg (fun i _ => s.coeff_nn i)]
          omega
        replace this' : ∀ i ∉ ix, s.q.coeff i = 0 := fun i hi =>
          if h : i ∈ s.q.support
            then this' i <| Finset.mem_sdiff.mpr ⟨h, hi⟩
            else notMem_support_iff.mp h
        clear nodup finset ix_card
        clear_value ix
        ext i; aesop
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      . apply hq; simp
      . apply hq; simp [hix']
      . unfold a
        split <;> rename_i h
        . apply hq; simp [h]
        . rw [← revAt_le d.k_le_n]
          apply hqm; simp [h]
      . rw [← revAt_zero d.n]
        apply hqm; simp

    theorem step : ∃ s' : SymmFactor'' d, s.q = s'.q ∨ s.q = s'.q.mirror := by
      rcases s.step_aux with ⟨q, rfl | rfl, h⟩
      . exact ⟨{ s with hq' := h }, .inl rfl⟩
      . exact ⟨{ s.mirror with hq' := h }, .inr (s.q.mirror_mirror ▸ rfl)⟩
  end SymmFactor'

  namespace SymmFactor''
    variable {d} (s : SymmFactor'' d)

    theorem tada : s.q = d.p := by
      obtain ⟨a, rfl | rfl, h⟩ := s.hq'
      . rw [h, p]
      absurd s.sq_eval_neg1
      rw [h]
      simp only [eval_add, eval_pow, eval_X, eval_one]
      rw [d.n_odd.neg_one_pow, (d.n_odd.tsub_odd d.m_odd).neg_one_pow]
      norm_num
  end SymmFactor''

end main₁


open main₁ in
theorem main₁
  (q : ℤ[X])
  (hq : d.p * d.p.mirror = q * q.mirror) :
    q = d.p ∨ q = -d.p ∨ q = d.p.mirror ∨ q = -d.p.mirror := by
  let s : SymmFactor d := { q, hq }
  rw [show q = s.q from rfl]
  clear_value s; clear q hq
  obtain ⟨s', hs⟩ := s.step
  obtain ⟨s'', hs'⟩ := s'.step
  have := s''.tada
  aesop


theorem main₂ : IsRelPrime d.p d.p.mirror := by
  apply d.p_primitive.isRelPrime_fraction_map_iff (K := ℚ)
  rw [isRelPrime_iff_isCoprime]
  apply IsCoprime.of_add_mul_left_right (z := -1)
  let { n, m, n_odd, m_odd, h_n_m, h_m_1 } := d
  rw [mirror_p_eq, p]
  dsimp only
  simp only [algebraMap_int_eq, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one]
  convert_to IsCoprime _ (X ^ (n - 1) + X ^ (n - m) - X ^ m - X : ℚ[X])
  . ring
  have h₀ : n - 1 = n - m - 1 + (m - 1) + 1 := by omega
  have h₁ : n - m = n - m - 1 + 1 := by omega
  have h₂ : m = m - 1 + 1 := by omega
  have m_1_even : Even (m - 1) :=
    m_odd.tsub_odd odd_one
  have n_m_1_odd : Odd (n - m - 1) :=
    Nat.Even.sub_odd (by omega) (n_odd.tsub_odd m_odd) (by simp)
  convert_to IsCoprime _
      (X ^ ((n - m - 1) + (m - 1) + 1) + X ^ ((n - m - 1) + 1)
        - X ^ (m - 1 + 1) - X : ℚ[X]) using 5
  convert_to IsCoprime _ ((X ^ (n - m - 1) - 1) * (X ^ (m - 1) + 1) * X : ℚ[X])
  . ring
  refine .mul_right (.mul_right ?_ ?_) ?_
  . apply IsCoprime.of_add_mul_left_left (z := - X ^ (m - 1 + 1 + 1))
    convert_to IsCoprime
        (X ^ n + X ^ m + X + 1
          - X ^ (n - m - 1 + (m - 1) + 1 + 1) + X ^ (m - 1 + 1 + 1) : ℚ[X]) _
    . ring
    convert_to ← IsCoprime (X ^ n + X ^ m + X + 1 - X ^ n + X ^ (m + 1) : ℚ[X]) _ using 5
    . omega
    convert_to IsCoprime ((X ^ m + 1) * (X + 1) : ℚ[X]) _
    . ring
    refine .mul_left ?_ ?_
    . rw [isCoprime_iff_aeval_ne_zero]
      intro A _ _ _ a
      have := algebraRat.charZero A
      simp only [map_add, map_pow, map_one, map_sub, aeval_X]
      by_contra! h; rcases h with ⟨hf, hg⟩
      rw [add_eq_zero_iff_eq_neg] at hf
      rw [sub_eq_zero] at hg
      suffices (a ^ m) ^ (n - m - 1) ≠ (a ^ (n - m - 1)) ^ m from absurd (pow_right_comm ..) this
      rw [hf, hg, n_m_1_odd.neg_one_pow, one_pow]
      norm_num
    . rw [isCoprime_iff_aeval_ne_zero]
      intro A _ _ _ a
      have := algebraRat.charZero A
      simp only [map_add, map_pow, map_one, map_sub, aeval_X]
      by_contra! h; rcases h with ⟨hf, hg⟩
      rw [add_eq_zero_iff_eq_neg] at hf
      absurd hg
      rw [hf, n_m_1_odd.neg_one_pow]
      norm_num
  . apply IsCoprime.of_add_mul_left_left (z := - X)
    convert_to IsCoprime (X ^ n + (X ^ m - X ^ (m - 1 + 1)) + 1 : ℚ[X]) _
    . ring
    rw [← h₂, sub_self, add_zero]
    rw [isCoprime_iff_aeval_ne_zero]
    intro A _ _ _ a
    have := algebraRat.charZero A
    simp only [map_add, map_pow, map_one, aeval_X]
    by_contra! h; rcases h with ⟨hf, hg⟩
    rw [add_eq_zero_iff_eq_neg] at hf hg
    suffices (a ^ n) ^ (m - 1) ≠ (a ^ (m - 1)) ^ n from absurd (pow_right_comm ..) this
    rw [hf, hg, m_1_even.neg_one_pow, n_odd.neg_one_pow]
    norm_num
  . apply IsCoprime.of_add_mul_left_left (z := - (X^(n-1) + X^(m-1) + 1))
    convert_to IsCoprime ((X ^ n - X ^ (n - 1 + 1)) + (X ^ m - X ^ (m - 1 + 1)) + 1 : ℚ[X]) _
    . ring
    convert_to IsCoprime ((X ^ n - X ^ n) + (X ^ m - X ^ m) + 1 : ℚ[X]) _ using 5
    . omega
    . omega
    simp_rw [sub_self, zero_add]
    apply isCoprime_one_left

end Data


theorem yay
  (n m : ℕ)
  (n_odd : Odd n) (m_odd : Odd m)
  (h_n_m : n > m) (h_m_1 : m > 1) :
    Irreducible (X ^ n + X ^ m + X + 1 : ℤ[X]) :=
  let d : Data := { n, m, n_odd, m_odd, h_n_m, h_m_1 }
  -- it bothers me that the hypothesis takes ± rather than Associated :( oh well
  irreducible_of_mirror (not_isUnit_of_natDegree_pos d.p d.p_natDeg_pos) d.main₁ d.main₂
