import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc
import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.Subfield
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.Norm

import Utils.Nat

/-!

# Radical extensions

Some facts about radical field extensions.

-/

-- FIXME:
-- Why isn't QuotientGroup.mk_pow (etc) a norm_cast lemma or whatever?

namespace Polynomial

-- TODO you can weaken the assumptions here (and below) right
theorem natDegree_pos_of_irreducible {F} [Field F] {f : F[X]} (hf : Irreducible f) :
    0 < natDegree f :=
  natDegree_pos_iff_degree_pos.mpr <| degree_pos_of_irreducible hf

end Polynomial

namespace Irreducible

-- 2:38

open Polynomial

theorem degree_pos {F} [Field F] {f : F[X]} (hf : Irreducible f) : 0 < degree f :=
  degree_pos_of_irreducible hf

theorem natDegree_pos {F} [Field F] {f : F[X]} (hf : Irreducible f) : 0 < natDegree f :=
  natDegree_pos_of_irreducible hf

end Irreducible

namespace IntermediateField

open Algebra FiniteDimensional

theorem AdjoinSimple.norm_gen_eq_coeff_zero_minpoly
  {F} {E} [Field F] [Field E] [Algebra F E] {α : E} (hα : IsIntegral F α) :
    norm F (gen F α) = (-1) ^ (minpoly F α).natDegree * (minpoly F α).coeff 0 := by
  convert PowerBasis.norm_gen_eq_coeff_zero_minpoly <| adjoin.powerBasis hα
  simp [minpoly_gen hα]

-- TODO kill a finitude assumption on FiniteDimensional.finrank_mul_finrank

-- TODO you can get rid of the integrality assumption, I think.
-- also, there are a bunch of places where integrality is assumed
-- but isn't necessary throughout mathlib. (at least if you're over a field, I think?)
theorem minpoly.degree_dvd {F} {E} [Field F] [Field E] [Algebra F E] {α : E} (hα : IsIntegral F α) :
    (minpoly F α).natDegree ∣ finrank F E := by
  haveI := adjoin.finiteDimensional hα
  rw [← adjoin.finrank hα, ← finrank_mul_finrank F F⟮α⟯ E]
  apply dvd_mul_right

end IntermediateField

namespace RadicalExt


open scoped algebraMap
open Algebra Polynomial IntermediateField AdjoinSimple FiniteDimensional

variable {F} [Field F]


section

variable {f : F[X]}

-- start time: 1:10 or so
lemma irreducible_of_degree_irreducible_factor
  {g : F[X]} (hg : Irreducible g) (g_dvd : g ∣ f) (hf : natDegree f ∣ natDegree g) :
    Irreducible f := by
  rcases g_dvd with ⟨h, rfl⟩
  suffices IsUnit h from irreducible_mul_isUnit this |>.mpr hg
  have deg_g := natDegree_pos_of_irreducible hg
  have h_nz : h ≠ 0 := by
    suffices g * h ≠ 0 from this ∘ mul_eq_zero.mpr ∘ .inr
    suffices natDegree (g * h) ≠ 0 by contrapose! this; simp [this]
    exact ne_zero_of_dvd_ne_zero deg_g.ne' hf
  replace hf := Nat.le_of_dvd deg_g hf
  rw [natDegree_mul hg.ne_zero h_nz, add_le_iff_nonpos_right] at hf
  rw [isUnit_iff_degree_eq_zero]
  apply le_antisymm
  . exact natDegree_eq_zero_iff_degree_le_zero.mp <| nonpos_iff_eq_zero.mp hf
  . exact zero_le_degree_iff.mpr h_nz


lemma irreducible_of_degree_root
  (hf : 0 < natDegree f)
  (h : ∀ {g} {g_dvd : g ∣ f} [Fact (Irreducible g)],
      let E := AdjoinRoot g
      let α := AdjoinRoot.root g
      let hα : AdjoinRoot.mk g f = 0 := AdjoinRoot.mk_eq_zero.mpr g_dvd
      natDegree f ∣ finrank F E) :
    Irreducible f := by
  let g := factor f
  haveI hg : Fact (Irreducible g) := ⟨irreducible_factor f⟩
  have g_dvd : g ∣ f := factor_dvd_of_natDegree_ne_zero hf.ne'
  apply irreducible_of_degree_irreducible_factor (g := g) hg.1 g_dvd
  rw [← AdjoinRoot.powerBasis_dim hg.1.ne_zero, ← PowerBasis.finrank]
  apply h; assumption


end



lemma degree_pos_of_irreducible_radical {n : ℕ} {r : F} (hf : Irreducible (X ^ n - C r)) : 0 < n := by
  obtain rfl | n_pos := n.eq_zero_or_pos
  . exfalso; apply not_irreducible_C (1 - r); simpa
  . exact n_pos

lemma monic_of_irreducible_radical {n : ℕ} {r : F} (hf : Irreducible (X ^ n - C r)) : Monic (X ^ n - C r) :=
  monic_X_pow_sub_C _ (degree_pos_of_irreducible_radical hf).ne'

lemma minpoly_of_irreducible_radical {E} [Field E] [Algebra F E] {n : ℕ} {r : F}
  (hf : Irreducible (X ^ n - C r)) {α : E} (hα : α ^ n = r) :
    minpoly F α = X ^ n - C r :=
  symm <| minpoly.eq_of_irreducible_of_monic hf (by simp [hα, Algebra.cast]) <|
    monic_X_pow_sub_C _ (degree_pos_of_irreducible_radical hf).ne'

lemma norm_of_irreducible_radical' {E} [Field E] [Algebra F E] {n : ℕ} {r : F}
  (hf : Irreducible (X ^ n - C r)) {α : E} (hα : α ^ n = r) :
    norm F (gen F α) = (-1) ^ n * -r := by
  have n_pos := degree_pos_of_irreducible_radical hf
  rw [norm_gen_eq_coeff_zero_minpoly, minpoly_of_irreducible_radical hf hα]
  . simp [natDegree_X_pow_sub_C, coeff_X_pow n 0, n_pos.ne]
  . exact isIntegral_of_pow n_pos (hα ▸ isIntegral_algebraMap)


-- start: like 3:05
-- back for more: 18:51
-- done: 20:28
theorem irreducible_radical_of_degree_prime {p : ℕ} (hp : p.Prime) {r : F} :
    Irreducible (X ^ p - C r) ↔ ¬ ∃ a : F, a ^ p = r := by
  have h_deg' : natDegree (X ^ p - C r) = p := natDegree_X_pow_sub_C ..

  constructor
  . rintro h ⟨a, ha⟩
    -- TODO clean this up slightly
    suffices degree (X ^ p - C r) = 1 from hp.ne_one <| by
      rw [degree_X_pow_sub_C hp.pos _] at this
      norm_cast at this
    apply degree_eq_one_of_irreducible_of_root h (x := a)
    simp [ha]

  intro hr
  apply irreducible_of_degree_root (h_deg'.substr hp.pos)
  intro g g_dvd hg E α hα
  replace hα : α ^ p = r := sub_eq_zero.mp hα
  rw [h_deg']

  obtain ⟨c, hc⟩ : ∃ c : F, c ^ p = r ^ finrank F E
  . use norm F α; rw [← map_pow, hα, ← Algebra.norm_algebraMap]; rfl
  contrapose! hr
  rw [← hp.coprime_iff_not_dvd] at hr

  obtain rfl | r_nz := eq_or_ne r 0
  . use 0; exact zero_pow_eq_zero.mpr hp.pos
  -- TODO phrase this in terms of subgroup membership rather than the quotient
  -- that is, these two things are in (powMonoidHom p).range,
  -- and x^n, x^m in a subgroup implies x^gcd n m in the subgroup
  let Q := Fˣ ⧸ (powMonoidHom p).range
  let r' : Fˣ := .mk0 r r_nz
  suffices : (r' : Q) = 1
  . rw [QuotientGroup.eq_one_iff, MonoidHom.mem_range] at this
    rcases this with ⟨x, hx⟩
    rw [powMonoidHom_apply] at hx
    use x; rw_mod_cast [hx]; rfl

  rw [← pow_one (r' : Q), ← hr.gcd_eq_one]
  apply pow_gcd_eq_one <;> rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_range]
  . use r'; rfl
  . use .mk0 c (ne_zero_pow hp.ne_zero <| hc.substr <| pow_ne_zero _ r_nz)
    rw [powMonoidHom_apply]
    ext; push_cast; exact hc


section irreducible_radical_step

variable {E} [Field E] [Algebra F E]

lemma irreducible_radical_step_of_degree_odd_prime {p : ℕ} (hp : p.Prime) {r : F}
  (p_odd : Odd p) (hr : ¬ ∃ a : F, a ^ p = r) {α : E} (hα : α ^ p = r) :
    ¬ ∃ μ : F⟮α⟯, μ ^ p = gen F α := by
  have hf : Irreducible (X ^ p - C r) := by rw [irreducible_radical_of_degree_prime]; assumption'
  
  contrapose! hr with hμ
  rcases hμ with ⟨μ, hμ⟩

  use norm F μ
  rw [← map_pow, hμ, norm_of_irreducible_radical' hf hα, p_odd.neg_one_pow]
  simp


variable {r : F} (hr : ¬ ∃ a : F, a ^ 2 = r) (hr' : ¬ ∃ a : F, -4 * a ^ 4 = r) {α : E} (hα : α ^ 2 = r)

-- 01:20 taking a break
-- (also i feel like i've been on this particular lemma for literally ages)
-- new start time 7:07
private lemma irreducible_radical_step_of_degree_two_aux : ¬ ∃ μ : F⟮α⟯, μ ^ 2 = gen F α := by
  -- TODO factor this out
  have hp : Nat.Prime 2 := by norm_num
  have hf : Irreducible (X ^ 2 - C r) := by rw [irreducible_radical_of_degree_prime]; assumption'

  contrapose! hr' with hμ
  rcases hμ with ⟨μ, hμ⟩

  -- TODO kill this when you end up showing X^2 - r is irreducible anyway
  have α_i : IsIntegral F α := isIntegral_of_pow hp.pos (hα ▸ isIntegral_algebraMap)
  let pb := adjoin.powerBasis α_i
  have hd : pb.dim = 2
  . rw [adjoin.powerBasis_dim α_i, minpoly_of_irreducible_radical hf hα, natDegree_X_pow_sub_C]
  replace hα : gen F α ^ 2 = r := by ext; exact hα
  
  obtain ⟨f, f_deg, hf⟩ := pb.exists_eq_aeval μ
  obtain ⟨x, y, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one <|
    Nat.le_pred_of_lt <| f_deg.trans_eq hd
  obtain rfl : μ = x * gen F α + y
  . simp only [aeval_add, aeval_mul, aeval_X, aeval_C] at hf
    exact hf
  replace hμ : (2 * x * y : F) * pb.gen + (r * x ^ 2 + y ^ 2 : F) * 1 = pb.gen
  . rw [Algebra.cast]; simp; rw [← Algebra.cast, ← hα]
    convert hμ using 1; ring
  
  rcases pb with ⟨α', d, B, hB⟩; subst hd; dsimp only at *
  replace hμ := congrArg (Finsupp.equivFunOnFinite ∘ B.repr) hμ
  replace hμ : ![r * x ^ 2 + y ^ 2, 2 * x * y] = ![0, 1]
  . simp_rw [Algebra.cast, ← smul_def, Function.comp_apply, map_add, map_smul,
      (show 1 = B 0 by simp [hB 0]), (show α' = B 1 by simp [hB 1]), B.repr_self] at hμ
    convert hμ using 2 <;> ext i <;> fin_cases i <;> simp
  obtain ⟨hμ1, hμ2⟩ : r * x ^ 2 + y ^ 2 = 0 ∧ 2 * x * y = 1
  . simpa [Matrix.vecCons] using hμ

  use y
  rw [← neg_add_eq_zero]
  calc
    _ = r * 1 ^ 2 + 4 * y ^ 4           := by ring
    _ = r * (2 * x * y) ^ 2 + _         := by rw [← hμ2]
    _ = 4 * y ^ 2 * (r * x ^ 2 + y ^ 2) := by ring
    _ = 0                               := by rw [hμ1, mul_zero]
  

private lemma irreducible_radical_step_of_degree_two :
    (¬ ∃ μ : F⟮α⟯, μ ^ 2 = gen F α) ∧ (¬ ∃ μ : F⟮α⟯, -4 * μ ^ 4 = gen F α) := by
  constructor
  . apply irreducible_radical_step_of_degree_two_aux; assumption'
  suffices : ¬ ∃ μ : F⟮-α⟯, μ ^ 2 = gen F (-α)
  . rintro ⟨⟨μ, μ_mem⟩, hμ⟩
    replace hμ : -4 * μ ^ 4 = α
    . simpa using congrArg Subtype.val hμ
    let μ' : F⟮-α⟯ := ⟨μ, ?_⟩
    . exact this ⟨2 * μ' ^ 2, Subtype.ext <| show _ = -α by
        simp_rw [← hμ, ← algebraMap.coe_pow]; ring_nf; norm_cast⟩
    suffices F⟮α⟯ ≤ F⟮-α⟯ from this μ_mem
    rw [adjoin_simple_le_iff, ← neg_mem_iff (x := α)]
    apply mem_adjoin_simple_self
  rw [← neg_sq] at hα
  apply irreducible_radical_step_of_degree_two_aux; assumption'

end irreducible_radical_step



variable {r : F}

theorem not_irreducible_radical_of_degree_four (hr' : ∃ a : F, -4 * a^4 = r) :
    ¬ Irreducible (X ^ 4 - C r) := by
  rcases hr' with ⟨a, rfl⟩
  intro h
  replace h := h.isUnit_or_isUnit'
    (C 1 * X ^ 2 + C (2 * a) * X + C (2 * a ^ 2))
    (C 1 * X ^ 2 + C (-2 * a) * X + C (2 * a ^ 2))
    (by simp; ring)
  cases h with | inl h | inr h =>
    have := degree_eq_zero_of_isUnit h
    rw [degree_quadratic one_ne_zero] at this
    cases this

-- TODO so which way around are m and n meant to go again idk
theorem irreducible_radical_of_dvd {n m : ℕ} (m_dvd : m ∣ n)
  (h : Irreducible (X ^ n - C r)) :
    Irreducible (X ^ m - C r) := by
  rcases m_dvd with ⟨k, rfl⟩
  have k_nz : k ≠ 0 := (degree_pos_of_irreducible_radical h |>.ne' <| · ▸ mul_zero m)
  suffices X ^ (m * k) - C r = expand _ k (X ^ m - C r) from
    of_irreducible_expand k_nz <| this ▸ h
  simp [pow_mul']


theorem irreducible_radical_of_coprime {m n : ℕ} (h : m.coprime n)
  (hm : Irreducible (X ^ m - C r)) (hn : Irreducible (X ^ n - C r)) :
    Irreducible (X ^ (m * n) - C r) := by
  have m_pos := degree_pos_of_irreducible_radical hm
  have n_pos := degree_pos_of_irreducible_radical hn

  apply irreducible_of_degree_root <;> rw [natDegree_X_pow_sub_C]
  . exact mul_pos m_pos n_pos
  intro g g_dvd hg E α hα
  replace hα : α ^ (m * n) = r := sub_eq_zero.mp hα
  -- TODO isn't there a more "automatic" way of doing this,
  -- since this is a field extension of finite type?
  have α_i : IsIntegral F α := AdjoinRoot.isIntegral_root hg.1.ne_zero

  -- TODO it's a bit silly to have to do this by hand isn't it
  -- one way to get rid of this is to kill a finiteness assumption
  -- on finrank_mul_finrank (assuming that's legit which it totally is isn't it)
  haveI : FiniteDimensional F F⟮α ^ n⟯ := adjoin.finiteDimensional (α_i.pow _)
  haveI : FiniteDimensional F F⟮α ^ m⟯ := adjoin.finiteDimensional (α_i.pow _)

  apply h.mul_dvd_of_dvd_of_dvd
  . suffices : finrank F F⟮α ^ n⟯ = m
    . rw [← this]
      use finrank F⟮α ^ n⟯ E
      exact symm <| finrank_mul_finrank F _ E
    rw [adjoin.finrank (α_i.pow _), minpoly_of_irreducible_radical hm, natDegree_X_pow_sub_C]
    rw [← pow_mul', hα]
  . suffices : finrank F F⟮α ^ m⟯ = n
    . rw [← this]
      use finrank F⟮α ^ m⟯ E
      exact symm <| finrank_mul_finrank F _ E
    rw [adjoin.finrank (α_i.pow _), minpoly_of_irreducible_radical hn, natDegree_X_pow_sub_C]
    rw [← pow_mul, hα]
  

theorem irreducible_radical_iff {n : ℕ} (hn : 0 < n) :
    Irreducible (X ^ n - C r) ↔
      (∀ p ∈ n.factors, ¬ ∃ a : F, a ^ p = r) ∧
      (4 ∣ n → ¬ ∃ a : F, -4 * a ^ 4 = r) := by
  constructor
  . exact fun hf =>
      ⟨fun q hq => have ⟨qp, hq⟩ := Nat.mem_factors hn.ne' |>.mp hq
        irreducible_radical_of_degree_prime qp |>.mp <| irreducible_radical_of_dvd hq hf,
      fun h4 h =>
        not_irreducible_radical_of_degree_four h <| irreducible_radical_of_dvd h4 hf⟩

  induction n using induction_on_prime_powers generalizing F with
  | h₀ => cases hn
  | h₁ => rintro -; simp [irreducible_X_sub_C]
  | @hcp m n hmn ihm ihn =>
    have m_pos := pos_of_mul_pos_left hn zero_le'
    have n_pos := pos_of_mul_pos_right hn zero_le'

    rintro ⟨hq, h4⟩
    apply irreducible_radical_of_coprime hmn
    . exact ihm m_pos
        ⟨fun p hp => hq p <| Nat.mem_factors_mul_left hp n_pos.ne',
        fun h => h4 <| dvd_mul_of_dvd_left h _⟩   
    . exact ihn n_pos
        ⟨fun p hp => hq p <| Nat.mem_factors_mul_right hp m_pos.ne',
        fun h => h4 <| dvd_mul_of_dvd_right h _⟩
  | @hps p k hp ih =>
    rintro ⟨hq, h4⟩
    replace hq : ¬ ∃ a : F, a ^ p = r
    . simp_rw [hp.factors_pow, List.mem_replicate] at hq
      simpa using hq

    apply irreducible_of_degree_root <;> rw [natDegree_X_pow_sub_C]
    . simp [hp.pos]
    intro g g_dvd hg E α hα
    replace hα : α ^ p ^ (k + 1) = r := sub_eq_zero.mp hα
    
    have α_i : IsIntegral F α := AdjoinRoot.isIntegral_root hg.1.ne_zero
    haveI : FiniteDimensional F F⟮α ^ p ^ k⟯ := adjoin.finiteDimensional (α_i.pow _)
    rw [← finrank_mul_finrank F F⟮α ^ p ^ k⟯ E, pow_succ]
    apply mul_dvd_mul
    . suffices hf : Irreducible (X ^ p - C r)
      . rw [adjoin.finrank (α_i.pow _), minpoly_of_irreducible_radical hf, natDegree_X_pow_sub_C]
        rw [← hα]; ring -- rw [← pow_mul, ← pow_succ', hα]
      rwa [irreducible_radical_of_degree_prime hp]
    . cases k with | zero => simp | succ k =>
      dsimp only [Nat.succ_eq_add_one] at *

      let F' := F⟮α ^ p ^ (k + 1)⟯
      suffices hf : Irreducible (X ^ p ^ (k + 1) - C (gen F _) : F'[X])
      . convert minpoly.degree_dvd <| isIntegral_of_isScalarTower (A := F') α_i
        rw [minpoly_of_irreducible_radical hf, natDegree_X_pow_sub_C]
        rfl
      apply ih
      . simp [hp.pos]
      suffices : (¬ ∃ a : F', a ^ p = gen F _) ∧ _
      . simp_rw [hp.factors_pow, List.mem_replicate]
        -- TODO would love to "simpa" this but i guess it's too complex
        simp only [ne_eq, add_eq_zero, and_false, not_false_eq_true, true_and, forall_eq]
        exact this
      have α_p : (α ^ p ^ (k + 1)) ^ p = r
      . rw [← hα]; ring -- rw [← pow_mul, ← pow_succ', hα]
      obtain rfl | p_odd := hp.eq_two_or_odd'
      . suffices _ ∧ _ from ⟨this.1, fun _ => this.2⟩
        replace h4 := h4 ⟨2 ^ k, by ring⟩
        apply irreducible_radical_step_of_degree_two; assumption'
      . constructor
        . apply irreducible_radical_step_of_degree_odd_prime; assumption'
        . exact fun h => absurd (show 2 ∣ 4 by norm_num |>.trans h) p_odd.pow.not_two_dvd_nat
        
        

end RadicalExt