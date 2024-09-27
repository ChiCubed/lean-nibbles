import algebra.group.basic
import algebra.category.Group.basic
import algebra.category.Module.basic

import group_theory.specific_groups.quaternion
import group_theory.order_of_element

-- FIXME make this a git repo :  :
-- FIXME fintype instances for zpowers via the equivalence
-- (zmultiples as well, probably, why not i guess).

-- FIXME is this import necessary?
import group_theory.submonoid.centralizer

import group_theory.noncomm_pi_coprod
import group_theory.torsion

-- import data.set.pointwise

import group_theory.commutator

import ring_theory.multiplicity

import data.nat.choose.basic

import data.zmod.basic

open subgroup


section group_exp

open subgroup add_subgroup

variables {G : Type*} (x : G)
variables {n : ℕ}

noncomputable def add_group_exp [add_group G] (h : add_order_of x = n) :
  zmod n ≃+ zmultiples x :=
add_equiv.of_bijective
  (zmod.lift n ⟨(zmultiples_hom _ x).range_restrict,
    begin
      change (⟨↑n • x, _, rfl⟩ : zmultiples x) = 0,
      simp_rw [← h, coe_nat_zsmul, add_order_of_nsmul_eq_zero],
      refl,
    end⟩)
  ⟨begin
    rw injective_iff_map_eq_zero,
    intros a ha,
    rw subtype.ext_iff at ha,
    change ↑a • x = 0 at ha,
    rw [← add_order_of_dvd_iff_zsmul_eq_zero, h] at ha,
    rw [← zmod.int_cast_zmod_cast a, zmod.int_coe_zmod_eq_zero_iff_dvd],
    exact ha
  end,
  by { rintro ⟨a, i, rfl⟩, exact ⟨i, (zmod.lift_coe _ _ _).subst rfl⟩ }⟩

noncomputable def group_exp [group G] (h : order_of x = n) :
  multiplicative (zmod n) ≃* zpowers x :=
add_equiv.to_multiplicative'' $
(add_group_exp (additive.of_mul x) ((add_order_of_of_mul_eq_order_of x).trans h)).trans $
show zmultiples (additive.of_mul x) ≃+ additive (zpowers x), from add_equiv.refl _

-- FIXME is this something you want?

@[simp] lemma add_group_exp_apply [add_group G] (h : add_order_of x = n) (i : zmod n) :
  ↑(add_group_exp x h (multiplicative.of_add i)) = (i : ℤ) • x :=
rfl

@[simp] lemma group_exp_apply [group G] (h : order_of x = n) (i : zmod n) :
  ↑(group_exp x h (multiplicative.of_add i)) = x ^ (i : ℤ) :=
rfl

end group_exp

-- FIXME location for these lemmas too
namespace quaternion_group

variable {n : ℕ}

-- FIXME are these desirable?
-- (probably in stdlib, at least)
@[simp] lemma a_inv (i : zmod (2 * n)) : (a i)⁻¹ = a (-i) := rfl
@[simp] lemma xa_inv (i : zmod (2 * n)) : (xa i)⁻¹ = xa (n + i) := rfl

end quaternion_group


section quaternion_hom

private abbreviation Q₈ := quaternion_group 2

-- FIXME what the hell did you do? everything works nicely now

parameters {G : Type*} [group G]
  (i j : G) (o : order_of ⁅i, j⁆ = 2)
  (oi : order_of i = 4) (hi : ⁅i, j⁆ = i ^ 2)
  (oj : order_of j = 4) (hj : ⁅i, j⁆ = j ^ 2)

-- FIXME oi, oj are deducible from hi, hj.
-- FIXME FIXME FIXME!!!!

-- FIXME make this better.....

-- FIXME FIXME FIXME FIXME FIXME FIXME FIXME
-- oi, oj don't really seem to get used very much at all, lol

@[reducible]
noncomputable def exp_i := group_exp i oi

noncomputable def quaternion_fun (x : Q₈) : G :=
match x with
| quaternion_group.a  k := exp_i (multiplicative.of_add k)
| quaternion_group.xa k := j * exp_i (multiplicative.of_add k)
end

include i j oi hi oj hj

lemma comm_j_one : j = i * j * i :=
begin
  rw [← mul_inv_eq_one, ← mul_left_inj i, ← mul_right_inj i],
  convert hi using 1; group,
end

lemma comm_j_nat : ∀ (n : ℕ), j = i ^ n * j * i ^ n
| 0     := by simp
| (n+1) :=
begin
  convert_to j = (i * i ^ n) * j * (i ^ n * i), rw [← pow_succ, ← pow_succ'],
  convert_to j = i * (i ^ n * j * i ^ n) * i, simp [mul_assoc],
  rw [← comm_j_nat n],
  exact comm_j_one,
end

lemma comm_j : ∀ (n : ℤ), j = i ^ n * j * i ^ n
| (n : ℕ) := by exact_mod_cast comm_j_nat n
| -[1+ n] :=
begin
  rw [← mul_left_inj (i ^ (n+1)), ← mul_right_inj (i ^ (n+1))],
  convert_to i ^ (n + 1) * j * i ^ (n + 1) = j,
  { rw mul_assoc }, { simp },
  exact_mod_cast (comm_j_nat (n + 1)).symm,
end

-- FIXME phrase stuff in terms of semiconj_by?
-- FIXME FIXME FIXME that makes this proof a lot cleaner, i think.
-- FIXME same for the earlier stuff.
noncomputable def quaternion_hom : Q₈ →* G :=
monoid_hom.mk' quaternion_fun
begin
  rintros (a | a) (b | b); simp only [quaternion_group.a_mul_a, quaternion_group.a_mul_xa,
    quaternion_group.xa_mul_a, quaternion_group.xa_mul_xa, quaternion_fun],
  { rw [of_add_add, map_mul, coe_mul] },
  { simp_rw [sub_eq_neg_add, of_add_add, of_add_neg,
      map_mul, map_inv, coe_mul, coe_inv, group_exp_apply],
    rw ← mul_right_inj (i ^ (-a : ℤ)),
    simp_rw [← mul_assoc, mul_left_inj],
    convert (comm_j (-a : ℤ)).symm; simp },
  { rw [of_add_add, map_mul, mul_assoc, coe_mul] },
  { simp_rw [sub_eq_neg_add, of_add_add, of_add_neg,
      map_mul, map_inv, coe_mul, coe_inv, group_exp_apply],
    rw ← mul_right_inj (i ^ (a : ℤ)),
    rw (show (((2 : ℕ) : zmod (2 * 2)) : ℤ) = ↑(2 : ℕ), by norm_num),
    simp_rw [← mul_assoc],
    rw [mul_inv_self, one_mul, zpow_coe_nat, ← hi, hj, pow_two, mul_left_inj, mul_left_inj],
    exact comm_j _, },
end

-- FIXME automation for these lemmas?
lemma quaternion_hom_a (a : zmod 4) :
  quaternion_hom (quaternion_group.a a) = exp_i (multiplicative.of_add a) :=
rfl

lemma quaternion_hom_xa (a : zmod 4) :
  quaternion_hom (quaternion_group.xa a) = j * exp_i (multiplicative.of_add a) :=
rfl

lemma quaternion_hom_injective : function.injective quaternion_hom :=
(injective_iff_map_eq_one _).mpr
begin
  rintro (a | a),
  { intro h,
    rw [quaternion_hom_a, one_mem_class.coe_eq_one, mul_equiv.map_eq_one_iff, of_add_eq_one] at h,
    rw h, refl },
  { intro h,
    rw [quaternion_hom_xa, group_exp_apply] at h,
    have h' := congr_arg (λ x, i ^ (a : ℤ) * x) h,
    dsimp only at h',
    rw [← mul_assoc, ← comm_j (a : ℤ), mul_one] at h',
    rw [← h', ← pow_two] at h,
    exact absurd h (pow_ne_one_of_lt_order_of' (by norm_num) (by norm_num [oj])) },
end

omit oi oj hi hj

end quaternion_hom






namespace tactic.interactive

open tactic interactive

setup_tactic_parser

meta def transport_group (eqv : parse texpr) (l : parse location) : tactic unit :=
do ns ← l.get_locals,
   replace_at norm_cast.derive ns l.include_goal,
   -- TODO can you give this a reasonable pos? instead of ⟨0, 0⟩?
   simp_rw ⟨[⟨⟨0, 0⟩, tt, ``((%%eqv).injective.eq_iff)⟩], none⟩ l,
   simp none none tt ([
    ``(map_one), ``(map_mul), ``(map_mul_inv), ``(map_inv), ``(map_pow), ``(map_zpow),
    ``(mul_equiv.apply_symm_apply), ``(mul_equiv.symm_apply_apply)
   ].map simp_arg_type.expr) [] l,
   -- FIXME is this behaviour actually desirable?
   norm_fin [],
   when l.include_goal $ try exact_dec_trivial

end tactic.interactive



-- FIXME location for these lemmas
lemma is_of_fin_order_pow {G : Type*} [group G] {x : G} (hx : is_of_fin_order x) :
  ∀ (n : ℕ), is_of_fin_order (x^n)
| 0     := (pow_zero _).substr is_of_fin_order_one
| (n+1) :=
(pow_succ _ _).substr $ (commute.self_pow _ _).is_of_fin_order_mul hx (is_of_fin_order_pow _)

theorem order_of_zpow' {G : Type*} [group G] (x : G) {n : ℤ} (h : n ≠ 0) :
  order_of (x ^ n) = order_of x / (order_of x : ℤ).gcd n :=
begin
  cases n.nat_abs_eq with hs hs; rw [hs, int.gcd],
  work_on_goal 2 { rw [zpow_neg, order_of_inv, int.nat_abs_neg] },
  all_goals { exact_mod_cast order_of_pow' _ (int.nat_abs_ne_zero_of_ne_zero h) },
end

-- FIXME use this lemma in more places
-- FIXME FIXME FIXME FIXME FIXME FIXME FIXME this one is important ig
theorem order_of_zpow'' {G : Type*} [group G] (x : G) (n : ℤ) (h : is_of_fin_order x) :
  order_of (x ^ n) = order_of x / (order_of x : ℤ).gcd n :=
begin
  by_cases hn : n = 0,
  { rw [hn, zpow_zero, order_of_one, int.gcd_zero_right],
    exact_mod_cast (nat.div_self $ order_of_pos' h).symm },
  exact order_of_zpow' x hn,
end

theorem exists_zpow_eq_self_of_coprime {G : Type*} [group G] {x : G} {n : ℤ}
    (h : is_coprime n ↑(order_of x)) :
  ∃ (m : ℤ), (x ^ n) ^ m = x :=
begin
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    (by { simpa [int.coprime_iff_nat_coprime, -is_coprime] using h }),
  cases n.nat_abs_eq with hs hs; rw hs,
  { use m, simpa using hm }, { use -m, simpa using hm },
end

theorem commutator_element_mul_right {G : Type*} [group G] (g₁ g₂ g₃ : G) :
  ⁅g₁, g₂ * g₃⁆ = ⁅g₁, g₂⁆ * (g₂ * ⁅g₁, g₃⁆ * g₂⁻¹) :=
begin
  simp_rw commutator_element_def,
  group,
end





-- FIXME appropriate namespacing

def group.is_hamiltonian (G : Type*) [group G] :=
(∀ S : subgroup G, S.normal) ∧ ¬ (∀ a b : G, commute a b)

namespace hamiltonian

abbreviation Q₈ := quaternion_group 2


-- FIXME
-- group_theory.order_of_element has sooo many problems:
-- decidability assumptions
-- finiteness assumptions on fin equiv zpowers
-- etcetera, etcetera.

-- FIXME local attribute simp on lemmata?


section structure_theorem

parameters {G : Type*} [group G] [hG : fact (group.is_hamiltonian G)]
include hG

instance subgroups_normal : Π S : subgroup G, S.normal :=
hG.out.1


section commutator_lemmas

variables (x y : G)

-- FIXME duplicate argument here
-- FIXME use semiconj_by machinery?

lemma conj_is_zpow :
  ∃ n : ℤ, y * x * y⁻¹ = x^n :=
Exists.imp (λ n, eq.symm) begin
  rw ← mem_closure_singleton,
  refine (hG.out.1 _).conj_mem _ _ _,
  simp [mem_closure],
end

lemma comm_in_zpowers_left :
  ⁅x, y⁆ ∈ zpowers x :=
begin
  convert_to x * (y * x⁻¹ * y⁻¹) ∈ _, { group },
  refine subgroup.mul_mem _ _ ((hG.out.1 _).conj_mem _ _ _); simp [mem_closure],
end

lemma comm_in_zpowers_right : ⁅x, y⁆ ∈ zpowers y :=
begin
  rw [← inv_mem_iff, commutator_element_inv],
  apply comm_in_zpowers_left,
end

lemma comm_is_zpow_left : ∃ n : ℤ, ⁅x, y⁆ = x^n :=
Exists.imp (λ n, eq.symm) $ mem_zpowers_iff.mp $ comm_in_zpowers_left x y

lemma comm_is_zpow_right : ∃ n : ℤ, ⁅x, y⁆ = y^n :=
Exists.imp (λ n, eq.symm) $ mem_zpowers_iff.mp $ comm_in_zpowers_right x y

-- TODO should these be simp lemmas?
@[simp]
lemma commute.comm_left : commute ⁅x, y⁆ x :=
let ⟨n, h⟩ := comm_is_zpow_left x y in
h.symm ▸ commute.zpow_self x n

@[simp]
lemma commute.comm_right : commute ⁅x, y⁆ y :=
let ⟨n, h⟩ := comm_is_zpow_right x y in
h.symm ▸ commute.zpow_self y n


lemma comm_inv_left : ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ :=
begin
  convert_to x⁻¹ * (y * x * y⁻¹) = (y * x * y⁻¹) * x⁻¹,
  { group }, { group },

  obtain ⟨n, h⟩ := conj_is_zpow x y,
  simp_rw h,
  exact commute.inv_left (by simp),
end

lemma comm_inv_right : ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ :=
by rw [← commutator_element_inv, comm_inv_left, commutator_element_inv]


lemma comm_pow_left : ∀ (n : ℕ), ⁅x^n, y⁆ = ⁅x, y⁆^n
| 0     := by simp
| (n+1) :=
begin
  simp_rw pow_succ,
  rw [← comm_pow_left n, commutator_element_def (x^n) y,
    ← mul_assoc, ← mul_assoc, ← mul_assoc,
    ((commute.comm_left x y).pow_right n).eq],
  group,
end

lemma comm_pow_right (n : ℕ) : ⁅x, y^n⁆ = ⁅x, y⁆^n :=
by rw [← commutator_element_inv, comm_pow_left, ← inv_pow, commutator_element_inv]

lemma comm_zpow_left : ∀ (n : ℤ), ⁅x^n, y⁆ = ⁅x, y⁆^n
| (n : ℕ) := by exact_mod_cast comm_pow_left x y n
| -[1+ n] :=
begin
  simp_rw zpow_neg_succ_of_nat,
  rw [comm_inv_left, inv_inj],
  exact_mod_cast comm_pow_left x y (n+1),
end

lemma comm_zpow_right (n : ℤ) : ⁅x, y^n⁆ = ⁅x, y⁆^n :=
by rw [← commutator_element_inv, comm_zpow_left, ← inv_zpow, commutator_element_inv]


-- TODO name for this
lemma pow_mul_distrib_comm :
∀ (n : ℕ), (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ n.choose 2
| 0     := by simp
| (n+1) :=
begin
  rw [nat.choose_succ_succ, nat.choose_one_right],
  simp_rw [pow_succ, pow_add],
  rw [pow_mul_distrib_comm n, ← comm_pow_right y x n],
  simp_rw [← mul_assoc, mul_assoc x _ _],
  rw [mul_right_inj, mul_left_inj],
  conv_rhs { rw [mul_assoc,
    ← ((commute.comm_left y (x^n)).pow_right n).eq, ← mul_assoc] },
  rw [mul_left_inj, ← inv_inj, ← inv_inj],
  conv_rhs { rw [mul_inv_rev, mul_inv_rev,
    ← comm_inv_left, ← comm_inv_right] },
  group,
end

end commutator_lemmas


section noncommutative

-- FIXME there's a lot of explicit passing of G around. why is it an explicit argument?
parameter (G)

-- FIXME opening nat, int, etc.?

lemma exists_noncommutative :
  ∃ x y : G, ¬ commute x y :=
begin
  have := hG.out.2,
  push_neg at this,
  exact this,
end

-- FIXME exists npow eq one of zpow eq one. that takes care of the hard part right?
lemma finite_order_of_noncommutative : ∀ {x y : G} (h : ¬ commute x y),
  is_of_fin_order ⁅x, y⁆ ∧
  is_of_fin_order x ∧
  is_of_fin_order y :=
begin
  suffices : ∀ {x y : G}, ¬ commute x y → is_of_fin_order ⁅x, y⁆ ∧ is_of_fin_order x,
  { intros x y h,
    use [(this h).1, (this h).2, (this $ h ∘ commute.symm).2], },
  intros x y h,

  obtain hc := commutator_element_eq_one_iff_commute.not.mpr h,
  obtain ⟨n', hn'⟩ := comm_is_zpow_left x y,

  let n := n'.nat_abs,
  have n_pos : 0 < n := int.nat_abs_pos_of_ne_zero (λ h, begin
    rw [h, zpow_zero] at hn',
    exact hc hn',
  end),
  have hno : ⁅x, y⁆ ^ n' = 1,
  { simp [← comm_zpow_left, ← hn', commutator_element_eq_one_iff_commute] },
  have ho : ⁅x, y⁆ ^ n = 1,
  { rcases int.nat_abs_eq n' with hs | hs,
    work_on_goal 1 { rw ← zpow_coe_nat },
    work_on_goal 2 { rw [← inv_inj, inv_one, ← zpow_neg_coe_of_pos _ n_pos] },
    all_goals { exact hs ▸ hno } },

  simp_rw is_of_fin_order_iff_pow_eq_one,
  use [n, n_pos, ho,
       n^2, sq_pos_of_pos n_pos],

  rw [← zpow_coe_nat],
  push_cast,
  rw [int.nat_abs_sq, pow_two, zpow_mul, ← hn', hno],
end

lemma lift_to_prime_order (x y : G) {p : ℕ} (hp : p.prime) (ho : order_of ⁅x, y⁆ = p)
    (ox : is_of_fin_order x) :
  ∃ x' : G, order_of ⁅x', y⁆ = p ∧ is_of_fin_order x' ∧ ∃ n : ℕ, order_of x' = p^n :=
begin
  obtain ⟨b, ox', b_ndvd⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd
    (multiplicity.finite_nat_iff.mpr
      ⟨hp.ne_one, order_of_pos' ox⟩),
  have b_nz : b ≠ 0 := λ h, (h ▸ b_ndvd) (dvd_zero _),

  use x ^ b,
  simp only [comm_pow_left, order_of_pow' _ b_nz],
  split, { rw [ho, (hp.coprime_iff_not_dvd.mpr b_ndvd).gcd_eq_one, nat.div_one] },
  split, from is_of_fin_order_pow ox _,
  rw [nat.gcd_eq_right (dvd.intro_left _ ox'.symm), ox',
      nat.mul_div_cancel _ (nat.pos_of_ne_zero b_nz)],
  simp,
end

lemma exists_prime_order (x y : G) (h : ¬ commute x y) :
  ∃ (x' y' : G) (p : ℕ) (hp : p.prime) (m n : ℕ),
  order_of ⁅x', y'⁆ = p ∧ order_of x' = p ^ (m + 1) ∧ order_of y' = p ^ (n + 1) :=
begin
  obtain ⟨oc, ox, oy⟩ := finite_order_of_noncommutative G h,

  let a := order_of ⁅x, y⁆,
  have a_pos : 0 < a := order_of_pos' oc,
  obtain ⟨p, p_prime, p_dvd⟩ := nat.exists_prime_and_dvd (by
    rwa [← commutator_element_eq_one_iff_commute, ← order_of_eq_one_iff] at h),

  let x' := x ^ (a / p),
  have o' : order_of ⁅x', y⁆ = p,
  { rwa [comm_pow_left, order_of_pow', nat.gcd_eq_right (nat.div_dvd_of_dvd p_dvd),
       nat.div_div_self],
    from a_pos,
    exact (nat.div_eq_zero_iff p_prime.pos).not.mpr (nat.le_of_dvd a_pos p_dvd).not_lt },

  have ox' : is_of_fin_order x' := is_of_fin_order_pow ox _,
  clear_value x', clear_dependent x, rename [x' x, o' o, ox' ox],

  obtain ⟨x', o', ox', n, hx⟩ := lift_to_prime_order _ x y p_prime o ox,
  clear_dependent x, rename [x' x, o' o, ox' ox],

  rw [← commutator_element_inv, order_of_inv] at o,

  obtain ⟨y', o', oy', m, hy⟩ := lift_to_prime_order _ y x p_prime o oy,
  clear_dependent y, rename [y' y, o' o, oy' oy],

  cases m,
  { exfalso,
    rw [pow_zero, order_of_eq_one_iff] at hy,
    simpa [hy, p_prime.ne_one.symm] using o },
  cases n,
  { exfalso,
    rw [pow_zero, order_of_eq_one_iff] at hx,
    simpa [hx, p_prime.ne_one.symm] using o },

  use [y, x, p, p_prime, m, n, o, hy, hx],
end

-- FIXME propagate primality information (of p) via instances instead.
-- FIXME okay this is a big fixme ig

lemma decomp_of_prime_order {x y : G} (hy : y ∈ zpowers x) {p : ℕ} (hp : p.prime) {n : ℕ}
    (ox : order_of x = p ^ (n + 1)) (oy : order_of y = p) :
  ∃ r : ℕ, y = x ^ (r * p ^ n) ∧ p.coprime r :=
begin
  have y_ne : y ≠ 1 := λ h, hp.ne_one.symm $ by rwa [h, order_of_one] at oy,
  obtain ⟨a, ha⟩ := mem_zpowers_iff.mp hy,

  let a' := int.nat_mod a ↑(p ^ (n + 1)),
  have ha' : x ^ a' = y,
  { dsimp only [a'],
    rw [← ha, zpow_eq_mod_order_of, ox, int.nat_mod, ← zpow_coe_nat, int.to_nat_of_nonneg],
    apply int.mod_nonneg,
    simpa using hp.ne_zero },
  clear_value a', clear_dependent a, rename [a' a, ha' ha],
  rw ← ha at *,

  have a_nz : a ≠ 0 := λ h, y_ne $ by rw [h, pow_zero],
  have a_gcd : (p ^ (n + 1)).gcd a = p ^ n,
  { rw [order_of_pow' _ a_nz, ox, nat.div_eq_iff_eq_mul_left] at oy,
    nth_rewrite 0 pow_succ at oy,
    rw nat.mul_right_inj hp.pos at oy,
    exact oy.symm,
    exact nat.gcd_pos_of_pos_right _ (nat.pos_of_ne_zero a_nz),
    exact nat.gcd_dvd_left _ _ },
  have dvd_a : p ^ n ∣ a := a_gcd ▸ nat.gcd_dvd_right _ _,

  use a / p ^ n,
  split, { rwa nat.div_mul_cancel },
  rw nat.coprime_iff_gcd_eq_one,
  convert nat.gcd_div (pow_dvd_pow p n.le_succ) dvd_a,
  { rw [nat.pow_div n.le_succ hp.pos, nat.succ_eq_add_one, nat.add_sub_cancel_left, pow_one] },
  rw [a_gcd, nat.div_self],
  exact pow_pos hp.pos _,
end

-- FIXME this proof is slightly sad

lemma canonicalise_of_prime_order {x y : G} {p : ℕ} (hp : p.prime) {m n : ℕ}
    (o : order_of ⁅x, y⁆ = p) (ox : order_of x = p ^ (m + 1)) (oy : order_of y = p ^ (n + 1)) :
  ∃ (x' y' : G),
  order_of ⁅x', y'⁆ = p ∧
  order_of x' = p ^ (m + 1) ∧ ⁅x', y'⁆ = x' ^ (p ^ m) ∧
  order_of y' = p ^ (n + 1) ∧ ⁅x', y'⁆ = y' ^ (p ^ n) :=
begin
  have hc : ⁅x, y⁆ ≠ 1 := λ h, hp.ne_one.symm $ by rwa [h, order_of_one] at o,

  obtain ⟨a, ha, a_cp⟩ := decomp_of_prime_order G (comm_in_zpowers_left x y) hp ox o,
  obtain ⟨b, hb, b_cp⟩ := decomp_of_prime_order G (comm_in_zpowers_right x y) hp oy o,

  obtain ⟨a', ha'⟩ := nat.exists_mul_mod_eq_one_of_coprime a_cp.symm hp.one_lt,
  obtain ⟨b', hb'⟩ := nat.exists_mul_mod_eq_one_of_coprime b_cp.symm hp.one_lt,
  have ma : a' * a ≡ 1 [MOD p], { rwa [← nat.mod_eq_of_lt hp.one_lt, nat.mul_comm] at ha' },
  have mb : b' * b ≡ 1 [MOD p], { rwa [← nat.mod_eq_of_lt hp.one_lt, nat.mul_comm] at hb' },
  have a'_cp := (nat.coprime_of_mul_modeq_one _ ma).symm,
  have b'_cp := (nat.coprime_of_mul_modeq_one _ mb).symm,
  have a'_nz : a' ≠ 0 := λ h, hp.ne_one $ p.coprime_zero_right.mp $ h ▸ a'_cp,
  have b'_nz : b' ≠ 0 := λ h, hp.ne_one $ p.coprime_zero_right.mp $ h ▸ b'_cp,

  use [x ^ b', y ^ a'],
  rw [comm_pow_left, comm_pow_right],
  split,
  { rw [← pow_mul, order_of_pow' _ (mul_ne_zero a'_nz b'_nz), o,
      nat.coprime_iff_gcd_eq_one.mp (a'_cp.mul_right b'_cp), nat.div_one] },
  rw [order_of_pow' _ b'_nz, order_of_pow' _ a'_nz,
    ox, nat.coprime_iff_gcd_eq_one.mp (b'_cp.pow_left _), nat.div_one,
    oy, nat.coprime_iff_gcd_eq_one.mp (a'_cp.pow_left _), nat.div_one],
  refine ⟨rfl, ha.symm ▸ _, rfl, hb.symm ▸ _⟩; simp_rw ← pow_mul; rw pow_eq_pow_iff_modeq,
  { rw [ox, pow_succ],
    convert_to a' * a * b' * p ^ m ≡ 1 * b' * p ^ m [MOD p * p ^ m], ring1, ring1,
    exact (nat.modeq.mul_right' _ $ nat.modeq.mul_right _ ma) },
  { rw [oy, pow_succ],
    convert_to b' * b * a' * p ^ n ≡ 1 * a' * p ^ n [MOD p * p ^ n], ring1, ring1,
    exact (nat.modeq.mul_right' _ $ nat.modeq.mul_right _ mb) },
end

-- FIXME pretty slow
lemma embeds_quaternions :
  ∃ S : subgroup G, nonempty (Q₈ ≃* S) :=
begin
  obtain ⟨x, y, hxy⟩ := exists_noncommutative G,
  obtain ⟨i, j, p, hp, m, n, o, oi, oj⟩ := exists_prime_order G x y hxy,
  clear hxy x y,

  haveI hpI : fact p.prime := ⟨hp⟩,

  revert i j,
  wlog hnm : n ≤ m,
  swap, from this j i (by rw [← commutator_element_inv, order_of_inv, o]) oj oi,
  intros i j o oi oj,

  induction n using nat.strong_induction_on with n ih generalizing i j,

  obtain ⟨i', j', o', oi', hi', oj', hj'⟩ := canonicalise_of_prime_order G hp o oi oj,
  clear_dependent i j, rename [i' i, j' j, o' o, oi' oi, hi' hi, oj' oj, hj' hj],

  let j' := i⁻¹ ^ (p ^ (m - n)) * j,
  have j'_pow : j' ^ (p ^ n) = _ := pow_mul_distrib_comm _ _ _,
  rw [← pow_mul, pow_sub_mul_pow p hnm, inv_pow, ← hi, ← hj, inv_mul_self, one_mul,
    comm_pow_right, ← pow_mul, comm_inv_right, commutator_element_inv] at j'_pow,

  by_cases hdvd : p ∣ p ^ (m - n) * (p ^ n).choose 2,
  { nth_rewrite 0 ← o at hdvd, rw order_of_dvd_iff_pow_eq_one.mp hdvd at j'_pow,
    obtain ⟨n', oj'⟩ := exists_order_of_eq_prime_pow_iff.mpr ⟨_, j'_pow⟩,
    have o' : order_of ⁅i, j'⁆ = p,
    { dsimp only [j'],
      rw [commutator_element_mul_right,
        ((commute.refl i).inv_right.pow_right $ p ^ (m - n)).commutator_eq,
        one_mul],
      -- FIXME do you want to pull out order_of_injective into an order_of_equiv?
      convert order_of_injective (mul_aut.conj $ i⁻¹ ^ p ^ (m - n)).to_monoid_hom
        (by simpa using function.injective_id) _,
      exact o.symm },
    have n'_le : n' ≤ n,
    { rw [← nat.pow_dvd_pow_iff_le_right hp.one_lt, ← oj',
          order_of_dvd_iff_pow_eq_one, j'_pow] },
    cases n',
    { rw [pow_zero, order_of_eq_one_iff] at oj',
      rw [oj', commutator_element_one_right, order_of_one] at o',
      exact absurd o'.symm hp.ne_one },
    exact ih n' (nat.lt_of_succ_le n'_le) ((n'.le_succ.trans n'_le).trans hnm) i j' o' oi oj' },
  clear_dependent ih j',

  obtain rfl : n = m,
  { refine le_antisymm hnm (nat.le_of_sub_eq_zero _),
    contrapose! hdvd with sub_nz,
    exact dvd_mul_of_dvd_left (dvd_pow_self _ sub_nz) _ },
  rw [tsub_self, pow_zero, one_mul] at hdvd,

  cases n,
  { rw [pow_zero, pow_one] at hi,
    rw [← hi, (commute.comm_right i j).commutator_eq, order_of_one] at o,
    exact absurd o hp.ne_one.symm },

  clear hpI,
  obtain rfl : p = 2 := hp.eq_two_or_odd'.resolve_right _,
  swap,
  { contrapose! hdvd with p_odd,
    rw [nat.choose_two_right, nat.mul_div_assoc],
    exact dvd_mul_of_dvd_left (dvd_pow_self _ n.succ_ne_zero) _,
    rw [← even_iff_two_dvd, nat.even_sub (nat.one_le_pow _ _ hp.pos),
      nat.even_pow' n.succ_ne_zero],
    simpa using p_odd },

  rw [← even_iff_two_dvd, nat.choose_two_right, mul_comm,
    nat.mul_div_assoc _ (dvd_pow_self _ n.succ_ne_zero), nat.even_mul,
    not_or_distrib, pow_succ', nat.mul_div_cancel _ zero_lt_two,
    nat.even_pow] at hdvd,
  simp only [even_two, true_and] at hdvd,
  obtain rfl : n = 0 := of_not_not hdvd.2,

  clear hp hnm hdvd,
  norm_num at *,

  use (⊤ : subgroup Q₈).map (quaternion_hom i j oi hi oj hj),
  exact ⟨subgroup.top_equiv.symm.trans $ subgroup.equiv_map_of_injective
   ⊤ _ (quaternion_hom_injective _ _ _ _ _ _)⟩,
end

end noncommutative










-- FIXME the location of this lemma leaves something to be desired
@[protected] instance subgroup.is_modular_lattice : 
  is_modular_lattice (subgroup G) :=
⟨λ x y z h,
eq.le $ eq.symm $ set_like.coe_set_eq.mp begin
  change _ = ↑(x ⊔ y) ⊓ ↑z,
  simp_rw subgroup.normal_mul,
  exact subgroup.mul_inf_assoc _ _ _ h
end⟩

section abelian_part

parameters {Q : subgroup G} (ϕ : Q₈ ≃* Q)

omit hG

private abbreviation Q₈.a := @quaternion_group.a 2
private abbreviation Q₈.xa := @quaternion_group.xa 2
private abbreviation i := Q₈.a 1
private abbreviation j := Q₈.xa 0

include hG

-- FIXME
-- lemma order_of_i : order_of i = 4 :=
-- (show 2 ^ 2 = 4, by norm_num) ▸ order_of_eq_prime_pow (by dec_trivial) (by dec_trivial)
-- lemma order_of_j : order_of j = 4 :=
-- (show 2 ^ 2 = 4, by norm_num) ▸ order_of_eq_prime_pow (by dec_trivial) (by dec_trivial)
--
-- lemma order_of_eq (x : Q₈) : order_of (ϕ x : G) = order_of x :=
-- begin
--   rw ← ϕ.coe_to_monoid_hom,
--   apply_mod_cast order_of_injective,
--   exact ϕ.injective,
-- end
--
-- lemma order_of_ϕi : order_of (ϕ i : G) = 4 := (order_of_eq ϕ i).trans order_of_i
-- lemma order_of_ϕj : order_of (ϕ j : G) = 4 := (order_of_eq ϕ j).trans order_of_j

-- TODO?
-- open_locale pointwise


lemma comm_cases_of_order_dvd_four (x y : G) (ho : x ^ 4 = 1) :
  ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = x ^ 2 :=
begin
  obtain ⟨n, hn⟩ := conj_is_zpow x⁻¹ y,
  by_cases hx : x = 1, from or.inl (hx.symm ▸ commutator_element_one_left y),
  have n_nz : n ≠ 0 :=
  λ h, hx (by rwa [h, zpow_zero, mul_inv_eq_one, mul_right_eq_self, inv_eq_one] at hn),

  have h := congr_arg order_of hn,
  have o_conj : order_of x⁻¹ = order_of (y * x⁻¹ * y⁻¹) :=
  order_of_eq_order_of_iff.mpr (λ n, by rw [conj_pow, mul_inv_eq_one, mul_right_eq_self]),
  rw [← o_conj, order_of_zpow' _ n_nz, eq_comm, nat.div_eq_self] at h,

  rw (show 4 = 2 ^ 2, by norm_num) at ho,
  obtain ⟨k, ho'⟩ := exists_order_of_eq_prime_pow_iff.mpr ⟨2, ho⟩,
  have hk : 0 < k ∧ k ≤ 2 :=
  ⟨by { rw zero_lt_iff, rintro rfl,
      rw [pow_zero, order_of_eq_one_iff] at ho',
      exact hx ho' },
    (nat.pow_dvd_pow_iff_le_right one_lt_two).mp (ho' ▸ order_of_dvd_of_pow_eq_one ho)⟩,
  rw [order_of_inv, ho'] at h,

  replace h := h.resolve_left (pow_ne_zero k $ by norm_num),
  rw [int.gcd_eq_one_iff_coprime, nat.cast_pow, is_coprime.pow_left_iff hk.1] at h,
  rw_mod_cast int.prime_two.coprime_iff_not_dvd at h,

  rw ← mul_right_inj x at hn,
  simp_rw ← mul_assoc at hn,
  rw [inv_zpow', ← zpow_one_add, add_comm] at hn,

  rw [← even_iff_two_dvd, ← even_neg, ← int.even_add_one] at h,
  obtain ⟨m, hm⟩ := h,
  rw [commutator_element_def, hn, hm, ← two_mul],

  cases hk,
  interval_cases k,
  { rw zpow_mul, convert or.inl (one_zpow _),
    norm_cast, rw pow_one at ho', rw ← ho',
    exact pow_order_of_eq_one _ },
  { rw [zpow_eq_mod_order_of, ho', pow_two, nat.cast_mul,
      show ((2 : ℕ) : ℤ) = (2 : ℤ), by norm_num, int.mul_mod_mul_of_pos two_pos m 2],
    cases int.mod_two_eq_zero_or_one m with h h; rw h,
    from or.inl (by simp),
    from or.inr (by norm_cast) },
end



include Q ϕ

-- FIXME FIXME FIXME
-- we want a tactic that takes goals which "live in Q",
-- in the sense that all the terms are like varphi bleh or whatever,
-- and transports them into Q₈.
-- this seems pretty easy, so maybe just do it.
-- refer to zify perhaps for an example of something super ez?

-- FIXME why isn't parameters stuff working?

-- FIXME FIXME FIXME loc for lemma
omit hG Q ϕ

lemma transport_var {A B : Type*} [has_mul A] [has_mul B] (ρ : A ≃* B) {P : B → Prop} :
  (∀ x : A, P (ρ x)) ↔ (∀ x : B, P x) :=
ρ.to_equiv.forall_congr_left

include hG Q ϕ

lemma centralize_of_comm_generators (x : G) :
  ⁅(ϕ i : G), x⁆ = 1 ∧ ⁅(ϕ j : G), x⁆ = 1 → x ∈ Q.centralizer :=
begin
  simp_rw commutator_element_eq_one_iff_commute,
  rintro ⟨hi, hj⟩,

  intros y hy,
  lift y to Q using hy,
  revert y, refine (transport_var ϕ).mp (λ y, _),

  -- FIXME have this as a global instance for this section so that this isn't sussy
  haveI : fact (0 < 2 * 2) := ⟨by norm_num⟩,
  cases y,
  { rw [← zmod.nat_cast_zmod_val y, ← quaternion_group.a_one_pow, map_pow],
    exact hi.pow_left y.val },
  { rw [← zero_add y, ← quaternion_group.xa_mul_a 0 y, map_mul],
    rw [← zmod.nat_cast_zmod_val y, ← quaternion_group.a_one_pow, map_pow],
    exact hj.mul_left (hi.pow_left y.val) },
end


-- TODO is this the best form for this lemma's result to be in?
lemma group_eq_quaternion_mul_centraliser : Q ⊔ Q.centralizer = ⊤ :=
begin
  ext x,
  suffices : ∃ q : Q, ↑q * x ∈ Q.centralizer,
  { obtain ⟨q, h⟩ := this,
    have := mul_mem_sup q⁻¹.2 h,
    simpa using this },

  -- FIXME oi, oj could be used here, to reasonable effect
  -- norm_cast, rw ← map_pow, convert map_one _
  cases comm_cases_of_order_dvd_four (ϕ i : G) x
    (by transport_group ϕ.symm) with hi hi;
  cases comm_cases_of_order_dvd_four (ϕ j : G) x
    (by transport_group ϕ.symm) with hj hj;
  [use 1, use ϕ i, use ϕ j, use ϕ (i * j)];
  { apply centralize_of_comm_generators ϕ,
    simp_rw [commutator_element_mul_right, hi, hj, commutator_element_def],
    transport_group ϕ.symm },
end

lemma comm_ϕ (q : Q₈) (g : Q.centralizer) :
  commute (ϕ q : G) g :=
g.2 (ϕ q) (by simp)


lemma not_order_four_in_centralizer (g : Q.centralizer) :
  ¬ order_of g = 4 :=
begin
  have ci := comm_ϕ ϕ i g,
  have cj := comm_ϕ ϕ j g,
  have : ⁅(ϕ j * g : G), (ϕ i : G)⁆ = ϕ (quaternion_group.a 2),
  { rw [← commutator_element_inv, ← comm_inv_left, commutator_element_mul_right,
      ci.inv_left.commutator_eq, commutator_element_def],
    transport_group ϕ.symm },

  by_contra' ho,
  cases comm_cases_of_order_dvd_four (ϕ j * g : G) (ϕ i) begin
    convert cj.mul_pow _,
    rw_mod_cast (show g ^ 4 = 1, from ho ▸ pow_order_of_eq_one g),
    transport_group ϕ.symm,
  end; rw this at h,
  { revert h, transport_group ϕ.symm },

  suffices : (g : G) ^ 2 = 1,
  from pow_ne_one_of_lt_order_of' two_ne_zero' (by { rw_mod_cast ho, norm_num }) this,
  rw cj.mul_pow at h,
  convert mul_right_eq_self.mp (h.symm.trans _),
  transport_group ϕ.symm,
end


@[protected] instance quaternion_centralizer_commutative :
  Q.centralizer.is_commutative :=
⟨⟨λ a b, begin
  by_contra' h,
  haveI : fact (group.is_hamiltonian Q.centralizer) := ⟨⟨λ S, begin
    convert (hG.1.1 $ S.map Q.centralizer.subtype).comap Q.centralizer.subtype,
    simp only [comap_map_eq_self_of_injective, subgroup.coe_subtype, subtype.coe_injective],
  end, λ hc, h (hc a b)⟩⟩,

  obtain ⟨S, ⟨ψ⟩⟩ := embeds_quaternions Q.centralizer,
  refine not_order_four_in_centralizer ϕ (ψ i) (eq.trans _ (show order_of i = 4, from _)),
  { rw ← ψ.coe_to_monoid_hom,
    apply_mod_cast order_of_injective,
    exact ψ.injective },
  -- FIXME this follows from oi
  change 4 with 2 ^ 2,
  apply order_of_eq_prime_pow; dec_trivial,
end⟩⟩

@[protected] instance quaternion_centralizer_comm_group :
  comm_group Q.centralizer :=
begin
  haveI := hamiltonian.quaternion_centralizer_commutative,
  apply_instance,
end

lemma quaternion_centralizer.is_torsion :
  monoid.is_torsion Q.centralizer :=
begin
  intro g,
  rw is_of_fin_order_iff_coe Q.centralizer.to_submonoid g,

  have : ¬ commute (ϕ i : G) (ϕ j * g),
  { by_contra' h,
    replace h := (h.mul_right $ commute.inv_right $ comm_ϕ ϕ i g),
    rw [mul_inv_cancel_right] at h,
    replace h := h.commutator_eq,
    rw commutator_element_def at h,
    revert h, transport_group ϕ.symm },

  replace this := (finite_order_of_noncommutative G this).2.2,

  rw [← one_mul g, coe_mul, coe_one, ← inv_mul_self (ϕ j : G), mul_assoc],
  refine commute.is_of_fin_order_mul _ _ this,
  from ((commute.refl (ϕ j : G)).mul_right $ comm_ϕ ϕ j g).inv_left,
  -- FIXME this follows from oj
  rw [is_of_fin_order_inv_iff, ← is_of_fin_order_iff_coe Q.to_submonoid,
    ← ϕ.coe_to_monoid_hom],
  exact (monoid_hom.is_of_fin_order _ $ order_of_pos_iff.mp $ order_of_pos j),
end


def odd_component : subgroup Q.centralizer :=
{ carrier := {g : Q.centralizer | odd (order_of g)},
  one_mem' := ⟨0, by simp⟩,
  inv_mem' := λ x ⟨k, hk⟩, ⟨k, (order_of_inv x).symm ▸ hk⟩,
  mul_mem' :=
  begin
    haveI := hamiltonian.quaternion_centralizer_commutative,

    intros a b hm hn,
    simp only [set.mem_set_of_eq, not_not] at *,
    have hh := hm.mul hn,
    simp only [nat.odd_iff_not_even, even_iff_two_dvd] at ⊢ hh,
    exact λ h, hh $ h.trans (commute.all a b).order_of_mul_dvd_mul_order_of,
  end }

def two_primary_component : subgroup Q.centralizer :=
@comm_group.primary_component Q.centralizer
  hamiltonian.quaternion_centralizer_comm_group 2 _

lemma mem_two_primary_iff {x : Q.centralizer} :
  x ∈ two_primary_component ↔ x = 1 ∨ order_of x = 2 :=
⟨begin
  rintro ⟨n, hn⟩,
  suffices : n < 2,
  { interval_cases n,
    { left, rw [← order_of_eq_one_iff, hn, pow_zero] },
    { right, rw [hn, pow_one] } },

  by_contra',
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le this, clear this,
  have := order_of_pow' x (show 2 ^ k ≠ 0, from (pow_pos two_pos _).ne'),
  rw [hn, nat.gcd_eq_right (pow_dvd_pow 2 le_add_self), pow_add,
    nat.mul_div_cancel _ (pow_pos two_pos _)] at this,
  change 2 ^ 2 with 4 at this,
  exact not_order_four_in_centralizer ϕ _ this,
 end,
 by { rintro (rfl | h),
   { use 0, rw [pow_zero, order_of_one] },
   { use 1, rw [pow_one, h] } }⟩

lemma mem_two_primary' (x : two_primary_component) :
  x ^ 2 = 1 :=
suffices (x : Q.centralizer) ^ 2 = 1, by exact_mod_cast this,
show x.val ^ 2 = 1, from
(mem_two_primary_iff.mp x.2).elim
  (λ h, by rw [h, one_pow])
  (λ h, by rw [← h, pow_order_of_eq_one])


@[protected] instance two_primary_comm_group :
  comm_group two_primary_component :=
begin
  haveI := hamiltonian.quaternion_centralizer_commutative,
  apply_instance,
end

@[protected] instance two_primary_vector_space :
  module (zmod 2) (additive two_primary_component) := module.of_core
{ smul := λ s x, s.val • x,
  smul_add := λ r, smul_add r.val,
  add_smul := λ r s, additive.of_mul.forall_congr_left.mp $ λ x, begin
    change x ^ (r + s).val = x ^ r.val * x ^ s.val,
    rw [← pow_add, zmod.val_add],
    exact (pow_eq_pow_mod _ (mem_two_primary' ϕ x)).symm,
  end,
  mul_smul := λ r s, additive.of_mul.forall_congr_left.mp $ λ x, begin
    change x ^ (r * s).val = (x ^ s.val) ^ r.val,
    rw [← pow_mul', zmod.val_mul],
    exact (pow_eq_pow_mod _ (mem_two_primary' ϕ x)).symm,
  end,
  one_smul := λ x, by { dsimp only, rw [zmod.val_one, one_smul] } }


lemma quaternion_centralizer_decomp :
  is_compl two_primary_component odd_component :=
⟨λ x ⟨he, ho⟩, (mem_two_primary_iff.mp he).cases_on mem_bot.mpr $
 λ h, by { simp only [odd_component, nat.odd_iff_not_even, coe_to_submonoid, coe_set_mk,
   set.mem_set_of_eq] at ho, exact absurd (even_two : even (2 : ℕ)) (h ▸ ho) },
begin
  haveI := hamiltonian.quaternion_centralizer_commutative,

  rw [codisjoint_iff, eq_top_iff'],
  from λ x,
    let n := order_of x in
    have hn : 0 < n := order_of_pos' (quaternion_centralizer.is_torsion ϕ x),
    
    let o := ord_compl[2] n, e := ord_proj[2] n in

    have o_pos : 0 < o := nat.ord_compl_pos _ hn.ne',
    have e_pos : 0 < e := nat.ord_proj_pos _ _,

    have two_ndvd : ¬ 2 ∣ o := nat.not_dvd_ord_compl nat.prime_two hn.ne',

    have he : order_of (x ^ o) = e,
    { rw [order_of_pow' x o_pos.ne', nat.gcd_eq_right (n.ord_compl_dvd _)],
      exact nat.div_eq_of_eq_mul_left o_pos (n.ord_proj_mul_ord_compl_eq_self _).symm },
    have ho : order_of (x ^ e) = o,
    { rw [order_of_pow' x e_pos.ne', nat.gcd_eq_right (n.ord_proj_dvd _)] },

    have hfe : is_of_fin_order (x ^ o) := order_of_pos_iff.mp (he.symm ▸ e_pos),
    have hfo : is_of_fin_order (x ^ e) := order_of_pos_iff.mp (ho.symm ▸ o_pos),

    let a := o.gcd_a e, b := o.gcd_b e in

    have hab : ↑1 = ↑o * a + ↑e * b :=
    (show o.gcd e = 1, from nat.coprime_iff_gcd_eq_one.mp $
      nat.prime_two.coprime_pow_of_not_dvd two_ndvd) ▸ o.gcd_eq_gcd_ab e,

    have hea : int.gcd e a = 1 := (nat.dvd_one.mp $ int.gcd_dvd_iff.mpr $
      ⟨b, o, int.mul_comm o a ▸ hab.trans (add_comm _ _)⟩),
    have hob : int.gcd o b = 1 := (nat.dvd_one.mp $ int.gcd_dvd_iff.mpr $
      ⟨a, e, int.mul_comm e b ▸ hab⟩),

    mem_sup.mpr
    ⟨(x ^ o) ^ a, ⟨n.factorization 2, by rwa [order_of_zpow'', he, hea, nat.div_one]⟩,
     (x ^ e) ^ b, show odd (order_of ((x ^ e) ^ b)),
       by rw [order_of_zpow'', ho, hob, nat.div_one,
         nat.odd_iff_not_even, even_iff_two_dvd]; assumption,
     by rw [← zpow_coe_nat, ← zpow_coe_nat, ← zpow_mul, ← zpow_mul,
       ← zpow_add, ← hab, zpow_coe_nat, pow_one]⟩
end⟩


omit hG ϕ
abbreviation n1 : Q₈ := quaternion_group.a 2
include hG ϕ

-- FIXME this is the second time you're proving order of image in an equiv
-- is equal. so maybe you want order_of_equiv?
-- (the first time was commutativity of odd_component)
lemma order_of_n1 :
  order_of (ϕ n1 : G) = 2 :=
(show order_of (ϕ n1 : G) = order_of n1,
 by { rw ← ϕ.coe_to_monoid_hom,
  apply_mod_cast order_of_injective,
  exact ϕ.injective }).trans $
by { apply order_of_eq_prime; dec_trivial }

lemma zpowers_of_n1 (x : G) :
  x ∈ zpowers (ϕ n1 : G) ↔ x = 1 ∨ x = ϕ n1 :=
⟨λ hx, begin
  lift x to zpowers (ϕ n1 : G) using hx,
  let f := group_exp (ϕ n1 : G) (order_of_n1 ϕ),
  revert x,
  refine (multiplicative.of_add.trans f.to_equiv).forall_congr_left.mp (λ x, _),
  fin_cases x;
  simp only [equiv.trans_apply, f, mul_equiv.to_equiv_eq_coe,
    mul_equiv.coe_to_equiv, group_exp_apply];
  transport_group ϕ.symm,
end,
by { rintro (rfl | rfl), use [0, zpow_zero _], use [1, zpow_one _] }⟩

-- FIXME okay, i'm starting to be convinced that transport_group
-- should develop the ability to move local variables via equivalences.
-- like a variable of type Q should become one of type Q₈ when you use ϕ.symm.
-- that should be pretty easy to implement, right?
-- (i guess just multiplicative equivalences is fine for the time being...?
--  i'm not sure how to deal with the other thingy though. maybe
--  just always have those simplification lemmata be a thing.)
-- you could also just decide it's too much effort i guess.

-- um FIXME FIXME FIXME
-- you know how you have the transport_to_Q₈ thingy?
-- maybe generalise that to other equivalences.
lemma quaternion_inf_centralizer :
  Q ⊓ Q.centralizer = zpowers (ϕ n1) :=
begin
  ext x,
  rw [zpowers_of_n1, mem_inf, mem_centralizer_iff, subtype.forall'],
  change {a // a ∈ Q} with Q,
  rw ← transport_var ϕ,
  split,
  { rintro ⟨hq, hc⟩,
    lift x to Q using hq,
    revert x, refine (transport_var ϕ).mp _,
    transport_group ϕ.symm },
  { rintro (rfl | rfl);
    [use [one_mem _], use [set_like.coe_mem _]];
    transport_group ϕ.symm },
end

abbreviation low_neg_one : two_primary_component :=
⟨⟨ϕ n1,
by { refine (mem_inf.mp (_ : _ ∈ Q ⊓ _)).2,
  rw quaternion_inf_centralizer ϕ,
  exact ⟨1, zpow_one _⟩ }⟩,
1, by rw [pow_one, ← order_of_subgroup, coe_mk, order_of_n1]⟩

lemma lift_low_neg_one : (ϕ n1 : G) = ↑low_neg_one := rfl

lemma zpowers_n1 :
  zpowers (ϕ n1 : G) =
  ((zpowers low_neg_one).map two_primary_component.subtype).map Q.centralizer.subtype :=
begin
  ext x,
  simp_rw [mem_map, subgroup.coe_subtype, exists_prop, exists_exists_and_eq_and,
    mem_zpowers_iff, exists_exists_eq_and, coe_zpow, subtype.coe_mk],
end

lemma exists_compl :
  ∃ s : submodule (zmod 2) (additive two_primary_component),
  is_compl (zpowers low_neg_one) s.to_add_subgroup.to_subgroup' :=
begin
  let f : add_subgroup (additive (two_primary_component ϕ)) →
    submodule (zmod 2) (additive (two_primary_component ϕ)) :=
  λ s, { smul_mem' := λ c a ha, by { change c.val • a ∈ _,
      rw add_subgroup.mem_carrier at ha, from s.nsmul_mem ha _ },
      ..s },

  obtain ⟨a, ha⟩ : ∃ (a : submodule (zmod 2) (additive (two_primary_component ϕ))), _ :=
  (submodule.exists_is_compl $ f $ add_subgroup.zmultiples $ additive.of_mul (low_neg_one ϕ)),
  use a,
  refine_struct {..},
  { rintros x ⟨⟨k, hk⟩, h⟩,
    rw ← hk,
    convert ha.1 ⟨⟨k, by simp⟩,
      by { change (additive.of_mul ((low_neg_one ϕ) ^ k)) ∈ _, rw hk, convert h }⟩ using 0 },
  { intros x hx,
    have := submodule.mem_sup.mp (ha.2 (show additive.of_mul x ∈ ⊤, by convert hx using 0)),
    rw mem_sup,
    convert this using 0 },
end

section structure_theorem_aux

parameters (E' : subgroup two_primary_component) (hE' : is_compl (zpowers low_neg_one) E')
include E' hE'

def cover : fin 3 → subgroup G :=
![ Q,
  (E'.map two_primary_component.subtype).map Q.centralizer.subtype,
  odd_component.map Q.centralizer.subtype]

-- FIXME this is a bit sus
lemma c0 : cover 0 = Q := rfl
lemma c1 : cover 1 = (E'.map two_primary_component.subtype).map Q.centralizer.subtype := rfl
lemma c2 : cover 2 = odd_component.map Q.centralizer.subtype := rfl

lemma hcomm : ∀ i j, i ≠ j → ∀ x y, x ∈ cover i → y ∈ cover j → commute x y :=
begin
  -- FIXME it's a bit suspicious that we need to be reminded?
  haveI := hamiltonian.quaternion_centralizer_commutative,

  intros i j hij,
  wlog hij : i < j, from lt_or_lt_iff_ne.mpr hij,
  intros x y hx hy,
  fin_cases j; fin_cases i; try { exact absurd hij (by norm_num) };
    dsimp only [c0, c1, c2] at hy hx;
    try { lift x to Q.centralizer using map_subtype_le _ hx };
    try { lift y to Q.centralizer using map_subtype_le _ hy },
  from y.2 x hx,
  from y.2 x hx,
  change ↑x * ↑y = ↑y * ↑x,
  exact_mod_cast commute.all x y,
end

lemma disjoint_c12' : disjoint (E'.map two_primary_component.subtype) (odd_component) :=
quaternion_centralizer_decomp.disjoint.mono_left $ map_subtype_le _

lemma disjoint_c12 : disjoint (cover 1) (cover 2) :=
begin
  have := disjoint_iff.mp (disjoint_c12' ϕ E' hE'),
  have := Q.centralizer.coe_subtype.substr subtype.coe_injective,
  rw [disjoint_iff, c1, c2, ← map_inf_eq, map_eq_bot_iff_of_injective]; assumption,
end

-- omit hG Q ϕ E' hE'
-- -- FIXME lemma location
-- @[simp] lemma coe_mem_map_subtype (S : subgroup G) (K : subgroup S) (x : S) :
--   (x : G) ∈ K.map S.subtype ↔ x ∈ K :=
-- by simp_rw [mem_map, subgroup.coe_subtype, set_like.coe_eq_coe, exists_prop, exists_eq_right],

-- include hG Q ϕ E' hE'

-- FIXME lemma that states subtype thingy is injective?
-- alternatively FIXME FIXME FIXME lemma that transports disjointness across subtype map

lemma disjoint_n1c1 : disjoint (zpowers (ϕ n1 : G)) (cover 1) :=
begin
  have := hE'.inf_eq_bot,
  have := Q.centralizer.coe_subtype.substr subtype.coe_injective,
  have := (two_primary_component ϕ).coe_subtype.substr subtype.coe_injective,
  rw [disjoint_iff, zpowers_n1 ϕ, c1, ← map_inf_eq, ← map_inf_eq,
    map_eq_bot_iff_of_injective, map_eq_bot_iff_of_injective]; assumption,
end

-- FIXME FIXME FIXME lemma location
omit hG Q ϕ E' hE'

@[simp] lemma map_subtype_top (S : subgroup G) : map S.subtype ⊤ = S :=
by rw [← top_subgroup_of S, subgroup_of_map_subtype, top_inf_eq]

noncomputable def equiv_map_subtype {G : Type*} [group G] {S : subgroup G} {K : subgroup S} :
  map S.subtype K ≃* K :=
(equiv_map_of_injective _ _ (S.coe_subtype.substr subtype.coe_injective)).symm

include hG Q ϕ E' hE'

lemma sup_n1c1 :
  zpowers (ϕ n1 : G) ⊔ cover 1 = two_primary_component.map Q.centralizer.subtype :=
by rw [zpowers_n1 ϕ, c1, ← map_sup, ← map_sup, codisjoint_iff.mp hE'.codisjoint, map_subtype_top]

lemma cover_compl :
  is_compl (cover 0) (cover 1 ⊔ cover 2) :=
⟨begin
  rw [c0, c1, c2, disjoint_iff, ← map_sup,
    ← inf_of_le_right (map (two_primary_component ϕ).subtype _ ⊔ _).map_subtype_le,
    ← inf_assoc, quaternion_inf_centralizer ϕ, map_sup, ← disjoint_iff],
  refine (disjoint_n1c1 ϕ E' hE').disjoint_sup_right_of_disjoint_sup_left _,
  rw sup_n1c1 ϕ E' hE',
  have := (quaternion_centralizer_decomp ϕ).inf_eq_bot,
  have := Q.centralizer.coe_subtype.substr subtype.coe_injective,
  rw [disjoint_iff, ← map_inf_eq, map_eq_bot_iff_of_injective]; assumption,
end,
begin
  rw [c0, c1, c2, codisjoint_iff],
  have h := (zpowers_n1 ϕ).symm.trans_le (show zpowers (ϕ n1 : G) ≤ Q,
  begin
    rintros x ⟨n, rfl⟩,
    rw [← coe_zpow, ← map_zpow],
    apply set_like.coe_mem,
  end),
  conv_lhs
  { conv { congr, rw ← sup_of_le_left h },
    rw sup_assoc,
    congr, skip,
    simp only [← sup_assoc, ← map_sup,
      hE'.sup_eq_top, (quaternion_centralizer_decomp ϕ).sup_eq_top, map_subtype_top], },
  exact group_eq_quaternion_mul_centraliser ϕ,
end⟩

def f := noncomm_pi_coprod hcomm

-- FIXME FIXME FIXME make the parameters implicittttt

lemma f_inj : function.injective f :=
injective_noncomm_pi_coprod_of_independent $ show complete_lattice.independent cover,
begin
  intro i,
  simp_rw [show ∀ j : fin 3, j ≠ i ↔ j ∈ ({i + 1, i + 2} : set (fin 3)), by dec_trivial!,
    supr_pair],
  
  have := (cover_compl ϕ E' hE').disjoint,
  have d12 := disjoint_c12 ϕ E' hE',
  fin_cases i; norm_fin,
  exact this,
  exact d12.disjoint_sup_right_of_disjoint_sup_left this.symm,
  exact sup_comm.substr
    (disjoint.disjoint_sup_right_of_disjoint_sup_left d12.symm (sup_comm.subst this).symm),
end

lemma f_surj : function.surjective f :=
monoid_hom.range_top_iff_surjective.mp $
noncomm_pi_coprod_range.trans $ cover_compl.sup_eq_top.congr_right.mp $
begin
  rw ← finset.sup_univ_eq_supr,
  change ({0, 1, 2} : finset (fin 3)).sup _ = _,
  simp only [finset.sup_insert, finset.sup_singleton],
end

-- FIXME FIXME FIXME i think just making arguments implicit would make a lot of things happy

noncomputable def structure_theorem_aux : G ≃* Q × E' × odd_component :=
(mul_equiv.of_bijective f ⟨f_inj, f_surj⟩).symm.trans $
mul_equiv.trans
{ to_fun := λ f, (f 0, f 1, f 2),
  inv_fun := λ ⟨a, b, c⟩, fin.cons a $ fin.cons b $ fin.cons c fin_zero_elim,
  left_inv := λ f, funext $ λ x, by fin_cases x; refl,
  right_inv := λ ⟨a, b, c⟩, rfl,
  map_mul' := λ x y, rfl } $
(mul_equiv.refl _).prod_congr $
(show cover 1 ≃* E', from equiv_map_subtype.trans equiv_map_subtype).prod_congr $
equiv_map_subtype

end structure_theorem_aux

theorem structure_theorem :
  ∃ E' : submodule (zmod 2) (additive two_primary_component),
  nonempty (Q × E'.to_add_subgroup.to_subgroup' × odd_component ≃* G) :=
let ⟨E'', hE'⟩ := exists_compl in
⟨E'', ⟨(structure_theorem_aux E''.to_add_subgroup.to_subgroup' hE').symm⟩⟩

end abelian_part

end structure_theorem

universe u

-- FIXME directions of the equivalences.
-- FIXME FIXME FIXME it totally seems like they're just backwards but idk...
-- (like it makes sense for forwards to let you use the simple representation)
-- if you swap the order of one of them, it looks like it might break one of the defeqs
-- in the below proof though. so have fun dealing with that i guess :)
-- (maybe the best way is to literally just symmetrise the final equivalence...)

theorem hamiltonian_characterisation (G : Type u) [group G] :
  group.is_hamiltonian G ↔
  ∃ (E : Module.{u} (zmod 2)) (T : CommGroup.{u}) (hT : ∀ x : T, odd (order_of x)),
  nonempty (Q₈ × (multiplicative E) × T ≃* G) :=
⟨begin
  intro h,
  haveI := fact.mk h,

  obtain ⟨Q, ⟨ϕ⟩⟩ := embeds_quaternions G,
  obtain ⟨E', ⟨ψ⟩⟩ := structure_theorem ϕ,

  haveI := hamiltonian.quaternion_centralizer_commutative ϕ,

  refine ⟨⟨E'⟩, ⟨odd_component ϕ⟩, λ ⟨x, hx⟩, by rwa ← order_of_subgroup, ⟨_⟩⟩,
  refine mul_equiv.trans _ ψ,
  refine ϕ.prod_congr (mul_equiv.symm _),
  refine mul_equiv.prod_congr (mul_equiv.multiplicative_additive _).symm (mul_equiv.refl _),
end,
λ ⟨E, T, hT, ⟨ψ⟩⟩,
⟨λ S, ⟨λ n hn g, begin
    convert_to g * n * g⁻¹ * n⁻¹ * n ∈ S, { group },
    refine S.mul_mem _ hn,

    -- FIXME FIXME FIXME
    -- the cherry on top of the transport_group tactic would be
    -- a ∈ S (S is a subgroup) iff ψ a ∈ S.map ψ.to_monoid_hom

    revert n g,
    refine ((transport_var ψ).mp $ λ n, (transport_var ψ).mp $ λ g hn, _),
    simp only [← map_mul, ← map_mul_inv],
    rw [← ψ.symm_symm, ← mem_map_equiv] at ⊢ hn,
    let S' := S.map ψ.symm.to_monoid_hom,
    dsimp only [← S'] at ⊢ hn,
    clear_value S', clear S, rename S' S,

    rcases n with ⟨xn, yn, zn⟩,
    rcases g with ⟨xg, yg, zg⟩,

    simp only [prod.mk_mul_mk, prod.inv_mk, mul_inv_cancel_comm, mul_right_inv],

    obtain hc | ⟨hc, hns⟩ :
      xg * xn * xg⁻¹ * xn⁻¹ = 1 ∨
      (xg * xn * xg⁻¹ * xn⁻¹ = quaternion_group.a 2 ∧ xn^2 = quaternion_group.a 2),
    { clear hn, dec_trivial! },
    from hc.symm ▸ one_mem S,

    rw hc,
    convert S.pow_mem hn (2 * order_of zn),
    { obtain ⟨k, ho⟩ := hT zn,
      rw [ho, npow_eq_pow, pow_mul, hns, pow_add, pow_one, pow_mul,
        (dec_trivial : (quaternion_group.a 2 ^ 2 : Q₈) = 1), one_pow, one_mul] },
    { change 0 = (2 * order_of zn) • yn.to_add,
      haveI := E.is_module,
      rw [← smul_smul, nsmul_eq_smul_cast (zmod 2), zmod.nat_cast_self, zero_smul] },
    { rw [npow_eq_pow, pow_mul', pow_order_of_eq_one, one_pow] },
  end⟩,
  λ h, absurd
    (h (ψ (i, 1, 1)) (ψ (j, 1, 1)))
    (by { change ¬ _ * _ = _ * _, transport_group ψ.symm })⟩⟩

end hamiltonian
