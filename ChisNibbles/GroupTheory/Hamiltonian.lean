import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Torsion
import Mathlib.Algebra.Group.Commutator
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Multiplicity
import Mathlib.Data.Nat.Choose.Basic

/-!
# Hamiltonian groups

A nonabelian group all of whose subgroups are normal is called *Hamiltonian*.

It turns out that these groups have a simple classification: they are all
of the form Q₈ × E × T where E is a vector space over Z/2Z and T is a
torsion group with no elements of order 2.

In this file this is proven.
-/

/-
This file was originally in Lean 3, so porting it was an... experience.

On the plus side, Lean 4 is so much faster than Lean 3 was.
And there are a couple extra constructions in Mathlib nowadays.
-/

section Spec
  class Group.IsHamiltonian (G : Type*) [Group G] : Prop where
    subgroups_normal : ∀ S : Subgroup G, S.Normal
    anabelian : ¬ ∀ x y : G, Commute x y
  attribute [instance] Group.IsHamiltonian.subgroups_normal
end Spec

open Subgroup
open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

namespace Subgroup
  variable {G : Type*} [Group G]

  @[simp] lemma map_subtype_top (S : Subgroup G) : map S.subtype ⊤ = S := by
    rw [← top_subgroupOf S, subgroupOf_map_subtype, top_inf_eq]

  noncomputable def equiv_map_subtype {G : Type*} [Group G] {S : Subgroup G} {K : Subgroup S} :
      map S.subtype K ≃* K :=
    .symm $ equivMapOfInjective _ _ $ S.coeSubtype ▸ Subtype.coe_injective
end Subgroup

section orderOf
  theorem orderOf_zpow' {G : Type*} [Group G] (x : G) {n : ℤ} (h : n ≠ 0) :
      orderOf (x ^ n) = orderOf x / (orderOf x : ℤ).gcd n := by
    induction n using Int.negInduction with
    | nat n | neg n =>
      simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero] at h
      simp [orderOf_pow' _ h]

  theorem IsOfFinOrder.orderOf_zpow {G : Type*} [Group G] (x : G) (n : ℤ) (h : IsOfFinOrder x) :
      orderOf (x ^ n) = orderOf x / (orderOf x : ℤ).gcd n := by
    obtain rfl | hn := eq_or_ne n 0
    . simp [h.orderOf_pos]
    exact orderOf_zpow' _ hn

  theorem exists_zpow_eq_self_of_coprime {G : Type*} [Group G] {x : G} {n : ℤ}
    (h : IsCoprime n (orderOf x)) :
      ∃ (m : ℤ), (x ^ n) ^ m = x := by
    wlog hn : 0 ≤ n generalizing n
    . have ⟨m, hm⟩ := this (h.neg_left) (by omega)
      use -m; convert hm using 1; group
    lift n to ℕ using hn
    have ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (h.nat_coprime)
    use m; exact_mod_cast hm
end orderOf

namespace Group.IsHamiltonian
section transport
  -- note: the simp_rw would infinite loop if we ever transported
  -- using an automorphism, which is not really what you want, but
  -- whatever good enough for me. also i feel like this should be
  -- an "elab"
  macro "transport_group" ρ:term : tactic => `(tactic|
    focus
    norm_cast
    simp_rw [← ($ρ).injective.eq_iff]
    simp only [map_one, map_mul, map_mul_inv, map_inv, map_pow, map_zpow,
      MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    try decide)

  lemma transport_var {A B : Type*} [Mul A] [Mul B] (ρ : A ≃* B) {P : B → Prop} :
      (∀ x : A, P (ρ x)) → (∀ x : B, P x) :=
    ρ.forall_congr_right.mp
end transport
end Group.IsHamiltonian

section commutatorElement
  lemma commutatorElement_mul_right {G : Type*} [Group G] (g₁ g₂ g₃ : G) :
      ⁅g₁, g₂ * g₃⁆ = ⁅g₁, g₂⁆ * (g₂ * ⁅g₁, g₃⁆ * g₂⁻¹) := by
    group
end commutatorElement

section groupExp
  open AddSubgroup

  variable {G : Type*} {x : G} {n : ℕ}

  noncomputable def addGroupExp [AddGroup G] (h : addOrderOf x = n) :
      ZMod n ≃+ zmultiples x :=
    .ofBijective
      (ZMod.lift n ⟨(zmultiplesHom _ x).rangeRestrict, by
        ext : 1
        show (n : ℤ) • x = 0
        rw [← h, natCast_zsmul, addOrderOf_nsmul_eq_zero]⟩)
      ⟨by
        erw [ZMod.lift_injective]
        intro m hm
        rw [Subtype.ext_iff] at hm
        change m • x = 0 at hm
        rw [← addOrderOf_dvd_iff_zsmul_eq_zero, h] at hm
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd],
      by rintro ⟨a, i, rfl⟩; exact ⟨i, ZMod.lift_coe ..⟩⟩

  noncomputable def groupExp [Group G] (h : orderOf x = n) :
      Multiplicative (ZMod n) ≃* zpowers x :=
    AddEquiv.toMultiplicative'' $
      addGroupExp (x := ofMul x) (by simpa) |>.trans <| .refl _

  @[simp] lemma addGroupExp_apply_coe [AddGroup G] (h : addOrderOf x = n) (i : ℤ) :
      addGroupExp h (i : ZMod n) = i • x := by
    simp only [addGroupExp, range_zmultiplesHom, AddEquiv.ofBijective_apply, ZMod.lift_coe]
    rfl

  @[simp] lemma groupExp_apply_coe [Group G] (h : orderOf x = n) (i : ℤ) :
      groupExp h (ofAdd (i : ZMod n)) = x ^ i :=
    addGroupExp_apply_coe (x := ofMul x) (by simpa) i

  lemma groupExp_apply [Group G] (h : orderOf x = n) (i : Multiplicative (ZMod n)) :
      groupExp h i = x ^ ((toAdd i).cast : ℤ) := by
    induction i using ZMod.forall.mpr with | _ i =>
    erw [groupExp_apply_coe, zpow_eq_zpow_iff_modEq, h,
      Int.ModEq, ← ZMod.intCast_eq_intCast_iff', ZMod.intCast_cast, ZMod.cast_intCast']
end groupExp

namespace QuaternionGroup
  variable {n : ℕ}

  @[simp] lemma a_inv (i : ZMod (2 * n)) : (a i)⁻¹ = a (-i) := rfl
  @[simp] lemma xa_inv (i : ZMod (2 * n)) : (xa i)⁻¹ = xa ((n : ZMod _) + i) := rfl
end QuaternionGroup


-- time for the good stuff
namespace Group.IsHamiltonian

private abbrev Q₈ := QuaternionGroup 2

section quaternionHom

variable {G : Type*} [Group G]
  {i j : G} (o : orderOf ⁅i, j⁆ = 2)
  (oi : orderOf i = 4) (hi : ⁅i, j⁆ = i ^ 2)
  (oj : orderOf j = 4) (hj : ⁅i, j⁆ = j ^ 2)

-- hi ∧ hj implies oi ∧ oj, but (I think) this doesn't
-- turn out to actually be useful to prove. Not totally
-- sure though

noncomputable abbrev exp_i : ZMod 4 → zpowers i := groupExp oi ∘ ofAdd
@[simp] lemma exp_i_apply_coe (n : ℤ) : exp_i oi n = i ^ n := by simp

variable (j) in
noncomputable def quaternionFun : Q₈ → G
  |  .a k => exp_i oi k
  | .xa k => j * exp_i oi k

include hi in
lemma semiconj_j : SemiconjBy j i i⁻¹ := by
  rw [SemiconjBy, eq_comm, ← mul_inv_eq_one, ← mul_right_inj (i ^ 2)]
  convert hi using 1 <;> group

open QuaternionGroup in
noncomputable def quaternionHom : Q₈ →* G :=
  .mk' (quaternionFun j oi) $ by
    rintro (a | a) (b | b) <;>
      change ZMod 4 at a b <;>
      cases' a using ZMod.forall.mpr with a <;>
      cases' b using ZMod.forall.mpr with b <;>
      simp only [a_mul_a, a_mul_xa, xa_mul_a, xa_mul_xa, quaternionFun] <;>
      (try rw [← Int.cast_natCast]) <;>
      simp only [← Int.cast_add, ← Int.cast_sub] <;>
      simp only [Nat.cast_ofNat, Nat.reduceMul, exp_i_apply_coe]
    . group
    . rw [sub_eq_add_neg, add_comm, zpow_add, ← inv_zpow',
        ← mul_assoc, ← mul_assoc, semiconj_j hi |>.inv_right.zpow_right a |>.eq, inv_inv]
    . group
    . rw [semiconj_j hi |>.zpow_right a |>.eq]
      convert_to _ = i⁻¹ ^ a * j ^ 2 * i ^ b
      . rw [pow_two]; group
      rw [← hj, hi]
      group

lemma quaternionHom_a (a : ZMod 4) :
    quaternionHom oi hi hj (.a a) = exp_i oi a :=
  rfl

lemma quaternionHom_xa (a : ZMod 4) :
    quaternionHom oi hi hj (.xa a) = j * exp_i oi a :=
  rfl

lemma quaternionHom_injective : Function.Injective (quaternionHom oi hi hj) :=
  injective_iff_map_eq_one _ |>.mpr $ by
    rintro (a | a)
    . revert a; simp [quaternionHom_a]; decide
    . cases' a using ZMod.forall.mpr with a
      intro h
      rw [quaternionHom_xa, exp_i_apply_coe, mul_eq_one_iff_eq_inv, ← zpow_neg] at h
      absurd h ▸ hi
      rw [Commute.self_zpow i (-a) |>.commutator_eq, eq_comm]
      apply pow_ne_one_of_lt_orderOf <;> norm_num [oi]

end quaternionHom



section structure_theorem

variable {G : Type*} [Group G] [hG : IsHamiltonian G]


section commutator_lemmas

variable (x y : G)

lemma conj_is_zpow : ∃ n : ℤ, y * x * y⁻¹ = x ^ n :=
  .imp (fun _ => symm) $ by
    rw [← mem_closure_singleton]
    apply hG.subgroups_normal _ |>.conj_mem
    simp

lemma comm_in_zpowers_left : ⁅x, y⁆ ∈ zpowers x := by
  have ⟨n, hn⟩ := conj_is_zpow (x := x⁻¹) (y := y)
  convert_to x * (y * x⁻¹ * y⁻¹) ∈ _
  . group
  use 1 - n
  rw [hn]; group

lemma comm_in_zpowers_right : ⁅x, y⁆ ∈ zpowers y := by
  rw [← inv_mem_iff, commutatorElement_inv]
  apply comm_in_zpowers_left

lemma comm_is_zpow_left : ∃ n : ℤ, ⁅x, y⁆ = x^n :=
  .imp (fun _ => symm) $ mem_zpowers_iff.mp $ comm_in_zpowers_left x y

lemma comm_is_zpow_right : ∃ n : ℤ, ⁅x, y⁆ = y^n :=
  .imp (fun _ => symm) $ mem_zpowers_iff.mp $ comm_in_zpowers_right x y

@[simp] lemma comm_left : Commute ⁅x, y⁆ x :=
  let ⟨n, h⟩ := comm_is_zpow_left x y
  h ▸ Commute.zpow_self x n

@[simp]
lemma comm_right : Commute ⁅x, y⁆ y :=
  let ⟨n, h⟩ := comm_is_zpow_right x y
  h ▸ Commute.zpow_self y n


lemma comm_inv_left : ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  convert_to x⁻¹ * (y * x * y⁻¹) = (y * x * y⁻¹) * x⁻¹
  . group
  . group

  have ⟨n, h⟩ := conj_is_zpow x y
  exact h ▸ Commute.self_zpow .. |>.inv_left

lemma comm_inv_right : ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
  rw [← commutatorElement_inv, comm_inv_left, commutatorElement_inv]

lemma comm_pow_left : ∀ (n : ℕ), ⁅x^n, y⁆ = ⁅x, y⁆^n
  | 0     => by simp
  | n + 1 => by
    simp_rw [pow_succ']
    rw [← comm_pow_left n, commutatorElement_def (x^n) y,
      ← mul_assoc, ← mul_assoc, ← mul_assoc,
      comm_left x y |>.pow_right n |>.eq]
    group

lemma comm_pow_right (n : ℕ) : ⁅x, y^n⁆ = ⁅x, y⁆^n := by
  rw [← commutatorElement_inv, comm_pow_left, ← inv_pow, commutatorElement_inv]

lemma comm_zpow_left (n : ℤ) : ⁅x^n, y⁆ = ⁅x, y⁆^n := by
  induction n using Int.negInduction with
  | nat n | neg n => simp [comm_inv_left, comm_pow_left]

lemma comm_zpow_right (n : ℤ) : ⁅x, y^n⁆ = ⁅x, y⁆^n := by
  rw [← commutatorElement_inv, comm_zpow_left, ← inv_zpow, commutatorElement_inv]


lemma pow_mul_distrib_comm :
    ∀ (n : ℕ), (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ n.choose 2
  | 0     => by simp
  | n + 1 => by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    simp_rw [pow_succ', pow_add]
    rw [pow_mul_distrib_comm n, ← comm_pow_right y x n]
    simp_rw [← mul_assoc, mul_assoc x _ _]
    rw [mul_right_inj, mul_left_inj]
    conv_rhs =>
      rw [mul_assoc, ← comm_left y (x^n) |>.pow_right n |>.eq, ← mul_assoc]
    rw [mul_left_inj, ← inv_inj, ← inv_inj]
    conv_rhs =>
      rw [mul_inv_rev, mul_inv_rev, ← comm_inv_left, ← comm_inv_right]
    group

end commutator_lemmas


section noncommutative

lemma exists_noncommutative : ∃ x y : G, ¬ Commute x y := by
  simpa using hG.anabelian

set_option linter.unusedVariables false in
lemma finite_order_of_noncommutative : ∀ {x y : G} (h : ¬ Commute x y),
    IsOfFinOrder ⁅x, y⁆ ∧ IsOfFinOrder x ∧ IsOfFinOrder y := by
  suffices ∀ {x y : G}, ¬ Commute x y → IsOfFinOrder ⁅x, y⁆ ∧ IsOfFinOrder x from
    fun x y h => ⟨this h |>.1, this h |>.2, this (h ∘ .symm) |>.2⟩
  intro x y h
  rw [← commutatorElement_eq_one_iff_commute] at h
  have ⟨n', hn'⟩ := comm_is_zpow_left x y
  have n'_nz : n' ≠ 0 := by rintro rfl; rw [zpow_zero] at hn'; contradiction
  have h : ⁅x, y⁆ ^ n' = 1 := by
    rw [← comm_zpow_left, ← hn', commutatorElement_eq_one_iff_commute]
    apply comm_right
  constructor <;> rw [isOfFinOrder_iff_zpow_eq_one]
  . use n'
  . use n' ^ 2, by simpa
    rw [pow_two, zpow_mul, ← hn', h]

lemma lift_to_prime_order (x y : G) {p : ℕ} (hp : p.Prime) (ho : orderOf ⁅x, y⁆ = p)
  (ox : IsOfFinOrder x) :
    ∃ x' : G,
      orderOf ⁅x', y⁆ = p ∧ IsOfFinOrder x' ∧
      ∃ n : ℕ, orderOf x' = p ^ (n + 1) := by
  have ⟨b, ox', b_ndvd⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd $
    multiplicity.finite_nat_iff.mpr ⟨hp.ne_one, ox.orderOf_pos⟩
  have b_nz : b ≠ 0 := fun h => h ▸ b_ndvd $ dvd_zero _

  let x' := x ^ b
  suffices orderOf ⁅x', y⁆ = p ∧ ∃ n, orderOf x' = p ^ n by
    rcases this with ⟨o₁, n, hn⟩
    refine ⟨x', o₁, ox.pow, n - 1, ?_⟩
    suffices n ≠ 0 by convert hn; omega
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hn
    rw [hn, commutatorElement_one_left, orderOf_one] at o₁
    exact hp.one_lt.ne o₁
  simp only [x', comm_pow_left, orderOf_pow' _ b_nz]
  constructor
  . rw [ho, hp.coprime_iff_not_dvd.mpr b_ndvd |>.gcd_eq_one, Nat.div_one]
  . rw [Nat.gcd_eq_right (Dvd.intro_left _ ox'.symm), ox',
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero b_nz)]
    simp

set_option linter.unusedVariables false in
lemma exists_prime_order (x y : G) (h : ¬ Commute x y) :
  ∃ (x' y' : G) (p : ℕ) (hp : p.Prime) (m n : ℕ),
    orderOf ⁅x', y'⁆ = p ∧ orderOf x' = p ^ (m + 1) ∧ orderOf y' = p ^ (n + 1) := by
  have ⟨oc, ox, oy⟩ := finite_order_of_noncommutative h

  let a := orderOf ⁅x, y⁆
  have a_pos : 0 < a := oc.orderOf_pos
  obtain ⟨p, p_prime, p_dvd⟩ := a.exists_prime_and_dvd $ by
    rwa [← commutatorElement_eq_one_iff_commute, ← orderOf_eq_one_iff] at h

  let x' := x ^ (a / p)
  have o' : orderOf ⁅x', y⁆ = p := by
    rw [comm_pow_left, orderOf_pow_of_dvd ?hn (Nat.div_dvd_of_dvd p_dvd),
      Nat.div_div_self p_dvd a_pos.ne']
    case hn =>
      rw [Nat.div_ne_zero_iff_of_dvd p_dvd]
      exact ⟨a_pos.ne', p_prime.ne_zero⟩

  have ox' : IsOfFinOrder x' := ox.pow
  clear_value x'; clear! x; rename' x' => x, o' => o, ox' => ox

  have ⟨x', o', ox', n, hx⟩ := lift_to_prime_order x y p_prime o ox
  clear! x; rename' x' => x, o' => o, ox' => ox

  rw [← commutatorElement_inv, orderOf_inv] at o

  have ⟨y', o', oy', m, hy⟩ := lift_to_prime_order y x p_prime o oy
  clear! y; rename' y' => y, o' => o, oy' => oy

  use y, x, p, p_prime, m, n, o, hy, hx

omit hG in
lemma decomp_of_prime_order {x y : G} (hy : y ∈ zpowers x) {p : ℕ} (hp : p.Prime) {n : ℕ}
  (ox : orderOf x = p ^ (n + 1)) (oy : orderOf y = p) :
    ∃ r : ℕ, y = x ^ (r * p ^ n) ∧ p.Coprime r := by
  have y_ne : y ≠ 1 := fun h => hp.ne_one.symm $ by rwa [h, orderOf_one] at oy
  have ⟨a, ha⟩ := mem_zpowers_iff.mp hy

  let a' := Int.natMod a ↑(p ^ (n + 1))
  have ha' : x ^ a' = y := by
    dsimp only [a']
    rw [← ha, ← zpow_mod_orderOf, ox, Int.natMod, ← zpow_natCast, Int.toNat_of_nonneg]
    apply Int.emod_nonneg
    simpa using hp.ne_zero
  clear_value a'; clear! a; rename' a' => a, ha' => ha
  subst ha

  have a_nz : a ≠ 0 := fun h => y_ne $ by rw [h, pow_zero]
  have a_gcd : (p ^ (n + 1)).gcd a = p ^ n := by
    rw [orderOf_pow' _ a_nz, ox, Nat.div_eq_iff_eq_mul_left ?gcd_pos ?gcd_dvd] at oy
    nth_rw 1 [pow_succ'] at oy
    rw [Nat.mul_right_inj hp.ne_zero] at oy
    exact oy.symm
    case gcd_pos => apply Nat.gcd_pos_of_pos_right; omega
    case gcd_dvd => apply Nat.gcd_dvd_left
  have dvd_a : p ^ n ∣ a := a_gcd ▸ Nat.gcd_dvd_right ..

  use a / p ^ n
  constructor
  . rwa [Nat.div_mul_cancel]
  rw [Nat.coprime_iff_gcd_eq_one]
  convert Nat.gcd_div (pow_dvd_pow p n.le_succ) dvd_a
  . rw [Nat.pow_div n.le_succ hp.pos, Nat.succ_eq_add_one, Nat.add_sub_cancel_left, pow_one]
  rw [a_gcd, Nat.div_self]
  exact pow_pos hp.pos _


open Nat in
lemma canonicalise_of_prime_order {x y : G} {p : ℕ} (hp : p.Prime) {m n : ℕ}
  (o : orderOf ⁅x, y⁆ = p) (ox : orderOf x = p ^ (m + 1)) (oy : orderOf y = p ^ (n + 1)) :
  ∃ x' y' : G,
    orderOf ⁅x', y'⁆ = p ∧
    orderOf x' = p ^ (m + 1) ∧ ⁅x', y'⁆ = x' ^ (p ^ m) ∧
    orderOf y' = p ^ (n + 1) ∧ ⁅x', y'⁆ = y' ^ (p ^ n) := by
  -- have hc : ⁅x, y⁆ ≠ 1 := fun h => hp.ne_one.symm $ by rwa [h, orderOf_one] at o

  have ⟨a, ha, a_cp⟩ := decomp_of_prime_order (comm_in_zpowers_left x y) hp ox o
  have ⟨b, hb, b_cp⟩ := decomp_of_prime_order (comm_in_zpowers_right x y) hp oy o

  obtain ⟨a', ha'⟩ := exists_mul_emod_eq_one_of_coprime a_cp.symm hp.one_lt
  obtain ⟨b', hb'⟩ := exists_mul_emod_eq_one_of_coprime b_cp.symm hp.one_lt
  have ma : a' * a ≡ 1 [MOD p] := by rwa [← mod_eq_of_lt hp.one_lt, mul_comm] at ha'
  have mb : b' * b ≡ 1 [MOD p] := by rwa [← mod_eq_of_lt hp.one_lt, mul_comm] at hb'
  have a'_cp : p.Coprime a' := coprime_of_mul_modEq_one _ ma |>.symm
  have b'_cp : p.Coprime b' := coprime_of_mul_modEq_one _ mb |>.symm
  have a'_nz : a' ≠ 0 := fun h => hp.ne_one $ p.coprime_zero_right.mp $ h ▸ a'_cp
  have b'_nz : b' ≠ 0 := fun h => hp.ne_one $ p.coprime_zero_right.mp $ h ▸ b'_cp

  use x ^ b', y ^ a'
  rw [comm_pow_left, comm_pow_right]
  constructor
  . rw [← pow_mul, orderOf_pow' _ (mul_ne_zero a'_nz b'_nz), o,
      coprime_iff_gcd_eq_one.mp (a'_cp.mul_right b'_cp), Nat.div_one]
  rw [orderOf_pow' _ b'_nz, orderOf_pow' _ a'_nz,
    ox, coprime_iff_gcd_eq_one.mp (b'_cp.pow_left _), Nat.div_one,
    oy, coprime_iff_gcd_eq_one.mp (a'_cp.pow_left _), Nat.div_one]
  refine ⟨rfl, ha ▸ ?_, rfl, hb ▸ ?_⟩ <;> simp_rw [← pow_mul, pow_eq_pow_iff_modEq]
  . rw [ox, pow_succ']
    convert_to a' * a * b' * p ^ m ≡ 1 * b' * p ^ m [MOD p * p ^ m]; ring1; ring1
    exact .mul_right' _ $ .mul_right _ ma
  . rw [oy, pow_succ']
    convert_to b' * b * a' * p ^ n ≡ 1 * a' * p ^ n [MOD p * p ^ n]; ring1; ring1
    exact .mul_right' _ $ .mul_right _ mb


lemma embeds_quaternions : ∃ S : Subgroup G, Nonempty (Q₈ ≃* S) := by
  have ⟨x, y, hxy⟩ := hG.exists_noncommutative
  obtain ⟨i, j, p, hp, m, n, o, oi, oj⟩ := exists_prime_order x y hxy
  clear hxy x y

  haveI hpI : Fact p.Prime := ⟨hp⟩

  wlog hnm : n ≤ m generalizing n m i j
  . exact this j i n m (by rw [← commutatorElement_inv, orderOf_inv, o]) oj oi (by omega)

  induction n using Nat.strong_induction_on generalizing i j with | h n ih =>

  have ⟨i', j', o', oi', hi', oj', hj'⟩ := canonicalise_of_prime_order hp o oi oj
  clear! i j; rename' i' => i, j' => j, o' => o, oi' => oi, hi' => hi, oj' => oj, hj' => hj

  let j' := i⁻¹ ^ (p ^ (m - n)) * j
  have j'_pow : j' ^ (p ^ n) = _ := pow_mul_distrib_comm ..
  rw [← pow_mul, pow_sub_mul_pow p hnm, inv_pow, ← hi, ← hj, inv_mul_cancel, one_mul,
    comm_pow_right, ← pow_mul, comm_inv_right, commutatorElement_inv] at j'_pow

  by_cases hdvd : p ∣ p ^ (m - n) * (p ^ n).choose 2
  case pos =>
    nth_rewrite 1 [← o] at hdvd
    rw [orderOf_dvd_iff_pow_eq_one.mp hdvd] at j'_pow
    have ⟨n', oj'⟩ := exists_orderOf_eq_prime_pow_iff.mpr ⟨_, j'_pow⟩
    have o' : orderOf ⁅i, j'⁆ = p := by
      dsimp only [j']
      rw [commutatorElement_mul_right,
        Commute.refl i |>.inv_right.pow_right (p ^ (m - n)) |>.commutator_eq,
        one_mul]
      erw [MulAut.conj _ |>.orderOf_eq, o]
    have n'_le : n' ≤ n := by
      rw [← Nat.pow_dvd_pow_iff_le_right hp.one_lt, ← oj',
          orderOf_dvd_iff_pow_eq_one, j'_pow]
    cases' n' with n'
    . rw [pow_zero, orderOf_eq_one_iff] at oj'
      rw [oj', commutatorElement_one_right, orderOf_one] at o'
      exact absurd o'.symm hp.ne_one
    exact ih n' (by omega) i j' o' oi oj' (by omega)
  clear! ih j'

  obtain rfl : n = m := by
    refine le_antisymm hnm $ Nat.le_of_sub_eq_zero ?_
    contrapose! hdvd with sub_nz
    exact dvd_mul_of_dvd_left (dvd_pow_self _ sub_nz) _
  rw [tsub_self, pow_zero, one_mul] at hdvd

  cases' n with n
  . rw [pow_zero, pow_one] at hi
    rw [← hi, comm_right i j |>.commutator_eq, orderOf_one] at o
    exact absurd o hp.ne_one.symm

  clear hpI
  obtain rfl : p = 2 := hp.eq_two_or_odd'.resolve_right $ by
    contrapose! hdvd with p_odd
    rw [Nat.choose_two_right, Nat.mul_div_assoc _ ?H]
    exact dvd_pow_self _ n.succ_ne_zero |>.mul_right _
    case H =>
      rw [← even_iff_two_dvd, Nat.even_sub (Nat.one_le_pow _ _ hp.pos),
        Nat.even_pow' n.succ_ne_zero]
      simpa using p_odd

  rw [← even_iff_two_dvd, Nat.choose_two_right, mul_comm,
    Nat.mul_div_assoc _ (dvd_pow_self _ n.succ_ne_zero), Nat.even_mul,
    not_or, pow_succ, Nat.mul_div_cancel _ zero_lt_two,
    Nat.even_pow] at hdvd
  simp only [even_two, true_and] at hdvd
  obtain rfl : n = 0 := of_not_not hdvd.2

  clear hp hnm hdvd
  norm_num at *

  use (⊤ : Subgroup Q₈).map (quaternionHom oi hi hj)
  exact ⟨Subgroup.topEquiv.symm.trans $ Subgroup.equivMapOfInjective ⊤ _ $
    quaternionHom_injective ..⟩

end noncommutative







-- Normal subgroups form a modular lattice.
-- Since they're *all* normal that works out well for us
protected instance subgroup_modular_lattice :
    IsModularLattice (Subgroup G) where
  sup_inf_le_assoc_of_le {x} y z h := le_of_eq ∘ symm $ by
    rw [← SetLike.coe_set_eq]
    show _ = ↑(x ⊔ y) ⊓ ↑z
    simp_rw [Subgroup.normal_mul]
    apply Subgroup.mul_inf_assoc (h := h)


section abelian_part

variable {Q : Subgroup G} (ϕ : Q₈ ≃* Q)

private abbrev Q₈.a : ZMod (2 * 2) → Q₈ := QuaternionGroup.a
private abbrev Q₈.xa : ZMod (2 * 2) → Q₈ := QuaternionGroup.xa
private abbrev i := Q₈.a 1
private abbrev j := Q₈.xa 0


-- this lemma is just kinda hanging out here.
lemma comm_cases_of_order_dvd_four (x y : G) (ho : x ^ 4 = 1) :
    ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = x ^ 2 := by
  obtain ⟨n, hn⟩ := conj_is_zpow x⁻¹ y
  by_cases hx : x = 1
  . exact .inl $ hx ▸ commutatorElement_one_left y
  have n_nz : n ≠ 0 := fun h =>
    hx $ by rwa [h, zpow_zero, mul_inv_eq_one, mul_right_eq_self, inv_eq_one] at hn

  have h := congrArg orderOf hn
  have o_conj : orderOf x⁻¹ = orderOf (y * x⁻¹ * y⁻¹) :=
    MulAut.conj _ |>.orderOf_eq _ |>.symm
  rw [← o_conj, orderOf_zpow' _ n_nz, eq_comm, Nat.div_eq_self] at h

  rw [show 4 = 2 ^ 2 by norm_num] at ho
  obtain ⟨k, ho'⟩ := exists_orderOf_eq_prime_pow_iff.mpr ⟨2, ho⟩
  have hk : 0 < k ∧ k ≤ 2 := by
    constructor
    . rw [zero_lt_iff]; rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at ho'
      exact hx ho'
    . exact Nat.pow_dvd_pow_iff_le_right one_lt_two |>.mp <| ho' ▸ orderOf_dvd_of_pow_eq_one ho
  rw [orderOf_inv, ho'] at h

  replace h := h.resolve_left $ pow_ne_zero k $ by norm_num
  rw [Int.gcd_eq_one_iff_coprime, Nat.cast_pow, IsCoprime.pow_left_iff hk.1] at h
  rw_mod_cast [Int.prime_two.coprime_iff_not_dvd] at h

  rw [← mul_right_inj x] at hn
  simp_rw [← mul_assoc] at hn
  rw [inv_zpow', ← zpow_one_add, add_comm] at hn

  rw [← even_iff_two_dvd, ← even_neg, ← Int.even_add_one] at h
  rcases h with ⟨m, hm⟩
  rw [commutatorElement_def, hn, hm, ← two_mul]

  cases hk
  interval_cases k
  . rw [zpow_mul]; convert Or.inl $ one_zpow _
    rw [pow_one] at ho'
    rw_mod_cast [← ho']
    apply pow_orderOf_eq_one
  . rw [← zpow_mod_orderOf, ho', pow_two, Nat.cast_mul,
      show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num, Int.mul_emod_mul_of_pos _ _ two_pos]
    cases' Int.emod_two_eq_zero_or_one m with h h <;> rw [h]
    . left; simp
    . right; norm_cast


include Q ϕ

local notation "C" => centralizer (G := G) Q

omit hG in
lemma centralize_of_comm_generators (x : G) :
    ⁅(ϕ i : G), x⁆ = 1 ∧ ⁅(ϕ j : G), x⁆ = 1 → x ∈ C := by
  simp_rw [commutatorElement_eq_one_iff_commute]
  rintro ⟨hi, hj⟩

  intro y hy
  lift y to Q using hy
  induction y using transport_var ϕ with | _ y =>

  haveI : Fact (0 < 2 * 2) := ⟨by norm_num⟩
  cases' y with y y
  . rw [← ZMod.natCast_zmod_val y, ← QuaternionGroup.a_one_pow, map_pow]
    exact hi.pow_left y.val
  . rw [← zero_add y, ← QuaternionGroup.xa_mul_a 0 y, map_mul]
    rw [← ZMod.natCast_zmod_val y, ← QuaternionGroup.a_one_pow, map_pow]
    exact hj.mul_left $ hi.pow_left y.val


lemma group_eq_quaternion_mul_centraliser : Q ⊔ C = ⊤ := by
  ext x
  suffices ∃ q : Q, ↑q * x ∈ C by
    rcases this with ⟨q, h⟩
    have := mul_mem_sup q⁻¹.2 h
    simpa using this

  cases' comm_cases_of_order_dvd_four (ϕ i : G) x
    (by transport_group ϕ.symm) with hi hi <;>
  cases' comm_cases_of_order_dvd_four (ϕ j : G) x
    (by transport_group ϕ.symm) with hj hj <;>
  [use 1 ; use ϕ i ; use ϕ j ; use ϕ (i * j)]
  all_goals
    apply centralize_of_comm_generators ϕ
    simp_rw [commutatorElement_mul_right, hi, hj, commutatorElement_def]
    transport_group ϕ.symm

omit hG in
lemma comm_ϕ (q : Q₈) (g : C) : Commute (ϕ q : G) g :=
  g.2 (ϕ q) (by simp)


lemma not_order_four_in_centralizer (g : C) :
    ¬ orderOf g = 4 := by
  have ci := comm_ϕ ϕ i g
  have cj := comm_ϕ ϕ j g
  have : ⁅(ϕ j * g : G), (ϕ i : G)⁆ = ϕ (.a 2) := by
    rw [← commutatorElement_inv, ← comm_inv_left, commutatorElement_mul_right,
      ci.inv_left.commutator_eq, commutatorElement_def]
    transport_group ϕ.symm

  intro ho
  obtain h | h := comm_cases_of_order_dvd_four (ϕ j * g : G) (ϕ i) $ by
    convert cj.mul_pow _
    rw_mod_cast [show g ^ 4 = 1 from ho ▸ pow_orderOf_eq_one g, mul_one]
    transport_group ϕ.symm
  all_goals rw [this] at h
  . revert h; transport_group ϕ.symm

  suffices (g : G) ^ 2 = 1 from
    pow_ne_one_of_lt_orderOf two_ne_zero (by rw_mod_cast [ho]; norm_num) this
  rw [cj.mul_pow] at h
  convert mul_right_eq_self.mp $ h.symm.trans _
  transport_group ϕ.symm


instance quaternion_centralizer.commutative :
    Subgroup.IsCommutative C where
  is_comm.comm a b := by
    by_contra h
    haveI hC : IsHamiltonian C :=
      { subgroups_normal := fun S => by
          convert hG.subgroups_normal (S.map (C).subtype) |>.comap (C).subtype
          simp only [comap_map_eq_self_of_injective, Subgroup.coeSubtype, Subtype.coe_injective]
        anabelian := fun hc => h $ hc a b }

    obtain ⟨S, ⟨ψ⟩⟩ := hC.embeds_quaternions
    refine not_order_four_in_centralizer ϕ (ψ i) (Eq.trans ?_ (show orderOf i = 4 from ?_))
    . rw [orderOf_coe, ψ.orderOf_eq]
    rw [show 4 = 2 ^ 2 by norm_num]
    apply orderOf_eq_prime_pow <;> decide


lemma quaternion_centralizer.is_torsion :
    Monoid.IsTorsion C := by
  intro g
  rw [← (C).toSubmonoid.isOfFinOrder_coe]

  have : ¬ Commute (ϕ i : G) (ϕ j * g) := by
    by_contra h
    replace h := h.mul_right $ .inv_right $ comm_ϕ ϕ i g
    rw [mul_inv_cancel_right] at h
    replace h := h.commutator_eq
    rw [commutatorElement_def] at h
    revert h; transport_group ϕ.symm

  replace this := finite_order_of_noncommutative this |>.2.2

  rw [← one_mul g, coe_mul, coe_one, ← inv_mul_cancel (ϕ j : G), mul_assoc]
  refine Commute.isOfFinOrder_mul ?_ ?_ this
  . exact Commute.refl (ϕ j : G) |>.mul_right (comm_ϕ ϕ j g) |>.inv_left
  rw [isOfFinOrder_inv_iff, (Q).toSubmonoid.isOfFinOrder_coe]
  exact ϕ.toMonoidHom.isOfFinOrder $ orderOf_pos_iff.mp $ orderOf_pos j


def odd_component : Subgroup C where
  carrier := {g : C | Odd (orderOf g)}
  one_mem' := by simp
  inv_mem' := by simp
  mul_mem' := by
    haveI := quaternion_centralizer.commutative ϕ
    intro a b hm hn
    simp only [Set.mem_setOf_eq, not_not] at *
    have hh := hm.mul hn
    simp only [← Nat.not_even_iff_odd, even_iff_two_dvd] at hh ⊢
    exact fun h => hh $ h.trans (Commute.all a b).orderOf_mul_dvd_mul_orderOf

def two_primary_component : Subgroup C :=
  haveI := quaternion_centralizer.commutative ϕ
  CommGroup.primaryComponent C 2

local notation "O" => odd_component ϕ
local notation "E" => two_primary_component ϕ


lemma mem_two_primary_iff {x : C} :
    x ∈ E ↔ x = 1 ∨ orderOf x = 2 where
  mpr := by rintro (rfl | h) <;> [ use 0 ; use 1 ] <;> simp [*]
  mp := by
    rintro ⟨n, hn⟩
    suffices n < 2 by
      interval_cases n
      . left; rw [← orderOf_eq_one_iff, hn, pow_zero]
      . right; rw [hn, pow_one]
    by_contra! h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
    have := orderOf_pow' x $ show 2 ^ k ≠ 0 from (pow_pos two_pos _).ne'
    rw [hn, Nat.gcd_eq_right (pow_dvd_pow 2 le_add_self), pow_add,
      Nat.mul_div_cancel _ (pow_pos two_pos _)] at this
    exact not_order_four_in_centralizer ϕ _ this

lemma mem_two_primary' (x : E) :
    x ^ 2 = 1 :=
  suffices (x : C) ^ 2 = 1 by exact_mod_cast this
  show x.val ^ 2 = 1 from
    mem_two_primary_iff ϕ |>.mp x.2 |>.elim
      (fun h => by rw [h, one_pow])
      (fun h => by rw [← h, pow_orderOf_eq_one])


instance two_primary.comm_group :
    CommGroup E :=
  haveI := quaternion_centralizer.commutative ϕ
  inferInstance

-- two cheers for zmodModule!!
instance two_primary.vector_space :
    Module (ZMod 2) (Additive E) :=
  AddCommGroup.zmodModule $ mem_two_primary' ϕ


open Nat in
lemma quaternion_centralizer.decomp :
    IsCompl E O where
  disjoint := by
    rw [disjoint_def]
    intro x he ho
    rw [mem_two_primary_iff] at he
    rcases he with rfl | he
    . rfl
    . simp [odd_component, he, show ¬ Odd 2 by decide] at ho

  codisjoint := by
    haveI := commutative ϕ
    rw [codisjoint_iff, eq_top_iff']
    intro x

    let n := orderOf x
    have hn : 0 < n := is_torsion ϕ x |>.orderOf_pos

    let o := ord_compl[2] n
    let e := ord_proj[2] n

    have o_pos : 0 < o := ord_compl_pos _ hn.ne'
    have e_pos : 0 < e := ord_proj_pos ..

    have two_ndvd : ¬ 2 ∣ o := not_dvd_ord_compl prime_two hn.ne'

    have he : orderOf (x ^ o) = e := by
      rw [orderOf_pow' x o_pos.ne', gcd_eq_right (n.ord_compl_dvd _)]
      exact Nat.div_eq_of_eq_mul_left o_pos $ symm $
        n.ord_proj_mul_ord_compl_eq_self _
    have ho : orderOf (x ^ e) = o := by
      rw [orderOf_pow' x e_pos.ne', Nat.gcd_eq_right (n.ord_proj_dvd _)]

    have hfe : IsOfFinOrder (x ^ o) := orderOf_pos_iff.mp (he ▸ e_pos)
    have hfo : IsOfFinOrder (x ^ e) := orderOf_pos_iff.mp (ho ▸ o_pos)

    let a := o.gcdA e
    let b := o.gcdB e

    have hab : (1 : ℤ) = o * a + e * b := by
      convert o.gcd_eq_gcd_ab e
      norm_cast
      rw [eq_comm, ← coprime_iff_gcd_eq_one]
      apply prime_two.coprime_pow_of_not_dvd two_ndvd

    have hea : Int.gcd e a = 1 := Nat.dvd_one.mp $ Int.gcd_dvd_iff.mpr $
      ⟨b, o, Int.mul_comm o a ▸ hab.trans (add_comm ..)⟩
    have hob : Int.gcd o b = 1 := Nat.dvd_one.mp $ Int.gcd_dvd_iff.mpr $
      ⟨a, e, Int.mul_comm e b ▸ hab⟩

    rw [mem_sup]
    refine ⟨
      (x ^ o) ^ a, ?_, (x ^ e) ^ b, ?_, ?_⟩
    . exact ⟨n.factorization 2, by rw [hfe.orderOf_zpow, he, hea, Nat.div_one]⟩
    . show Odd $ orderOf _
      rw [hfo.orderOf_zpow, ho, hob, Nat.div_one,
        ← not_even_iff_odd, even_iff_two_dvd]; assumption
    . rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
        ← zpow_add, ← hab, zpow_one]


private abbrev n1 : Q₈ := Q₈.a 2

omit hG

lemma orderOf_n1 :
    orderOf (ϕ n1 : G) = 2 := by
  rw [orderOf_coe, ϕ.orderOf_eq]
  apply orderOf_eq_prime <;> decide

lemma zpowers_of_n1 (x : G) :
    x ∈ zpowers (ϕ n1 : G) ↔ x = 1 ∨ x = ϕ n1 where
  mpr := by rintro (rfl | rfl) <;> [ use 0 ; use 1 ] <;> simp
  mp := by
    intro hx
    lift x to zpowers (ϕ n1 : G) using hx
    let f := groupExp (orderOf_n1 ϕ)
    induction x using (ofAdd.trans f.toEquiv).forall_congr_right.mp with | _ x =>
    simp [f, groupExp_apply]; revert x; transport_group ϕ.symm

lemma quaternion_inf_centralizer :
    Q ⊓ C = zpowers (ϕ n1 : G) := by
  ext x
  rw [zpowers_of_n1, mem_inf, mem_centralizer_iff, Subtype.forall']
  erw [← ϕ.forall_congr_right, MulEquiv.toEquiv_eq_coe]
  constructor
  . rintro ⟨hq, hc⟩
    lift x to Q using hq
    induction x using transport_var ϕ with | _ x =>
    revert x hc; transport_group ϕ.symm
  . rintro (rfl | rfl) <;>
      [ use one_mem _ ; use SetLike.coe_mem _ ] <;>
      transport_group ϕ.symm

include hG

@[simps]
def low_neg_one : E where
  val.val := ϕ n1
  val.property := by
    refine mem_inf (p := Q) |>.mp ?_ |>.2
    rw [quaternion_inf_centralizer ϕ]
    simp only [mem_zpowers]
  property := by
    use 1
    rw [pow_one, ← orderOf_coe, coe_mk, orderOf_n1]

local notation "lo_n1" => low_neg_one ϕ

lemma zpowers_n1 :
    zpowers (ϕ n1 : G) =
    (zpowers lo_n1 |>.map (E).subtype |>.map (C).subtype) := by
  ext x; simp


def two_primary_submodule_equiv :
    Submodule (ZMod 2) (Additive E) ≃o Subgroup E :=
  AddSubgroup.toZModSubmodule 2 |>.symm.trans AddSubgroup.toSubgroup'

local notation "Ee" => two_primary_submodule_equiv ϕ

lemma exists_isCompl : ∃ s, IsCompl (zpowers lo_n1) (Ee s) :=
  have ⟨a, ha⟩ := Submodule.exists_isCompl $ (Ee).symm $ zpowers lo_n1
  ⟨a, by convert ha.map Ee⟩

section structure_theorem_aux

-- it seems like you can't use notation in a variable command
-- fair enough i guess but the error message is not exactly transparent...
-- (at time of writing)
variable (E' : Subgroup (two_primary_component ϕ)) (hE' : IsCompl (zpowers $ low_neg_one ϕ) E')

def parts : Fin 3 → Subgroup G :=
  ![ Q
   , E'.map (E).subtype |>.map (C).subtype
   , (O).map (C).subtype]

local notation "cover" => parts ϕ E'

-- i don't really like this... but oh well
lemma c0 : cover 0 = Q := rfl
lemma c1 : cover 1 = (E'.map (E).subtype).map (C).subtype := rfl
lemma c2 : cover 2 = (O).map (C).subtype := rfl

lemma hcomm i j (hij : i ≠ j)
  x y (hx : x ∈ cover i) (hy : y ∈ cover j) :
    Commute x y := by
  haveI := quaternion_centralizer.commutative ϕ

  wlog hij' : i < j generalizing i j x y
  . exact this j i hij.symm y x hy hx (by omega) |>.symm
  rename' hij' => hij
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk] at * <;>
    norm_num at hij <;>
    (try lift x to C using map_subtype_le _ hx) <;>
    (try lift y to C using map_subtype_le _ hy)
  all_goals first
  | exact y.2 x hx
  | rw [commute_iff_eq]; exact_mod_cast Commute.all x y

lemma disjoint_c12' : Disjoint (E'.map (E).subtype) O :=
  quaternion_centralizer.decomp ϕ |>.disjoint.mono_left $ map_subtype_le _


lemma disjoint_c12 : Disjoint (cover 1) (cover 2) := by
  have := disjoint_iff.mp $ disjoint_c12' ϕ E'
  rw [disjoint_iff, c1, c2, ← map_inf_eq, map_eq_bot_iff_of_injective] <;>
    first | assumption | apply subtype_injective

include hE'

lemma disjoint_n1c1 : Disjoint (zpowers (ϕ n1 : G)) (cover 1) := by
  have := hE'.inf_eq_bot
  rw [disjoint_iff, zpowers_n1 ϕ, c1, ← map_inf_eq, ← map_inf_eq,
    map_eq_bot_iff_of_injective, map_eq_bot_iff_of_injective] <;>
    first | assumption | apply subtype_injective

open Subgroup renaming map_sup → smap_sup

lemma sup_n1c1 :
    zpowers (ϕ n1 : G) ⊔ cover 1 = (E).map (C).subtype := by
  rw [zpowers_n1, c1, ← smap_sup, ← smap_sup, codisjoint_iff.mp hE'.codisjoint, map_subtype_top]

lemma cover_compl :
    IsCompl (cover 0) (cover 1 ⊔ cover 2) where
  disjoint := by
    rw [c0, c1, c2, disjoint_iff, ← smap_sup, ← inf_of_le_right $ map_subtype_le _,
      ← inf_assoc, quaternion_inf_centralizer ϕ, smap_sup, ← disjoint_iff]
    apply (disjoint_n1c1 ϕ E' hE').disjoint_sup_right_of_disjoint_sup_left
    rw [sup_n1c1 ϕ E' hE']
    have := quaternion_centralizer.decomp ϕ |>.inf_eq_bot
    rw [disjoint_iff, ← map_inf_eq, map_eq_bot_iff_of_injective] <;>
      first | assumption | apply subtype_injective
  codisjoint := by
    rw [c0, c1, c2, codisjoint_iff]
    have h := zpowers_n1 ϕ |>.symm.trans_le $ show zpowers (ϕ n1 : G) ≤ Q by
      rintro x ⟨n, rfl⟩
      dsimp only
      rw [← coe_zpow, ← map_zpow]
      apply SetLike.coe_mem
    conv_lhs =>
      conv => arg 1; rw [← sup_of_le_left h]
      rw [sup_assoc]
      arg 2
      simp only [← sup_assoc, ← smap_sup, hE'.sup_eq_top,
        quaternion_centralizer.decomp ϕ |>.sup_eq_top, map_subtype_top]
    exact group_eq_quaternion_mul_centraliser ϕ

def ff := noncommPiCoprod $ hcomm ϕ E'

local notation "f" => ff ϕ E'

-- cool proof using distrib lattice hax
lemma f_inj : Function.Injective f :=
  injective_noncommPiCoprod_of_independent $ by
    rw [CompleteLattice.independent_def']
    intro i
    rw [show {j | j ≠ i} = {i + 1, i + 2} by ext x; revert i x; decide,
      Set.image_pair, sSup_pair]

    have d12 := disjoint_c12 ϕ E'
    have h₀ := cover_compl ϕ E' hE' |>.disjoint
    have h₁ := d12.disjoint_sup_right_of_disjoint_sup_left h₀.symm
    have h₂ : Disjoint (cover 2) (cover 0 ⊔ cover 1) := by
      rw [sup_comm]
      exact d12.symm.disjoint_sup_right_of_disjoint_sup_left (sup_comm .. |>.subst h₀).symm
    fin_cases i; exacts [h₀, h₁, h₂]

lemma f_surj : Function.Surjective f :=
  MonoidHom.range_top_iff_surjective.mp $
    noncommPiCoprod_range.trans $ cover_compl ϕ E' hE' |>.sup_eq_top.congr_right.mp $ by
      rw [← Finset.sup_univ_eq_iSup]
      show ({0, 1, 2} : Finset _).sup _ = _
      simp only [Finset.sup_insert, Finset.sup_singleton]

lemma f_bij : Function.Bijective f := ⟨f_inj _ _ hE', f_surj _ _ hE'⟩


noncomputable def structure_theorem_aux : G ≃* Q × E' × O :=
  MulEquiv.ofBijective f (f_bij _ _ hE') |>.symm.trans <|
  .trans
    { toFun := fun v => (v 0, v 1, v 2)
      invFun := fun (a, b, c) => Fin.cons a $ Fin.cons b $ Fin.cons c (·.elim0)
      left_inv := fun v => funext fun x => by fin_cases x <;> rfl
      right_inv := fun (a, b, c) => rfl
      map_mul' := fun x y => rfl } <|
  MulEquiv.refl _ |>.prodCongr <|
    equiv_map_subtype.trans equiv_map_subtype |>.prodCongr <|
      equiv_map_subtype

end structure_theorem_aux

theorem structure_theorem :
  ∃ E' : Submodule (ZMod 2) (Additive E),
    Nonempty (G ≃* Q × Ee E' × O) :=
  exists_isCompl ϕ |>.imp fun _ hE' => ⟨structure_theorem_aux _ _ hE'⟩

end abelian_part

end structure_theorem

universe u


set_option linter.unusedVariables false in
theorem isHamiltonian_characterisation (G : Type u) [Group G] :
  IsHamiltonian G ↔
  ∃ (E : ModuleCat.{u} (ZMod 2))
    (T : CommGrp.{u}) (hT : ∀ x : T, Odd (orderOf x)),
    Nonempty (G ≃* Q₈ × (Multiplicative E) × T) where
  mp := by
    intro hG
    have ⟨Q, ⟨ϕ⟩⟩ := hG.embeds_quaternions
    have ⟨E', ⟨ψ⟩⟩ := structure_theorem ϕ
    haveI := quaternion_centralizer.commutative ϕ
    refine ⟨.of _ E', .of (odd_component ϕ), fun ⟨x, hx⟩ => by rwa [← orderOf_coe], ⟨?_⟩⟩
    exact ψ.trans <|
      ϕ.symm.prodCongr <| MulEquiv.multiplicativeAdditive _ |>.prodCongr <| .refl _
  mpr := by
    rintro ⟨E, T, hT, ⟨ψ⟩⟩
    constructor
    case anabelian =>
      intro h
      absurd h (ψ.symm (i, 1)) (ψ.symm (j, 1))
      rw [commute_iff_eq]
      transport_group ψ
      simp only [Prod.mk_mul_mk, Prod.mk.injEq, and_true]
      decide
    case subgroups_normal =>
      intro S
      constructor
      intro n hn g
      convert_to ⁅g, n⁆ * n ∈ S
      . group
      refine S.mul_mem ?_ hn

      induction n using transport_var ψ.symm with | _ n =>
      induction g using transport_var ψ.symm with | _ g =>
      rw [← map_commutatorElement]
      rw [← mem_map_equiv] at hn ⊢
      set S' := map ψ.toMonoidHom S
      clear_value S'; clear S; rename' S' => S

      rcases n with ⟨xn, yn⟩
      rcases g with ⟨xg, yg⟩

      show (⁅xg, xn⁆, ⁅yg, yn⁆) ∈ S
      rw [Commute.all yg yn |>.commutator_eq]
      obtain hc | ⟨hc, hns⟩ : ⁅xg, xn⁆ = 1 ∨ ⁅xg, xn⁆ = n1 ∧ xn ^ 2 = n1 := by
        clear hn; revert xg xn; decide
      . exact hc ▸ one_mem S

      rcases yn with ⟨yn, zn⟩
      rw [← Prod.mk_one_one, hc]
      convert S.pow_mem hn (2 * orderOf zn) <;> simp only [Prod.pow_mk]
      . have ⟨k, ho⟩ := hT zn
        rw [ho, pow_mul, hns, pow_add, pow_one, pow_mul,
          show n1 ^ 2 = 1 by decide, one_pow, one_mul]
      . show 0 = (2 * orderOf zn) • toAdd yn
        rw [← smul_smul, ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
      . rw [pow_mul', pow_orderOf_eq_one, one_pow]

end Group.IsHamiltonian
