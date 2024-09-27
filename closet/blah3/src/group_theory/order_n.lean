import algebra.group.basic
import algebra.category.Group.basic
import algebra.category.Module.basic
import category_theory.skeletal

import group_theory.specific_groups.cyclic
import group_theory.specific_groups.quaternion

/-
import group_theory.specific_groups.quaternion
import group_theory.order_of_element

import group_theory.submonoid.centralizer

import group_theory.noncomm_pi_coprod
import group_theory.torsion
-/

-- import data.set.pointwise

-- import group_theory.commutator

-- import ring_theory.multiplicity

-- import data.nat.choose.basic

-- import data.zmod.basic
import data.fin.basic

import tactic.equiv_rw

import logic.equiv.transfer_instance

import category_theory.full_subcategory

open subgroup
open category_theory



-- frequently we use a nonstandard multiplication on fin n
-- FIXME do we want to use a different "canonical set of size n"
-- (e.g. finset.range n) to avoid this
local attribute [-instance] fin.has_mul
local attribute [instance] category_theory.is_isomorphic_setoid
local attribute [instance] category_theory.full_subcategory.category






section equiv_functor_instance

instance equiv_functor_group : equiv_functor group :=
{ map := λ α β e, @equiv.group _ _ e.symm, }

end equiv_functor_instance


def Group.of_mul_equiv {X Y : Type*} [group X] [group Y] (e : X ≃* Y) :
  Group.of X ≅ Group.of Y :=
by refine ⟨Group.of_hom e.to_monoid_hom, Group.of_hom e.symm.to_monoid_hom, _, _⟩;
  ext; simp only [comp_apply, Group.of_hom_apply, mul_equiv.coe_to_monoid_hom,
    mul_equiv.apply_symm_apply, mul_equiv.symm_apply_apply, id_apply]

def Group.of_exists_mul_equiv {X Y : Type*} [group X] [group Y] (e : nonempty (X ≃* Y)) :
  is_isomorphic (Group.of X) (Group.of Y) :=
e.elim $ λ e, ⟨Group.of_mul_equiv e⟩

-- namespace alt_def

-- section

-- parameter (n : ℕ)

-- def is_on_fin_n (g : Group) := g.α = fin n
-- abbreviation on_fin_n := full_subcategory is_on_fin_n
-- abbreviation of_order_n := skeleton on_fin_n

-- end

-- end alt_def


section

parameter (n : ℕ)

def is_order_n (g : Group) := nonempty (g.α ≃ fin n)

def is_order_n_skel : skeleton Group → Prop := quotient.lift is_order_n $
λ a b ⟨h⟩, let h := h.Group_iso_to_mul_equiv.to_equiv in
propext $ ⟨λ ⟨ho⟩, ⟨h.symm.trans ho⟩, λ ⟨ho⟩, ⟨h.trans ho⟩⟩

def of_order_n := full_subcategory is_order_n_skel


lemma suss {α : Type*} : (@group.to_monoid α).injective :=
begin
  intros g₁ g₂,
  have a_mul_left_inj : ∀ a b c, g₁.mul b a = g₁.mul c a ↔ b = c,
  { revert g₁, introI,
    exact mul_left_inj, },
  have g₁_zpow_of_nat :=
  @zpow_of_nat _ (@group.to_div_inv_monoid _ g₁),
  have g₁_zpow_neg_succ_of_nat :=
  @zpow_neg_succ_of_nat _ (@group.to_div_inv_monoid _ g₁),
  have g₂_zpow_of_nat :=
  @zpow_of_nat _ (@group.to_div_inv_monoid _ g₂),
  have g₂_zpow_neg_succ_of_nat :=
  @zpow_neg_succ_of_nat _ (@group.to_div_inv_monoid _ g₂),
  rcases g₁, rcases g₂,
  change ∀ a b c, g₁_mul _ _ = g₁_mul _ _ ↔ _ at a_mul_left_inj,
  change ∀ a n, g₁_zpow _ _ = _ at g₁_zpow_of_nat,
  change ∀ a n, g₁_zpow _ _ = _ at g₁_zpow_neg_succ_of_nat,
  change ∀ a n, g₂_zpow _ _ = _ at g₂_zpow_of_nat,
  change ∀ a n, g₂_zpow _ _ = _ at g₂_zpow_neg_succ_of_nat,
  rintro ⟨⟩,
  have inv_eq : g₁_inv = g₂_inv,
  { change ∀ a, g₁_mul (g₁_inv a) a = _ at g₁_mul_left_inv,
    change ∀ a, g₁_mul (g₂_inv a) a = _ at g₂_mul_left_inv,
    ext, rw [← a_mul_left_inj x, g₁_mul_left_inv x, g₂_mul_left_inv] },
  subst inv_eq,
  suffices : g₁_div = g₂_div ∧ g₁_zpow = g₂_zpow,
  { simp_rw [this] },
  refine ⟨_, _⟩,
  { change @has_div.div α {div := g₁_div} = @has_div.div α {div := g₂_div},
    ext, rw [g₁_div_eq_mul_inv, g₂_div_eq_mul_inv] },
  { ext n x, cases n,
    { rw [g₁_zpow_of_nat, g₂_zpow_of_nat] },
    { rw [g₁_zpow_neg_succ_of_nat, g₂_zpow_neg_succ_of_nat] }},
end

lemma sussy {α : Type*} : (@monoid.to_semigroup α).injective :=
begin
  rintros ⟨⟩ ⟨⟩ ⟨⟩,
  have one_eq : a₁_one = a₂_one, { rw [← a₁_one_mul a₂_one, a₂_mul_one] },
  subst one_eq,
  suffices : a₁_npow = a₂_npow, { simp_rw [this] },
  ext n x, induction n,
  { rw [a₁_npow_zero', a₂_npow_zero'] },
  { rw [a₁_npow_succ', a₂_npow_succ', n_ih] },
end

lemma sussier {α : Type*} : (@semigroup.mul α).injective :=
by { rintros ⟨⟩ ⟨⟩ ⟨⟩, refl }

lemma silly {α : Type*} : (@group.mul α).injective :=
sussier.comp (sussy.comp suss)


instance on_fin_n.finite : finite {x : Group // x.α = fin n} :=
begin
  suffices : finite (group (fin n)),
  { haveI := this,
    exact finite.of_equiv (group (fin n))
    { to_fun := λ g, ⟨⟨_, g⟩, rfl⟩,
      inv_fun := λ ⟨g, h⟩, h.rec_on g.group,
      left_inv := λ g, rfl,
      right_inv := λ ⟨⟨_, g⟩, h⟩, by { dsimp only at ⊢ h, subst h, refl } } },
  exact finite.of_injective _ silly,
end

-- TODO what does reducible actually do lol
@[reducible]
def fin_n_to_skel : {x : Group // x.α = fin n} → of_order_n :=
λ ⟨g, h⟩, ⟨⟦g⟧, ⟨by rw h⟩⟩

instance of_order_n.finite : finite of_order_n :=
begin
  refine finite.of_surjective fin_n_to_skel _,

  rintro ⟨⟨g, h⟩, ⟨ho⟩⟩, dsimp only at ho,
  letI h' : group (fin n) := by { equiv_rw ho at h, from h },
  use ⟨⟨_, h'⟩, rfl⟩,

  ext, refine quotient.eq.mpr ⟨Group.of_mul_equiv $ (mul_equiv.mk' ho _).symm⟩,
  equiv_rw ho, intros, simp only [id.def, equiv.apply_symm_apply], refl,
end

end



example : nat.card (of_order_n 1) = 1 :=
begin
  rw nat.card_eq_one_iff_unique,
  suffices : ∃ x, ∀ y, x = y,
  { rcases this with ⟨x, h⟩,
    exact ⟨⟨λ a b, (h a).symm.trans (h b)⟩, ⟨x⟩⟩ },
  use ⟨⟦Group.of (multiplicative (zmod 1))⟧,
       by { rw [is_order_n_skel, quotient.lift_mk], use equiv.refl _ }⟩,
  rintro ⟨⟨g, h⟩, ⟨ho⟩⟩, change g ≃ multiplicative (zmod 1) at ho, 
  haveI : subsingleton (multiplicative (zmod 1)),
  { change subsingleton (fin 1), apply_instance },

  ext, refine quotient.eq.mpr ⟨Group.of_mul_equiv $ (mul_equiv.mk' ho _).symm⟩,
  exact λ x y, (eq_iff_true_of_subsingleton _ _).mpr ⟨⟩,
end

example (p : ℕ) (hp : p.prime) : nat.card (of_order_n p) = 1 :=
begin
  rw nat.card_eq_one_iff_unique,
  suffices : ∃ x, ∀ y, x = y,
  { rcases this with ⟨x, h⟩,
    exact ⟨⟨λ a b, (h a).symm.trans (h b)⟩, ⟨x⟩⟩ },
  use ⟨⟦Group.of (multiplicative (zmod p))⟧,
       by { rw [is_order_n_skel, quotient.lift_mk],
            cases p, from absurd rfl hp.ne_zero,
            use equiv.refl _ }⟩,

  -- these five lines are more or less boilerplate aren't they
  rintro ⟨⟨g, h⟩, ⟨ho⟩⟩, dsimp only at ho,
  haveI : fintype g := fintype.of_equiv _ ho.symm,
  have hc : fintype.card g = p,
  { rw ← fintype.card_fin p, convert fintype.of_equiv_card ho.symm },
  ext, refine quotient.eq.mpr (Group.of_exists_mul_equiv _),

  suffices : is_cyclic g,
  { rcases this with ⟨a, h⟩,
    choose φ hφ using h,
    let φ' : g → zmod p := (int.cast : ℤ → zmod p) ∘ φ,
    have : ∀ x y, φ' x + φ' y = φ' (x * y),
    { intros,
      simp [φ'],
      change ↑(φ x) + ↑(φ y) = ↑(φ (x * y)),
      rw ← int.cast_add, },
    refine ⟨(mul_equiv.of_bijective φ' _).symm⟩, },
  have : (fintype.card g).prime := hc.symm ▸ hp,
end