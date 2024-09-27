import data.real.basic
import data.real.sqrt

namespace pos

-- by analogy to nnreal's definition in the stdlib, i have this thing
-- that provides general structure on the positive subtype,
-- and then specialise it to ℝ later
-- (i tried not doing this but ran into weirdnesses)
--
-- basically this is copied from nonneg, and preal is copied from nnreal

variables {α : Type*} [linear_ordered_field α]

instance has_one : has_one {x : α // 0 < x} := ⟨⟨1, one_pos⟩⟩
instance has_add : has_add {x : α // 0 < x} := ⟨λ x y, ⟨x.1 + y.1, add_pos x.2 y.2⟩⟩
instance has_mul : has_mul {x : α // 0 < x} := ⟨λ x y, ⟨x.1 * y.1, mul_pos x.2 y.2⟩⟩
instance has_inv : has_inv {x : α // 0 < x} := ⟨λ x, ⟨x.1⁻¹, inv_pos.mpr x.2⟩⟩
instance has_div : has_div {x : α // 0 < x} := ⟨λ x y, ⟨x.1 / y.1, div_pos x.2 y.2⟩⟩
instance has_pow : has_pow {x : α // 0 < x} ℕ := ⟨λ x n, ⟨x.1 ^ n, pow_pos x.2 n⟩⟩

@[simp, norm_cast]
protected lemma coe_add (a b : {x : α // 0 < x}) :
  ((a + b : {x : α // 0 < x}) : α) = a + b := rfl
@[simp] lemma mk_add_mk {x y : α} (hx : 0 < x) (hy : 0 < y) :
  (⟨x, hx⟩ : {x : α // 0 < x}) + ⟨y, hy⟩ = ⟨x + y, add_pos hx hy⟩ := rfl

@[simp, norm_cast]
protected lemma coe_one : ((1 : {x : α // 0 < x}) : α) = 1 := rfl
@[simp] lemma mk_eq_one {x : α} (hx : 0 < x) : (⟨x, hx⟩ : {x : α // 0 < x}) = 1 ↔ x = 1 :=
subtype.ext_iff

@[simp, norm_cast]
protected lemma coe_mul (a b : {x : α // 0 < x}) :
  ((a * b : {x : α // 0 < x}) : α) = a * b := rfl
@[simp] lemma mk_mul_mk {x y : α} (hx : 0 < x) (hy : 0 < y) :
  (⟨x, hx⟩ : {x : α // 0 < x}) * ⟨y, hy⟩ = ⟨x * y, mul_pos hx hy⟩ := rfl

@[simp, norm_cast]
protected lemma coe_pow (a : {x : α // 0 < x}) (n : ℕ) :
  ((a ^ n : {x : α // 0 < x}) : α) = a ^ n := rfl
@[simp] lemma mk_pow {x : α} (hx : 0 < x) (n : ℕ) :
  (⟨x, hx⟩ : {x : α // 0 < x}) ^ n = ⟨x ^ n, pow_pos hx n⟩ := rfl

@[simp, norm_cast]
protected lemma coe_inv (r : {x : α // 0 < x}) :
  ((r⁻¹ : {x : α // 0 < x}) : α) = r⁻¹ := rfl
@[simp] lemma inv_mk {x : α} (hx : 0 < x) :
  (⟨x, hx⟩ : {x : α // 0 < x})⁻¹ = ⟨x⁻¹, inv_pos.mpr hx⟩ := rfl

@[simp, norm_cast]
protected lemma coe_div (a b : {x : α // 0 < x}) :
  ((a / b : {x : α // 0 < x}) : α) = a / b := rfl
@[simp] lemma mk_div_mk {x y : α} (hx : 0 < x) (hy : 0 < y) :
  (⟨x, hx⟩ : {x : α // 0 < x}) / ⟨y, hy⟩ = ⟨x / y, div_pos hx hy⟩ := rfl

instance partial_order : partial_order {x : α // 0 < x} := subtype.partial_order _
instance linear_order : linear_order {x : α // 0 < x} := subtype.linear_order _

instance add_comm_semigroup : add_comm_semigroup {x : α // 0 < x} :=
subtype.coe_injective.add_comm_semigroup _ (λ _ _, rfl)
instance add_left_cancel_semigroup : add_left_cancel_semigroup {x : α // 0 < x} :=
subtype.coe_injective.add_left_cancel_semigroup _ (λ _ _, rfl)
instance add_right_cancel_semigroup : add_right_cancel_semigroup {x : α // 0 < x} :=
subtype.coe_injective.add_right_cancel_semigroup _ (λ _ _, rfl)

instance distrib : distrib {x : α // 0 < x} :=
subtype.coe_injective.distrib _ (λ _ _, rfl) (λ _ _, rfl)

instance comm_monoid : comm_monoid {x : α // 0 < x} :=
subtype.coe_injective.comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

instance monoid : monoid {x : α // 0 < x} := by apply_instance

instance linear_ordered_comm_group : linear_ordered_comm_group {x : α // 0 < x} :=
begin
  refine_struct
  { inv := has_inv.inv, div := has_div.div, zpow := zpow_rec,
    .. pos.comm_monoid, .. pos.linear_order },
  repeat { simp only [subtype.forall] },
  { intros, simp [division_def] },
  { intros, ext, norm_cast },
  { intros, dsimp only [zpow_rec], norm_cast },
  { intros, dsimp only [zpow_rec], norm_cast },
  { intros a a_pos, simp [inv_mul_cancel (ne_of_gt a_pos)] },
  { intros a a_pos b b_pos h c c_pos,
    simp only [mk_mul_mk, subtype.mk_le_mk] at ⊢ h,
    rwa mul_le_mul_left c_pos },
end

end pos

@[derive [
  comm_monoid, linear_ordered_comm_group, distrib,
  add_comm_semigroup, add_left_cancel_semigroup, add_right_cancel_semigroup]]
def preal := {x : ℝ // 0 < x}
local notation `ℝ>0` := preal

namespace preal

instance : has_coe ℝ>0 ℝ := ⟨subtype.val⟩
@[simp] lemma val_eq_coe (n : ℝ>0) : n.val = n := rfl
instance : can_lift ℝ ℝ>0 := subtype.can_lift _

@[norm_cast] theorem coe_mk (a : ℝ) (ha) : ((⟨a, ha⟩ : ℝ>0) : ℝ) = a := rfl

protected lemma coe_injective : function.injective (coe : ℝ>0 → ℝ) :=
subtype.coe_injective
@[simp, norm_cast] protected lemma coe_eq {r₁ r₂ : ℝ>0} : (r₁:ℝ) = (r₂:ℝ) ↔ r₁ = r₂ :=
preal.coe_injective.eq_iff

@[simp, norm_cast] protected lemma coe_bit0 (r : ℝ>0) : ((bit0 r : ℝ>0) : ℝ) = bit0 r := rfl
@[simp, norm_cast] protected lemma coe_bit1 (r : ℝ>0) : ((bit1 r : ℝ>0) : ℝ) = bit1 r := rfl
protected lemma coe_two : ((2 : ℝ>0) : ℝ) = 2 := rfl

@[simp, norm_cast] protected lemma coe_le_coe {r₁ r₂ : ℝ>0} : (r₁ : ℝ) ≤ r₂ ↔ r₁ ≤ r₂ := iff.rfl
@[simp, norm_cast] protected lemma coe_lt_coe {r₁ r₂ : ℝ>0} : (r₁ : ℝ) < r₂ ↔ r₁ < r₂ := iff.rfl

-- is this sane
@[simp, norm_cast] protected lemma coe_ne_zero {r : ℝ>0} : (r : ℝ) ≠ 0 ↔ true :=
iff_true_intro (ne_of_gt r.2)
@[simp, norm_cast] protected lemma coe_pos {r : ℝ>0} : (0 : ℝ) < r ↔ true := iff_true_intro r.2

protected lemma coe_one : ((1 : ℝ>0) : ℝ) = 1 := rfl
@[simp, norm_cast] protected lemma coe_eq_one (r : ℝ>0) : ↑r = (1:ℝ) ↔ r = 1 :=
by rw [← preal.coe_one, preal.coe_eq]

@[simp] lemma zero_le_coe {n : ℝ>0} : 0 ≤ (n:ℝ) := le_of_lt n.2

-- help why are these all noncomputable :(
noncomputable example : has_one ℝ>0 := by apply_instance
noncomputable example : has_add ℝ>0 := by apply_instance
noncomputable example : has_div ℝ>0 := by apply_instance

-- a bunch of properties of sqrt, almost certainly don't need all of these
@[pp_nodot] noncomputable def sqrt (x : ℝ>0) : ℝ>0 := ⟨real.sqrt ↑x, real.sqrt_pos.mpr x.2⟩
@[simp, norm_cast] lemma coe_sqrt {x : ℝ>0} : (preal.sqrt x : ℝ) = real.sqrt x := rfl
@[simp] lemma sqrt_one : sqrt (1 : ℝ>0) = 1 := by { ext, simp }
@[simp] lemma mul_self_sqrt (x : ℝ>0) : sqrt x * sqrt x = x := by { ext, simp }
@[simp] lemma sqrt_mul_self (x : ℝ>0) : sqrt (x * x) = x := by { ext, simp }
@[simp] lemma sq_sqrt (x : ℝ>0) : (sqrt x)^2 = x := by { ext, simp }
@[simp] lemma sqrt_sq (x : ℝ>0) : sqrt (x^2) = x := by { ext, simp }
/- @[simp] -/ lemma sqrt_mul (x y : ℝ>0) : sqrt (x * y) = sqrt x * sqrt y := by { ext, simp }
/- @[simp] -/ lemma sqrt_inv (x : ℝ>0) : sqrt x⁻¹ = (sqrt x)⁻¹ := by { ext, simp }
@[simp] lemma sqrt_le_sqrt_iff {x y : ℝ>0} : sqrt x ≤ sqrt y ↔ x ≤ y :=
begin
  convert @nnreal.sqrt_le_sqrt_iff ⟨↑x, by simp⟩ ⟨↑y, by simp⟩ using 1,
  rw ← preal.coe_le_coe, push_cast, simp,
end
@[simp] lemma sqrt_lt_sqrt_iff {x y : ℝ>0} : sqrt x < sqrt y ↔ x < y :=
lt_iff_lt_of_le_iff_le sqrt_le_sqrt_iff
lemma sqrt_inj (x y : ℝ>0) : sqrt x = sqrt y ↔ x = y :=
by simp [le_antisymm_iff]

end preal

open tactic

namespace rify

-- zify but for preal

@[user_attribute]
meta def rify_attr : user_attribute simp_lemmas unit :=
{ name := `rify,
  descr := "Used to tag lemmas for use in the `rify` tactic",
  cache_cfg :=
    { mk_cache :=
        λ ns, mmap (λ n, do c ← mk_const n, return (c, tt)) ns >>= simp_lemmas.mk.append_with_symm,
      dependencies := []}}

meta def lift_to_r (e : expr) : tactic (expr × expr) :=
do sl ← rify_attr.get_cache,
   sl ← sl.add_simp `ge_iff_le, sl ← sl.add_simp `gt_iff_lt,
   (e', prf, _) ← simplify sl [] e,
   return (e', prf)

attribute [rify] preal.coe_le_coe preal.coe_lt_coe preal.coe_eq

end rify

@[rify] lemma preal.coe_ne_coe (a b : ℝ>0) : (a : ℝ) ≠ b ↔ a ≠ b :=
by simp

meta def tactic.rify (extra_lems : list simp_arg_type) : expr → tactic (expr × expr) := λ z,
do (z1, p1) ← rify.lift_to_r z <|> fail "failed to find an applicable rify lemma",
   (z2, p2) ← norm_cast.derive_push_cast extra_lems z1,
   prod.mk z2 <$> mk_eq_trans p1 p2

meta def tactic.rify_proof (extra_lems : list simp_arg_type) (h : expr) : tactic expr :=
do (_, pf) ← infer_type h >>= tactic.rify extra_lems,
   mk_eq_mp pf h

section

setup_tactic_parser

meta def tactic.interactive.rify (sl : parse simp_arg_list) (l : parse location) : tactic unit :=
do locs ← l.get_locals,
replace_at (tactic.rify sl) locs l.include_goal >>= guardb

end

namespace imo2022q2

section

open real

lemma am_gm_two (x y : ℝ) (x_nn : x ≥ 0) (y_nn : y ≥ 0) :
  x + y ≥ 2 * sqrt(x * y) ∧ (x + y = 2 * sqrt(x * y) ↔ x = y) :=
begin
  have sqrt_sqr : ∀ {r} (r_nn : r ≥ 0), r = sqrt r * sqrt r,
  { intros, rw [← sqrt_mul, sqrt_mul_self]; exact r_nn },
  have : x + y = _ + _, { rw [sqrt_sqr x_nn, sqrt_sqr y_nn] },
  rw [sqrt_mul x_nn, this, ← sqrt_inj x_nn y_nn],

  refine ⟨_, ⟨_, _⟩⟩; intros; nlinarith [sq_nonneg (sqrt x - sqrt y)]
end

lemma am_gm_two_eq (x y : ℝ) (x_nn : x ≥ 0) (y_nn : y ≥ 0) :
  x + y ≤ 2 * sqrt (x * y) ↔ x = y :=
begin
  obtain ⟨amgm_ge, amgm_eq⟩ := am_gm_two x y x_nn y_nn,
  rw [← amgm_eq, le_iff_eq_or_lt],
  exact or_iff_left (not_lt_of_ge amgm_ge),
end

end

open preal

lemma am_gm_two' (x y : ℝ>0) :
  x + y ≥ 2 * sqrt (x * y) ∧ (x + y = 2 * sqrt (x * y) ↔ x = y) :=
by { rify, exact am_gm_two ↑x ↑y (by simp) (by simp), }

lemma am_gm_inv_eq (x : ℝ>0) :
  x + x⁻¹ ≤ 2 ↔ x = 1 :=
begin
  rw (⟨by {rintro rfl, norm_num}, eq_one_of_inv_eq' ∘ eq.symm⟩ : x = 1 ↔ x = x⁻¹),
  convert am_gm_two_eq x.1 x⁻¹.1 (by simp) (by simp) using 1,
  all_goals { simp, norm_cast },
end

def soln_set : set (ℝ>0 → ℝ>0) :=
{λ x, x⁻¹}

theorem imo2022q2 (f : ℝ>0 → ℝ>0) :
  (∀ x, ∃! y, x * f y + y * f x ≤ 2) ↔ f ∈ soln_set :=
begin
  dsimp [soln_set],
  split, swap, -- we do the boring case (←) first
  { rintros rfl x, use [x, by simp [bit0]],
    intro y, dsimp only,
    convert (iff.mp $ am_gm_inv_eq (x * y⁻¹)), ext,
    refine imp_congr (by simp) _,
    rw mul_inv_eq_one, exact comm },

  intro h, choose g h using h,

  have g_inv : function.involutive g :=
  λ x, eq.symm $ (h (g x)).right x $ by { rw add_comm, exact (h x).left },

  have f_large_iff_ne : ∀ x, x ≠ g x ↔ x * f x > 1,
  { intro, rw ← not_iff_comm, push_neg,
    suffices : x * (f x) + x * (f x) ≤ 2 ↔ x = g x,
    { rw [← this, ← mul_two], simp },
    exact ⟨(h x).right x, λ g_eq, by convert (h x).left⟩ },

  have g_id : g = id,
  { funext x, dsimp only [id], by_contra g_ne,

    have lx : 1 < x * f x       := ((f_large_iff_ne    x ).mp $ ne_comm.mp g_ne),
    have ly : 1 < g x * f (g x) := ((f_large_iff_ne (g x)).mp $ by rwa g_inv),

    suffices : x * f (g x) + g x * f x > 2, from not_le_of_gt this (h x).left,
    calc x * f (g x) + g x * f x ≥ 2 * sqrt (_ * _) : (am_gm_two' _ _).left
                             ... > 2 * 1            : _
                             ... = 2                : by norm_num,
    suffices : 1 < sqrt _, by simpa,
    rw [← sqrt_one, sqrt_lt_sqrt_iff],
    convert one_lt_mul' lx ly using 1, rify, ring },

  subst g_id, dsimp only [id] at *,
  have f_small := λ x, le_of_not_gt $ (not_iff_comm.mp $ f_large_iff_ne x).mpr rfl,

  funext x, apply eq_inv_of_mul_eq_one_right,
  by_contra' f_lt,
  replace f_lt : x * f x < 1 := (lt_or_eq_of_le $ f_small x).resolve_right f_lt,

  suffices : ∃ x' ≠ x, x * f x' + x' * f x ≤ 2,
  from let ⟨x', x'_ne, hx'⟩ := this in x'_ne $ (h x).right x' hx',

  let c := f x * x,
  suffices : ∃ x' ≠ x, x ^ 2 + x'^2 * c ≤ 2 * (x * x'),
  { rcases this with ⟨x', x'_ne, hx'⟩, use [x', x'_ne],
    refine le_of_mul_le_mul_right' (_ : _ * _ ≤ 2 * (x * x')),
    calc (x * f x' + x' * f x) * (x * x')
         = x^2 * (f x' * x') + x'^2 * (f x * x)   : by { rify, ring }
     ... ≤ x^2 + x'^2 * (f x * x)                 : by { have := f_small x',
       rify at ⊢ this, nlinarith only [this, (by simp : (0:ℝ) < ↑x^2)] }
     ... ≤ 2 * (x * x')                           : hx' },

  have hc : sqrt c < 1,
  { dsimp only [c], rwa [← sqrt_one, sqrt_lt_sqrt_iff, mul_comm] },
  use [x / sqrt c, by simp [ne_of_lt hc]],
  suffices : 2 * x^2 ≤ 2 * x^2 / sqrt c,
  { simp, rify at ⊢ this, convert this using 1; ring },
  simp [le_of_lt hc],
end

end imo2022q2
