import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Tactic.Rify

/-
When I first did this there was way less infrastructure in Mathlib
about the positive part of a ring. Now the approach I took is much more plausible.
(I still have to set up a bunch of machinery though. If I had an AI or something
to do that part it would be actually OK)
-/

namespace IMO.«2022»

namespace q2

abbrev PReal := { x : ℝ // 0 < x }
notation "ℝ+" => PReal

namespace PReal
  instance : One ℝ+ := ⟨1, by linarith⟩
  instance (n : ℕ) [hn : n.AtLeastTwo] : OfNat ℝ+ n := ⟨n, by norm_cast; linarith [hn.prop]⟩
  -- instance : CanLift ℝ ℝ+ Subtype.val (0 < ·) := Subtype.canLift _

  section coe
    @[norm_cast] theorem coe_mk (a : ℝ) ha : ((⟨a, ha⟩ : ℝ+) : ℝ) = a := rfl
    -- @[simp, norm_cast] theorem mk_coe (a : ℝ+) h : (⟨a, h⟩ : ℝ+) = a := rfl

    protected lemma coe_injective : Function.Injective (Subtype.val : ℝ+ → ℝ) := Subtype.coe_injective
    @[simp, norm_cast] protected lemma coe_eq {a b : ℝ+} : (a : ℝ) = b ↔ a = b := Subtype.coe_inj
    @[simp, norm_cast] protected lemma coe_one : ((1 : ℝ+) : ℝ) = 1 := rfl
    @[simp, norm_cast]
    protected lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] :
        (no_index (OfNat.ofNat n : ℝ+) : ℝ) = OfNat.ofNat n :=
      rfl
    @[simp, norm_cast] protected lemma coe_le_coe {a b : ℝ+} : (a : ℝ) ≤ b ↔ a ≤ b := Iff.rfl
    @[simp, norm_cast] protected lemma coe_lt_coe {a b : ℝ+} : (a : ℝ) < b ↔ a < b := Iff.rfl
    @[simp, norm_cast] protected lemma coe_ne_zero {r : ℝ+} : (r : ℝ) ≠ 0 ↔ True := iff_true_intro $ ne_of_gt r.2
    @[simp, norm_cast] protected lemma coe_pos {r : ℝ+} : (0 : ℝ) < r ↔ True := iff_true_intro r.2
    @[simp] lemma zero_le_coe {n : ℝ+} : 0 ≤ (n:ℝ) := le_of_lt n.2
    @[simp, norm_cast] protected lemma coe_eq_one (r : ℝ+) : ↑r = (1:ℝ) ↔ r = 1 := by
      rw [← PReal.coe_one, PReal.coe_eq]

    @[simp, norm_cast] protected lemma coe_mul (a b : ℝ+) : (↑(a * b) : ℝ) = a * b := rfl
    @[simp, norm_cast] protected lemma coe_div (a b : ℝ+) : ↑(a / b) = (a / b : ℝ) := rfl
    @[simp, norm_cast] protected lemma coe_pow (r : ℝ+) (n : ℕ) : (↑(r ^ n) : ℝ) = r ^ n := rfl
  end coe

  section sqrt
    @[pp_nodot] noncomputable def sqrt (x : ℝ+) : ℝ+ := ⟨Real.sqrt x, Real.sqrt_pos.mpr x.2⟩

    @[simp, norm_cast] lemma coe_sqrt (x : ℝ+) : sqrt x = Real.sqrt x := rfl
    @[simp] lemma sqrt_one : sqrt 1 = 1 := by ext; simp
    lemma mul_self_sqrt x : sqrt x * sqrt x = x := by ext; simp
    @[simp] lemma sqrt_mul x y : sqrt (x * y) = sqrt x * sqrt y := by ext; simp
    @[simp] lemma sqrt_mul_self x : sqrt (x * x) = x := by ext; simp
    @[simp] lemma sq_sqrt x : sqrt x ^ 2 = x := by ext; simp
    @[simp] lemma sqrt_sq x : sqrt (x ^ 2) = x := by ext; simp
    @[simp] lemma sqrt_le_sqrt_iff {x y} : sqrt x ≤ sqrt y ↔ x ≤ y := by rw [← PReal.coe_le_coe]; simp
    @[simp] lemma sqrt_lt_sqrt_iff {x y} : sqrt x < sqrt y ↔ x < y := by rw [← PReal.coe_lt_coe]; simp
    lemma sqrt_inj x y : sqrt x = sqrt y ↔ x = y := by simp [le_antisymm_iff]
  end sqrt
end PReal

section Rify
  @[rify_simps] lemma prealCast_eq {a b : ℝ+} : a = b ↔ (a : ℝ) = b := by simp
  @[rify_simps] lemma prealCast_le {a b : ℝ+} : a ≤ b ↔ (a : ℝ) ≤ b := by simp
  @[rify_simps] lemma prealCast_lt {a b : ℝ+} : a < b ↔ (a : ℝ) < b := by simp
  @[rify_simps] lemma prealCast_ne {a b : ℝ+} : a ≠ b ↔ (a : ℝ) ≠ b := by simp
end Rify

section am_gm
namespace PReal
  lemma am_gm_two' (x y : ℝ+) :
      x + y ≥ 2 * sqrt (x * y) ∧ (x + y = 2 * sqrt (x * y) ↔ x = y) := by
    let a := sqrt x
    let b := sqrt y
    simp_rw [show x = a ^ 2 by simp [a], show y = b ^ 2 by simp [b]]
    clear_value a b; clear x y
    simp only [sqrt_mul, sqrt_sq]
    rify
    constructor
    . linarith only [sq_nonneg (a - b : ℝ)]
    . rw [← sub_eq_zero]
      convert_to (a - b : ℝ) ^ 2 = 0 ↔ _ using 1
      . ring_nf
      simp [sub_eq_zero]

  lemma am_gm_two_eq (x y : ℝ+) :
      x + y ≤ 2 * sqrt (x * y) ↔ x = y := by
    obtain ⟨h_ge, h_eq⟩ := am_gm_two' x y
    rw [← h_eq, le_iff_eq_or_lt]
    exact or_iff_left $ not_lt_of_ge h_ge

  lemma am_gm_inv_eq (x : ℝ+) :
      x + x⁻¹ ≤ 2 ↔ x = 1 := by
    have : x = 1 ↔ x = x⁻¹ := ⟨by rintro rfl; simp, eq_one_of_inv_eq' ∘ symm⟩
    rw [this]
    convert am_gm_two_eq x x⁻¹ using 2
    simp
end PReal
end am_gm

end q2

def q2.soln_set : Set (PReal → PReal) := {(·⁻¹)}

open q2 PReal in
theorem q2 (f : ℝ+ → ℝ+) :
    (∀ x, ∃! y, x * f y + y * f x ≤ 2) ↔ f ∈ soln_set := by
  simp only [soln_set, Set.mem_singleton_iff]
  constructor
  case mpr =>
    rintro rfl; dsimp only
    intro x
    use x, (by simp only [mul_inv_cancel]; rify; norm_num)
    intro y; dsimp only
    convert am_gm_inv_eq (x * y⁻¹) |>.mp using 1
    . simp
    . simp [mul_inv_eq_one, eq_comm]

  intro hf
  choose g hg h using hf
  dsimp at hg h

  have g_inv : Function.Involutive g :=
    fun x => symm $ h (g x) x $ by rw [add_comm]; apply hg

  have ne_iff_f_large x : x ≠ g x ↔ x * f x > 1 := by
    rw [← not_iff_comm, not_lt]
    suffices x * f x + x * f x ≤ 2 ↔ x = g x by
      rw [← this]
      rify; simp [← mul_two]
    exact ⟨h x x, fun _ => by convert hg x⟩

  obtain rfl : g = id := by
    funext x; dsimp only [id]
    by_contra g_ne

    have lx : 1 < x * f x       := ne_iff_f_large    x  |>.mp $ ne_comm.mp g_ne
    have ly : 1 < g x * f (g x) := ne_iff_f_large (g x) |>.mp $ by rwa [g_inv]

    suffices x * f (g x) + g x * f x > 2 by rify at *; linarith [hg x]
    calc
      x * f (g x) + g x * f x ≥ 2 * sqrt (_ * _) := am_gm_two' _ _ |>.1
      _                       > 2 * 1            := ?_
      _                       = 2                := by norm_num
    gcongr
    rw [← sqrt_one, sqrt_lt_sqrt_iff]
    convert one_lt_mul' lx ly using 1
    rify; ring
  dsimp only [id] at *

  have f_small x : x * f x ≤ 1 := le_of_not_gt $
    (not_iff_comm.mp $ ne_iff_f_large x).mpr rfl

  funext x; apply eq_inv_of_mul_eq_one_right
  by_contra f_lt
  replace f_lt : x * f x < 1 := f_small x |>.lt_of_ne f_lt

  suffices ∃ x' ≠ x, x * f x' + x' * f x ≤ 2 from
    have ⟨x', x'_ne, hx'⟩ := this; x'_ne $ h x x' hx'

  let c := f x * x
  suffices ∃ x' ≠ x, x^2 + x'^2 * c ≤ 2 * (x * x') by
    rcases this with ⟨x', x'_ne, hx'⟩
    use x', x'_ne
    apply le_of_mul_le_mul_right' (a := x * x')
    calc
      _ = x^2 * (f x' * x') + x'^2 * (f x * x) := by rify; ring
      _ ≤ x^2 + x'^2 * (f x * x)               := ?_
      _ ≤ 2 * (x * x')                         := hx'
    gcongr
    conv_rhs => rw [← mul_one (x ^ 2)]
    gcongr
    rw [mul_comm]; apply f_small

  have hc : sqrt c < 1 := by
    dsimp only [c]; rwa [← sqrt_one, sqrt_lt_sqrt_iff, mul_comm]

  use x / sqrt c, by simp [ne_of_lt hc]
  suffices 2 * x^2 ≤ 2 * x^2 / sqrt c by
    simp only [div_pow, sq_sqrt, div_mul_cancel]; rify at this ⊢
    convert this using 1 <;> ring
  simp [le_of_lt hc]

end IMO.«2022»
