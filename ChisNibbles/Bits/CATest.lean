import Mathlib


/-!
The (Lebesgue) integral of cos x / (x ^ 2 + 1) on the real line is π / e.
-/


section MissingStuff

variable
  {𝕜 E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] [SMulCommClass ℂ 𝕜 E]

open Complex

-- exists in Mathlib but without a name
noncomputable def rectIntegral (f : ℂ → E) (z w : ℂ) :=
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

open MeasureTheory in
def RectIntegrable (f : ℂ → E) (z w : ℂ) :=
  IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im


omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectIntegrable {f : ℂ → E} {z w}
    (h₁ : ContinuousOn (fun x : ℝ => f (x + z.im * I)) (.uIcc z.re w.re))
    (h₂ : ContinuousOn (fun x : ℝ => f (x + w.im * I)) (.uIcc z.re w.re))
    (h₃ : ContinuousOn (fun y : ℝ => f (w.re + y * I)) (.uIcc z.im w.im))
    (h₄ : ContinuousOn (fun y : ℝ => f (z.re + y * I)) (.uIcc z.im w.im)) :
    RectIntegrable f z w := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ContinuousOn.intervalIntegrable <;> assumption

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectIntegrable' {f : ℂ → E} {z w}
    (h₁ : ContinuousOn f (.uIcc z.re w.re ×ℂ {z.im}))
    (h₂ : ContinuousOn f (.uIcc z.re w.re ×ℂ {w.im}))
    (h₃ : ContinuousOn f ({w.re} ×ℂ .uIcc z.im w.im))
    (h₄ : ContinuousOn f ({z.re} ×ℂ .uIcc z.im w.im)) :
    RectIntegrable f z w := by
  refine rectIntegrable
    (h₁.comp' (by fun_prop) ?_)
    (h₂.comp' (by fun_prop) ?_)
    (h₃.comp' (by fun_prop) ?_)
    (h₄.comp' (by fun_prop) ?_)
  all_goals
    simp only [Set.mapsTo_iff_image_subset, horizontalSegment_eq,
      verticalSegment_eq, subset_rfl]


namespace rectIntegral

variable {z w : ℂ} {f g : ℂ → E}

theorem integral_fun_const_smul (r : 𝕜) (f : ℂ → E) :
    rectIntegral (fun x => r • f x) z w = r • rectIntegral f z w := by
  unfold rectIntegral
  simp [intervalIntegral.integral_smul, smul_add, smul_sub, smul_comm]

theorem integral_fun_add (hf : RectIntegrable f z w) (hg : RectIntegrable g z w) :
    rectIntegral (fun x => f x + g x) z w = rectIntegral f z w + rectIntegral g z w := by
  unfold RectIntegrable at hf hg
  unfold rectIntegral
  repeat rw [intervalIntegral.integral_add]
  . module
  all_goals tauto

theorem integral_fun_comp_sub_right (c : ℂ) :
    rectIntegral (fun x => f (x - c)) z w = rectIntegral f (z - c) (w - c) := by
  unfold rectIntegral
  simp_rw [sub_re, sub_im, ← intervalIntegral.integral_comp_sub_right]
  congr <;> (simp; grind [Complex.re_add_im])

-- i cbs encoding the rect boundary and doing this for measure is a pain for some reason
-- so here's an easy version
theorem integral_congr_cofinite (h : f =ᶠ[.cofinite] g) :
    rectIntegral f z w = rectIntegral g z w := by
  unfold rectIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
    <;> apply intervalIntegral.integral_congr_ae
  all_goals
    suffices ∀ᵐ (x : ℝ), _ = _ from this.mono (fun _ h _ => h)
    apply Filter.EventuallyEq.filter_mono (l := .cofinite) _ <|
      Filter.le_cofinite_iff_eventually_ne.mpr MeasureTheory.volume.ae_ne
    apply h.comap _ |>.filter_mono _
    rw [Function.Injective.comap_cofinite_eq]
    simp [Function.Injective]

end rectIntegral


/-
mathlib does have circle integral around (z-c)⁻¹ but no homotopy invariance stuff so we need to get our hands dirty...
fortunately [PNT+](https://alexkontorovich.github.io/PrimeNumberTheoremAnd/docs/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.html#ResidueTheoremInRectangle) already did this so i can steal the proof strategy (but i'm rewriting many of the proofs for no reason)
-/

namespace rectIntegral.integral_div_sub_center

open intervalIntegral

variable {a b : ℝ} {x y : ℝ}

@[local grind .] lemma sq_add_sq_ne_zero (hy : y ≠ 0) :
    x ^ 2 + y ^ 2 ≠ 0 := by
  contrapose! hy; nlinarith

lemma one_div_re_add_im :
    1 / (x + y * I) = (x - y * I) / (x ^ 2 + y ^ 2) := by
  rw [one_div, Complex.inv_def, div_eq_mul_inv]
  simp [normSq_apply]; ring

lemma re_div_normSq (hy : y ≠ 0) :
    ∫ x in a..b, x / (x ^ 2 + y ^ 2) = Real.log (b ^ 2 + y ^ 2) / 2 - Real.log (a ^ 2 + y ^ 2) / 2 := by
  letI f x := Real.log (x ^ 2 + y ^ 2) / 2
  show _ = f b - f a
  convert integral_deriv_of_contDiffOn_uIcc _ using 2 <;> try infer_instance
  . funext x
    have hf : HasDerivAt f _ x
    . apply_rules only [HasDerivAt.div_const, HasDerivAt.log, HasDerivAt.add,
        HasDerivAt.pow, hasDerivAt_id, hasDerivAt_const, sq_add_sq_ne_zero hy]
    convert hf.deriv.symm using 1; ring
  . fun_prop (disch := grind)

lemma im_div_normSq (hy : y ≠ 0) :
    ∫ x in a..b, y / (x ^ 2 + y ^ 2) = Real.arctan (b / y) - Real.arctan (a / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ a hy, ← div_mul_cancel₀ b hy]
  simp_rw [← mul_integral_comp_mul_right, ← integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr <| fun x _ => by field_simp; ring

lemma div_self_on_re (hy : y ≠ 0) :
    ∫ x in a..b, 1 / (x + y * I) =
    (Real.log (b ^ 2 + y ^ 2) / 2 - Real.log (a ^ 2 + y ^ 2) / 2) -
      I * (Real.arctan (b / y) - Real.arctan (a / y)) := by
  have this (x : ℝ) : 1 / (x + y * I) = x / (x ^ 2 + y ^ 2) - I * (y / (x ^ 2 + y ^ 2)) := by
    rw [one_div_re_add_im]; ring
  simp_rw [this]; clear this
  rw [integral_sub]
  . rw_mod_cast [integral_const_mul, ← re_div_normSq hy, ← im_div_normSq hy]
    simp_rw [integral_ofReal]
  all_goals
    apply Continuous.intervalIntegrable
    norm_cast; fun_prop (disch := grind)

lemma div_self_on_im (hx : x ≠ 0) :
    ∫ y in a..b, 1 / (x + y * I) =
    -I * (Real.log (x ^ 2 + b ^ 2) / 2 - Real.log (x ^ 2 + a ^ 2) / 2) -
      (Real.arctan (-b / x) - Real.arctan (-a / x)) := by
  have this (y : ℝ) : 1 / (x + y * I) = (-I) * (1 / (y + (-x : ℝ) * I)) := by
    simp_rw [one_div_re_add_im]; push_cast; grind [I_mul_I]
  simp_rw [this]; clear this
  rw [integral_const_mul, div_self_on_re] <;> grind [I_mul_I]

theorem aux {z w : ℂ}
    (h_re : z.re < 0 ∧ 0 < w.re)
    (h_im : z.im < 0 ∧ 0 < w.im) :
    rectIntegral (·⁻¹) z w = 2 * I * Real.pi := by
  simp_rw [← one_div]
  rcases h_re with ⟨h1, h3⟩
  rcases h_im with ⟨h2, h4⟩
  rw [rectIntegral, div_self_on_re, div_self_on_re, div_self_on_im, div_self_on_im]
  . have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
    have l3 := Real.arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
    have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
    have l6 := Real.arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
    have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
    have r3 := Real.arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
    have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
    have r6 := Real.arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
    ring_nf
    simp_rw [neg_div, Real.arctan_neg, smul_eq_mul]
    simp_rw [l1, l3, l4, l6, r1, r3, r4, r6]
    push_cast
    grind [I_mul_I]
  all_goals grind

end rectIntegral.integral_div_sub_center

theorem rectIntegral.integral_div_sub_center (c : ℂ) {z w : ℂ}
    (c_re : c.re ∈ Set.Ioo z.re w.re)
    (c_im : c.im ∈ Set.Ioo z.im w.im)
    (A : ℂ) :
    rectIntegral (fun z => A / (z - c)) z w = 2 * I * Real.pi * A := by
  simp_rw [div_eq_mul_inv, ← smul_eq_mul A]
  rw [integral_fun_const_smul, integral_fun_comp_sub_right, integral_div_sub_center.aux]
  all_goals simp; grind

end MissingStuff



namespace Aux

open Complex Filter Topology

attribute [local grind =] I_mul_I I_sq
local grind_pattern I_ne_zero => I

-- set_option trace.Meta.Tactic.fun_prop.attr true
attribute [fun_prop]
  AnalyticAt.comp analyticAt_id analyticAt_fst analyticAt_snd AnalyticAt.prod


@[local grind] noncomputable def f z := exp (z * I) / (z^2 + 1)
@[local grind] noncomputable def K : ℂ := exp (-1) / (2 * I) -- residue of f at I
noncomputable def g : ℂ → ℂ :=
  Function.update aux I (limUnder (𝓝[≠] I) aux)
  where aux z := f z - K / (z - I)

-- attribute [fun_prop] MeromorphicAt MeromorphicAt.comp_analyticAt MeromorphicAt.div
-- theorem f_mero : Meromorphic f := fun x => by fun_prop [f]

@[fun_prop] theorem f_diff {z} (hz : z ≠ I ∧ z ≠ -I) : DifferentiableAt ℂ f z := by
  unfold f; fun_prop (disch := grind)

theorem f_res_I : Tendsto (fun z => (z - I) * f z) (𝓝[≠] I) (𝓝 K) :=
  .congr' (f₁ := fun z => exp (z * I) / (z + I))
    (eventuallyEq_nhdsWithin_of_eqOn <| by grind [Set.EqOn]) <| by
  convert continuousAt_iff_punctured_nhds.mp _ using 1
  . congr 1; grind
  . fun_prop (disch := grind)

theorem g_diff : DifferentiableOn ℂ g {-I}ᶜ := by
  convert differentiableOn_update_limUnder_insert_of_isLittleO (s := {I, -I}ᶜ) _ _ _ using 1
    <;> try infer_instance
  . ext; simp; grind
  . rw [← insert_mem_nhds_iff]
    convert_to {-I}ᶜ ∈ _ using 1 <;> try infer_instance
    . simp [Set.insert_def, Set.compl_def]; grind
    rw [IsOpen.mem_nhds_iff]
    . grind
    . simp
  . unfold g.aux
    intro x hx
    apply DifferentiableAt.differentiableWithinAt; fun_prop (disch := grind)
  . simp_rw [show g.aux I = 0 by simp [g.aux, f], sub_zero]
    apply Asymptotics.isLittleO_of_tendsto'
    . filter_upwards [self_mem_nhdsWithin] with z hz; grind
    apply Tendsto.congr' (f₁ := fun z => (z - I) * f z - K)
    . filter_upwards [self_mem_nhdsWithin] with z hz; simp_all [g.aux]; grind
    rw [tendsto_sub_nhds_zero_iff]
    apply f_res_I

lemma rectIntegral_g {C : ℝ} (hC : 0 ≤ C) :
    rectIntegral g (-C) (C + I * C) = 0 := by
  apply integral_boundary_rect_eq_zero_of_differentiableOn
  apply g_diff.mono _
  simp [reProdIm, Set.uIcc_of_le hC]

@[local grind .] lemma sq_add_one_ne_zero (x : ℂ) (hx : x ≠ I ∧ x ≠ -I) :
    x ^ 2 + 1 ≠ 0 := by
  grind

@[local grind] abbrev p (x : ℂ) := x ^ 2 + 1 ≠ 0
lemma p_of_lines (x : ℝ) :
    p x ∧ ∀ C : ℝ, 1 < C → p (x + C * I) ∧ p (C + x * I) ∧ p (-C + x * I) := by
  refine ⟨by norm_cast; nlinarith, fun C hC => ?_⟩
  apply_rules only [And.intro] <;> dsimp [p]
  all_goals
    apply sq_add_one_ne_zero
    simp [Complex.ext_iff]; grind

theorem rectIntegrable_f {C : ℝ} (hC : 1 < C) :
    RectIntegrable f (-C) (C + I * C) := by
  apply ContinuousOn.rectIntegrable <;> apply Continuous.continuousOn
    <;> (simp [f]; fun_prop (disch := have := p_of_lines; grind))

theorem intervalIntegrable_f {C : ℝ} :
    IntervalIntegrable (f ·) MeasureTheory.volume (-C) C := by
  apply Continuous.intervalIntegrable
  simp [f]; fun_prop (disch := have := p_of_lines; grind)

set_option linter.unnecessarySeqFocus false in
theorem rectIntegral_f {C : ℝ} (hC : 1 < C) :
    rectIntegral f (-C) (C + I * C) = 2 * I * Real.pi * K := by
  have : f =ᶠ[.cofinite] (fun z => g z + K / (z - I)) := by
    filter_upwards [show {I}ᶜ ∈ _ by simp] with z hz
    unfold g g.aux
    grind only [= Set.mem_compl_iff, Function.update, = Set.mem_singleton_iff]
  rw [rectIntegral.integral_congr_cofinite this, rectIntegral.integral_fun_add,
    rectIntegral_g (C := C) (by lia), rectIntegral.integral_div_sub_center, zero_add]
  . simp; lia
  . simp; lia
  . have := g_diff.continuousOn
    apply ContinuousOn.rectIntegrable' <;> apply this.mono
      <;> simp [reProdIm, Set.uIcc_of_le (show 0 ≤ C by lia)] <;> grind
  . have : ContinuousOn (fun z => K / (z - I)) {I}ᶜ := by fun_prop (disch := grind)
    apply ContinuousOn.rectIntegrable' <;> apply this.mono
      <;> simp [reProdIm, Set.uIcc_of_le (show 0 ≤ C by lia)] <;> grind



namespace EdgeBounds

open intervalIntegral

lemma aux_f {z} (hz : 0 ≤ z.im) : ‖f z‖ ≤ 1 / (‖z + I‖ * ‖z - I‖) := by
  rw [show ‖z + I‖ * ‖z - I‖ = ‖z ^ 2 + 1‖ by rw [← norm_mul]; grind]
  grw [f, norm_div, norm_exp, mul_I_re, show -z.im ≤ 0 by lia, Real.exp_zero]

lemma aux_re {z} (hz : 0 ≤ z.im) (hz' : z.re ≠ 0) : ‖f z‖ ≤ 1 / z.re ^ 2 := by
  grw [aux_f hz]; gcongr
  rw [show z.re ^ 2 = |z.re| * |z.re| by simp [pow_two]]; gcongr
  all_goals refine abs_re_le_norm _ |>.trans_eq' ?_; simp

lemma aux_im {z} (hz : 1 < z.im) : ‖f z‖ ≤ 1 / (z.im ^ 2 - 1) := by
  grw [aux_f (by lia)]; gcongr
  . nlinarith
  rw [show z.im ^ 2 - 1 = (z.im + 1) * (z.im - 1) by ring]; gcongr
  . lia
  all_goals refine abs_im_le_norm _ |>.trans_eq' ?_; simp; lia

theorem aux₁ :
    Tendsto (fun C : ℝ => rectIntegral f (-C) (C + I * C)) atTop (𝓝 (Real.pi / exp 1)) := by
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [Ioi_mem_atTop 1] with C hC
  rw [rectIntegral_f (by grind)]
  simp [K, exp_neg]; field

set_option linter.unnecessarySeqFocus false in
theorem aux₂ :
    Tendsto (fun C : ℝ => ∫ x : ℝ in -C..C, f (x + C * I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_const_nhds.squeeze' ?_ (by simp)
    (eventually_atTop.mpr <| .intro 2 fun C hC =>
      norm_integral_le_of_norm_le_const (C := 1 / (C ^ 2 - 1)) fun x hx =>
        aux_im (by simp; lia) |>.trans_eq (by simp))
  simp_rw [mul_comm, mul_one_div]
  rw [← Asymptotics.isLittleO_iff_tendsto']
  . open Polynomial Asymptotics in
    apply IsLittleO.abs_left
    convert_to (2 * X : ℝ[X]).eval =o[atTop] (X ^ 2 - 1 : ℝ[X]).eval
    . simp; grind
    . simp
    apply Polynomial.isLittleO_atTop_of_degree_lt
    convert_to (1 : WithBot ℕ) < 2
      <;> (try compute_degree)
      <;> norm_num <;> decide
  . rw [eventually_atTop]
    exists 2; intro b hb h; nlinarith

theorem aux₃ :
    Tendsto (fun C : ℝ => ∫ y : ℝ in 0..C, f (C + y * I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_const_nhds.squeeze' ?_ (by simp)
    (eventually_atTop.mpr <| .intro 0 fun C hC =>
      norm_integral_le_of_norm_le_const (C := 1 / C ^ 2) fun x hx =>
        aux_re (by simp; grind) (by simp; grind) |>.trans_eq (by simp))
  exact tendsto_abs_atTop_atTop.inv_tendsto_atTop.congr
    (f₁ := fun C : ℝ => |C|⁻¹) (by grind)

theorem aux₄ :
    Tendsto (fun C : ℝ => ∫ y : ℝ in 0..C, f (-C + y * I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_const_nhds.squeeze' ?_ (by simp)
    (eventually_atTop.mpr <| .intro 0 fun C hC =>
      norm_integral_le_of_norm_le_const (C := 1 / C ^ 2) fun x hx =>
        aux_re (by simp; grind) (by simp; grind) |>.trans_eq (by simp))
  exact tendsto_abs_atTop_atTop.inv_tendsto_atTop.congr
    (f₁ := fun C : ℝ => |C|⁻¹) (by grind)

end EdgeBounds

open EdgeBounds in
theorem tendsto_intervalIntegral_f :
    Tendsto (fun C : ℝ => ∫ x in -C..C, f x) atTop (𝓝 (Real.pi / exp 1)) := by
  convert aux₁ |>.add aux₂ |>.sub (aux₃.const_smul I) |>.add (aux₄.const_smul I) using 1
  . simp [rectIntegral]; ext; ring
  . ring_nf

end Aux


open Real Filter Topology


lemma final.aux :
    Tendsto (fun C => ∫ x in -C..C, cos x / (x ^ 2 + 1)) atTop (𝓝 (π / exp 1)) := by
  convert Complex.continuous_re.tendsto _ |>.comp Aux.tendsto_intervalIntegral_f using 1
  . ext C
    rw [Function.comp_apply, ← Complex.reCLM_apply,
      ← Complex.reCLM.intervalIntegral_comp_comm Aux.intervalIntegrable_f]
    congr! with x
    rw [Complex.reCLM_apply, Aux.f]
    norm_cast
    rw [Complex.div_ofReal_re]
    simp
  . erw [← Complex.ofReal_exp]
    norm_cast


theorem final :
    ∫ x : ℝ, cos x / (x ^ 2 + 1) = π / exp 1 := by
  convert symm <| tendsto_nhds_unique final.aux _
  refine MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_inv_one_add_sq.mono ?_ ?_) tendsto_neg_atTop_atBot tendsto_id
  . apply Measurable.aestronglyMeasurable
    fun_prop
  . filter_upwards with x
    simp; grw [abs_cos_le_one]; lia
