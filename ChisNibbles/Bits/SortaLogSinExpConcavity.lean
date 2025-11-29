import Mathlib

open Set Real



namespace Short
variable {r : ℝ} (hr : 1 < r)
include hr

attribute [grind! .] mul_pos div_pos inv_pos sin_pos_of_mem_Ioo cos_pos_of_mem_Ioo tan_pos_of_pos_of_lt_pi_div_two
@[bound, grind →] lemma pi_div_lt : π / r < π := by bound
@[grind =, grind =_] lemma mul_lt_pi {x : ℝ} : x < π / r ↔ r * x < π := by rw [← lt_div_iff₀']; cutsat
@[bound, grind! .] lemma sin_pos_r {x : ℝ} (hx : x ∈ Ioo 0 (π / r)) : 0 < sin (r * x) := by grind

attribute [fun_prop]
  HasDerivAt
  hasDerivAt_id hasDerivAt_const HasDerivAt.comp HasDerivAt.prodMk
  HasDerivAt.add HasDerivAt.fun_add HasDerivAt.sub HasDerivAt.fun_sub
  HasDerivAt.mul HasDerivAt.fun_mul HasDerivAt.div HasDerivAt.fun_div
  hasDerivAt_sin hasDerivAt_cos
theorem blob : StrictMonoOn (fun x => sin x / sin (r * x)) (Ico 0 (π / r)) := by
  set f := fun x => sin x / sin (r * x)
  rw [← Ioo_insert_left (by bound), strictMonoOn_insert_iff_of_forall_ge (by grind)]
  refine ⟨by simp [f]; grind, ?_⟩

  -- due to some kind of fun_prop bug, disch := grind isn't working, so we do this instead
  have : ∀ x ∈ Ioo 0 (π / r), sin (r * x) ≠ 0 := by grind
  let g x := cos x * sin (r * x) - r * sin x * cos (r * x)
  have hf' x (hx : x ∈ Ioo 0 (π / r) := by grind) : HasDerivAt f (g x / sin (r * x) ^ 2) x := by
    have : HasDerivAt f _ x
    . fun_prop (disch := solve_by_elim)
    convert this using 1; ring
  apply strictMonoOn_of_deriv_pos (convex_Ioo ..) (by fun_prop (disch := solve_by_elim))
  rw [interior_Ioo]
  intro x hx
  rw [hf' x |>.deriv]; clear * - hr hx
  field_simp [sin_pos_r hr hx]
  rw [zero_mul]

  suffices StrictMonoOn (fun x => g x) (Ico 0 (π / r)) by
    convert this (a := 0) (b := x) (by grind) (by grind) (by grind); simp [g]
  have hg' x : HasDerivAt g ((r ^ 2 - 1) * sin x * sin (r * x)) x := by
    have : HasDerivAt g _ x
    . fun_prop
    convert this using 1; ring
  apply strictMonoOn_of_deriv_pos (convex_Ico ..) (by fun_prop)
  rw [interior_Ico]
  intro x hx
  rw [hg' x |>.deriv]; clear * - hr hx

  have : 0 < r ^ 2 - 1 := by nlinarith
  have : 0 < sin x := by grind
  have : 0 < sin (r * x) := by grind
  positivity
end Short



namespace Long
lemma Real.tan_strictConvexOn : StrictConvexOn ℝ (Ico 0 (π / 2)) tan := by
  apply strictConvexOn_of_deriv2_pos (convex_Ico ..) (continuousOn_tan_Ioo.mono (by grind))
  rw [interior_Ico]
  intro x hx
  simp_rw [Function.iterate_succ_apply, Function.iterate_zero_apply, funext deriv_tan, one_div]
  have hc : 0 < cos x := by grind [cos_pos_of_mem_Ioo]
  rw [deriv_fun_inv'' (by fun_prop) (by simp; try bound)]
  simp only [differentiableAt_cos, deriv_fun_pow, deriv_cos']
  norm_num; field_simp
  have : π / 2 < π := by bound
  grind [sin_pos_of_mem_Ioo]


variable {r : ℝ} (hr : 1 < r)
include hr

@[bound, grind →] lemma pi_div_lt : π / r < π := by bound
@[grind =, grind =_] lemma mul_lt_pi {x : ℝ} : x < π / r ↔ r * x < π := by rw [← lt_div_iff₀']; cutsat
attribute [grind! .] mul_pos div_pos inv_pos sin_pos_of_mem_Ioo cos_pos_of_mem_Ioo tan_pos_of_pos_of_lt_pi_div_two
@[bound, grind! .] lemma sin_pos_r {x : ℝ} (hx : x ∈ Ioo 0 (π / r)) : 0 < sin (r * x) := by grind

theorem bob : StrictMonoOn (fun x => sin x / sin (r * x)) (Ico 0 (π / r)) := by
  -- It suffices that log ∘ f is strictly increasing on (0, π/r)
  set f := fun x => sin x / sin (r * x)
  have f_pos x (hx : x ∈ Ioo 0 (π / r) := by grind) : 0 < f x := by grind
  intro x hx y hy hxy
  obtain rfl | x_pos : x = 0 ∨ 0 < x := hx.1.eq_or_lt'
  . aesop
  rw [← log_lt_log_iff (f_pos x) (f_pos y)]
  suffices StrictMonoOn (log ∘ f) (Ioo 0 (π / r)) by grind [StrictMonoOn]

  -- This is equal to x ↦ log sin x - log sin(rx)
  let g x := log (sin x)
  have : EqOn (log ∘ f) (fun x => g x - g (r * x)) (Ioo 0 (π / r)) := by grind [EqOn, log_div]
  refine .congr ?_ this.symm
  clear * - hr

  -- It suffices that the derivative, cot x - r cot(rx), is positive
  have hg' x (hx : x ∈ Ioo 0 π := by grind) : HasDerivAt g x.cot x :=
    cot_eq_cos_div_sin x ▸ (hasDerivAt_sin x |>.log (by grind))
  have h' x (hx : x ∈ Ioo 0 (π / r)) :
      HasDerivAt (fun x => g x - g (r * x)) (cot x - cot (r * x) * r) x := by
    convert hg' x |>.sub <| hg' (x * r) |>.comp x <| hasDerivAt_mul_const r using 2
      <;> (dsimp; ring_nf)
  apply strictMonoOn_of_deriv_pos (convex_Ioo ..) (HasDerivAt.continuousOn h')
  rw [interior_Ioo]
  peel h' with x hx h'
  rw [h'.deriv]

  -- It suffices that x cot x is decreasing on (0, π)
  suffices r * x * cot (r * x) < x * cot x by
    cases hx; linear_combination (norm := field_simp) x⁻¹ * this; cutsat
  suffices StrictAntiOn (fun x => x * cot x) (Ioo 0 π) from
    this (by grind) (by grind) (by cases hx; linear_combination x * hr)
  clear * -

  -- Split into (0, π/2] ∪ [π/2, π)
  rw [← Ioc_union_Ico_eq_Ioo (b := π / 2) (by bound) (by bound)]
  refine .union (c := π / 2) ?hl ?hr
    (isGreatest_Ioc <| by bound) (isLeast_Ico <| by bound)

  -- On (0, π/2]:
  case hl =>
    -- Reduce to (0, π/2) and take the reciprocal
    rw [← Ioo_insert_right (by bound), strictAntiOn_insert_iff_of_forall_le (by grind)]
    constructor
    . simp [cot_eq_cos_div_sin]; grind
    suffices StrictMonoOn (fun x => tan x / x) (Ioo 0 (π / 2)) by
      refine inv_strictAntiOn.comp_strictMonoOn this (by grind [MapsTo]) |>.congr ?_
      grind [EqOn, cot_eq_cos_div_sin, tan_eq_sin_div_cos]

    -- tan x / x is increasing because tan x is strictly convex
    intro x hx y hy hxy
    convert tan_strictConvexOn.secant_strict_mono (a := 0) (x := x) (y := y) _ _ _ _ _ _ using 1
    . simp
    . simp
    all_goals grind

  -- On [π/2, π), x ≥ 0 is increasing and cot x ≤ 0 is decreasing
  case hr =>
    have cot_anti : StrictAntiOn cot (Ioo 0 π) := by
      have : cot = tan ∘ (fun x => π/2 - x) := by
        ext; simp [cot_eq_cos_div_sin, tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub]
      rw [this]; clear this
      apply strictMonoOn_tan.comp_strictAntiOn
        <;> aesop (config := { introsTransparency? := some .default })
    replace cot_anti := cot_anti.mono (s₂ := Ico (π / 2) π) (Ico_subset_Ioo_left <| by bound)
    peel cot_anti with x hx y hy hxy _
    suffices cot x ≤ 0 by nlinarith [show 0 < x from hx.1.trans_lt' (by bound)]
    convert cot_anti.antitoneOn (a := π / 2) (by grind) hx hx.1
    simp [cot_eq_cos_div_sin]
end Long
