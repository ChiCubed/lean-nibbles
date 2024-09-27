import analysis.special_functions.pow
import analysis.special_functions.gamma
import data.set.pointwise.basic
import measure_theory.measurable_space
import measure_theory.measure.haar_of_basis
import measure_theory.measure.lebesgue
import measure_theory.measure.haar_lebesgue
import measure_theory.constructions.borel_space
import measure_theory.constructions.pi
import measure_theory.integral.layercake
import logic.lemmas
import tactic.equiv_rw

open set real measure measure_theory
open_locale ennreal pointwise topology

namespace please_help_me

section amgm

-- put this and other "mixed-types" am gm implementations
-- in the standard library?
theorem ennreal.geom_mean_le_arith_mean2_weighted (w₁ w₂ : ℝ) (p₁ p₂ : ℝ≥0∞)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
  p₁ ^ w₁ * p₂ ^ w₂ ≤ ennreal.of_real w₁ * p₁ + ennreal.of_real w₂ * p₂ :=
begin
  wlog hp : p₁ ≤ p₂,
  { convert this w₂ w₁ p₂ p₁ hw₂ hw₁ ((add_comm _ _).trans hw) (le_of_not_le hp) using 1; ring_nf },

  -- TODO all this casting stuff around sounds like
  -- it should be doable with skilled tactics
  obtain rfl | p₂_fin : p₂ = ∞ ∨ _ := le_top.eq_or_lt,
  { obtain rfl | w₂_pos := hw₂.eq_or_lt,
    { rw add_zero at hw, subst hw,
      simp only [ennreal.rpow_one, ennreal.rpow_zero, mul_one,
        ennreal.of_real_one, one_mul, ennreal.of_real_zero,
        zero_mul, add_zero, le_refl], },
    simp only [w₂_pos, with_top.mul_top, ne.def, ennreal.of_real_eq_zero,
      not_le, ennreal.add_top, le_top], },
  have p₁_fin := hp.trans_lt p₂_fin,

  rw [← ennreal.coe_to_nnreal p₁_fin.ne, ← ennreal.coe_to_nnreal p₂_fin.ne,
      ennreal.of_real, ennreal.of_real],
  norm_cast,
  convert nnreal.geom_mean_le_arith_mean2_weighted
    w₁.to_nnreal w₂.to_nnreal p₁.to_nnreal p₂.to_nnreal _,
  from (coe_to_nnreal _ hw₁).symm,
  from (coe_to_nnreal _ hw₂).symm,
  rw ← nnreal.coe_eq,
  push_cast,
  rw [coe_to_nnreal _ hw₁, coe_to_nnreal _ hw₂, hw],
end

end amgm

section brunn_minkowski_1d

lemma measure_eq_supr_is_compact {α : Type*}
  [measurable_space α] [topological_space α] {μ : measure α}
  [μ.regular] [sigma_finite μ] ⦃A : set α⦄ (A_meas : measurable_set A) (A_ne : A.nonempty) :
μ A = ⨆ K (H : K ⊆ A ∧ is_compact K ∧ K.nonempty), μ K :=
begin
  apply le_antisymm,
  swap,
  { rw supr_le_iff, intro i,
    rw supr_le_iff, rintro ⟨H, h⟩,
    exact measure_mono H, },
  rw ← measure.supr_restrict_spanning_sets A_meas,

  simp_rw [measure.restrict_apply A_meas],
  have : (⨆ i, μ (A ∩ spanning_sets μ i)) =
         (⨆ i, ⨆ (K ⊆ A ∩ spanning_sets μ i) (h : is_compact K), μ K),
  { refine supr_congr (λ i, _),
    apply measurable_set.measure_eq_supr_is_compact_of_ne_top,
    { have := measurable_spanning_sets μ i, measurability },
    exact (measure_inter_lt_top_of_right_ne_top $
      (measure_spanning_sets_lt_top μ i).ne).ne, },
  rw this, clear this,
  -- this is so cursed
  rw supr_le_iff, intro i,
  rw supr_le_iff, intro K,
  rw supr_le_iff, intro H,
  rw supr_le_iff, intro h,
  rw le_supr_iff, intros b ho,
  specialize ho K,
  rw supr_le_iff at ho,

  by_cases K_ne : K = ∅,
  { rw K_ne, simp only [measure_empty, zero_le'] },
  exact ho ⟨(subset_inter_iff.mp H).1, h, nonempty_iff_ne_empty.mpr K_ne⟩,
end

-- FIXME FIXME FIXME!!!
-- All the nonemptys everywhere should almost certainly be
-- instance parameters, probably, maybe.
variables {A B : set ℝ}
  (A_meas : measurable_set A) (B_meas : measurable_set B)
  (A_ne : A.nonempty) (B_ne : B.nonempty)

include A_ne B_ne

lemma brunn_minkowski_compact_1d
(hA : is_compact A) (hB : is_compact B) :
  volume A + volume B ≤ volume (A + B) :=
begin
  let A' := A + {Inf B},
  let B' := {Sup A} + B,

  have hA' : volume A = volume A',
  { simp only [A', add_singleton, image_add_right, measure_preimage_add_right] },
  have hB' : volume B = volume B',
  { simp only [B', singleton_add, image_add_left, measure_preimage_add] },
  have : volume (A' ∩ B') = 0,
  { convert @volume_singleton (Sup A + Inf B),
    rw eq_singleton_iff_unique_mem,
    split,
    from mem_inter (by simpa [A'] using hA.Sup_mem A_ne) (by simpa [B'] using hB.Inf_mem B_ne),
    intros x hx,
    rw mem_inter_iff at hx,
    apply le_antisymm,
    { rcases hx.1 with ⟨a, b, ha, hb, rfl⟩,
      exact add_le_add ((real.is_lub_Sup A A_ne hA.bdd_above).1 ha) (mem_singleton_iff.mp hb).le },
    { rcases hx.2 with ⟨a, b, ha, hb, rfl⟩,
      exact add_le_add (mem_singleton_iff.mp ha).ge ((real.is_glb_Inf B B_ne hB.bdd_below).1 hb) } },

  have A'_meas : measurable_set A',
  { simp only [A', add_singleton, image_add_right],
    have := hA.measurable_set, measurability, },

  rw [hA', hB', ← measure_union_add_inter' A'_meas B', this, add_zero],
  refine measure_mono (union_subset (add_subset_add_left _) (add_subset_add_right _)),
  from singleton_subset_iff.mpr (hB.Inf_mem B_ne),
  from singleton_subset_iff.mpr (hA.Sup_mem A_ne),
end

include A_meas B_meas

-- instance is_add_haar_measure_volume : 
--   measure.is_add_haar_measure (volume : measure ℝ) :=
-- by { rw ← add_haar_measure_eq_volume, apply_instance }

-- FIXME change argument order and parentheses (eg ⦃⦄)
-- to make this work better
lemma brunn_minkowski_1d :
  volume A + volume B ≤ volume (A + B) :=
begin
  simp_rw [measure_eq_supr_is_compact A_meas A_ne,
           measure_eq_supr_is_compact B_meas B_ne],
  apply ennreal.bsupr_add_bsupr_le',
  -- using local compactness this is a bit messy but whatever
  obtain ⟨a, ha⟩ := A_ne,
  exact ⟨{a}, singleton_subset_iff.mpr ha, is_compact_singleton, singleton_nonempty _⟩,
  obtain ⟨b, hb⟩ := B_ne,
  exact ⟨{b}, singleton_subset_iff.mpr hb, is_compact_singleton, singleton_nonempty _⟩,
  rintros i ⟨Hi, hi, i_ne⟩ j ⟨Hj, hj, j_ne⟩,
  refine (brunn_minkowski_compact_1d i_ne j_ne hi hj).trans _,
  exact measure_mono (add_subset_add Hi Hj),
end

end brunn_minkowski_1d

section

theorem ennreal_lintegral_eq_lintegral_meas_lt {α : Type*} [measurable_space α]
    {f : α → ℝ≥0∞} (μ : measure α) [sigma_finite μ] (f_meas : measurable f) :
  ∫⁻ ω, f ω ∂μ = ∫⁻ (t : ℝ) in Ioi 0, μ {a | ennreal.of_real t < f a} :=
begin
  obtain h | h := @eq_zero_or_pos _ _ (μ {a | f a = ∞}),
  { simp_rw [eq_top_iff, ← not_lt, ← ae_iff] at h,
    convert lintegral_eq_lintegral_meas_lt μ
      (λ x, show 0 ≤ (f x).to_real, from ennreal.to_real_nonneg)
      (by measurability) using 1,
    { exact (lintegral_congr_ae ∘ ae_eq_symm ∘ of_real_to_real_ae_eq $ h), },
    { refine (set_lintegral_congr_fun (by measurability) $
        filter.eventually_of_forall $ λ t ht,
        measure_congr $ filter.eventually.set_eq _),
      filter_upwards [h],
      intros a ha,
      rw [← not_iff_not, not_lt, not_lt],
      exact ennreal.le_of_real_iff_to_real_le ha.ne (mem_Ioi.mp ht).le, } },
  let c := μ {a | f a = ∞},
  convert eq.refl ∞; rw eq_top_iff,
  -- TODO rewrite these using ae_lt_top
  { exact (lintegral_eq_top_of_measure_eq_top_pos f_meas.ae_measurable h).ge, },
  { calc ∫⁻ (t : ℝ) in Ioi 0, μ {a | ennreal.of_real t < f a}
          ≥ ∫⁻ (t : ℝ) in Ioi 0, c
      : lintegral_mono $ λ t, measure_mono $ set_of_subset_set_of.mpr $
        λ a ha, ha.substr ennreal.of_real_lt_top
      ... = c * volume (Ioi 0 : set ℝ)     : set_lintegral_const _ _
      ... = ∞                              : by rw [volume_Ioi, with_top.mul_top h.ne'] },
end

-- also you can prove this theorem for different measure spaces or wtv
-- (just for funsies, later)
parameters (f g h : ℝ → ℝ≥0∞)
  (f_meas : measurable f) (g_meas : measurable g) (h_meas : measurable h)
  (a b : ℝ) (a_nn : 0 ≤ a) (b_nn : 0 ≤ b) (hab : a + b = 1)
  (f_ineq : ∀ x y, f (a * x + b * y) ≥ g x ^ a * h y ^ b)

-- FIXME better parameter handling stuff
include f g h f_meas g_meas h_meas a b hab f_ineq

-- FIXME open ennreal!
lemma slice_lemma (a_pos : 0 < a) (b_pos : 0 < b) {u v w : ℝ≥0∞}
      (hu : ∃ x, u < g x) (hv : ∃ y, v < h y)
      (hw : w ≤ u ^ a * v ^ b) :
  volume {x | w < f x} ≥ ennreal.of_real a * volume {x | u < g x} + ennreal.of_real b * volume {y | v < h y} := 
begin
  have : ∀ {r : ℝ} (r_nn : 0 ≤ r) (s : set ℝ),
    volume (r • s) = ennreal.of_real r * volume s :=
  λ r r_nn s, by rw [measure.add_haar_smul , finite_dimensional.finrank_self, pow_one, abs_of_nonneg r_nn],

  rw [← this a_pos.le, ← this b_pos.le],
  clear this,

  rcases hu with ⟨x, hx⟩,
  rcases hv with ⟨y, hy⟩,
  refine ge_trans (measure_mono _) (brunn_minkowski_1d
  -- TODO this can't be solved by the measurability tactic atm
    ((measurable_set_lt measurable_const g_meas).const_smul₀ a)
    ((measurable_set_lt measurable_const h_meas).const_smul₀ b)
    ⟨a * x, smul_mem_smul_set hx⟩ ⟨b * y, smul_mem_smul_set hy⟩),
  clear' x hx y hy,
  
  rintros _ ⟨u, v, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, rfl⟩,
  rw mem_set_of_eq at ⊢ hx hy,
  calc w ≤ u ^ a * v ^ b       : hw
     ... < g x ^ a * h y ^ b   : _
     ... ≤ f (a * x + b * y)   : f_ineq _ _,
  exact ennreal.mul_lt_mul (ennreal.rpow_lt_rpow hx a_pos) (ennreal.rpow_lt_rpow hy b_pos),
end

lemma prekopa_leindler_1d_supr_inf (a_pos : 0 < a) (b_pos : 0 < b)
    (hg : 0 < ∫⁻ x, g x) (ch_inf : supr h = ∞) :
  ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b :=
begin
  suffices : ∞ ≤ ∫⁻ x, f x, from (eq_top_iff.mpr this).substr le_top,

  obtain ⟨u, u_pos, hu⟩ :
    ∃ (t : ℝ≥0∞) (t_pos : 0 < t), (0 : ℝ≥0∞) < volume {x | t < g x},
  { rw ennreal_lintegral_eq_lintegral_meas_lt at hg,
    swap, from g_meas,
    contrapose! hg,
    simp_rw [le_zero_iff] at ⊢ hg,
    replace hg : ∀ (t : ℝ), 0 < t → volume {x | ennreal.of_real t < g x} = 0 :=
    λ t ht, hg (ennreal.of_real t) (ennreal.of_real_pos.mpr ht),
    simp_rw [← mem_Ioi] at hg,
    -- TODO phrase this better?
    rw [← zero_mul (volume (Ioi (0 : ℝ))), ← set_lintegral_const],
    convert set_lintegral_congr_fun _ _,
    { measurability, },
    { exact ae_of_all _ hg, }, },
  set c := volume {x | u < g x},

  -- TODO here on is just bad
  suffices : ∀ (n : ℕ), ↑n * (ennreal.of_real a * c) ≤ ∫⁻ x, f x,
  { convert supr_le this,
    rw [← ennreal.supr_mul, ennreal.supr_coe_nat, ennreal.top_mul],
    simp only [(ennreal.mul_pos (ennreal.of_real_pos.mpr a_pos).ne' hu.ne').ne', if_false] },
  
  suffices : ∀ (ε : ℝ≥0∞) (ε_pos : 0 < ε) (ε_fin : ε < ∞),
    ennreal.of_real a * c ≤ volume {x | ε < f x},
  { intro n,
    obtain rfl | n_pos := n.eq_zero_or_pos,
    { simp only [algebra_map.coe_zero, zero_mul, zero_le'], },
    replace this : ennreal.of_real a * c ≤ volume {x | ↑n < f x} :=
    this n (nat.cast_pos.mpr n_pos) ennreal.coe_lt_top,

    calc ↑n * _
          ≤ ↑n * volume {x | ↑n ≤ f x}
      : mul_le_mul_left' (this.trans $ measure_mono $ λ x, le_of_lt) _
      ... ≤ ∫⁻ x, f x
      : mul_meas_ge_le_lintegral f_meas n },
  
  intros w w_pos w_fin,
  obtain ⟨x, hx⟩ : ∃ x, u < g x := nonempty_of_measure_ne_zero hu.ne',
  obtain ⟨v, v_fin, huv⟩ : ∃ v (v_fin : v < ∞), w ≤ u ^ a * v ^ b,
  { have ua_pos := ennreal.rpow_pos_of_nonneg u_pos a_pos.le,
    use (w / u ^ a) ^ b⁻¹,
    split, from ennreal.rpow_lt_top_of_nonneg
      (inv_nonneg_of_nonneg b_pos.le)
      (ennreal.div_lt_top w_fin.ne ua_pos.ne').ne,
    rw [← ennreal.rpow_mul, inv_mul_cancel b_pos.ne', ennreal.rpow_one,
      ennreal.mul_div_cancel'],
    from le_refl _,
    from ua_pos.ne',
    from (ennreal.rpow_lt_top_of_nonneg a_pos.le hx.ne_top).ne, },
  obtain ⟨y, hy⟩ : ∃ y, v < h y := ((supr_eq_top _).mp ch_inf) v v_fin,
  -- TODO why isn't "parameters" working?
  exact le_self_add.trans (slice_lemma
    f g h f_meas g_meas h_meas a b hab f_ineq
    a_pos b_pos ⟨x, hx⟩ ⟨y, hy⟩ huv),
end

-- TODO is measurability even necessary at all?
lemma prekopa_leindler_1d_supr_1 (a_pos : 0 < a) (b_pos : 0 < b)
    (hg : supr g = 1) (hh : supr h = 1) :
  ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b :=
begin
  rw [ennreal_lintegral_eq_lintegral_meas_lt volume f_meas,
      ennreal_lintegral_eq_lintegral_meas_lt volume g_meas,
      ennreal_lintegral_eq_lintegral_meas_lt volume h_meas],
  
  refine (ennreal.geom_mean_le_arith_mean2_weighted _ _ _ _ a_pos.le b_pos.le hab)
    .trans _,
  rw [← lintegral_const_mul, ← lintegral_const_mul, ← lintegral_add_left],
  { refine lintegral_mono (λ t, _),
    obtain ht | ht := lt_or_le (ennreal.of_real t) 1,
    { apply slice_lemma; try { assumption },
      from exists_lt_of_lt_csupr (hg.substr ht),
      from exists_lt_of_lt_csupr (hh.substr ht),
      obtain ht₂ | ht₂ := eq_or_ne (ennreal.of_real t) 0,
      from ht₂.trans_le (zero_le _),
      rw [← ennreal.rpow_add, hab, ennreal.rpow_one], from le_refl _,
      from ht₂,
      from ennreal.of_real_lt_top.ne, },
    { refine eq.trans_le _ (zero_le _),
      rw [add_eq_zero_iff],
      split, all_goals
      { apply mul_eq_zero_of_right,
        convert measure_empty using 2,
        refine eq_empty_of_forall_not_mem (λ x, _),
        rw mem_set_of_eq,
        exact not_lt_of_le (((le_supr _ x).trans_eq $ by assumption).trans ht) } } },
  all_goals
  { try { apply measurable.const_mul },
    apply antitone.measurable,
    intros t₁ t₂ ht,
    apply measure_mono,
    rw set_of_subset_set_of,
    exact λ _, (ennreal.of_real_le_of_real ht).trans_lt, },
end

include a_nn b_nn

theorem prekopa_leindler_1d : 
  ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b :=
begin
  have sym₁ : b + a = 1 := by rw [add_comm, hab],
  have sym₂ : ∀ x y, f (b * x + a * y) ≥ h x ^ b * g y ^ a,
  { intros, convert f_ineq y x using 1; ring_nf},

  wlog h₁ : a ≤ b generalizing a b g h,
  { rw mul_comm, apply this; assumption <|> exact le_of_not_le h₁ },
  obtain rfl | a_pos := a_nn.eq_or_lt,
  { rw zero_add at hab, subst hab,
    convert lintegral_mono (show f ≥ h, by simpa using f_ineq),
    simp only [ennreal.rpow_zero, ennreal.rpow_one, one_mul] },
  have b_pos := a_pos.trans_le h₁,
  clear a_nn b_nn h₁,
  
  wlog h₂ : supr g ≤ supr h generalizing a b g h,
  { rw mul_comm, apply this; assumption <|> exact le_of_not_le h₂ },
  clear sym₁ sym₂,

  obtain hg | hg := @eq_zero_or_pos _ _ (∫⁻ x, g x),
  { rw [hg, ennreal.zero_rpow_of_pos a_pos, zero_mul], exact zero_le' },

  have cg_pos : 0 < supr g,
  { contrapose! hg,
    rw le_zero_iff at ⊢ hg,
    rw ennreal.supr_eq_zero at hg,
    simp_rw [hg, lintegral_zero], },
  have ch_pos : 0 < supr h := cg_pos.trans_le h₂,
  
  obtain ch_inf | ch_fin : supr h = ∞ ∨ _ := le_top.eq_or_lt,
  from prekopa_leindler_1d_supr_inf f g h f_meas g_meas h_meas a b hab f_ineq
    a_pos b_pos hg ch_inf,
  have cg_fin : supr g < ∞ := h₂.trans_lt ch_fin,

  clear hg h₂,

  set cgi := (supr g)⁻¹,
  set chi := (supr h)⁻¹,
  let c := cgi ^ a * chi ^ b,
  have cgi_pos := ennreal.inv_pos.mpr cg_fin.ne,
  have chi_pos := ennreal.inv_pos.mpr ch_fin.ne,
  have cgi_fin := ennreal.inv_lt_top.mpr cg_pos,
  have chi_fin := ennreal.inv_lt_top.mpr ch_pos,
  have c_pos : 0 < c := ennreal.mul_pos (ennreal.rpow_pos cgi_pos cgi_fin.ne).ne' (ennreal.rpow_pos chi_pos chi_fin.ne).ne',
  have c_fin : c < ∞ := ennreal.mul_lt_top (ennreal.rpow_lt_top_of_nonneg a_pos.le cgi_fin.ne).ne (ennreal.rpow_lt_top_of_nonneg b_pos.le chi_fin.ne).ne,

  let f' := λ x, c * f x,
  let g' := λ x, cgi * g x,
  let h' := λ x, chi * h x,

  convert_to ∫⁻ x, f' x ≥ (∫⁻ x, g' x) ^ a * (∫⁻ x, h' x) ^ b using 0,
  { ext, simp only [f', g', h'],
    rw [lintegral_const_mul, lintegral_const_mul, lintegral_const_mul], assumption',
    rw [ennreal.mul_rpow_of_nonneg _ _ a_pos.le, ennreal.mul_rpow_of_nonneg _ _ b_pos.le],
    convert (ennreal.mul_le_mul_left c_pos.ne' c_fin.ne).symm using 1,
    simp only [c], ring_nf, },
  apply prekopa_leindler_1d_supr_1,
  { measurability },
  { measurability },
  { measurability },
  from hab,
  { intros x y,
    convert (ennreal.mul_le_mul_left c_pos.ne' c_fin.ne).mpr (f_ineq x y) using 1,
    simp only [g', h'],
    rw [ennreal.mul_rpow_of_nonneg _ _ a_pos.le, ennreal.mul_rpow_of_nonneg _ _ b_pos.le],
    simp only [c], ring_nf, },
  from a_pos,
  from b_pos,
  from ennreal.mul_supr.symm.trans (ennreal.inv_mul_cancel cg_pos.ne' cg_fin.ne),
  from ennreal.mul_supr.symm.trans (ennreal.inv_mul_cancel ch_pos.ne' ch_fin.ne),
end

end

section sus_equivs

parameters {α β : Type*} (e : α ≃ β) [fintype α] [fintype β]

@[reducible] def pi_real_mequiv_of_equiv :
  (α → ℝ) ≃ᵐ (β → ℝ) :=
{ to_equiv := e.arrow_congr (equiv.refl ℝ),
  measurable_to_fun :=
    measurable_pi_lambda _ (λ b, measurable_pi_apply (e.symm b)),
  measurable_inv_fun :=
    measurable_pi_lambda _ (λ a, measurable_pi_apply (e a)) }

lemma volume_preserving_pi_real_mequiv_of_equiv :
  measure_preserving pi_real_mequiv_of_equiv :=
{ measurable := measurable_equiv.measurable_to_fun _,
  map_eq := begin
    refine (measure.pi_eq $ λ s hs, _).symm,
    rw measurable_equiv.map_apply,
    change volume {x : α → ℝ | (λ b, x (e.symm b)) ∈ univ.pi s} = _,
    simp_rw mem_univ_pi,
    convert_to volume (univ.pi $ s ∘ e) = _,
    { congr, ext x,
      apply e.forall_congr_left.symm.trans,
      apply forall_congr, intro a,
      have : a ∈ univ := mem_univ a,
      -- LEM isn't necessary, right? whatever
      rw e.symm_apply_apply, tauto! },
    rw volume_pi_pi,
    exact e.prod_comp (volume ∘ s),
  end }

lemma linear_map_pi_real_mequiv_of_equiv :
  is_linear_map ℝ pi_real_mequiv_of_equiv :=
{ map_add := λ x y, by { ext, refl },
  map_smul := λ c x, by { ext, refl }, }

parameters (α β)

@[reducible] def pi_real_mequiv_of_sum :
  (α ⊕ β → ℝ) ≃ᵐ (α → ℝ) × (β → ℝ) :=
{ to_equiv := equiv.sum_arrow_equiv_prod_arrow _ _ _,
  measurable_to_fun := begin
    refine (measurable_pi_lambda _ (λ a, _)).prod
           (measurable_pi_lambda _ (λ b, _)),
    exact measurable_pi_apply (sum.inl a),
    exact measurable_pi_apply (sum.inr b),
  end,
  measurable_inv_fun := begin
    refine measurable_pi_lambda _ (λ x, _),
    cases x,
    exact measurable_fst.eval,
    exact measurable_snd.eval,
  end }

lemma volume_preserving_pi_real_mequiv_of_sum :
  measure_preserving pi_real_mequiv_of_sum :=
measure_preserving.symm pi_real_mequiv_of_sum.symm $
{ measurable := measurable_equiv.measurable_inv_fun _,
  map_eq := begin
    refine (measure.pi_eq $ λ s hs, _).symm,
    rw measurable_equiv.map_apply,
    change volume {x : (α → ℝ) × (β → ℝ) | sum.elim x.1 x.2 ∈ univ.pi s} = _,
    simp_rw mem_univ_pi,
    convert_to volume (univ.pi (s ∘ sum.inl) ×ˢ univ.pi (s ∘ sum.inr)) = _,
    { congr, ext x,
      simp only [sum.forall, sum.elim_inl, sum.elim_inr, mem_univ_pi], },
    simp_rw [measure.volume_eq_prod, measure.prod_prod, volume_pi_pi, fintype.prod_sum_type],
  end }

lemma linear_map_pi_real_mequiv_of_sum :
  is_linear_map ℝ pi_real_mequiv_of_sum :=
{ map_add := λ x y, by { ext; refl },
  map_smul := λ c x, by { ext; refl } }

end sus_equivs

section prekopa_leindler

@[reducible] private def has_prekopa_leindler (α : Type*) [add_comm_monoid α] [module ℝ α] [measure_space α] :=
  ∀ (f g h : α → ℝ≥0∞)
    (f_meas : measurable f) (g_meas : measurable g) (h_meas : measurable h)
    (a b : ℝ) (a_nn : 0 ≤ a) (b_nn : 0 ≤ b) (hab : a + b = 1)
    (f_ineq : ∀ x y, f (a • x + b • y) ≥ g x ^ a * h y ^ b),
  ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b

lemma has_prekopa_leindler_of_volume_preserving_linear_map {α β}
    [add_comm_monoid α] [module ℝ α] [measure_space α]
    [add_comm_monoid β] [module ℝ β] [measure_space β]
    (φ : α →ₗ[ℝ] β) (hφ : measure_preserving φ) (hα : has_prekopa_leindler α) :
  has_prekopa_leindler β :=
begin
  rw has_prekopa_leindler, intros,
  
  have f'_ineq : ∀ x y, (f ∘ φ) (a • x + b • y) ≥ (g ∘ φ) x ^ a * (h ∘ φ) y ^ b,
  { intros x y,
    simp only [function.comp_app, map_add, linear_map.map_smulₛₗ, ring_hom.id_apply],
    apply f_ineq },

  convert hα (f ∘ φ) (g ∘ φ) (h ∘ φ)
    (f_meas.comp hφ.measurable)
    (g_meas.comp hφ.measurable)
    (h_meas.comp hφ.measurable)
    a b a_nn b_nn hab f'_ineq,
  all_goals { rwa hφ.lintegral_comp },
end

lemma has_prekopa_leindler_empty {ι : Type*} [is_empty ι] :
  has_prekopa_leindler (ι → ℝ) :=
begin
  rw has_prekopa_leindler, intros,
  simp_rw [lintegral_unique, volume_pi, measure.pi_univ,
    finset.prod_of_empty, mul_one],
  convert f_ineq 0 0,
end

lemma has_prekopa_leindler_1d :
  has_prekopa_leindler ℝ :=
prekopa_leindler_1d

lemma has_prekopa_leindler_equiv {α β} [fintype α] [fintype β] (e : α ≃ β)
    (hα : has_prekopa_leindler (α → ℝ)) :
  has_prekopa_leindler (β → ℝ) :=
begin
  let e' := pi_real_mequiv_of_equiv e,
  refine has_prekopa_leindler_of_volume_preserving_linear_map
    (e'.to_linear_equiv (linear_map_pi_real_mequiv_of_equiv _)).to_linear_map
    (volume_preserving_pi_real_mequiv_of_equiv _)
    _,
  convert hα,
end

lemma has_prekopa_leindler_tensorial {α β} [fintype α] [fintype β]
    (hα : has_prekopa_leindler (α → ℝ)) (hβ : has_prekopa_leindler (β → ℝ)) :
  has_prekopa_leindler (α ⊕ β → ℝ) :=
begin
  let e := pi_real_mequiv_of_sum α β,
  refine has_prekopa_leindler_of_volume_preserving_linear_map
    (e.to_equiv.to_linear_equiv $ linear_map_pi_real_mequiv_of_sum _ _).symm.to_linear_map
    ((volume_preserving_pi_real_mequiv_of_sum α β).symm e)
    _,
  clear e,

  rw has_prekopa_leindler, intros,

  rw [measure.volume_eq_prod, lintegral_prod, lintegral_prod, lintegral_prod],
  any_goals { exact measurable.ae_measurable (by assumption) },

  refine hα _ _ _
    f_meas.lintegral_prod_right'
    g_meas.lintegral_prod_right'
    h_meas.lintegral_prod_right'
    _ _ a_nn b_nn hab (λ x₁ y₁, _),
  refine hβ _ _ _
    (f_meas.comp measurable_prod_mk_left)
    (g_meas.comp measurable_prod_mk_left)
    (h_meas.comp measurable_prod_mk_left)
    _ _ a_nn b_nn hab (λ x₂ y₂, _),
  apply f_ineq,
end

lemma has_prekopa_leindler_induction (ι : Type*) [fintype ι] :
  has_prekopa_leindler (ι → ℝ) :=
begin
  revertI ι,
  refine fintype.induction_empty_option _ _ _,

  { introsI α β _ e hα,
    haveI : fintype α := @fintype.of_equiv α β _ e.symm,
    apply has_prekopa_leindler_equiv e,
    convert hα },
  { apply has_prekopa_leindler_empty },
  { introsI α _ hα,
    refine has_prekopa_leindler_equiv (equiv.option_equiv_sum_punit α).symm _,
    refine has_prekopa_leindler_tensorial hα _,
    let e := measurable_equiv.fun_unique punit ℝ,
    exact has_prekopa_leindler_of_volume_preserving_linear_map
      (e.to_linear_equiv ⟨λ x y, rfl, λ (c:ℝ) x, rfl⟩).symm.to_linear_map
      ((volume_preserving_fun_unique _ _).symm e)
      has_prekopa_leindler_1d },
end

parameters {ι : Type*} [fintype ι]
parameters (f g h : (ι → ℝ) → ℝ≥0∞)
  (f_meas : measurable f) (g_meas : measurable g) (h_meas : measurable h)
  (a b : ℝ) (a_nn : 0 ≤ a) (b_nn : 0 ≤ b) (hab : a + b = 1)
  (f_ineq : ∀ x y, f (a • x + b • y) ≥ g x ^ a * h y ^ b)

include f g h f_meas g_meas h_meas a b a_nn b_nn hab f_ineq

theorem prekopa_leindler :
  ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b :=
by apply has_prekopa_leindler_induction; assumption

end prekopa_leindler

section brunn_minkowski

variables {ι : Type*} [fintype ι]
variables (A B : set (ι → ℝ))
  (A_meas : measurable_set A) (B_meas : measurable_set B)

include A B A_meas B_meas

-- note that you can have a, b ∈ [0, 1] instead
-- at the cost of requiring A, B nonempty.
theorem brunn_minkowski_multiplicative
    (a b : ℝ) (a_pos : 0 < a) (b_pos : 0 < b) (hab : a + b = 1) :
  volume (a • A + b • B) ≥ volume A ^ a * volume B ^ b :=
begin
  rw ← measure_to_measurable,
  set C := to_measurable volume (a • A + b • B),
  have C_meas : measurable_set C := measurable_set_to_measurable _ _,

  convert_to 1 * volume C ≥ (1 * volume A) ^ a * (1 * volume B) ^ b,
  { simp_rw one_mul }, { simp_rw one_mul },
  rw [← lintegral_indicator_const, ← lintegral_indicator_const, ← lintegral_indicator_const],
  assumption',

  apply prekopa_leindler,
  { measurability }, { measurability }, { measurability },
  from a_pos.le,
  from b_pos.le,
  from hab,

  intros x y,
  by_cases hx : x ∈ A,
  swap,
  { rw [indicator_of_not_mem hx, ennreal.zero_rpow_of_pos a_pos, zero_mul],
    from zero_le _ },
  by_cases hy : y ∈ B,
  swap,
  { rw [indicator_of_not_mem hy, ennreal.zero_rpow_of_pos b_pos, mul_zero],
    from zero_le _ },
  rw [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem
    (show a • x + b • y ∈ C, from subset_to_measurable _ _ ⟨_, _, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, rfl⟩)],
  simp_rw [ennreal.one_rpow, one_mul],
  from le_refl _,
end

variables (A_ne : A.nonempty) (B_ne : B.nonempty)
include A_ne B_ne

theorem brunn_minkowski [nonempty ι] :
  let n := fintype.card ι in
  volume (A + B) ^ (n⁻¹ : ℝ) ≥ volume A ^ (n⁻¹ : ℝ) + volume B ^ (n⁻¹ : ℝ) :=
begin
  intro n,
  have n_pos : 0 < n := fintype.card_pos,
  have cn_pos : 0 < (n : ℝ) := nat.cast_pos.mpr n_pos,
  have icn_pos : 0 < (n⁻¹ : ℝ) := inv_pos.mpr cn_pos,

  wlog h : volume A ≤ volume B generalizing A B,
  { rw add_comm, conv_rhs { rw add_comm },
    replace h := le_of_not_le h,
    apply this; assumption, },
  -- TODO there's some redundancy here
  obtain vA_z | vA_pos : 0 = volume A ∨ _ := zero_le'.eq_or_lt,
  { rw [ge_iff_le, ← vA_z, ennreal.zero_rpow_of_pos icn_pos, zero_add, ennreal.rpow_le_rpow_iff icn_pos],
    rcases A_ne with ⟨a, ha⟩,
    rw (show volume B = volume ({a} + B),
      by simp only [singleton_add, image_add_left, measure_preimage_add]),
    exact (measure_mono $ add_subset_add_right $ singleton_subset_iff.mpr ha) },
  have vB_pos : 0 < volume B := vA_pos.trans_le h,
  obtain vB_inf | vB_fin : volume B = ∞ ∨ _ := le_top.eq_or_lt,
  { rcases A_ne with ⟨a, ha⟩,
    rw (show volume B = volume ({a} + B),
      by simp only [singleton_add, image_add_left, measure_preimage_add]) at vB_inf,
    refine le_top.trans_eq (eq.symm _),
    rw ennreal.rpow_eq_top_iff_of_pos icn_pos,
    exact eq_top_mono (measure_mono $ add_subset_add_right $ singleton_subset_iff.mpr ha) vB_inf },
  have vA_fin : volume A < ∞ := h.trans_lt vB_fin,
  clear h,
  
  let μn := λ (s : set (ι → ℝ)), volume s ^ (n⁻¹ : ℝ),
  let a := μn A,
  let b := μn B,
  let a' := (a / (a + b)).to_real,
  let b' := (b / (a + b)).to_real,
  let A' := a'⁻¹ • A,
  let B' := b'⁻¹ • B,

  have μn_linear : ∀ {r : ℝ} (r_nn : 0 ≤ r) s,
    μn (r • s) = ennreal.of_real r * μn s,
  { intros, simp only [μn],
    rw [measure.add_haar_smul,
      finite_dimensional.finrank_fintype_fun_eq_card, abs_pow, abs_of_nonneg r_nn,
      ennreal.of_real_pow r_nn, ennreal.mul_rpow_of_nonneg _ _ icn_pos.le,
      ← ennreal.rpow_nat_cast, ← ennreal.rpow_mul],
    change fintype.card ι with n,
    rw [mul_inv_cancel cn_pos.ne', ennreal.rpow_one] },

  have A'_meas : measurable_set A' := A_meas.const_smul₀ _,
  have B'_meas : measurable_set B' := B_meas.const_smul₀ _,
  have a_pos : 0 < a := ennreal.rpow_pos vA_pos vA_fin.ne,
  have b_pos : 0 < b := ennreal.rpow_pos vB_pos vB_fin.ne,
  have a_fin : a < ∞ := ennreal.rpow_lt_top_of_nonneg icn_pos.le vA_fin.ne,
  have b_fin : b < ∞ := ennreal.rpow_lt_top_of_nonneg icn_pos.le vB_fin.ne,
  have s_pos : 0 < a + b := add_pos' a_pos b_pos,
  have s_fin : a + b < ∞ := ennreal.add_lt_top.mpr ⟨a_fin, b_fin⟩,
  have a'_pos : 0 < a / (a + b) := ennreal.div_pos_iff.mpr ⟨a_pos.ne', s_fin.ne⟩,
  have b'_pos : 0 < b / (a + b) := ennreal.div_pos_iff.mpr ⟨b_pos.ne', s_fin.ne⟩,
  have a'_fin : a / (a + b) < ∞ := ennreal.div_lt_top a_fin.ne s_pos.ne',
  have b'_fin : b / (a + b) < ∞ := ennreal.div_lt_top b_fin.ne s_pos.ne',
  have a'_pos' : 0 < a' := ennreal.to_real_pos a'_pos.ne' a'_fin.ne,
  have b'_pos' : 0 < b' := ennreal.to_real_pos b'_pos.ne' b'_fin.ne,
  have ha'b' : a' + b' = 1,
  { simp only [a', b'],
    rw [← ennreal.to_real_add a'_fin.ne b'_fin.ne, ennreal.to_real_eq_one_iff,
      ← ennreal.add_div, ennreal.div_self s_pos.ne' s_fin.ne] },
  
  calc μn (A + B) = μn (a' • A' + b' • B')               : _
    ... ≥ (volume A' ^ a' * volume B' ^ b') ^ (n⁻¹ : ℝ)  : _
    ... = μn A' ^ a' * μn B' ^ b'                        : _
    ... = μn A + μn B                                    : _,
  { congr; simp only [A', B', smul_smul, one_smul,
      mul_inv_cancel a'_pos'.ne', mul_inv_cancel b'_pos'.ne'] },
  { refine (ennreal.rpow_le_rpow_iff icn_pos).mpr _,
    apply brunn_minkowski_multiplicative; assumption },
  { dsimp only [μn],
    rw [ennreal.mul_rpow_of_nonneg _ _ icn_pos.le],
    congr' 1; rw [← ennreal.rpow_mul, ← ennreal.rpow_mul, mul_comm], },
  { simp only [A', B'],
    rw [μn_linear (inv_pos_of_pos a'_pos').le, μn_linear (inv_pos_of_pos b'_pos').le,
      ← ennreal.of_real_inv_of_pos a'_pos', ← ennreal.of_real_inv_of_pos b'_pos'],
    erw [ennreal.of_real_to_real a'_fin.ne, ennreal.of_real_to_real b'_fin.ne],
    rw [ennreal.div_eq_inv_mul, ennreal.div_eq_inv_mul,
      ennreal.mul_inv (or.inr a_fin.ne) (or.inr a_pos.ne'),
      ennreal.mul_inv (or.inr b_fin.ne) (or.inr b_pos.ne'),
      inv_inv],
    conv_lhs
    { congr, rw [mul_assoc, ennreal.inv_mul_cancel a_pos.ne' a_fin.ne, mul_one],
      skip, rw [mul_assoc, ennreal.inv_mul_cancel b_pos.ne' b_fin.ne, mul_one] },
    rw [← ennreal.rpow_add _ _ s_pos.ne' s_fin.ne, ha'b', ennreal.rpow_one] },
end

-- TODO um it's a bit silly that you're allowing n = 0.
-- it might be worth to define a "linearized volume",
-- one which has units of nothing,
-- and think about what this should mean for n = 0.
-- so like n = 0... it's just a single point.
-- what should the linearized volume of that point be? ∞?
-- who even knows mate
theorem brunn_minkowski' :
  let n := fintype.card ι in
  volume (A + B) ≥ (volume A ^ (n⁻¹ : ℝ) + volume B ^ (n⁻¹ : ℝ)) ^ (n : ℝ) :=
begin
  intro n,

  obtain n_z | n_pos := n.eq_zero_or_pos,
  { haveI : is_empty ι := fintype.card_eq_zero_iff.mp n_z,
    obtain ⟨a, rfl⟩ := exists_eq_singleton_iff_nonempty_subsingleton.mpr
      ⟨A_ne, subsingleton_of_subsingleton⟩,
    obtain ⟨b, rfl⟩ := exists_eq_singleton_iff_nonempty_subsingleton.mpr
      ⟨B_ne, subsingleton_of_subsingleton⟩,
    rw [singleton_add_singleton, n_z, algebra_map.coe_zero, ennreal.rpow_zero,
      ← metric.closed_ball_zero, measure_theory.volume_pi_closed_ball, finset.prod_of_empty],
    from le_refl _, from le_refl _, },
  have cn_pos : 0 < (n : ℝ) := nat.cast_pos.mpr n_pos,
  have icn_pos : 0 < (n⁻¹ : ℝ) := inv_pos.mpr cn_pos,

  haveI : nonempty ι := fintype.card_pos_iff.mp n_pos,
  rw [ge_iff_le, ← ennreal.le_rpow_one_div_iff cn_pos, ← inv_eq_one_div],
  apply brunn_minkowski; assumption,
end

end brunn_minkowski

section minkowski_content

variables {ι : Type*} [fintype ι]

noncomputable def sphere_vol (m : ℝ) :=
real.pi ^ (m / 2) / real.Gamma (m / 2 + 1)

noncomputable def lower_minkowski_content (d : ℝ) (A : set (ι → ℝ)) :=
let n := fintype.card ι in
filter.liminf
  (λ r : ℝ, volume (metric.thickening r A) / ennreal.of_real (sphere_vol (↑n - d) * r ^ (↑n - d)))
  (𝓝[>] 0) 

notation (name := lower_minkowski_content) `ℳ⁻[` d `]` := lower_minkowski_content d

end minkowski_content

-- so the proof goes like...
-- μ (A + ε B) ≥ (μ A ^ 1/n + ε * μ B ^ 1/n) ^ n
-- μ (A + ε B) ≥ (μ A + ε * μ A ^ (1 - 1/n) * μ B ^ 1/n + o(ε))
-- μ (A + ε B) = μ A + ε |∂A| + ...
-- (prove it or whatever)

-- basically we need A to be nice enough that
-- |∂A| = lim inf (μ (A + ε B) - μ A) / ε.
-- indeed if we take this as the definition the result is
-- (basically) immediate.
-- to try: consider the "volume function" V ε := μ (A + ε B).
-- see https://arxiv.org/pdf/1610.03117.pdf
-- see https://www.jstor.org/stable/pdf/24903398.pdf
-- see file:///C:/Users/alber/Downloads/978-3-642-62010-2.pdf
--     p. 278

-- other things to do:
-- inside (A + ε B) ∖ A,
-- you can draw "outside" {0 < d x A < ε}. in fact it
-- coincides exactly with this for A closed or something?
-- up to closure of B at least.


-- well okay so the actual definition:
-- μM⁻ S := lim inf as x → 0 $ λ x, μ {x | d x S < r} / α^? r^?

-- well what you really want is something proving that:
-- 

-- eventually we want to end up with:
-- (|∂A| / |∂B|) ^ 1/(n-1) ≥ (μ A / μ B) ^ 1/n
-- or equivalently,
-- |∂A| ^ 1/(n-1) / (μ A) ^ 1/n ≥ |∂B| ^ 1/(n-1) / (μ B) ^ 1/n
-- or any of a bunch of other forms i guess.

end please_help_me