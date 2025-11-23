import Mathlib

open MeasureTheory ProbabilityTheory

/-!
If you roll a die until you get an odd number, the expected stopping time (0-indexed) is 1.
-/




namespace MeasureTheory

open scoped ENNReal Topology

open Set Filter Measure

variable {α : Type*} [MeasurableSpace α]

theorem lintegral_eq_lintegral_meas_le'
  {f : α → ENNReal}
  (μ : Measure α)
  (f_mble : AEMeasurable f μ) :
    ∫⁻ ω, f ω ∂μ = ∫⁻ t : ℝ in Ioi 0, μ {ω | .ofReal t ≤ f ω} := by
  by_cases h_top : μ {x | f x = ⊤} = 0
  . rw [← compl_mem_ae_iff] at h_top
    have : f =ᵐ[μ] ENNReal.ofReal ∘ ENNReal.toReal ∘ f := by
      rw [← Function.comp_assoc]
      filter_upwards [h_top]
      aesop
    rw [lintegral_congr_ae this]; clear this
    simp_rw [Function.comp_apply]
    rw [lintegral_eq_lintegral_meas_le μ (by filter_upwards; simp) f_mble.ennreal_toReal]
    congr with x
    apply measure_congr
    filter_upwards [h_top] with a ha
    ext; symm; apply ENNReal.ofReal_le_iff_le_toReal
    simpa
  . rw [lintegral_eq_top_of_measure_eq_top_ne_zero f_mble h_top]
    rw [eq_comm, ← top_le_iff]
    calc
      ⊤ = ∫⁻ t : ℝ in Ioi 0, μ {x | f x = ⊤} := by simp [h_top]
      _ ≤ _                                   := by gcongr; aesop


theorem lintegral_eq_tsum_meas_lt
  {f : α → ENat}
  (μ : Measure α)
  (f_mble : AEMeasurable f μ) :
    ∫⁻ ω, f ω ∂μ = ∑' k : ℕ, μ {ω | k < f ω} := by
  erw [lintegral_eq_lintegral_meas_le' μ (measurable_of_countable ENat.toENNReal |>.comp_aemeasurable f_mble)]
  simp_rw [Function.comp_apply]

  have h_Ioc (i : ℕ) : Ioc (α := ℝ) i (i + 1) = Nat.ceil ⁻¹' {i + 1} := by
    rw [Nat.preimage_ceil_of_ne_zero] <;> simp

  have : restrict ℙ (Ioi (α := ℝ) 0) = sum (fun i : ℕ => restrict ℙ (Ioc (α := ℝ) i (i + 1))) := by
    rw [← restrict_iUnion]
    . congr with x
      simp [h_Ioc]
    . exact pairwise_disjoint_Ioc_intCast ℝ |>.comp_of_injective CharZero.cast_injective
    . simp
  rw [this]; clear this
  rw [lintegral_sum_measure]
  congr with i

  suffices ∀ a ∈ Ioc (α := ℝ) i (i + 1),
      μ {ω | ENNReal.ofReal a ≤ f ω} = μ {ω | i < f ω} by
    rw [setLIntegral_congr_fun (by simp) this]
    simp
  rw [h_Ioc]
  intro a ha
  congr! with ω
  induction f ω using ENat.recTopCoe with
  | top => simp
  | coe y =>
    simp only [ENat.toENNReal_coe, ENNReal.ofReal_le_natCast, Nat.cast_lt]
    rw [mem_preimage, mem_singleton_iff] at ha
    rw [← Nat.ceil_le, ha]
    omega


theorem lintegral_eq_tsum_meas_le
  {f : α → ENat}
  (μ : Measure α)
  (f_mble : AEMeasurable f μ) :
    ∫⁻ ω, f ω ∂μ = ∑' k : ℕ+, μ {ω | k ≤ f ω} := by
  rw [lintegral_eq_tsum_meas_lt μ f_mble, tsum_pnat_eq_tsum_succ (f := fun k => μ {ω | k ≤ f ω})]
  congr! 5 with n ω
  push_cast
  simp [ENat.add_one_le_iff]

end MeasureTheory


theorem NullMeasurable.ite {α β} {f g : α → β}
  {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α}
  {p : α → Prop} {_ : DecidablePred p}
  (hp : NullMeasurableSet {a | p a} μ) (hf : NullMeasurable f μ) (hg : NullMeasurable g μ) :
    NullMeasurable (fun x => if p x then f x else g x) μ :=
  Measurable.ite (α := NullMeasurableSpace α μ) hp hf hg


instance ENat.instBorelSpace : BorelSpace ENat := ⟨borel_eq_top_of_countable.symm⟩

theorem ENat.toENNReal_measurableEmbedding : MeasurableEmbedding toENNReal :=
  Measurable.measurableEmbedding .of_discrete (fun _ _ => ENat.toENNReal_inj.mp)



theorem wah
  {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
  (rolls : ℕ → Ω → ℕ)
  (rolls_unif : ∀ n, pdf.IsUniform (rolls n) (Set.Icc 1 6) ℙ Measure.count)
  (rolls_indep : iIndepFun rolls) :
    ∫⁻ ω, sInf ((↑) '' {i | Odd (rolls i ω)}) = 1 := by
  have six : Measure.count (Set.Icc 1 6) = 6 := by
    rw [Measure.count_apply_finite' (Set.toFinite _) (by trivial)]
    simp
  suffices ∀ k : ℕ, ℙ {ω | k ≤ sInf (((↑) : ℕ → ENat) '' {i | Odd (rolls i ω)})} = 1 / 2 ^ k by
    simp_rw [show Nat.cast = ENat.toENNReal ∘ Nat.cast from rfl, Set.image_comp]
    have h_inf : ∀ s : Set ENat, sInf (ENat.toENNReal '' s) = sInf s := fun s => by
      obtain rfl | s_ne := s.eq_empty_or_nonempty
      . simp
      rw [← ENat.toENNReal_mono.map_csInf s_ne]
    simp_rw [h_inf]
    have f_mble : AEMeasurable (fun ω => sInf (Nat.cast '' {i | Odd (rolls i ω)}) : Ω → ENat) := by
      rw [← ENat.toENNReal_measurableEmbedding.aemeasurable_comp_iff]
      simp_rw [Function.comp_def, ← h_inf, ← Set.image_comp, sInf_image, Set.mem_setOf]
      apply AEMeasurable.iInf
      intro i
      simp_rw [ciInf_eq_ite, sInf_empty, dite_eq_ite]
      refine NullMeasurable.ite ?_ measurable_const measurable_const |>.aemeasurable
      rw [show {a | Odd (rolls i a)} = rolls i ⁻¹' {n | Odd n} from rfl]
      refine rolls_unif i |>.aemeasurable ?_ ?_ |>.nullMeasurable (by simp) <;> simp [six]
    rw [lintegral_eq_tsum_meas_le _ f_mble]
    simp_rw [this]
    rw [tsum_pnat_eq_tsum_succ (f := fun k => 1 / 2 ^ k)]
    simp_rw [one_div, ENNReal.inv_pow, ENNReal.tsum_geometric_add_one]
    simp only [ENNReal.one_sub_inv_two, inv_inv]
    apply ENNReal.inv_mul_cancel <;> norm_num
  -- the rest courtesy of @wen1now
  have : ∀ k : ℕ, ∀ ω, (k ≤ sInf (((↑) : ℕ → ENat) '' {i : ℕ | Odd (rolls i ω)})) ↔ ∀ i < k, Even (rolls i ω) := by
    simp_rw [← Nat.not_even_iff_odd]
    intro k ω
    simp only [le_sInf_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Nat.cast_le]
    congr! 1
    rw [← not_lt]
    tauto
  simp_rw [this]; clear this
  intro k
  have : {ω | ∀ i < k, Even (rolls i ω)} = ⋂ i ∈ Finset.range k, {ω | Even (rolls i ω)} := by aesop
  rw [this]; clear this
  rw [iIndepFun.meas_biInter rolls_indep]
  . have : ∀ i, ℙ {ω | Even (rolls i ω)} = 1 / 2 := by
      intro i
      have three : Measure.count (Set.Icc 1 6 ∩ setOf Even) = 3 := by
        rw [Measure.count_apply_finite' (Set.toFinite _) (by trivial)]
        simp
        norm_cast
      have : {ω | Even (rolls i ω)} = rolls i ⁻¹' setOf Even := rfl
      rw [this, (rolls_unif i).measure_preimage (by simp [six]) (by simp [six]) (by trivial)]
      rw [six, three, ENNReal.div_eq_div_iff]
      <;> norm_num
    simp [this]
    exact Eq.symm ENNReal.inv_pow
  . simp only [Finset.mem_range, measurableSet_setOf]
    intro i hik
    apply Measurable.comp (g := Even)
    . apply measurable_of_countable
    . exact Measurable.of_comap_le fun s a => a
