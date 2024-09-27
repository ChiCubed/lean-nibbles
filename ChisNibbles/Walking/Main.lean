import ChisNibbles.Walking.HilbertCurve

open HilbertCurve

namespace Walking

def IsWalkable {α} (s e : α → EuclideanSpace ℝ (Fin 2)) :=
  ∃ p : (i : α) → Path (s i) (e i),
  ∀ t, Function.Injective (fun i => p i t)

namespace IsWalkable

instance instIsSymm {α} : IsSymm (α → EuclideanSpace ℝ (Fin 2)) IsWalkable where
  symm _ _ := fun ⟨p, h⟩ => ⟨Path.symm ∘' p, h ∘' unitInterval.symm⟩

def symm {α s e} (h : @IsWalkable α s e) : IsWalkable e s :=
  _root_.symm h

instance instIsTrans {α} : IsTrans (α → EuclideanSpace ℝ (Fin 2)) IsWalkable where
  trans a b c := fun ⟨p₁, h₁⟩ ⟨p₂, h₂⟩ => by
    exists fun i => .trans (p₁ i) (p₂ i)
    intro t
    simp_rw [Path.trans_apply]
    split
    . apply h₁
    . apply h₂

def trans {α s m e} (h₁ : @IsWalkable α s m) (h₂ : IsWalkable m e) : IsWalkable s e :=
  Trans.trans h₁ h₂

def comap {α β s e} (h : @IsWalkable α s e) (f : β ↪ α) : IsWalkable (s ∘ f) (e ∘ f) :=
  let ⟨p, h⟩ := h
  ⟨p ∘' f, fun t => (h t).comp f.injective⟩

@[simp]
theorem start_injective {α s e} (h : @IsWalkable α s e) : Function.Injective s :=
  let ⟨p, h⟩ := h
  by convert h 0; simp

@[simp]
theorem end_injective {α s e} (h : @IsWalkable α s e) : Function.Injective e :=
  let ⟨p, h⟩ := h
  by convert h 1; simp



open unitInterval

-- TODO: imma just use choice for now,
-- but mayyyybe you can get around it?
noncomputable def invHilbertCurve (x : I × I) : I :=
  hilbertCurve_surjective x |>.choose

-- idk why simp has stopped working for this, pretty annoying :(
-- how do i make it start working again
@[simp]
theorem hilbertCurve_invHilbertCurve x : hilbertCurve (invHilbertCurve x) = x :=
  hilbertCurve_surjective x |>.choose_spec

@[simp]
theorem invHilbertCurve_injective : Function.Injective invHilbertCurve :=
  Function.Injective.of_comp (f := hilbertCurve) fun x y => by
    simp_rw [Function.comp_apply, hilbertCurve_invHilbertCurve, imp_self]

-- TODO put this somewhere else lol
theorem squareCoe.continuous : Continuous squareCoe := by
  unfold squareCoe
  continuity

def hilbert : @IsWalkable (I × I) (fun x => ![x.1, x.2]) (fun x => ![invHilbertCurve x, 0]) := by
  refine (show IsWalkable _ (fun x => ![invHilbertCurve x, 1/2]) from ?_).trans ?_
  . apply symm
    exists fun x => .mk
      (.mk
        (fun t => aux.e ∘ squareCoe <| hilbertHomotopy' (t, invHilbertCurve x))
        (aux.e.continuous.comp <| squareCoe.continuous.comp <| .comp
          (map_continuous _)
          (.prod_mk continuous_id continuous_const)))
      (by simp)
      (by simp [squareCoe]; rw [hilbertCurve_invHilbertCurve])
    intro t
    simp only [Path.coe_mk_mk]
    apply aux.e.injective.comp
    obtain rfl | ht : t = 1 ∨ t < 1 := unitInterval.le_one'.eq_or_lt
    . intro x y
      simp [hilbertCurve_invHilbertCurve x, hilbertCurve_invHilbertCurve y]
    refine (show Function.Injective squareCoe from ?_).comp ?_
    . intro x y hxy
      simp_rw [squareCoe, Prod.mk.injEq, Subtype.coe_inj, ← Prod.mk.injEq] at hxy
      exact hxy
    refine (show Function.Injective fun x => hilbertHomotopy' (t, x) from ?_).comp
      invHilbertCurve_injective
    simp_rw [← ContinuousMap.Homotopy.curry_apply]
    apply hilbertHomotopy'_injective
    rcases t with ⟨t, ht₀, ht₁⟩
    simpa [unitInterval.symm, ← Subtype.coe_lt_coe] using ht
  save
  . exists fun x => .mk
      (.mk
        (fun t => ![invHilbertCurve x, σ t / 2])
        (by
          simp_rw [← aux.e_apply_mk]
          exact aux.e.continuous.comp <| .prod_mk
            continuous_const
            (by continuity)))
      (by simp)
      (by simp)
    intro t
    refine Function.Injective.of_comp (f := fun x => x 0) ?_
    simpa [Function.comp] using Subtype.coe_injective.comp invHilbertCurve_injective

end IsWalkable

-- i'm just proving the necessary affine transformations give walk stuff
-- by hand, because it seems like the machinery to make it easier isn't in mathlib
-- (or at least i can't find it)

open Function (Injective) in
open unitInterval IsWalkable Function.Injective in
lemma walkies.aux {α} (s : α ↪ EuclideanSpace ℝ (Fin 2)) :
    ∃ e : α ↪ I,
    IsWalkable s (fun i => ![e i, 0]) := by
  wlog hs : ∀ i, s i 0 ∈ I ∧ s i 1 ∈ I
  . let e i := (1 + ‖s i‖)⁻¹ • s i
    have h₁ : IsWalkable s e
    . have hc (t : I) {v : EuclideanSpace ℝ (Fin 2)} : 0 < 1 + t * ‖v‖
      . rcases t with ⟨t, ht₀, ht₁⟩
        positivity
      exists fun i => .mk
        (.mk
          (fun t => (1 + t * ‖s i‖)⁻¹ • s i)
          (.smul (.inv₀ (by clear * -; continuity) (fun t => (hc t).ne')) continuous_const))
        (by simp)
        (by simp)
      intro t i j h
      simp only [Path.coe_mk_mk] at h
      have h_norm : ‖s i‖ = ‖s j‖
      . apply congrArg (‖·‖) at h
        simp_rw [norm_smul, norm_inv, Real.norm_of_nonneg (hc t).le, inv_mul_eq_div,
          div_eq_div_iff (hc t).ne' (hc t).ne'] at h
        linear_combination h
      rw [h_norm, inv_smul_eq_iff₀ (hc t).ne', smul_inv_smul₀ (hc t).ne'] at h
      exact s.injective h
    have e_inj : Injective e := h₁.end_injective
    have e_norm i : ‖e i‖ < 1
    . have hc : 0 < 1 + ‖s i‖ := by positivity
      simp_rw [e, norm_smul, norm_inv, Real.norm_of_nonneg hc.le, inv_mul_lt_iff hc]
      simp
    let e' i : EuclideanSpace ℝ (Fin 2) := midpoint ℝ (e i) ![1, 1]
    have h₂ : IsWalkable e e'
    . exists fun i => .mk
        (.mk
          (fun t => AffineMap.lineMap (e i) ![1, 1] (t / 2 : ℝ))
          (AffineMap.lineMap_continuous.comp (by clear * -; continuity)))
        (by simp)
        (lineMap_one_half _ _)
      intro t
      simp only [Path.coe_mk_mk]
      conv => congr; ext i; rw [← AffineMap.lineMap_apply_one_sub, ← AffineMap.homothety_eq_lineMap]
      refine comp
        (of_comp (f := AffineMap.homothety ![1, 1] (1 / (1 - t / 2) : ℝ)) ?_)
        e_inj
      erw [← AffineMap.coe_comp, ← AffineMap.homothety_mul, one_div_mul_cancel (by linarith only [t.2.2]),
        AffineMap.homothety_one, AffineMap.coe_id]
      exact fun {_ _} => id
    save
    have e'_inj : Injective e' := h₂.end_injective
    obtain ⟨te, h₃⟩ := this ⟨e', e'_inj⟩ <| by
      clear * - e_inj e_norm
      intro i
      replace e_norm := e_norm i |>.le -- lol
      rw [EuclideanSpace.norm_eq (e i), Real.sqrt_le_one] at e_norm
      suffices ∀ k, e' i k ∈ I from Fin.forall_fin_two.mp this
      intro k
      suffices e i k ∈ Set.Icc (-1) 1 by
        rw [Set.mem_Icc] at this ⊢
        suffices 0 ≤ 2⁻¹ * e i k + 2⁻¹ ∧ 2⁻¹ * e i k + 2⁻¹ ≤ 1 by fin_cases k <;> simpa [e', midpoint_eq_smul_add]
        rw [inv_eq_one_div]
        constructor <;> linarith only [this.1, this.2]
      have := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ k) |>.trans e_norm
      simpa only [Real.norm_eq_abs, sq_abs, sq_le_one_iff_abs_le_one, abs_le]
    exact ⟨te, .trans h₁ (.trans h₂ h₃)⟩
  save
  let s' i : I × I :=
    (⟨s i 0, (hs i).1⟩, ⟨s i 1, (hs i).2⟩)
  have s'_inj : Injective s'
  . refine of_comp (f := fun x => (![x.1, x.2] : EuclideanSpace ℝ (Fin 2))) ?_
    convert s.injective
    ext i k; fin_cases k <;> rfl
  exists ⟨invHilbertCurve ∘ s', invHilbertCurve_injective.comp s'_inj⟩
  convert hilbert.comap ⟨s', s'_inj⟩
  ext i k; fin_cases k <;> rfl

open Function (Injective) in
open Function.Injective in
theorem walkies {α} (s e : α ↪ EuclideanSpace ℝ (Fin 2)) :
    ∃ p : (i : α) → Path (s i) (e i),
    ∀ t, Injective (fun i => p i t) := by
  change IsWalkable s e
  obtain ⟨s', hs⟩ := walkies.aux s
  obtain ⟨e', he⟩ := walkies.aux e
  refine .trans hs (.trans ?_ he.symm)
  clear * -
  refine .trans (m := fun i => ![s' i, e' i]) ?_ <| .trans (m := fun i => ![0, e' i]) ?_ ?_
  . exists fun i => .mk
      (.mk
        (fun t => ![s' i, t * e' i])
        (by
          simp_rw [← aux.e_apply_mk]
          exact aux.e.continuous.comp <| by continuity))
      (by norm_num)
      (by norm_num)
    intro t
    refine of_comp (f := fun x => x 0) ?_
    simpa using Subtype.coe_injective.comp s'.injective
  save
  . exists fun i => .mk
      (.mk
        (fun t => ![(1 - t) * s' i, e' i])
        (by
          simp_rw [← aux.e_apply_mk]
          exact aux.e.continuous.comp <| by continuity))
      (by norm_num)
      (by norm_num)
    intro t
    refine of_comp (f := fun x => x 1) ?_
    simpa using Subtype.coe_injective.comp e'.injective
  save
  . exists fun i => .mk
      (.mk
        (fun t => ![t * e' i, (1 - t) * e' i])
        (by
          simp_rw [← aux.e_apply_mk]
          exact aux.e.continuous.comp <| by continuity))
      (by norm_num)
      (by norm_num)
    intro t
    refine of_comp (f := fun x => x 0 + x 1) ?_
    simpa [Function.comp_def, ← add_mul] using Subtype.coe_injective.comp e'.injective

end Walking
